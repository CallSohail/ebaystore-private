"""
Leboncoin Product Scraper with AI Processing
============================================

A Leboncoin (leboncoin.fr) listing scraper that mirrors the eBay Scraper Studio
feature set: scrape a listing, download its images, store everything in a local
product folder + CSV, and generate platform-tuned descriptions with Groq.

Design
------
This module reuses all of the *generic* infrastructure already built and tested
in ``ebay_scraper`` (data models, image downloading, file management, the Groq
processor and platform agent, the batch queue, the image-format converter, the
folder-name dialog and the global styling). Only the parts that are genuinely
Leboncoin-specific are reimplemented here:

* ``LeboncoinScraper`` — URL validation/normalisation and listing extraction.
  Leboncoin is a Next.js app, so the most reliable source of truth is the
  ``__NEXT_DATA__`` JSON blob embedded in the page (with OpenGraph/JSON-LD
  fallbacks).
* A Leboncoin-branded Streamlit ``main()``.

Run with:
    streamlit run leboncoin_scraper.py

Version: 1.0
"""

from __future__ import annotations

import json
import re
import time
import random
import traceback
import concurrent.futures
from pathlib import Path
from datetime import datetime
from urllib.parse import urlparse
from typing import Dict, List, Optional, Any

import streamlit as st
from bs4 import BeautifulSoup

# ---------------------------------------------------------------------------
# Reuse the battle-tested building blocks from the eBay studio.
# Importing the module also configures logging, proxy env vars, etc. It does
# NOT launch the eBay UI (that is guarded by ``if __name__ == "__main__"``).
# ---------------------------------------------------------------------------
from ebay_scraper import (
    # data models + errors
    ProductData,
    ScrapingResult,
    ValidationError,
    # core classes we extend / reuse
    EbayScraper,
    FileManager,
    GroqProcessor,
    # shared helpers
    safe_request,
    append_to_local_csv,
    load_groq_api_key,
    save_groq_api_key,
)

# Some helpers are module-level functions in ebay_scraper; reference them via
# the module to keep this file resilient to upstream refactors.
import ebay_scraper as _eb

logger = _eb.logger

# Reused UI + persistence helpers (module-level functions in ebay_scraper).
inject_global_styles = _eb.inject_global_styles
display_scraping_results = _eb.display_scraping_results
render_batch_tab = _eb.render_batch_tab
render_image_format_tab = _eb.render_image_format_tab
_folder_name_dialog = _eb._folder_name_dialog
BASE_SAVE_DIR = _eb.BASE_SAVE_DIR

LEBONCOIN_CSV = "Leboncoin_Products.csv"

# Leboncoin sits behind DataDome, which 403s plain HTTP requests. When that
# happens we fall back to a real headless browser (Playwright) that executes
# the JS challenge and collects a valid cookie.
BROWSER_INSTALL_MSG = (
    "Leboncoin blocked the request (DataDome) and the headless-browser "
    "fallback is not available.\n\n"
    "To enable it, install Playwright + a browser once:\n"
    "    pip install playwright\n"
    "    playwright install chromium\n\n"
    "Then try again. (A residential / home internet connection also helps — "
    "datacenter IPs are blocked aggressively.)"
)


def _playwright_available() -> bool:
    try:
        import playwright  # noqa: F401
        return True
    except Exception:
        return False


# =============================================================================
# LEBONCOIN SCRAPER
# =============================================================================

class LeboncoinScraper(EbayScraper):
    """Scraper for leboncoin.fr listings.

    Subclasses :class:`EbayScraper` to inherit the anti-bot session handling,
    image download plumbing (``download_image``/``_get_image_extension``) and
    folder helpers, and overrides only the Leboncoin-specific bits: URL
    validation, normalisation and the actual page extraction.
    """

    LEBONCOIN_HOSTS = ("leboncoin.fr",)

    def __init__(self):
        super().__init__()
        # French-leaning Accept-Language helps us get the FR listing variant.
        self.session.headers["Accept-Language"] = "fr-FR,fr;q=0.9,en;q=0.7"
        logger.info("Leboncoin scraper initialized")

    # ----- URL handling ----------------------------------------------------
    def validate_ebay_url(self, url: str) -> bool:
        """Validate a Leboncoin listing URL.

        Kept under the name ``validate_ebay_url`` so the reused single-product
        and batch handlers (which call this method on the scraper) work
        unchanged. Accepts e.g.::

            https://www.leboncoin.fr/ad/accessoires_bagagerie/2494715054
            https://www.leboncoin.fr/voitures/2494715054.htm
            leboncoin.fr/ad/.../2494715054?utm=...
        """
        if not url or not isinstance(url, str):
            raise ValidationError("URL must be a non-empty string")

        url = url.strip()
        if not url:
            raise ValidationError("URL is empty")

        if not re.match(r"^[a-zA-Z]+://", url):
            url = "https://" + url

        try:
            parsed = urlparse(url)
        except Exception as e:
            raise ValidationError(f"Could not parse URL: {e}")

        netloc = parsed.netloc.lower().split(":")[0]
        for prefix in ("www.", "m."):
            if netloc.startswith(prefix):
                netloc = netloc[len(prefix):]
                break

        if not netloc:
            raise ValidationError("URL is missing a domain")

        is_lbc = netloc in self.LEBONCOIN_HOSTS or netloc.endswith(".leboncoin.fr")
        if not is_lbc:
            raise ValidationError(
                "URL must be from leboncoin.fr (e.g. "
                "https://www.leboncoin.fr/ad/<category>/<id>)"
            )

        # Must contain a numeric listing id somewhere in the path.
        if self.extract_id_from_url(url):
            return True

        raise ValidationError(
            "URL does not look like a Leboncoin listing. Expected a numeric "
            "ad id, e.g. /ad/accessoires_bagagerie/2494715054"
        )

    def extract_id_from_url(self, url: str) -> Optional[str]:
        """Pull the numeric ad id out of a Leboncoin URL."""
        try:
            path = urlparse(url).path
        except Exception:
            path = url or ""
        # /ad/<cat>/<id>  |  /<cat>/<id>.htm  |  trailing /<id>
        m = re.search(r"/(\d{6,})(?:\.htm)?(?:[/?#]|$)", path)
        if m:
            return m.group(1)
        m = re.search(r"(\d{6,})", path)
        return m.group(1) if m else None

    def normalize_ebay_url(self, url: str) -> str:
        """Strip tracking query/fragment, keep the canonical listing URL."""
        try:
            parsed = urlparse(url if re.match(r"^[a-zA-Z]+://", url) else "https://" + url)
            netloc = parsed.netloc or "www.leboncoin.fr"
            return f"{parsed.scheme or 'https'}://{netloc}{parsed.path}"
        except Exception:
            return url

    # ----- extraction ------------------------------------------------------
    def _find_ad_dict(self, obj: Any) -> Optional[Dict]:
        """Recursively locate the listing dict inside arbitrary JSON.

        A Leboncoin ad object is identified by having a ``subject`` plus at
        least one of ``list_id``/``price``/``images``.
        """
        if isinstance(obj, dict):
            keys = obj.keys()
            if "subject" in keys and any(k in keys for k in ("list_id", "price", "images", "body")):
                return obj
            for v in obj.values():
                found = self._find_ad_dict(v)
                if found:
                    return found
        elif isinstance(obj, list):
            for v in obj:
                found = self._find_ad_dict(v)
                if found:
                    return found
        return None

    def _extract_ad_json(self, soup: BeautifulSoup) -> Optional[Dict]:
        """Find and parse the embedded listing JSON."""
        # 1) The canonical Next.js data island.
        script = soup.find("script", id="__NEXT_DATA__")
        if script and script.string:
            try:
                data = json.loads(script.string)
                ad = (
                    data.get("props", {})
                    .get("pageProps", {})
                    .get("ad")
                )
                if isinstance(ad, dict) and ad.get("subject"):
                    return ad
                found = self._find_ad_dict(data)
                if found:
                    return found
            except Exception as e:
                logger.debug(f"Failed to parse __NEXT_DATA__: {e}")

        # 2) Any other application/json blob on the page.
        for tag in soup.find_all("script", {"type": "application/json"}):
            if not tag.string:
                continue
            try:
                data = json.loads(tag.string)
            except Exception:
                continue
            found = self._find_ad_dict(data)
            if found:
                return found
        return None

    @staticmethod
    def _format_price(ad: Dict) -> str:
        """Return a human price string like ``120 €``."""
        cents = ad.get("price_cents")
        if isinstance(cents, (int, float)) and cents > 0:
            euros = cents / 100
            return f"{euros:.0f} €" if euros == int(euros) else f"{euros:.2f} €"
        price = ad.get("price")
        if isinstance(price, list) and price:
            price = price[0]
        if isinstance(price, (int, float)) and price > 0:
            return f"{int(price)} €"
        if isinstance(price, str) and price.strip():
            return price.strip()
        return ""

    @staticmethod
    def _extract_images(ad: Dict) -> List[str]:
        imgs = ad.get("images") or {}
        urls: List[str] = []
        if isinstance(imgs, dict):
            for key in ("urls_large", "urls", "urls_thumb"):
                val = imgs.get(key)
                if isinstance(val, list) and val:
                    urls = [u for u in val if isinstance(u, str)]
                    if urls:
                        break
        elif isinstance(imgs, list):
            for item in imgs:
                if isinstance(item, str):
                    urls.append(item)
                elif isinstance(item, dict):
                    u = item.get("url") or item.get("url_large") or item.get("src")
                    if u:
                        urls.append(u)
        # De-dupe preserving order.
        seen, out = set(), []
        for u in urls:
            if u not in seen:
                seen.add(u)
                out.append(u)
        return out

    def _build_product_from_ad(self, ad: Dict, url: str) -> ProductData:
        title = (ad.get("subject") or "").strip()
        description = (ad.get("body") or "").strip()
        price = self._format_price(ad)

        brand = ""
        condition = ""
        specifics: Dict[str, str] = {}
        for attr in ad.get("attributes", []) or []:
            if not isinstance(attr, dict):
                continue
            label = (attr.get("key_label") or attr.get("key") or "").strip()
            value = (attr.get("value_label") or attr.get("value") or "").strip()
            if label and value:
                specifics[label] = value
            key = (attr.get("key") or "").lower()
            if key in ("brand", "marque") and value:
                brand = value
            if key in ("condition", "item_condition", "etat", "état") and value:
                condition = value

        category = (ad.get("category_name") or "").strip()

        location = ""
        loc = ad.get("location") or {}
        if isinstance(loc, dict):
            parts = [str(loc.get(k)) for k in ("city", "zipcode") if loc.get(k)]
            location = " ".join(parts).strip()

        seller = ""
        owner = ad.get("owner") or {}
        if isinstance(owner, dict):
            seller = (owner.get("name") or "").strip()

        item_id = str(ad.get("list_id") or self.extract_id_from_url(url) or "").strip()

        return ProductData(
            url=url,
            title=title,
            price=price,
            condition=condition,
            seller=seller,
            shipping="",  # Leboncoin shipping is negotiated per-listing; rarely structured
            description=description,
            brand=brand,
            item_specifics=specifics,
            location=location,
            category=category,
            item_id=item_id,
        )

    def _build_product_from_meta(self, soup: BeautifulSoup, url: str):
        """OpenGraph fallback when the JSON island is unavailable.

        Returns a ``(ProductData, list[str])`` tuple (product + image urls).
        """
        def og(prop: str) -> str:
            tag = soup.find("meta", property=prop) or soup.find("meta", attrs={"name": prop})
            return (tag.get("content").strip() if tag and tag.get("content") else "")

        title = og("og:title") or (soup.title.string.strip() if soup.title and soup.title.string else "")
        description = og("og:description")
        price = og("product:price:amount")
        if price:
            currency = og("product:price:currency") or "€"
            price = f"{price} {currency}".strip()
        image = og("og:image")

        return ProductData(
            url=url,
            title=title,
            price=price,
            description=description,
            item_id=self.extract_id_from_url(url) or "",
        ), ([image] if image else [])

    # ----- fetching (HTTP first, headless browser fallback) ----------------
    def _browser_worker(self, url: str):
        """Render ``url`` in headless Chromium; return (html, cookies).

        Runs in its own thread (see ``_fetch_with_browser``) so Playwright's
        sync API never collides with an asyncio loop Streamlit may be running.
        """
        from playwright.sync_api import sync_playwright

        ua = random.choice(_eb.USER_AGENTS)
        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=True,
                args=[
                    "--no-sandbox",
                    "--disable-blink-features=AutomationControlled",
                    "--disable-dev-shm-usage",
                ],
            )
            context = browser.new_context(
                user_agent=ua,
                locale="fr-FR",
                timezone_id="Europe/Paris",
                viewport={"width": 1366, "height": 900},
                extra_http_headers={"Accept-Language": "fr-FR,fr;q=0.9,en;q=0.7"},
            )
            # Hide the obvious navigator.webdriver automation flag.
            context.add_init_script(
                "Object.defineProperty(navigator, 'webdriver', {get: () => undefined});"
            )
            page = context.new_page()
            try:
                page.goto(url, wait_until="domcontentloaded", timeout=45000)
                # Give DataDome a moment, then wait for the data island.
                try:
                    page.wait_for_selector("script#__NEXT_DATA__", timeout=15000)
                except Exception:
                    page.wait_for_timeout(3500)
                html = page.content()
                cookies = context.cookies()
                return html, cookies
            finally:
                context.close()
                browser.close()

    def _fetch_with_browser(self, url: str):
        """Run the browser worker in an isolated thread. Returns (html, cookies)."""
        if not _playwright_available():
            return None, None
        try:
            with concurrent.futures.ThreadPoolExecutor(max_workers=1) as ex:
                return ex.submit(self._browser_worker, url).result(timeout=75)
        except Exception as e:
            logger.warning(f"Headless-browser fetch failed: {e}")
            return None, None

    def _get_page(self, url: str, referer: str) -> Optional[str]:
        """Return rendered HTML for ``url``.

        Tries a fast HTTP request first; on a block/anti-bot response, falls
        back to a headless browser and copies its cookies onto the session so
        image downloads (img.leboncoin.fr) stay authenticated.
        """
        response = safe_request(self.session, url, timeout=30, referer=referer)
        if response is not None and response.status_code == 200:
            text = response.text
            low = text.lower()
            blocked = ("datadome" in low or "captcha" in low or "are you a human" in low)
            if "__NEXT_DATA__" in text or not blocked:
                return text

        # HTTP failed or was challenged — try a real browser.
        html, cookies = self._fetch_with_browser(url)
        if html:
            for c in cookies or []:
                try:
                    self.session.cookies.set(
                        c.get("name"), c.get("value"), domain=c.get("domain")
                    )
                except Exception:
                    pass
            return html
        return None

    def scrape_product(self, url: str) -> ScrapingResult:
        """Scrape a single Leboncoin listing into a :class:`ScrapingResult`."""
        try:
            self.validate_ebay_url(url)
            url = self.normalize_ebay_url(url.strip())

            try:
                host = urlparse(url).netloc or "www.leboncoin.fr"
                self._warm_session(host)
                referer = f"https://{host}/"
            except Exception:
                referer = "https://www.leboncoin.fr/"

            time.sleep(random.uniform(0.8, 2.0))

            html = self._get_page(url, referer)
            if not html:
                if not _playwright_available():
                    return ScrapingResult(success=False, error_message=BROWSER_INSTALL_MSG)
                return ScrapingResult(
                    success=False,
                    error_message=(
                        "Could not load the listing even via the headless browser.\n"
                        "• DataDome may be serving a hard challenge for this IP — "
                        "wait a few minutes, or use a residential connection.\n"
                        "• The ad may have been sold, expired or removed."
                    ),
                )

            soup = BeautifulSoup(html, "html.parser")

            lowered = html.lower()
            if ("__NEXT_DATA__" not in html) and (
                "datadome" in lowered or "captcha" in lowered or "are you a human" in lowered
            ):
                return ScrapingResult(
                    success=False,
                    error_message="Leboncoin is showing a bot-verification (DataDome) challenge. Wait a few minutes and try again.",
                )

            ad = self._extract_ad_json(soup)
            if ad:
                product_data = self._build_product_from_ad(ad, url)
                image_urls = self._extract_images(ad)
            else:
                product_data, image_urls = self._build_product_from_meta(soup, url)

            if not product_data.title:
                return ScrapingResult(
                    success=False,
                    error_message="Could not extract the listing title. The page format may have changed or the request was blocked.",
                )

            return ScrapingResult(success=True, product_data=product_data, image_urls=image_urls)

        except ValidationError as e:
            return ScrapingResult(success=False, error_message=f"Invalid URL: {e}")
        except Exception:
            logger.error(f"Unexpected error in scrape_product: {traceback.format_exc()}")
            return ScrapingResult(success=False, error_message="An unexpected error occurred. Please try again.")


# =============================================================================
# PERSISTENCE (Leboncoin-branded CSV)
# =============================================================================

def _save_scraped_product(result: ScrapingResult, folder_name: str,
                          scraper: LeboncoinScraper, file_manager: FileManager):
    """Persist a scraped Leboncoin product under the chosen folder name."""
    folder_path = file_manager.create_product_folder(
        brand=result.product_data.brand,
        item_id=result.product_data.item_id,
        fallback_title=result.product_data.title,
        custom_name=folder_name,
    )
    result.folder_path = str(folder_path)

    file_manager.save_product_description_markdown(result.product_data, folder_path)
    file_manager.save_product_text(result.product_data, folder_path)
    file_manager.save_raw_scrape_text(result.product_data, folder_path)

    downloaded_images: List[str] = []
    if result.image_urls:
        downloaded_images = file_manager.download_images(scraper, result.image_urls, folder_path)

    csv_updated = append_to_local_csv(result.product_data, filename=LEBONCOIN_CSV)
    return folder_path, downloaded_images, csv_updated


def _persist_after_dialog(scraper: LeboncoinScraper, file_manager: FileManager) -> None:
    """If the folder-name dialog was confirmed, write files + render the card."""
    pending = st.session_state.get("pending_save")
    name = st.session_state.get("confirmed_folder_name")
    if not pending or not name:
        return

    result: ScrapingResult = pending["result"]
    progress_bar = st.progress(0)
    status_msg = st.empty()
    try:
        status_msg.markdown("**Saving files...**")
        progress_bar.progress(30)
        folder_path, downloaded_images, csv_updated = _save_scraped_product(
            result, name, scraper, file_manager
        )
        progress_bar.progress(95)
        status_msg.markdown("**Done.**")
        time.sleep(0.4)
        status_msg.empty()
        progress_bar.empty()
        display_scraping_results(result, downloaded_images, folder_path, csv_updated)
    except Exception as e:
        status_msg.error(f"Save failed: {e}")
        logger.error(f"Save error: {traceback.format_exc()}")
    finally:
        st.session_state["pending_save"] = None
        st.session_state["confirmed_folder_name"] = None
        st.session_state["save_phase"] = None


def handle_single_product_scrape(url: str, scraper: LeboncoinScraper, file_manager: FileManager):
    """Scrape one Leboncoin URL, then open the folder-name dialog to save."""
    if not url or not url.strip():
        st.error("Please paste a Leboncoin listing URL before clicking Start scraping.")
        return

    url = url.strip().strip("<>\"'")
    if any(ws in url for ws in (" ", "\t", "\n")):
        parts = [p for p in re.split(r"\s+", url) if p]
        if parts:
            url = parts[0]
            if len(parts) > 1:
                st.info(f"Detected multiple URLs — using the first. Use **Batch Processing** for {len(parts)} at once.")

    try:
        scraper.validate_ebay_url(url)
    except ValidationError as e:
        st.error(f"Invalid URL — {e}")
        return

    progress_bar = st.progress(0)
    status_msg = st.empty()
    try:
        status_msg.markdown("**Extracting listing data...**")
        progress_bar.progress(15)
        result = scraper.scrape_product(url)
        if not result.success:
            status_msg.error(f"Failed: {result.error_message}")
            progress_bar.empty()
            return

        progress_bar.progress(60)
        status_msg.markdown("**Ready — choose a folder name to continue.**")
        time.sleep(0.3)
        status_msg.empty()
        progress_bar.empty()

        suggested = file_manager.suggest_folder_name(
            brand=result.product_data.brand,
            item_id=result.product_data.item_id,
            fallback_title=result.product_data.title,
        )
        st.session_state["pending_save"] = {"result": result, "suggested": suggested}
        st.session_state["pending_folder_name"] = suggested
        st.session_state["save_phase"] = "awaiting_name"
        st.rerun()
    except Exception as e:
        status_msg.error(f"Unexpected error: {e}")
        logger.error(f"Scrape handler error: {traceback.format_exc()}")


# =============================================================================
# STREAMLIT APP
# =============================================================================

def initialize_components():
    return LeboncoinScraper(), FileManager()


def _render_ai_tab(file_manager: FileManager, groq_api_key: str):
    """AI content studio: content generator + a simple context-aware assistant."""
    st.markdown(
        """
        <div class="es-card">
            <div class="es-card-title">AI content studio</div>
            <p class="es-card-sub">Generate platform-tuned descriptions from your scraped Leboncoin data, or ask the assistant about a listing.</p>
        </div>
        """,
        unsafe_allow_html=True,
    )

    if not groq_api_key:
        st.warning("Add a Groq API key in the sidebar to use the AI features.")
        return

    ai_tab1, ai_tab2 = st.tabs(["Content generator", "AI assistant"])

    # ----- Content generator ----------------------------------------------
    with ai_tab1:
        product_folders = file_manager.get_existing_product_folders()
        if not product_folders:
            st.info("No scraped listings yet. Use the Single Product or Batch Processing tab first.")
        else:
            col_input, col_output = st.columns([1, 1.5], gap="large")
            with col_input:
                st.markdown("**1. Select content**")
                folder_names = [f["folder_name"] for f in product_folders]
                selected_folder_name = st.selectbox("Product folder", folder_names, key="ai_folder")

                # Clear stale output when the user switches folders.
                if st.session_state.get("ai_last_folder") != selected_folder_name:
                    st.session_state["ai_generated_result"] = None
                    st.session_state["ai_last_folder"] = selected_folder_name

                folder_info = next((f for f in product_folders if f["folder_name"] == selected_folder_name), None)

                selected_file = None
                if folder_info:
                    files = folder_info.get("text_files", [])
                    if files:
                        default_idx = next((i for i, f in enumerate(files) if "raw_scrape.txt" in f), 0)
                        selected_file = st.selectbox("Source file", files, index=default_idx, key="ai_file")
                    else:
                        st.warning("This folder has no text files. Re-scrape the listing.")

                st.markdown("**2. Configure**")
                target_platform = st.selectbox(
                    "Target platform",
                    ["Leboncoin", "General", "eBay", "Vinted", "Vestiaire Collective",
                     "Depop", "Poshmark", "Mercari", "Etsy", "Facebook Marketplace",
                     "Shopify", "Grailed", "Instagram"],
                    help="Tone, structure and length are optimised for this marketplace.",
                    key="ai_platform",
                )
                with st.expander("Advanced instructions", expanded=False):
                    custom_instructions = st.text_area(
                        "Custom rules",
                        placeholder="e.g. 'no emojis', 'focus on flaws', 'short & punchy'",
                        height=80,
                        key="ai_custom",
                    )
                generate_btn = st.button(
                    "Generate description",
                    type="primary",
                    use_container_width=True,
                    disabled=not (folder_info and selected_file),
                    key="ai_generate_btn",
                )

            with col_output:
                st.markdown("**3. Result**")
                if "ai_generated_result" not in st.session_state:
                    st.session_state["ai_generated_result"] = None

                if generate_btn and folder_info and selected_file:
                    try:
                        original_content = file_manager.load_product_text(folder_info["folder_path"], selected_file)
                        if not original_content:
                            st.error("Source file is empty.")
                        else:
                            with st.spinner(f"Rewriting for {target_platform}..."):
                                groq_processor = GroqProcessor(groq_api_key)
                                result_text = groq_processor.platform_agent.generate_platform_description(
                                    raw_text=original_content,
                                    product_data=None,
                                    platform=target_platform,
                                    custom_instructions=custom_instructions,
                                )
                                st.session_state["ai_generated_result"] = {
                                    "text": result_text,
                                    "platform": target_platform,
                                    "timestamp": datetime.now().strftime("%H:%M"),
                                    "key": f"{selected_folder_name}_{target_platform}_{datetime.now().strftime('%H%M%S%f')}",
                                }
                                out_name = f"{selected_folder_name}_{target_platform}_listing.txt"
                                out_path = Path(folder_info["folder_path"]) / out_name
                                with open(out_path, "w", encoding="utf-8") as f:
                                    f.write(result_text)
                                st.toast(f"Saved to {out_name}")
                    except Exception as e:
                        st.error(f"Generation failed: {e}")

                res = st.session_state.get("ai_generated_result")
                if res:
                    st.caption(f"Generated for **{res['platform']}** at {res['timestamp']}")
                    st.text_area("Output", value=res["text"], height=420, key=f"ai_result_area_{res.get('key', '')}")
                    st.download_button(
                        "Download .txt",
                        data=res["text"],
                        file_name=f"listing_{res['platform']}.txt",
                        key="ai_download",
                    )
                else:
                    st.info("Select a product on the left and click **Generate description**.")

    # ----- Assistant -------------------------------------------------------
    with ai_tab2:
        folders = file_manager.get_existing_product_folders()
        context_folder = None
        if folders:
            names = ["(none)"] + [f["folder_name"] for f in folders]
            chosen = st.selectbox("Listing context", names, key="chat_ctx_folder")
            if chosen != "(none)":
                context_folder = next((f for f in folders if f["folder_name"] == chosen), None)

        if "lbc_chat" not in st.session_state:
            st.session_state["lbc_chat"] = []

        for msg in st.session_state["lbc_chat"]:
            with st.chat_message(msg["role"]):
                st.markdown(msg["content"])

        prompt = st.chat_input("Ask about the listing, request a description, etc.")
        if prompt:
            st.session_state["lbc_chat"].append({"role": "user", "content": prompt})
            with st.chat_message("user"):
                st.markdown(prompt)

            context = None
            if context_folder:
                files = context_folder.get("text_files", [])
                src = "raw_scrape.txt" if "raw_scrape.txt" in files else (files[0] if files else None)
                if src:
                    raw = file_manager.load_product_text(context_folder["folder_path"], src)
                    if raw:
                        context = {"listing": raw[:4000]}

            with st.chat_message("assistant"):
                with st.spinner("Thinking..."):
                    try:
                        reply = GroqProcessor(groq_api_key).chat_with_ai(prompt, context=context)
                    except Exception as e:
                        reply = f"Sorry, I hit an error: {e}"
                    st.markdown(reply)
            st.session_state["lbc_chat"].append({"role": "assistant", "content": reply})


def main():
    st.set_page_config(page_title="LEBONCOIN SCRAPER", layout="wide", initial_sidebar_state="expanded")
    inject_global_styles()

    st.markdown(
        """
        <div class="es-hero">
            <div class="es-badge">Leboncoin · v1.0</div>
            <h1>Leboncoin Scraper Studio</h1>
            <p>Extract listings, download photos and generate platform-tuned descriptions.</p>
        </div>
        """,
        unsafe_allow_html=True,
    )

    try:
        scraper, file_manager = initialize_components()
    except Exception as e:
        st.error(f"Failed to initialize application: {e}")
        return

    NAV_OPTIONS = ["Single Product", "Batch Processing", "AI Processing", "Image Format", "Logs"]

    with st.sidebar:
        st.markdown(
            """
            <div class="es-side-brand">
                <div class="es-logo">lbc</div>
                <div>
                    <div class="es-side-title">Leboncoin Studio</div>
                    <div class="es-side-sub">Scraper · AI · Images</div>
                </div>
            </div>
            """,
            unsafe_allow_html=True,
        )
        st.markdown('<div class="es-side-section">Configuration</div>', unsafe_allow_html=True)
        st.caption(f"Storage: local CSV ({LEBONCOIN_CSV})")

        stored_key = load_groq_api_key()
        groq_api_key = st.text_input("Groq API key", value=stored_key, type="password", help="Required for AI features")
        save_key = st.checkbox("Save key to this project", value=bool(groq_api_key))
        if save_key and groq_api_key and groq_api_key != stored_key:
            if save_groq_api_key(groq_api_key):
                st.success("Saved")
            else:
                st.warning("Could not save key locally")
        if groq_api_key:
            st.success("Groq key set")
        else:
            st.info("Add key to enable AI features")

    tab1, tab2, tab3, tab_fmt, tab5 = st.tabs(NAV_OPTIONS)

    # --- Single Product ---
    with tab1:
        st.markdown(
            """
            <div class="es-card">
                <div class="es-card-title">Find a listing</div>
                <p class="es-card-sub">Paste any leboncoin.fr ad URL. Tracking parameters are stripped automatically.</p>
            </div>
            """,
            unsafe_allow_html=True,
        )
        col_a, col_b = st.columns([4, 1])
        with col_a:
            lbc_url = st.text_input(
                "Leboncoin listing URL",
                placeholder="https://www.leboncoin.fr/ad/accessoires_bagagerie/2494715054",
                label_visibility="collapsed",
                key="single_url_input",
            )
        with col_b:
            scrape_button = st.button("Start scraping", type="primary", use_container_width=True, key="single_scrape_btn")

        if scrape_button:
            handle_single_product_scrape(lbc_url, scraper, file_manager)

        save_phase = st.session_state.get("save_phase")
        if save_phase == "awaiting_name":
            _folder_name_dialog()
        elif save_phase == "persist":
            _persist_after_dialog(scraper, file_manager)

        with st.expander("Supported URL formats", expanded=False):
            st.markdown(
                """
- **Ad URL** &nbsp;`https://www.leboncoin.fr/ad/<category>/<id>`
- **Legacy** &nbsp;`https://www.leboncoin.fr/<category>/<id>.htm`
- **With tracking params** &nbsp;`?utm_source=...` (stripped automatically)
- **Mobile** &nbsp;`https://m.leboncoin.fr/...`
                """
            )

    # --- Batch Processing (reused generic queue) ---
    with tab2:
        render_batch_tab(scraper, file_manager)

    # --- AI Processing ---
    with tab3:
        _render_ai_tab(file_manager, groq_api_key)

    # --- Image Format (reused) ---
    with tab_fmt:
        render_image_format_tab(file_manager)

    # --- Logs ---
    with tab5:
        st.markdown("**Application logs**")
        log_path = Path("ebay_scraper.log")
        if log_path.exists():
            try:
                lines = log_path.read_text(encoding="utf-8", errors="ignore").splitlines()
                st.code("\n".join(lines[-300:]) or "(empty)", language="text")
            except Exception as e:
                st.error(f"Could not read log: {e}")
        else:
            st.info("No log file yet.")


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        st.error(f"Application error: {e}")
        logger.critical(f"Application startup error: {traceback.format_exc()}")
