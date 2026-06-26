"""
Multi-Platform Product Scraper Studio
=====================================

A Streamlit application that scrapes full product details (title, price,
condition/availability, brand, images, specifications and description) from
multiple e-commerce marketplaces and turns them into clean, platform-optimized
listings with AI.

Supported source marketplaces (selectable from a dropdown):

    • Temu          (temu.com)
    • Alibaba       (alibaba.com)
    • AliExpress    (aliexpress.com / aliexpress.us)
    • Shein         (shein.com)

This module deliberately mirrors the architecture of ``ebay_scraper.py`` so the
two tools feel identical to use. It re-uses the shared building blocks
(``ProductData``, ``ScrapingResult``, the AI ``PlatformAgent`` / ``GroqProcessor``
and the ``FileManager``) and adds a small, robust scraper class per marketplace.

Run it with:

    streamlit run multi_platform_scraper.py
"""

from __future__ import annotations

import os
import re
import csv
import json
import time
import random
import logging
import traceback
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Tuple, Type
from urllib.parse import urlparse, urljoin, parse_qs

import requests
import streamlit as st
from bs4 import BeautifulSoup, Tag

# ---------------------------------------------------------------------------
# Re-use the battle-tested infrastructure already implemented for eBay so the
# two scrapers stay perfectly in sync (same data model, same AI engine, same
# file handling and the same global styling).
# ---------------------------------------------------------------------------
from ebay_scraper import (
    ProductData,
    ScrapingResult,
    ScrapingError,
    ValidationError,
    NetworkError,
    DataExtractionError,
    ResponseCache,
    PlatformAgent,
    GroqProcessor,
    FileManager,
    NoProxyHTTPAdapter,
    REQUEST_HEADERS,
    safe_request,
    clean_filename,
    ensure_directory,
    load_groq_api_key,
    save_groq_api_key,
    inject_global_styles,
)

logger = logging.getLogger(__name__)

# Where multi-platform rows are appended (kept separate from the eBay CSV).
MULTI_CSV_FILENAME = "MultiPlatform_Products.csv"


# =============================================================================
# BASE SCRAPER
# =============================================================================
class BaseScraper:
    """
    Shared scraping engine for JavaScript-heavy marketplaces.

    Each marketplace (Temu, Alibaba, AliExpress, Shein) subclasses this and only
    declares its domains, image-CDN hosts and id patterns. The heavy lifting —
    fetching, structured-data parsing, image discovery and downloading — lives
    here so behaviour is consistent across every platform.

    Extraction uses a layered, best-effort strategy (the same philosophy as the
    eBay scraper): JSON-LD → OpenGraph/meta → embedded page JSON → CSS
    selectors. Whatever a page exposes, we try to read it.
    """

    # ---- Per-platform configuration (overridden by subclasses) -------------
    PLATFORM_KEY: str = "generic"
    DISPLAY_NAME: str = "Generic"
    ICON: str = "🛒"
    DOMAINS: Tuple[str, ...] = ()
    IMAGE_HOSTS: Tuple[str, ...] = ()
    ID_PATTERNS: Tuple[str, ...] = ()
    EXAMPLE_URL: str = ""
    # Substrings that mark a URL as a *product* page (not homepage/search/cart).
    PRODUCT_URL_HINTS: Tuple[str, ...] = ()
    # Only keep images whose URL contains one of these path fragments (when set).
    # This is the single most effective filter for dropping logos / UI icons that
    # live on the same CDN as the real product photos.
    IMAGE_PATH_HINTS: Tuple[str, ...] = ()
    # CSS selectors for the product image gallery, tried first (highest signal).
    GALLERY_SELECTORS: Tuple[str, ...] = ()
    # A selector Playwright waits for so we know the product actually rendered.
    WAIT_SELECTOR: str = "h1"
    # Currency tokens used when sniffing prices out of free text / JSON.
    CURRENCY_TOKENS = ("$", "£", "€", "¥", "₹", "US $", "USD", "EUR", "GBP", "AED", "PKR")

    def __init__(self) -> None:
        self.session = requests.Session()
        # Bypass any system / corporate proxy exactly like the eBay scraper.
        self.session.mount("http://", NoProxyHTTPAdapter())
        self.session.mount("https://", NoProxyHTTPAdapter())
        self.session.proxies = {}
        self.session.headers.update(REQUEST_HEADERS)
        logger.info("%s scraper initialized", self.DISPLAY_NAME)

    # ------------------------------------------------------------------ URLs
    def validate_url(self, url: str) -> bool:
        """Validate the URL belongs to this marketplace. Raises ValidationError."""
        if not url or not isinstance(url, str):
            raise ValidationError("URL must be a non-empty string")

        url = url.strip().strip("<>\"'")
        if not url:
            raise ValidationError("URL is empty")

        if not re.match(r"^[a-zA-Z]+://", url):
            url = "https://" + url

        try:
            parsed = urlparse(url)
        except Exception as exc:  # pragma: no cover - defensive
            raise ValidationError(f"Could not parse URL: {exc}")

        netloc = parsed.netloc.lower().split(":")[0]
        for prefix in ("www.", "m.", "us.", "de.", "fr.", "es.", "it.", "pt."):
            if netloc.startswith(prefix):
                netloc = netloc[len(prefix):]
                break

        if not netloc:
            raise ValidationError("URL is missing a domain")

        if not any(netloc == d or netloc.endswith("." + d) for d in self.DOMAINS):
            raise ValidationError(
                f"URL must be from {self.DISPLAY_NAME} "
                f"(expected one of: {', '.join(self.DOMAINS)})"
            )

        # Reject homepage / search / category / ad-redirect links. A real product
        # page either matches a product-id pattern or contains a product hint.
        path_q = ((parsed.path or "") + "?" + (parsed.query or "")).lower()
        has_hint = (
            bool(self.extract_item_id(url))
            or any(h in path_q for h in self.PRODUCT_URL_HINTS)
        )
        if not has_hint:
            raise ValidationError(
                f"This doesn't look like a {self.DISPLAY_NAME} *product* page "
                "(it may be a homepage, search, category or ad-redirect link). "
                "Open the product itself and copy the full URL from your browser's "
                f"address bar — it should contain the product id, e.g. "
                f"{self.EXAMPLE_URL}"
            )
        return True

    def extract_item_id(self, url: str) -> str:
        """Best-effort product id extraction from the URL."""
        if not url:
            return ""
        try:
            for pattern in self.ID_PATTERNS:
                m = re.search(pattern, url)
                if m:
                    return m.group(1)
            # Common query-param ids used across these marketplaces.
            query = parse_qs(urlparse(url).query or "")
            for key in ("goods_id", "productId", "product_id", "id", "spu_id", "skuId"):
                if key in query and query[key]:
                    digits = re.sub(r"\D", "", query[key][0])
                    if digits:
                        return digits
            # Fallback: longest digit run in the path.
            runs = re.findall(r"\d{6,}", urlparse(url).path)
            if runs:
                return max(runs, key=len)
        except Exception:
            pass
        return ""

    # --------------------------------------------------------------- fetching
    @staticmethod
    def playwright_available() -> bool:
        """True if Playwright (the headless-browser engine) is importable."""
        try:
            import playwright  # noqa: F401
            return True
        except Exception:
            return False

    def _fetch_rendered(self, url: str) -> Tuple[Optional[str], Optional[str]]:
        """
        Render the page in a real headless Chromium via Playwright and return
        (html, final_url). This is essential for Temu / Alibaba / AliExpress /
        Shein, which build their pages with JavaScript. Returns (None, None)
        when Playwright is not installed or the render fails.
        """
        try:
            from playwright.sync_api import sync_playwright
        except Exception:
            return None, None

        launch_args = [
            "--no-sandbox",
            "--disable-blink-features=AutomationControlled",
            "--disable-dev-shm-usage",
        ]

        try:
            with sync_playwright() as pw:
                try:
                    browser = pw.chromium.launch(headless=True, args=launch_args)
                except Exception as launch_exc:
                    # The matching browser build may be missing (e.g. "playwright
                    # install" not run, or a revision mismatch). Fall back to any
                    # Chromium/Chrome we can find on disk before giving up.
                    exe = self._find_chromium_executable()
                    if not exe:
                        logger.warning(
                            "Playwright browser not found (%s). Run "
                            "'playwright install chromium'.", launch_exc,
                        )
                        return None, None
                    browser = pw.chromium.launch(
                        headless=True, args=launch_args, executable_path=exe
                    )
                context = browser.new_context(
                    user_agent=REQUEST_HEADERS["User-Agent"],
                    locale="en-US",
                    viewport={"width": 1366, "height": 900},
                    extra_http_headers={"Accept-Language": "en-US,en;q=0.9"},
                )
                # Light stealth: hide the webdriver flag many anti-bots look for.
                context.add_init_script(
                    "Object.defineProperty(navigator,'webdriver',{get:()=>undefined});"
                )
                page = context.new_page()
                page.goto(url, wait_until="domcontentloaded", timeout=45000)
                # Give the SPA a chance to paint the product.
                try:
                    page.wait_for_selector(self.WAIT_SELECTOR, timeout=10000)
                except Exception:
                    pass
                # Scroll to trigger lazy-loaded gallery images.
                for _ in range(5):
                    page.mouse.wheel(0, 2500)
                    page.wait_for_timeout(600)
                try:
                    page.wait_for_load_state("networkidle", timeout=8000)
                except Exception:
                    pass
                html = page.content()
                final_url = page.url
                context.close()
                browser.close()
                return html, final_url
        except Exception as exc:
            logger.warning("Playwright render failed for %s: %s", self.DISPLAY_NAME, exc)
            return None, None

    @staticmethod
    def _find_chromium_executable() -> Optional[str]:
        """Locate a Chromium/Chrome binary when Playwright's own build is absent."""
        import glob
        import shutil

        candidates: List[str] = []
        base = os.environ.get("PLAYWRIGHT_BROWSERS_PATH", "")
        if base:
            candidates += glob.glob(os.path.join(base, "chromium-*/chrome-linux/chrome"))
            candidates += glob.glob(os.path.join(base, "chromium-*/chrome-win/chrome.exe"))
            candidates += glob.glob(os.path.join(
                base, "chromium-*/chrome-mac/Chromium.app/Contents/MacOS/Chromium"))
        for name in ("chromium", "chromium-browser", "google-chrome",
                     "google-chrome-stable", "chrome"):
            found = shutil.which(name)
            if found:
                candidates.append(found)
        # Common Windows install locations.
        for path in (
            r"C:\Program Files\Google\Chrome\Application\chrome.exe",
            r"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",
        ):
            candidates.append(path)
        for exe in candidates:
            if exe and os.path.exists(exe):
                return exe
        return None

    def scrape_product(self, url: str) -> ScrapingResult:
        """Main entry point: validate, fetch (browser-first), parse and return."""
        try:
            self.validate_url(url)
            url = url.strip().strip("<>\"'")
            if not re.match(r"^[a-zA-Z]+://", url):
                url = "https://" + url

            time.sleep(random.uniform(0.3, 1.0))

            # 1) Preferred path: render with a real browser so JS-built product
            #    content actually exists in the HTML we parse.
            html, final_url = self._fetch_rendered(url)
            used_browser = html is not None

            # 2) Fallback: plain HTTP (works only for pages that ship structured
            #    data server-side; kept so the tool still does *something* without
            #    Playwright installed).
            if html is None:
                response = safe_request(self.session, url, timeout=30)
                if not response:
                    return ScrapingResult(
                        success=False,
                        error_message=(
                            f"Could not load this {self.DISPLAY_NAME} page.\n\n"
                            + self._playwright_hint()
                        ),
                    )
                if response.status_code == 404:
                    return ScrapingResult(
                        success=False,
                        error_message=f"This {self.DISPLAY_NAME} listing was not found (404).",
                    )
                html = response.text
                final_url = response.url

            soup = BeautifulSoup(html, "html.parser")
            page_text = soup.get_text(" ", strip=True).lower()
            low_html = html.lower()
            if (
                "px-captcha" in low_html
                or "/_sec/cp_challenge" in low_html
                or "verify you are a human" in page_text
                or "are you a robot" in page_text
                or "access denied" in page_text[:2000]
            ):
                return ScrapingResult(
                    success=False,
                    error_message=(
                        f"{self.DISPLAY_NAME} blocked this request with anti-bot "
                        "verification. Wait a minute and retry; opening the product "
                        "once in a normal browser first can also help."
                    ),
                )

            product = self.extract_product_data(soup, html, final_url or url)
            images = self.get_product_images(soup, html, final_url or url)
            product.item_specifics.setdefault("Source Platform", self.DISPLAY_NAME)

            if not product.title:
                hint = "" if used_browser else "\n\n" + self._playwright_hint()
                extra = (
                    " The page rendered but exposed no product data — it may be a "
                    "login wall, a region/redirect page, or behind anti-bot."
                    if used_browser else ""
                )
                return ScrapingResult(
                    success=False,
                    error_message=(
                        f"Could not extract a product title from {self.DISPLAY_NAME}."
                        + extra + hint
                    ),
                )

            return ScrapingResult(success=True, product_data=product, image_urls=images)

        except ValidationError as exc:
            return ScrapingResult(success=False, error_message=f"{exc}")
        except NetworkError as exc:
            return ScrapingResult(success=False, error_message=f"Network error: {exc}")
        except DataExtractionError as exc:
            return ScrapingResult(success=False, error_message=f"Could not extract data: {exc}")
        except Exception:  # pragma: no cover - defensive
            logger.error("Unexpected error in scrape_product: %s", traceback.format_exc())
            return ScrapingResult(
                success=False,
                error_message="An unexpected error occurred. Please try again.",
            )

    @staticmethod
    def _playwright_hint() -> str:
        return (
            "These marketplaces build their pages with JavaScript, so the headless "
            "browser engine **Playwright** is required. Install it once:\n\n"
            "```\npip install playwright\nplaywright install chromium\n```\n\n"
            "Then restart the app and try again."
        )

    # ------------------------------------------------------- data extraction
    def extract_product_data(self, soup: BeautifulSoup, html: str, url: str) -> ProductData:
        """Build a ProductData by layering every available data source."""
        try:
            product = ProductData(url=url)
            ld = self._collect_jsonld_products(soup)
            og = self._collect_meta(soup)

            # Title
            product.title = (
                self._first(ld.get("name"))
                or og.get("og:title")
                or og.get("twitter:title")
                or self._text(soup.select_one("h1"))
                or (soup.title.get_text(strip=True) if soup.title else "")
            ).strip()

            # Price
            product.price = self._extract_price(ld, og, soup, html)

            # Brand
            brand = self._first(ld.get("brand"))
            if isinstance(ld.get("brand"), dict):
                brand = ld["brand"].get("name", "")
            product.brand = (brand or og.get("product:brand") or "").strip()

            # Availability / condition
            offers = ld.get("offers") or {}
            if isinstance(offers, list) and offers:
                offers = offers[0]
            availability = ""
            if isinstance(offers, dict):
                availability = str(offers.get("availability", "")).split("/")[-1]
                itemcond = str(offers.get("itemCondition", "")).split("/")[-1]
                product.condition = self._humanize(itemcond) or self._humanize(availability)
            if not product.condition:
                product.condition = self._humanize(availability) or "New"

            # Seller / shop
            seller = ""
            if isinstance(offers, dict):
                seller_obj = offers.get("seller")
                if isinstance(seller_obj, dict):
                    seller = seller_obj.get("name", "")
            product.seller = (seller or self._platform_seller(soup, html)).strip()

            # Description
            product.description = self._extract_description(ld, og, soup)

            # Category / breadcrumbs
            product.category = self._extract_category(ld, soup)

            # Item specifics (key/value attributes)
            product.item_specifics = self._extract_specifics(ld, soup, html)
            if product.brand:
                product.item_specifics.setdefault("Brand", product.brand)

            # Currency, rating, sku as helpful specifics
            if isinstance(offers, dict):
                if offers.get("priceCurrency"):
                    product.item_specifics.setdefault("Currency", str(offers["priceCurrency"]))
            sku = self._first(ld.get("sku")) or self._first(ld.get("mpn"))
            if sku:
                product.item_specifics.setdefault("SKU", str(sku))
            rating = ld.get("aggregateRating")
            if isinstance(rating, dict) and rating.get("ratingValue"):
                product.item_specifics.setdefault(
                    "Rating",
                    f"{rating.get('ratingValue')} ({rating.get('reviewCount', rating.get('ratingCount', '?'))} reviews)",
                )

            product.item_id = self.extract_item_id(url)
            logger.info(
                "Extracted %s product: %s... (id=%s)",
                self.DISPLAY_NAME, product.title[:50], product.item_id,
            )
            return product
        except Exception as exc:
            logger.error("Error extracting product data: %s", exc)
            raise DataExtractionError(str(exc))

    # ----------------------------------------------------------------- images
    def get_product_images(self, soup: BeautifulSoup, html: str, url: str,
                           max_images: int = 30) -> List[str]:
        """
        Discover *product* image URLs only.

        Priority order, each more reliable than the next as a signal that the
        image actually belongs to the product (not site chrome):
            1. The product image gallery (per-platform selectors)
            2. JSON-LD `image`
            3. OpenGraph / twitter image
            4. Embedded JSON / raw HTML matching the product CDN + path hints
            5. <img> tags (last resort, same strict filtering applies)

        Every candidate must pass `_is_valid_image`, which drops logos, icons,
        sprites, payment badges and anything off the product CDN. Results are
        de-duplicated by image identity (ignoring resize suffixes).
        """
        images: List[str] = []
        seen_keys = set()

        def add(candidate: Optional[str]) -> None:
            if not candidate:
                return
            candidate = candidate.strip().replace("\\/", "/").replace("\\u002F", "/")
            if candidate.startswith("//"):
                candidate = "https:" + candidate
            elif candidate.startswith("/"):
                candidate = urljoin(url, candidate)
            candidate = self.get_high_res_image_url(candidate)
            if not self._is_valid_image(candidate):
                return
            key = self._image_key(candidate)
            if key in seen_keys:
                return
            seen_keys.add(key)
            images.append(candidate)

        # 1) Gallery DOM (strongest product signal)
        for selector in self.GALLERY_SELECTORS:
            for container in soup.select(selector):
                for img in container.select("img"):
                    for attr in ("src", "data-src", "data-lazy-src", "data-zoom-src", "data-image"):
                        if img.get(attr):
                            add(img.get(attr))
                    srcset = img.get("srcset")
                    if srcset:
                        add(srcset.split(",")[-1].strip().split(" ")[0])

        # 2) JSON-LD images
        ld = self._collect_jsonld_products(soup)
        ld_images = ld.get("image")
        if isinstance(ld_images, str):
            add(ld_images)
        elif isinstance(ld_images, list):
            for img in ld_images:
                add(img if isinstance(img, str) else (img.get("url") if isinstance(img, dict) else None))

        # 3) OpenGraph / twitter images
        for meta in soup.select('meta[property="og:image"], meta[property="og:image:secure_url"], meta[name="twitter:image"]'):
            add(meta.get("content"))

        # 4) Embedded JSON / raw HTML — product CDN hosts (+ path hints) only.
        for found in self._regex_images_from_text(html):
            add(found)

        # 5) <img> tags (last resort, still strictly filtered).
        if not images:
            for img in soup.select("img"):
                add(img.get("src") or img.get("data-src") or img.get("data-lazy-src"))

        images = images[:max_images]
        logger.info("Found %d product images on %s", len(images), self.DISPLAY_NAME)
        return images

    @staticmethod
    def _image_key(url: str) -> str:
        """Identity of an image ignoring host and resize suffixes, for dedup."""
        path = urlparse(url).path.lower()
        stem = path.rsplit("/", 1)[-1]
        stem = re.sub(r"_\d{2,4}x\d{2,4}.*", "", stem)
        stem = re.sub(r"\.(jpg|jpeg|png|webp)$", "", stem)
        return stem or url.lower()

    def _regex_images_from_text(self, html: str) -> List[str]:
        """Find image URLs hosted on this platform's CDN inside raw text/JSON."""
        if not self.IMAGE_HOSTS:
            return []
        hosts = "|".join(re.escape(h) for h in self.IMAGE_HOSTS)
        # Matches https://host/...jpg|png|webp|jpeg, including escaped slashes.
        pattern = re.compile(
            r'(?:https?:)?(?:\\?/\\?/|//)(?:' + hosts + r')[^\s"\'<>\\]+?\.(?:jpg|jpeg|png|webp)',
            re.IGNORECASE,
        )
        results = []
        for raw in pattern.findall(html):
            cleaned = raw.replace("\\/", "/")
            if cleaned.startswith("//"):
                cleaned = "https:" + cleaned
            results.append(cleaned)
        return results

    def _is_valid_image(self, url: str) -> bool:
        low = url.lower()
        if low.startswith("data:"):
            return False
        if not any(ext in low for ext in (".jpg", ".jpeg", ".png", ".webp")):
            return False
        if ".svg" in low or ".gif" in low:
            return False
        # Generic non-product assets that show up across these sites.
        bad = (
            "sprite", "logo", "icon", "placeholder", "blank", "loading", "avatar",
            "/1x1", "pixel", "favicon", "banner", "payment", "visa", "mastercard",
            "paypal", "appstore", "app-store", "google-play", "googleplay", "qrcode",
            "qr_code", "/qr", "download", "flag_", "/flags/", "coin", "/cms/", "/ui/",
            "watermark", "thumbnail_220", "_50x50", "_60x60", "_80x80", "_90x90",
            "_100x100", "_.gif", "rating", "star",
        )
        if any(b in low for b in bad):
            return False
        # Must be on the platform's product image CDN (drops third-party chrome).
        if self.IMAGE_HOSTS and not any(h in low for h in self.IMAGE_HOSTS):
            return False
        # When a product-path hint is configured, require it — this is what
        # separates real product photos from same-CDN UI icons (e.g. AliExpress
        # product images live under /kf/).
        if self.IMAGE_PATH_HINTS and not any(h in low for h in self.IMAGE_PATH_HINTS):
            return False
        return True

    def get_high_res_image_url(self, img_url: str) -> str:
        """Upgrade thumbnail URLs to the largest available variant when possible."""
        try:
            url = img_url
            # AliExpress / Alibaba: strip size suffixes like _220x220.jpg or _.webp
            url = re.sub(r"_\d{2,4}x\d{2,4}(?:xz)?(?:q\d+)?(\.(?:jpg|jpeg|png|webp))", r"\1", url, flags=re.IGNORECASE)
            url = re.sub(r"_\d{2,4}x\d{2,4}\.(jpg|jpeg|png|webp)_?\.webp", r".\1", url, flags=re.IGNORECASE)
            # Shein: thumbnails carry _thumbnail_<w>x<h>
            url = re.sub(r"_thumbnail_\d+x\d+", "", url, flags=re.IGNORECASE)
            return url
        except Exception:
            return img_url

    def download_image(self, img_url: str, save_path: str) -> Optional[str]:
        """Download a single image, choosing the extension from the response."""
        try:
            response = safe_request(self.session, img_url, timeout=30)
            if not response:
                return None
            content_type = response.headers.get("Content-Type", "").lower()
            ext = self._image_extension(content_type, img_url)
            final_path = f"{save_path}.{ext}"
            with open(final_path, "wb") as fh:
                fh.write(response.content)
            return final_path
        except Exception as exc:
            logger.error("Error downloading image %s: %s", img_url, exc)
            return None

    @staticmethod
    def _image_extension(content_type: str, url: str) -> str:
        if "png" in content_type:
            return "png"
        if "webp" in content_type:
            return "webp"
        if "jpeg" in content_type or "jpg" in content_type:
            return "jpg"
        path = urlparse(url).path.lower()
        ext = os.path.splitext(path)[1].lstrip(".")
        if ext in {"jpg", "jpeg", "png", "webp"}:
            return "jpg" if ext == "jpeg" else ext
        return "jpg"

    # -------------------------------------------------- structured-data helpers
    def _collect_jsonld_products(self, soup: BeautifulSoup) -> Dict:
        """Return the first JSON-LD object that looks like a Product."""
        for script in soup.select('script[type="application/ld+json"]'):
            raw = script.string or script.get_text()
            if not raw:
                continue
            try:
                data = json.loads(raw)
            except Exception:
                # Some sites embed multiple objects or trailing commas; try lenient.
                try:
                    data = json.loads(re.sub(r",\s*([}\]])", r"\1", raw))
                except Exception:
                    continue
            for obj in self._iter_jsonld(data):
                t = obj.get("@type", "")
                types = t if isinstance(t, list) else [t]
                if any(str(x).lower() == "product" for x in types):
                    return obj
        return {}

    @staticmethod
    def _iter_jsonld(data):
        if isinstance(data, dict):
            if "@graph" in data and isinstance(data["@graph"], list):
                for item in data["@graph"]:
                    yield from BaseScraper._iter_jsonld(item)
            yield data
        elif isinstance(data, list):
            for item in data:
                yield from BaseScraper._iter_jsonld(item)

    @staticmethod
    def _collect_meta(soup: BeautifulSoup) -> Dict[str, str]:
        meta: Dict[str, str] = {}
        for tag in soup.select("meta"):
            key = tag.get("property") or tag.get("name")
            if key and tag.get("content"):
                meta[key.lower()] = tag["content"]
        return meta

    def _extract_price(self, ld: Dict, og: Dict, soup: BeautifulSoup, html: str) -> str:
        offers = ld.get("offers") or {}
        if isinstance(offers, list) and offers:
            offers = offers[0]
        if isinstance(offers, dict):
            price = offers.get("price") or offers.get("lowPrice")
            currency = offers.get("priceCurrency", "")
            if price:
                symbol = {"USD": "$", "GBP": "£", "EUR": "€", "AED": "AED ", "PKR": "₨"}.get(str(currency), "")
                return f"{symbol}{price}".strip() if symbol else f"{price} {currency}".strip()
        for key in ("product:price:amount", "og:price:amount"):
            if og.get(key):
                cur = og.get("product:price:currency", og.get("og:price:currency", ""))
                return f"{og[key]} {cur}".strip()
        # Sniff a currency-prefixed number out of the raw HTML.
        m = re.search(r"(US\s?\$|\$|£|€|¥|₹|AED|PKR|Rs\.?)\s?\d[\d,]*\.?\d*", html)
        if m:
            return m.group(0).strip()
        return ""

    def _extract_description(self, ld: Dict, og: Dict, soup: BeautifulSoup) -> str:
        desc = self._first(ld.get("description")) or og.get("og:description") or og.get("description") or ""
        if not desc:
            node = soup.select_one(
                '[class*="description"], [id*="description"], [class*="detail"], [class*="productDesc"]'
            )
            if node:
                desc = node.get_text(" ", strip=True)
        return (desc or "")[:5000]

    def _extract_category(self, ld: Dict, soup: BeautifulSoup) -> str:
        cat = self._first(ld.get("category"))
        if cat:
            return str(cat)
        crumbs = soup.select('nav[aria-label*="readcrumb" i] a, [class*="breadcrumb" i] a')
        names = [c.get_text(strip=True) for c in crumbs if c.get_text(strip=True)]
        return " > ".join(names[:6])

    def _extract_specifics(self, ld: Dict, soup: BeautifulSoup, html: str) -> Dict[str, str]:
        specifics: Dict[str, str] = {}

        # JSON-LD additionalProperty list
        for prop in ld.get("additionalProperty", []) or []:
            if isinstance(prop, dict) and prop.get("name") and prop.get("value") is not None:
                specifics[str(prop["name"]).strip()] = str(prop["value"]).strip()

        # Common JSON-LD scalar attributes
        for key in ("color", "material", "size", "model", "gtin", "weight"):
            val = ld.get(key)
            if val:
                specifics.setdefault(key.capitalize(), self._first(val) or str(val))

        # Definition lists & spec tables in the DOM
        for container in soup.select('dl, table, [class*="spec" i], [class*="attribute" i], [class*="prop" i]'):
            dts = container.select("dt")
            dds = container.select("dd")
            if dts and dds and len(dts) == len(dds):
                for dt, dd in zip(dts, dds):
                    k = dt.get_text(" ", strip=True)
                    v = dd.get_text(" ", strip=True)
                    if k and v and len(k) < 60:
                        specifics.setdefault(k, v)
            for row in container.select("tr"):
                cells = row.select("td, th")
                if len(cells) >= 2:
                    k = cells[0].get_text(" ", strip=True)
                    v = cells[1].get_text(" ", strip=True)
                    if k and v and len(k) < 60:
                        specifics.setdefault(k, v)

        return specifics

    # Subclasses may override to read a shop/store name from page JSON.
    def _platform_seller(self, soup: BeautifulSoup, html: str) -> str:
        return ""

    # ----------------------------------------------------------- tiny helpers
    @staticmethod
    def _first(value):
        if isinstance(value, list):
            return value[0] if value else ""
        return value if value is not None else ""

    @staticmethod
    def _text(node: Optional[Tag]) -> str:
        return node.get_text(" ", strip=True) if node else ""

    @staticmethod
    def _humanize(token: str) -> str:
        token = (token or "").strip()
        if not token:
            return ""
        mapping = {
            "InStock": "In stock",
            "OutOfStock": "Out of stock",
            "PreOrder": "Pre-order",
            "NewCondition": "New",
            "UsedCondition": "Used",
            "RefurbishedCondition": "Refurbished",
        }
        if token in mapping:
            return mapping[token]
        # CamelCase -> spaced
        return re.sub(r"(?<!^)(?=[A-Z])", " ", token).strip()


# =============================================================================
# PLATFORM-SPECIFIC SCRAPERS
# =============================================================================
class TemuScraper(BaseScraper):
    PLATFORM_KEY = "temu"
    DISPLAY_NAME = "Temu"
    ICON = "🟠"
    DOMAINS = ("temu.com",)
    IMAGE_HOSTS = ("img.kwcdn.com", "aimg.kwcdn.com", "kwcdn.com")
    ID_PATTERNS = (r"-g-(\d+)\.html", r"goods_id=(\d+)", r"_g_(\d+)")
    PRODUCT_URL_HINTS = ("-g-", "/goods", "goods_id=")
    IMAGE_PATH_HINTS = ()  # product photos live across kwcdn paths; host filter is enough
    GALLERY_SELECTORS = ('[class*="gallery" i]', '[class*="Gallery" i]', '[class*="swiper" i]', "main")
    WAIT_SELECTOR = 'h1, [class*="goods" i], [class*="title" i]'
    EXAMPLE_URL = "https://www.temu.com/product-name-g-601099512123456.html"

    def _platform_seller(self, soup: BeautifulSoup, html: str) -> str:
        m = re.search(r'"mallName"\s*:\s*"([^"]+)"', html)
        return m.group(1) if m else "Temu"


class AlibabaScraper(BaseScraper):
    PLATFORM_KEY = "alibaba"
    DISPLAY_NAME = "Alibaba"
    ICON = "🟧"
    DOMAINS = ("alibaba.com",)
    IMAGE_HOSTS = ("alicdn.com", "sc04.alicdn.com", "s.alicdn.com", "cbu01.alicdn.com")
    ID_PATTERNS = (r"/product-detail/[^/]*?_?(\d{6,})\.html", r"/(\d{6,})\.html", r"productId=(\d+)")
    PRODUCT_URL_HINTS = ("/product-detail/", "productid=")
    IMAGE_PATH_HINTS = ()  # /imgextra/ covers products; host + excludes handle chrome
    GALLERY_SELECTORS = ('[class*="gallery" i]', '[class*="image" i][class*="module" i]',
                         '[class*="thumb" i]', '[class*="main-image" i]')
    WAIT_SELECTOR = 'h1, [class*="product-title" i], [class*="title" i]'
    EXAMPLE_URL = "https://www.alibaba.com/product-detail/Product-Name_1600123456789.html"

    def _platform_seller(self, soup: BeautifulSoup, html: str) -> str:
        m = re.search(r'"companyName"\s*:\s*"([^"]+)"', html) or re.search(r'"company"\s*:\s*"([^"]+)"', html)
        return m.group(1) if m else ""


class AliExpressScraper(BaseScraper):
    PLATFORM_KEY = "aliexpress"
    DISPLAY_NAME = "AliExpress"
    ICON = "🔴"
    DOMAINS = ("aliexpress.com", "aliexpress.us", "aliexpress.ru")
    IMAGE_HOSTS = ("alicdn.com", "ae01.alicdn.com", "ae04.alicdn.com")
    ID_PATTERNS = (r"/item/(?:[^/]*?/)?(\d+)\.html", r"/i/(\d+)\.html", r"productId=(\d+)")
    PRODUCT_URL_HINTS = ("/item/", "/i/")
    # AliExpress product photos live under /kf/ — this single hint removes the
    # site logo, payment icons and other same-CDN chrome.
    IMAGE_PATH_HINTS = ("/kf/",)
    GALLERY_SELECTORS = ('[class*="gallery" i]', '[class*="slider--img" i]',
                         '[class*="image-view" i]', '[class*="magnifier" i]')
    WAIT_SELECTOR = 'h1, [class*="title--wrap" i], [data-pl="product-title"]'
    EXAMPLE_URL = "https://www.aliexpress.com/item/1005006123456789.html"

    def extract_product_data(self, soup: BeautifulSoup, html: str, url: str) -> ProductData:
        product = super().extract_product_data(soup, html, url)
        # AliExpress embeds a rich window.runParams blob; pull title/price if the
        # standard structured-data path came up empty.
        if not product.title or not product.price:
            m = re.search(r'"subject"\s*:\s*"([^"]+)"', html)
            if m and not product.title:
                product.title = m.group(1)
            mp = re.search(r'"formatedActivityPrice"\s*:\s*"([^"]+)"', html) or \
                re.search(r'"formatedPrice"\s*:\s*"([^"]+)"', html)
            if mp and not product.price:
                product.price = mp.group(1)
        return product

    def _platform_seller(self, soup: BeautifulSoup, html: str) -> str:
        m = re.search(r'"storeName"\s*:\s*"([^"]+)"', html)
        return m.group(1) if m else ""


class SheinScraper(BaseScraper):
    PLATFORM_KEY = "shein"
    DISPLAY_NAME = "Shein"
    ICON = "🖤"
    DOMAINS = ("shein.com", "shein.co.uk", "us.shein.com", "shein.in")
    IMAGE_HOSTS = ("img.ltwebstatic.com", "ltwebstatic.com", "img.shein.com", "sheinsz.ltwebstatic.com")
    ID_PATTERNS = (r"-p-(\d+)\.html", r"goods_id=(\d+)", r"-p-(\d+)-cat")
    PRODUCT_URL_HINTS = ("-p-", "goods_id=")
    IMAGE_PATH_HINTS = ()  # Shein product images sit under /images3_pi/ etc.; host filter is enough
    GALLERY_SELECTORS = ('[class*="gallery" i]', '[class*="swiper" i]',
                         '[class*="crop-image" i]', '[class*="product-intro__main" i]')
    WAIT_SELECTOR = 'h1, [class*="product-intro" i], [class*="goods" i]'
    EXAMPLE_URL = "https://www.shein.com/Product-Name-p-12345678.html"

    def extract_product_data(self, soup: BeautifulSoup, html: str, url: str) -> ProductData:
        product = super().extract_product_data(soup, html, url)
        if not product.title:
            m = re.search(r'"goods_name"\s*:\s*"([^"]+)"', html)
            if m:
                product.title = m.group(1)
        if not product.price:
            m = re.search(r'"salePrice"\s*:\s*\{[^}]*"amountWithSymbol"\s*:\s*"([^"]+)"', html)
            if m:
                product.price = m.group(1)
        return product


# Registry that powers the source-platform dropdown.
SCRAPERS: Dict[str, Type[BaseScraper]] = {
    TemuScraper.DISPLAY_NAME: TemuScraper,
    AlibabaScraper.DISPLAY_NAME: AlibabaScraper,
    AliExpressScraper.DISPLAY_NAME: AliExpressScraper,
    SheinScraper.DISPLAY_NAME: SheinScraper,
}


def get_scraper(display_name: str) -> BaseScraper:
    cls = SCRAPERS.get(display_name, TemuScraper)
    return cls()


# =============================================================================
# LOCAL CSV
# =============================================================================
def append_to_multi_csv(product: ProductData, platform: str,
                        filename: str = MULTI_CSV_FILENAME) -> bool:
    """Append a scraped product (with its source platform) to the shared CSV."""
    try:
        csv_path = Path.cwd() / filename
        is_new = not csv_path.exists()
        fields = [
            "platform", "title", "price", "condition", "brand", "seller",
            "category", "item_id", "url", "image_count", "scraped_at",
        ]
        with open(csv_path, "a", newline="", encoding="utf-8") as fh:
            writer = csv.DictWriter(fh, fieldnames=fields)
            if is_new:
                writer.writeheader()
            writer.writerow({
                "platform": platform,
                "title": product.title,
                "price": product.price,
                "condition": product.condition,
                "brand": product.brand,
                "seller": product.seller,
                "category": product.category,
                "item_id": product.item_id,
                "url": product.url,
                "image_count": len(product.item_specifics.get("__image_count__", "") or ""),
                "scraped_at": product.scraped_at,
            })
        return True
    except Exception as exc:
        logger.error("Error writing multi-platform CSV: %s", exc)
        return False


# =============================================================================
# STREAMLIT UI
# =============================================================================
def display_results(result: ScrapingResult, platform: str,
                    downloaded_images: List[str], folder_path: Path, csv_updated: bool):
    """Render a premium product card for the scraped item."""
    if not result.success or not result.product_data:
        st.error(f"Scraping failed: {result.error_message}")
        return

    pd = result.product_data
    main_image = result.image_urls[0] if result.image_urls else ""

    badges = f'<span class="status-badge">Images: {len(downloaded_images)}</span>'
    badges += f'<span class="status-badge">{platform}</span>'
    badges += ('<span class="status-badge">CSV: Saved</span>' if csv_updated
               else '<span class="status-badge neutral">CSV: Skipped</span>')

    st.markdown(f"""
    <div class="product-card">
        <div class="product-header">
            <h3 class="product-title">{pd.title}</h3>
        </div>
        <div class="product-body">
            <div class="product-image-container">
                <img src="{main_image}" class="product-image" onerror="this.style.display='none'"/>
            </div>
            <div class="product-details">
                <div class="price-tag">{pd.price or 'N/A'}</div>
                <div class="detail-row"><span class="detail-label">Availability</span>
                    <span class="detail-value">{pd.condition or 'N/A'}</span></div>
                <div class="detail-row"><span class="detail-label">Brand</span>
                    <span class="detail-value">{pd.brand or 'N/A'}</span></div>
                <div class="detail-row"><span class="detail-label">Seller / Store</span>
                    <span class="detail-value">{pd.seller or 'N/A'}</span></div>
                <div class="detail-row"><span class="detail-label">Category</span>
                    <span class="detail-value">{pd.category or 'N/A'}</span></div>
                <div class="status-section">{badges}</div>
            </div>
        </div>
    </div>
    """, unsafe_allow_html=True)

    # Image gallery
    if result.image_urls:
        st.markdown("#### 🖼️ Product Gallery")
        cols = st.columns(5)
        for i, img in enumerate(result.image_urls[:10]):
            with cols[i % 5]:
                st.image(img, use_container_width=True)

    with st.expander("📝 View Full Product Description", expanded=False):
        st.markdown(pd.description or "*No description available*")

    if pd.item_specifics:
        with st.expander("📋 View Item Specifics", expanded=True):
            html = '<div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(280px,1fr));gap:0.75rem;">'
            for key, value in pd.item_specifics.items():
                if key.startswith("__"):
                    continue
                html += f"""
                <div style="background:#f9fafb;padding:0.7rem;border-radius:8px;border:1px solid #f3f4f6;">
                    <div style="font-size:0.75rem;color:#6b7280;font-weight:600;text-transform:uppercase;letter-spacing:0.04em;">{key}</div>
                    <div style="font-size:0.92rem;color:#111827;font-weight:500;word-break:break-word;">{value}</div>
                </div>"""
            html += "</div>"
            st.markdown(html, unsafe_allow_html=True)

    st.success(f"📁 Data saved to: `{folder_path}`")


def handle_scrape(url: str, platform: str, file_manager: FileManager):
    """Orchestrate a single multi-platform scrape end to end."""
    if not url or not url.strip():
        st.error("⚠️ Please paste a product URL before clicking Start scraping.")
        return

    scraper = get_scraper(platform)

    # Allow forgiving input (quotes, multiple URLs).
    url = url.strip().strip("<>\"'")
    if any(ws in url for ws in (" ", "\t", "\n")):
        parts = [p for p in re.split(r"\s+", url) if p]
        if parts:
            url = parts[0]

    try:
        scraper.validate_url(url)
    except ValidationError as exc:
        st.error(f"❌ Invalid URL — {exc}")
        return

    progress = st.progress(0)
    status = st.empty()
    try:
        status.markdown(f"**🔍 Extracting product data from {platform}...**")
        progress.progress(15)
        result = scraper.scrape_product(url)

        if not result.success:
            status.empty()
            progress.empty()
            st.error(f"❌ Failed: {result.error_message}")
            return

        progress.progress(45)
        status.markdown("**📁 Setting up project workspace...**")
        folder_path = file_manager.create_product_folder(
            brand=result.product_data.brand or platform,
            item_id=result.product_data.item_id,
            fallback_title=result.product_data.title,
        )
        result.folder_path = str(folder_path)
        file_manager.save_product_description_markdown(result.product_data, folder_path)
        file_manager.save_product_text(result.product_data, folder_path)
        file_manager.save_raw_scrape_text(result.product_data, folder_path)

        progress.progress(65)
        status.markdown(f"**📸 Downloading {len(result.image_urls)} images...**")
        downloaded_images: List[str] = []
        if result.image_urls:
            downloaded_images = file_manager.download_images(
                scraper, result.image_urls, folder_path,
                progress_callback=lambda c, t: progress.progress(65 + int((c / t) * 20)),
            )
        result.product_data.item_specifics["__image_count__"] = "x" * len(downloaded_images)

        progress.progress(90)
        status.markdown("**📊 Saving to local CSV...**")
        csv_updated = append_to_multi_csv(result.product_data, platform)

        progress.progress(100)
        status.markdown("✅ **Success! Processing complete.**")
        time.sleep(0.6)
        status.empty()
        progress.empty()

        display_results(result, platform, downloaded_images, folder_path, csv_updated)
        st.balloons()
    except Exception as exc:
        status.empty()
        progress.empty()
        st.error(f"❌ An unexpected error occurred: {exc}")
        logger.error("Scrape handler error: %s", traceback.format_exc())


def render_scrape_tab(file_manager: FileManager):
    st.markdown(
        """
        <div class="es-card">
            <div class="es-card-title">🌐 Choose a marketplace & paste a product link</div>
            <p class="es-card-sub">Pick the source platform from the dropdown, paste a product URL,
            and we'll extract the title, price, images, specifications and description — then save
            everything locally and prep it for AI rewriting.</p>
        </div>
        """,
        unsafe_allow_html=True,
    )

    col_platform, col_url, col_btn = st.columns([1.1, 3, 1])

    with col_platform:
        platform = st.selectbox(
            "Source platform",
            options=list(SCRAPERS.keys()),
            format_func=lambda name: f"{SCRAPERS[name].ICON}  {name}",
            key="mp_platform",
        )
    scraper_cls = SCRAPERS[platform]

    with col_url:
        url = st.text_input(
            "Product URL",
            placeholder=scraper_cls.EXAMPLE_URL,
            label_visibility="visible",
            key="mp_url",
        )
    with col_btn:
        st.write("")
        st.write("")
        go = st.button("Start scraping", type="primary", use_container_width=True, key="mp_go")

    st.caption(f"Example {platform} URL:  `{scraper_cls.EXAMPLE_URL}`")

    # Browser-engine status — these sites need a real browser to render.
    if BaseScraper.playwright_available():
        st.caption("🟢 Browser engine ready (Playwright) — JavaScript pages will render fully.")
    else:
        st.warning(
            "🔴 **Playwright is not installed.** Temu / Alibaba / AliExpress / Shein build "
            "their pages with JavaScript, so a real browser engine is required to read them. "
            "Install it once, then restart the app:\n\n"
            "```\npip install playwright\nplaywright install chromium\n```"
        )

    if go:
        handle_scrape(url, platform, file_manager)

    with st.expander("ℹ️ Supported marketplaces & how to copy a good link", expanded=False):
        st.markdown(
            """
**Paste the product page URL from your browser's address bar** — not a search,
category, share or ad link.

- **🟠 Temu** — `https://www.temu.com/<name>-g-<id>.html`
- **🟧 Alibaba** — `https://www.alibaba.com/product-detail/<name>_<id>.html`
- **🔴 AliExpress** — `https://www.aliexpress.com/item/<id>.html`
- **🖤 Shein** — `https://www.shein.com/<name>-p-<id>.html`

**Why a real browser is used:** these marketplaces render everything with
JavaScript and run aggressive anti-bot protection. The app opens the page in a
headless Chromium (Playwright), waits for the product to load, then extracts the
title, price, specs, description and **only the product-gallery images** (logos,
payment badges and UI icons are filtered out). If a site still blocks the
request, you'll get a clear message instead of wrong data.
            """
        )


def render_ai_tab(file_manager: FileManager, groq_api_key: str):
    st.title("🤖 AI Content Studio")
    st.caption("Turn any scraped product into a clean, platform-optimized listing.")

    if not groq_api_key:
        st.warning("⚠️ Add a Groq API key in the sidebar to use AI features.")
        return

    folders = file_manager.get_existing_product_folders()
    if not folders:
        st.info("📂 No scraped products yet. Scrape one from the **Scrape Product** tab first.")
        return

    col_in, col_out = st.columns([1, 1.5], gap="large")
    with col_in:
        st.markdown("### 1. Select content")
        folder_names = [f["folder_name"] for f in folders]
        selected_folder = st.selectbox("Product folder", folder_names, key="mp_ai_folder")
        if st.session_state.get("mp_ai_last_folder") != selected_folder:
            st.session_state.mp_ai_result = None
            st.session_state.mp_ai_last_folder = selected_folder

        folder_info = next((f for f in folders if f["folder_name"] == selected_folder), None)
        selected_file = None
        if folder_info:
            files = folder_info.get("text_files", [])
            default_idx = next((i for i, f in enumerate(files) if "raw_scrape.txt" in f), 0)
            selected_file = st.selectbox("Source file", files, index=default_idx, key="mp_ai_file")

        st.markdown("### 2. Configure")
        target_platform = st.selectbox(
            "Target platform",
            ["General", "eBay", "Poshmark", "Mercari", "Depop", "Etsy",
             "Facebook Marketplace", "Shopify", "Vinted", "Grailed", "Instagram"],
            key="mp_ai_target",
        )
        with st.expander("Advanced instructions", expanded=False):
            custom_instructions = st.text_area(
                "Custom rules",
                placeholder="e.g. 'Use emojis', 'Focus on materials', 'Short & punchy'",
                height=80, key="mp_ai_custom",
            )
        st.divider()
        generate = st.button("✨ Generate description", type="primary",
                             use_container_width=True, key="mp_ai_gen")

    with col_out:
        st.markdown("### 3. Result")
        if "mp_ai_result" not in st.session_state:
            st.session_state.mp_ai_result = None

        if generate and folder_info and selected_file:
            content = file_manager.load_product_text(folder_info["folder_path"], selected_file)
            if not content:
                st.error("Empty source file.")
            else:
                with st.spinner(f"🔍 Rewriting for {target_platform}..."):
                    processor = GroqProcessor(groq_api_key)
                    text = processor.platform_agent.generate_platform_description(
                        raw_text=content, product_data=None,
                        platform=target_platform, custom_instructions=custom_instructions,
                    )
                    st.session_state.mp_ai_result = {
                        "text": text, "platform": target_platform,
                        "timestamp": datetime.now().strftime("%H:%M"),
                    }
                    out_name = f"{selected_folder}_{target_platform}_listing.txt"
                    with open(Path(folder_info["folder_path"]) / out_name, "w", encoding="utf-8") as fh:
                        fh.write(text)
                    st.toast(f"Saved to {out_name}", icon="💾")

        res = st.session_state.mp_ai_result
        if res:
            st.markdown(f"**Generated for {res['platform']} at {res['timestamp']}**")
            st.text_area("Final output", value=res["text"], height=480, key="mp_ai_output")
            st.download_button("📥 Download .txt", data=res["text"],
                               file_name=f"listing_{res['platform']}.txt")
        else:
            st.info("👈 Select a product and click Generate.")


def render_library_tab(file_manager: FileManager):
    st.title("📚 Scraped Library")
    csv_path = Path.cwd() / MULTI_CSV_FILENAME
    if csv_path.exists():
        try:
            import pandas as pd
            df = pd.read_csv(csv_path)
            st.dataframe(df, use_container_width=True, hide_index=True)
            st.download_button("📥 Download CSV", data=csv_path.read_bytes(),
                               file_name=MULTI_CSV_FILENAME, mime="text/csv")
        except Exception as exc:
            st.error(f"Could not read CSV: {exc}")
    else:
        st.info("No products scraped yet — your library is empty.")


def main():
    st.set_page_config(
        page_title="Multi-Platform Scraper",
        page_icon="🌐",
        layout="wide",
        initial_sidebar_state="expanded",
    )
    inject_global_styles()

    # When Google Fonts is blocked on the network, Streamlit's Material Symbols
    # icon font fails to load and expander / select carets render as raw ligature
    # text ("keyboard_arrow_right") that overlaps labels. Clamp those icon spans
    # so the broken text can never overflow onto neighbouring content.
    st.markdown(
        """
        <style>
        span[data-testid="stIconMaterial"],
        [data-testid="stExpanderToggleIcon"],
        .material-icons, .material-symbols-outlined,
        span[class*="material-symbols"] {
            max-width: 1.5rem !important;
            max-height: 1.5rem !important;
            overflow: hidden !important;
            white-space: nowrap !important;
            font-size: 1.1rem !important;
            line-height: 1.5rem !important;
            display: inline-flex !important;
            flex: 0 0 auto !important;
        }
        details summary { gap: 0.4rem !important; align-items: center !important; }
        </style>
        """,
        unsafe_allow_html=True,
    )

    st.markdown(
        """
        <div class="es-hero">
            <div class="es-badge">v1.0 · Temu · Alibaba · AliExpress · Shein</div>
            <h1>Multi-Platform Scraper Studio</h1>
            <p>Pick a marketplace, paste a product link, and pull every detail —
            then generate platform-tuned listings with AI.</p>
        </div>
        """,
        unsafe_allow_html=True,
    )

    file_manager = FileManager()

    NAV = [("Scrape Product", "🌐"), ("AI Studio", "🤖"), ("Library", "📚")]
    with st.sidebar:
        st.markdown(
            """
            <div class="es-side-brand">
                <div class="es-logo">MP</div>
                <div>
                    <div class="es-side-title">Multi-Platform</div>
                    <div class="es-side-sub">Temu · Alibaba · AliExpress · Shein</div>
                </div>
            </div>
            """,
            unsafe_allow_html=True,
        )
        st.markdown('<div class="es-side-section">Configuration</div>', unsafe_allow_html=True)
        st.caption(f"Storage: Local CSV ({MULTI_CSV_FILENAME})")

        stored_key = load_groq_api_key()
        groq_api_key = st.text_input("Groq API Key", value=stored_key, type="password",
                                     help="Required for AI features")
        if st.checkbox("Persist API key to this project", value=bool(groq_api_key)):
            if groq_api_key and groq_api_key != stored_key:
                save_groq_api_key(groq_api_key)
                st.success("API key saved", icon="✅")
        if groq_api_key:
            st.success("Groq API key configured", icon="🤖")
        else:
            st.info("Add API key to unlock AI features", icon="🔑")

        st.markdown('<div class="es-side-section">Marketplaces</div>', unsafe_allow_html=True)
        for name, cls in SCRAPERS.items():
            st.caption(f"{cls.ICON}  {name}")

    tab_scrape, tab_ai, tab_lib = st.tabs([f"{ico}  {name}" for name, ico in NAV])
    with tab_scrape:
        render_scrape_tab(file_manager)
    with tab_ai:
        render_ai_tab(file_manager, groq_api_key)
    with tab_lib:
        render_library_tab(file_manager)


if __name__ == "__main__":
    main()
