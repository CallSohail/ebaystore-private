"""
Local backend for the HTML edition (index.html).

Run this to bypass CORS proxies entirely:

    python server.py

Then open http://127.0.0.1:8000/ in your browser. The HTML auto-detects the
backend and uses it for scraping + image fetches.

Reuses the existing scraper logic from ebay_scraper.py (no changes to that
file). No third-party deps — pure stdlib.
"""

import json
import logging
import mimetypes
import os
import sys
import threading
import traceback
from dataclasses import asdict
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse, parse_qs

# Import the existing scraper without modifying ebay_scraper.py.
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from ebay_scraper import EbayScraper, FileManager, append_to_local_csv  # noqa: E402

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("ebay-server")

HOST = os.environ.get("EBAY_HTTP_HOST", "127.0.0.1")
PORT = int(os.environ.get("EBAY_HTTP_PORT", "8000"))

SCRAPER = EbayScraper()
FILE_MANAGER = FileManager()
_LOCK = threading.Lock()


def _cors(handler: BaseHTTPRequestHandler) -> None:
    handler.send_header("Access-Control-Allow-Origin", "*")
    handler.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
    handler.send_header("Access-Control-Allow-Headers", "Content-Type")


def _send_json(handler: BaseHTTPRequestHandler, status: int, payload) -> None:
    body = json.dumps(payload).encode("utf-8")
    handler.send_response(status)
    handler.send_header("Content-Type", "application/json; charset=utf-8")
    handler.send_header("Content-Length", str(len(body)))
    _cors(handler)
    handler.end_headers()
    handler.wfile.write(body)


def _send_bytes(handler: BaseHTTPRequestHandler, status: int, body: bytes, content_type: str) -> None:
    handler.send_response(status)
    handler.send_header("Content-Type", content_type)
    handler.send_header("Content-Length", str(len(body)))
    _cors(handler)
    handler.end_headers()
    handler.wfile.write(body)


def _serve_static(handler: BaseHTTPRequestHandler, rel_path: str) -> None:
    if rel_path in ("", "/"):
        rel_path = "index.html"
    rel_path = rel_path.lstrip("/")
    target = (ROOT / rel_path).resolve()
    if ROOT not in target.parents and target != ROOT / rel_path.rstrip("/"):
        _send_json(handler, 403, {"error": "forbidden"})
        return
    if not target.exists() or not target.is_file():
        _send_json(handler, 404, {"error": "not found"})
        return
    ctype, _ = mimetypes.guess_type(str(target))
    ctype = ctype or "application/octet-stream"
    data = target.read_bytes()
    _send_bytes(handler, 200, data, ctype)


def _scrape(url: str) -> dict:
    """Run the existing Python scraper and return a JSON-friendly dict."""
    result = SCRAPER.scrape_product(url)
    if not result.success:
        return {"success": False, "error": result.error_message or "unknown"}
    p = result.product_data
    return {
        "success": True,
        "product": {
            "url": p.url,
            "title": p.title,
            "price": p.price,
            "condition": p.condition,
            "seller": p.seller,
            "shipping": p.shipping,
            "description": p.description,
            "brand": p.brand,
            "item_specifics": p.item_specifics or {},
            "scraped_at": p.scraped_at,
            "location": p.location,
            "returns_policy": p.returns_policy,
            "category": p.category,
            "item_id": p.item_id,
        },
        "image_urls": result.image_urls or [],
    }


def _fetch_image(url: str) -> tuple[bytes, str]:
    resp = SCRAPER.session.get(url, timeout=20)
    resp.raise_for_status()
    ctype = resp.headers.get("Content-Type", "image/jpeg").split(";")[0].strip()
    return resp.content, ctype


def _save_to_disk(payload: dict) -> dict:
    """Mirror the Python pipeline: create folder, save text/md, download images, append CSV."""
    product = payload.get("product") or {}
    image_urls = payload.get("image_urls") or []
    base_dir = payload.get("base_dir")  # optional override

    fm = FILE_MANAGER
    if base_dir:
        try:
            fm = FileManager(base_dir=base_dir)
        except Exception as e:
            return {"success": False, "error": f"bad base_dir: {e}"}

    # Build a ProductData-like object via dataclass fields
    from ebay_scraper import ProductData  # local import to avoid top-level cycles
    pd = ProductData(
        url=product.get("url", ""),
        title=product.get("title", ""),
        price=product.get("price", ""),
        condition=product.get("condition", ""),
        seller=product.get("seller", ""),
        shipping=product.get("shipping", ""),
        description=product.get("description", ""),
        brand=product.get("brand", ""),
        item_specifics=product.get("item_specifics") or {},
        scraped_at=product.get("scraped_at", ""),
        location=product.get("location", ""),
        returns_policy=product.get("returns_policy", ""),
        category=product.get("category", ""),
        item_id=product.get("item_id", ""),
    )

    folder = fm.create_product_folder(brand=pd.brand, item_id=pd.item_id, fallback_title=pd.title)
    fm.save_product_description_markdown(pd, folder)
    fm.save_product_text(pd, folder)
    fm.save_raw_scrape_text(pd, folder)
    saved_images = []
    if image_urls:
        try:
            saved_images = fm.download_images(SCRAPER, image_urls, folder)
        except Exception as e:
            log.warning("image download failed: %s", e)
    with _LOCK:
        append_to_local_csv(pd)
    return {"success": True, "folder": str(folder), "saved_images": [str(p) for p in saved_images]}


class Handler(BaseHTTPRequestHandler):
    server_version = "EbayScraperLocal/1.0"

    def log_message(self, fmt: str, *args) -> None:  # quieter access log
        log.info("%s - %s", self.address_string(), fmt % args)

    def do_OPTIONS(self) -> None:
        self.send_response(204)
        _cors(self)
        self.end_headers()

    def do_GET(self) -> None:
        parsed = urlparse(self.path)
        path = parsed.path

        if path == "/api/health":
            _send_json(self, 200, {"ok": True, "version": "1.0", "cwd": str(ROOT)})
            return

        if path == "/api/image":
            qs = parse_qs(parsed.query)
            url = (qs.get("url") or [""])[0]
            if not url:
                _send_json(self, 400, {"error": "missing url"})
                return
            try:
                data, ctype = _fetch_image(url)
                _send_bytes(self, 200, data, ctype)
            except Exception as e:
                _send_json(self, 502, {"error": str(e)})
            return

        # Static files
        _serve_static(self, path)

    def do_POST(self) -> None:
        parsed = urlparse(self.path)
        path = parsed.path
        try:
            length = int(self.headers.get("Content-Length") or 0)
            raw = self.rfile.read(length) if length else b""
            body = json.loads(raw or b"{}")
        except Exception as e:
            _send_json(self, 400, {"error": f"bad json: {e}"})
            return

        if path == "/api/scrape":
            url = (body.get("url") or "").strip()
            if not url:
                _send_json(self, 400, {"error": "missing url"})
                return
            try:
                _send_json(self, 200, _scrape(url))
            except Exception as e:
                log.error("scrape failed: %s", traceback.format_exc())
                _send_json(self, 500, {"success": False, "error": str(e)})
            return

        if path == "/api/save":
            try:
                _send_json(self, 200, _save_to_disk(body))
            except Exception as e:
                log.error("save failed: %s", traceback.format_exc())
                _send_json(self, 500, {"success": False, "error": str(e)})
            return

        _send_json(self, 404, {"error": "no such endpoint"})


def main() -> None:
    log.info("eBay scraper backend listening on http://%s:%s", HOST, PORT)
    log.info("Open http://%s:%s/ in your browser to use the HTML UI", HOST, PORT)
    server = ThreadingHTTPServer((HOST, PORT), Handler)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        log.info("Shutting down")
        server.server_close()


if __name__ == "__main__":
    main()
