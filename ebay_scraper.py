"""
eBay Product Scraper with AI Processing
======================================

A production-ready eBay product scraper with integrated AI processing capabilities.
Features include:
- Robust eBay product data extraction
- Image downloading and enhancement
- Local CSV storage (EbayStore_Products.csv)
- AI-powered content generation with Groq
- Batch processing driven by an uploaded CSV/Excel file (Brand | S.NO | Link | Status)
- Duplicate protection: every link ever processed is recorded in
  batch_status_log.csv, so re-uploading the same file marks the repeated
  entries as `duplicate` and moves on instead of scraping them again
- Errors reported by cause (API quota, bad key, rate limit, locked file)

Author: Production Development Team
Version: 3.3
"""

import csv
import hashlib
import html
import json
import logging
import os
import random
import re
import shutil
import stat
import tempfile
import threading
import time
import traceback
import unicodedata
from dataclasses import dataclass, asdict, field
from datetime import datetime
from functools import lru_cache
from io import BytesIO
from pathlib import Path
from typing import Any, Dict, List, NamedTuple, Optional, Tuple
from urllib.parse import urljoin, urlparse, parse_qs

import pandas as pd
import requests
import streamlit as st
import urllib3
from bs4 import BeautifulSoup, Tag
from groq import Groq
from PIL import Image, ImageEnhance
from requests.adapters import HTTPAdapter

# Configure logging to file and console
log_filename = "ebay_scraper.log"
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(log_filename, encoding='utf-8'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)


# =============================================================================
# NETWORK CONFIGURATION - Bypass proxy/university network
# =============================================================================

# Disable proxy for all HTTP requests
os.environ['NO_PROXY'] = '*'
os.environ['no_proxy'] = '*'
os.environ['HTTP_PROXY'] = ''
os.environ['HTTPS_PROXY'] = ''
os.environ['http_proxy'] = ''
os.environ['https_proxy'] = ''

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ---------------------------------------------------------------------------
# HTTP transport
# ---------------------------------------------------------------------------
# eBay's edge fingerprints the TLS handshake, not just the headers. `requests`
# always produces the same handshake, and it matches no real browser — so a
# request claiming to be Chrome in its User-Agent contradicts itself at the
# TLS layer, which is one of the cheapest possible bot signals. Rotating the
# User-Agent cannot fix that mismatch, which is why identity refreshes alone
# never cleared the block.
#
# curl_cffi replays a real browser's TLS/HTTP2 fingerprint, so the handshake
# and the User-Agent finally agree. It is optional: when it is not installed
# the app falls back to `requests` and simply keeps the old behaviour.
try:
    from curl_cffi import requests as curl_requests
    CURL_CFFI_AVAILABLE = True
except Exception:  # pragma: no cover - depends on the install
    curl_requests = None
    CURL_CFFI_AVAILABLE = False

# Impersonation targets paired with the matching User-Agent, so the two
# always tell the same story.
IMPERSONATION_PROFILES = [
    ("chrome131", 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36'),
    ("chrome136", 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/136.0.0.0 Safari/537.36'),
    ("safari180", 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.0 Safari/605.1.15'),
    ("firefox133", 'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:133.0) Gecko/20100101 Firefox/133.0'),
]

# Exceptions that mean "the request did not complete". curl_cffi raises its
# own hierarchy, unrelated to requests', so both are caught.
NETWORK_EXCEPTIONS: Tuple[type, ...] = (requests.RequestException,)
if CURL_CFFI_AVAILABLE:
    try:
        NETWORK_EXCEPTIONS = NETWORK_EXCEPTIONS + (curl_requests.errors.RequestsError,)
    except Exception:
        NETWORK_EXCEPTIONS = NETWORK_EXCEPTIONS + (Exception,)


def transport_name() -> str:
    """Which HTTP transport is active, for display in the UI."""
    return "curl_cffi (browser TLS fingerprint)" if CURL_CFFI_AVAILABLE else "requests (basic TLS)"


class NoProxyHTTPAdapter(HTTPAdapter):
    """HTTPAdapter that bypasses all proxies."""
    def proxy_manager_for(self, proxy, **kwargs):
        return super().proxy_manager_for(None, **kwargs)

# =============================================================================
# CACHING AND AGENTS
# =============================================================================

# Rotating pool of realistic desktop browser User-Agents. eBay's anti-bot
# system flags repeated fingerprints, so each scraper session picks a UA at
# init time and retries after a failure pick a fresh one.
USER_AGENTS = [
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:128.0) Gecko/20100101 Firefox/128.0',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 14_6_0) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.6 Safari/605.1.15',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36 Edg/130.0.0.0',
]

# Browser-like headers to avoid anti-bot detection
REQUEST_HEADERS = {
    'User-Agent': USER_AGENTS[0],
    'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8',
    'Accept-Language': 'en-US,en;q=0.9',
    'Accept-Encoding': 'gzip, deflate, br',
    'DNT': '1',
    'Connection': 'keep-alive',
    'Upgrade-Insecure-Requests': '1',
    'Sec-Fetch-Dest': 'document',
    'Sec-Fetch-Mode': 'navigate',
    'Sec-Fetch-Site': 'none',
    'Sec-Fetch-User': '?1',
    'Cache-Control': 'max-age=0',
}

class ResponseCache:
    """Simple cache for API responses to avoid redundant calls."""
    
    def __init__(self, max_size: int = 100):
        self.cache: Dict[str, Any] = {}
        self.max_size = max_size
        
    def get(self, key: str) -> Optional[Any]:
        """Get cached response."""
        return self.cache.get(self._hash_key(key))
    
    def set(self, key: str, value: Any) -> None:
        """Cache a response."""
        if len(self.cache) >= self.max_size:
            # Remove oldest entry
            self.cache.pop(next(iter(self.cache)))
        self.cache[self._hash_key(key)] = value
    
    def _hash_key(self, key: str) -> str:
        """Hash the key for consistent lookup."""
        return hashlib.md5(key.encode()).hexdigest()

class PlatformAgent:
    """AI agent that researches and optimizes for specific platforms."""
    
    def __init__(self, groq_client, groq_model: str, cache: ResponseCache):
        """Initialize with Groq client, model name, and cache."""
        self.client = groq_client
        self.model = groq_model
        self.cache = cache
        
        # Platform knowledge base - researched per-marketplace listing requirements
        self.platforms = {
            "leboncoin": {
                "name": "Leboncoin",
                "language": "French",
                "style": "Casual, direct, local-focused, no exaggerated claims",
                "key_features": ["Price visibility", "Local pickup options", "Honest condition description"],
                "title_length": 50,
                "max_description_chars": 1500,
                "required_fields": ["état", "marque", "taille", "couleur", "ville/code postal"],
                "tone_rules": "Plain French, no emojis, no all-caps. Mention local pickup and shipping options.",
                "description_style": "Short paragraphs, clear bullet points, end with delivery options.",
                "must_avoid": ["external links", "phone numbers in description", "promotional language"]
            },
            "vinted": {
                "name": "Vinted",
                "language": "Buyer's local language (EN/FR/DE/ES/IT/PL)",
                "style": "Friendly, fashion-forward, community-oriented, lowercase ok",
                "key_features": ["Brand", "Size (with size system EU/UK/US)", "Material composition", "Condition (new with tags / very good / good / satisfactory)", "Measurements (pit-to-pit, length, waist, inseam)"],
                "title_length": 60,
                "max_description_chars": 1500,
                "required_fields": ["brand", "size", "condition", "color", "material", "category"],
                "tone_rules": "Warm and casual. 1-3 light emojis allowed. Mention bundle discounts and fast shipping. Be transparent about flaws.",
                "description_style": "Two sections only: a 'Specifications' bullet list and a 'Condition' bullet list. No intro paragraph, no marketing copy, no hashtags, no emojis.",
                "must_avoid": ["counterfeit claims", "external links", "personal contact info", "price negotiation outside Vinted", "marketing fluff", "hashtags", "emojis", "intro/closing lines"],
                # Vinted uses a strict two-section template (see _generate_strict_description).
                "strict_format": True
            },
            "vestiaire collective": {
                "name": "Vestiaire Collective",
                "language": "English (primary) or French",
                "style": "Luxury, professional, authentication-focused, formal tone",
                "key_features": ["Authenticity proof", "Serial/date code", "Original packaging (dust bag, box, receipt)", "Precise measurements in cm", "Condition grading (Never worn / Very good / Good / Fair)", "Provenance/year of purchase"],
                "title_length": 100,
                "max_description_chars": 3000,
                "required_fields": ["brand", "model name", "material", "color", "size", "year of purchase", "condition grade"],
                "tone_rules": "Formal, third-person, factual. No emojis, no hashtags, no exclamations. Focus on craftsmanship and authenticity.",
                "description_style": "1) Item summary (brand, model, year). 2) Materials and craftsmanship. 3) Exact measurements in cm. 4) Condition with specific flaws. 5) Included accessories. 6) Provenance.",
                "must_avoid": ["price comparisons to retail", "urgency phrasing", "emojis", "informal slang"]
            },
            "depop": {
                "name": "Depop",
                "language": "English",
                "style": "Gen-Z, trendy, aesthetic, hashtag-heavy",
                "key_features": ["Aesthetic/style tags (y2k, grunge, cottagecore)", "Brand & era", "Size (listed and measured)", "Vibe descriptors", "Hashtags (up to 5 used by algorithm)"],
                "title_length": 65,
                "max_description_chars": 1000,
                "required_fields": ["brand", "size", "condition", "color", "category", "5 hashtags"],
                "tone_rules": "Trendy, lowercase friendly, emojis welcome (2-4). Use aesthetic terms. Mention model size for fit reference if relevant.",
                "description_style": "Hook line with vibe → key details (brand, size, condition) → measurements → end with 5 hashtags. Keep it scannable.",
                "must_avoid": ["walls of text", "boring corporate tone", "external links"]
            },
            "poshmark": {
                "name": "Poshmark",
                "language": "English (US)",
                "style": "Boutique, upbeat, retail-style",
                "key_features": ["Brand", "Size (US sizing)", "Color", "Condition", "Original retail price", "Smoke-free/pet-free home note"],
                "title_length": 80,
                "max_description_chars": 1500,
                "required_fields": ["brand", "size", "category", "color", "condition", "NWT/EUC/GUC code"],
                "tone_rules": "Boutique-style. NWT (New With Tags), EUC (Excellent Used Condition), GUC (Good Used Condition) abbreviations expected. Light emojis ok.",
                "description_style": "Title line → bullet list (brand, size, material, measurements) → condition note → closing line (bundle discount, ships next day). Add 3-5 relevant hashtags.",
                "must_avoid": ["off-platform contact", "trade requests in title", "misleading sizing"]
            },
            "mercari": {
                "name": "Mercari",
                "language": "English (US)",
                "style": "Clean, factual, search-keyword optimized",
                "key_features": ["Brand", "Size", "Color", "Material", "Condition (New / Like new / Good / Fair / Poor)", "Shipping weight"],
                "title_length": 80,
                "max_description_chars": 1000,
                "required_fields": ["brand", "category", "condition", "size/dimensions", "weight"],
                "tone_rules": "Direct and keyword-heavy for search. No fluff, no emojis required. Front-load brand and key specs in title.",
                "description_style": "Title front-loaded with brand+keyword. Description: bulleted specs, condition disclosure, dimensions, shipping notes (smoke-free home, ships within 1 business day).",
                "must_avoid": ["external links", "vague condition", "missing dimensions"]
            },
            "etsy": {
                "name": "Etsy",
                "language": "English",
                "style": "Story-driven, handmade/vintage focus, SEO-rich",
                "key_features": ["Era/year for vintage", "Materials", "Dimensions", "Care instructions", "Handmade vs vintage vs craft supply", "13 tags max for SEO"],
                "title_length": 140,
                "max_description_chars": 5000,
                "required_fields": ["category", "materials", "dimensions", "production type (handmade/vintage)", "13 SEO tags"],
                "tone_rules": "Warm, storytelling, evocative. Front-load primary keyword + descriptor in first 40 chars of title for SEO.",
                "description_style": "Opening hook → materials and dimensions → backstory/inspiration → care instructions → shipping/processing time → return policy. Include FAQ at the end.",
                "must_avoid": ["mass-produced claims labeled handmade", "external shop links", "trademarked terms"]
            },
            "grailed": {
                "name": "Grailed",
                "language": "English",
                "style": "Streetwear/menswear connoisseur, brand-savvy",
                "key_features": ["Designer/brand (capitalized correctly)", "Season/year (SS18, FW20)", "Collection name", "Size (chest, waist, length in inches)", "Tagged size", "Condition (10/10 scale common)"],
                "title_length": 60,
                "max_description_chars": 1000,
                "required_fields": ["designer", "department", "category", "size", "color", "condition"],
                "tone_rules": "Knowledgeable, no fluff. Use correct collection/season codes. Mention provenance for hype items. No emojis.",
                "description_style": "Designer + collection + piece type → measurements in inches (P2P, length, shoulder, sleeve) → condition with any flaws called out → reason for sale optional.",
                "must_avoid": ["fake season codes", "wrong designer spelling", "overpriced anchoring"]
            },
            "facebook marketplace": {
                "name": "Facebook Marketplace",
                "language": "English (US/UK)",
                "style": "Local, conversational, pickup-friendly",
                "key_features": ["Location/pickup area", "Condition", "Local pickup vs shipping", "Cash/Venmo accepted", "Bundle deals", "Dimensions for furniture"],
                "title_length": 100,
                "max_description_chars": 5000,
                "required_fields": ["category", "condition", "location", "price"],
                "tone_rules": "Friendly and conversational. Mention 'pickup in [neighborhood]'. Light emojis ok. Say 'first come first served' or 'serious buyers only' as appropriate.",
                "description_style": "Item + condition → why selling (moving, upgraded, etc.) → dimensions → pickup details → preferred payment.",
                "must_avoid": ["prohibited items", "trades unless specified", "vague location"]
            },
            "ebay": {
                "name": "eBay",
                "language": "English",
                "style": "Professional retailer, search-optimized, detail-rich",
                "key_features": ["Brand/MPN/UPC", "Exact model number", "Item specifics (every field filled)", "Condition with detailed notes", "Shipping policy", "Returns policy", "Authentication for high-value"],
                "title_length": 80,
                "max_description_chars": 4000,
                "required_fields": ["brand", "MPN", "model", "size/dimensions", "color", "material", "condition", "country of manufacture"],
                "tone_rules": "Professional, third-person, no all-caps in title (eBay penalizes). Pack keywords into the 80-char title without keyword-stuffing.",
                "description_style": "Title with brand+model+key spec → bulleted feature list → detailed condition (call out every flaw, include photos referenced as 'see photos') → shipping & handling → returns. Use HTML-friendly line breaks.",
                "must_avoid": ["misleading titles", "competitor brand keywords in title (keyword spamming = listing removal)", "external links"]
            },
            "shopify": {
                "name": "Shopify Store",
                "language": "English",
                "style": "Brand-voice driven, conversion-focused",
                "key_features": ["Product benefit headline", "Bullet feature list", "Detailed spec table", "SEO meta description (155 chars)", "Schema-ready details"],
                "title_length": 70,
                "max_description_chars": 5000,
                "required_fields": ["product title", "vendor", "type", "tags", "SKU", "weight", "dimensions"],
                "tone_rules": "Brand-consistent. Lead with the customer benefit, not the feature. Strong CTA at the end.",
                "description_style": "Benefit headline → 3-5 feature bullets (benefit-led) → specs table → social proof if available → shipping & return note. Add 155-char SEO meta separately.",
                "must_avoid": ["raw scraped text", "generic phrasing", "missing alt-text suggestions"]
            },
            "instagram": {
                "name": "Instagram",
                "language": "English",
                "style": "Visual-first caption, hook-led, hashtag-rich",
                "key_features": ["Hook (first line)", "Story/CTA", "15-25 hashtags", "Emojis", "Link-in-bio reference"],
                "title_length": 30,
                "max_description_chars": 2200,
                "required_fields": ["hook", "CTA", "hashtags"],
                "tone_rules": "Punchy hook. Conversational body. 15-25 relevant hashtags grouped at the bottom or in first comment.",
                "description_style": "Line 1 hook → emoji-led body → CTA (link in bio / DM to buy) → blank line → hashtag block.",
                "must_avoid": ["banned hashtags", "all-caps", "more than 30 hashtags (algorithm penalty)"]
            },
            "general": {
                "name": "General Marketplace",
                "language": "English",
                "style": "Professional, clear, informative",
                "key_features": ["Complete specs", "Clear photos", "Honest description"],
                "title_length": 80,
                "max_description_chars": 2000,
                "required_fields": ["brand", "size", "condition", "category"],
                "tone_rules": "Professional and clear. Adapt to context.",
                "description_style": "Structured with clear sections: overview, specs, condition, shipping.",
                "must_avoid": ["misleading claims", "external links"]
            }
        }
    
    def research_platform(self, platform_name: str) -> Dict:
        """Get platform-specific requirements and best practices.
        Matches loosely on lowercase, ignoring spaces/underscores/hyphens."""
        if not platform_name:
            return self.platforms["general"]
        target = re.sub(r'[\s_\-]+', '', platform_name.lower())
        for key, val in self.platforms.items():
            if re.sub(r'[\s_\-]+', '', key.lower()) == target:
                return val
        # Common aliases
        aliases = {
            'vc': 'vestiaire collective',
            'fb': 'facebook marketplace',
            'facebook': 'facebook marketplace',
            'marketplace': 'facebook marketplace',
            'ig': 'instagram',
            'insta': 'instagram',
        }
        if target in aliases:
            return self.platforms.get(aliases[target], self.platforms["general"])
        return self.platforms["general"]
    
    def _generate_strict_description(self, platform_info: Dict, raw_text: str, title: str,
                                     brand: str, condition: str, specs: Dict,
                                     custom_instructions: str = "") -> str:
        """Generate a description for platforms that require a strict, fixed
        two-section layout (Specifications + Condition) and nothing else.

        Used for Vinted. The output deliberately omits titles, marketing
        intros, closing lines, hashtags and emojis — only the two bullet
        sections are produced, matching the seller's expected format.
        """
        name = platform_info.get('name', 'this platform')
        extra = (
            f"\nUSER CUSTOM INSTRUCTIONS (apply where they do not break the format): {custom_instructions}\n"
            if custom_instructions else ""
        )

        prompt = f"""You are an expert second-hand fashion listing writer for {name}.

Produce a listing using EXACTLY two sections and NOTHING else: "Specifications" and "Condition". Do not add a title line, an intro paragraph, marketing copy, a closing line, hashtags, or emojis.

INPUT DATA:
Title: {title}
Brand: {brand}
Condition: {condition}
Specifications: {json.dumps(specs, ensure_ascii=False)}

RAW TEXT (may contain noise like nav menus, similar-item lists, seller banners — extract only the real product information):
{raw_text}
{extra}
OUTPUT FORMAT — copy this structure exactly (plain text, no markdown symbols like # or **):

Specifications
- Brand: <value>
- Category: <value>
- Material: <value>
- Color: <value>
- Size: <value, include cm and inches when available>
- <add only the spec lines the source supports, e.g. Strap Drop, Handle Drop, Dimensions, Product Line, Serial No., Country of Manufacture, Hardware>

Condition (<overall grade, e.g. Pre-owned – Good>)
- Exterior: <value>
- <add only the condition lines the source supports, e.g. Handle, Shoulder Strap, Metal fittings, Interior, Pocket, Corners, Odor>

HARD RULES:
1. Output ONLY the two sections above — no title, no description paragraph, no hashtags, no emojis, no marketing language, no shipping/bundle lines.
2. Use the exact section headers "Specifications" and "Condition (<grade>)".
3. Use bullet lines in the form "- Label: value".
4. Only include lines that the source actually supports. NEVER invent specs, measurements, materials, serial numbers, or condition flaws.
5. Keep every concrete number and code from the source (cm, inches, serial numbers, product line codes).
6. In the Condition header, state the overall condition grade in parentheses when it is known.
7. Be honest and specific about flaws, using the source's wording.

Begin now with the line "Specifications".
"""

        cache_key = f"{name}_strict_{title}_{hash(raw_text[:500])}"
        cached = self.cache.get(cache_key)
        if cached:
            logger.debug("Using cached strict-format description")
            return cached

        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                temperature=0.4,
                max_tokens=1500
            )
        except Exception as e:
            raise_ai_error(e)
        result_text = response.choices[0].message.content.strip() if response.choices[0].message.content else ""
        if not result_text:
            raise AIServiceError("The model returned an empty response. Try again, or pick a different source file.")
        self.cache.set(cache_key, result_text)
        return result_text

    def generate_platform_description(self, raw_text: str, product_data: Optional[Any],
                                     platform: str, custom_instructions: str = "") -> str:
        """
        Generate clean, platform-optimized product description.
        
        Args:
            raw_text: Raw scraped text  
            product_data: Structured product data
            platform: Target platform name
            custom_instructions: User's custom requirements
            
        Returns:
            Clean, structured description without raw headers
        """
        try:
            platform_info = self.research_platform(platform)
            
            # Extract key data
            title = ""
            brand = ""
            condition = ""
            specs = {}
            
            if product_data:
                title = getattr(product_data, 'title', '')
                brand = getattr(product_data, 'brand', '')
                condition = getattr(product_data, 'condition', '')
                specs = getattr(product_data, 'item_specifics', {})
            
            # Platforms with a strict, fixed-structure template (e.g. Vinted)
            # bypass the generic listing prompt and use a dedicated builder that
            # emits ONLY the required sections.
            if platform_info.get('strict_format'):
                return self._generate_strict_description(
                    platform_info, raw_text, title, brand, condition, specs, custom_instructions
                )

            required_fields = platform_info.get('required_fields', [])
            tone_rules = platform_info.get('tone_rules', '')
            must_avoid = platform_info.get('must_avoid', [])
            max_chars = platform_info.get('max_description_chars', 2000)

            prompt = f"""
You are an expert product listing writer for {platform_info['name']}. You know this platform's algorithm, audience and unwritten rules.

TASK: Produce a ready-to-publish listing optimized for {platform_info['name']}. No commentary, no preface — just the final listing.

INPUT DATA:
Title: {title}
Brand: {brand}
Condition: {condition}
Specifications: {json.dumps(specs, ensure_ascii=False)}

RAW TEXT (may contain noise like nav menus, similar-item lists, seller banners — extract only the real product information):
{raw_text}

PLATFORM PROFILE — {platform_info['name']}:
- Language: {platform_info['language']}
- Audience & style: {platform_info['style']}
- Title length target: ~{platform_info['title_length']} characters (hard ceiling)
- Description ceiling: ~{max_chars} characters
- Required fields to address explicitly: {', '.join(required_fields) if required_fields else 'standard'}
- Key features this platform's buyers care about: {', '.join(platform_info['key_features'])}
- Tone rules: {tone_rules}
- Description structure: {platform_info['description_style']}
- Must AVOID on this platform: {', '.join(must_avoid) if must_avoid else 'none'}

{f"USER CUSTOM INSTRUCTIONS (override defaults where they conflict): {custom_instructions}" if custom_instructions else ""}

HARD RULES:
1. Output ONLY the listing. No "Here is your listing", no markdown headers like "# Title".
2. First line = the optimized TITLE (no quotes, no prefix). Blank line. Then the description.
3. Never invent specs, measurements, materials, or provenance that aren't in the source. If unknown, omit.
4. Strip noise: nav links, "similar items", "people also viewed", seller promo, breadcrumbs, eBay/site chrome.
5. Keep every concrete number from the source (cm, in, kg, size, year).
6. Be honest about flaws — call them out in the platform's expected phrasing.
7. Match the platform tone exactly. Casual platforms get casual; luxury platforms stay formal.
8. Address each required field if the source provides it.
9. Output language: write in {platform_info['language']}.

Begin the output now with the title on the first line.
"""
            
            # Check cache first
            cache_key = f"{platform}_{title}_{hash(raw_text[:500])}"
            cached = self.cache.get(cache_key)
            if cached:
                logger.debug("Using cached platform description")
                return cached
            
            try:
                response = self.client.chat.completions.create(
                    model=self.model,
                    messages=[{"role": "user", "content": prompt}],
                    temperature=0.6,
                    max_tokens=2000
                )
            except Exception as e:
                raise_ai_error(e)
            result_text = response.choices[0].message.content.strip() if response.choices[0].message.content else ""
            if not result_text:
                raise AIServiceError("The model returned an empty response. Try again, or pick a different source file.")

            # Cache the result
            self.cache.set(cache_key, result_text)

            return result_text

        except AIServiceError:
            # Already carries a user-facing cause — let the UI show it as-is
            # instead of silently returning an empty description.
            raise
        except Exception as e:
            logger.error(f"Error generating platform description: {traceback.format_exc()}")
            raise AIServiceError(describe_ai_error(e)) from e

# =============================================================================
# CONFIGURATION AND CONSTANTS
# =============================================================================

# Logging configuration
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('ebay_scraper.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# Application constants
SERVICE_ACCOUNT_JSON_FILENAME = "sylvan-airship-469509-b1-beef32b9a116.json"
BASE_SAVE_DIR = "downloads"
SHEET_TITLES_TO_TRY = [
    "ebay_Product_List",
    "Ebay_Product_List", 
    "eBay Product List",
    "Ebay Product List",
    "ebay product list",
    "ebay_Product_List.csv",
]
DEFAULT_WORKSHEET_INDEX = 0
WORKSHEET_NAMES_TO_TRY = [
    'ebay_Product_List',
    'Ebay_Product_List',
    'eBay_Product_List',
    'ebay product list',
    'Products'
]
DEFAULT_SHEET_ID = "1YsDXTexrtz3h-uaErbwhLZlDVGLDUKoIT3By-5UrhLI"

# Pages rejected as bot-checks are kept here so a real block can be told
# apart from a detection false positive.
BLOCKED_PAGES_DIR = "blocked_pages"
BLOCKED_PAGES_KEEP = 10

# A run gives up after this many listings are blocked back to back: grinding
# through the rest of the file against an active block wastes the user's time
# and keeps hammering an edge that is already refusing traffic.
MAX_CONSECUTIVE_BLOCKED_ROWS = 3
# How long to wait before a blocked run is worth retrying.
BLOCK_COOLDOWN_MINUTES = 15

# Downloaded images are normalised to JPEG. eBay serves WebP to modern
# browsers and most listing tools and photo editors still cannot open it.
SAVE_IMAGES_AS_JPEG = True
JPEG_QUALITY = 92

# Summary-row labels per regional site. Class-name matching handles most
# listings, but eBay localises the visible labels, so an English-only list
# silently loses condition and location on ebay.fr, .de, .it and .es — which
# is exactly what the reported logs showed.
LABELS_CONDITION = [
    'condition', 'item condition',
    'état', 'etat', 'état de l\'objet', 'etat de l\'objet',   # French
    'artikelzustand', 'zustand',                              # German
    'condizione', 'condizioni', "condizione dell'oggetto",    # Italian
    'estado', 'estado del artículo', 'estado del articulo',   # Spanish
    'staat', 'conditie',                                      # Dutch
    'stan',                                                   # Polish
]

LABELS_LOCATION = [
    'located in', 'item location', 'location', 'ships from',
    'lieu où se trouve l\'objet', 'lieu ou se trouve l\'objet',
    'lieu', 'se trouve à', 'se trouve a', 'expédié depuis', 'expedie depuis',
    'artikelstandort', 'standort', 'versand aus',
    'luogo in cui si trova l\'oggetto', 'si trova a', 'spedizione da',
    'ubicación del artículo', 'ubicacion del articulo', 'ubicación', 'ubicacion',
    'objectlocatie', 'locatie',
    'lokalizacja przedmiotu',
]

LABELS_SHIPPING = [
    'shipping', 'delivery', 'postage',
    'livraison', 'frais de livraison', 'expédition', 'expedition',
    'versand', 'versandkosten', 'lieferung',
    'spedizione', 'costi di spedizione', 'consegna',
    'envío', 'envio', 'gastos de envío', 'gastos de envio',
    'verzending', 'verzendkosten',
    'wysyłka', 'wysylka',
]

LABELS_RETURNS = [
    'returns', 'return policy',
    'retours', 'politique de retour', 'renvois',
    'rücknahme', 'rucknahme', 'rückgabe', 'ruckgabe', 'rücknahmebedingungen',
    'restituzioni', 'resi', 'politica di reso',
    'devoluciones', 'política de devoluciones', 'politica de devoluciones',
    'retourbeleid', 'retourneren',
    'zwroty',
]


# The longest label in any of the lists below, with headroom. Text nodes
# longer than this cannot be a label, and skipping them avoids running the
# Unicode normalisation over every paragraph on the page.
MAX_LABEL_LENGTH = 48


@lru_cache(maxsize=8192)
def normalize_label(text: str) -> str:
    """Fold a label to a comparable form: lowercase, unaccented, no trailing colon.

    Folding accents means the label lists do not have to carry every spelling
    variant ('État', 'Etat', 'ETAT') for each language. Cached because the
    same short strings recur across a page and across a batch.
    """
    value = str(text or '').strip().lower()
    value = value.rstrip(':').strip()
    decomposed = unicodedata.normalize('NFKD', value)
    return ''.join(ch for ch in decomposed if not unicodedata.combining(ch))


def is_label_candidate(text: str) -> bool:
    """Cheap pre-filter: only short strings can be a field label."""
    return bool(text) and len(text) <= MAX_LABEL_LENGTH


def convert_bytes_to_jpeg(payload: bytes, quality: int = JPEG_QUALITY) -> Optional[bytes]:
    """Re-encode image bytes as JPEG. Returns None when the input is unreadable.

    Transparency is flattened onto white rather than dropped, which would
    otherwise turn transparent product cut-outs black.
    """
    try:
        with Image.open(BytesIO(payload)) as image:
            image.load()
            if image.mode in ('RGBA', 'LA') or (image.mode == 'P' and 'transparency' in image.info):
                background = Image.new('RGB', image.size, (255, 255, 255))
                rgba = image.convert('RGBA')
                background.paste(rgba, mask=rgba.split()[-1])
                image = background
            elif image.mode != 'RGB':
                image = image.convert('RGB')
            buffer = BytesIO()
            image.save(buffer, format='JPEG', quality=quality, optimize=True, subsampling=0)
            return buffer.getvalue()
    except Exception as e:
        logger.debug(f"JPEG conversion failed: {e}")
        return None

# =============================================================================
# DATA MODELS
# =============================================================================

@dataclass
class ProductData:
    """Data class for eBay product information."""
    url: str = ""
    title: str = ""
    price: str = ""
    condition: str = ""
    seller: str = ""
    shipping: str = ""
    description: str = ""
    brand: str = ""
    item_specifics: Dict[str, str] = None
    scraped_at: str = ""
    location: str = ""
    returns_policy: str = ""
    category: str = ""
    item_id: str = ""
    
    def __post_init__(self):
        if self.item_specifics is None:
            self.item_specifics = {}
        if not self.scraped_at:
            self.scraped_at = datetime.now().isoformat()

@dataclass
class ScrapingResult:
    """Result of a scraping operation."""
    success: bool
    product_data: Optional[ProductData] = None
    image_urls: List[str] = None
    error_message: str = ""
    folder_path: str = ""
    
    def __post_init__(self):
        if self.image_urls is None:
            self.image_urls = []

# =============================================================================
# CUSTOM EXCEPTIONS
# =============================================================================

class ScrapingError(Exception):
    """Base exception for scraping operations."""
    pass

class ValidationError(ScrapingError):
    """Exception raised for validation errors."""
    pass

class NetworkError(ScrapingError):
    """Exception raised for network-related errors."""
    pass

class DataExtractionError(ScrapingError):
    """Exception raised for data extraction errors."""
    pass


class AIServiceError(Exception):
    """An AI request failed for a reason the user can act on.

    Carries a message that is already safe to render in the UI, plus a `kind`
    so callers can branch on it — a bulk run stops immediately on a spent
    quota or a rejected key, but keeps going past a single oversized source.
    """

    def __init__(self, message: str, kind: str = 'error'):
        super().__init__(message)
        self.kind = kind


# Kinds that make continuing a bulk run pointless: every remaining request
# would fail the same way.
AI_FATAL_KINDS = {'quota', 'rate_limit', 'auth', 'model'}


# Groq surfaces failures as HTTP status codes plus a JSON error body. The
# status alone is ambiguous (429 covers both "too many requests per minute"
# and "daily token budget spent"), so the body text is inspected as well.
def classify_ai_error(exc: BaseException) -> str:
    """Bucket a Groq exception: quota, rate_limit, auth, model, too_long, ..."""
    status = getattr(exc, 'status_code', None)
    if status is None:
        status = getattr(getattr(exc, 'response', None), 'status_code', None)
    low = str(exc).lower()

    if status == 429 or 'rate_limit' in low or 'rate limit' in low or 'quota' in low:
        if 'tokens per day' in low or 'tpd' in low or 'per day' in low or 'daily' in low:
            return 'quota'
        return 'rate_limit'
    if status in (401, 403) or 'invalid_api_key' in low or 'invalid api key' in low or 'unauthorized' in low:
        return 'auth'
    if status == 404 or 'model_not_found' in low or 'does not exist' in low or 'decommissioned' in low:
        return 'model'
    if status == 413 or 'context_length' in low or 'too large' in low or 'reduce the length' in low:
        return 'too_long'
    if status in (500, 502, 503, 504) or 'service unavailable' in low or 'overloaded' in low:
        return 'unavailable'
    if isinstance(exc, (requests.exceptions.ConnectionError, requests.exceptions.Timeout)) \
            or 'connection' in low or 'timed out' in low or 'timeout' in low:
        return 'network'
    if status == 400 or 'invalid_request' in low:
        return 'bad_request'
    return 'error'


def describe_ai_error(exc: BaseException) -> str:
    """Translate an exception from the Groq client into a plain-language cause.

    The point is that a user who has run out of quota should read "you have
    used your free daily allowance" and not "Error code: 429 -
    {'error': {'message': ...}}".
    """
    kind = classify_ai_error(exc)
    text = str(exc)
    low = text.lower()

    # Some deployments wrap the retry hint in the message ("try again in 7.5s")
    retry_hint = ''
    match = re.search(r'try again in ([\w.]+\s*\w*)', low)
    if match:
        retry_hint = f" Try again in {match.group(1)}."

    if kind == 'quota':
        return ("Groq daily token allowance used up. The quota resets every 24 hours — "
                "wait for the reset or upgrade the Groq plan for this API key." + retry_hint)
    if kind == 'rate_limit':
        return ("Groq rate limit reached — too many requests in a short window. "
                "Wait a moment and run it again." + retry_hint)
    if kind == 'auth':
        return ("The Groq API key was rejected. Check it in the sidebar — keys start with "
                "'gsk_' and can be regenerated at console.groq.com/keys.")
    if kind == 'model':
        return ("The configured Groq model is unavailable or has been retired. "
                "Pick a current model at console.groq.com/docs/models.")
    if kind == 'too_long':
        return ("The source text is too long for the model's context window. "
                "Use a shorter source file or trim the custom instructions.")
    if kind == 'unavailable':
        return "Groq is temporarily unavailable or overloaded. Wait a minute and try again."
    if kind == 'network':
        return "Could not reach Groq. Check the internet connection and try again."
    if kind == 'bad_request':
        return f"Groq rejected the request: {text[:200]}"
    return f"AI request failed: {text[:200]}"


def raise_ai_error(exc: BaseException) -> None:
    """Log the raw failure and re-raise it as a user-facing AIServiceError."""
    logger.error(f"AI request failed: {exc}")
    raise AIServiceError(describe_ai_error(exc), classify_ai_error(exc)) from exc


# =============================================================================
# UTILITY FUNCTIONS
# =============================================================================

class FetchOutcome(NamedTuple):
    """Result of an HTTP fetch, with the failure cause preserved.

    The cause matters: a 403 from eBay's edge means "you are being throttled,
    slow down", while an empty page after a 200 means the layout changed.
    Collapsing both into `None` is what made every failure surface as the
    misleading "Could not extract the product title".
    """
    response: Optional[requests.Response]
    reason: str = ''    # '' | 'blocked' | 'not_found' | 'network'
    detail: str = ''


# Statuses eBay's edge returns when it is throttling or challenging a client.
BLOCK_STATUSES = frozenset({403, 429, 503})


def _retry_after_seconds(response: requests.Response) -> float:
    """Honour a Retry-After header when the server sends one."""
    raw = (response.headers.get('Retry-After') or '').strip()
    if not raw:
        return 0.0
    try:
        return max(0.0, min(float(raw), 120.0))
    except ValueError:
        return 0.0


def safe_request(session: requests.Session, url: str, timeout: int = 30,
                 max_retries: int = 3) -> FetchOutcome:
    """Fetch a URL with backoff, reporting *why* it failed.

    A blocked response backs off harder than a network error and honours
    Retry-After, because hammering an edge that is already throttling is what
    turns a slow batch into a completely failed one.
    """
    last = FetchOutcome(None, 'network', 'Request failed.')
    for attempt in range(max_retries):
        try:
            response = session.get(url, timeout=timeout)
            status = response.status_code

            if status in (404, 410):
                logger.info(f"Listing not available (HTTP {status}): {url}")
                return FetchOutcome(None, 'not_found', f"HTTP {status}")

            if status in BLOCK_STATUSES:
                last = FetchOutcome(None, 'blocked', f"HTTP {status}")
                wait = _retry_after_seconds(response) or (2 ** (attempt + 1)) + random.uniform(1.0, 3.0)
                logger.warning(
                    f"eBay returned HTTP {status} for {url} "
                    f"(attempt {attempt + 1}/{max_retries}); backing off {wait:.1f}s"
                )
                if attempt < max_retries - 1:
                    time.sleep(wait)
                continue

            response.raise_for_status()
            return FetchOutcome(response)

        except requests.exceptions.HTTPError as e:
            status = e.response.status_code if e.response is not None else 0
            last = FetchOutcome(None, 'network', f"HTTP {status}")
            logger.warning(f"HTTP error {status} for {url} on attempt {attempt + 1}")
        except NETWORK_EXCEPTIONS as e:
            last = FetchOutcome(None, 'network', str(e)[:200])
            logger.warning(f"Request failed: {e}. Attempt {attempt + 1}/{max_retries}")

        if attempt < max_retries - 1:
            time.sleep((2 ** attempt) + random.uniform(0.5, 1.5))

    logger.error(f"Failed to fetch {url} after {max_retries} attempts ({last.reason})")
    return last

def clean_filename(filename: str, max_length: int = 100) -> str:
    """
    Clean filename to be safe for file system.
    
    Args:
        filename: Original filename
        max_length: Maximum length of cleaned filename
        
    Returns:
        Cleaned filename safe for file system
    """
    if not filename:
        return "Unknown_Product"
    
    # Remove invalid characters
    filename = re.sub(r'[<>:"/\\|?*]', '', filename)
    # Replace multiple spaces with single space
    filename = re.sub(r'\s+', ' ', filename)
    # Trim and limit length
    filename = filename.strip()[:max_length]
    return filename or "Unknown_Product"

def ensure_directory(path: str) -> bool:
    """
    Ensure directory exists, create if necessary.
    
    Args:
        path: Directory path to ensure
        
    Returns:
        True if directory exists or was created successfully
    """
    try:
        os.makedirs(path, exist_ok=True)
        return True
    except OSError as e:
        logger.error(f"Failed to create directory {path}: {e}")
        return False

# =============================================================================
# EBAY SCRAPER CLASS
# =============================================================================

class EbayScraper:
    """
    Advanced eBay product scraper with robust error handling and data extraction.
    
    This class handles:
    - URL validation and normalization
    - Product data extraction with multiple fallback strategies
    - Image URL extraction and high-resolution optimization
    - Rate limiting and anti-detection measures
    """
    
    # Accept-Language per regional site. Requesting a French listing with an
    # en-US header is an obvious mismatch, and it also returns English labels
    # that the localized extractors then have to guess at.
    DOMAIN_LANGUAGES = {
        'ebay.fr': 'fr-FR,fr;q=0.9,en;q=0.7',
        'ebay.de': 'de-DE,de;q=0.9,en;q=0.7',
        'ebay.at': 'de-AT,de;q=0.9,en;q=0.7',
        'ebay.ch': 'de-CH,de;q=0.9,fr;q=0.8,en;q=0.7',
        'ebay.it': 'it-IT,it;q=0.9,en;q=0.7',
        'ebay.es': 'es-ES,es;q=0.9,en;q=0.7',
        'ebay.nl': 'nl-NL,nl;q=0.9,en;q=0.7',
        'ebay.be': 'nl-BE,nl;q=0.9,fr;q=0.8,en;q=0.7',
        'ebay.pl': 'pl-PL,pl;q=0.9,en;q=0.7',
        'ebay.co.uk': 'en-GB,en;q=0.9',
        'ebay.ie': 'en-IE,en;q=0.9',
        'ebay.com.au': 'en-AU,en;q=0.9',
        'ebay.ca': 'en-CA,en;q=0.9,fr;q=0.8',
    }

    def __init__(self):
        """Initialize the scraper with configured session."""
        self.impersonation = ''
        self.session = self._build_session()
        self._warmed_hosts: set = set()
        # The scraper is shared across browser tabs (it is cached per process),
        # and Streamlit runs each tab in its own thread. Serialising listing
        # fetches keeps two tabs from sharing one HTTP session concurrently and,
        # more importantly, from doubling the request rate into eBay — which is
        # the surest way to get the whole IP thrown into an anti-bot check.
        self._fetch_lock = threading.Lock()
        # Consecutive blocked fetches, used to slow down before eBay does it
        # for us. Reset by any successful listing fetch.
        self.consecutive_blocks = 0
        logger.info("eBay scraper initialized")

    def _build_session(self):
        """Create a fresh session with a coherent browser identity.

        When curl_cffi is installed the TLS fingerprint and the User-Agent are
        chosen as a matched pair, so the handshake and the header agree. With
        plain requests only the header can be set, and the mismatch remains.
        """
        profile, user_agent = random.choice(IMPERSONATION_PROFILES)
        headers = dict(REQUEST_HEADERS)
        headers['User-Agent'] = user_agent

        if CURL_CFFI_AVAILABLE:
            try:
                session = curl_requests.Session(impersonate=profile)
                session.headers.update(headers)
                self.impersonation = profile
                return session
            except Exception as e:
                # An unknown target in an older curl_cffi build should not
                # take the scraper down; fall through to requests.
                logger.warning(f"curl_cffi session with '{profile}' failed ({e}); using requests")

        session = requests.Session()
        session.mount('http://', NoProxyHTTPAdapter())
        session.mount('https://', NoProxyHTTPAdapter())
        session.proxies = {}
        session.headers.update(headers)
        self.impersonation = ''
        return session

    def refresh_identity(self) -> None:
        """Discard the current session (cookies + fingerprint) and start fresh.

        Called between retries when eBay serves an interstitial/bot-check page:
        a new cookie jar plus a different User-Agent usually clears the block.
        """
        try:
            self.session.close()
        except Exception:
            pass
        self.session = self._build_session()
        self._warmed_hosts = set()
        logger.info("Scraper identity refreshed (new session + user agent)")

    def _site_language(self, host: str) -> str:
        for domain, language in self.DOMAIN_LANGUAGES.items():
            if host.endswith(domain):
                return language
        return 'en-US,en;q=0.9'

    def prepare_for(self, url: str) -> None:
        """Make the session look like a browser that arrived from the site.

        A real visitor lands on the homepage first and carries its cookies and
        a Referer into the listing. Requesting a deep item URL cold, with no
        cookies and a mismatched language, is one of the cheapest signals for
        an edge to flag — and warming up costs one request per host per
        session.
        """
        try:
            host = urlparse(url).netloc.lower()
        except Exception:
            return
        if not host:
            return

        self.session.headers['Accept-Language'] = self._site_language(host)
        self.session.headers['Referer'] = f"https://{host}/"

        if host in self._warmed_hosts:
            return
        self._warmed_hosts.add(host)
        try:
            self.session.get(f"https://{host}/", timeout=15)
            time.sleep(random.uniform(0.8, 1.8))
            logger.debug(f"Warmed up session for {host}")
        except NETWORK_EXCEPTIONS as e:
            # Not fatal: the listing request may still succeed on its own.
            logger.debug(f"Warm-up request for {host} failed: {e}")

    def cooldown_seconds(self) -> float:
        """How long to wait before the next listing, given recent blocks.

        Backing off while eBay is actively refusing traffic is what turns a
        run where most rows fail into one where most rows succeed.
        """
        if self.consecutive_blocks <= 0:
            return random.uniform(1.0, 2.5)
        return min(15.0, 3.0 * self.consecutive_blocks) + random.uniform(1.0, 3.0)
    
    # Known eBay regional domains and short link hosts
    EBAY_DOMAINS = (
        'ebay.com', 'ebay.co.uk', 'ebay.de', 'ebay.fr', 'ebay.it', 'ebay.es',
        'ebay.com.au', 'ebay.ca', 'ebay.at', 'ebay.be', 'ebay.ch', 'ebay.ie',
        'ebay.nl', 'ebay.pl', 'ebay.com.hk', 'ebay.com.sg', 'ebay.com.my',
        'ebay.ph', 'ebay.in', 'ebay.us', 'ebay.cn', 'ebay.co.jp',
    )
    EBAY_SHORT_HOSTS = ('ebay.to', 'ebay.us')

    def validate_ebay_url(self, url: str) -> bool:
        """
        Validate that the URL is from an eBay domain or recognised short link host.

        Accepts a wide range of formats:
        - /itm/<id>, /itm/<slug>/<id>, /itm/<id>?...
        - /p/<product-id>
        - URLs with query params (?_trkparms=, &hash=, etc.)
        - Regional eBay domains (.com, .co.uk, .de, .fr, .it, .com.au, ...)
        - Short URLs (ebay.to, ebay.us redirects)
        - URLs with trailing slashes, fragments, mixed case

        Raises ValidationError with a clear, user-actionable message on failure.
        """
        if not url or not isinstance(url, str):
            raise ValidationError("URL must be a non-empty string")

        url = url.strip()
        if not url:
            raise ValidationError("URL is empty")

        # Auto-prepend scheme if missing (common user mistake)
        if not re.match(r'^[a-zA-Z]+://', url):
            url = 'https://' + url

        try:
            parsed = urlparse(url)
        except Exception as e:
            raise ValidationError(f"Could not parse URL: {e}")

        netloc = parsed.netloc.lower().split(':')[0]
        # Strip leading www. and m. (mobile) prefixes
        for prefix in ('www.', 'm.', 'pages.'):
            if netloc.startswith(prefix):
                netloc = netloc[len(prefix):]
                break

        if not netloc:
            raise ValidationError("URL is missing a domain")

        # Accept any *.ebay.<tld> and known short hosts
        is_ebay_host = (
            netloc in self.EBAY_DOMAINS
            or netloc in self.EBAY_SHORT_HOSTS
            or netloc.startswith('ebay.')
            or '.ebay.' in netloc
        )
        if not is_ebay_host:
            raise ValidationError(
                "URL must be from an eBay domain (e.g. ebay.com, ebay.co.uk, ebay.de, ebay.to)"
            )

        # Short URLs will be resolved on fetch — accept them here
        if netloc in self.EBAY_SHORT_HOSTS:
            return True

        path = parsed.path or ''
        query = parsed.query or ''

        # Accept any of: /itm/, /p/, ?item=, ?itm=, or a path containing a long numeric id
        if (
            '/itm/' in path
            or '/p/' in path
            or re.search(r'[?&](item|itm)=\d{6,}', query)
            or re.search(r'/\d{10,}(?:[/?#]|$)', path)
        ):
            return True

        raise ValidationError(
            "URL does not look like an eBay item or product page. "
            "Expected formats: /itm/<id>, /p/<product-id>, or a short ebay.to link."
        )

    def normalize_ebay_url(self, url: str) -> str:
        """
        Return a canonical eBay item URL when possible, otherwise the original.
        Trims tracking params and resolves to a clean /itm/<id> form on .com.
        """
        try:
            item_id = self.extract_id_from_url(url)
            if item_id and item_id.isdigit() and len(item_id) >= 9:
                # Preserve the user's regional TLD if present
                parsed = urlparse(url if re.match(r'^[a-zA-Z]+://', url) else 'https://' + url)
                netloc = parsed.netloc.lower() or 'www.ebay.com'
                if not netloc.startswith('www.') and not netloc.startswith('m.'):
                    netloc = 'www.' + netloc
                return f"https://{netloc}/itm/{item_id}"
        except Exception:
            pass
        return url
    
    def _get_clean_text(self, element: Tag) -> str:
        """
        Extract and clean text from an element, handling duplicates and hidden text.
        Specific handling for eBay's tendency to duplicate text for accessibility.
        """
        if not element:
            return ""
            
        # Get text with separator to distinguish blocks
        text_content = element.get_text(separator='|', strip=True)
        parts = [p.strip() for p in text_content.split('|') if p.strip()]
        
        if not parts:
            return ""
            
        # Deduplicate adjacent identical parts (e.g. "Pre-owned|Pre-owned")
        deduped = []
        if parts:
            deduped.append(parts[0])
            for i in range(1, len(parts)):
                if parts[i] != parts[i-1]:
                    deduped.append(parts[i])
        
        # Check for full repetition (e.g. "Cond: New|Cond: New")
        if len(deduped) > 1 and len(deduped) % 2 == 0:
            mid = len(deduped) // 2
            if deduped[:mid] == deduped[mid:]:
                deduped = deduped[:mid]
                
        text = " ".join(deduped)
        
        # Clean specific eBay artifacts
        text = text.replace("More information", "")
        text = text.replace("About this item condition", "")
        text = text.replace("Read moreabout the seller notes", "")
        text = text.replace("Read lessabout the seller notes", "")
        
        # Clean up repeated hyphens or spaces from removals
        text = re.sub(r'\s+-\s*$', '', text)
        text = re.sub(r'\s+', ' ', text)
        
        return text.strip()

    def extract_product_data(self, soup: BeautifulSoup, url: str) -> ProductData:
        """
        Extract comprehensive product data from eBay page with multiple fallback strategies.
        
        Args:
            soup: BeautifulSoup object of the page
            url: Original product URL
            
        Returns:
            ProductData object with extracted information
            
        Raises:
            DataExtractionError: If critical data extraction fails
        """
        try:
            product_data = ProductData(url=url)
            
            # Extract title with multiple selectors
            title_selectors = [
                'h1[id="x-title-label-lbl"]',
                'h1.x-title-label-lbl',
                'h1.notranslate',
                '.x-title-label-lbl',
                'h1.x-item-title__mainTitle',
                '#vi-lkhdr-itmTitl',
                'h1[data-testid="x-item-title-mainTitle"]'
            ]
            
            product_data.title = self._extract_text_by_selectors(soup, title_selectors, "title")
            
            # Extract price with robust detection
            price_selectors = [
                '[data-testid="price"]',
                '[data-testid="x-price"]', 
                '[data-testid="x-bin-price"]',
                '.x-price-primary > span',
                '.x-price-approx__price',
                'span[itemprop="price"]',
                '#prcIsum',
                '#mm-saleDscPrc',
                '#prcIsum_bidPrice',
                '.kqq8oj > span:nth-child(1)',
                '.notranslate'
            ]
            
            product_data.price = self._extract_price(soup, price_selectors)
            
            # Extract condition. The current layout puts it in a labelled
            # summary row, so try that first and fall back to the older
            # standalone elements.
            product_data.condition = self._extract_labeled_value(
                soup, ['condition'], LABELS_CONDITION, 'condition'
            ) or self._extract_text_by_selectors(soup, [
                '.x-item-condition-value .ux-textspans',
                '.x-item-condition-max-view .ux-section__item',
                '[data-testid="x-item-condition"] span',
                '.x-item-condition-text',
                '#vi-itm-cond',
                '.vi-itm-cond',
                '.d-item-condition',
            ], "condition")

            # Extract seller information
            seller_selectors = [
                '[data-testid="str-title"] a',
                '.seller-persona-title a',
                '.seller-info a',
                '#mbgLink',
                'a[href*="feedback"]'
            ]
            
            product_data.seller = self._extract_text_by_selectors(soup, seller_selectors, "seller")
            
            # Extract shipping information
            product_data.shipping = self._extract_labeled_value(
                soup, ['shipping', 'delivery'], LABELS_SHIPPING, 'shipping'
            ) or self._extract_text_by_selectors(soup, [
                '[data-testid="ux-labels-values"] .ux-textspans--BOLD',
                '[data-testid="vi-price-ship"]',
                '#fshippingCost',
                '#shSummary',
            ], "shipping")
            
            # Extract brand and item specifics
            product_data.item_specifics = self._extract_item_specifics(soup)
            product_data.brand = product_data.item_specifics.get('Brand', '')
            
            # Extract description (including iframe content)
            product_data.description = self._extract_description(soup, url)

            # Additional fields for richer AI prompts
            product_data.location = self._extract_labeled_value(
                soup, ['itemLocation', 'location'], LABELS_LOCATION, 'location'
            ) or self._extract_text_by_selectors(soup, [
                '#itemLocation', '.item-location',
                '[data-testid="ux-seller-location"]', '.ux-seller-section__itemLocation',
            ], "location")

            product_data.returns_policy = self._extract_labeled_value(
                soup, ['returns'], LABELS_RETURNS, 'returns'
            ) or self._extract_text_by_selectors(soup, [
                '#vi-ret-accrd-txt', '.x-ret-accrd-txt', '.returns-policy',
            ], "returns")

            product_data.category = self._extract_breadcrumbs(soup)
            # Try to parse item id from URL or page
            product_data.item_id = self.extract_id_from_url(url)
            
            # Fallback: Extract from DOM if not found in URL
            if not product_data.item_id:
                product_data.item_id = self._extract_id_from_dom(soup)
                
            # One consolidated warning instead of a storm of per-field ones.
            missing = [
                name for name, value in (
                    ('title', product_data.title),
                    ('price', product_data.price),
                    ('condition', product_data.condition),
                    ('seller', product_data.seller),
                    ('shipping', product_data.shipping),
                    ('location', product_data.location),
                    ('returns', product_data.returns_policy),
                    ('category', product_data.category),
                ) if not value
            ]
            if missing:
                logger.warning(
                    f"Fields not found for {url}: {', '.join(missing)} "
                    "(interstitial page or unsupported listing layout)"
                )
            if product_data.title:
                logger.info(f"Successfully extracted product data for: {product_data.title[:50]}... (ID: {product_data.item_id})")
            return product_data
        
        except Exception as e:
            logger.error(f"Error extracting product data: {e}")
            raise DataExtractionError(f"Failed to extract product data: {e}")

    def extract_id_from_url(self, url: str) -> Optional[str]:
        """Extract eBay Item ID from a wide variety of URL formats."""
        if not url:
            return None
        try:
            parsed = urlparse(url if re.match(r'^[a-zA-Z]+://', url) else 'https://' + url)

            # Standard /itm/<id> or /itm/<slug>/<id>
            if '/itm/' in parsed.path:
                for p in reversed(parsed.path.split('/')):
                    digits = re.sub(r'\D', '', p)
                    if digits.isdigit() and len(digits) >= 9:
                        return digits

            # /p/<product-id> (product-page form, may not be a listing id but still useful)
            if '/p/' in parsed.path:
                for p in reversed(parsed.path.split('/')):
                    digits = re.sub(r'\D', '', p)
                    if digits.isdigit() and len(digits) >= 6:
                        return digits

            # Query-param forms: ?item=, ?itm=, ?hash=item123:...
            query = parse_qs(parsed.query or '')
            for key in ('item', 'itm', 'iid'):
                if key in query and query[key]:
                    digits = re.sub(r'\D', '', query[key][0])
                    if digits.isdigit() and len(digits) >= 9:
                        return digits
            hash_val = query.get('hash', [''])[0]
            m = re.search(r'item(\d{9,})', hash_val)
            if m:
                return m.group(1)

            # Fallback: any 10+ digit number anywhere in path
            m = re.search(r'(\d{10,})', parsed.path)
            if m:
                return m.group(1)
        except Exception:
            pass
        return None

    def _extract_id_from_dom(self, soup: BeautifulSoup) -> Optional[str]:
        """Extract eBay Item ID from DOM."""
        try:
            # Look for "eBay item number:" text pattern
            id_node = soup.find(string=re.compile(r"eBay item number:", re.IGNORECASE))
            if id_node:
                text = id_node.strip() if isinstance(id_node, str) else id_node.get_text(strip=True)
                match = re.search(r'(\d{9,})', text)
                if match:
                    return match.group(1)
            
            # Try specific selector
            elem = soup.select_one('.ux-layout-section__textual-display--itemId span, .d-item-id')
            if elem:
                match = re.search(r'(\d{9,})', elem.get_text(strip=True))
                if match:
                    return match.group(1)
        except Exception:
            pass
        return None

    def _extract_text_by_selectors(self, soup: BeautifulSoup, selectors: List[str], field_name: str) -> str:
        """Extract text using multiple CSS selectors with fallbacks."""
        for selector in selectors:
            try:
                element = soup.select_one(selector)
                if element:
                    text = self._get_clean_text(element)
                    if text:
                        logger.debug(f"Extracted {field_name} using selector: {selector}")
                        return text
            except Exception as e:
                logger.debug(f"Selector {selector} failed for {field_name}: {e}")
                continue
        
        logger.debug(f"No {field_name} found using any selector")
        return ""
    
    # eBay renders most of the summary panel as label/value rows. The class
    # modifier (ux-labels-values--condition) is the fast path; the visible
    # label text is the durable fallback, because eBay reshuffles class names
    # far more often than it renames the labels a buyer reads.
    LABEL_ROW_VALUE = '.ux-labels-values__values'

    def _extract_labeled_value(self, soup: BeautifulSoup, modifiers: List[str],
                               labels: List[str], field_name: str) -> str:
        """Read a value from an eBay label/value row, by class then by label text."""
        for modifier in modifiers:
            try:
                for row in soup.select(f'[class*="ux-labels-values--{modifier}"]'):
                    value_node = row.select_one(self.LABEL_ROW_VALUE)
                    text = self._get_clean_text(value_node) if value_node else ''
                    if text:
                        logger.debug(f"Extracted {field_name} from ux-labels-values--{modifier}")
                        return text
            except Exception as e:
                logger.debug(f"Label modifier {modifier} failed for {field_name}: {e}")

        wanted = {normalize_label(label) for label in labels}

        # Search the text nodes rather than the elements. Calling get_text()
        # on every div re-walks that div's whole subtree, so on a real listing
        # (20k+ elements, deeply nested) the element scan is quadratic and
        # costs hundreds of milliseconds per field. Label text is short and
        # lives in exactly one text node, so matching strings directly is both
        # faster and more precise.
        try:
            matches = soup.find_all(
                string=lambda s: is_label_candidate(s) and normalize_label(s) in wanted
            )
        except Exception:
            return ''

        for text_node in matches:
            parent = text_node.parent
            if parent is None:
                continue
            value = self._value_near_label(parent)
            if value:
                logger.debug(f"Extracted {field_name} by label text")
                return value
        return ''

    def _value_near_label(self, label_node: Tag, max_levels: int = 4) -> str:
        """Find the value that belongs to a label node.

        Walks up a few ancestors looking first for eBay's explicit value
        container, then for the next sibling cell. Anything that just repeats
        the label is rejected so a row never reports its own heading.
        """
        label_text = normalize_label(label_node.get_text(' ', strip=True))
        node: Optional[Tag] = label_node
        for _ in range(max_levels):
            if node is None:
                break
            parent = node.parent
            if parent is None:
                break
            try:
                value_node = parent.select_one(self.LABEL_ROW_VALUE)
            except Exception:
                value_node = None
            if value_node is not None:
                text = self._get_clean_text(value_node)
                if text and normalize_label(text) != label_text:
                    return text
            sibling = node.find_next_sibling()
            while sibling is not None:
                if isinstance(sibling, Tag):
                    text = self._get_clean_text(sibling)
                    if text and normalize_label(text) != label_text:
                        return text
                sibling = sibling.find_next_sibling()
            node = parent
        return ''

    # Words meaning "breadcrumb" on the regional sites, matched against the
    # nav's aria-label. ebay.fr labels it "Fil d'Ariane", so an English-only
    # match returned no category at all on every non-English listing.
    BREADCRUMB_ARIA = (
        'readcrumb', 'fil d\'ariane', 'ariane', 'navigationspfad', 'brotkrumen',
        'percorso', 'ruta de navegaci', 'kruimelpad', 'okruszki',
    )

    HOME_LINK_TEXTS = {'ebay', 'back to home page', 'accueil', 'startseite',
                       'home', 'inicio', 'pagina iniziale'}

    def _extract_breadcrumbs(self, soup: BeautifulSoup) -> str:
        """Category path, joined with ' > '."""
        candidates: List[Tag] = []
        for selector in ('.seo-breadcrumb-text', '#vi-VR-brumb-lnkLst',
                         '.breadcrumbs', '.bc-w',
                         '[itemtype*="BreadcrumbList" i]'):
            try:
                node = soup.select_one(selector)
            except Exception:
                continue
            if node is not None:
                candidates.append(node)

        # Any <nav> whose aria-label reads as "breadcrumb" in some language,
        # then, as a last resort, any nav holding a list of links.
        try:
            navs = soup.find_all('nav')
        except Exception:
            navs = []
        labelled, generic = [], []
        for nav in navs:
            aria = normalize_label(nav.get('aria-label') or '')
            (labelled if any(word in aria for word in self.BREADCRUMB_ARIA) else generic).append(nav)
        candidates.extend(labelled)
        candidates.extend(generic)

        for node in candidates:
            parts = [a.get_text(' ', strip=True) for a in node.select('a')]
            if not parts:
                parts = [li.get_text(' ', strip=True) for li in node.select('li')]
            cleaned = [p for p in dict.fromkeys(parts)
                       if p and normalize_label(p) not in self.HOME_LINK_TEXTS]
            if len(cleaned) >= 1:
                return " > ".join(cleaned[:8])
        return ''

    def _extract_price(self, soup: BeautifulSoup, selectors: List[str]) -> str:
        """Extract price with currency symbol validation."""
        currency_symbols = ['$', '£', '€', '¥', '₹', 'CAD', 'USD', 'GBP', 'EUR']
        
        for selector in selectors:
            try:
                element = soup.select_one(selector)
                if element:
                    text = element.get_text(strip=True)
                    if any(symbol in text for symbol in currency_symbols):
                        logger.debug(f"Extracted price using selector: {selector}")
                        return text
            except Exception as e:
                logger.debug(f"Price selector {selector} failed: {e}")
                continue
        
        # Fallback: search for clipped price elements
        for element in soup.select('.clipped, .clipped > span'):
            try:
                text = element.get_text(strip=True)
                if any(symbol in text for symbol in currency_symbols) and any(ch.isdigit() for ch in text):
                    logger.debug("Extracted price from clipped element")
                    return text
            except Exception:
                continue
        
        logger.debug("No price found using any method")
        return ""
    
    def _extract_item_specifics(self, soup: BeautifulSoup) -> Dict[str, str]:
        """Extract comprehensive item specifics including dimensions, materials, etc."""
        specifics = {}
        
        try:
            # Method 1: Traditional eBay specifics format
            specifics_rows = soup.select('.u-flL.condText')
            for row in specifics_rows:
                text = self._get_clean_text(row)
                if ':' in text:
                    key, value = text.split(':', 1)
                    specifics[key.strip()] = value.strip()
            
            # Method 2: Definition list format (more comprehensive)
            for container in soup.select('dl, .ux-labels-values, .x-about-this-item__table, .ux-layout-section-evo__item'):
                try:
                    dts = container.select('dt, .ux-labels-values__labels-content, .ux-layout-section__item dt')
                    dds = container.select('dd, .ux-labels-values__values-content, .ux-layout-section__item dd')
                    if dts and dds and len(dts) == len(dds):
                        for dt, dd in zip(dts, dds):
                            key = self._get_clean_text(dt)
                            value = self._get_clean_text(dd)
                            if key and value:
                                specifics[key] = value
                except Exception:
                    continue
            
            # Method 3: Table rows (including detailed specifications)
            for tr in soup.select('#viTabs_0_is tr, table tr, .ux-table-view__row'):
                try:
                    tds = tr.select('td, th, .ux-textspans')
                    if len(tds) >= 2:
                        key = self._get_clean_text(tds[0])
                        value = self._get_clean_text(tds[1])
                        if key and value and len(key) < 60:  # Reasonable key length
                            specifics[key] = value
                except Exception:
                    continue
            
            # Method 4: Structured data (JSON-LD)
            try:
                for script in soup.select('script[type="application/ld+json"]'):
                    data = json.loads(script.get_text(strip=True))
                    if isinstance(data, dict):
                        # Extract common product properties
                        if 'brand' in data:
                            specifics.setdefault('Brand', data['brand'].get('name', '') if isinstance(data['brand'], dict) else str(data['brand']))
                        if 'color' in data:
                            specifics.setdefault('Color', str(data['color']))
                        if 'material' in data:
                            specifics.setdefault('Material', str(data['material']))
                        if 'model' in data:
                            specifics.setdefault('Model', str(data['model']))
                        if 'width' in data and 'height' in data:
                            specifics.setdefault('Dimensions', f"{data.get('width')} x {data.get('height')}")
                        if 'additionalProperty' in data and isinstance(data['additionalProperty'], list):
                            for prop in data['additionalProperty']:
                                if isinstance(prop, dict) and 'name' in prop and 'value' in prop:
                                    specifics.setdefault(str(prop['name']), str(prop['value']))
            except Exception as e:
                logger.debug(f"Could not extract JSON-LD specifics: {e}")
            
            logger.debug(f"Extracted {len(specifics)} item specifics")
            
        except Exception as e:
            logger.warning(f"Error extracting item specifics: {e}")
        
        return specifics
    
    def _extract_description(self, soup: BeautifulSoup, base_url: str) -> str:
        """Extract product description including iframe content."""
        description_text = ""
        
        try:
            # Method 1: Standard description containers
            description_selectors = [
                '.product-description',
                '#viTabs_0_pnlDesc',
                '#desc_div',
                '#descArea',
                '.x-item-description',
                'article[itemprop="description"]'
            ]
            
            for selector in description_selectors:
                element = soup.select_one(selector)
                if element:
                    description_text = element.get_text(separator=' ', strip=True)
                    if description_text:
                        logger.debug(f"Found description using selector: {selector}")
                        break
            
            # Method 2: Iframe content extraction
            if not description_text:
                iframe_selectors = [
                    '#desc_wrapper_ctr iframe',
                    'iframe#desc_ifr',
                    'iframe[src*="desc"]'
                ]
                
                for selector in iframe_selectors:
                    iframe = soup.select_one(selector)
                    if iframe and (iframe.get('src') or iframe.get('data-src')):
                        try:
                            iframe_src = iframe.get('src') or iframe.get('data-src')
                            iframe_url = urljoin(base_url, iframe_src)
                            
                            response = safe_request(self.session, iframe_url, timeout=15).response
                            if response:
                                iframe_soup = BeautifulSoup(response.content, 'html.parser')
                                description_text = iframe_soup.get_text(separator=' ', strip=True)
                                if description_text:
                                    logger.debug("Extracted description from iframe")
                                    break
                        except Exception as e:
                            logger.debug(f"Failed to extract iframe content: {e}")
                            continue
            
        except Exception as e:
            logger.warning(f"Error extracting description: {e}")
        
        return description_text[:5000]  # Limit description length
    
    def get_product_images(self, soup: BeautifulSoup, base_url: str) -> List[str]:
        """
        Extract high-quality product image URLs with smart filtering.
        
        Args:
            soup: BeautifulSoup object of the page
            base_url: Base URL for relative URL resolution
            
        Returns:
            List of high-quality image URLs
        """
        # Preserve discovery order as shown on the page; de-duplicate while keeping order
        image_urls: List[str] = []
        seen: set = set()
        def append_unique(url: Optional[str]) -> None:
            if not url:
                return
            if url not in seen:
                seen.add(url)
                image_urls.append(url)
        
        try:
            # Primary gallery containers (highest priority)
            gallery_selectors = [
                '[data-testid="ux-image-carousel"]',
                '.ux-image-carousel',
                '.ux-image-filmstrip-carousel',
                '#mainImgHldr',
                '#PicturePanel',
                '#vi_main_img_fs',
                '#mainImgId',
                '#pic'
            ]
            
            for selector in gallery_selectors:
                containers = soup.select(selector)
                for container in containers:
                    images = container.select('img')
                    for img in images:
                        urls = self._extract_image_urls_from_element(img, base_url)
                        for u in urls:
                            append_unique(u)
            
            # Fallback: Open Graph and JSON-LD images
            if not image_urls:
                for u in self._extract_fallback_images(soup):
                    append_unique(u)
            
            # Convert to high-resolution URLs
            high_res_urls_ordered: List[str] = []
            seen_hr: set = set()
            for url in image_urls:
                hr = self.get_high_res_image_url(url)
                if hr not in seen_hr:
                    seen_hr.add(hr)
                    high_res_urls_ordered.append(hr)

            logger.info(f"Extracted {len(high_res_urls_ordered)} product images (order preserved)")
            return high_res_urls_ordered
            
        except Exception as e:
            logger.error(f"Error extracting images: {e}")
            return []
    
    def _extract_image_urls_from_element(self, img_element, base_url: str) -> List[str]:
        """Extract all possible image URLs from an img element."""
        urls = []
        
        # Primary sources
        primary_url = img_element.get('src') or img_element.get('data-src') or img_element.get('data-zoom-src')
        if primary_url:
            urls.append(primary_url)
        
        # Srcset parsing for highest resolution
        srcset = img_element.get('srcset')
        if srcset:
            try:
                srcset_urls = [url.strip().split(' ')[0] for url in srcset.split(',') if url.strip()]
                if srcset_urls:
                    urls.append(srcset_urls[-1])  # Highest resolution typically last
            except Exception:
                pass
        
        # Process URLs
        processed_urls = []
        for url in urls:
            if not url:
                continue
            
            # Handle protocol-relative URLs
            if url.startswith('//'):
                url = 'https:' + url
            elif url.startswith('/'):
                url = urljoin(base_url, url)
            
            # Filter out non-product images
            if self._is_valid_product_image(url):
                processed_urls.append(url)
        
        return processed_urls
    
    def _is_valid_product_image(self, url: str) -> bool:
        """
        Check if URL appears to be a valid product image with improved filtering.
        
        Args:
            url: Image URL to validate
            
        Returns:
            True if URL is likely a product image
        """
        url_lower = url.lower()
        
        # Exclude common non-product image patterns
        exclude_patterns = [
            'logo', 'banner', 'sprite', 'icon', 'placeholder',
            'seller', 'feedback', 'payments', 'shipping',
            'paypal', 'visa', 'mastercard', 'amex', 'discover',
            'returns', 'delivery', 'warranty', 'guarantee',
            'star', 'rating', 'badge', 'award',
            'similar', 'recommended', 'sponsored', 'advertisement',
            'btn_', 'button', 'arrow', 'chevron',
            'social', 'facebook', 'twitter', 'instagram',
            '/s-l64/', '/s-l140/', '/s-l225/',  # Exclude thumbnail sizes
            '/_p/', '/_g/', '/_n/',  # Pattern-based thumbnails
            'thumb', 'thumbnail', 'small', 'tiny',
            'ebay_sticker', 'ebay_badge', 'authentic'
        ]
        
        # Strong indicators this is NOT a product image
        if any(pattern in url_lower for pattern in exclude_patterns):
            return False
        
        # Must be from eBay image CDN (ebayimg.com)
        if 'ebayimg.com' not in url_lower:
            return False
        
        # Include only image file types
        valid_extensions = ['jpg', 'jpeg', 'png', 'webp']
        if not any(ext in url_lower for ext in valid_extensions):
            return False
        
        # Exclude very small images (likely thumbnails or icons)
        # Look for size indicators in URL
        small_sizes = ['/s-l64', '/s-l96', '/s-l140', '/s-l225']
        if any(size in url for size in small_sizes):
            return False
        
        # Must contain item number or product identifier
        # eBay product images typically have numeric identifiers
        has_numbers = any(char.isdigit() for char in url)
        if not has_numbers:
            return False
        
        return True
    
    def _extract_fallback_images(self, soup: BeautifulSoup) -> List[str]:
        """Extract images from Open Graph and JSON-LD as fallback."""
        fallback_urls = []
        
        # Open Graph image
        og_image = soup.select_one('meta[property="og:image"]')
        if og_image and og_image.get('content'):
            url = og_image.get('content')
            if 'ebayimg' in url.lower():
                fallback_urls.append(url)
        
        # JSON-LD images
        try:
            for script in soup.select('script[type="application/ld+json"]'):
                data = json.loads(script.get_text(strip=True))
                if isinstance(data, dict) and 'image' in data:
                    images = data['image']
                    if isinstance(images, list):
                        for img_url in images:
                            if isinstance(img_url, str) and 'ebayimg' in img_url.lower():
                                fallback_urls.append(img_url)
                    elif isinstance(images, str) and 'ebayimg' in images.lower():
                        fallback_urls.append(images)
        except Exception:
            pass
        
        return fallback_urls
    
    def get_high_res_image_url(self, img_url: str) -> str:
        """
        Convert eBay image URL to highest available resolution.
        
        Args:
            img_url: Original image URL
            
        Returns:
            High-resolution image URL
        """
        try:
            # eBay image resolution mappings
            resolution_mappings = {
                's-l64': 's-l1600',
                's-l140': 's-l1600', 
                's-l300': 's-l1600',
                's-l500': 's-l1600',
                's-l640': 's-l1600'
            }
            
            for low_res, high_res in resolution_mappings.items():
                if low_res in img_url:
                    return img_url.replace(low_res, high_res)
            
            return img_url
            
        except Exception:
            return img_url
    
    def download_image(self, img_url: str, save_path: str) -> Optional[str]:
        """
        Download image with proper extension detection and error handling.
        
        Args:
            img_url: Image URL to download
            save_path: Base path for saving (without extension)
            
        Returns:
            Final saved file path or None if download failed
        """
        try:
            response = safe_request(self.session, img_url, timeout=30).response
            if not response:
                return None

            content_type = response.headers.get('Content-Type', '').lower()
            extension = self._get_image_extension(content_type, img_url)
            payload = response.content

            # eBay serves WebP to modern browsers, which most listing tools and
            # photo editors still refuse to open. Normalising to JPEG at
            # download time means the product folders only ever contain files
            # that can be uploaded straight to another marketplace.
            if SAVE_IMAGES_AS_JPEG and extension != 'jpg':
                converted = convert_bytes_to_jpeg(payload)
                if converted is not None:
                    payload, extension = converted, 'jpg'
                else:
                    logger.debug(f"Keeping original format for {img_url} (conversion failed)")

            final_path = f"{save_path}.{extension}"
            with open(final_path, 'wb') as f:
                f.write(payload)

            logger.debug(f"Downloaded image: {final_path}")
            return final_path

        except Exception as e:
            logger.error(f"Error downloading image {img_url}: {e}")
            return None
    
    def _get_image_extension(self, content_type: str, url: str) -> str:
        """Determine image file extension from content type or URL."""
        # From content type
        if 'image/jpeg' in content_type or 'image/jpg' in content_type:
            return 'jpg'
        elif 'image/png' in content_type:
            return 'png'
        elif 'image/webp' in content_type:
            return 'webp'
        
        # From URL
        path = urlparse(url).path.lower()
        extension = os.path.splitext(path)[1].lstrip('.')
        if extension in {'jpg', 'jpeg', 'png', 'webp'}:
            return 'jpg' if extension == 'jpeg' else extension
        
        # Default
        return 'jpg'
    
    # Phrases that appear on eBay's bot-check / interstitial pages but not on
    # real listings. Deliberately specific: generic words like "robot" false-
    # positive on legitimate listings (e.g. robot vacuum cleaners). The
    # non-English entries matter because a regional site serves its challenge
    # page in the local language.
    BOT_PAGE_MARKERS = (
        # English
        'pardon our interruption',
        'checking your browser',
        'please verify yourself',
        'verify yourself to continue',
        'reference id:',
        'unusual traffic',
        'splashui/captcha',
        'are you a human',
        'access to this page has been denied',
        'enable javascript and cookies to continue',
        # French (ebay.fr)
        'veuillez patienter',
        "vérifiez que vous n'êtes pas un robot",
        'excusez-nous pour cette interruption',
        'activez javascript',
        # German (ebay.de / .at / .ch)
        'entschuldigen sie die unterbrechung',
        'bitte bestätigen sie',
        'sind sie ein mensch',
        # Italian / Spanish
        'ci scusiamo per l',
        'perdona la interrupción',
        'verifica que eres humano',
    )

    # Elements that only ever appear on a genuine item page. Their presence
    # is what keeps the structural check below from firing on a real listing
    # whose class names have drifted.
    LISTING_MARKERS = (
        'h1.x-item-title__mainTitle', '[data-testid="x-item-title"]', '#itemTitle',
        '.x-price-primary', '[data-testid="x-price-primary"]', '#prcIsum',
        '.ux-labels-values', '#vi-desc-maincntr', '.x-item-condition-value',
        '[itemprop="price"]', 'meta[property="og:title"]', '#desc_ifr',
    )

    def _looks_like_bot_page(self, soup: BeautifulSoup) -> str:
        """Return why a page looks like a bot-check, or '' if it looks real.

        Returning the reason rather than a bare bool matters for support: the
        log now says which rule fired, so a false positive can be told from a
        genuine challenge without guessing.

        Marker text is the fast path. The structural rule is deliberately
        conservative — it needs *every* listing marker to be absent *and* no
        eBay-hosted image anywhere on the page — because wrongly classifying
        a real listing as a block would silently skip good data.
        """
        try:
            text = soup.get_text(" ", strip=True).lower()
            head = text[:5000]
            for marker in self.BOT_PAGE_MARKERS:
                if marker in head:
                    return f"challenge text: {marker!r}"

            if len(text) < 400 and not soup.select_one('h1'):
                return "empty shell: under 400 chars and no heading"

            if soup.select_one(', '.join(self.LISTING_MARKERS)) is not None:
                return ''

            has_item_image = any(
                'ebayimg.com' in (img.get('src') or img.get('data-src') or
                                  img.get('data-srcset') or '')
                for img in soup.find_all('img')
            )
            if not has_item_image:
                return "no listing element and no eBay-hosted image"
        except Exception as e:
            logger.debug(f"Bot-page check failed: {e}")
        return ''

    def save_blocked_page(self, url: str, html: bytes) -> Optional[Path]:
        """Write a page classified as a bot-check to `blocked_pages/`.

        Without this there is no way to tell a genuine eBay challenge from a
        detection false positive — both look identical from the log. Keeping
        the actual HTML makes that question answerable in seconds. Old
        captures are pruned so the folder cannot grow without bound.
        """
        try:
            folder = Path.cwd() / BLOCKED_PAGES_DIR
            folder.mkdir(parents=True, exist_ok=True)

            existing = sorted(folder.glob('blocked_*.html'), key=lambda p: p.stat().st_mtime)
            for stale in existing[:max(0, len(existing) - BLOCKED_PAGES_KEEP + 1)]:
                stale.unlink(missing_ok=True)

            item_id = self.extract_id_from_url(url) or 'unknown'
            # Microseconds, not seconds: two listings blocked in the same
            # second would otherwise overwrite each other's capture.
            stamp = datetime.now().strftime('%Y%m%d_%H%M%S_%f')
            target = folder / f"blocked_{item_id}_{stamp}.html"
            target.write_bytes(html[:2_000_000])
            logger.info(f"Saved the blocked page to {target} for diagnosis")
            return target
        except OSError as e:
            logger.debug(f"Could not save the blocked page: {e}")
            return None

    BLOCKED_MESSAGE = (
        "eBay refused the request (anti-bot check). This is rate limiting, not a "
        "problem with the link — eBay throttles bursts from one IP. Wait a few "
        "minutes, then use Retry failed; the app now slows itself down "
        "automatically after each block."
    )

    def scrape_product(self, url: str, max_attempts: int = 3) -> ScrapingResult:
        """
        Main scraping method that orchestrates the entire process.

        Retries up to ``max_attempts`` times with a fresh browser identity
        (new session, cookies and User-Agent) whenever eBay serves a
        bot-check page or the page yields no usable data. Returns a
        ScrapingResult with success/failure and a detailed error message —
        this method never raises.
        """
        try:
            # Validate URL (raises ValidationError on bad input)
            self.validate_ebay_url(url)
            # Normalize to a canonical form when we can extract an item id
            url = self.normalize_ebay_url(url.strip())
        except ValidationError as e:
            return ScrapingResult(success=False, error_message=f"Invalid URL: {e}. Please use a valid eBay product URL.")
        except Exception as e:
            return ScrapingResult(success=False, error_message=f"Invalid URL: {e}")

        with self._fetch_lock:
            return self._scrape_product_locked(url, max_attempts)

    def _scrape_product_locked(self, url: str, max_attempts: int) -> ScrapingResult:
        last_error = "Unknown error"
        blocked = False

        for attempt in range(1, max_attempts + 1):
            try:
                if attempt > 1:
                    # Rotate identity once. A second rotation is pointless: if
                    # a fresh session and User-Agent did not clear the block,
                    # the decision is being made on the IP, and rebuilding the
                    # session again only doubles the traffic (each rebuild
                    # also re-runs the homepage warm-up) against an edge that
                    # is already refusing us. Past that, only waiting helps.
                    if attempt == 2:
                        self.refresh_identity()
                    base = 6 if blocked else 2
                    time.sleep(min(base ** attempt, 30) + random.uniform(0.5, 2.0))
                else:
                    time.sleep(random.uniform(0.5, 2.0))

                self.prepare_for(url)

                # Fetch page (requests follows redirects by default, handling ebay.to/ebay.us)
                outcome = safe_request(self.session, url, timeout=30)

                if outcome.reason == 'not_found':
                    # Definitive: the listing is gone. Retrying cannot help,
                    # and burning two more attempts on it slows the batch.
                    self.consecutive_blocks = 0
                    return ScrapingResult(
                        success=False,
                        error_message="The listing no longer exists on eBay (removed, ended or sold).",
                    )

                if outcome.response is None:
                    if outcome.reason == 'blocked':
                        blocked = True
                        self.consecutive_blocks += 1
                        last_error = self.BLOCKED_MESSAGE
                        logger.warning(
                            f"Blocked by eBay ({outcome.detail}) for {url} "
                            f"(attempt {attempt}/{max_attempts})"
                        )
                    else:
                        last_error = (
                            f"Could not reach eBay ({outcome.detail or 'network error'}). "
                            "Check the internet connection and retry."
                        )
                    continue

                # Parse HTML
                body = response_content(outcome.response)
                soup = BeautifulSoup(body, 'html.parser')

                # Check for blocked/captcha/interstitial pages
                block_reason = self._looks_like_bot_page(soup)
                if block_reason:
                    blocked = True
                    self.consecutive_blocks += 1
                    last_error = self.BLOCKED_MESSAGE
                    logger.warning(
                        f"Bot-check page served for {url} "
                        f"(attempt {attempt}/{max_attempts}) — {block_reason}"
                    )
                    if attempt == 1:
                        # Keep one copy per listing, from the first attempt,
                        # so the classification can be checked afterwards.
                        self.save_blocked_page(url, body)
                    continue

                # Extract data
                product_data = self.extract_product_data(soup, url)
                image_urls = self.get_product_images(soup, url)

                # Validate we got essential data
                if not product_data.title:
                    if not image_urls and not product_data.price:
                        # Nothing at all came back: this is a challenge page
                        # that slipped past the checks above, not a listing
                        # whose layout we failed to parse.
                        blocked = True
                        self.consecutive_blocks += 1
                        last_error = self.BLOCKED_MESSAGE
                        logger.warning(
                            f"Empty listing page for {url} "
                            f"(attempt {attempt}/{max_attempts}); treating as a block"
                        )
                    else:
                        last_error = (
                            "Could not extract the product title. The listing may have "
                            "ended or its layout is not supported."
                        )
                        logger.warning(
                            f"No title extracted for {url} "
                            f"(attempt {attempt}/{max_attempts}); retrying with a fresh identity"
                        )
                    continue

                self.consecutive_blocks = 0
                return ScrapingResult(
                    success=True,
                    product_data=product_data,
                    image_urls=image_urls
                )

            except NetworkError as e:
                last_error = f"Network error: {e}. Check your internet connection."
            except DataExtractionError as e:
                last_error = f"Could not extract product data: {e}"
            except Exception:
                logger.error(f"Unexpected error in scrape_product (attempt {attempt}): {traceback.format_exc()}")
                last_error = "An unexpected error occurred. Please try again."

        return ScrapingResult(success=False, error_message=last_error)


def response_content(response: requests.Response) -> bytes:
    """Raw bytes of a response, tolerating a broken transfer encoding."""
    try:
        return response.content
    except Exception as e:
        logger.warning(f"Could not read response body: {e}")
        return b''


# =============================================================================
# LOCAL CSV FALLBACK
# =============================================================================

def append_to_local_csv(product_data: ProductData, filename: str = 'EbayStore_Products.csv') -> bool:
    """
    Append product data to local CSV file as fallback.
    
    Args:
        product_data: ProductData object to append
        filename: CSV filename
        
    Returns:
        True if successful, False otherwise
    """
    try:
        csv_path = Path.cwd() / filename
        header = [
            'Scraped At', 'eBay URL', 'Title', 'Price', 'Condition',
            'Brand', 'Seller', 'Shipping', 'Description', 'Item Specifics'
        ]
        
        item_specifics_str = " | ".join([
            f"{k}: {v}" for k, v in product_data.item_specifics.items()
        ])
        
        row = [
            datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            product_data.url,
            product_data.title,
            product_data.price,
            product_data.condition,
            product_data.brand,
            product_data.seller,
            product_data.shipping,
            (product_data.description or '')[:1000],
            item_specifics_str,
        ]
        
        file_exists = csv_path.exists()
        with open(csv_path, 'a', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            if not file_exists:
                writer.writerow(header)
            writer.writerow(row)
        
        logger.info(f"Appended product data to local CSV: {filename}")
        return True
        
    except Exception as e:
        logger.error(f"Error appending to local CSV: {e}")
        return False

# =============================================================================
# AI PROCESSING WITH GEMINI - ENHANCED VERSION
# =============================================================================



class AIProcessor:
    """AI processing against whichever provider the user selected.

    Every supported provider speaks the OpenAI chat-completions shape, so this
    class only needs a client and a model name — nothing below this point
    knows or cares which provider is in use.

    Accepts either an AISettings (the normal path) or a bare API key string,
    which keeps `AIProcessor("gsk_...")` working exactly as `GroqProcessor`
    did before providers existed.
    """

    def __init__(self, settings: Any, model: str = ''):
        if isinstance(settings, AISettings):
            self.settings = settings
        else:
            # Legacy call style: a plain Groq key.
            self.settings = AISettings(
                provider=get_provider(DEFAULT_PROVIDER),
                api_key=str(settings or ''),
                model=model,
            )
        self.api_key = self.settings.api_key
        self.provider = self.settings.provider
        self.cache = ResponseCache()
        self._configure_api()
        self.platform_agent = PlatformAgent(self.client, self.model, self.cache)

    def _configure_api(self) -> None:
        """Build the provider client.

        Only construction problems are caught here — an unusable key is not
        detected until the first request, which is where the rate-limit and
        authentication messages come from.
        """
        self.client = build_ai_client(self.settings)
        self.model = self.settings.model_name
        logger.info(f"AI provider configured: {self.provider.label} ({self.model})")

    def chat_with_ai(self, user_message: str, context: Optional[Dict] = None) -> str:
        """
        Interactive chat with AI for custom requests.
        
        Args:
            user_message: User's message/question
            context: Optional context (product data, raw text, etc.)
            
        Returns:
            AI response
        """
        try:
            context_str = ""
            if context:
                context_str = f"\n\nCONTEXT:\n{json.dumps(context, ensure_ascii=False, indent=2)}"
            
            prompt = f"""
You are a helpful AI assistant specializing in e-commerce product listings and marketplace optimization.

USER MESSAGE:
{user_message}
{context_str}

Provide a helpful, accurate response. If the user is asking for a product description, use the context provided and generate a clean, professional description.
"""
            
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                temperature=0.7,
                max_tokens=2000
            )
            return (response.choices[0].message.content or '').strip()

        except Exception as e:
            raise_ai_error(e)
    
    def clean_product_data(self, product_data: ProductData) -> Dict[str, str]:
        """
        Clean and standardize product data using AI.
        
        Args:
            product_data: Raw product data to clean
            
        Returns:
            Dictionary with cleaned fields
        """
        try:
            prompt = self._build_cleaning_prompt(product_data)
            
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                temperature=0.3,
                max_tokens=2000
            )
        except Exception as e:
            raise_ai_error(e)

        cleaned_data = self._parse_json_response(response.choices[0].message.content)
        if cleaned_data:
            logger.info("Successfully cleaned product data with Groq")
            return cleaned_data
        logger.warning("Groq response was not valid JSON")
        return {}
    
    def _build_cleaning_prompt(self, product_data: ProductData) -> str:
        """Build prompt for product data cleaning."""
        return f"""
You are a precise product data cleaner and optimizer. Given raw scraped data from an eBay item, 
return clean, standardized fields without hallucinating or adding information not present in the source.

INPUT DATA:
{json.dumps(asdict(product_data), ensure_ascii=False, indent=2)}

TASK:
Clean and standardize the product data following these rules:

1. **title**: Create a concise, professional title. Remove seller noise, excessive punctuation, 
   emoji, and marketing fluff. Keep essential product information.

2. **price**: Keep currency symbol and number exactly as seen. Do not convert currencies or 
   change formatting.

3. **condition**: Normalize to standard values when possible:
   - "New" (brand new, unopened)
   - "New with tags" 
   - "New without tags"
   - "Pre-owned" (general used condition)
   - "Used - Excellent" (minimal wear)
   - "Used - Very Good" (light wear)
   - "Used - Good" (moderate wear)
   - "Used - Fair" (significant wear)
   - "For parts or not working"

4. **brand**: Extract and clean brand name if clearly identifiable. Leave empty if uncertain.

5. **cleaned_description**: Rewrite the description for clarity and professionalism:
   - Remove redundant information
   - Organize key features logically
   - Keep all factual product details
   - Remove seller-specific language
   - Improve readability
   - Maintain original measurements, specifications, and technical details
   - Include additional fields if present (location, returns_policy, category, item_id)

OUTPUT FORMAT:
Return ONLY a valid JSON object with these exact keys:
{{
  "title": "cleaned title",
  "price": "original price format", 
  "condition": "standardized condition",
  "brand": "brand name or empty string",
  "cleaned_description": "professionally rewritten description"
}}

IMPORTANT: Output ONLY the JSON object. No additional text or markdown formatting.
"""
    
    def _parse_json_response(self, response_text: str) -> Dict[str, Any]:
        """Safely parse JSON content from Groq response, handling code fences and extra text."""
        try:
            if not response_text:
                return {}
            
            cleaned = response_text.strip()
            # Remove markdown code fences if present
            if cleaned.startswith("```"):
                cleaned = re.sub(r"^```(?:json)?", "", cleaned, flags=re.IGNORECASE).strip()
                if cleaned.endswith("```"):
                    cleaned = cleaned[:-3].strip()
            # Extract first JSON object bounds
            start = cleaned.find("{")
            end = cleaned.rfind("}")
            if start != -1 and end != -1 and end > start:
                json_str = cleaned[start:end+1]
                return json.loads(json_str)
        except Exception as e:
            logger.warning(f"Failed to parse JSON from Groq response: {e}")
        return {}
    
    def enhance_for_resale(self, product_data: ProductData, target_platform: str = "general") -> Dict[str, str]:
        """
        Generate enhanced content optimized for resale platforms.
        
        Args:
            product_data: Original product data
            target_platform: Target platform (ebay, amazon, mercari, general)
            
        Returns:
            Dictionary with enhanced content for resale
        """
        try:
            prompt = self._build_resale_prompt(product_data, target_platform)
            
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                temperature=0.5,
                max_tokens=2000
            )
        except Exception as e:
            raise_ai_error(e)

        enhanced_data = self._parse_json_response(response.choices[0].message.content)
        if enhanced_data:
            logger.info(f"Successfully enhanced product data for {target_platform}")
            return enhanced_data
        logger.warning("Groq response was not valid JSON for resale enhancement")
        return {}
    
    def _build_resale_prompt(self, product_data: ProductData, target_platform: str) -> str:
        """Build prompt for resale content enhancement."""
        platform_specific = {
            "leboncoin": "Leboncoin listing: concise French copy, clear condition, pickup/shipping notes, price fairness cues, seller location.",
            "vinted": "Vinted listing: casual tone, detailed condition/flaws, size/fit advice, brand/style tags #hashtags, shipping presets.",
            "vestiaire": "Vestiaire Collective: premium tone, authenticity focus, detailed condition grading, precise measurements, material composition.",
            "ebay": "eBay listing: professional, comprehensive specs, item specifics, shipping policies, returns, checking for 'Item Specifics' fields.",
            "poshmark": "Poshmark listing: enthusiastic tone ('Posh Love'), style keywords, brand tagging, bundle discounts.",
            "mercari": "Mercari listing: friendly but concise, clear condition description, 'free shipping' checks if applicable, keyword stuffing at bottom.",
            "depop": "Depop listing: trendy/streetwear vibe, Gen-Z slang if appropriate, exact measurements, #aesthetic #hashtags (max 5), style eras (Y2K, 90s).",
            "etsy": "Etsy listing: focus on 'vintage' or 'handmade' story, craftsmanship, era/date code, emotional connection, gift potential.",
            "facebook": "Facebook Marketplace: local focus, 'pickup in [City]', cash/venmo friendly, concise, firm/OBO pricing indicators.",
            "grailed": "Grailed listing: streetwear/luxury focus, hype keywords, fit pics description, condition rating (1-10), grail status.",
            "shopify": "Shopify product page: professional e-commerce brand tone, SEO meta title/desc, benefit-focused bullets, clean formatting.",
            "general": "general marketplace listing suitable for multiple platforms"
        }
        
        normalized = target_platform.lower().strip()
        # Aliases
        if normalized in ["vestiaire collective", "vestiaire-collective"]: normalized = "vestiaire"
        if normalized in ["facebook marketplace", "fb marketplace"]: normalized = "facebook"
        
        platform_desc = platform_specific.get(normalized, platform_specific["general"])
        
        return f"""
You are an expert product listing optimizer. Create enhanced content for resale based on the original product data.

ORIGINAL PRODUCT DATA:
{json.dumps(asdict(product_data), ensure_ascii=False, indent=2)}

TARGET PLATFORM: {normalized.upper()}
STRATEGY: {platform_desc}

TASK:
Create optimized content for this platform.

GUIDELINES:
1. **optimized_title**: SEO-friendly title, maximize character usage for the platform.
2. **key_features**: 5-8 bullet points highlighting main selling points.
3. **enhanced_description**: 
   - Write in the specific TONE of the platform (e.g., Poshmark = emojis, Depop = trendy).
   - Be honest about condition.
   - Include measurements if available.
4. **suggested_keywords/hashtags**: Relevant terms (use #hashtags for Poshmark/Depop/Vinted).
5. **condition_notes**: Detailed assessment.
6. **shipping_notes**: Platform-specific advice.

OUTPUT FORMAT (JSON ONLY):
{{
  "optimized_title": "...",
  "key_features": ["...", "..."],
  "enhanced_description": "...",
  "suggested_keywords": ["...", "..."],
  "condition_notes": "...",
  "shipping_notes": "..."
}}
"""


    def generate_listing_markdown(self, raw_text: str, sections: List[str], tone: str = "Professional", platform: str = "general") -> str:
        """Generate a well-structured product listing description in Markdown from raw text."""
        try:
            sections_list = "\n".join([f"- {s}" for s in sections])
            prompt = (
                "You are a meticulous product copy editor for e-commerce listings. "
                "You will receive raw text scraped from a product page. The text may include unwanted fragments such as "
                "seller boilerplate, shipping banners, similar/related items, ads, HTML remnants, or duplicated lines. "
                "Your task is to extract only the true product information and produce a clean, accurate, well-structured "
                "Markdown description suitable for publishing directly on a product page.\n\n"
                "Rules:\n"
                "- Remove any unrelated or promotional content (similar items, ads, recommended, social links, tracking lines, warranty boilerplate, return policy banners). Keep only verifiable product details.\n"
                "- Do not hallucinate or invent facts. If a detail is not clearly present, omit it.\n"
                f"- Preserve units and measurements exactly if present. Do not convert currencies or sizes.\n"
                f"- No emojis, no ALL CAPS, no marketing fluff. Keep tone: {tone}.\n"
                "- Language: keep the same language as the source text.\n"
                "- Output must be valid Markdown, readable, and ready to paste into a product listing.\n\n"
                f"Target platform context (optional): {platform}\n\n"
                "Requested sections (include only if information exists, in this order):\n"
                f"{sections_list}\n\n"
                "Formatting requirements:\n"
                "- Use clear headings (##) and unordered lists (-) where appropriate.\n"
                "- Keep paragraphs short. Group measurements under a single subsection.\n"
                "- If condition notes exist, write them factually and briefly.\n"
                "- If nothing is available for a requested section, omit the section.\n\n"
                "SOURCE TEXT (raw):\n"
                f"{raw_text}\n\n"
                "Return ONLY the final Markdown. No explanations."
            )
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                temperature=0.5,
                max_tokens=2000
            )
        except Exception as e:
            raise_ai_error(e)
        return (response.choices[0].message.content or '').strip()

    def generate_listing_text(self, raw_text: str, tone: str = "Professional", platform: str = "general", product_data: Optional[ProductData] = None) -> str:
        """
        Generate a well-structured plain text listing from raw text using platform agent.
        
        Args:
            raw_text: Raw scraped text
            tone: Desired tone
            platform: Target platform
            product_data: Optional structured product data
            
        Returns:
            Clean, platform-optimized description
        """
        try:
            # Use platform agent for better results
            return self.platform_agent.generate_platform_description(
                raw_text, product_data, platform, ""
            )
        except Exception as e:
            logger.error(f"Error generating listing text: {e}")
            return ""


# Kept so existing code and any saved snippets that construct GroqProcessor
# with a bare key keep working; the class is provider-agnostic now.
GroqProcessor = AIProcessor


# =============================================================================
# FILE MANAGEMENT
# =============================================================================

class FileManager:
    """
    Manages file operations for scraped data and AI processing.
    
    Handles:
    - Product folder creation and organization
    - Text file saving and loading
    - Image downloads and organization
    - AI-processed content management
    """
    
    def __init__(self, base_dir: str = BASE_SAVE_DIR):
        """Initialize file manager with base directory."""
        self.base_dir = Path(base_dir)
        self.base_dir.mkdir(exist_ok=True)

    def enhance_image(self, image_path: Path, brightness: float = 1.0, contrast: float = 1.0,
                      sharpness: float = 1.0, saturation: float = 1.0) -> Image.Image:
        """Apply simple enhancements to an image and return the enhanced PIL Image."""
        img = Image.open(image_path).convert("RGB")
        if brightness != 1.0:
            img = ImageEnhance.Brightness(img).enhance(brightness)
        if contrast != 1.0:
            img = ImageEnhance.Contrast(img).enhance(contrast)
        if sharpness != 1.0:
            img = ImageEnhance.Sharpness(img).enhance(sharpness)
        if saturation != 1.0:
            img = ImageEnhance.Color(img).enhance(saturation)
        return img

    def overlay_logo(self, base_image: Image.Image, logo_path: Path, size_ratio: float = 0.15,
                     margin: int = 10, position: str = "bottom-right", opacity: float = 1.0) -> Image.Image:
        """
        Overlay a transparent logo on the base image with customizable position and opacity.
        
        Args:
            base_image: Base image to overlay logo on
            logo_path: Path to logo file
            size_ratio: Logo size as ratio of image width (0.0-1.0)
            margin: Margin from edges in pixels
            position: Logo position - "bottom-right", "bottom-left", "top-right", "top-left", "center"
            opacity: Logo opacity (0.0-1.0, where 1.0 is fully opaque)
            
        Returns:
            Image with logo overlaid
        """
        if not logo_path.exists():
            logger.warning(f"Logo file not found: {logo_path}")
            return base_image
            
        try:
            logo = Image.open(logo_path).convert("RGBA")
            
            # Calculate logo dimensions
            logo_width = int(base_image.width * size_ratio)
            logo_height = int(logo.height * (logo_width / max(1, logo.width)))
            logo = logo.resize((logo_width, logo_height), Image.Resampling.LANCZOS)
            
            # Apply opacity if needed
            if opacity < 1.0:
                alpha = logo.split()[3]
                alpha = ImageEnhance.Brightness(alpha).enhance(opacity)
                logo.putalpha(alpha)
            
            # Calculate position
            base_rgba = base_image.convert("RGBA")
            
            if position == "bottom-right":
                pos = (base_rgba.width - logo_width - margin, base_rgba.height - logo_height - margin)
            elif position == "bottom-left":
                pos = (margin, base_rgba.height - logo_height - margin)
            elif position == "top-right":
                pos = (base_rgba.width - logo_width - margin, margin)
            elif position == "top-left":
                pos = (margin, margin)
            elif position == "center":
                pos = ((base_rgba.width - logo_width) // 2, (base_rgba.height - logo_height) // 2)
            else:
                pos = (base_rgba.width - logo_width - margin, base_rgba.height - logo_height - margin)
            
            # Paste logo
            base_rgba.paste(logo, pos, logo)
            return base_rgba.convert("RGB")
            
        except Exception as e:
            logger.error(f"Error overlaying logo: {e}")
            return base_image
    
    def overlay_logo_pil(self, base_image: Image.Image, logo: Image.Image, size_ratio: float = 0.15,
                         margin: int = 10, position: str = "bottom-right", opacity: float = 1.0) -> Image.Image:
        """Overlay a PIL Image logo on the base image."""
        try:
            logo = logo.convert("RGBA")
            logo_width = int(base_image.width * size_ratio)
            logo_height = int(logo.height * (logo_width / max(1, logo.width)))
            logo = logo.resize((logo_width, logo_height), Image.Resampling.LANCZOS)
            
            if opacity < 1.0:
                alpha = logo.split()[3]
                alpha = ImageEnhance.Brightness(alpha).enhance(opacity)
                logo.putalpha(alpha)
            
            base_rgba = base_image.convert("RGBA")
            
            if position == "bottom-right":
                pos = (base_rgba.width - logo_width - margin, base_rgba.height - logo_height - margin)
            elif position == "bottom-left":
                pos = (margin, base_rgba.height - logo_height - margin)
            elif position == "top-right":
                pos = (base_rgba.width - logo_width - margin, margin)
            elif position == "top-left":
                pos = (margin, margin)
            elif position == "center":
                pos = ((base_rgba.width - logo_width) // 2, (base_rgba.height - logo_height) // 2)
            else:
                pos = (base_rgba.width - logo_width - margin, base_rgba.height - logo_height - margin)
            
            base_rgba.paste(logo, pos, logo)
            return base_rgba.convert("RGB")
        except Exception as e:
            logger.error(f"Error overlaying logo: {e}")
            return base_image
    
    def batch_process_images(self, image_paths: List[Path], output_folder: Path,
                            logo_path: Optional[Path] = None,
                            logo_image: Optional[Image.Image] = None,
                            brightness: float = 1.0, contrast: float = 1.0,
                            sharpness: float = 1.0, saturation: float = 1.0,
                            logo_size_ratio: float = 0.15, logo_margin: int = 10,
                            logo_position: str = "bottom-right", logo_opacity: float = 1.0,
                            progress_callback=None) -> List[Path]:
        """
        Batch process multiple images with enhancements and logo watermarking.
        
        Args:
            image_paths: List of image paths to process
            output_folder: Output folder for processed images
            logo_path: Optional path to logo file (deprecated, use logo_image)
            logo_image: Optional PIL Image logo (preferred)
            brightness, contrast, sharpness, saturation: Enhancement parameters
            logo_size_ratio, logo_margin, logo_position, logo_opacity: Logo parameters
            progress_callback: Optional callback for progress updates
            
        Returns:
            List of processed image paths
        """
        processed_paths = []
        output_folder.mkdir(parents=True, exist_ok=True)
        
        try:
            for idx, img_path in enumerate(image_paths):
                try:
                    # Enhance image
                    img = self.enhance_image(img_path, brightness, contrast, sharpness, saturation)
                    
                    # Add logo if provided (prefer PIL Image over path)
                    if logo_image is not None:
                        img = self.overlay_logo_pil(img, logo_image, logo_size_ratio, 
                                                    logo_margin, logo_position, logo_opacity)
                    elif logo_path and logo_path.exists():
                        img = self.overlay_logo(img, logo_path, logo_size_ratio, 
                                              logo_margin, logo_position, logo_opacity)
                    
                    # Save processed image
                    out_ext = img_path.suffix.lower()
                    if out_ext not in {'.jpg', '.jpeg', '.png', '.webp'}:
                        out_ext = '.jpg'
                    out_name = img_path.stem + "_enhanced" + out_ext
                    out_path = output_folder / out_name
                    
                    self.save_image(img, out_path)
                    processed_paths.append(out_path)
                    
                    # Progress callback
                    if progress_callback:
                        progress_callback(idx + 1, len(image_paths))
                    
                    logger.debug(f"Processed image {idx + 1}/{len(image_paths)}: {out_name}")
                    
                except Exception as e:
                    logger.warning(f"Failed to process image {img_path.name}: {e}")
                    continue
            
            logger.info(f"Batch processed {len(processed_paths)}/{len(image_paths)} images")
            return processed_paths
            
        except Exception as e:
            logger.error(f"Error in batch processing: {e}")
            return processed_paths

    def save_image(self, image: Image.Image, output_path: Path, quality: int = 90) -> None:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        # Preserve original format and maximize quality
        suffix = output_path.suffix.lower()
        if suffix in {'.jpg', '.jpeg'}:
            image.save(output_path, format='JPEG', quality=100, subsampling=0, optimize=False)
        elif suffix == '.png':
            image.save(output_path, format='PNG')
        elif suffix == '.webp':
            try:
                image.save(output_path, format='WEBP', quality=100, method=6, lossless=True)
            except Exception:
                image.save(output_path, format='WEBP', quality=100)
        else:
            image.save(output_path)

    def list_image_folders(self) -> List[Path]:
        """Folders under base_dir that contain at least one image (cached)."""
        return [Path(p) for p in scan_image_folders(str(self.base_dir), data_version())]

    def list_images(self, folder_path: Path) -> List[Path]:
        try:
            return sorted((p for p in folder_path.iterdir()
                           if p.is_file() and p.suffix.lower() in IMAGE_SUFFIXES),
                          key=lambda p: p.name.lower())
        except OSError:
            return []
    
    def create_product_folder(self, brand: str, item_id: str = "", fallback_title: str = "") -> Path:
        """
        Create and return product-specific folder path named "<Brand> <ItemID>".

        Falls back to the first word of the title when brand is missing.
        """
        try:
            raw_brand = (brand or "").strip()
            if not raw_brand:
                first_word = (fallback_title or "").strip().split()[0:1]
                raw_brand = first_word[0] if first_word else "Unknown"

            brand_part = clean_filename(raw_brand, max_length=60) or "Unknown"
            raw_id = str(item_id or "").strip()
            id_part = clean_filename(raw_id, max_length=40) if raw_id else ""

            folder_name = f"{brand_part} {id_part}".strip() if id_part else brand_part

            product_folder = self.base_dir / folder_name
            product_folder.mkdir(exist_ok=True)
            logger.debug(f"Created product folder: {product_folder}")
            return product_folder

        except Exception as e:
            logger.error(f"Error creating product folder: {e}")
            raise

    def create_serial_folder(self, serial: str) -> Path:
        """
        Create and return a product folder named after a batch serial number
        (the S.NO column of an uploaded batch file).
        """
        name = clean_filename(str(serial or "").strip(), max_length=60) or "Unknown"
        folder = self.base_dir / name
        folder.mkdir(parents=True, exist_ok=True)
        logger.debug(f"Created serial folder: {folder}")
        return folder


    def save_product_text(self, product_data: ProductData, folder_path: Path) -> Path:
        """
        Save product data to text file.
        
        Args:
            product_data: ProductData object to save
            folder_path: Folder to save file in
            
        Returns:
            Path to saved text file
        """
        try:
            filename = f"{clean_filename(product_data.title)}.txt"
            file_path = folder_path / filename
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write((product_data.description or '').strip())
            logger.info(f"Saved product text to: {file_path}")
            return file_path
        except Exception as e:
            logger.error(f"Error saving product text: {e}")
            raise


    def save_product_description_markdown(self, product_data: ProductData, folder_path: Path) -> Path:
        """
        Save ONLY the original product description to a Markdown (.md) file.
        """
        try:
            desc = (product_data.description or '').strip()
            md_name = f"{clean_filename(product_data.title)}.md" if product_data.title else "description.md"
            md_path = folder_path / md_name
            with open(md_path, 'w', encoding='utf-8') as f:
                f.write(desc)
            logger.info(f"Saved product description markdown to: {md_path}")
            return md_path
        except Exception as e:
            logger.error(f"Error saving markdown description: {e}")
            raise

    def save_raw_scrape_text(self, product_data: ProductData, folder_path: Path) -> Path:
        """
        Save a raw, comprehensive scrape to plain text including title, price, condition,
        brand, seller, shipping, item specifics, and the original description.
        This is intended as AI input for further cleaning/structuring.
        """
        try:
            lines: List[str] = []
            if product_data.title:
                lines.append(f"TITLE: {product_data.title}")
            if product_data.price:
                lines.append(f"Price: {product_data.price}")
            if product_data.condition:
                lines.append(f"Condition: {product_data.condition}")
            if product_data.brand:
                lines.append(f"Brand: {product_data.brand}")
            if product_data.seller:
                lines.append(f"Seller: {product_data.seller}")
            if product_data.shipping:
                lines.append(f"Shipping: {product_data.shipping}")
            if product_data.item_specifics:
                lines.append("Item Specifics:")
                for k, v in product_data.item_specifics.items():
                    lines.append(f"- {k}: {v}")
            if product_data.description:
                lines.append("\nDESCRIPTION:")
                lines.append(product_data.description)
            if product_data.url:
                lines.append(f"\nSOURCE URL: {product_data.url}")
            if product_data.scraped_at:
                lines.append(f"SCRAPED AT: {product_data.scraped_at}")

            content = "\n".join(lines).strip()
            if not content:
                content = "(No data found)"

            raw_path = folder_path / "raw_scrape.txt"
            with open(raw_path, 'w', encoding='utf-8') as f:
                f.write(content)
            logger.info(f"Saved raw scrape text to: {raw_path}")
            return raw_path
        except Exception as e:
            logger.error(f"Error saving raw scrape text: {e}")
            raise
    
    def save_ai_processed_content(self, folder_path: Path, ai_content: Dict[str, Any], 
                                content_type: str = "cleaned") -> Path:
        """
        Save AI-processed content to separate file.
        
        Args:
            folder_path: Product folder path
            ai_content: AI-processed content dictionary
            content_type: Type of processing (cleaned, enhanced, etc.)
            
        Returns:
            Path to saved AI content file
        """
        try:
            filename = f"ai_{content_type}_content.txt"
            file_path = folder_path / filename
            
            content_parts = [f"=== AI {content_type.upper()} CONTENT ==="]
            
            # Add cleaned/enhanced fields
            for key, value in ai_content.items():
                if isinstance(value, list):
                    content_parts.append(f"{key.upper()}:")
                    for item in value:
                        content_parts.append(f"  • {item}")
                else:
                    content_parts.append(f"{key.upper()}: {value}")
            
            content_parts.append(f"PROCESSED AT: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
            
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write("\n\n".join(content_parts))
            
            logger.info(f"Saved AI {content_type} content to: {file_path}")
            return file_path
            
        except Exception as e:
            logger.error(f"Error saving AI processed content: {e}")
            raise
    
    def download_images(self, scraper: EbayScraper, image_urls: List[str], 
                       folder_path: Path, progress_callback=None) -> List[str]:
        """
        Download all images to product folder sequentially (more reliable).
        
        Args:
            scraper: EbayScraper instance for downloading
            image_urls: List of image URLs to download
            folder_path: Folder to save images in
            progress_callback: Optional callback for progress updates
            
        Returns:
            List of successfully downloaded image paths
        """
        downloaded_paths = []
        
        try:
            # Download sequentially to avoid session threading issues
            for i, img_url in enumerate(image_urls):
                try:
                    img_base = folder_path / f"image_{i+1:02d}"
                    saved_path = scraper.download_image(img_url, str(img_base))
                    
                    if saved_path:
                        downloaded_paths.append(saved_path)
                        logger.debug(f"Downloaded image {i+1}/{len(image_urls)}")
                        
                        if progress_callback:
                            progress_callback(i + 1, len(image_urls))
                    else:
                        logger.warning(f"Failed to download image {i+1}: No response")
                        
                except Exception as e:
                    logger.warning(f"Failed to download image {i+1}: {e}")
                    continue
            
            logger.info(f"Downloaded {len(downloaded_paths)}/{len(image_urls)} images")
            return downloaded_paths
            
        except Exception as e:
            logger.error(f"Error downloading images: {e}")
            return downloaded_paths
    
    def get_existing_product_folders(self) -> List[Dict[str, Any]]:
        """Product folders holding scraped text, with file lists and counts.

        Backed by a cached directory scan, so calling this several times in
        one render (the AI tab does) costs nothing after the first call.
        """
        return scan_product_folders(str(self.base_dir), data_version())
    
    def load_product_text(self, folder_path: str, filename: str) -> str:
        """
        Load product text content from file.
        
        Args:
            folder_path: Path to product folder
            filename: Text filename to load
            
        Returns:
            Content of text file
        """
        try:
            file_path = Path(folder_path) / filename
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            logger.debug(f"Loaded text content from: {file_path}")
            return content
            
        except Exception as e:
            logger.error(f"Error loading product text: {e}")
            return ""

# =============================================================================
# STREAMLIT APPLICATION
# =============================================================================

# =============================================================================
# AI PROVIDERS
# =============================================================================
#
# Every provider below exposes an OpenAI-compatible /chat/completions endpoint,
# so one client shape covers all of them: only the base URL, the key and the
# model change. Adding a sixth provider is a single entry in AI_PROVIDERS —
# no branching anywhere else.
#
# Groq deliberately keeps its own SDK. The existing integration is known to
# work and there is no reason to put it through a new code path; the two
# clients expose the same `.chat.completions.create` surface, so everything
# downstream is identical either way.

try:
    from openai import OpenAI
    OPENAI_SDK_AVAILABLE = True
except Exception:  # pragma: no cover - depends on the install
    OpenAI = None
    OPENAI_SDK_AVAILABLE = False


@dataclass(frozen=True)
class AIProviderSpec:
    """Everything that differs between one AI provider and the next."""
    key: str                       # stable id used in config files
    label: str                     # shown in the sidebar
    base_url: str                  # OpenAI-compatible root
    default_model: str
    console_url: str               # where the user gets a key
    key_prefix: str = ''           # typical prefix, used for a soft warning only
    key_label: str = 'API key'
    model_hint: str = ''
    extra_headers: Dict[str, str] = field(default_factory=dict)
    native_sdk: str = ''           # '' = use the OpenAI-compatible client
    env_vars: Tuple[str, ...] = ()


AI_PROVIDERS: Dict[str, AIProviderSpec] = {
    'groq': AIProviderSpec(
        key='groq',
        label='Groq',
        base_url='https://api.groq.com/openai/v1',
        default_model='openai/gpt-oss-20b',
        console_url='https://console.groq.com/keys',
        key_prefix='gsk_',
        key_label='Groq API key',
        model_hint='Open models on Groq hardware. Very fast, generous free tier.',
        native_sdk='groq',
        env_vars=('GROQ_API_KEY',),
    ),
    'openrouter': AIProviderSpec(
        key='openrouter',
        label='OpenRouter',
        base_url='https://openrouter.ai/api/v1',
        default_model='openai/gpt-oss-20b',
        console_url='https://openrouter.ai/keys',
        key_prefix='sk-or-',
        key_label='OpenRouter API key',
        model_hint='One key for many providers. Model ids look like "vendor/model"; '
                   'ids ending in ":free" cost nothing.',
        # Optional attribution headers; OpenRouter uses them for its rankings.
        extra_headers={
            'HTTP-Referer': 'https://github.com/CallSohail/ebaystore-private',
            'X-Title': 'eBay Scraper Studio',
        },
        env_vars=('OPENROUTER_API_KEY',),
    ),
    'nvidia': AIProviderSpec(
        key='nvidia',
        label='NVIDIA NIM',
        base_url='https://integrate.api.nvidia.com/v1',
        default_model='meta/llama-3.3-70b-instruct',
        console_url='https://build.nvidia.com/',
        key_prefix='nvapi-',
        key_label='NVIDIA API key',
        model_hint='Open models hosted by NVIDIA. Ids are prefixed by their vendor, '
                   'e.g. "meta/..." or "nvidia/...".',
        env_vars=('NVIDIA_API_KEY', 'NVIDIA_NIM_API_KEY'),
    ),
    'gemini': AIProviderSpec(
        key='gemini',
        label='Google Gemini',
        base_url='https://generativelanguage.googleapis.com/v1beta/openai/',
        default_model='gemini-flash-latest',
        console_url='https://aistudio.google.com/apikey',
        key_prefix='AIza',
        key_label='Google AI Studio key',
        model_hint='Google\'s own models through their OpenAI-compatible endpoint. '
                   'Prefer a "-latest" alias: numbered versions get retired.',
        env_vars=('GEMINI_API_KEY', 'GOOGLE_API_KEY'),
    ),
    'huggingface': AIProviderSpec(
        key='huggingface',
        label='Hugging Face',
        base_url='https://router.huggingface.co/v1',
        default_model='openai/gpt-oss-20b',
        console_url='https://huggingface.co/settings/tokens',
        key_prefix='hf_',
        key_label='Hugging Face token',
        model_hint='Routes to many inference providers. Append ":provider" to pin one '
                   '(e.g. "openai/gpt-oss-20b:together"); without it HF picks for you. '
                   'The token needs the "Make calls to Inference Providers" permission.',
        env_vars=('HF_TOKEN', 'HUGGINGFACE_API_KEY'),
    ),
}

DEFAULT_PROVIDER = 'groq'
AI_CONFIG_PATH = Path.cwd() / '.ai_config.json'
LEGACY_GROQ_CONFIG = Path.cwd() / '.groq_config.json'


def get_provider(provider_key: str) -> AIProviderSpec:
    """Look up a provider, falling back to the default for unknown ids."""
    return AI_PROVIDERS.get(provider_key or '', AI_PROVIDERS[DEFAULT_PROVIDER])


@dataclass
class AISettings:
    """The provider, key and model a request should use."""
    provider: AIProviderSpec
    api_key: str = ''
    model: str = ''

    @property
    def ready(self) -> bool:
        return bool(self.api_key.strip())

    @property
    def model_name(self) -> str:
        return (self.model or '').strip() or self.provider.default_model


# -----------------------------------------------------------------------------
# Credential storage
# -----------------------------------------------------------------------------
#
# Precedence: Streamlit secrets, then environment, then a local file. Secrets
# and environment come first so a deployment can inject credentials without a
# key ever being written to disk. The local file exists because this app is
# normally run locally by one person, and re-pasting five keys on every start
# is not realistic — it is created 0600 and is gitignored.

def _read_local_config() -> Dict[str, Any]:
    for path in (AI_CONFIG_PATH, LEGACY_GROQ_CONFIG):
        try:
            if not path.exists():
                continue
            with open(path, 'r', encoding='utf-8') as f:
                data = json.load(f) or {}
            if path is LEGACY_GROQ_CONFIG:
                # Migrate the single-provider file written by earlier versions.
                legacy = str(data.get('groq_api_key', '')).strip()
                return {'keys': {'groq': legacy}} if legacy else {}
            return data if isinstance(data, dict) else {}
        except (OSError, json.JSONDecodeError) as e:
            logger.warning(f"Could not read {path.name}: {e}")
    return {}


def _write_local_config(data: Dict[str, Any]) -> bool:
    """Write the config with owner-only permissions."""
    try:
        payload = json.dumps(data, indent=2).encode('utf-8')
        # Create with 0600 before any secret reaches the file, so it is never
        # briefly world-readable.
        fd = os.open(AI_CONFIG_PATH, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        try:
            os.write(fd, payload)
        finally:
            os.close(fd)
        try:
            os.chmod(AI_CONFIG_PATH, 0o600)
        except OSError:
            # Windows ignores POSIX modes; the file still lands in a
            # user-profile directory and is gitignored.
            pass
        return True
    except OSError as e:
        logger.error(f"Could not save AI settings: {e}")
        return False


def _secret(name: str) -> str:
    try:
        if hasattr(st, 'secrets') and name in st.secrets:
            return str(st.secrets[name]).strip()
    except Exception:
        pass
    return ''


def load_api_key(provider: AIProviderSpec) -> str:
    """Resolve a provider's key: secrets, then environment, then local file.

    Never logged — only its presence is ever reported.
    """
    for name in (f"{provider.key}_api_key", provider.key):
        value = _secret(name)
        if value:
            return value
    for env_var in provider.env_vars:
        value = os.getenv(env_var, '').strip()
        if value:
            return value
    stored = _read_local_config().get('keys') or {}
    return str(stored.get(provider.key, '') or '').strip()


def save_api_key(provider: AIProviderSpec, api_key: str) -> bool:
    """Persist one provider's key, leaving the others untouched."""
    data = _read_local_config()
    keys = dict(data.get('keys') or {})
    if api_key.strip():
        keys[provider.key] = api_key.strip()
    else:
        keys.pop(provider.key, None)
    data['keys'] = keys
    return _write_local_config(data)


def forget_api_key(provider: AIProviderSpec) -> bool:
    return save_api_key(provider, '')


def load_ai_preferences() -> Tuple[str, Dict[str, str]]:
    """Return the last selected provider and any per-provider model overrides."""
    data = _read_local_config()
    provider = str(data.get('provider') or DEFAULT_PROVIDER)
    models = {str(k): str(v) for k, v in (data.get('models') or {}).items()}
    return (provider if provider in AI_PROVIDERS else DEFAULT_PROVIDER), models


def save_ai_preferences(provider_key: str, model: str) -> bool:
    """Remember the chosen provider and its model. No secrets involved."""
    data = _read_local_config()
    data['provider'] = provider_key
    models = dict(data.get('models') or {})
    if model.strip():
        models[provider_key] = model.strip()
    else:
        models.pop(provider_key, None)
    data['models'] = models
    return _write_local_config(data)


# -----------------------------------------------------------------------------
# Client construction
# -----------------------------------------------------------------------------

def build_ai_client(settings: AISettings):
    """Return a client exposing `.chat.completions.create` for this provider.

    Groq keeps its own SDK so the path that already works stays exactly as it
    was; everything else goes through the OpenAI-compatible client. Both
    expose the same call surface, so no caller needs to know the difference.
    """
    if not settings.ready:
        raise AIServiceError(
            f"No {settings.provider.key_label} set. Add one in the sidebar to use AI features.",
            'auth',
        )

    api_key = settings.api_key.strip()
    if settings.provider.native_sdk == 'groq':
        try:
            return Groq(api_key=api_key)
        except Exception as e:
            raise_ai_error(e)

    if not OPENAI_SDK_AVAILABLE:
        raise AIServiceError(
            f"{settings.provider.label} needs the `openai` package. "
            "Install it with `pip install openai` and restart the app.",
            'config',
        )
    try:
        return OpenAI(
            api_key=api_key,
            base_url=settings.provider.base_url,
            default_headers=dict(settings.provider.extra_headers) or None,
            timeout=120.0,
            max_retries=2,
        )
    except Exception as e:
        raise_ai_error(e)


def list_provider_models(settings: AISettings, limit: int = 300) -> List[str]:
    """Ask the provider which models it currently serves.

    Model ids churn constantly — Gemini retires numbered versions, OpenRouter
    adds models weekly — so a hardcoded dropdown goes stale. Every
    OpenAI-compatible provider exposes GET /models, so the list can just be
    asked for.
    """
    client = build_ai_client(settings)
    try:
        response = client.models.list()
    except Exception as e:
        raise_ai_error(e)
    names: List[str] = []
    for item in getattr(response, 'data', None) or []:
        model_id = getattr(item, 'id', None) or (item.get('id') if isinstance(item, dict) else None)
        if model_id:
            names.append(str(model_id))
    return sorted(set(names))[:limit]

# =============================================================================
# CACHING
# =============================================================================
#
# Streamlit re-runs the whole script on every widget interaction. Without
# caching, each click re-walked the downloads tree, re-read the history CSV
# and re-read the log file — which is what made the app feel like it hung
# once a few hundred images had been downloaded.
#
# Two invalidation strategies are used, both cheap and both correct:
#
#   * File-backed reads are keyed on (path, mtime, size). The moment the file
#     changes on disk the key changes, so there is no staleness window.
#   * Directory scans are keyed on a version counter that is bumped whenever
#     the app writes into the downloads tree, with a short TTL as a backstop
#     for changes made outside the app (e.g. the user deleting a folder).

DIR_CACHE_TTL = 30       # seconds; backstop for out-of-band filesystem changes
FILE_CACHE_TTL = 300     # file reads are keyed on mtime, so this is just a cap


def bump_data_version() -> None:
    """Invalidate cached directory scans after the app writes to disk."""
    try:
        st.session_state['_data_version'] = st.session_state.get('_data_version', 0) + 1
        # A prepared export no longer reflects what is on disk.
        st.session_state.pop('zip_payload', None)
    except Exception:
        # Called from a non-Streamlit context (tests); nothing to invalidate.
        pass


def data_version() -> int:
    try:
        return st.session_state.get('_data_version', 0)
    except Exception:
        return 0


def _stat_key(path: Path) -> Tuple[str, float, int]:
    """(path, mtime, size) cache key. Missing files get a stable zero key."""
    try:
        stat = path.stat()
        return (str(path), stat.st_mtime, stat.st_size)
    except OSError:
        return (str(path), 0.0, 0)


IMAGE_SUFFIXES = {'.jpg', '.jpeg', '.png', '.webp'}


@st.cache_data(ttl=DIR_CACHE_TTL, show_spinner=False)
def scan_product_folders(base_dir: str, version: int) -> List[Dict[str, Any]]:
    """Folders under base_dir holding scraped text, with their files and counts."""
    base = Path(base_dir)
    folders: List[Dict[str, Any]] = []
    try:
        entries = sorted(base.iterdir(), key=lambda p: p.name.lower())
    except OSError:
        return folders

    for folder in entries:
        if not folder.is_dir():
            continue
        try:
            children = list(folder.iterdir())
        except OSError:
            continue
        listings = [f.name for f in children if f.name.endswith('_listing.txt')]
        # Generated output is never a source: feeding a listing back into the
        # generator would rewrite the model's own text instead of the scrape.
        text_files = [f.name for f in children
                      if f.suffix.lower() in ('.txt', '.md')
                      and not f.name.startswith('ai_')
                      and f.name not in listings]
        if not text_files:
            continue
        images = [f.name for f in children if f.suffix.lower() in IMAGE_SUFFIXES]
        folders.append({
            'folder_name': folder.name,
            'folder_path': str(folder),
            'text_files': sorted(text_files),
            'main_file': sorted(text_files)[0],
            'image_count': len(images),
            'listing_files': sorted(listings),
        })
    return folders


@st.cache_data(ttl=DIR_CACHE_TTL, show_spinner=False)
def scan_image_folders(base_dir: str, version: int) -> List[str]:
    """Folders (including base_dir itself) that contain at least one image."""
    base = Path(base_dir)
    found: List[str] = []
    try:
        if any(p.suffix.lower() in IMAGE_SUFFIXES for p in base.iterdir() if p.is_file()):
            found.append(str(base))
        for folder in sorted(base.iterdir(), key=lambda p: p.name.lower()):
            if not folder.is_dir():
                continue
            try:
                if any(p.suffix.lower() in IMAGE_SUFFIXES for p in folder.iterdir() if p.is_file()):
                    found.append(str(folder))
            except OSError:
                continue
    except OSError:
        pass
    return found


@st.cache_data(ttl=DIR_CACHE_TTL, show_spinner=False)
def scan_webp_folders(base_dir: str, version: int) -> List[Tuple[str, int]]:
    """(folder, webp_count) for every folder in the tree holding .webp files.

    One recursive walk produces both the folder list and the counts; the
    previous version walked the tree once and then re-listed every folder
    again just to label the dropdown.
    """
    base = Path(base_dir)
    results: List[Tuple[str, int]] = []
    if not base.exists():
        return results

    def webp_count(folder: Path) -> int:
        try:
            return sum(1 for c in folder.iterdir()
                       if c.is_file() and c.suffix.lower() == '.webp')
        except OSError:
            return 0

    count = webp_count(base)
    if count:
        results.append((str(base), count))
    try:
        for path in base.rglob('*'):
            if path.is_dir():
                count = webp_count(path)
                if count:
                    results.append((str(path), count))
    except OSError:
        pass
    return sorted(results, key=lambda item: item[0].lower())


@st.cache_data(ttl=FILE_CACHE_TTL, show_spinner=False)
def _read_status_log(key: Tuple[str, float, int]) -> pd.DataFrame:
    """Parse batch_status_log.csv. Keyed on the file's stat, never on content."""
    path = Path(key[0])
    empty = pd.DataFrame(columns=BATCH_LOG_COLUMNS)
    if key[2] == 0:
        return empty
    try:
        df = pd.read_csv(path, dtype=str, keep_default_na=False, encoding='utf-8-sig')
    except Exception as e:
        logger.warning(f"Could not read {path.name}: {e}")
        return empty
    # Tolerate a log written by an older version with fewer columns
    for column in BATCH_LOG_COLUMNS:
        if column not in df.columns:
            df[column] = ''
    return df[BATCH_LOG_COLUMNS]


@st.cache_data(ttl=5, show_spinner=False)
def read_log_tail(key: Tuple[str, float, int], tail: int) -> str:
    """Last `tail` lines of the application log."""
    path = Path(key[0])
    if key[2] == 0:
        return ''
    try:
        with open(path, 'r', encoding='utf-8', errors='replace') as f:
            return "".join(f.readlines()[-tail:])
    except OSError as e:
        logger.warning(f"Could not read {path.name}: {e}")
        return ''


# =============================================================================
# BATCH PROCESSING (CSV/Excel driven)
# =============================================================================
#
# The batch workflow is driven entirely by an uploaded CSV/Excel file whose
# first four columns are: Brand | S.NO | Link | Status. Only those four
# columns are read; every other column is carried through untouched so the
# downloadable result matches the uploaded file plus updated statuses.
#
# Three files live next to the app:
#   .batch_state.csv / .batch_state_meta.json  resumable state for the run in
#                                              progress (hidden, disposable)
#   batch_status_log.csv                       permanent per-link history. Every
#                                              link that is processed, skipped
#                                              or rejected is appended here with
#                                              its status and details, and this
#                                              same file is what makes duplicate
#                                              detection work across uploads.

BATCH_STATE_CSV = Path.cwd() / '.batch_state.csv'
BATCH_STATE_META = Path.cwd() / '.batch_state_meta.json'
BATCH_STATUS_LOG = Path.cwd() / 'batch_status_log.csv'
_BATCH_STATE_LOCK = threading.Lock()
_STATUS_LOG_LOCK = threading.Lock()

STATUS_PENDING = 'pending'
STATUS_DONE = 'done'
STATUS_ERROR = 'error'
STATUS_DUPLICATE = 'duplicate'
VALID_STATUSES = {STATUS_PENDING, STATUS_DONE, STATUS_ERROR, STATUS_DUPLICATE}

# Positional indices of the four batch columns (the spec is positional, so
# header names don't matter).
BRAND_COL, SERIAL_COL, LINK_COL, STATUS_COL = 0, 1, 2, 3

# Columns of batch_status_log.csv, in order.
BATCH_LOG_COLUMNS = [
    'Logged At', 'Source', 'Source File', 'S.NO', 'Brand', 'Link', 'Item ID',
    'Status', 'Details', 'Folder', 'Title', 'Price', 'Condition', 'Images',
]


def normalize_serial(value: Any) -> str:
    """Normalize an S.NO cell into a clean, folder-safe string."""
    s = str(value if value is not None else '').strip()
    if not s or s.lower() in ('nan', 'none'):
        return ''
    # Excel reads integer serials back as floats ("1" -> "1.0")
    if re.fullmatch(r'\d+\.0+', s):
        s = s.split('.')[0]
    return clean_filename(s, max_length=60)


def normalize_status(value: Any) -> str:
    """Map any status cell (any case, blank, NaN) onto a known status."""
    s = str(value if value is not None else '').strip().lower()
    return s if s in VALID_STATUSES else STATUS_PENDING


def batch_link_key(link: str, scraper: Optional["EbayScraper"] = None) -> str:
    """Canonical identity of a listing, used for duplicate detection.

    The eBay item id is preferred because the same listing is reachable
    through many URL forms (mobile, regional domain, tracking parameters,
    short links). When no id can be extracted the normalized URL is used, and
    the two kinds are prefixed so an item id can never collide with a URL.
    """
    raw = str(link or '').strip()
    if not raw or raw.lower() in ('nan', 'none'):
        return ''
    if scraper is not None:
        try:
            item_id = scraper.extract_id_from_url(raw)
            if item_id:
                return f"item:{item_id}"
        except Exception:
            pass
    return f"url:{raw.lower().rstrip('/')}"


def _log_key(item_id: str, link: str) -> str:
    """Rebuild a link key from a logged row without needing the scraper."""
    item_id = str(item_id or '').strip()
    if item_id:
        return f"item:{item_id}"
    link = str(link or '').strip()
    return f"url:{link.lower().rstrip('/')}" if link else ''


# -----------------------------------------------------------------------------
# batch_status_log.csv - permanent per-link history
# -----------------------------------------------------------------------------

def append_batch_status(record: Dict[str, Any]) -> bool:
    """Append one row to batch_status_log.csv.

    Every link the app touches ends up here: processed, skipped as a
    duplicate, or rejected during validation. Missing fields are written as
    empty strings so the column layout is always stable. Returns False when
    the file is locked by another program (typically open in Excel) — the
    batch keeps running in that case, only the history row is lost.
    """
    row = {col: str(record.get(col, '') or '') for col in BATCH_LOG_COLUMNS}
    if not row['Logged At']:
        row['Logged At'] = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    if not row['Source']:
        row['Source'] = 'batch'
    # Keep single cells readable in Excel
    row['Details'] = row['Details'].replace('\n', ' ').strip()[:500]
    row['Title'] = row['Title'].replace('\n', ' ').strip()[:300]

    last_err: Optional[BaseException] = None
    with _STATUS_LOG_LOCK:
        for attempt in range(4):
            try:
                needs_header = (not BATCH_STATUS_LOG.exists()) or BATCH_STATUS_LOG.stat().st_size == 0
                with open(BATCH_STATUS_LOG, 'a', newline='', encoding='utf-8') as f:
                    if needs_header:
                        # BOM written once, at creation, so Excel opens the
                        # file as UTF-8. Appends must not repeat it.
                        f.write('\ufeff')
                    writer = csv.DictWriter(f, fieldnames=BATCH_LOG_COLUMNS)
                    if needs_header:
                        writer.writeheader()
                    writer.writerow(row)
                return True
            except OSError as e:
                last_err = e
                time.sleep(0.3 * (attempt + 1))
    logger.error(
        f"Could not append to {BATCH_STATUS_LOG.name}: {last_err}. "
        "If the file is open in Excel, close it there."
    )
    return False


def load_batch_status_log() -> pd.DataFrame:
    """Read batch_status_log.csv. Returns an empty frame when absent/unreadable.

    Parsing is cached against the file's mtime and size, so repeated reruns
    cost a stat() rather than a full CSV parse.
    """
    return _read_status_log(_stat_key(BATCH_STATUS_LOG))


def clear_batch_status_log() -> bool:
    """Delete the history file. Returns False when it is locked."""
    with _STATUS_LOG_LOCK:
        for attempt in range(3):
            try:
                if BATCH_STATUS_LOG.exists():
                    BATCH_STATUS_LOG.unlink()
                return True
            except OSError as e:
                logger.warning(f"Could not remove {BATCH_STATUS_LOG.name} (attempt {attempt + 1}): {e}")
                time.sleep(0.3 * (attempt + 1))
    return False


# -----------------------------------------------------------------------------
# Duplicate ledger
# -----------------------------------------------------------------------------

def new_ledger() -> Dict[str, Dict[str, Dict[str, str]]]:
    """An empty duplicate index: exact pairs, serials and links."""
    return {'pairs': {}, 'serials': {}, 'links': {}}


def ledger_register(ledger: Dict[str, Dict[str, Dict[str, str]]], serial: str,
                    link_key: str, record: Dict[str, str]) -> None:
    """Record a successfully processed entry so later rows can be compared to it.

    First writer wins: the record kept is the one that originally claimed the
    serial or the listing, which is what the duplicate message should point at.
    """
    if serial and serial not in ledger['serials']:
        ledger['serials'][serial] = record
    if link_key and link_key not in ledger['links']:
        ledger['links'][link_key] = record
    if serial and link_key:
        ledger['pairs'].setdefault(f"{serial}||{link_key}", record)


def build_history_ledger() -> Dict[str, Dict[str, Dict[str, str]]]:
    """Build the duplicate index from batch_status_log.csv.

    Only rows that actually completed (`done`) count as history. Failed rows
    stay eligible so a re-upload retries them, and rows already skipped as
    duplicates never chain into new duplicates of their own.
    """
    ledger = new_ledger()
    df = load_batch_status_log()
    if df.empty:
        return ledger
    for _, row in df.iterrows():
        if str(row.get('Status', '')).strip().lower() != STATUS_DONE:
            continue
        if str(row.get('Source', 'batch')).strip().lower() != 'batch':
            continue
        serial = normalize_serial(row.get('S.NO'))
        link = str(row.get('Link', '')).strip()
        key = _log_key(row.get('Item ID'), link)
        record = {
            'serial': serial,
            'link': link,
            'when': str(row.get('Logged At', '')).strip(),
            'file': str(row.get('Source File', '')).strip(),
            'folder': str(row.get('Folder', '')).strip(),
        }
        ledger_register(ledger, serial, key, record)
    return ledger


def _origin(record: Dict[str, str]) -> str:
    """Human-readable 'where it came from' fragment for duplicate messages."""
    bits = []
    if record.get('when'):
        bits.append(f"on {record['when']}")
    if record.get('file'):
        bits.append(f"from {record['file']}")
    return " ".join(bits)


def duplicate_reason(ledger: Dict[str, Dict[str, Dict[str, str]]], serial: str,
                     link_key: str, scope: str) -> str:
    """Return a duplicate explanation, or '' when the entry is new.

    Three distinct collisions are reported, because each one means something
    different to the user:

    1. Same S.NO *and* same link  -> the exact entry was handled before.
    2. Same link, different S.NO  -> the listing would be downloaded twice
       into two folders.
    3. Same S.NO, different link  -> the folder named after that S.NO already
       holds another listing, and processing would mix two products into it.

    `scope` is 'this file' or 'earlier' and only shapes the wording.
    """
    if serial and link_key:
        record = ledger['pairs'].get(f"{serial}||{link_key}")
        if record is not None:
            where = _origin(record) if scope == 'earlier' else 'in this file'
            return f"Duplicate — S.NO {serial} with this link was already processed {where}.".replace('  ', ' ')
    if link_key:
        record = ledger['links'].get(link_key)
        if record is not None:
            other = record.get('serial') or '?'
            where = _origin(record) if scope == 'earlier' else 'in this file'
            return f"Duplicate link — this listing was already processed under S.NO {other} {where}.".replace('  ', ' ')
    if serial:
        record = ledger['serials'].get(serial)
        if record is not None:
            where = _origin(record) if scope == 'earlier' else 'in this file'
            return (f"Duplicate S.NO — folder '{serial}' already holds a different listing processed "
                    f"{where}. Give this row a new S.NO.").replace('  ', ' ')
    return ''


_EXPECTED_FORMAT_HINT = (
    "Expected columns (in order): Brand | S.NO | Link | Status. "
    "The 3rd column must contain the eBay listing links; Status is optional."
)


def _sheet_has_links(raw: pd.DataFrame) -> bool:
    """True when a raw (headerless) frame plausibly matches the batch format."""
    if raw is None or raw.empty or raw.shape[1] <= LINK_COL:
        return False
    col = raw.iloc[:, LINK_COL].astype(str).str.lower()
    return bool(col.str.contains('http', na=False).any() or col.str.contains('ebay\\.', na=False, regex=True).any())


def _apply_header(raw: pd.DataFrame) -> pd.DataFrame:
    """Turn a raw (headerless) frame into one with usable column names.

    If the first row's 3rd cell already looks like a link, the sheet has no
    header row and a synthetic one is added; otherwise the first row becomes
    the header. Blank or duplicate header cells get unique fallback names.
    """
    first_link = str(raw.iloc[0, LINK_COL]).lower() if len(raw) else ''
    if 'http' in first_link or 'ebay.' in first_link:
        df = raw.copy()
        names = ['Brand', 'S.NO', 'Link', 'Status'] + [f'Column {i + 1}' for i in range(4, df.shape[1])]
        df.columns = names[:df.shape[1]]
    else:
        df = raw.iloc[1:].reset_index(drop=True).copy()
        df.columns = [str(c).strip() for c in raw.iloc[0].tolist()]

    # Make column names non-empty and unique so pandas operations stay sane
    seen: Dict[str, int] = {}
    cols: List[str] = []
    for i, c in enumerate(df.columns):
        name = str(c).strip() or f'Column {i + 1}'
        if name in seen:
            seen[name] += 1
            name = f"{name}.{seen[name]}"
        else:
            seen[name] = 0
        cols.append(name)
    df.columns = cols
    return df


def read_batch_upload(uploaded_file) -> pd.DataFrame:
    """Read an uploaded CSV/Excel batch file with every cell kept as a string.

    Reading as strings (with NaN suppressed) is what guarantees the extra
    columns round-trip unmodified. For Excel workbooks every sheet is
    scanned and the first one whose 3rd column contains links is used, so
    uploading a workbook with the data on a later sheet still works. A clear
    error is raised when no sheet matches the expected format.
    """
    name = uploaded_file.name.lower()
    if name.endswith('.csv'):
        uploaded_file.seek(0)
        try:
            raw = pd.read_csv(uploaded_file, dtype=str, keep_default_na=False, header=None)
        except UnicodeDecodeError:
            # Files exported from Excel on Windows are often cp1252, not UTF-8
            uploaded_file.seek(0)
            raw = pd.read_csv(uploaded_file, dtype=str, keep_default_na=False,
                              header=None, encoding='latin-1')
        except pd.errors.EmptyDataError:
            raise ValueError("The CSV file is empty.")
        if not _sheet_has_links(raw):
            raise ValueError(f"No eBay links found in the 3rd column of the file. {_EXPECTED_FORMAT_HINT}")
        return _apply_header(raw)

    uploaded_file.seek(0)
    sheets = pd.read_excel(uploaded_file, sheet_name=None, dtype=str, keep_default_na=False, header=None)
    if not sheets:
        raise ValueError("The workbook contains no sheets.")
    for sheet_name, raw in sheets.items():
        if _sheet_has_links(raw):
            if len(sheets) > 1:
                logger.info(f"Batch upload: using sheet '{sheet_name}' (first sheet with links in column 3)")
            return _apply_header(raw)
    sheet_list = ", ".join(str(s) for s in sheets.keys())
    raise ValueError(
        f"None of the sheets ({sheet_list}) has eBay links in the 3rd column. {_EXPECTED_FORMAT_HINT}"
    )


def prepare_batch_dataframe(df: pd.DataFrame, scraper: "EbayScraper",
                            history: Optional[Dict[str, Dict[str, Dict[str, str]]]] = None,
                            source_name: str = '') -> Tuple[pd.DataFrame, Dict[str, str], Dict[str, int]]:
    """Validate and normalize an uploaded batch table.

    Every row is classified up front so the user sees the outcome the moment
    the file is uploaded rather than after a long run:

    * `error`     — the row cannot be processed (missing S.NO, missing or
                    invalid link).
    * `duplicate` — the entry repeats one earlier in the same file, or one
                    already completed in an earlier upload (`history`).
    * `pending`   — ready to process.
    * `done`      — left untouched when the uploaded file already says so.

    Returns the prepared DataFrame, a {row_index: reason} map, and a count of
    each outcome. Raises ValueError when the file itself is unusable.
    """
    if df is None or df.shape[1] < 3:
        raise ValueError("The file must have at least 3 columns: Brand, S.NO and Link (Status is optional and defaults to pending).")

    df = df.copy()
    history = history if history is not None else new_ledger()

    def _cell(row, idx) -> str:
        return str(row.iloc[idx]).strip() if idx < len(row) else ''

    # Drop rows where Brand, S.NO and Link are all empty (blank padding rows)
    keep = df.apply(lambda r: any(_cell(r, i) for i in (BRAND_COL, SERIAL_COL, LINK_COL)), axis=1)
    df = df[keep].reset_index(drop=True)
    if df.empty:
        raise ValueError("The file has no data rows.")

    # Guarantee a Status column in position 4
    if df.shape[1] < 4:
        status_name = 'Status'
        while status_name in df.columns:
            status_name += '_'
        df.insert(3, status_name, STATUS_PENDING)

    notes: Dict[str, str] = {}
    counts = {STATUS_PENDING: 0, STATUS_DONE: 0, STATUS_ERROR: 0, STATUS_DUPLICATE: 0}
    in_file = new_ledger()

    for i in range(len(df)):
        status = normalize_status(df.iat[i, STATUS_COL])
        serial = normalize_serial(df.iat[i, SERIAL_COL])
        brand = str(df.iat[i, BRAND_COL]).strip() if df.shape[1] > BRAND_COL else ''
        link = str(df.iat[i, LINK_COL]).strip()
        link_key = batch_link_key(link, scraper)
        reason = ''

        if status == STATUS_DONE:
            # The uploaded file already marks this row complete. Trust it, and
            # register it so later rows repeating it are flagged.
            ledger_register(in_file, serial, link_key,
                            {'serial': serial, 'link': link, 'when': '', 'file': source_name})
            counts[STATUS_DONE] += 1
            df.iat[i, STATUS_COL] = STATUS_DONE
            continue

        if not serial:
            reason, status = 'Missing S.NO — every row needs a serial number.', STATUS_ERROR
        elif not link or link.lower() in ('nan', 'none'):
            reason, status = 'Missing link.', STATUS_ERROR
        else:
            try:
                valid = scraper.validate_ebay_url(link)
            except Exception:
                valid = False
            if not valid:
                reason, status = 'Not a recognised eBay URL.', STATUS_ERROR
            else:
                dup = duplicate_reason(in_file, serial, link_key, scope='file')
                if not dup:
                    dup = duplicate_reason(history, serial, link_key, scope='earlier')
                if dup:
                    reason, status = dup, STATUS_DUPLICATE
                else:
                    status = STATUS_PENDING
                    ledger_register(in_file, serial, link_key,
                                    {'serial': serial, 'link': link, 'when': '', 'file': source_name})

        df.iat[i, STATUS_COL] = status
        counts[status] = counts.get(status, 0) + 1
        if reason:
            notes[str(i)] = reason
        # Rows that will never run are recorded in the history file now, so
        # batch_status_log.csv holds an entry for every link of every upload.
        if status in (STATUS_ERROR, STATUS_DUPLICATE):
            append_batch_status({
                'Source': 'batch', 'Source File': source_name, 'S.NO': serial,
                'Brand': brand, 'Link': link,
                'Item ID': link_key[5:] if link_key.startswith('item:') else '',
                'Status': status, 'Details': reason,
            })

    # If not a single row survived validation, the file is almost certainly in
    # the wrong format — fail loudly with guidance instead of showing a table
    # where everything is silently marked as error.
    if counts[STATUS_ERROR] == len(df):
        sample = "; ".join(list(dict.fromkeys(notes.values()))[:3])
        raise ValueError(f"No usable rows found ({sample}). {_EXPECTED_FORMAT_HINT}")
    return df, notes, counts


def _atomic_write(path: Path, data: bytes, attempts: int = 4) -> bool:
    """Write a file atomically (temp file + os.replace) with brief retries.

    On Windows the target can be locked by another program (typically the CSV
    open in Excel), which raises PermissionError/WinError 32 on a direct
    write. Retrying a few times covers transient locks; a persistent lock is
    reported to the caller instead of crashing the app.
    """
    tmp = path.with_suffix(path.suffix + '.tmp')
    last_err: Optional[BaseException] = None
    for attempt in range(attempts):
        try:
            with open(tmp, 'wb') as f:
                f.write(data)
            os.replace(tmp, path)
            return True
        except OSError as e:
            last_err = e
            # On Windows a read-only attribute on the target makes os.replace
            # fail with EACCES even when no process holds the file open, and
            # the app otherwise looks broken while every other write succeeds.
            # Clearing the flag between attempts recovers that case; a genuine
            # lock (the CSV open in Excel) still falls through to the retry.
            try:
                if path.exists() and not os.access(path, os.W_OK):
                    os.chmod(path, stat.S_IWRITE | stat.S_IREAD)
                    logger.info(f"Cleared the read-only attribute on {path.name}")
            except OSError:
                pass
            time.sleep(0.3 * (attempt + 1))
    try:
        if tmp.exists():
            tmp.unlink()
    except OSError:
        pass
    logger.error(
        f"Could not write {path.name} after {attempts} attempts: {last_err}. "
        "The file is most likely open in Excel or another program — close it there."
    )
    return False


def save_batch_state(df: pd.DataFrame, meta: Dict[str, Any]) -> bool:
    """Persist the working table + metadata so progress survives reruns/restarts.

    Returns False when the state files are locked by another program. The
    batch keeps running from memory in that case and results stay available
    via the download button — nothing is lost, only the on-disk snapshot.
    """
    try:
        with _BATCH_STATE_LOCK:
            csv_ok = _atomic_write(BATCH_STATE_CSV, df.to_csv(index=False).encode('utf-8-sig'))
            meta_ok = _atomic_write(
                BATCH_STATE_META,
                json.dumps(meta, indent=2, ensure_ascii=False).encode('utf-8'),
            )
        return csv_ok and meta_ok
    except Exception as e:
        logger.error(f"Failed to persist batch state: {e}")
        return False


def load_batch_state() -> Tuple[Optional[pd.DataFrame], Dict[str, Any]]:
    try:
        if BATCH_STATE_CSV.exists():
            df = pd.read_csv(BATCH_STATE_CSV, dtype=str, keep_default_na=False, encoding='utf-8-sig')
            meta: Dict[str, Any] = {}
            if BATCH_STATE_META.exists():
                with open(BATCH_STATE_META, 'r', encoding='utf-8') as f:
                    meta = json.load(f) or {}
            if not df.empty and df.shape[1] >= 4:
                return df, meta
    except Exception as e:
        logger.warning(f"Could not load saved batch state: {e}")
    return None, {}


def clear_batch_state() -> bool:
    """Delete the persisted state files. Returns False if a file is locked."""
    all_ok = True
    for path in (BATCH_STATE_CSV, BATCH_STATE_META):
        removed = False
        for attempt in range(3):
            try:
                if path.exists():
                    path.unlink()
                removed = True
                break
            except OSError as e:
                logger.warning(f"Could not remove {path.name} (attempt {attempt + 1}): {e}")
                time.sleep(0.3 * (attempt + 1))
        if not removed:
            all_ok = False
    return all_ok


def build_batch_download(df: pd.DataFrame, file_format: str, source_name: str) -> Tuple[bytes, str, str]:
    """Serialize the current batch table for download in its original format."""
    stem = Path(source_name or 'batch').stem or 'batch'
    if file_format == 'xlsx':
        buf = BytesIO()
        with pd.ExcelWriter(buf, engine='openpyxl') as writer:
            df.to_excel(writer, index=False)
        return (
            buf.getvalue(),
            f"{stem}_updated.xlsx",
            'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
        )
    return df.to_csv(index=False).encode('utf-8-sig'), f"{stem}_updated.csv", 'text/csv'


def count_statuses(df: pd.DataFrame) -> Dict[str, int]:
    """Count rows per status from the Status column."""
    values = df.iloc[:, STATUS_COL].astype(str).str.strip().str.lower()
    return {status: int((values == status).sum()) for status in VALID_STATUSES}


def render_queue_view(df: pd.DataFrame, notes: Dict[str, str],
                      metrics_slot, table_slot) -> None:
    """Render (or re-render) the batch metrics and status table into the given
    placeholders. Used both for the static view and for live updates while a
    batch is running."""
    counts = count_statuses(df)
    with metrics_slot.container():
        cols = st.columns(5)
        cols[0].metric("Rows", len(df))
        cols[1].metric("Pending", counts[STATUS_PENDING])
        cols[2].metric("Done", counts[STATUS_DONE])
        cols[3].metric("Duplicate", counts[STATUS_DUPLICATE])
        cols[4].metric("Errors", counts[STATUS_ERROR])
    view = df.copy()
    view['Details'] = [notes.get(str(i), '') for i in range(len(df))]
    table_slot.dataframe(view, width='stretch', hide_index=True)


def process_batch_rows(df: pd.DataFrame, row_indices: List[int], scraper: "EbayScraper",
                       file_manager: "FileManager", notes: Dict[str, str],
                       meta: Dict[str, Any], history: Dict[str, Dict[str, Dict[str, str]]],
                       metrics_slot=None, table_slot=None,
                       check_history: bool = True) -> Dict[str, int]:
    """Process the given rows one at a time, persisting status after each row.

    Sequential on purpose: parallel workers sharing one session were the main
    cause of eBay rate-limit blocks and half-finished batches. Every row is
    isolated in its own try/except, so one bad listing can never abort the
    rest of the batch, and the scraper itself retries with a fresh identity
    when eBay serves a bot-check page.

    Duplicates are re-checked here rather than trusted from import time: rows
    completed earlier in this same run must be able to flag later rows, and
    the history file may have grown since the file was uploaded. A duplicate
    is announced, written to the history log and skipped — the run always
    moves straight on to the next entry.
    """
    progress = st.progress(0.0)
    status_box = st.empty()
    stats = {'done': 0, 'error': 0, 'duplicate': 0, 'blocked': 0}
    total = len(row_indices)
    persist_ok = True
    source_file = str(meta.get('source_name', '') or '')

    # Rows already completed in the current table seed the in-run ledger, so a
    # second row pointing at the same listing is caught even with history off.
    run_ledger = new_ledger()
    for j in range(len(df)):
        if normalize_status(df.iat[j, STATUS_COL]) != STATUS_DONE:
            continue
        j_serial = normalize_serial(df.iat[j, SERIAL_COL])
        j_link = str(df.iat[j, LINK_COL]).strip()
        ledger_register(run_ledger, j_serial, batch_link_key(j_link, scraper),
                        {'serial': j_serial, 'link': j_link, 'when': '', 'file': source_file})

    consecutive_blocked_rows = 0
    aborted = False

    for pos, i in enumerate(row_indices, start=1):
        serial = normalize_serial(df.iat[i, SERIAL_COL])
        brand = str(df.iat[i, BRAND_COL]).strip() if df.shape[1] > BRAND_COL else ''
        link = str(df.iat[i, LINK_COL]).strip()
        link_key = batch_link_key(link, scraper)
        item_id = link_key[5:] if link_key.startswith('item:') else ''
        record = {
            'Source': 'batch', 'Source File': source_file, 'S.NO': serial,
            'Brand': brand, 'Link': link, 'Item ID': item_id,
        }
        status_box.info(f"Processing {pos}/{total} — S.NO {serial or '?'}")
        try:
            if not serial:
                raise ValidationError('Missing S.NO — cannot create a folder for this row.')
            if not link or link.lower() in ('nan', 'none'):
                raise ValidationError('Missing link.')

            dup = duplicate_reason(run_ledger, serial, link_key, scope='file')
            if not dup and check_history:
                dup = duplicate_reason(history, serial, link_key, scope='earlier')
            if dup:
                df.iat[i, STATUS_COL] = STATUS_DUPLICATE
                notes[str(i)] = dup
                stats['duplicate'] += 1
                status_box.warning(f"Skipped {pos}/{total} — {dup}")
                append_batch_status({**record, 'Status': STATUS_DUPLICATE, 'Details': dup})
                continue

            result = scraper.scrape_product(link)
            if result.success and result.product_data:
                folder_path = file_manager.create_serial_folder(serial)
                file_manager.save_product_description_markdown(result.product_data, folder_path)
                file_manager.save_product_text(result.product_data, folder_path)
                file_manager.save_raw_scrape_text(result.product_data, folder_path)
                images: List[str] = []
                if result.image_urls:
                    try:
                        images = file_manager.download_images(scraper, result.image_urls, folder_path)
                    except Exception as img_err:
                        # Images are best-effort; the scraped data is already saved.
                        logger.warning(f"Image download failed for S.NO {serial}: {img_err}")
                append_to_local_csv(result.product_data)
                bump_data_version()
                df.iat[i, STATUS_COL] = STATUS_DONE
                notes.pop(str(i), None)
                stats['done'] += 1
                entry = {'serial': serial, 'link': link,
                         'when': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                         'file': source_file, 'folder': folder_path.name}
                ledger_register(run_ledger, serial, link_key, entry)
                ledger_register(history, serial, link_key, entry)
                append_batch_status({
                    **record,
                    'Item ID': item_id or (result.product_data.item_id or ''),
                    'Status': STATUS_DONE, 'Details': '',
                    'Folder': str(folder_path), 'Title': result.product_data.title,
                    'Price': result.product_data.price,
                    'Condition': result.product_data.condition,
                    'Images': str(len(images)),
                })
            else:
                message = (result.error_message or 'Unknown error')[:300]
                df.iat[i, STATUS_COL] = STATUS_ERROR
                notes[str(i)] = message
                stats['error'] += 1
                if 'anti-bot' in message or 'refused the request' in message:
                    stats['blocked'] += 1
                    consecutive_blocked_rows += 1
                else:
                    consecutive_blocked_rows = 0
                append_batch_status({**record, 'Status': STATUS_ERROR, 'Details': message})
        except ValidationError as ve:
            df.iat[i, STATUS_COL] = STATUS_ERROR
            notes[str(i)] = str(ve)[:300]
            stats['error'] += 1
            append_batch_status({**record, 'Status': STATUS_ERROR, 'Details': str(ve)})
        except Exception as e:
            logger.error(f"Batch row {i} (S.NO {serial}) failed: {traceback.format_exc()}")
            message = str(e)[:300] or e.__class__.__name__
            df.iat[i, STATUS_COL] = STATUS_ERROR
            notes[str(i)] = message
            stats['error'] += 1
            append_batch_status({**record, 'Status': STATUS_ERROR, 'Details': message})
        finally:
            meta['notes'] = notes
            if not save_batch_state(df, meta):
                persist_ok = False
            progress.progress(pos / total)
            if metrics_slot is not None and table_slot is not None:
                render_queue_view(df, notes, metrics_slot, table_slot)

            if consecutive_blocked_rows >= MAX_CONSECUTIVE_BLOCKED_ROWS:
                # Every remaining row would fail the same way. Stopping keeps
                # the rest of the file `pending` so Retry picks up exactly
                # where this left off, instead of marking 40 good links as
                # errors and forcing the user to sort them out afterwards.
                aborted = True
                logger.warning(
                    f"Stopping the batch after {consecutive_blocked_rows} consecutive blocked "
                    f"listings; {total - pos} row(s) left untouched."
                )
                break

            if pos < total and normalize_status(df.iat[i, STATUS_COL]) != STATUS_DUPLICATE:
                # Pause between listings that actually hit the network. The
                # delay grows while eBay is blocking us, which is what stops a
                # run from degrading into every remaining row failing.
                # Duplicates never make a request, so they are not delayed.
                delay = scraper.cooldown_seconds()
                if scraper.consecutive_blocks:
                    status_box.warning(
                        f"eBay is throttling requests — waiting {delay:.0f}s before the next listing "
                        f"({scraper.consecutive_blocks} block(s) in a row)."
                    )
                time.sleep(delay)

    summary = f"{stats['done']} done, {stats['duplicate']} duplicate, {stats['error']} failed"
    if aborted:
        remaining = len(row_indices) - stats['done'] - stats['error'] - stats['duplicate']
        status_box.error(f"Batch stopped early — {summary}, {remaining} not attempted.")
    else:
        status_box.success(f"Batch finished — {summary}.")
    # Stash outcome messages in session state: the caller reruns the page
    # right after this returns, which would wipe anything rendered here.
    st.session_state.batch_last_run = f"Last run: {summary}."
    if not persist_ok:
        st.session_state.batch_persist_warning = True
    if stats['blocked']:
        # Retrying straight away just reproduces the block, which is what
        # makes the retry button look broken. Record when it is worth trying
        # again so the UI can hold the button until then.
        st.session_state.batch_blocked_count = stats['blocked']
        st.session_state.batch_aborted = aborted
        st.session_state.batch_retry_after = time.time() + BLOCK_COOLDOWN_MINUTES * 60
    return stats


def _render_batch_history() -> None:
    """History panel: the permanent per-link log, newest first."""
    log_df = load_batch_status_log()
    with st.expander(f"Processing history — {len(log_df)} entries", expanded=False):
        st.caption(
            f"Every link ever submitted is recorded in `{BATCH_STATUS_LOG.name}` with its "
            "status and details. Completed entries are what a re-upload is checked against."
        )
        if log_df.empty:
            st.info("No entries yet.")
            return
        # Size to content up to 10 rows, then scroll — a fixed height would
        # pad a short history with empty rows.
        row_height = 35
        height = min(len(log_df), 10) * row_height + 38
        st.dataframe(log_df.iloc[::-1], width='stretch', hide_index=True, height=height)
        col_dl, col_clear = st.columns(2)
        with col_dl:
            st.download_button(
                "Download history",
                data=log_df.to_csv(index=False).encode('utf-8-sig'),
                file_name=BATCH_STATUS_LOG.name,
                mime='text/csv',
                width='stretch',
            )
        with col_clear:
            if st.button("Clear history", width='stretch',
                         help="Forgets every processed entry — re-uploads will no longer be flagged as duplicates."):
                if clear_batch_status_log():
                    st.session_state.batch_history_cleared = True
                else:
                    st.session_state.batch_history_lock_warning = True
                st.rerun()


def render_batch_tab(scraper: "EbayScraper", file_manager: "FileManager") -> None:
    """CSV/Excel-driven batch processing tab."""
    st.subheader("Batch Processing")
    st.caption(
        "Upload a CSV or Excel file with the columns Brand, S.NO, Link, Status. "
        "Each listing is saved to a folder named after its S.NO, the Status column "
        "is updated, and links already processed are skipped as duplicates."
    )

    # Restore persisted state (survives page reruns and app restarts)
    if 'batch_df' not in st.session_state:
        saved_df, saved_meta = load_batch_state()
        st.session_state.batch_df = saved_df
        st.session_state.batch_meta = saved_meta or {}

    # Messages parked in session state by an action that ended in st.rerun()
    if st.session_state.pop('batch_clear_warning', False):
        st.warning("The saved state file is open in another program (usually Excel). "
                   "Close it there so batch progress can be saved to disk.")
    if st.session_state.pop('batch_persist_warning', False):
        st.warning(f"Progress could not be saved to `{BATCH_STATE_CSV.name}` because the file is "
                   "locked by another program. Your results are safe in this session — "
                   "use Download Updated File to export them.")
    if st.session_state.pop('batch_history_cleared', False):
        st.success("Processing history cleared. Previously processed links can be run again.")
    if st.session_state.pop('batch_history_lock_warning', False):
        st.warning(f"`{BATCH_STATUS_LOG.name}` is open in another program and could not be cleared.")
    last_run = st.session_state.pop('batch_last_run', '')
    if last_run:
        st.success(last_run)
    blocked_count = st.session_state.pop('batch_blocked_count', 0)
    if blocked_count:
        aborted = st.session_state.pop('batch_aborted', False)
        lead = (f"Stopped after {MAX_CONSECUTIVE_BLOCKED_ROWS} listings in a row were blocked. "
                "The rows that were never attempted are still `pending`, so Retry continues "
                "from where it stopped."
                if aborted else
                f"{blocked_count} row(s) were blocked by eBay.")
        st.warning(
            f"{lead}\n\neBay refused these requests with an anti-bot check — **the links are "
            "fine**. This is throttling of one IP address. Waiting is the only thing that "
            "clears it; retrying straight away hits the same block."
        )
        if not CURL_CFFI_AVAILABLE:
            st.info(
                "**This is worth doing once:** install `curl_cffi` and eBay sees a real "
                "browser's TLS fingerprint instead of Python's.\n\n"
                "```\npip install curl_cffi\n```\n\n"
                "Restart the app afterwards. Right now the requests claim to be Chrome in "
                "their headers while the TLS handshake says Python — that mismatch is one of "
                "the easiest things for eBay's edge to flag."
            )

    # --- Upload ---
    uploaded_file = st.file_uploader(
        "Upload batch file",
        type=['csv', 'xlsx', 'xls'],
        help="Columns 1-4: Brand, S.NO, Link, Status. Extra columns are preserved as-is.",
        key="batch_upload",
    )

    if uploaded_file is not None:
        file_sig = f"{uploaded_file.name}:{uploaded_file.size}"
        # Import once per uploaded file: Streamlit re-delivers the upload on
        # every rerun, and re-importing would wipe processing progress. A file
        # the user explicitly cleared is not re-imported either — it stays
        # attached to the uploader widget, so without this check clearing the
        # batch would immediately load it again.
        already_seen = st.session_state.get('batch_file_sig') == file_sig
        was_cleared = st.session_state.get('batch_cleared_sig') == file_sig
        if not already_seen and not was_cleared:
            try:
                raw_df = read_batch_upload(uploaded_file)
                history = build_history_ledger()
                df, notes, counts = prepare_batch_dataframe(
                    raw_df, scraper, history=history, source_name=uploaded_file.name
                )
                meta = {
                    'source_name': uploaded_file.name,
                    'format': 'xlsx' if uploaded_file.name.lower().endswith(('.xlsx', '.xls')) else 'csv',
                    'notes': notes,
                    'imported_at': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                }
                st.session_state.batch_df = df
                st.session_state.batch_meta = meta
                st.session_state.batch_file_sig = file_sig
                st.session_state.batch_import_counts = counts
                if not save_batch_state(df, meta):
                    st.warning(f"Could not save the batch to `{BATCH_STATE_CSV.name}` — it is locked by "
                               "another program. The batch will still run from memory in this session.")
                st.toast(f"Imported {len(df)} row(s) from {uploaded_file.name}")
            except ValueError as ve:
                st.error(str(ve))
            except Exception as e:
                logger.error(f"Failed reading batch upload: {traceback.format_exc()}")
                st.error(f"Could not read the file: {e}. Please upload a valid .csv or .xlsx file.")

    # Import summary — this is where a re-uploaded file announces its duplicates
    import_counts = st.session_state.pop('batch_import_counts', None)
    if import_counts:
        if import_counts.get(STATUS_DUPLICATE):
            st.warning(
                f"{import_counts[STATUS_DUPLICATE]} row(s) were already processed before and are "
                "marked **duplicate** — they will be skipped. See the Details column for which "
                "entry each one repeats."
            )
        if import_counts.get(STATUS_ERROR):
            st.error(f"{import_counts[STATUS_ERROR]} row(s) could not be read and are marked **error**. "
                     "See the Details column.")

    df = st.session_state.get('batch_df')
    meta = st.session_state.get('batch_meta') or {}
    notes: Dict[str, str] = meta.get('notes') or {}

    if df is None or len(df) == 0:
        st.info("No batch loaded yet. Upload a file above to begin.")
        with st.expander("Expected file format", expanded=False):
            st.markdown(
                """
| Brand | S.NO | Link | Status |
|-------|------|------|--------|
| Gucci | MB1079 | https://www.ebay.com/itm/1234567890 | pending |
| Prada | MB1080 | https://www.ebay.fr/itm/9876543210 | |

- Status may be `pending`, `done`, `duplicate` or `error`. Blank means pending.
- Rows marked `done` or `duplicate` are skipped.
- Columns after the fourth are never modified.
                """
            )
        _render_batch_history()
        return

    # --- Queue view (placeholders so processing can refresh it live) ---
    st.divider()
    st.markdown(f"**Current batch** — `{meta.get('source_name', 'restored session')}`")

    metrics_slot = st.empty()
    table_slot = st.empty()
    render_queue_view(df, notes, metrics_slot, table_slot)

    counts = count_statuses(df)
    n_pending = counts[STATUS_PENDING]
    n_error = counts[STATUS_ERROR]
    n_duplicate = counts[STATUS_DUPLICATE]

    # --- Actions ---
    col_a, col_b, col_c, col_d = st.columns(4)
    with col_a:
        process_clicked = st.button(
            f"Process {n_pending} pending", type="primary",
            disabled=n_pending == 0, width='stretch',
        )
    with col_b:
        # Hold Retry shut while eBay is still likely to be blocking us.
        # Letting the user re-trigger it immediately just reproduces the
        # block and burns another few minutes for nothing.
        retry_after = float(st.session_state.get('batch_retry_after') or 0)
        seconds_left = max(0, int(retry_after - time.time()))
        if seconds_left:
            retry_clicked = False
            st.button(f"Retry in {seconds_left // 60}m {seconds_left % 60:02d}s",
                      disabled=True, width='stretch',
                      help="eBay was blocking this run. Waiting is what clears it.")
        else:
            st.session_state.pop('batch_retry_after', None)
            retry_clicked = st.button(
                f"Retry {n_error} failed", disabled=n_error == 0, width='stretch',
            )
    with col_c:
        try:
            payload, fname, mime = build_batch_download(
                df, meta.get('format', 'csv'), meta.get('source_name', 'batch')
            )
            st.download_button("Download updated file", data=payload,
                               file_name=fname, mime=mime, width='stretch')
        except Exception as e:
            logger.error(f"Could not build batch download: {e}")
            st.button("Download unavailable", disabled=True, width='stretch')
    with col_d:
        if st.button("Clear batch", width='stretch',
                     help="Removes the loaded table. The processing history is kept."):
            if not clear_batch_state():
                # Surfaced after the rerun below, otherwise it would vanish
                st.session_state.batch_clear_warning = True
            st.session_state.batch_df = None
            st.session_state.batch_meta = {}
            st.session_state.batch_cleared_sig = st.session_state.pop('batch_file_sig', None)
            st.rerun()

    force_clicked = False
    if n_duplicate:
        force_clicked = st.button(
            f"Force reprocess {n_duplicate} duplicate row(s)",
            help="Runs rows that were skipped as already processed. Folders with the same "
                 "S.NO are overwritten. Repeats within this file are still skipped.",
        )

    # --- Processing ---
    indices: List[int] = []
    check_history = True
    if process_clicked:
        indices = [i for i in range(len(df)) if normalize_status(df.iat[i, STATUS_COL]) == STATUS_PENDING]
    elif retry_clicked:
        # Retry reprocesses every failed row plus anything still pending, so
        # nothing gets silently skipped. Duplicates stay skipped.
        for i in range(len(df)):
            if normalize_status(df.iat[i, STATUS_COL]) == STATUS_ERROR:
                df.iat[i, STATUS_COL] = STATUS_PENDING
                notes.pop(str(i), None)
        meta['notes'] = notes
        save_batch_state(df, meta)
        indices = [i for i in range(len(df)) if normalize_status(df.iat[i, STATUS_COL]) == STATUS_PENDING]
    elif force_clicked:
        check_history = False
        for i in range(len(df)):
            if normalize_status(df.iat[i, STATUS_COL]) == STATUS_DUPLICATE:
                df.iat[i, STATUS_COL] = STATUS_PENDING
                notes.pop(str(i), None)
        meta['notes'] = notes
        save_batch_state(df, meta)
        indices = [i for i in range(len(df)) if normalize_status(df.iat[i, STATUS_COL]) == STATUS_PENDING]

    if indices:
        st.divider()
        st.markdown("**Processing**")
        st.caption("One listing at a time with automatic retries. Progress is saved after every "
                   "row, so an interrupted batch can be resumed.")
        process_batch_rows(df, indices, scraper, file_manager, notes, meta,
                           history=build_history_ledger(),
                           metrics_slot=metrics_slot, table_slot=table_slot,
                           check_history=check_history)
        st.session_state.batch_df = df
        st.session_state.batch_meta = meta
        time.sleep(1.0)
        st.rerun()

    _render_batch_history()


# =============================================================================
# IMAGE FORMAT CONVERSION HELPERS
# =============================================================================

# JPG first: it is the default target, and new downloads already arrive as
# JPEG, so this tab is mainly for folders scraped before that change.
WEBP_TARGET_FORMATS = {
    "JPG":  {"ext": ".jpg",  "pillow": "JPEG", "save_kwargs": {"quality": 95, "subsampling": 0, "optimize": True}},
    "JPEG": {"ext": ".jpeg", "pillow": "JPEG", "save_kwargs": {"quality": 95, "subsampling": 0, "optimize": True}},
    "PNG":  {"ext": ".png",  "pillow": "PNG",  "save_kwargs": {}},
    "BMP":  {"ext": ".bmp",  "pillow": "BMP",  "save_kwargs": {}},
    "TIFF": {"ext": ".tiff", "pillow": "TIFF", "save_kwargs": {}},
}


def convert_webp_in_folder(folder: Path, target_key: str) -> Tuple[int, int, List[str]]:
    """Convert every .webp in `folder` to target_key format, replacing the original.

    Returns: (converted_count, failed_count, error_messages).
    """
    cfg = WEBP_TARGET_FORMATS[target_key]
    converted = 0
    failed = 0
    errors: List[str] = []
    for img_path in list(folder.iterdir()):
        if not (img_path.is_file() and img_path.suffix.lower() == '.webp'):
            continue
        try:
            with Image.open(img_path) as im:
                save_im = im
                if cfg["pillow"] == "JPEG" and save_im.mode in ("RGBA", "LA", "P"):
                    save_im = save_im.convert("RGB")
                elif cfg["pillow"] == "BMP" and save_im.mode == "RGBA":
                    save_im = save_im.convert("RGB")
                target_path = img_path.with_suffix(cfg["ext"])
                save_im.save(target_path, format=cfg["pillow"], **cfg["save_kwargs"])
            img_path.unlink(missing_ok=True)
            converted += 1
        except Exception as e:
            failed += 1
            errors.append(f"{img_path.name}: {e}")
            logger.warning(f"WebP conversion failed for {img_path}: {e}")
    return converted, failed, errors


def render_image_format_tab(file_manager: "FileManager") -> None:
    """Tab to bulk-convert .webp files in a chosen folder to another format."""
    st.subheader("Image Format")
    st.caption("New downloads are already saved as JPEG. Use this to convert WebP files in "
               "folders scraped earlier. Originals are replaced.")

    base_dir = file_manager.base_dir
    # One cached walk yields both the folders and their counts.
    folders = scan_webp_folders(str(base_dir), data_version())

    if not folders:
        st.info(f"No WebP images found under `{base_dir}`. Scrape some products first.")
        return

    def label(index: int) -> str:
        folder_str, count = folders[index]
        folder = Path(folder_str)
        name = "(root)" if folder == base_dir else str(folder.relative_to(base_dir))
        return f"{name} — {count} webp"

    col_folder, col_target = st.columns([2, 1])
    idx = col_folder.selectbox("Folder", options=list(range(len(folders))), format_func=label)
    target = col_target.selectbox("Convert to", options=list(WEBP_TARGET_FORMATS.keys()))

    selected_folder = Path(folders[idx][0])
    count = folders[idx][1]

    if st.button(f"Convert {count} file(s) to {target}", type="primary", disabled=not count):
        with st.spinner(f"Converting {count} image(s)..."):
            converted, failed, errors = convert_webp_in_folder(selected_folder, target)
        bump_data_version()
        if converted:
            st.session_state.fmt_result = f"Converted {converted} image(s) to {target}. Originals removed."
        if failed:
            st.session_state.fmt_errors = errors
        st.rerun()

    result = st.session_state.pop('fmt_result', '')
    if result:
        st.success(result)
    errors = st.session_state.pop('fmt_errors', None)
    if errors:
        st.error(f"{len(errors)} image(s) could not be converted.")
        with st.expander("Show errors"):
            for err in errors:
                st.code(err, language=None)


# =============================================================================
# IMAGE ENHANCEMENT TAB
# =============================================================================

# Preset name -> (brightness, contrast, sharpness, saturation)
IMAGE_PRESETS: Dict[str, Tuple[float, float, float, float]] = {
    "eBay ready":   (1.10, 1.15, 1.20, 1.05),
    "Social":       (1.05, 1.20, 1.15, 1.25),
    "Professional": (1.02, 1.08, 1.25, 0.98),
    "Reset":        (1.00, 1.00, 1.00, 1.00),
}


def render_image_enhancement_tab(file_manager: "FileManager") -> None:
    """Adjust brightness/contrast/sharpness/saturation and optionally watermark."""
    st.subheader("Image Enhancement")
    st.caption("Pick a folder, adjust the look, and optionally stamp a logo onto every image.")

    if 'img_settings' not in st.session_state:
        st.session_state.img_settings = IMAGE_PRESETS["Reset"]

    # --- Source folder and logo ---
    col_folder, col_logo = st.columns([2, 1])
    with col_folder:
        try:
            available_folders = [str(p) for p in file_manager.list_image_folders()]
        except Exception as e:
            logger.error(f"Could not list image folders: {e}")
            available_folders = []
        default_folder = str(Path.cwd() / BASE_SAVE_DIR)
        if default_folder not in available_folders:
            available_folders.insert(0, default_folder)
        base_folder = st.selectbox("Image folder", options=available_folders, index=0)
    with col_logo:
        uploaded_logo = st.file_uploader(
            "Logo (optional)", type=['png', 'jpg', 'jpeg', 'webp'],
            help="Watermarks every processed image.",
        )
        logo_image = None
        if uploaded_logo is not None:
            try:
                logo_image = Image.open(uploaded_logo)
                st.image(logo_image, width=90)
            except Exception as e:
                logger.warning(f"Could not read uploaded logo: {e}")
                st.error("That file could not be read as an image. Try a PNG or JPG.")

    # --- Presets ---
    preset_cols = st.columns(len(IMAGE_PRESETS))
    for col, (name, values) in zip(preset_cols, IMAGE_PRESETS.items()):
        if col.button(name, width='stretch'):
            st.session_state.img_settings = values
            st.rerun()

    brightness_default, contrast_default, sharpness_default, saturation_default = st.session_state.img_settings
    col_b, col_c, col_s, col_sat = st.columns(4)
    brightness = col_b.slider("Brightness", 0.1, 2.5, brightness_default, 0.01)
    contrast = col_c.slider("Contrast", 0.1, 2.5, contrast_default, 0.01)
    sharpness = col_s.slider("Sharpness", 0.1, 3.0, sharpness_default, 0.01)
    saturation = col_sat.slider("Saturation", 0.1, 2.5, saturation_default, 0.01)

    with st.expander("Logo placement", expanded=False):
        col_l1, col_l2, col_l3 = st.columns(3)
        logo_ratio = col_l1.slider("Size", 0.02, 0.40, 0.15, 0.01,
                                   help="Logo width as a fraction of the image width.")
        logo_position = col_l2.selectbox(
            "Position",
            options=["bottom-right", "bottom-left", "top-right", "top-left", "center"],
        )
        logo_opacity = col_l3.slider("Opacity", 0.1, 1.0, 1.0, 0.05)
        logo_margin = col_l1.number_input("Margin (px)", min_value=0, max_value=200, value=10, step=1)

    # --- Image selection ---
    folder_path = Path(base_folder)
    image_files: List[Path] = []
    try:
        if folder_path.exists() and folder_path.is_dir():
            image_files = file_manager.list_images(folder_path)
    except Exception as e:
        logger.error(f"Could not list images in {folder_path}: {e}")

    if not folder_path.exists():
        st.info(f"`{folder_path}` does not exist yet. Scrape a product to create it.")
        return
    if not image_files:
        st.info(f"No images found in `{folder_path}`.")
        return

    st.divider()
    file_names = [p.name for p in image_files]
    selections = st.multiselect(f"Images ({len(file_names)} available)",
                                options=file_names, default=file_names)
    out_subdir = st.text_input("Output subfolder", value="Enhanced")

    col_process, col_preview = st.columns(2)
    process_btn = col_process.button("Enhance selected", type="primary",
                                     disabled=not selections, width='stretch')
    preview_btn = col_preview.button("Preview first image", disabled=not selections, width='stretch')

    def _apply_logo(image: Image.Image) -> Image.Image:
        if logo_image is None:
            return image
        return file_manager.overlay_logo_pil(
            image, logo_image, size_ratio=logo_ratio, margin=int(logo_margin),
            position=logo_position, opacity=logo_opacity,
        )

    if preview_btn:
        try:
            source = next(p for p in image_files if p.name == selections[0])
            preview = file_manager.enhance_image(source, brightness, contrast, sharpness, saturation)
            st.image(_apply_logo(preview), caption=source.name, width='stretch')
        except FileNotFoundError:
            st.error("That image is no longer on disk. Refresh the folder and try again.")
        except Exception as e:
            logger.error(f"Preview failed: {traceback.format_exc()}")
            st.error(f"Could not build a preview: {e}")

    if process_btn:
        selected_paths = [p for p in image_files if p.name in selections]
        output_root = folder_path / (out_subdir.strip() or "Enhanced")
        progress_bar = st.progress(0.0)
        status_text = st.empty()

        def report(done: int, total: int) -> None:
            progress_bar.progress(done / total if total else 1.0)
            status_text.caption(f"Processing {done}/{total}")

        try:
            processed = file_manager.batch_process_images(
                image_paths=selected_paths,
                output_folder=output_root,
                logo_image=logo_image,
                brightness=brightness, contrast=contrast,
                sharpness=sharpness, saturation=saturation,
                logo_size_ratio=logo_ratio, logo_margin=int(logo_margin),
                logo_position=logo_position, logo_opacity=logo_opacity,
                progress_callback=report,
            )
            progress_bar.empty()
            status_text.empty()
            bump_data_version()
            failed = len(selected_paths) - len(processed)
            if processed:
                st.success(f"Enhanced {len(processed)} image(s) into `{output_root}`.")
            if failed > 0:
                st.warning(f"{failed} image(s) could not be processed — see the Logs tab for details.")
            if processed:
                with st.expander("Preview results", expanded=False):
                    cols = st.columns(3)
                    for idx, img_path in enumerate(processed[:6]):
                        try:
                            cols[idx % 3].image(str(img_path), caption=img_path.name, width='stretch')
                        except Exception:
                            continue
        except PermissionError:
            progress_bar.empty()
            status_text.empty()
            st.error(f"No permission to write into `{output_root}`. Pick a different output subfolder.")
        except OSError as e:
            progress_bar.empty()
            status_text.empty()
            logger.error(f"Image enhancement failed: {traceback.format_exc()}")
            st.error(f"Could not write the enhanced images: {e}")
        except Exception as e:
            progress_bar.empty()
            status_text.empty()
            logger.error(f"Image enhancement failed: {traceback.format_exc()}")
            st.error(f"Image enhancement failed: {e}")


# =============================================================================
# LOGS TAB AND FOOTER
# =============================================================================

def render_logs_tab(tail: int = 200) -> None:
    """Show the tail of the application log."""
    st.subheader("Logs")
    col_caption, col_refresh = st.columns([4, 1])
    col_caption.caption(f"Last {tail} lines of `{log_filename}`.")
    if col_refresh.button("Refresh", width='stretch'):
        read_log_tail.clear()
        st.rerun()

    log_path = Path(log_filename)
    if not log_path.exists():
        st.info("No log file yet — it is created on the first action.")
        return

    content = read_log_tail(_stat_key(log_path), tail)
    if not content:
        st.info("The log file is empty.")
        return

    st.code(content, language="text")
    try:
        st.download_button("Download full log", data=log_path.read_bytes(),
                           file_name=log_path.name, mime='text/plain')
    except PermissionError:
        st.caption(f"`{log_filename}` is locked by another program — download unavailable.")
    except OSError as e:
        st.caption(f"Download unavailable: {e}")


def build_downloads_archive(downloads_path: Path) -> bytes:
    """Zip the whole downloads tree into memory."""
    base = Path(tempfile.gettempdir()) / f"ebay_data_{os.getpid()}"
    archive = shutil.make_archive(str(base), 'zip', downloads_path)
    try:
        return Path(archive).read_bytes()
    finally:
        Path(archive).unlink(missing_ok=True)


def render_footer() -> None:
    """Export controls shown under every tab."""
    st.divider()
    downloads_path = Path.cwd() / BASE_SAVE_DIR
    has_data = downloads_path.exists() and any(downloads_path.iterdir())
    col_zip, col_open = st.columns(2)

    with col_zip:
        # Building the archive is deliberately behind a click. Zipping every
        # downloaded image on each script rerun made the whole app stall once
        # a few batches had been scraped.
        payload = st.session_state.get('zip_payload')
        if payload:
            st.download_button(
                "Download all data (ZIP)", data=payload,
                file_name=f"ebay_data_{st.session_state.get('zip_stamp', 'export')}.zip",
                mime="application/zip", width='stretch',
            )
        elif not has_data:
            st.button("Download all data (ZIP)", disabled=True, width='stretch',
                      help="Nothing has been scraped yet.")
        elif st.button("Prepare data export (ZIP)", width='stretch'):
            try:
                with st.spinner("Zipping downloads..."):
                    st.session_state.zip_payload = build_downloads_archive(downloads_path)
                st.session_state.zip_stamp = datetime.now().strftime('%Y%m%d_%H%M%S')
                st.rerun()
            except Exception as e:
                logger.error(f"Could not build the ZIP archive: {traceback.format_exc()}")
                st.error(f"Could not build the archive: {e}")

    with col_open:
        # Only meaningful when the app runs on the same machine as the browser.
        if st.button("Open downloads folder", width='stretch',
                     help="Works when the app runs locally, not on a hosted server."):
            opened, reason = open_local_folder(downloads_path)
            if opened:
                st.success(f"Opened `{downloads_path}`.")
            else:
                st.warning(reason)


def open_local_folder(path: Path) -> Tuple[bool, str]:
    """Open `path` in the OS file browser. Returns (opened, reason_if_not)."""
    import platform
    import subprocess

    if not path.exists():
        return False, f"`{path}` does not exist yet."
    system = platform.system()
    try:
        if system == "Windows":
            os.startfile(str(path))  # noqa: F821 - Windows only
        elif system == "Darwin":
            subprocess.Popen(["open", str(path)])
        else:
            subprocess.Popen(["xdg-open", str(path)])
        return True, ""
    except FileNotFoundError:
        return False, ("No desktop file browser is available here — this usually means the app "
                       "is running on a server. Use Download all data (ZIP) instead.")
    except Exception as e:
        logger.warning(f"Could not open {path}: {e}")
        return False, f"Could not open the folder: {e}"


# =============================================================================
# AI PROCESSING TAB
# =============================================================================

AI_PLATFORMS = [
    "General", "eBay", "Poshmark", "Mercari", "Depop", "Etsy",
    "Facebook Marketplace", "Shopify", "Vinted", "Grailed",
]

AI_PRESET_PROMPTS = {
    "Rewrite description": "Rewrite the product description to be more professional.",
    "Price analysis": "Analyse the pricing strategy for this item.",
    "SEO tags": "Suggest 10 relevant SEO tags for this product.",
}


def _pick_source_file(files: List[str]) -> int:
    """Index of the file to preselect — the raw scrape when it exists."""
    return next((i for i, name in enumerate(files) if "raw_scrape.txt" in name), 0)


def listing_filename(folder_name: str, platform: str) -> str:
    """Filename a generated listing is saved under, inside its product folder."""
    return f"{folder_name}_{platform}_listing.txt"


def has_listing(folder_info: Dict[str, Any], platform: str) -> bool:
    """True when this folder already holds a listing for the given platform."""
    target = listing_filename(folder_info['folder_name'], platform)
    return target in (folder_info.get('listing_files') or [])


def generate_listing_for_folder(processor: "AIProcessor", file_manager: "FileManager",
                                folder_info: Dict[str, Any], platform: str,
                                custom_instructions: str = "") -> Tuple[str, Path]:
    """Generate one listing and write it into the product folder.

    Returns (text, saved_path). Raises AIServiceError when the model call
    fails, and OSError when the folder cannot be written to.
    """
    files = folder_info.get('text_files') or []
    if not files:
        raise AIServiceError("No source text in this folder.", 'no_source')
    source = files[_pick_source_file(files)]
    raw_text = file_manager.load_product_text(folder_info['folder_path'], source)
    if not raw_text.strip():
        raise AIServiceError(f"`{source}` is empty.", 'no_source')

    text = processor.platform_agent.generate_platform_description(
        raw_text=raw_text, product_data=None, platform=platform,
        custom_instructions=custom_instructions,
    )
    out_path = Path(folder_info['folder_path']) / listing_filename(folder_info['folder_name'], platform)
    out_path.write_text(text, encoding='utf-8')
    return text, out_path


def render_bulk_generator(settings: AISettings, file_manager: "FileManager") -> None:
    """Generate listings for many scraped folders in one run.

    This is the batch counterpart to the single-folder generator: after a
    batch scrape of 50 listings, generating each one by hand is the slowest
    part of the workflow.
    """
    product_folders = file_manager.get_existing_product_folders()
    if not product_folders:
        st.info("No scraped products yet. Use the Batch Processing tab first.")
        return

    col_platform, col_scope = st.columns([1, 1])
    platform = col_platform.selectbox("Platform", AI_PLATFORMS, key="bulk_platform")
    skip_existing = col_scope.checkbox(
        "Skip folders that already have this listing", value=True,
        help="Uncheck to regenerate and overwrite existing listings.",
    )

    with st.expander("Custom instructions", expanded=False):
        custom_instructions = st.text_area(
            "Applied to every listing", height=80, label_visibility="collapsed",
            placeholder="e.g. always mention free returns",
        )

    pending = [f for f in product_folders if not (skip_existing and has_listing(f, platform))]
    done_count = len(product_folders) - len(pending)

    summary = st.columns(3)
    summary[0].metric("Folders", len(product_folders))
    summary[1].metric("To generate", len(pending))
    summary[2].metric("Already done", done_count)

    names = [f['folder_name'] for f in pending]
    chosen = st.multiselect("Folders to process", options=names, default=names)
    targets = [f for f in pending if f['folder_name'] in chosen]

    if st.button(f"Generate {len(targets)} listing(s)", type="primary",
                 disabled=not targets, width='stretch'):
        progress = st.progress(0.0)
        status = st.empty()
        results: List[Dict[str, str]] = []
        stopped = ''

        try:
            processor = AIProcessor(settings)
        except AIServiceError as e:
            st.error(str(e))
            return

        for position, folder in enumerate(targets, start=1):
            name = folder['folder_name']
            status.caption(f"Generating {position}/{len(targets)} — {name}")
            try:
                _, path = generate_listing_for_folder(
                    processor, file_manager, folder, platform, custom_instructions
                )
                results.append({'Folder': name, 'Status': 'done', 'Detail': path.name})
            except AIServiceError as e:
                results.append({'Folder': name, 'Status': 'error', 'Detail': str(e)})
                if e.kind in AI_FATAL_KINDS:
                    # Every remaining call would fail identically — stop here
                    # and keep what has already been written to disk.
                    stopped = str(e)
                    break
            except OSError as e:
                results.append({'Folder': name, 'Status': 'error',
                                'Detail': f"Could not save the listing: {e}"})
            except Exception as e:
                logger.error(f"Bulk generation failed for {name}: {traceback.format_exc()}")
                results.append({'Folder': name, 'Status': 'error', 'Detail': str(e)[:200]})
            progress.progress(position / len(targets))

        progress.empty()
        status.empty()
        bump_data_version()
        st.session_state.bulk_results = results
        st.session_state.bulk_stopped = stopped
        st.rerun()

    results = st.session_state.get('bulk_results')
    if results:
        succeeded = sum(1 for r in results if r['Status'] == 'done')
        failed = len(results) - succeeded
        stopped = st.session_state.get('bulk_stopped', '')
        if stopped:
            st.error(f"Stopped after {len(results)} folder(s): {stopped}")
            st.caption("Listings generated before the stop are saved. Re-run to continue "
                       "where it left off — completed folders are skipped.")
        elif failed:
            st.warning(f"{succeeded} generated, {failed} failed.")
        else:
            st.success(f"Generated {succeeded} listing(s) for {platform}.")
        st.dataframe(pd.DataFrame(results), width='stretch', hide_index=True)
        if st.button("Clear results"):
            st.session_state.pop('bulk_results', None)
            st.session_state.pop('bulk_stopped', None)
            st.rerun()


def _load_folder_context(file_manager: "FileManager", folder_info: Dict[str, str],
                         limit: int = 4000) -> str:
    """Read a folder's raw scrape text for use as chat context."""
    files = folder_info.get("text_files") or []
    if not files:
        return ""
    target = "raw_scrape.txt" if "raw_scrape.txt" in files else files[0]
    content = file_manager.load_product_text(folder_info["folder_path"], target)
    return f"\n\nCONTEXT:\n{content[:limit]}" if content else ""


def render_content_generator(settings: AISettings, file_manager: "FileManager") -> None:
    """Turn a scraped folder into a listing written for one marketplace."""
    product_folders = file_manager.get_existing_product_folders()
    if not product_folders:
        st.info("No scraped products yet. Use the Single Product or Batch Processing tab first.")
        return

    col_input, col_output = st.columns([1, 1.5], gap="large")

    with col_input:
        folder_names = [f["folder_name"] for f in product_folders]
        selected_folder_name = st.selectbox("Product folder", folder_names)

        # Switching folders clears the previous result so the output panel
        # never shows a description belonging to another product. The old
        # result is already saved in its own folder, so nothing is lost.
        if st.session_state.get("ai_last_folder") != selected_folder_name:
            st.session_state.ai_generated_result = None
            st.session_state.ai_last_folder = selected_folder_name

        folder_info = next((f for f in product_folders if f["folder_name"] == selected_folder_name), None)
        files = folder_info.get("text_files", []) if folder_info else []
        selected_file = st.selectbox("Source file", files, index=_pick_source_file(files)) if files else None

        target_platform = st.selectbox("Platform", AI_PLATFORMS,
                                       help="Sets the tone, structure and length.")
        with st.expander("Custom instructions", expanded=False):
            custom_instructions = st.text_area(
                "Extra rules", placeholder="e.g. focus on flaws, keep it short",
                height=80, label_visibility="collapsed",
            )
        generate_btn = st.button("Generate", type="primary", width='stretch',
                                 disabled=not selected_file)

    with col_output:
        st.session_state.setdefault("ai_generated_result", None)

        if generate_btn and folder_info and selected_file:
            try:
                original_content = file_manager.load_product_text(folder_info["folder_path"], selected_file)
                if not original_content.strip():
                    st.error(f"`{selected_file}` is empty. Pick another source file.")
                else:
                    with st.spinner(f"Writing for {target_platform}..."):
                        processor = AIProcessor(settings)
                        result_text = processor.platform_agent.generate_platform_description(
                            raw_text=original_content,
                            product_data=None,
                            platform=target_platform,
                            custom_instructions=custom_instructions,
                        )
                    st.session_state.ai_generated_result = {
                        "text": result_text,
                        "platform": target_platform,
                        "folder": selected_folder_name,
                        "timestamp": datetime.now().strftime("%H:%M"),
                    }
                    out_name = listing_filename(selected_folder_name, target_platform)
                    try:
                        (Path(folder_info["folder_path"]) / out_name).write_text(result_text, encoding='utf-8')
                        bump_data_version()
                        st.toast(f"Saved {out_name}")
                    except OSError as e:
                        logger.warning(f"Could not save generated listing: {e}")
                        st.warning("The listing was generated but could not be saved to the "
                                   "product folder. Use the download button below.")
            except AIServiceError as e:
                # Real cause (rate limit, bad key, context too long) rather
                # than a raw traceback.
                st.error(str(e))
            except Exception as e:
                logger.error(f"Content generation failed: {traceback.format_exc()}")
                st.error(f"Generation failed: {e}")

        result = st.session_state.ai_generated_result
        if result:
            st.caption(f"{result['platform']} · {result['folder']} · {result['timestamp']}")
            st.text_area("Listing", value=result['text'], height=460, label_visibility="collapsed")
            st.download_button(
                "Download .txt", data=result['text'],
                file_name=f"{result['folder']}_{result['platform']}_listing.txt",
                mime='text/plain',
            )
        else:
            st.info("Pick a product and press Generate.")


def render_ai_assistant(settings: AISettings, file_manager: "FileManager") -> None:
    """Free-form chat, optionally grounded in one scraped product folder."""
    product_folders = file_manager.get_existing_product_folders()
    context_options = ["No product context"] + [f["folder_name"] for f in product_folders]

    col_ctx, col_clear = st.columns([3, 1])
    selected_context = col_ctx.selectbox("Context", options=context_options,
                                         help="Ground the answers in one scraped product.")

    st.session_state.setdefault("chat_messages", [])
    messages: List[Dict[str, Any]] = st.session_state.chat_messages

    if col_clear.button("Clear chat", width='stretch', disabled=not messages):
        st.session_state.chat_messages = []
        st.rerun()

    if not messages:
        st.caption("Ask anything about your listings, or start with one of these:")
        preset_cols = st.columns(len(AI_PRESET_PROMPTS))
        for col, (label, prompt) in zip(preset_cols, AI_PRESET_PROMPTS.items()):
            if col.button(label, width='stretch'):
                messages.append({"user": prompt, "assistant": None})
                st.rerun()

    for msg in messages:
        with st.chat_message("user"):
            st.write(msg['user'])
        if msg.get('assistant') is not None:
            with st.chat_message("assistant"):
                st.write(msg['assistant'])

    # The last message having no answer means a reply is owed — either from a
    # preset button or from a run that was interrupted mid-stream.
    if messages and messages[-1].get('assistant') is None:
        with st.chat_message("assistant"):
            try:
                context_text = ""
                if selected_context != "No product context":
                    folder_info = next((f for f in product_folders if f["folder_name"] == selected_context), None)
                    if folder_info:
                        context_text = _load_folder_context(file_manager, folder_info)

                processor = AIProcessor(settings)
                system_prompt = (
                    "You are an e-commerce listing expert helping the owner of an eBay resale "
                    "store. Be specific and actionable. When CONTEXT is supplied, answer from it "
                    "rather than in generalities. When asked for a rewrite, output the final text "
                    "only, with no preamble. Keep answers concise."
                )
                with st.spinner("Thinking..."):
                    stream = processor.client.chat.completions.create(
                        model=processor.model,
                        messages=[
                            {"role": "system", "content": system_prompt},
                            {"role": "user", "content": messages[-1]['user'] + context_text},
                        ],
                        stream=True,
                    )

                    def chunks():
                        for chunk in stream:
                            piece = chunk.choices[0].delta.content
                            if piece:
                                yield piece

                    full_response = st.write_stream(chunks())
                messages[-1]['assistant'] = full_response
                st.rerun()
            except AIServiceError as e:
                st.error(str(e))
                # Drop the unanswered turn so the failure is not retried on
                # every rerun of the page.
                messages.pop()
            except Exception as e:
                logger.error(f"AI assistant failed: {traceback.format_exc()}")
                st.error(describe_ai_error(e))
                messages.pop()

    if query := st.chat_input("Ask about your products..."):
        messages.append({"user": query, "assistant": None})
        st.rerun()


def render_ai_tab(settings: AISettings, file_manager: "FileManager") -> None:
    """AI Processing tab: listing generator plus a product-aware assistant."""
    st.subheader("AI Processing")
    st.caption(f"Generate platform-ready listings and ask questions about your scraped "
               f"products. Using **{settings.provider.label}** · `{settings.model_name}`.")

    if not settings.ready:
        # Note: no st.stop() here — that would abort the whole script run and
        # leave every tab rendered after this one blank.
        st.info(f"Add a {settings.provider.key_label} in the sidebar to enable these "
                f"features. Create one at {settings.provider.console_url}.")
        return

    gen_tab, bulk_tab, chat_tab = st.tabs(["Content Generator", "Bulk Generate", "Assistant"])
    with gen_tab:
        render_content_generator(settings, file_manager)
    with bulk_tab:
        render_bulk_generator(settings, file_manager)
    with chat_tab:
        render_ai_assistant(settings, file_manager)


def inject_global_styles() -> None:
    """Inject modern, premium global styles with sidebar-nav-friendly layout."""
    st.markdown(
        """
        <style>
        @import url('https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700;800;900&family=JetBrains+Mono:wght@400;500&display=swap');

        :root {
            --bg: #f7f7f8;
            --surface: #ffffff;
            --surface-2: #fafafa;
            --surface-3: #f3f4f6;
            --border: #e5e7eb;
            --border-strong: #d1d5db;
            --text: #0f172a;
            --text-soft: #475569;
            --text-muted: #94a3b8;
            --brand: #0f172a;
            --brand-hover: #1e293b;
            --accent: #6366f1;
            --accent-2: #8b5cf6;
            --success: #10b981;
            --warning: #f59e0b;
            --danger: #ef4444;
            --info: #3b82f6;
            --shadow-sm: 0 1px 2px rgba(15, 23, 42, 0.04), 0 1px 3px rgba(15, 23, 42, 0.06);
            --shadow-md: 0 4px 12px rgba(15, 23, 42, 0.06), 0 2px 4px rgba(15, 23, 42, 0.04);
            --shadow-lg: 0 20px 40px -16px rgba(15, 23, 42, 0.18), 0 8px 16px -8px rgba(15, 23, 42, 0.08);
            --radius-sm: 8px;
            --radius-md: 12px;
            --radius-lg: 16px;
            --radius-xl: 20px;
            --radius-pill: 999px;
        }

        html, body, .stApp, [class*="st-emotion"] {
            font-family: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif !important;
            font-feature-settings: "ss01", "cv11";
        }

        /* Restore Streamlit's icon font: the rule above matches every
           st-emotion element, which otherwise breaks Material Symbols
           ligatures and renders icon names as raw text
           ("keyboard_arrow_right" etc.). */
        [data-testid="stIconMaterial"],
        [data-testid="stExpanderToggleIcon"],
        .material-symbols-rounded,
        span[class*="material-symbols"] {
            font-family: 'Material Symbols Rounded' !important;
            font-feature-settings: 'liga' !important;
        }
        .stApp { background: var(--bg) !important; color: var(--text) !important; }

        /* Hide Streamlit chrome */
        #MainMenu, footer, header[data-testid="stHeader"] { visibility: hidden !important; height: 0 !important; }

        /* ---------- LAYOUT ---------- */
        .block-container {
            padding: 1.75rem 2rem 4rem !important;
            max-width: 1400px !important;
        }

        /* ---------- TYPOGRAPHY ---------- */
        h1 { font-size: 2rem !important; font-weight: 800 !important; letter-spacing: -0.03em !important; color: var(--text) !important; margin: 0 0 0.25rem !important; }
        h2 { font-size: 1.4rem !important; font-weight: 700 !important; letter-spacing: -0.02em !important; color: var(--text) !important; margin: 0 0 0.5rem !important; }
        h3 { font-size: 1.1rem !important; font-weight: 700 !important; color: var(--text) !important; margin: 0 0 0.5rem !important; }
        h4 { font-size: 0.98rem !important; font-weight: 600 !important; color: var(--text) !important; }
        p, label, span, div { color: var(--text); }

        /* ---------- PAGE HEADER (custom hero block) ---------- */
        .es-hero {
            background: linear-gradient(135deg, #0f172a 0%, #1e293b 50%, #312e81 100%);
            color: white;
            border-radius: var(--radius-lg);
            padding: 1.75rem 2rem;
            margin-bottom: 1.5rem;
            box-shadow: var(--shadow-lg);
            position: relative;
            overflow: hidden;
        }
        .es-hero::before {
            content: "";
            position: absolute;
            top: -50%; right: -10%;
            width: 60%; height: 200%;
            background: radial-gradient(circle, rgba(139, 92, 246, 0.4) 0%, transparent 60%);
            transform: rotate(15deg);
            pointer-events: none;
        }
        .es-hero h1 { color: white !important; font-size: 1.85rem !important; font-weight: 800 !important; margin: 0 !important; letter-spacing: -0.02em !important; }
        .es-hero p { color: rgba(255, 255, 255, 0.7) !important; margin: 0.25rem 0 0 !important; font-size: 0.95rem !important; }
        .es-hero .es-badge {
            display: inline-block;
            background: rgba(139, 92, 246, 0.2);
            color: #c4b5fd;
            border: 1px solid rgba(139, 92, 246, 0.4);
            padding: 0.2rem 0.7rem;
            border-radius: var(--radius-pill);
            font-size: 0.72rem;
            font-weight: 600;
            letter-spacing: 0.05em;
            text-transform: uppercase;
            margin-bottom: 0.6rem;
        }

        /* ---------- SECTION CARDS ---------- */
        .es-card {
            background: var(--surface);
            border: 1px solid var(--border);
            border-radius: var(--radius-lg);
            padding: 1.5rem;
            box-shadow: var(--shadow-sm);
            margin-bottom: 1.25rem;
        }
        .es-card-title {
            font-size: 1rem;
            font-weight: 700;
            color: var(--text);
            display: flex;
            align-items: center;
            gap: 0.5rem;
            margin-bottom: 0.25rem;
        }
        .es-card-sub {
            color: var(--text-soft);
            font-size: 0.88rem;
            margin: 0 0 1rem;
        }

        /* ---------- SIDEBAR ---------- */
        section[data-testid="stSidebar"] {
            background: linear-gradient(180deg, #ffffff 0%, #fafafa 100%) !important;
            border-right: 1px solid var(--border) !important;
            box-shadow: 4px 0 24px rgba(15, 23, 42, 0.04);
        }

        /* Sidebar open/close controls.
           Streamlit ships these as visibility:hidden and only reveals them
           when the pointer is over the relevant corner. The hero banner sits
           across that corner, so once the sidebar was collapsed there was no
           discoverable way to bring it back. Both controls are therefore
           pinned visible, given a solid chip style and lifted above the hero. */
        [data-testid="stSidebarCollapseButton"],
        [data-testid="stSidebarCollapseButton"] button,
        [data-testid="stExpandSidebarButton"],
        [data-testid="stExpandSidebarButton"] button {
            visibility: visible !important;
            opacity: 1 !important;
            pointer-events: auto !important;
        }
        [data-testid="stExpandSidebarButton"] {
            position: fixed !important;
            top: 0.65rem !important;
            left: 0.65rem !important;
            z-index: 1000000 !important;
            background: var(--surface) !important;
            border: 1px solid var(--border-strong) !important;
            border-radius: 10px !important;
            box-shadow: var(--shadow-md) !important;
            width: 34px !important;
            height: 34px !important;
            align-items: center !important;
            justify-content: center !important;
        }
        [data-testid="stExpandSidebarButton"]:hover {
            border-color: var(--accent) !important;
            background: var(--surface-3) !important;
        }
        [data-testid="stExpandSidebarButton"] svg,
        [data-testid="stSidebarCollapseButton"] svg {
            fill: var(--text) !important;
            color: var(--text) !important;
        }
        /* Keep the hero clear of the pinned expand chip */
        .es-hero { position: relative; z-index: 1; }
        section[data-testid="stSidebar"] > div { padding: 1.25rem 0.85rem !important; }
        section[data-testid="stSidebar"] h2,
        section[data-testid="stSidebar"] h3 { color: var(--text) !important; }
        section[data-testid="stSidebar"] .es-side-brand {
            display: flex; align-items: center; gap: 0.6rem;
            padding: 0.4rem 0.5rem 1rem;
            border-bottom: 1px solid var(--border);
            margin-bottom: 1rem;
        }
        section[data-testid="stSidebar"] .es-side-brand .es-logo {
            width: 36px; height: 36px;
            border-radius: 10px;
            background: linear-gradient(135deg, #0f172a, #6366f1);
            display: flex; align-items: center; justify-content: center;
            color: white; font-weight: 800; font-size: 1rem;
            box-shadow: var(--shadow-md);
        }
        section[data-testid="stSidebar"] .es-side-brand .es-side-title {
            font-weight: 800; color: var(--text); font-size: 1.05rem; line-height: 1;
        }
        section[data-testid="stSidebar"] .es-side-brand .es-side-sub {
            color: var(--text-muted); font-size: 0.7rem; letter-spacing: 0.1em; text-transform: uppercase;
        }
        section[data-testid="stSidebar"] .es-side-section {
            color: var(--text-muted) !important;
            font-size: 0.68rem !important;
            font-weight: 700 !important;
            letter-spacing: 0.12em !important;
            text-transform: uppercase !important;
            padding: 0.5rem 0.75rem;
            margin-top: 0.5rem;
        }

        /* Sidebar radio nav -> styled pills/cards */
        section[data-testid="stSidebar"] div[role="radiogroup"] {
            gap: 0.25rem !important;
            background: transparent !important;
        }
        section[data-testid="stSidebar"] div[role="radiogroup"] > label {
            background: transparent !important;
            border: 1px solid transparent !important;
            border-radius: var(--radius-md) !important;
            padding: 0.6rem 0.85rem !important;
            cursor: pointer !important;
            transition: all 0.18s ease !important;
            display: flex !important;
            align-items: center !important;
            gap: 0.55rem !important;
            margin: 0 !important;
            color: var(--text-soft) !important;
            font-weight: 500 !important;
        }
        section[data-testid="stSidebar"] div[role="radiogroup"] > label:hover {
            background: var(--surface-3) !important;
            color: var(--text) !important;
        }
        section[data-testid="stSidebar"] div[role="radiogroup"] > label[data-baseweb="radio"] > div:first-child {
            display: none !important;
        }
        section[data-testid="stSidebar"] div[role="radiogroup"] > label[aria-checked="true"] {
            background: var(--brand) !important;
            color: white !important;
            border-color: var(--brand) !important;
            box-shadow: var(--shadow-md) !important;
            transform: translateX(2px);
        }
        section[data-testid="stSidebar"] div[role="radiogroup"] > label[aria-checked="true"] * {
            color: white !important;
        }

        /* ---------- TABS (used in sub-tabs) ---------- */
        .stTabs [data-baseweb="tab-list"] {
            gap: 0.4rem !important;
            background: var(--surface-3) !important;
            padding: 0.3rem !important;
            border-radius: var(--radius-pill) !important;
            border: 1px solid var(--border) !important;
            display: inline-flex !important;
            width: auto !important;
        }
        .stTabs [data-baseweb="tab"] {
            background: transparent !important;
            color: var(--text-soft) !important;
            border-radius: var(--radius-pill) !important;
            padding: 0.5rem 1.1rem !important;
            border: none !important;
            font-weight: 600 !important;
            font-size: 0.88rem !important;
            transition: all 0.18s ease !important;
            min-height: unset !important;
        }
        .stTabs [data-baseweb="tab"]:hover { background: rgba(15, 23, 42, 0.04) !important; color: var(--text) !important; transform: none !important; }
        .stTabs [aria-selected="true"] {
            background: var(--surface) !important;
            color: var(--text) !important;
            box-shadow: var(--shadow-sm) !important;
            transform: none !important;
        }
        .stTabs [data-baseweb="tab-highlight"] { display: none !important; }
        .stTabs [data-baseweb="tab-border"] { display: none !important; }

        /* ---------- INPUTS ---------- */
        .stTextInput input, .stNumberInput input, .stTextArea textarea, .stDateInput input {
            background: var(--surface) !important;
            color: var(--text) !important;
            border: 1.5px solid var(--border) !important;
            border-radius: var(--radius-md) !important;
            padding: 0.65rem 0.9rem !important;
            font-size: 0.95rem !important;
            font-weight: 500 !important;
            transition: all 0.18s ease !important;
            box-shadow: var(--shadow-sm) !important;
        }
        .stTextInput input::placeholder, .stTextArea textarea::placeholder {
            color: var(--text-muted) !important;
            font-weight: 400 !important;
        }
        .stTextInput input:focus, .stNumberInput input:focus, .stTextArea textarea:focus {
            border-color: var(--accent) !important;
            box-shadow: 0 0 0 4px rgba(99, 102, 241, 0.12) !important;
            outline: none !important;
        }
        .stTextInput input:hover, .stNumberInput input:hover, .stTextArea textarea:hover {
            border-color: var(--border-strong) !important;
        }

        /* Selects */
        .stSelectbox [data-baseweb="select"] > div,
        .stMultiSelect [data-baseweb="select"] {
            background: var(--surface) !important;
            border: 1.5px solid var(--border) !important;
            border-radius: var(--radius-md) !important;
            min-height: 44px !important;
            box-shadow: var(--shadow-sm) !important;
            transition: all 0.18s ease !important;
        }
        .stSelectbox [data-baseweb="select"]:focus-within > div,
        .stMultiSelect [data-baseweb="select"]:focus-within {
            border-color: var(--accent) !important;
            box-shadow: 0 0 0 4px rgba(99, 102, 241, 0.12) !important;
        }
        [data-baseweb="menu"] {
            background: var(--surface) !important;
            border: 1px solid var(--border) !important;
            border-radius: var(--radius-md) !important;
            box-shadow: var(--shadow-lg) !important;
        }
        [data-baseweb="menu"] li:hover { background: var(--surface-3) !important; }

        /* Multiselect tags */
        .stMultiSelect [data-baseweb="tag"] {
            background: var(--brand) !important;
            color: white !important;
            border-radius: var(--radius-sm) !important;
            font-weight: 600 !important;
        }
        .stMultiSelect [data-baseweb="tag"] svg { fill: white !important; }

        /* ---------- BUTTONS ---------- */
        .stButton > button {
            background: var(--brand) !important;
            color: white !important;
            border: 1.5px solid var(--brand) !important;
            border-radius: var(--radius-md) !important;
            padding: 0.6rem 1.25rem !important;
            font-weight: 600 !important;
            font-size: 0.92rem !important;
            transition: all 0.18s ease !important;
            box-shadow: var(--shadow-sm) !important;
            letter-spacing: -0.005em !important;
        }
        .stButton > button:hover {
            background: var(--brand-hover) !important;
            border-color: var(--brand-hover) !important;
            transform: translateY(-1px) !important;
            box-shadow: var(--shadow-md) !important;
        }
        .stButton > button:active { transform: translateY(0) !important; }
        .stButton > button[kind="secondary"] {
            background: var(--surface) !important;
            color: var(--text) !important;
            border: 1.5px solid var(--border) !important;
            box-shadow: var(--shadow-sm) !important;
        }
        .stButton > button[kind="secondary"]:hover {
            background: var(--surface-3) !important;
            border-color: var(--border-strong) !important;
        }
        .stButton > button[kind="primary"] {
            background: linear-gradient(135deg, #6366f1 0%, #8b5cf6 100%) !important;
            border-color: transparent !important;
            box-shadow: 0 4px 14px rgba(99, 102, 241, 0.35) !important;
        }
        .stButton > button[kind="primary"]:hover {
            box-shadow: 0 6px 20px rgba(99, 102, 241, 0.45) !important;
            filter: brightness(1.05);
        }
        .stDownloadButton > button {
            background: linear-gradient(135deg, #10b981 0%, #059669 100%) !important;
            border-color: transparent !important;
            color: white !important;
            box-shadow: 0 4px 14px rgba(16, 185, 129, 0.3) !important;
        }
        .stDownloadButton > button:hover {
            box-shadow: 0 6px 20px rgba(16, 185, 129, 0.4) !important;
        }

        /* ---------- ALERTS ---------- */
        .stAlert {
            border-radius: var(--radius-md) !important;
            border: 1px solid var(--border) !important;
            border-left-width: 4px !important;
            padding: 0.85rem 1rem !important;
            box-shadow: var(--shadow-sm) !important;
        }
        .stSuccess { background: #f0fdf4 !important; border-left-color: var(--success) !important; }
        .stInfo { background: #eff6ff !important; border-left-color: var(--info) !important; }
        .stWarning { background: #fffbeb !important; border-left-color: var(--warning) !important; }
        .stError { background: #fef2f2 !important; border-left-color: var(--danger) !important; }

        /* ---------- PROGRESS ---------- */
        .stProgress > div > div > div {
            background: linear-gradient(90deg, var(--accent), var(--accent-2)) !important;
            border-radius: var(--radius-pill) !important;
        }
        .stProgress > div > div {
            background: var(--surface-3) !important;
            border-radius: var(--radius-pill) !important;
        }

        /* ---------- EXPANDER ---------- */
        details[data-testid="stExpander"], .streamlit-expanderHeader {
            background: var(--surface) !important;
            border: 1px solid var(--border) !important;
            border-radius: var(--radius-md) !important;
            box-shadow: var(--shadow-sm) !important;
        }
        details[data-testid="stExpander"] summary {
            padding: 0.85rem 1rem !important;
            font-weight: 600 !important;
            color: var(--text) !important;
        }
        details[data-testid="stExpander"] summary:hover { background: var(--surface-3) !important; }

        /* ---------- METRICS ---------- */
        [data-testid="stMetric"] {
            background: var(--surface);
            border: 1px solid var(--border);
            border-radius: var(--radius-md);
            padding: 1rem 1.25rem;
            box-shadow: var(--shadow-sm);
        }
        [data-testid="stMetricValue"] {
            color: var(--text) !important;
            font-size: 1.75rem !important;
            font-weight: 800 !important;
            letter-spacing: -0.02em !important;
        }
        [data-testid="stMetricLabel"] {
            color: var(--text-muted) !important;
            font-size: 0.75rem !important;
            font-weight: 600 !important;
            text-transform: uppercase;
            letter-spacing: 0.08em;
        }

        /* ---------- CODE / LOGS ---------- */
        code, pre {
            font-family: 'JetBrains Mono', 'Fira Code', monospace !important;
            background: var(--surface-3) !important;
            color: var(--text) !important;
            border-radius: 6px !important;
            font-size: 0.85rem !important;
        }
        .stCodeBlock {
            background: #0f172a !important;
            border: 1px solid #1e293b !important;
            border-radius: var(--radius-md) !important;
        }
        .stCodeBlock pre, .stCodeBlock code {
            background: transparent !important;
            color: #e2e8f0 !important;
        }

        /* ---------- PRODUCT CARD (preserve existing classnames) ---------- */
        .product-card {
            background: var(--surface);
            border-radius: var(--radius-lg);
            box-shadow: var(--shadow-lg);
            border: 1px solid var(--border);
            overflow: hidden;
            margin-top: 1rem;
        }
        .product-header {
            padding: 1.25rem 1.75rem;
            background: linear-gradient(135deg, #fafafa, #ffffff);
            border-bottom: 1px solid var(--border);
        }
        .product-title { font-size: 1.25rem; font-weight: 700; color: var(--text); margin: 0; line-height: 1.4; }
        .product-body { display: flex; padding: 1.75rem; gap: 2rem; flex-wrap: wrap; }
        .product-image-container { flex: 0 0 320px; max-width: 100%; }
        .product-image { width: 100%; border-radius: var(--radius-md); object-fit: contain; background: var(--surface-3); aspect-ratio: 1; box-shadow: var(--shadow-sm); }
        .product-details { flex: 1; min-width: 280px; }
        .price-tag { font-size: 2.25rem; font-weight: 800; color: var(--text); margin-bottom: 0.5rem; letter-spacing: -0.03em; background: linear-gradient(135deg, #0f172a, #6366f1); -webkit-background-clip: text; -webkit-text-fill-color: transparent; background-clip: text; }
        .detail-row { display: flex; align-items: flex-start; padding: 0.65rem 0; border-bottom: 1px solid var(--surface-3); }
        .detail-label { font-weight: 600; color: var(--text-muted); width: 110px; flex-shrink: 0; font-size: 0.82rem; text-transform: uppercase; letter-spacing: 0.05em; }
        .detail-value { color: var(--text); font-size: 0.95rem; line-height: 1.5; }
        .status-section { display: flex; gap: 0.5rem; flex-wrap: wrap; margin-top: 1.25rem; padding-top: 1rem; border-top: 1px dashed var(--border); }
        .status-badge { display: inline-flex; align-items: center; padding: 0.3rem 0.75rem; border-radius: var(--radius-pill); font-size: 0.78rem; font-weight: 600; background: #ecfdf5; color: #047857; border: 1px solid #a7f3d0; }
        .status-badge.neutral { background: var(--surface-3); color: var(--text-soft); border-color: var(--border); }

        /* ---------- SLIDERS ---------- */
        .stSlider [role="slider"] {
            background: var(--brand) !important;
            box-shadow: 0 0 0 4px rgba(15, 23, 42, 0.1) !important;
            width: 18px !important;
            height: 18px !important;
        }
        .stSlider [data-baseweb="slider"] > div:first-child > div { background: var(--surface-3) !important; height: 5px !important; border-radius: 3px !important; }
        .stSlider [data-baseweb="slider"] > div:first-child > div > div { background: linear-gradient(90deg, var(--accent), var(--accent-2)) !important; }
        .stSlider [role="slider"]:hover { transform: scale(1.15) !important; }

        /* ---------- CHECKBOXES & RADIOS ---------- */
        .stCheckbox label, .stRadio label { color: var(--text) !important; font-weight: 500 !important; }

        /* ---------- DATAFRAME ---------- */
        [data-testid="stDataFrame"] { border: 1px solid var(--border) !important; border-radius: var(--radius-md) !important; overflow: hidden; box-shadow: var(--shadow-sm); }

        /* ---------- SCROLLBARS ---------- */
        ::-webkit-scrollbar { width: 10px; height: 10px; }
        ::-webkit-scrollbar-track { background: var(--surface-2); }
        ::-webkit-scrollbar-thumb { background: var(--border-strong); border-radius: 5px; border: 2px solid var(--surface-2); }
        ::-webkit-scrollbar-thumb:hover { background: var(--text-muted); }

        /* ---------- ANIMATIONS ---------- */
        @keyframes fadeInUp { from { opacity: 0; transform: translateY(8px); } to { opacity: 1; transform: translateY(0); } }
        @keyframes fadeIn { from { opacity: 0; } to { opacity: 1; } }
        .es-card, .product-card, .es-hero, .stAlert { animation: fadeInUp 0.35s ease-out; }

        /* ---------- RESPONSIVE ---------- */
        @media (max-width: 768px) {
            .block-container { padding: 1rem !important; }
            .es-hero { padding: 1.25rem; }
            .product-body { padding: 1rem; gap: 1rem; }
            .product-image-container { flex: 1 1 100%; }
        }

        /* ---------- DIVIDERS ---------- */
        hr { border: none !important; border-top: 1px solid var(--border) !important; margin: 1.25rem 0 !important; }

        /* ---------- FILE UPLOADER ---------- */
        [data-testid="stFileUploader"] section {
            background: var(--surface) !important;
            border: 2px dashed var(--border-strong) !important;
            border-radius: var(--radius-md) !important;
            padding: 1.25rem !important;
            transition: all 0.2s ease !important;
        }
        [data-testid="stFileUploader"] section:hover {
            border-color: var(--accent) !important;
            background: rgba(99, 102, 241, 0.03) !important;
        }

        /* =====================================================================
           THEME ROBUSTNESS
           This app ships a single, polished light theme. The block below makes
           sure it stays readable even when Streamlit is switched to its built-in
           Dark theme (Settings -> Appearance). It pins every surface and text
           colour explicitly so nothing renders dark-text-on-dark or
           white-text-on-white in any state.
           ===================================================================== */
        :root { color-scheme: light !important; }
        html, body, .stApp { color-scheme: light !important; }

        /* Force the app canvas + main containers to the light palette */
        .stApp, .main, .block-container,
        [data-testid="stAppViewContainer"],
        [data-testid="stMain"],
        [data-testid="stHeader"] {
            background: var(--bg) !important;
            color: var(--text) !important;
        }

        /* Generic readable text (paragraphs, lists, captions, markdown) */
        .stApp p, .stApp li, .stApp label,
        .stMarkdown, .stMarkdown p, .stMarkdown li,
        [data-testid="stMarkdownContainer"] p,
        [data-testid="stMarkdownContainer"] li,
        [data-testid="stCaptionContainer"],
        [data-testid="stWidgetLabel"] p,
        [data-testid="stWidgetLabel"] label {
            color: var(--text) !important;
        }

        /* Selectbox / multiselect: the closed control + its displayed value */
        .stSelectbox [data-baseweb="select"] div,
        .stSelectbox [data-baseweb="select"] span,
        .stSelectbox [data-baseweb="select"] input,
        .stMultiSelect [data-baseweb="select"] div,
        .stMultiSelect [data-baseweb="select"] span {
            color: var(--text) !important;
            -webkit-text-fill-color: var(--text) !important;
        }
        .stSelectbox [data-baseweb="select"] svg,
        .stMultiSelect [data-baseweb="select"] svg {
            fill: var(--text-soft) !important;
        }
        /* Selected multiselect chips sit on the dark brand colour, so they are
           the one place inside a select that must keep light text. Re-asserted
           here because the rule above would otherwise repaint them dark and
           the chip labels would vanish into their own background. */
        .stMultiSelect [data-baseweb="tag"],
        .stMultiSelect [data-baseweb="tag"] div,
        .stMultiSelect [data-baseweb="tag"] span {
            color: #ffffff !important;
            -webkit-text-fill-color: #ffffff !important;
        }
        .stMultiSelect [data-baseweb="tag"] svg {
            fill: #ffffff !important;
        }

        /* Dropdown menu/options. These render in a body-level portal, so the
           selectors are intentionally global (not scoped under .stApp). */
        div[data-baseweb="popover"],
        div[data-baseweb="popover"] > div,
        div[data-baseweb="popover"] [data-baseweb="menu"],
        [data-baseweb="menu"],
        ul[data-baseweb="menu"],
        ul[role="listbox"],
        [data-testid="stSelectboxVirtualDropdown"],
        [data-testid="stVirtualDropdown"] {
            background: var(--surface) !important;
            color: var(--text) !important;
        }
        [data-baseweb="menu"] li,
        ul[role="listbox"] li,
        [role="option"],
        [data-testid="stSelectboxVirtualDropdown"] li {
            background: var(--surface) !important;
            color: var(--text) !important;
        }
        [data-baseweb="menu"] li *,
        [role="option"] * {
            color: var(--text) !important;
        }
        [data-baseweb="menu"] li:hover,
        [role="option"]:hover,
        [data-baseweb="menu"] li[aria-selected="true"],
        [role="option"][aria-selected="true"] {
            background: var(--surface-3) !important;
            color: var(--text) !important;
        }

        /* Inputs + text areas: keep the typed/shown text dark on light */
        .stTextInput input, .stNumberInput input, .stTextArea textarea,
        .stDateInput input,
        [data-baseweb="input"] input, [data-baseweb="base-input"] input,
        [data-baseweb="textarea"] textarea {
            color: var(--text) !important;
            -webkit-text-fill-color: var(--text) !important;
            background: var(--surface) !important;
        }

        /* Radios / checkboxes labels */
        .stRadio label, .stCheckbox label,
        [data-testid="stWidgetLabel"] { color: var(--text) !important; }

        /* Expander body + tab panels keep light surfaces */
        details[data-testid="stExpander"] div,
        .stTabs [data-baseweb="tab-panel"] { color: var(--text) !important; }

        /* Help tooltips stay dark bubble + white text in either theme */
        div[data-baseweb="tooltip"], div[data-baseweb="tooltip"] * {
            background: #0f172a !important;
            color: #ffffff !important;
        }

        /* Keep alert text readable on their light tinted backgrounds */
        .stAlert, .stAlert p, .stAlert div, .stAlert span { color: var(--text) !important; }

        /* Re-assert hero (dark gradient) text after the broad overrides above.
           Streamlit wraps heading text in an inner <span>, which the broad
           "p, label, span, div" rule above would otherwise paint dark — the
           span selectors below are what keep the title readable. */
        .es-hero h1, .es-hero h1 span { color: #ffffff !important; }
        .es-hero p, .es-hero p span { color: rgba(255, 255, 255, 0.78) !important; }
        .es-hero .es-badge, .es-hero .es-badge span { color: #c4b5fd !important; }
        /* The anchor icon Streamlit appends to headings has no place here */
        .es-hero [data-testid="stHeaderActionElements"] { display: none !important; }
        </style>
        """,
        unsafe_allow_html=True,
    )

@st.cache_resource(show_spinner=False)
def initialize_components() -> Tuple[EbayScraper, FileManager]:
    """Build the scraper and file manager once per app process.

    Cached deliberately: a fresh EbayScraper per rerun threw away the cookie
    jar and re-ran the homepage warm-up on every widget click, and reset the
    consecutive-block counter that drives the adaptive backoff — so the app
    could never learn that eBay was throttling it.
    """
    return EbayScraper(), FileManager()

def display_scraping_results(result: ScrapingResult, downloaded_images: List[str],
                             folder_path: Path, csv_updated: bool) -> None:
    """Render the scraped product as a card plus expandable detail sections."""
    if not result.success or not result.product_data:
        st.error(f"Scraping failed: {result.error_message}")
        return

    product = result.product_data

    def esc(value: Any, fallback: str = "N/A") -> str:
        """Escape a scraped value before it goes into the raw-HTML card.

        Listing titles routinely contain <, > and &, which would otherwise
        break the card layout or inject markup into the page.
        """
        text = str(value or '').strip()
        return html.escape(text) if text else fallback

    main_image_src = html.escape(result.image_urls[0], quote=True) if result.image_urls else ""

    badges = [
        f'<span class="status-badge">Images: {len(downloaded_images)}</span>',
        '<span class="status-badge">CSV: saved</span>' if csv_updated
        else '<span class="status-badge neutral">CSV: not saved</span>',
        f'<span class="status-badge neutral">Folder: {esc(folder_path.name, "-")}</span>',
    ]

    image_html = (
        f'<img src="{main_image_src}" class="product-image" alt="" '
        f'onerror="this.style.display=\'none\'"/>' if main_image_src else ''
    )

    st.markdown(f"""
    <div class="product-card">
        <div class="product-header">
            <h3 class="product-title">{esc(product.title, 'Untitled listing')}</h3>
        </div>
        <div class="product-body">
            <div class="product-image-container">{image_html}</div>
            <div class="product-details">
                <div class="price-tag">{esc(product.price, '-')}</div>
                <div class="detail-row">
                    <span class="detail-label">Condition</span>
                    <span class="detail-value">{esc(product.condition)}</span>
                </div>
                <div class="detail-row">
                    <span class="detail-label">Brand</span>
                    <span class="detail-value">{esc(product.brand)}</span>
                </div>
                <div class="detail-row">
                    <span class="detail-label">Seller</span>
                    <span class="detail-value">{esc(product.seller)}</span>
                </div>
                <div class="detail-row">
                    <span class="detail-label">Shipping</span>
                    <span class="detail-value">{esc(product.shipping)}</span>
                </div>
                <div class="status-section">{''.join(badges)}</div>
            </div>
        </div>
    </div>
    """, unsafe_allow_html=True)

    with st.expander("Description", expanded=False):
        st.markdown(product.description or "*No description available*")

    specifics = {k.strip(): v.strip() for k, v in (product.item_specifics or {}).items()
                 if k.strip() and str(v).strip()}
    if specifics:
        with st.expander(f"Item specifics ({len(specifics)})", expanded=False):
            st.dataframe(
                pd.DataFrame({"Field": list(specifics.keys()), "Value": list(specifics.values())}),
                width='stretch', hide_index=True,
            )

    st.success(f"Saved to `{folder_path}`")


def handle_single_product_scrape(ebay_url: str, scraper: EbayScraper, file_manager: FileManager):
    """
    Orchestrates the single product scraping flow with full edge-case handling.
    """
    # Edge case: empty/whitespace input
    if not ebay_url or not ebay_url.strip():
        st.error("Please paste an eBay product URL before clicking Start scraping.")
        return

    ebay_url = ebay_url.strip()

    # Edge case: pasted with surrounding quotes / angle brackets (common mistake)
    ebay_url = ebay_url.strip('<>"\'')

    # Edge case: pasted multiple URLs separated by whitespace — use the first one
    if any(ws in ebay_url for ws in (' ', '\t', '\n')):
        parts = [p for p in re.split(r'\s+', ebay_url) if p]
        if parts:
            ebay_url = parts[0]
            if len(parts) > 1:
                st.info(f"Detected multiple URLs — using the first one. Use the **Batch Processing** tab for {len(parts)} URLs at once.")

    # 1. Validation with a user-friendly error
    try:
        scraper.validate_ebay_url(ebay_url)
    except ValidationError as e:
        st.error(f"Invalid URL — {e}")
        st.caption("See **Supported URL formats** above for examples.")
        return

    # 2. Operations
    progress_bar = st.progress(0)
    status_msg = st.empty()

    def log_single(status: str, details: str = '', product: Optional[ProductData] = None,
                   folder: str = '', images: int = 0) -> None:
        """Record this scrape in the shared history file.

        Single scrapes are tagged 'single' so they show up in the history
        table without being treated as batch entries for duplicate checks —
        the folder naming is different, so they are not interchangeable.
        """
        append_batch_status({
            'Source': 'single', 'Link': ebay_url, 'Status': status, 'Details': details,
            'Item ID': getattr(product, 'item_id', '') or '',
            'Brand': getattr(product, 'brand', '') or '',
            'Title': getattr(product, 'title', '') or '',
            'Price': getattr(product, 'price', '') or '',
            'Condition': getattr(product, 'condition', '') or '',
            'Folder': folder, 'Images': str(images),
        })

    try:
        status_msg.caption("Extracting product data...")
        progress_bar.progress(10)

        result = scraper.scrape_product(ebay_url)

        if not result.success:
            progress_bar.empty()
            status_msg.empty()
            st.error(result.error_message or "Scraping failed.")
            log_single(STATUS_ERROR, result.error_message or 'Unknown error')
            return

        progress_bar.progress(40)
        status_msg.caption("Saving product files...")

        folder_path = file_manager.create_product_folder(
            brand=result.product_data.brand,
            item_id=result.product_data.item_id,
            fallback_title=result.product_data.title,
        )
        result.folder_path = str(folder_path)

        file_manager.save_product_description_markdown(result.product_data, folder_path)
        file_manager.save_product_text(result.product_data, folder_path)
        file_manager.save_raw_scrape_text(result.product_data, folder_path)

        progress_bar.progress(60)
        downloaded_images: List[str] = []
        if result.image_urls:
            status_msg.caption(f"Downloading {len(result.image_urls)} image(s)...")
            try:
                downloaded_images = file_manager.download_images(
                    scraper, result.image_urls, folder_path,
                    progress_callback=lambda c, t: progress_bar.progress(60 + int((c / t) * 20)),
                )
            except Exception as img_err:
                # The product data is already on disk; images are best-effort.
                logger.warning(f"Image download failed for {ebay_url}: {img_err}")
                st.warning("The listing was saved but its images could not be downloaded.")

        progress_bar.progress(90)
        csv_updated = append_to_local_csv(result.product_data)
        log_single(STATUS_DONE, product=result.product_data,
                   folder=str(folder_path), images=len(downloaded_images))
        bump_data_version()

        progress_bar.empty()
        status_msg.empty()
        display_scraping_results(result, downloaded_images, folder_path, csv_updated)

    except PermissionError as e:
        progress_bar.empty()
        status_msg.empty()
        logger.error(f"Scrape handler permission error: {e}")
        st.error(f"A file could not be written — it may be open in another program: {e}")
        log_single(STATUS_ERROR, f"Permission denied: {e}")
    except OSError as e:
        progress_bar.empty()
        status_msg.empty()
        logger.error(f"Scrape handler OS error: {traceback.format_exc()}")
        st.error(f"Could not save the scraped files: {e}")
        log_single(STATUS_ERROR, str(e))
    except Exception as e:
        progress_bar.empty()
        status_msg.empty()
        logger.error(f"Scrape handler error: {traceback.format_exc()}")
        st.error(f"An unexpected error occurred: {e}")
        log_single(STATUS_ERROR, str(e))



TAB_NAMES = [
    "Single Product",
    "Batch Processing",
    "AI Processing",
    "Image Enhancement",
    "Image Format",
    "Logs",
]


def render_sidebar() -> AISettings:
    """Brand block plus configuration. Returns the AI settings to use."""
    with st.sidebar:
        st.markdown(
            """
            <div class="es-side-brand">
                <div class="es-logo">eS</div>
                <div>
                    <div class="es-side-title">eBay Studio</div>
                    <div class="es-side-sub">Scraper · AI · Images</div>
                </div>
            </div>
            """,
            unsafe_allow_html=True,
        )
        st.markdown('<div class="es-side-section">Configuration</div>', unsafe_allow_html=True)

        saved_provider, saved_models = load_ai_preferences()
        provider_keys = list(AI_PROVIDERS)
        selected_key = st.selectbox(
            "AI provider",
            options=provider_keys,
            index=provider_keys.index(saved_provider) if saved_provider in provider_keys else 0,
            format_func=lambda k: AI_PROVIDERS[k].label,
            help="Which service runs the AI features. Each keeps its own key.",
        )
        provider = get_provider(selected_key)

        # Each provider gets its own key field, seeded from secrets, the
        # environment or the saved config — switching provider never shows
        # another provider's key.
        #
        # Session state is seeded once per widget rather than passing `value=`
        # alongside `key=`. Streamlit drops the state of widgets that a run
        # did not render, and mixing the two meant that after switching away
        # and back the field came up blank even though the key was safely on
        # disk. Seeding on absence re-reads storage in exactly that case.
        stored_key = load_api_key(provider)
        key_state = f"api_key_{provider.key}"
        if key_state not in st.session_state:
            st.session_state[key_state] = stored_key
        api_key = st.text_input(
            provider.key_label, type="password", key=key_state,
            help=f"Create one at {provider.console_url}",
        ).strip()

        remember_state = f"remember_{provider.key}"
        if remember_state not in st.session_state:
            st.session_state[remember_state] = bool(stored_key)
        if st.checkbox("Remember this key", key=remember_state,
                       help=f"Saves it to {AI_CONFIG_PATH.name} (owner-only permissions, gitignored)."):
            if api_key and api_key != stored_key and not save_api_key(provider, api_key):
                st.warning("The key could not be saved to disk.")
        elif stored_key:
            # Unticking is an explicit instruction to stop storing this key.
            forget_api_key(provider)

        model_state = f"model_{provider.key}"
        if model_state not in st.session_state:
            st.session_state[model_state] = saved_models.get(provider.key, provider.default_model)
        model = st.text_input("Model", key=model_state, help=provider.model_hint).strip()

        settings = AISettings(provider=provider, api_key=api_key, model=model)

        if provider.key_prefix and api_key and not api_key.startswith(provider.key_prefix):
            st.caption(f"That does not look like a {provider.label} key "
                       f"(they usually start with `{provider.key_prefix}`).")

        if st.button("Load available models", width='stretch', disabled=not settings.ready,
                     help="Asks the provider which models it currently serves."):
            try:
                with st.spinner("Asking the provider..."):
                    st.session_state.provider_models = list_provider_models(settings)
                st.session_state.provider_models_for = provider.key
            except AIServiceError as e:
                st.session_state.provider_models = []
                st.warning(str(e))

        if (st.session_state.get('provider_models')
                and st.session_state.get('provider_models_for') == provider.key):
            available = st.session_state.provider_models
            with st.expander(f"{len(available)} models available", expanded=False):
                picked = st.selectbox("Pick one", options=available,
                                      index=available.index(model) if model in available else 0,
                                      key=f"pick_model_{provider.key}")
                if st.button("Use this model", width='stretch'):
                    st.session_state[model_state] = picked
                    save_ai_preferences(provider.key, picked)
                    st.rerun()

        # Remember the provider and model (never the key) so the next start
        # opens on the same setup.
        if selected_key != saved_provider or model != saved_models.get(provider.key, ''):
            save_ai_preferences(selected_key, model)

        st.caption(f"AI features enabled — {provider.label}." if settings.ready
                   else f"AI features need a {provider.key_label}.")

        st.markdown('<div class="es-side-section">Scraping</div>', unsafe_allow_html=True)
        if CURL_CFFI_AVAILABLE:
            st.caption("Browser TLS fingerprint active (curl_cffi).")
        else:
            st.caption("Basic TLS (requests). `pip install curl_cffi` to look like a real "
                       "browser and get blocked far less often.")

        st.markdown('<div class="es-side-section">Files</div>', unsafe_allow_html=True)
        st.caption(f"Products: `EbayStore_Products.csv`\n\nHistory: `{BATCH_STATUS_LOG.name}`")

    return settings


def main():
    """Main Streamlit application."""
    st.set_page_config(
        page_title="eBay Scraper Studio",
        layout="wide",
        initial_sidebar_state="expanded",
    )
    inject_global_styles()

    st.markdown(
        """
        <div class="es-hero">
            <div class="es-badge">v3.3 · Multi-platform</div>
            <h1>eBay Scraper Studio</h1>
            <p>Extract listings, enhance images and generate platform-tuned descriptions.</p>
        </div>
        """,
        unsafe_allow_html=True,
    )

    try:
        scraper, file_manager = initialize_components()
    except Exception as e:
        logger.critical(f"Initialization failed: {traceback.format_exc()}")
        st.error(f"The application could not start: {e}")
        return

    ai_settings = render_sidebar()

    tab1, tab2, tab3, tab4, tab_fmt, tab5 = st.tabs(TAB_NAMES)

    # Tab 1: Single Product Scraping
    with tab1:
        st.markdown(
            """
            <div class="es-card">
                <div class="es-card-title">Find a product</div>
                <p class="es-card-sub">Paste any eBay listing URL. Regional domains, short links and tracking parameters are handled automatically.</p>
            </div>
            """,
            unsafe_allow_html=True,
        )

        col_search, col_button = st.columns([4, 1])
        ebay_url = col_search.text_input(
            "eBay product URL",
            placeholder="https://www.ebay.com/itm/1234567890",
            label_visibility="collapsed",
            key="single_url_input",
        )
        scrape_button = col_button.button(
            "Scrape", type="primary", width='stretch', key="single_scrape_btn",
        )

        if scrape_button:
            handle_single_product_scrape(ebay_url, scraper, file_manager)

        with st.expander("Supported URL formats", expanded=False):
            st.markdown(
                """
- Item URLs, with or without a slug — `ebay.com/itm/1234567890`
- Regional domains — `.com`, `.co.uk`, `.de`, `.fr`, `.it`, `.es`, `.com.au`, `.ca`, `.ie`, `.nl`, `.pl`, `.com.hk`, `.com.sg`, `.co.jp`
- Short links — `ebay.to/abc123`
- Product pages — `ebay.com/p/12345678`
- Mobile URLs and links carrying tracking parameters
                """
            )

    # Tab 2: Batch Processing
    with tab2:
        render_batch_tab(scraper, file_manager)

    # Tab 3: AI Processing
    with tab3:
        render_ai_tab(ai_settings, file_manager)

    # Tab 4: Image Enhancement
    with tab4:
        render_image_enhancement_tab(file_manager)

    # Tab: Image Format (WebP conversion)
    with tab_fmt:
        render_image_format_tab(file_manager)

    # Tab 5: Logs
    with tab5:
        render_logs_tab()

    render_footer()


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        st.error(f"Application error: {e}")
        logger.critical(f"Application startup error: {traceback.format_exc()}")
        with st.expander("Technical details"):
            st.code(traceback.format_exc(), language="text")