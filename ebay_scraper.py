"""
eBay Product Scraper with AI Processing
======================================

A production-ready eBay product scraper with integrated AI processing capabilities.
Features include:
- Robust eBay product data extraction
- Concurrent image downloading with optimization
- Google Sheets integration
- AI-powered content enhancement with Groq
- Batch processing capabilities
- Comprehensive error handling and logging
- Modern UI with performance optimizations

Author: Production Development Team
Version: 3.1
"""

import streamlit as st
import requests
from bs4 import BeautifulSoup, Tag
import os
import re
from io import StringIO
import pandas as pd
import time
import random
from urllib.parse import urljoin, urlparse
from pathlib import Path
import json
from datetime import datetime
from typing import Dict, List, Tuple, Optional, Any
import logging
import gspread
from google.oauth2.service_account import Credentials
import csv
from groq import Groq
from dataclasses import dataclass, asdict
import traceback
from PIL import Image, ImageEnhance, ImageDraw, ImageFont
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import lru_cache
import hashlib
import shelve
import shutil
import concurrent.futures
import threading
from typing import Callable
from time import sleep

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

# Disable urllib3 warnings about unverified connections (if needed)
import urllib3
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# Configure requests to not use proxy
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

class NoProxyHTTPAdapter(HTTPAdapter):
    """HTTPAdapter that bypasses all proxies."""
    def proxy_manager_for(self, proxy, **kwargs):
        return super().proxy_manager_for(None, **kwargs)

# =============================================================================
# CACHING AND AGENTS
# =============================================================================

# Browser-like headers to avoid anti-bot detection
REQUEST_HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
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
        
        # Platform knowledge base
        self.platforms = {
            "leboncoin": {
                "name": "Leboncoin",
                "language": "French",
                "style": "Casual, direct, local-focused",
                "key_features": ["Price visibility", "Local pickup options", "Honest condition description"],
                "title_length": 50,
                "description_style": "Short paragraphs, clear bullet points"
            },
            "vinted": {
                "name": "Vinted",
                "language": "English/French",
                "style": "Friendly, fashion-forward, community-oriented",
                "key_features": ["Size/fit details", "Brand emphasis", "Styling suggestions"],
                "title_length": 60,
                "description_style": "Conversational, includes measurements and styling tips"
            },
            "vestiaire collective": {
                "name": "Vestiaire Collective",
                "language": "English/French",
                "style": "Luxury, professional, authentication-focused",
                "key_features": ["Authenticity proof", "Precise measurements", "Condition grading"],
                "title_length": 100,
                "description_style": "Detailed, professional, includes provenance"
            },
            "general": {
                "name": "General Marketplace",
                "language": "English",
                "style": "Professional, clear, informative",
                "key_features": ["Complete specs", "Clear photos", "Honest description"],
                "title_length": 80,
                "description_style": "Structured with clear sections"
            }
        }
    
    def research_platform(self, platform_name: str) -> Dict:
        """Get platform-specific requirements and best practices."""
        normalized = platform_name.lower().replace(" ", "_")
        return self.platforms.get(normalized, self.platforms["general"])
    
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
            
            prompt = f"""
You are an expert product listing writer for {platform_info['name']}.

TASK: Create a clean, professional product description optimized for {platform_info['name']}.

INPUT DATA:
Title: {title}
Brand: {brand}
Condition: {condition}
Specifications: {json.dumps(specs, ensure_ascii=False)}

RAW TEXT (may contain noise - extract only relevant product information):
{raw_text}

PLATFORM REQUIREMENTS:
- Language: {platform_info['language']}
- Style: {platform_info['style']}
- Title length: ~{platform_info['title_length']} characters
- Description style: {platform_info['description_style']}
- Key features to highlight: {', '.join(platform_info['key_features'])}

{f"CUSTOM INSTRUCTIONS: {custom_instructions}" if custom_instructions else ""}

RULES:
1. **NO raw data headers** - Don't include "Product Information", "Title:", "Price:", etc.
2. **Clean title only** - Write a compelling SEO-optimized title
3. **Structured description** - Use clear sections with headings
4. **Remove noise** - No seller info, shipping banners, similar items, ads
5. **Factual only** - Don't invent details not in the source
6. **Proper formatting** - Use line breaks and bullet points for readability
7. **Include measurements** - Keep exact dimensions, sizes, materials
8. **Condition details** - Be honest about any flaws or wear
9. **Platform tone** - Match the platform's typical listing style

OUTPUT FORMAT (plain text, no markdown):
[Write an optimized title on first line]

[Blank line]

[Well-structured description with clear sections]

IMPORTANT: Start directly with the title. No headers like "Product Information" or field labels.
"""
            
            # Check cache first
            cache_key = f"{platform}_{title}_{hash(raw_text[:500])}"
            cached = self.cache.get(cache_key)
            if cached:
                logger.debug("Using cached platform description")
                return cached
            
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                temperature=0.6,
                max_tokens=2000
            )
            result_text = response.choices[0].message.content.strip() if response.choices[0].message.content else ""
            
            # Cache the result
            self.cache.set(cache_key, result_text)
            
            return result_text
            
        except Exception as e:
            logger.error(f"Error generating platform description: {e}")
            return ""

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

# =============================================================================
# UTILITY FUNCTIONS
# =============================================================================

def safe_request(session: requests.Session, url: str, timeout: int = 30, max_retries: int = 3) -> Optional[requests.Response]:
    """
    Make a safe HTTP request with exponential backoff retry logic.
    """
    for attempt in range(max_retries):
        try:
            response = session.get(url, timeout=timeout)
            response.raise_for_status()
            return response
        except requests.exceptions.HTTPError as e:
            status = e.response.status_code if e.response else 0
            if status in [404, 410]: # Not found, don't retry
                 logger.error(f"Page not found: {url}")
                 return None
            if status == 429: # Rate limit
                wait_time = (2 ** attempt) + random.uniform(1, 3)
                logger.warning(f"Rate limited. Waiting {wait_time:.2f}s...")
                time.sleep(wait_time)
                continue
            logger.warning(f"HTTP error {e} on attempt {attempt + 1}")
        except requests.RequestException as e:
            logger.warning(f"Request failed: {e}. Attempt {attempt + 1}/{max_retries}")
        
        # Exponential backoff
        if attempt < max_retries - 1:
            sleep_time = (2 ** attempt) + random.uniform(0.5, 1.5)
            time.sleep(sleep_time)
            
    logger.error(f"Failed to fetch {url} after {max_retries} attempts")
    return None

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
    
    def __init__(self):
        """Initialize the scraper with configured session."""
        self.session = requests.Session()
        # Configure session to bypass proxies
        self.session.mount('http://', NoProxyHTTPAdapter())
        self.session.mount('https://', NoProxyHTTPAdapter())
        self.session.proxies = {}
        self.session.headers.update(REQUEST_HEADERS)
        logger.info("eBay scraper initialized")
    
    def validate_ebay_url(self, url: str) -> bool:
        """
        Validate if the URL is a valid eBay product URL.
        
        Args:
            url: URL to validate
            
        Returns:
            True if URL is valid eBay product URL
            
        Raises:
            ValidationError: If URL format is invalid
        """
        try:
            if not url or not isinstance(url, str):
                raise ValidationError("URL must be a non-empty string")
            
            parsed = urlparse(url.strip())
            netloc = parsed.netloc.lower()
            
            # Check for eBay domain (supports regional domains)
            if 'ebay.' not in netloc:
                raise ValidationError("URL must be from an eBay domain")
            
            # Check for item URL pattern
            if '/itm/' not in url:
                raise ValidationError("URL must be an eBay item URL (contains /itm/)")
            
            return True
            
        except ValidationError:
            raise
        except Exception as e:
            raise ValidationError(f"Invalid URL format: {e}")
    
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
            
            # Extract condition
            condition_selectors = [
                '[data-testid="u-flL condText"] span',
                '.x-item-condition-text',
                '[data-testid="x-item-condition"] span',
                '#vi-itm-cond',
                '.vi-itm-cond',
                '.d-item-condition',
                '.ux-textspans--BOLD[class*="cond"]'
            ]
            
            product_data.condition = self._extract_text_by_selectors(soup, condition_selectors, "condition")
            
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
            shipping_selectors = [
                '[data-testid="vi-price-ship"]',
                '#fshippingCost',
                '#shSummary'
            ]
            
            product_data.shipping = self._extract_text_by_selectors(soup, shipping_selectors, "shipping")
            
            # Extract brand and item specifics
            product_data.item_specifics = self._extract_item_specifics(soup)
            product_data.brand = product_data.item_specifics.get('Brand', '')
            
            # Extract description (including iframe content)
            product_data.description = self._extract_description(soup, url)

            # Additional fields for richer AI prompts
            product_data.location = self._extract_text_by_selectors(soup, [
                '#itemLocation', '.item-location', '[data-testid="ux-seller-location"]',
                '.ux-seller-section__itemLocation'] , "location")
            product_data.returns_policy = self._extract_text_by_selectors(soup, [
                '#vi-ret-accrd-txt', '.x-ret-accrd-txt', '.returns-policy'] , "returns")
            product_data.category = self._extract_text_by_selectors(soup, [
                '#vi-VR-brumb-lnkLst', '.bc-w', 'nav[aria-label="Breadcrumbs"]'] , "category")
            # Try to parse item id from URL or page
            product_data.item_id = self.extract_id_from_url(url)
            
            # Fallback: Extract from DOM if not found in URL
            if not product_data.item_id:
                product_data.item_id = self._extract_id_from_dom(soup)
                
            logger.info(f"Successfully extracted product data for: {product_data.title[:50]}... (ID: {product_data.item_id})")
            return product_data
        
        except Exception as e:
            logger.error(f"Error extracting product data: {e}")
            raise DataExtractionError(f"Failed to extract product data: {e}")

    def extract_id_from_url(self, url: str) -> Optional[str]:
        """Extract eBay Item ID from URL."""
        try:
            parsed = urlparse(url)
            # Standard /itm/ID format
            if '/itm/' in parsed.path:
                parts = parsed.path.split('/')
                for p in reversed(parts):
                    if p.isdigit():
                        return p
            
            # Query parameter format
            query = parse_qs(parsed.query)
            if 'itm' in query:
                return query['itm'][0]
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
        
        logger.warning(f"No {field_name} found using any selector")
        return ""
    
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
        
        logger.warning("No price found using any method")
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
                            
                            response = safe_request(self.session, iframe_url, timeout=15)
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
            response = safe_request(self.session, img_url, timeout=30)
            if not response:
                return None
            
            # Determine file extension from content type or URL
            content_type = response.headers.get('Content-Type', '').lower()
            extension = self._get_image_extension(content_type, img_url)
            
            final_path = f"{save_path}.{extension}"
            
            with open(final_path, 'wb') as f:
                f.write(response.content)
            
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
    
    def scrape_product(self, url: str) -> ScrapingResult:
        """
        Main scraping method that orchestrates the entire process.
        Returns ScrapingResult with success/failure and detailed error messages.
        """
        try:
            # Validate URL
            self.validate_ebay_url(url)
            
            # Add anti-detection delay
            time.sleep(random.uniform(0.5, 2.0))
            
            # Fetch page
            response = safe_request(self.session, url, timeout=30)
            if not response:
                return ScrapingResult(
                    success=False, 
                    error_message="Could not connect to eBay. Please check:\n• Your internet connection is stable\n• The eBay listing still exists\n• Wait 1-2 minutes if you've made many requests"
                )
            
            # Check for eBay error pages
            if response.status_code == 404:
                return ScrapingResult(
                    success=False,
                    error_message="This eBay listing was not found. It may have been sold, removed, or the URL is incorrect."
                )
            
            # Parse HTML
            soup = BeautifulSoup(response.content, 'html.parser')
            
            # Check for blocked/captcha pages
            page_text = soup.get_text().lower()
            if 'captcha' in page_text or 'robot' in page_text:
                return ScrapingResult(
                    success=False,
                    error_message="eBay is requesting verification. Please wait a few minutes and try again."
                )
            
            # Extract data
            product_data = self.extract_product_data(soup, url)
            image_urls = self.get_product_images(soup, url)
            
            # Validate we got essential data
            if not product_data.title:
                return ScrapingResult(
                    success=False,
                    error_message="Could not extract product title. The listing format may not be supported."
                )
            
            return ScrapingResult(
                success=True,
                product_data=product_data,
                image_urls=image_urls
            )
            
        except ValidationError as e:
            return ScrapingResult(success=False, error_message=f"Invalid URL: {e}. Please use a valid eBay product URL.")
        except NetworkError as e:
            return ScrapingResult(success=False, error_message=f"Network error: {e}. Check your internet connection.")
        except DataExtractionError as e:
            return ScrapingResult(success=False, error_message=f"Could not extract product data: {e}")
        except Exception as e:
            logger.error(f"Unexpected error in scrape_product: {traceback.format_exc()}")
            return ScrapingResult(success=False, error_message=f"An unexpected error occurred. Please try again.")

# =============================================================================
# GOOGLE SHEETS INTEGRATION
# =============================================================================

class GoogleSheetsManager:
    """
    Manages Google Sheets operations with robust error handling.
    
    Handles:
    - Service account authentication
    - Spreadsheet and worksheet management
    - Data insertion and updates
    - Batch processing operations
    """
    
    def __init__(self, service_account_info: Optional[Dict] = None):
        """Initialize with service account credentials."""
        self.client = self._init_client(service_account_info)
        self.config_path = Path.cwd() / '.gsheet_config.json'
        self.quota_exceeded: bool = False
    
    def _init_client(self, service_account_info: Optional[Dict]) -> Optional[gspread.Client]:
        """Initialize Google Sheets client with error handling."""
        try:
            if not service_account_info:
                logger.warning("No service account info provided")
                return None
            
            if isinstance(service_account_info, str):
                service_account_info = json.loads(service_account_info)
            
            scopes = [
                'https://www.googleapis.com/auth/spreadsheets',
                'https://www.googleapis.com/auth/drive'
            ]
            
            # Configure credentials to bypass proxy
            # Environment variables set at module level should handle proxy bypass
            credentials = Credentials.from_service_account_info(
                service_account_info, 
                scopes=scopes
            )
            
            # Create client - proxy bypass is handled by environment variables
            client = gspread.authorize(credentials)
            
            logger.info("Google Sheets client initialized successfully")
            return client
            
        except Exception as e:
            logger.error(f"Failed to initialize Google Sheets client: {e}")
            return None
    
    def is_available(self) -> bool:
        """Check if Google Sheets client is available."""
        return self.client is not None
    
    def ensure_spreadsheet_and_worksheet(self, title: str = 'EbayStore_Products', 
                                       worksheet_name: str = 'Products',
                                       share_email: Optional[str] = None,
                                       allow_create: bool = True) -> Tuple[Optional[Any], Optional[Any]]:
        """
        Ensure spreadsheet and worksheet exist, creating if necessary.
        
        Args:
            title: Spreadsheet title
            worksheet_name: Worksheet name
            share_email: Email to share spreadsheet with
            
        Returns:
            Tuple of (spreadsheet, worksheet) objects
        """
        if not self.client:
            return None, None
        
        try:
            spreadsheet = None
            
            # Try to open by an explicit Sheet ID from env/secrets/config
            if self.config_path.exists():
                try:
                    config = json.load(open(self.config_path, 'r', encoding='utf-8'))
                    sheet_id = config.get('sheet_id')
                    if sheet_id:
                        spreadsheet = self.client.open_by_key(sheet_id)
                        logger.debug(f"Opened existing spreadsheet: {sheet_id}")
                except Exception:
                    logger.debug("Failed to open spreadsheet from config")
            if not spreadsheet:
                # Environment/config override
                try:
                    import streamlit as _st
                    if hasattr(_st, 'secrets') and 'sheet_id' in _st.secrets:
                        secret_id = str(_st.secrets['sheet_id']).strip()
                    else:
                        secret_id = ''
                except Exception:
                    secret_id = ''
                env_id = os.getenv('EBAY_SHEET_ID', '').strip()
                sheet_id = secret_id or env_id or DEFAULT_SHEET_ID
                if sheet_id:
                    try:
                        spreadsheet = self.client.open_by_key(sheet_id)
                        logger.debug(f"Opened spreadsheet by provided sheet_id: {sheet_id}")
                    except Exception:
                        logger.debug("Failed to open spreadsheet by provided sheet_id")
            
            # Try to open by title
            if not spreadsheet:
                try:
                    spreadsheet = self.client.open(title)
                    logger.debug(f"Opened spreadsheet by title: {title}")
                except Exception:
                    logger.debug(f"Spreadsheet '{title}' not found")
            
            # Try known alternative titles
            if not spreadsheet:
                for alt_title in SHEET_TITLES_TO_TRY:
                    try:
                        spreadsheet = self.client.open(alt_title)
                        logger.debug(f"Opened spreadsheet by alternative title: {alt_title}")
                        break
                    except Exception:
                        continue
            
            # Create new spreadsheet
            if not spreadsheet:
                if not allow_create:
                    logger.debug("Creation disabled; returning without spreadsheet.")
                    return None, None
                try:
                    spreadsheet = self.client.create(title)
                    logger.info(f"Created new spreadsheet: {title}")
                except Exception as e:
                    # Detect Drive quota exceeded and set flag for graceful fallback
                    err_text = str(e).lower()
                    if ("quota" in err_text and "exceeded" in err_text) or ("403" in err_text and "quota" in err_text):
                        self.quota_exceeded = True
                        logger.error("Drive storage quota exceeded. Falling back to CSV only.")
                        return None, None
                    logger.error(f"Could not create spreadsheet: {e}")
                    return None, None
                
                # Save config
                try:
                    config = {'sheet_id': spreadsheet.id, 'worksheet_name': worksheet_name}
                    json.dump(config, open(self.config_path, 'w', encoding='utf-8'))
                except Exception as e:
                    logger.warning(f"Could not save spreadsheet config: {e}")
            
            # Ensure worksheet exists
            try:
                worksheet = spreadsheet.worksheet(worksheet_name)
                logger.debug(f"Found existing worksheet: {worksheet_name}")
            except gspread.WorksheetNotFound:
                # Try several common worksheet names
                worksheet = None
                for guess in WORKSHEET_NAMES_TO_TRY:
                    try:
                        worksheet = spreadsheet.worksheet(guess)
                        logger.info(f"Using worksheet by alternative name: {guess}")
                        break
                    except Exception:
                        continue
                # Fallback to first worksheet if present
                if not worksheet:
                    try:
                        worksheets = spreadsheet.worksheets()
                        if worksheets:
                            worksheet = worksheets[DEFAULT_WORKSHEET_INDEX]
                            logger.info(f"Using fallback worksheet: {worksheet.title}")
                    except Exception:
                        pass
                # Create if still none
                if not worksheet:
                    worksheet = spreadsheet.add_worksheet(title=worksheet_name, rows=1000, cols=20)
                    logger.info(f"Created new worksheet: {worksheet_name}")
            
            # Ensure header row
            self._ensure_header(worksheet)
            
            # Share if email provided
            if share_email:
                try:
                    spreadsheet.share(share_email, perm_type='user', role='writer', notify=False)
                    logger.info(f"Shared spreadsheet with: {share_email}")
                except Exception as e:
                    logger.warning(f"Could not share spreadsheet: {e}")
            
            # Success – clear any previous quota flag and return
            self.quota_exceeded = False
            # Success – clear any previous quota flag and return
            self.quota_exceeded = False
            return spreadsheet, worksheet
            
        except Exception as e:
            err_text = str(e).lower()
            if ("quota" in err_text and "exceeded" in err_text) or ("403" in err_text and "quota" in err_text):
                self.quota_exceeded = True
                logger.error("Error ensuring spreadsheet/worksheet: Drive storage quota exceeded. Using CSV fallback.")
            else:
                logger.error(f"Error ensuring spreadsheet/worksheet: {e}")
            return None, None
    
    def _ensure_header(self, worksheet) -> None:
        """Ensure worksheet has proper header row."""
        try:
            existing = worksheet.get_all_values()
            if not existing:
                header = [
                    'Scraped At', 'eBay URL', 'Title', 'Price', 'Condition', 
                    'Brand', 'Seller', 'Shipping', 'Description', 'Item Specifics'
                ]
                worksheet.append_row(header)
                logger.debug("Added header row to worksheet")
        except Exception as e:
            logger.warning(f"Could not ensure header: {e}")
    
    def append_product_data(self, product_data: ProductData, share_email: Optional[str] = None) -> bool:
        """
        Append product data to auto-managed Google Sheet.
        
        Args:
            product_data: ProductData object to append
            share_email: Optional email to share sheet with
            
        Returns:
            True if successful, False otherwise
        """
        try:
            # Open only existing sheet; do not create
            spreadsheet, worksheet = self.ensure_spreadsheet_and_worksheet(share_email=share_email, allow_create=False)
            if not worksheet:
                return False
            
            # Prepare row data
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
                (product_data.description or '')[:1000],  # Limit description length
                item_specifics_str,
            ]
            
            worksheet.append_row(row)
            logger.info("Successfully appended product data to Google Sheet")
            return True
            
        except Exception as e:
            logger.error(f"Error appending to Google Sheet: {e}")
            return False

    def append_to_ebay_product_list(self, product_data: ProductData) -> bool:
        """Upsert into user's 'ebay_Product_List' worksheet; update row if URL exists, else append.

        Expected columns (order can vary):
        eBay_URL, Status, Title, Selling Price, Condition, % margin, Listing Platform, Date of listing, brand, Notes
        """
        if not self.client:
            return False
        try:
            _, worksheet = self.ensure_spreadsheet_and_worksheet(
                title='ebay_Product_List',
                worksheet_name='ebay_Product_List',
                allow_create=False
            )
            if not worksheet:
                return False

            values = worksheet.get_all_values()
            header = values[0] if values else []
            if not header:
                header = ['Item ID', 'eBay_URL', 'Status', 'Title', 'Selling Price', 'Condition', '% margin', 'Listing Platform', 'Date of listing', 'brand', 'Notes']
                worksheet.append_row(header)

            header_map = self._get_header_map(worksheet)

            def val(col_name: str) -> str:
                name = col_name.strip().lower()
                if name in ('item id', 'id', 'ebay item number', 'ebay id'):
                     return product_data.item_id
                if name in ('ebay_url', 'ebay url', 'url', 'link'):
                    return product_data.url
                if name == 'status':
                    return 'done'
                if name == 'title':
                    return product_data.title
                if name in ('selling price', 'price'):
                    return product_data.price
                if name == 'condition':
                    return product_data.condition
                if name in ('% margin', 'margin', 'profit %'):
                    return ''
                if name in ('listing platform', 'platform'):
                    return 'eBay'
                if name in ('date of listing', 'date'):
                    return datetime.now().strftime('%Y-%m-%d')
                if name == 'brand':
                    return product_data.brand
                if name in ('seller', 'seller name'):
                    return product_data.seller
                if name == 'shipping':
                    return product_data.shipping
                if name in ('description', 'desc'):
                    return (product_data.description or '')[:1000]
                if name in ('item specifics', 'item_specifics', 'specifics'):
                    return " | ".join([f"{k}: {v}" for k, v in product_data.item_specifics.items()])
                if name == 'notes':
                    # Fallback: brief description snippet if no dedicated column exists
                    snippet = (product_data.description or '')[:140]
                    return snippet
                return ''

            new_row = [val(c) for c in header]

            # Upsert by URL
            row_index = self._find_row_by_url(worksheet, product_data.url)
            if row_index:
                start_col = 1
                end_col = len(header)
                a1 = gspread.utils.rowcol_to_a1(row_index, start_col) + ':' + gspread.utils.rowcol_to_a1(row_index, end_col)
                worksheet.update(a1, [new_row])
                logger.info("Updated existing row in 'ebay_Product_List'")
                return True
            else:
                worksheet.append_row(new_row)
                logger.info("Appended new row to 'ebay_Product_List'")
                return True
        except Exception as e:
            logger.warning(f"Could not upsert to 'ebay_Product_List': {e}")
            return False

    # ---------- Utilities for duplicates and status updates ----------
    @staticmethod
    def _normalize_key(name: str) -> str:
        return re.sub(r"[^a-z0-9]", "", name.lower())

    def _get_header_map(self, worksheet) -> Dict[str, int]:
        try:
            values = worksheet.get_all_values()
            header = values[0] if values else []
            mapping: Dict[str, int] = {}
            for idx, col in enumerate(header):
                mapping[self._normalize_key(col)] = idx
            return mapping
        except Exception:
            return {}

    def _find_row_by_url(self, worksheet, url: str) -> Optional[int]:
        try:
            values = worksheet.get_all_values()
            if not values:
                return None
            header = values[0]
            header_map = self._get_header_map(worksheet)
            # Try common keys for URL
            for key in ["ebayurl", "ebay_url", "url", "link", "ebayitemurl"]:
                if key in header_map:
                    url_idx = header_map[key]
                    break
            else:
                # try to guess by 'http' presence in first data row
                url_idx = None
                if len(values) > 1:
                    for idx, col in enumerate(values[1]):
                        if col.startswith("http"):
                            url_idx = idx
                            break
                if url_idx is None:
                    return None
            # Search rows
            for i, row in enumerate(values[1:], start=2):  # 1-based in Sheets, header is row 1
                if len(row) > url_idx and row[url_idx].strip() == url.strip():
                    return i
            return None
        except Exception:
            return None

    def url_exists(self, url: str) -> bool:
        if not self.client:
            return False
        try:
            # Only check ebay_Product_List style sheet
            _, ws2 = self.ensure_spreadsheet_and_worksheet(title='ebay_Product_List', worksheet_name='ebay_Product_List', allow_create=False)
            if ws2 and self._find_row_by_url(ws2, url):
                return True
        except Exception:
            return False
        return False

    def update_status_by_url(self, url: str, status: str = "Done") -> bool:
        if not self.client:
            return False
        try:
            _, worksheet = self.ensure_spreadsheet_and_worksheet(title='ebay_Product_List', worksheet_name='ebay_Product_List', allow_create=False)
            if not worksheet:
                return False
            row_index = self._find_row_by_url(worksheet, url)
            if not row_index:
                return False
            header_map = self._get_header_map(worksheet)
            status_idx = header_map.get("status")
            if status_idx is None:
                return False
            # gspread cells are 1-based
            worksheet.update_cell(row_index, status_idx + 1, status)
            logger.info(f"Updated status to '{status}' for URL in 'ebay_Product_List'")
            return True
        except Exception as e:
            logger.warning(f"Failed to update status: {e}")
            return False

    def ensure_columns(self, worksheet, required_columns: List[str]) -> Dict[str, int]:
        """
        Ensure required columns exist in the worksheet header. Add missing ones.
        
        Args:
            worksheet: gspread worksheet object
            required_columns: List of column names to ensure exist
            
        Returns:
            Dict mapping column name (normalized) to column index
        """
        try:
            values = worksheet.get_all_values()
            header = values[0] if values else []
            header_map = {self._normalize_key(col): i for i, col in enumerate(header)}
            
            # Find missing columns
            missing = []
            for col in required_columns:
                if self._normalize_key(col) not in header_map:
                    missing.append(col)
            
            # Add missing columns to header
            if missing:
                new_header = header + missing
                worksheet.update('1:1', [new_header])
                # Rebuild header map
                header_map = {self._normalize_key(col): i for i, col in enumerate(new_header)}
                logger.info(f"Added missing columns to sheet: {missing}")
            
            return header_map
        except Exception as e:
            logger.error(f"Error ensuring columns: {e}")
            return {}

    def update_row_with_product_data(self, url: str, product_data: ProductData) -> bool:
        """
        Update an existing row (identified by URL) with all product data.
        
        Args:
            url: The eBay URL to find the row
            product_data: ProductData object with scraped data
            
        Returns:
            True if successful, False otherwise
        """
        if not self.client:
            return False
        try:
            _, worksheet = self.ensure_spreadsheet_and_worksheet(
                title='ebay_Product_List', 
                worksheet_name='ebay_Product_List', 
                allow_create=False
            )
            if not worksheet:
                return False
            
            # Ensure all required columns exist
            required_columns = ['URL', 'Title', 'Price', 'Condition', 'Item ID', 'Brand', 'Status', 'Processed Date']
            header_map = self.ensure_columns(worksheet, required_columns)
            
            # Find the row
            row_index = self._find_row_by_url(worksheet, url)
            if not row_index:
                logger.warning(f"Row not found for URL: {url}")
                return False
            
            # Get current row data
            current_row = worksheet.row_values(row_index)
            
            # Extend row if needed
            max_col = max(header_map.values()) + 1 if header_map else len(current_row)
            while len(current_row) < max_col:
                current_row.append('')
            
            # Update specific columns
            def set_col(key: str, value: str):
                idx = header_map.get(self._normalize_key(key))
                if idx is not None and idx < len(current_row):
                    current_row[idx] = value
            
            set_col('Title', product_data.title or '')
            set_col('Price', product_data.price or '')
            set_col('Condition', product_data.condition or '')
            set_col('Item ID', product_data.item_id or '')
            set_col('Brand', product_data.brand or '')
            set_col('Status', 'Done')
            set_col('Processed Date', datetime.now().strftime('%Y-%m-%d %H:%M'))
            
            # Update the row in sheet
            worksheet.update(f'{row_index}:{row_index}', [current_row])
            logger.info(f"Updated row {row_index} with product data for: {product_data.title[:30]}...")
            return True
            
        except Exception as e:
            logger.error(f"Failed to update row with product data: {e}")
            return False

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



class GroqProcessor:
    """
    Enhanced AI processing with Groq, platform agents, chatbot, and caching.
    """
    
    def __init__(self, api_key: str):
        """Initialize with API key and caching."""
        self.api_key = api_key
        self.cache = ResponseCache()
        self._configure_api()
        self.platform_agent = PlatformAgent(self.client, self.model, self.cache)
    
    def _configure_api(self) -> None:
        """Configure Groq API."""
        try:
            if not self.api_key:
                raise ValueError("Groq API key is required")
            
            self.client = Groq(api_key=self.api_key)
            self.model = "openai/gpt-oss-20b"  # GPT-OSS model via Groq
            logger.info("Groq API configured successfully")
            
        except Exception as e:
            logger.error(f"Failed to configure Groq API: {e}")
            raise
    
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
            return response.choices[0].message.content.strip()
            
        except Exception as e:
            logger.error(f"Error in AI chat: {e}")
            return f"Sorry, I encountered an error: {e}"
    
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
            cleaned_data = self._parse_json_response(response.choices[0].message.content)
            if cleaned_data:
                logger.info("Successfully cleaned product data with Groq")
                return cleaned_data
            else:
                logger.warning("Groq response was not valid JSON")
                return {}
                
        except Exception as e:
            logger.error(f"Error cleaning product data with Groq: {e}")
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
            enhanced_data = self._parse_json_response(response.choices[0].message.content)
            if enhanced_data:
                logger.info(f"Successfully enhanced product data for {target_platform}")
                return enhanced_data
            else:
                logger.warning("Groq response was not valid JSON for resale enhancement")
                return {}
                
        except Exception as e:
            logger.error(f"Error enhancing product data for resale: {e}")
            return {}
    
    def _build_resale_prompt(self, product_data: ProductData, target_platform: str) -> str:
        """Build prompt for resale content enhancement."""
        platform_specific = {
            "leboncoin": "Leboncoin listing: concise French copy, clear condition, pickup/shipping notes, price fairness cues, seller location.",
            "vinted": "Vinted listing: casual tone, detailed condition/flaws, size/fit advice, brand/style tags #hashtags, shipping presets.",
            "vestiaire": "Vestiaire Collective: premium tone, authenticity focus, detailed condition grading, precise measurements, material composition.",
            "ebay": "eBay listing: professional, comprehensive specs, item specifics, shipping policies, returns, checking for 'Item Specifics' fields.",
            "poshmark": "Poshmark listing: enthusiastic tone ('Posh Love'), emoji usage 💖, style keywords, brand tagging, bundle discounts.",
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

    def _get_response_text(self, response) -> str:
        """Best-effort extraction of plain text from a Gemini response."""
        try:
            if hasattr(response, 'text') and response.text:
                return str(response.text).strip()
            parts: List[str] = []
            for candidate in getattr(response, 'candidates', []) or []:
                content = getattr(candidate, 'content', None)
                if content and hasattr(content, 'parts'):
                    for part in content.parts:
                        text = getattr(part, 'text', '')
                        if text:
                            parts.append(text)
            return "\n".join(parts).strip()
        except Exception:
            return ""

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
            md = response.choices[0].message.content.strip() if response.choices[0].message.content else ""
            return md
        except Exception as e:
            logger.error(f"Error generating listing markdown: {e}")
            return ""

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
    
    def _get_response_text(self, response) -> str:
        """Extract text from Gemini response."""
        try:
            if hasattr(response, 'text') and response.text:
                return str(response.text).strip()
            parts = []
            for candidate in getattr(response, 'candidates', []) or []:
                content = getattr(candidate, 'content', None)
                if content and hasattr(content, 'parts'):
                    for part in content.parts:
                        text = getattr(part, 'text', '')
                        if text:
                            parts.append(text)
            return "\n".join(parts).strip()
        except Exception:
            return ""
    
    def _parse_json_response(self, response) -> Dict[str, Any]:
        """Parse JSON from Gemini response."""
        try:
            response_text = ""
            if hasattr(response, 'text') and response.text:
                response_text = response.text
            else:
                try:
                    parts = []
                    for candidate in getattr(response, 'candidates', []) or []:
                        content = getattr(candidate, 'content', None)
                        if content and hasattr(content, 'parts'):
                            for part in content.parts:
                                text = getattr(part, 'text', '')
                                if text:
                                    parts.append(text)
                    response_text = "\n".join(parts)
                except Exception:
                    response_text = ""
            
            cleaned = response_text.strip()
            if cleaned.startswith("```"):
                cleaned = re.sub(r"^```(?:json)?", "", cleaned, flags=re.IGNORECASE).strip()
                if cleaned.endswith("```"):
                    cleaned = cleaned[:-3].strip()
            
            start = cleaned.find("{")
            end = cleaned.rfind("}")
            if start != -1 and end != -1 and end > start:
                json_str = cleaned[start:end+1]
                return json.loads(json_str)
        except Exception as e:
            logger.warning(f"Failed to parse JSON: {e}")
        return {}

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
        """List subfolders under base_dir that contain at least one image."""
        folders: List[Path] = []
        try:
            for p in self.base_dir.iterdir():
                if p.is_dir():
                    if any((p / f).suffix.lower() in {'.jpg', '.jpeg', '.png', '.webp'} for f in os.listdir(p)):
                        folders.append(p)
        except Exception:
            pass
        return sorted(folders, key=lambda x: x.name.lower())

    def list_images(self, folder_path: Path) -> List[Path]:
        try:
            return [p for p in folder_path.iterdir() if p.suffix.lower() in {'.jpg', '.jpeg', '.png', '.webp'}]
        except Exception:
            return []
    
    def create_product_folder(self, product_title: str, item_id: str = "") -> Path:
        """
        Create and return product-specific folder path.
        
        Args:
            product_title: Product title for folder naming
            item_id: Optional eBay Item ID to append for uniqueness
            
        Returns:
            Path object for product folder
        """
        try:
            clean_title = clean_filename(product_title)
            # Append ID for uniqueness and identification if present
            folder_name = f"{clean_title} - {item_id}" if item_id else clean_title
            
            product_folder = self.base_dir / folder_name
            product_folder.mkdir(exist_ok=True)
            logger.debug(f"Created product folder: {product_folder}")
            return product_folder
            
        except Exception as e:
            logger.error(f"Error creating product folder: {e}")
            raise
    
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

    def _get_response_text(self, response) -> str:
        """Best-effort extraction of plain text from a Gemini response."""
        try:
            if hasattr(response, 'text') and response.text:
                return str(response.text).strip()
            parts = []
            for candidate in getattr(response, 'candidates', []) or []:
                content = getattr(candidate, 'content', None)
                if content and hasattr(content, 'parts'):
                    for part in content.parts:
                        text = getattr(part, 'text', '')
                        if text:
                            parts.append(text)
            return "\n".join(parts).strip()
        except Exception:
            return ""

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
    
    def get_existing_product_folders(self) -> List[Dict[str, str]]:
        """
        Get list of existing product folders for AI processing.
        
        Returns:
            List of dictionaries with folder info
        """
        try:
            folders = []
            for folder_path in self.base_dir.iterdir():
                if folder_path.is_dir():
                    # Look for text-like files in folder (.txt, .md)
                    text_files = list(folder_path.glob("*.txt")) + list(folder_path.glob("*.md"))
                    if text_files:
                        # Exclude AI-processed files from main list
                        main_files = [f for f in text_files if not f.name.startswith("ai_")]
                        if main_files:
                            folders.append({
                                'folder_name': folder_path.name,
                                'folder_path': str(folder_path),
                                'text_files': [f.name for f in main_files],
                                'main_file': main_files[0].name if main_files else ""
                            })
            
            logger.debug(f"Found {len(folders)} product folders")
            return sorted(folders, key=lambda x: x['folder_name'])
            
        except Exception as e:
            logger.error(f"Error getting product folders: {e}")
            return []
    
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

def load_credentials() -> Optional[Dict]:
    """Load Google service account credentials from file or Streamlit secrets."""
    try:
        # Try Streamlit secrets first (handle case where secrets.toml doesn't exist)
        if hasattr(st, 'secrets') and 'gcp_service_account' in st.secrets:
             secret_value = st.secrets["gcp_service_account"]
             # Handle JSON string vs Dict
             if isinstance(secret_value, str):
                 return json.loads(secret_value)
             return dict(secret_value)
    except Exception as e:
        logger.error(f"Error loading secrets: {e}")
        # Secrets not configured or parse error - silent failure to allow fallback
        pass
    
    # Try common filenames
    common_names = [
        'service_account.json',
        'credentials.json',
        'gcp_credentials.json',
    ]
    for name in common_names:
        creds_path = Path.cwd() / name
        if creds_path.exists():
            with open(creds_path, 'r', encoding='utf-8') as f:
                return json.load(f)
    
    # Auto-detect: Look for any JSON file that looks like a service account
    for json_file in Path.cwd().glob('*.json'):
        try:
            with open(json_file, 'r', encoding='utf-8') as f:
                data = json.load(f)
                # Check if it's a service account file
                if data.get('type') == 'service_account' and 'private_key' in data:
                    logger.info(f"Auto-detected service account file: {json_file.name}")
                    return data
        except Exception:
            continue
    
    return None

def load_groq_api_key() -> str:
    """Load Groq API key from Streamlit secrets, environment, or local config file."""
    # 1) Streamlit secrets
    try:
        if hasattr(st, 'secrets') and "groq_api_key" in st.secrets:
            key = str(st.secrets["groq_api_key"]).strip()
            if key:
                return key
    except Exception:
        pass
    # 2) Environment
    env_key = os.getenv('GROQ_API_KEY', '').strip()
    if env_key:
        return env_key
    # 3) Local config file
    try:
        cfg_path = Path.cwd() / '.groq_config.json'
        if cfg_path.exists():
            data = json.load(open(cfg_path, 'r', encoding='utf-8'))
            key = str(data.get('groq_api_key', '')).strip()
            if key:
                return key
    except Exception as e:
        logger.warning(f"Could not read .groq_config.json: {e}")
    return ""

def save_groq_api_key(api_key: str) -> bool:
    """Persist Groq API key to a local config file in the project directory."""
    try:
        cfg_path = Path.cwd() / '.groq_config.json'
        json.dump({"groq_api_key": api_key.strip()}, open(cfg_path, 'w', encoding='utf-8'))
        return True
    except Exception as e:
        logger.error(f"Failed to save Groq API key: {e}")
        return False

def show_success_animation(message: str, icon: str = "✅"):
    """Display an animated success message."""
    st.markdown(
        f"""
        <div style="
            background: linear-gradient(135deg, rgba(34, 197, 94, 0.12), rgba(34, 197, 94, 0.05));
            border-left: 4px solid #22c55e;
            border-radius: 12px;
            padding: 1.25rem;
            margin: 1rem 0;
            animation: slideInLeft 0.4s ease-out, successPulse 1s ease-out;
            box-shadow: 0 4px 16px rgba(34, 197, 94, 0.2);
        ">
            <div style="
                display: flex;
                align-items: center;
                gap: 12px;
                font-size: 1rem;
                font-weight: 600;
                color: #22c55e;
            ">
                <span style="font-size: 1.5rem;">{icon}</span>
                <span>{message}</span>
            </div>
        </div>
        """,
        unsafe_allow_html=True
    )

def show_progress_stage(stage: str, icon: str = "⏳"):
    """Display a progress stage indicator."""
    st.markdown(
        f"""
        <div style="
            background: linear-gradient(135deg, rgba(91, 138, 255, 0.12), rgba(91, 138, 255, 0.05));
            border-left: 4px solid #5b8aff;
            border-radius: 12px;
            padding: 1rem 1.25rem;
            margin: 0.75rem 0;
            animation: fadeInScale 0.3s ease-out;
        ">
            <div style="
                display: flex;
                align-items: center;
                gap: 12px;
                font-size: 0.95rem;
                font-weight: 500;
                color: #5b8aff;
            ">
                <span style="font-size: 1.25rem; animation: pulse 2s ease-in-out infinite;">{icon}</span>
                <span>{stage}</span>
            </div>
        </div>
        """,
        unsafe_allow_html=True
    )

def show_metric_card(title: str, value: str, icon: str = "📊"):
    """Display an animated metric card."""
    st.markdown(
        f"""
        <div style="
            background: linear-gradient(135deg, #ffffff 0%, #f8fafc 100%);
            border: 1.5px solid rgba(15, 23, 42, 0.1);
            border-radius: 12px;
            padding: 1.5rem;
            margin: 0.5rem 0;
            animation: fadeInScale 0.4s ease-out;
            box-shadow: 0 2px 12px rgba(15, 23, 42, 0.06);
            transition: transform 0.3s ease, box-shadow 0.3s ease;
        ">
            <div style="
                display: flex;
                align-items: center;
                justify-content: space-between;
            ">
                <div>
                    <div style="
                        font-size: 0.85rem;
                        color: #64748b;
                        font-weight: 500;
                        margin-bottom: 0.5rem;
                        text-transform: uppercase;
                        letter-spacing: 0.05em;
                    ">{title}</div>
                    <div style="
                        font-size: 2rem;
                        font-weight: 700;
                        color: #3b82f6;
                        text-shadow: 0 0 20px rgba(59, 130, 246, 0.15);
                    ">{value}</div>
                </div>
                <div style="
                    font-size: 2.5rem;
                    opacity: 0.2;
                ">{icon}</div>
            </div>
        </div>
        """,
        unsafe_allow_html=True
    )

def show_animated_success(message: str, icon: str = "✅"):
    """Display an animated success message with modern light theme styling."""
    st.markdown(
        f"""
        <div style="
            background: linear-gradient(135deg, #ffffff 0%, #f0fdf4 100%);
            border: 2px solid #10b981;
            border-radius: 16px;
            padding: 1.25rem 1.5rem;
            margin: 1rem 0;
            animation: successPulse 0.6s ease-out, fadeInScale 0.4s ease-out;
            box-shadow: 0 4px 20px rgba(16, 185, 129, 0.12);
        ">
            <div style="
                display: flex;
                align-items: center;
                gap: 12px;
                font-size: 1rem;
                font-weight: 600;
                color: #059669;
            ">
                <span style="font-size: 1.5rem; animation: bounceIn 0.6s ease-out;">{icon}</span>
                <span>{message}</span>
            </div>
        </div>
        """,
        unsafe_allow_html=True
    )

def show_processing_stage(stage: str, icon: str = "⚙️"):
    """Display an animated processing stage indicator."""
    st.markdown(
        f"""
        <div style="
            background: linear-gradient(135deg, #ffffff 0%, #eff6ff 100%);
            border-left: 4px solid #3b82f6;
            border-radius: 12px;
            padding: 1rem 1.25rem;
            margin: 0.75rem 0;
            animation: fadeInScale 0.3s ease-out;
            box-shadow: 0 2px 8px rgba(59, 130, 246, 0.08);
        ">
            <div style="
                display: flex;
                align-items: center;
                gap: 12px;
                font-size: 0.95rem;
                font-weight: 500;
                color: #1e40af;
            ">
                <span style="font-size: 1.25rem; animation: pulse 2s ease-in-out infinite;">{icon}</span>
                <span>{stage}</span>
            </div>
        </div>
        """,
        unsafe_allow_html=True
    )

def inject_global_styles() -> None:
    """Inject modern, animated global styles with Streamlit's latest design patterns."""
    st.markdown(
        """
        <style>
        /* Import modern fonts */
        @import url('https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700;800&display=swap');
        
        :root {
          /* Modern color palette - Black and white with strong contrast */
          --bg-primary: #ffffff;
          --bg-secondary: #f9fafb;
          --bg-tertiary: #f3f4f6;
          --surface: linear-gradient(135deg, #ffffff 0%, #f9fafb 100%);
          --surface-hover: #e5e7eb;
          --text-primary: #000000;
          --text-secondary: #374151;
          --text-muted: #6b7280;
          --accent-primary: #000000;
          --accent-secondary: #1f2937;
          --accent-glow: rgba(0, 0, 0, 0.1);
          --success: #10b981;
          --success-glow: rgba(16, 185, 129, 0.15);
          --warning: #f59e0b;
          --error: #ef4444;
          --border: rgba(0, 0, 0, 0.1);
          --border-strong: rgba(0, 0, 0, 0.2);
          --shadow-sm: 0 1px 3px rgba(0, 0, 0, 0.12);
          --shadow-md: 0 4px 12px rgba(0, 0, 0, 0.15);
          --shadow-lg: 0 8px 24px rgba(0, 0, 0, 0.18);
          --glow-black: 0 0 20px rgba(0, 0, 0, 0.2);
          --glow-green: 0 0 20px rgba(16, 185, 129, 0.2);
        }
        
        html, body, .stApp {
          font-family: 'Inter', sans-serif !important;
          background: var(--bg-primary) !important;
          color: var(--text-primary) !important;
          scroll-behavior: smooth !important;
        }

        /* Enforce font on text elements only, avoiding icons */
        h1, h2, h3, h4, h5, h6, p, label, input, button, textarea, select, .stMarkdown, .stText {
             font-family: 'Inter', sans-serif !important;
        }
        
        /* Exception for icons if possible - Streamlit icons often use specific font families 
           that might be overwritten by 'span' or 'div' above. 
           We can try to exclude common icon classes or just accept that 'div'/'span' is still risky.
           Better approach: Apply font to local context or .stApp but NOT !important on generic tags if avoidable.
           However, to force the look, we need some force. Start with the above, if glitch persists, 
           we narrow down. The previous [class*="css"] was definitely too broad.
        */
        
        /* Input & Button Styling */
        .stTextInput input {
            border: 2px solid #e5e7eb !important;
            border-radius: 10px !important;
            padding: 12px 16px !important;
            font-size: 1.1rem !important;
            box-shadow: 0 2px 4px rgba(0,0,0,0.02) !important;
            transition: all 0.2s ease !important;
        }
        .stTextInput input:focus {
            border-color: #000000 !important;
            box-shadow: 0 4px 12px rgba(0,0,0,0.05) !important;
        }
        div[data-testid="stButton"] button {
            border-radius: 10px !important;
            font-weight: 600 !important;
            padding: 0.75rem 1.5rem !important;
            transition: transform 0.1s ease !important;
        }
        div[data-testid="stButton"] button:active {
            transform: scale(0.98) !important;
        }

        /* Product Card Styling */
        .product-card {
            background: #ffffff;
            border-radius: 16px;
            box-shadow: 0 10px 30px -5px rgba(0, 0, 0, 0.08);
            border: 1px solid rgba(0,0,0,0.04);
            overflow: hidden;
            margin-top: 1rem;
            animation: fadeInUp 0.5s ease-out;
        }
        .product-header {
            padding: 1.5rem 2rem;
            background: linear-gradient(to right, #f8f9fa, #ffffff);
            border-bottom: 1px solid rgba(0,0,0,0.05);
        }
        .product-title {
            font-size: 1.4rem;
            font-weight: 700;
            color: #111827;
            line-height: 1.4;
            margin: 0;
        }
        .product-body {
            display: flex;
            padding: 2rem;
            gap: 2.5rem;
            flex-wrap: wrap;
        }
        .product-image-container {
            flex: 0 0 350px;
            max-width: 100%;
        }
        .product-image {
            width: 100%;
            border-radius: 12px;
            box-shadow: 0 4px 12px rgba(0,0,0,0.08);
            object-fit: contain;
            background: #f3f4f6;
            aspect-ratio: 1;
        }
        .product-details {
            flex: 1;
            min-width: 300px;
        }
        .price-tag {
            font-size: 2.5rem;
            font-weight: 800;
            color: #000000;
            margin-bottom: 0.25rem;
        }
        .detail-row {
            display: flex;
            align-items: flex-start;
            padding: 0.75rem 0;
            border-bottom: 1px solid #f3f4f6;
        }
        .detail-label {
            font-weight: 600;
            color: #6b7280;
            width: 100px;
            flex-shrink: 0;
            font-size: 0.95rem;
        }
        .detail-value {
            color: #1f2937;
            font-size: 0.95rem;
            line-height: 1.5;
        }
        .status-section {
            display: flex;
            gap: 1rem;
            flex-wrap: wrap;
            margin-top: 1.5rem;
            padding-top: 1.5rem;
            border-top: 2px dashed #f3f4f6;
        }
        .status-badge {
            display: inline-flex;
            align-items: center;
            padding: 0.35rem 0.85rem;
            border-radius: 9999px;
            font-size: 0.85rem;
            font-weight: 600;
            background: #f0fdf4;
            color: #15803d;
            border: 1px solid rgba(22, 163, 74, 0.2);
        }
        .status-badge.neutral {
            background: #f3f4f6;
            color: #4b5563;
            border-color: #e5e7eb;
        }
        .action-buttons {
            display: flex;
            gap: 1rem;
            margin-top: 1.5rem;
        }
        
        /* Global app styles */
        .stApp {
          background: var(--bg-primary) !important;
        }
        
        .block-container {
          padding: 2.5rem 2rem !important;
          max-width: 1600px !important;
          animation: fadeInUp 0.5s ease-out !important;
        }
        
        /* Enhanced Typography */
        h1, h2, h3, h4, h5, h6 {
          font-weight: 700 !important;
          letter-spacing: -0.02em !important;
          color: var(--text-primary) !important;
          line-height: 1.3 !important;
        }
        
        h1 {
          font-size: 2.5rem !important;
          color: #000000 !important;
          margin-bottom: 0.5rem !important;
        }
        
        h2 {
          font-size: 1.75rem !important;
          margin-bottom: 1rem !important;
          color: #000000 !important;
        }
        
        h3 {
          font-size: 1.25rem !important;
          margin-bottom: 0.875rem !important;
          color: #374151 !important;
        }
        
        p, div, span, label {
          font-size: 0.95rem !important;
        }
        
        /* Input labels */
        .stTextInput label, .stNumberInput label, .stSelectbox label, .stTextArea label {
          font-size: 0.9rem !important;
          font-weight: 600 !important;
          color: #000000 !important;
          margin-bottom: 0.5rem !important;
        }
        
        /* Modern Tabs with black active state */
        .stTabs [data-baseweb="tab-list"] {
          gap: 10px !important;
          border-bottom: 2px solid var(--border-strong) !important;
          background: transparent !important;
          padding-bottom: 0 !important;
        }
        
        .stTabs [data-baseweb="tab"] {
          background: var(--bg-tertiary) !important;
          color: var(--text-muted) !important;
          border-radius: 8px 8px 0 0 !important;
          padding: 14px 24px !important;
          border: 2px solid var(--border) !important;
          border-bottom: none !important;
          font-weight: 600 !important;
          font-size: 0.95rem !important;
          transition: all 0.3s cubic-bezier(0.4, 0, 0.2, 1) !important;
          position: relative !important;
        }
        
        .stTabs [data-baseweb="tab"]::before {
          content: '' !important;
          position: absolute !important;
          bottom: -2px !important;
          left: 0 !important;
          right: 0 !important;
          height: 2px !important;
          background: transparent !important;
          transition: all 0.3s ease !important;
        }
        
        .stTabs [data-baseweb="tab"]:hover {
          background: var(--surface-hover) !important;
          color: var(--text-secondary) !important;
          transform: translateY(-2px) !important;
        }
        
        .stTabs [aria-selected="true"] {
          background: #000000 !important;
          color: white !important;
          border-color: #000000 !important;
          box-shadow: 0 4px 12px rgba(0, 0, 0, 0.2) !important;
          transform: translateY(-2px) !important;
        }
        
        .stTabs [aria-selected="true"]::before {
          background: white !important;
        }
        
        /* Enhanced Input fields with better visibility */
        .stTextInput input,
        .stNumberInput input {
          background: #ffffff !important;
          color: #000000 !important;
          border-radius: 8px !important;
          border: 2px solid #d1d5db !important;
          padding: 12px 16px !important;
          font-size: 1rem !important;
          font-weight: 500 !important;
          transition: all 0.3s cubic-bezier(0.4, 0, 0.2, 1) !important;
        }
        
        .stTextInput input:focus,
        .stNumberInput input:focus {
          border-color: #000000 !important;
          box-shadow: 0 0 0 3px rgba(0, 0, 0, 0.1) !important;
          background: #ffffff !important;
          outline: none !important;
        }
        
        .stTextInput input:hover,
        .stNumberInput input:hover {
          border-color: #9ca3af !important;
        }
        
        .stTextInput input::placeholder,
        .stNumberInput input::placeholder {
          color: #9ca3af !important;
          font-weight: 400 !important;
        }
        
        /* Select boxes with better visibility */
        .stSelectbox [data-baseweb="select"] > div {
          background: #ffffff !important;
          color: #000000 !important;
          border-radius: 8px !important;
          border: 2px solid #d1d5db !important;
          font-size: 1rem !important;
          font-weight: 500 !important;
          transition: all 0.3s ease !important;
          min-height: 48px !important;
        }
        
        .stSelectbox [data-baseweb="select"]:hover > div {
          border-color: #9ca3af !important;
        }
        
        .stSelectbox [data-baseweb="select"]:focus-within > div {
          border-color: #000000 !important;
          box-shadow: 0 0 0 3px rgba(0, 0, 0, 0.1) !important;
        }
        
        /* Dropdown menu */
        [data-baseweb="menu"] {
          background: #ffffff !important;
          border: 2px solid #d1d5db !important;
          border-radius: 8px !important;
          box-shadow: 0 4px 12px rgba(0, 0, 0, 0.15) !important;
        }
        
        [data-baseweb="menu"] li {
          color: #000000 !important;
          font-size: 0.95rem !important;
          font-weight: 500 !important;
          padding: 10px 16px !important;
        }
        
        [data-baseweb="menu"] li:hover {
          background: #f3f4f6 !important;
        }
        
        /* Text areas with better visibility */
        .stTextArea textarea {
          background: #ffffff !important;
          color: #000000 !important;
          border-radius: 8px !important;
          border: 2px solid #d1d5db !important;
          font-size: 1rem !important;
          font-weight: 500 !important;
          padding: 12px 16px !important;
          transition: all 0.3s ease !important;
        }
        
        .stTextArea textarea:focus {
          border-color: #000000 !important;
          box-shadow: 0 0 0 3px rgba(0, 0, 0, 0.1) !important;
          outline: none !important;
        }
        
        .stTextArea textarea::placeholder {
          color: #9ca3af !important;
          font-weight: 400 !important;
        }
        
        /* Modern Buttons with solid black */
        .stButton > button {
          background: #000000 !important;
          color: white !important;
          border-radius: 8px !important;
          padding: 12px 28px !important;
          border: 2px solid #000000 !important;
          font-weight: 600 !important;
          font-size: 0.95rem !important;
          transition: all 0.3s cubic-bezier(0.4, 0, 0.2, 1) !important;
          box-shadow: var(--shadow-sm) !important;
          position: relative !important;
          overflow: hidden !important;
        }
        
        .stButton > button::before {
          content: '' !important;
          position: absolute !important;
          top: 50% !important;
          left: 50% !important;
          width: 0 !important;
          height: 0 !important;
          border-radius: 50% !important;
          background: rgba(255, 255, 255, 0.2) !important;
          transform: translate(-50%, -50%) !important;
          transition: width 0.6s, height 0.6s !important;
        }
        
        .stButton > button:hover::before {
          width: 300px !important;
          height: 300px !important;
        }
        
        .stButton > button:hover {
          transform: translateY(-2px) !important;
          box-shadow: 0 6px 20px rgba(0, 0, 0, 0.25) !important;
          background: #1f2937 !important;
        }
        
        .stButton > button:active {
          transform: translateY(0) !important;
        }
        
        /* Download button with green */
        .stDownloadButton > button {
          background: #10b981 !important;
          border-color: #10b981 !important;
        }
        
        .stDownloadButton > button:hover {
          background: #059669 !important;
          box-shadow: var(--glow-green), var(--shadow-md) !important;
        }
        
        /* Enhanced Cards with gradient borders */
        .card {
          background: var(--surface) !important;
          border: 1.5px solid var(--border) !important;
          border-radius: 16px !important;
          padding: 2rem !important;
          margin-bottom: 2rem !important;
          box-shadow: var(--shadow-md) !important;
          position: relative !important;
          overflow: hidden !important;
          animation: fadeInScale 0.4s ease-out !important;
        }
        
        .card::before {
          content: '' !important;
          position: absolute !important;
          top: 0 !important;
          left: 0 !important;
          right: 0 !important;
          height: 3px !important;
          background: linear-gradient(90deg, var(--accent-primary), var(--success), var(--accent-primary)) !important;
          background-size: 200% 100% !important;
          animation: gradientShift 3s ease infinite !important;
        }
        
        .card h2, .card h3 {
          margin-top: 0 !important;
        }
        
        .card p.muted {
          color: var(--text-muted) !important;
          font-size: 0.95rem !important;
          margin-bottom: 1rem !important;
        }
        
        /* Status messages with animation */
        .stAlert {
          border-radius: 8px !important;
          border-left-width: 4px !important;
          padding: 1rem 1.25rem !important;
          animation: slideInLeft 0.3s ease-out !important;
        }
        
        .stSuccess {
          background: #f0fdf4 !important;
          border-left-color: #10b981 !important;
          color: #000000 !important;
        }
        
        .stWarning {
          background: #fffbeb !important;
          border-left-color: #f59e0b !important;
          color: #000000 !important;
        }
        
        .stError {
          background: #fef2f2 !important;
          border-left-color: #ef4444 !important;
          color: #000000 !important;
        }
        
        .stInfo {
          background: #eff6ff !important;
          border-left-color: #000000 !important;
          color: #000000 !important;
        }
        
        /* Animated Progress bar */
        .stProgress > div > div > div {
          background: linear-gradient(90deg, #000000, #10b981) !important;
          background-size: 200% 100% !important;
          animation: gradientShift 2s ease infinite !important;
          border-radius: 8px !important;
          box-shadow: 0 2px 8px rgba(0, 0, 0, 0.2) !important;
        }
        
        /* Enhanced Expander */
        .streamlit-expanderHeader {
          background: #f9fafb !important;
          border-radius: 8px !important;
          border: 2px solid #d1d5db !important;
          color: #000000 !important;
          font-weight: 600 !important;
          font-size: 1rem !important;
          padding: 1rem !important;
          transition: all 0.3s ease !important;
        }
        
        .streamlit-expanderHeader:hover {
          border-color: #000000 !important;
          background: #e5e7eb !important;
        }
        
        .streamlit-expanderContent {
          background: #ffffff !important;
          border: 2px solid #d1d5db !important;
          border-top: none !important;
          border-radius: 0 0 8px 8px !important;
          padding: 1rem !important;
        }
        
        /* Sidebar styling */
        section[data-testid="stSidebar"] {
          background: #f9fafb !important;
          border-right: 2px solid #d1d5db !important;
        }
        
        section[data-testid="stSidebar"] > div {
          padding-top: 2rem !important;
        }
        
        section[data-testid="stSidebar"] h2,
        section[data-testid="stSidebar"] h3 {
          color: #000000 !important;
          font-weight: 700 !important;
        }
        
        section[data-testid="stSidebar"] label {
          color: #000000 !important;
          font-weight: 600 !important;
          font-size: 0.9rem !important;
        }
        
        /* Spinner with pulse */
        .stSpinner > div {
          border-top-color: #000000 !important;
          animation: spin 1s linear infinite, pulse 2s ease-in-out infinite !important;
        }
        
        /* Metrics with emphasis */
        [data-testid="stMetricValue"] {
          color: #000000 !important;
          font-size: 2.2rem !important;
          font-weight: 700 !important;
        }
        
        [data-testid="stMetricLabel"] {
          color: #6b7280 !important;
          font-size: 0.9rem !important;
          font-weight: 600 !important;
        }
        
        /* Code blocks */
        .stCodeBlock {
          background: #f9fafb !important;
          border: 2px solid #d1d5db !important;
          border-radius: 8px !important;
          box-shadow: 0 1px 3px rgba(0, 0, 0, 0.12) !important;
        }
        
        code {
          background: #f3f4f6 !important;
          color: #000000 !important;
          padding: 2px 6px !important;
          border-radius: 4px !important;
          font-size: 0.9rem !important;
          font-weight: 500 !important;
        }
        
        /* Multiselect tags - modern black style */
        .stMultiSelect [data-baseweb="tag"] {
          background: #000000 !important;
          color: white !important;
          border-radius: 6px !important;
          padding: 6px 12px !important;
          font-weight: 600 !important;
          font-size: 0.9rem !important;
          margin: 2px !important;
        }
        
        .stMultiSelect [data-baseweb="tag"] svg {
          fill: white !important;
        }
        
        .stMultiSelect [data-baseweb="tag"]:hover {
          background: #1f2937 !important;
        }
        
        .stMultiSelect label {
          color: #000000 !important;
          font-weight: 600 !important;
          font-size: 0.9rem !important;
          margin-bottom: 0.5rem !important;
        }
        
        .stMultiSelect [data-baseweb="select"] {
          background: #ffffff !important;
          border: 2px solid #d1d5db !important;
          border-radius: 8px !important;
        }
        
        .stMultiSelect [data-baseweb="select"]:hover {
          border-color: #9ca3af !important;
        }
        
        .stMultiSelect [data-baseweb="select"]:focus-within {
          border-color: #000000 !important;
          box-shadow: 0 0 0 3px rgba(0, 0, 0, 0.1) !important;
        }
        
        /* Checkbox and Radio */
        .stCheckbox, .stRadio {
          color: #000000 !important;
          font-weight: 500 !important;
        }
        
        /* Slider styling */
        .stSlider [role="slider"] {
          background: #000000 !important;
          box-shadow: 0 0 0 4px rgba(0, 0, 0, 0.1) !important;
          width: 20px !important;
          height: 20px !important;
          transition: all 0.3s ease !important;
          cursor: pointer !important;
        }
        
        .stSlider [data-baseweb="slider"] > div:first-child > div {
          background: #e5e7eb !important;
          height: 6px !important;
          border-radius: 3px !important;
        }
        
        .stSlider [data-baseweb="slider"] > div:first-child > div > div {
          background: #000000 !important;
          height: 6px !important;
          border-radius: 3px !important;
        }
        
        .stSlider [role="slider"]:hover {
          transform: scale(1.15) !important;
          box-shadow: 0 0 0 6px rgba(0, 0, 0, 0.15) !important;
        }
        
        .stSlider label {
          color: #000000 !important;
          font-weight: 600 !important;
          font-size: 0.9rem !important;
          margin-bottom: 0.75rem !important;
        }
        
        /* Slider value display */
        .stSlider [data-testid="stTickBar"] {
          color: #6b7280 !important;
          font-size: 0.85rem !important;
        }
        
        .stSlider .rc-slider-rail {
          background: var(--bg-tertiary) !important;
          height: 6px !important;
        }
        
        /* Custom scrollbar */
        ::-webkit-scrollbar {
          width: 12px !important;
          height: 12px !important;
        }
        
        ::-webkit-scrollbar-track {
          background: var(--bg-secondary) !important;
        }
        
        ::-webkit-scrollbar-thumb {
          background: var(--bg-tertiary) !important;
          border-radius: 6px !important;
          border: 2px solid var(--bg-secondary) !important;
        }
        
        ::-webkit-scrollbar-thumb:hover {
          background: var(--surface-hover) !important;
        }
        
        /* Hide Streamlit branding */
        #MainMenu { visibility: hidden !important; }
        footer { visibility: hidden !important; }
        header { visibility: hidden !important; }
        
        /* Animations */
        @keyframes fadeIn {
          from { opacity: 0; }
          to { opacity: 1; }
        }
        
        @keyframes fadeInUp {
          from {
            opacity: 0;
            transform: translateY(20px);
          }
          to {
            opacity: 1;
            transform: translateY(0);
          }
        }
        
        @keyframes fadeInScale {
          from {
            opacity: 0;
            transform: scale(0.95);
          }
          to {
            opacity: 1;
            transform: scale(1);
          }
        }
        
        @keyframes slideInLeft {
          from {
            opacity: 0;
            transform: translateX(-20px);
          }
          to {
            opacity: 1;
            transform: translateX(0);
          }
        }
        
        @keyframes gradientShift {
          0%, 100% { background-position: 0% 50%; }
          50% { background-position: 100% 50%; }
        }
        
        @keyframes pulse {
          0%, 100% { opacity: 1; }
          50% { opacity: 0.7; }
        }
        
        @keyframes spin {
          to { transform: rotate(360deg); }
        }
        
        @keyframes shimmer {
          0% { background-position: -1000px 0; }
          100% { background-position: 1000px 0; }
        }
        
        /* Success animation overlay */
        @keyframes successPulse {
          0% {
            box-shadow: 0 0 0 0 var(--success-glow);
          }
          50% {
            box-shadow: 0 0 0 20px rgba(34, 197, 94, 0);
          }
          100% {
            box-shadow: 0 0 0 0 rgba(34, 197, 94, 0);
          }
        }
        
        .success-animation {
          animation: successPulse 1s ease-out !important;
        }
        
        /* Loading skeleton */
        .skeleton {
          background: linear-gradient(90deg, var(--bg-tertiary) 25%, var(--surface-hover) 50%, var(--bg-tertiary) 75%) !important;
          background-size: 1000px 100% !important;
          animation: shimmer 2s infinite !important;
          border-radius: 8px !important;
        }
        </style>
        """,
        unsafe_allow_html=True,
    )

def initialize_components() -> Tuple[EbayScraper, GoogleSheetsManager, FileManager]:
    """Initialize all application components."""
    scraper = EbayScraper()
    
    credentials = load_credentials()
    sheets_manager = GoogleSheetsManager(credentials)
    
    file_manager = FileManager()
    
    return scraper, sheets_manager, file_manager

def display_scraping_results(result: ScrapingResult, downloaded_images: List[str], 
                           folder_path: Path, sheets_updated: bool, csv_updated: bool):
    """
    Display results of scraping operation with a premium specific product card layout.
    """
    if not result.success or not result.product_data:
        st.error(f"Scraping failed: {result.error_message}")
        return

    pd = result.product_data
    
    # Determine Main Image
    main_image_src = ""
    # Try to find a local path first
    if downloaded_images:
        # Convert local absolute path to relative for Streamlit to serve if possible, 
        # BUT Streamlit serving local files from arbitrary paths is tricky without static config.
        # So we better use the remote URL for display to be safe and easy, 
        # OR assume we can just display the remote URL for the 'main' image.
        if result.image_urls:
             main_image_src = result.image_urls[0]
    elif result.image_urls:
        main_image_src = result.image_urls[0]
        
    # Generate Status Badges HTML
    badges_html = ""
    badges_html += f'<span class="status-badge">Images: {len(downloaded_images)}</span>'
    
    if sheets_updated:
        badges_html += '<span class="status-badge">Sheet: Updated</span>'
    else:
        badges_html += '<span class="status-badge neutral">Sheet: Skipped</span>'
        
    if csv_updated:
        badges_html += '<span class="status-badge">CSV: Saved</span>'
    else:
        badges_html += '<span class="status-badge neutral">CSV: Skipped</span>'
        
    badges_html += f'<span class="status-badge neutral">Folder: {folder_path.name[:20]}...</span>'

    # Render Card
    st.markdown(f"""
    <div class="product-card">
        <div class="product-header">
            <h3 class="product-title">{pd.title}</h3>
        </div>
        <div class="product-body">
            <div class="product-image-container">
                <img src="{main_image_src}" class="product-image" onerror="this.style.display='none'"/>
            </div>
            <div class="product-details">
                <div class="price-tag">{pd.price}</div>
                <div class="detail-row">
                    <span class="detail-label">Condition</span>
                    <span class="detail-value">{pd.condition or 'N/A'}</span>
                </div>
                <div class="detail-row">
                    <span class="detail-label">Brand</span>
                    <span class="detail-value">{pd.brand or 'N/A'}</span>
                </div>
                <div class="detail-row">
                    <span class="detail-label">Seller</span>
                    <span class="detail-value">{pd.seller or 'N/A'}</span>
                </div>
                 <div class="detail-row">
                    <span class="detail-label">Shipping</span>
                    <span class="detail-value">{pd.shipping or 'N/A'}</span>
                </div>
                <div class="status-section">
                    {badges_html}
                </div>
            </div>
        </div>
    </div>
    """, unsafe_allow_html=True)
    
    # Expandables for details
    st.write("")
    with st.expander("📝 View Full Product Description", expanded=False):
        st.markdown(pd.description or "*No description available*")
    
    if pd.item_specifics:
        with st.expander("📋 View Item Specifics", expanded=False):
            # Create a clean grid layout for item specifics
            specifics_html = '<div style="display: grid; grid-template-columns: repeat(auto-fill, minmax(300px, 1fr)); gap: 1rem;">'
            
            for key, value in pd.item_specifics.items():
                # clean up key/value for display
                k = key.strip()
                v = value.strip()
                if k and v:
                    specifics_html += f"""
                    <div style="background: #f9fafb; padding: 0.75rem; border-radius: 8px; border: 1px solid #f3f4f6;">
                        <div style="font-size: 0.8rem; color: #6b7280; font-weight: 600; text-transform: uppercase; letter-spacing: 0.05em; margin-bottom: 0.25rem;">{k}</div>
                        <div style="font-size: 0.95rem; color: #111827; font-weight: 500; word-break: break-word;">{v}</div>
                    </div>
                    """
            specifics_html += '</div>'
            st.markdown(specifics_html, unsafe_allow_html=True)
            
    # Quick Actions (e.g. Open Folder) - Streamlit can't easily open local folder on client side via button, 
    # but we can show the path text or provide a copy button.
    st.success(f"📁 Data saved to: `{folder_path}`")
    
    # Add open folder buttons if running locally
    col_open_1, col_open_2 = st.columns(2)
    with col_open_1:
         # Zip download button logic could go here if implemented
         pass
    with col_open_2:
        if st.button("📂 Open Folder", key=f"open_folder_{folder_path.name}"):
            try:
                os.startfile(folder_path)
            except Exception:
                st.warning("Could not open folder automatically.")


def handle_single_product_scrape(ebay_url: str, scraper: EbayScraper, file_manager: FileManager, sheets_manager: GoogleSheetsManager):
    """
    Orchestrates the single product scraping flow.
    """
    if not ebay_url:
        st.error("⚠️ Please enter a valid eBay URL to begin.")
        return

    # 1. Validation
    try:
        scraper.validate_ebay_url(ebay_url)
    except ValidationError as e:
        st.error(f"❌ URL Validation Error: {e}")
        return

    # 2. Check Duplicates (if Sheets active)
    if sheets_manager.is_available():
        if sheets_manager.url_exists(ebay_url):
            st.warning("⚠️ This product is already in your Google Sheet. Skipping to maintain data integrity.")
            return

    # 3. Operations
    progress_bar = st.progress(0)
    status_msg = st.empty()
    
    try:
        # SCRAPE
        status_msg.markdown("**🔍 Extracting product data...**")
        progress_bar.progress(10)
        
        result = scraper.scrape_product(ebay_url)
        
        if not result.success:
            status_msg.error(f"❌ Failed: {result.error_message}")
            progress_bar.empty()
            return
            
        progress_bar.progress(40)
        status_msg.markdown("**📁 Setting up project workspace...**")
        
        # FSYSOPS
        folder_path = file_manager.create_product_folder(result.product_data.title, result.product_data.item_id)
        result.folder_path = str(folder_path)
        
        file_manager.save_product_description_markdown(result.product_data, folder_path)
        file_manager.save_product_text(result.product_data, folder_path)
        file_manager.save_raw_scrape_text(result.product_data, folder_path)
        
        progress_bar.progress(60)
        status_msg.markdown(f"**📸 Downloading {len(result.image_urls)} high-res images...**")
        
        # IMAGES
        downloaded_images = []
        if result.image_urls:
            downloaded = file_manager.download_images(
                scraper, result.image_urls, folder_path,
                progress_callback=lambda c, t: progress_bar.progress(60 + int((c/t)*20))
            )
            downloaded_images = downloaded
        
        progress_bar.progress(85)
        status_msg.markdown("**📊 Updating databases...**")
        
        # DATABASE
        sheets_updated = False
        csv_updated = False
        
        # Sheets
        if sheets_manager.is_available() and not getattr(sheets_manager, 'quota_exceeded', False):
            try:
                sheets_updated = sheets_manager.append_to_ebay_product_list(result.product_data)
                if not sheets_updated:
                    sheets_updated = sheets_manager.append_product_data(result.product_data)
                # Status update
                sheets_manager.update_status_by_url(result.product_data.url, status="Done")
            except Exception as e:
                logger.error(f"Sheets update error: {e}")

        # CSV
        csv_updated = append_to_local_csv(result.product_data)

        progress_bar.progress(100)
        status_msg.markdown("✅ **Success! Processing Complete.**")
        time.sleep(1)
        status_msg.empty() # Clear status
        progress_bar.empty() # Clear progress
        
        # DISPLAY
        display_scraping_results(result, downloaded_images, folder_path, sheets_updated, csv_updated)
        
        # Confetti
        st.balloons()
        
    except Exception as e:
        status_msg.error(f"❌ An unexpected error occurred: {str(e)}")
        logger.error(f"Scrape handler error: {traceback.format_exc()}")

def main():
    """Main Streamlit application."""
    st.set_page_config(
        page_title="EBAY SCRAPER",
        layout="wide",
        initial_sidebar_state="expanded"
    )
    inject_global_styles()
    
    st.markdown("<div style='text-align: center; padding: 2rem 0; margin-bottom: 2rem;'><h1 style='color: #000000; font-size: 2.5rem; font-weight: 700; font-family: Arial, Helvetica, sans-serif; margin: 0;'>EBAY SCRAPER</h1></div>", unsafe_allow_html=True)
    
    # Initialize components
    try:
        scraper, sheets_manager, file_manager = initialize_components()
    except Exception as e:
        st.error(f"❌ Failed to initialize application: {e}")
        return
    
    # Sidebar configuration
    with st.sidebar:
        st.header("Configuration")
        
        # Google Sheets status
        if sheets_manager.is_available() and not getattr(sheets_manager, 'quota_exceeded', False):
            st.success("Google Sheets connected")
        else:

            st.info("Google Sheets unavailable (quota or connection). Using CSV only.")
        
        # Groq API configuration
        st.subheader("AI Processing")
        stored_key = load_groq_api_key()
        groq_api_key = st.text_input(
            "Groq API Key",
            value=stored_key,
            type="password",
            help="Required for AI content processing"
        )
        save_key = st.checkbox("Save API key to this project (persistent)", value=bool(groq_api_key))
        if save_key and groq_api_key and groq_api_key != stored_key:
            if save_groq_api_key(groq_api_key):
                st.success("API key saved locally")
            else:
                st.warning("Could not save API key locally")
        
        if groq_api_key:
            st.success("Groq API key set")
        else:
            st.info("Add API key for AI features")
    
    # Main application tabs
    tab1, tab2, tab3, tab4, tab5 = st.tabs(["Single Product", "Batch Processing", "AI Processing", "Image Enhancement", "Logs"])
    
    # Tab 1: Single Product Scraping
    with tab1:
        st.markdown("""
        <div style='background: linear-gradient(to right, #ffffff, #f9fafb); padding: 2rem; border-radius: 12px; border: 1px solid #e5e7eb; margin-bottom: 2rem; text-align: center;'>
            <h2 style='margin-bottom: 0.5rem; color: #111827;'>Find Product</h2>
            <p style='color: #6b7280; margin-bottom: 1.5rem;'>Paste an eBay URL to automatically extract data, download images, and update your records.</p>
        </div>
        """, unsafe_allow_html=True)

        col_search_1, col_search_2 = st.columns([4, 1])
        
        with col_search_1:
            ebay_url = st.text_input(
                "eBay Product URL",
                placeholder="https://www.ebay.com/itm/1234567890",
                label_visibility="collapsed"
            )

        with col_search_2:
            scrape_button = st.button(
                "Start Scraping",
                type="primary",
                use_container_width=True
            )
            
        if scrape_button:
            handle_single_product_scrape(ebay_url, scraper, file_manager, sheets_manager)
            
        # Recent/Footer info or features could go here
        st.write("")
        st.markdown("---")
        st.markdown("""
        <div style='text-align: center; color: #9ca3af; font-size: 0.85rem;'>
            Supports eBay.com listings using regular item format.
        </div>
        """, unsafe_allow_html=True)
    
    # Tab 2: Batch Processing
    with tab2:
        st.subheader("Batch Processing Operations")
        
        if not sheets_manager.is_available():
            st.warning("Google Sheets integration not available. Please configure service account credentials.")
            st.stop()
        
        # --- Batch Queue Status ---
        col_status_1, col_status_2 = st.columns([3, 1])
        with col_status_1:
            st.info("ℹ️ The batch queue is managed via your Google Sheet (**ebay_Product_List**). Rows with empty Status are processed.")
        with col_status_2:
            if st.button("🔄 Refresh Queue"):
                st.rerun()

        # --- Add New Items Section ---
        st.markdown("---")
        st.markdown("### 📥 Add Links to Batch")
        
        input_tab1, input_tab2 = st.tabs(["📁 File Upload (CSV/Excel)", "📝 Manual Paste"])
        
        new_urls_to_add = []
        source_note = "Batch Import"
        
        with input_tab1:
            uploaded_file = st.file_uploader("Upload File", type=['csv', 'xlsx', 'xls'], help="Upload a list of URLs")
            if uploaded_file:
                try:
                    df = None
                    if uploaded_file.name.endswith('.csv'):
                        df = pd.read_csv(uploaded_file)
                    else:
                        df = pd.read_excel(uploaded_file)
                    
                    if df is not None:
                        # Smart column detection
                        possible_cols = [c for c in df.columns if any(x in str(c).lower() for x in ['url', 'link', 'ebay', 'website'])]
                        target_col = possible_cols[0] if possible_cols else df.columns[0]
                        
                        st.caption(f"Reading URLs from column: `{target_col}`")
                        
                        raw_urls = df[target_col].dropna().astype(str).tolist()
                        new_urls_to_add.extend(raw_urls)
                        source_note = f"Import: {uploaded_file.name}"
                        
                except Exception as e:
                    st.error(f"Error reading file: {e}")

        with input_tab2:
            pasted_text = st.text_area("Paste eBay URLs (one per line)", height=200, placeholder="https://www.ebay.com/itm/...\nhttps://www.ebay.com/itm/...")
            if pasted_text:
                lines = [l.strip() for l in pasted_text.split('\n') if l.strip()]
                new_urls_to_add.extend(lines)
                if not source_note.startswith("Import"):
                    source_note = "Manual Paste"

        # --- Validation & Submission ---
        if new_urls_to_add:
            # Validate
            valid_urls = []
            for u in new_urls_to_add:
                # Basic cleaning
                u = u.strip()
                if u and scraper.validate_ebay_url(u):
                    valid_urls.append(u)
            
            # Deduplicate locally
            valid_urls = list(dict.fromkeys(valid_urls))
            
            if valid_urls:
                st.success(f"✅ Found {len(valid_urls)} valid eBay URLs ready to add.")
                
                if st.button(f"➕ Add {len(valid_urls)} Items to Queue", type="primary"):
                    try:
                        _, sheet_ws = sheets_manager.ensure_spreadsheet_and_worksheet(title='ebay_Product_List', worksheet_name='ebay_Product_List')
                        if sheet_ws:
                            # Get existing to prevent duplicates
                            existing_urls = set()
                            try:
                                all_vals = sheet_ws.get_all_values()
                                existing_urls = set(str(r).lower() for row in all_vals for r in row)
                            except: pass
                            
                            rows_to_add = []
                            h_map = sheets_manager._get_header_map(sheet_ws)
                            
                            # Determine column indices
                            col_url = h_map.get('ebayurl', h_map.get('url', 0))
                            col_status = h_map.get('status', 1)
                            col_notes = h_map.get('notes', 2)
                            
                            max_idx = max(col_url, col_status, col_notes, max(h_map.values()) if h_map else 5)
                            
                            added_count = 0
                            for url in valid_urls:
                                if url.lower() not in existing_urls:
                                    row = [''] * (max_idx + 1)
                                    row[col_url] = url
                                    row[col_status] = 'Pending'
                                    if col_notes: row[col_notes] = source_note
                                    
                                    rows_to_add.append(row)
                                    existing_urls.add(url.lower())
                                    added_count += 1
                            
                            if rows_to_add:
                                sheet_ws.append_rows(rows_to_add)
                                st.balloons()
                                st.toast(f"Added {added_count} new items to the batch queue!", icon="🚀")
                                time.sleep(1.5)
                                st.rerun()
                            else:
                                st.warning("All provided URLs are already in the batch list.")
                                
                    except Exception as e:
                        st.error(f"Failed to add to sheet: {e}")
            else:
                st.warning("No valid eBay URLs found in input.")

        # --- Processing Section ---
        st.markdown("---")
        st.markdown("### ⚙️ Processing Control")
        
        max_workers = st.slider("Max Concurrent Workers", min_value=1, max_value=8, value=3)
        
        # Check for pending items - use session state caching to avoid rate limits
        if 'pending_items_cache' not in st.session_state:
            st.session_state.pending_items_cache = []
            st.session_state.pending_items_last_fetch = 0
        
        pending_items = st.session_state.pending_items_cache
        
        # Only fetch from sheet when Refresh button is clicked
        col_refresh, col_info = st.columns([1, 3])
        with col_refresh:
            refresh_clicked = st.button("🔄 Refresh Queue", type="primary")
        with col_info:
            if st.session_state.pending_items_last_fetch:
                last_fetch_time = time.strftime('%H:%M:%S', time.localtime(st.session_state.pending_items_last_fetch))
                st.caption(f"Last refreshed: {last_fetch_time}")
        
        if refresh_clicked:
            try:
                _, sheet_worksheet = sheets_manager.ensure_spreadsheet_and_worksheet(title='ebay_Product_List', worksheet_name='ebay_Product_List', allow_create=False)
                if sheet_worksheet:
                    all_vals = sheet_worksheet.get_all_values()
                    pending_items = []
                    if len(all_vals) > 1:
                        header = all_vals[0]
                        # Simple mapper
                        h_map_clean = {k.lower().strip(): i for i, k in enumerate(header)}
                        u_idx = next((v for k, v in h_map_clean.items() if k in ['ebayurl', 'ebay_url', 'url', 'link']), None)
                        s_idx = next((v for k, v in h_map_clean.items() if k == 'status'), None)
                        
                        if u_idx is not None:
                            for i, row in enumerate(all_vals[1:]):
                                if len(row) > u_idx:
                                    u = row[u_idx]
                                    s = row[s_idx] if s_idx is not None and len(row) > s_idx else ''
                                    if u and scraper.validate_ebay_url(u) and (not s or s.lower() in ['pending', '']):
                                        pending_items.append({'row': i + 2, 'url': u})
                    
                    # Cache the results
                    st.session_state.pending_items_cache = pending_items
                    st.session_state.pending_items_last_fetch = time.time()
                    st.toast(f"Found {len(pending_items)} pending items!", icon="✅")
            except Exception as e:
                st.error(f"Error fetching pending items: {e}")

        st.metric("Pending Items in Queue", len(pending_items))

        # Process Button
        if pending_items:
            if st.button(f"🚀 Process {len(pending_items)} Items (Concurrent)", type="primary"):
                progress_container = st.container()
                status_container = st.empty()
                stop_event = threading.Event()
                stop_button = st.button("Stop Batch")
                
                # Sheet lock
                sheet_lock = threading.Lock()
                
                results_counter = {"success": 0, "fail": 0, "completed": 0}
                
                def process_url(item):
                    if stop_event.is_set(): return
                    
                    url = item['url']
                    try:
                        # 1. Update status to Processing (Thread safe?) 
                        # Ideally we batch updates or just do it optimistically. 
                        # For speed, skip the 'Processing' update or do it if low volume.
                        
                        # 2. Scrape
                        result = scraper.scrape_product(url)
                        
                        if result.success:
                            # 3. Save Data (File ops are generally thread safe if different folders)
                            folder_path = file_manager.create_product_folder(result.product_data.title, result.product_data.item_id)
                            file_manager.save_product_description_markdown(result.product_data, folder_path)
                            file_manager.save_product_text(result.product_data, folder_path)
                            file_manager.save_raw_scrape_text(result.product_data, folder_path)
                            
                            file_manager.download_images(scraper, result.image_urls, folder_path)
                            
                            # 4. Update Sheet & CSV (Critical Section)
                            with sheet_lock:
                                # Update the existing row with all product data
                                sheets_manager.update_row_with_product_data(url, result.product_data)
                                append_to_local_csv(result.product_data)
                                results_counter["success"] += 1
                        else:
                            with sheet_lock:
                                sheets_manager.update_status_by_url(url, f"Error: {result.error_message}")
                                results_counter["fail"] += 1
                                
                    except Exception as e:
                        logger.error(f"Batch worker error on {url}: {e}")
                        with sheet_lock:
                             try:
                                 sheets_manager.update_status_by_url(url, "Error: Exception")
                             except: pass
                             results_counter["fail"] += 1
                    finally:
                        results_counter["completed"] += 1
                        
                # Progress Bar Logic
                progress_bar = progress_container.progress(0.0)
                
                with ThreadPoolExecutor(max_workers=max_workers) as executor:
                    futures = [executor.submit(process_url, item) for item in pending_items]
                    
                    # Monitor loop
                    while not all(f.done() for f in futures):
                        if stop_button:
                            stop_event.set()
                            executor.shutdown(wait=False, cancel_futures=True)
                            st.warning("Stopping...")
                            break
                        
                        progress = results_counter["completed"] / len(pending_items)
                        progress_bar.progress(progress)
                        status_container.info(f"Completed: {results_counter['completed']}/{len(pending_items)} | Success: {results_counter['success']} | Failed: {results_counter['fail']}")
                        time.sleep(0.5)
                        
                    # Final update
                    progress_bar.progress(1.0)
                    status_container.success(f"Batch Finished! Success: {results_counter['success']}, Failed: {results_counter['fail']}")
                    st.toast("Batch processing completed!", icon="🎉")
                    time.sleep(2)
                    st.rerun()
        else:
            st.info("No pending items found in the sheet.")
    
    # Tab 3: AI Enhancement
    with tab3:
        # Header
        col_header_1, col_header_2 = st.columns([3, 1])
        with col_header_1:
            st.title("🤖 AI Content Studio")
            st.caption("Generate platform-optimized descriptions and chat with your product data.")
        
        if not groq_api_key:
            st.warning("⚠️ Please provide a Groq API key in the sidebar to use AI features.")
            st.stop()
        
        # Sub-tabs
        ai_tab1, ai_tab2 = st.tabs(["📝 Content Generator", "💬 AI Assistant"])
        
        # --- TAB 1: Content Generator ---
        with ai_tab1:
            product_folders = file_manager.get_existing_product_folders()
            
            if not product_folders:
                st.info("📂 No scraped products found. Go to the Single Product tab to scrape some data first.")
            else:
                # Layout: Input Sidebar (Left) vs Output (Right)
                col_input, col_output = st.columns([1, 1.5], gap="large")
                
                with col_input:
                    st.markdown("### 1. Select Content")
                    
                    # Smart Selection Logic
                    folder_names = [f["folder_name"] for f in product_folders]
                    selected_folder_name = st.selectbox("Product Folder", folder_names)
                    
                    folder_info = next((f for f in product_folders if f["folder_name"] == selected_folder_name), None)
                    
                    selected_file = None
                    if folder_info:
                        files = folder_info.get("text_files", [])
                        # Auto-select 'raw_scrape.txt' if available, else first file
                        default_idx = next((i for i, f in enumerate(files) if "raw_scrape.txt" in f), 0)
                        selected_file = st.selectbox("Source File", files, index=default_idx)
                    
                    st.markdown("### 2. Configure")
                    target_platform = st.selectbox(
                        "Target Platform",
                        ["General", "eBay", "Poshmark", "Mercari", "Depop", "Etsy", "Facebook Marketplace", "Shopify", "Vinted", "Grailed"],
                        help="Optimizes tone, structure, and length for this platform."
                    )
                    
                    with st.expander("Advanced Instructions", expanded=False):
                        custom_instructions = st.text_area(
                            "Custom Rules",
                            placeholder="e.g. 'Use emojis', 'Focus on flaws', 'Short & punchy'",
                            height=80
                        )
                    
                    st.divider()
                    
                    generate_btn = st.button("✨ Generate Description", type="primary", use_container_width=True)
                
                with col_output:
                    st.markdown("### 3. Result")
                    # Placeholder or Result
                    if "ai_generated_result" not in st.session_state:
                         st.session_state.ai_generated_result = None
                    
                    if generate_btn and folder_info and selected_file:
                        try:
                            # Load Content
                            original_content = file_manager.load_product_text(folder_info["folder_path"], selected_file)
                            if not original_content:
                                st.error("Empty source file.")
                            else:
                                with st.spinner(f"🔍 Analyzing and rewriting for {target_platform}..."):
                                    groq_processor = GroqProcessor(groq_api_key)
                                    result_text = groq_processor.platform_agent.generate_platform_description(
                                        raw_text=original_content,
                                        product_data=None, # Loading full object is harder here, raw text is usually enough
                                        platform=target_platform,
                                        custom_instructions=custom_instructions
                                    )
                                    st.session_state.ai_generated_result = {
                                        "text": result_text,
                                        "platform": target_platform,
                                        "timestamp": datetime.now().strftime("%H:%M")
                                    }
                                    
                                    # Save to file
                                    out_name = f"{selected_folder_name}_{target_platform}_listing.txt"
                                    out_path = Path(folder_info["folder_path"]) / out_name
                                    with open(out_path, 'w', encoding='utf-8') as f:
                                        f.write(result_text)
                                    st.toast(f"Saved to {out_name}", icon="💾")
                                    
                        except Exception as e:
                            st.error(f"Generation failed: {e}")
                    
                    # Display Result
                    res = st.session_state.ai_generated_result
                    if res:
                        st.markdown(f"**Generated for {res['platform']} at {res['timestamp']}**")
                        st.text_area("Final Output", value=res['text'], height=500)
                        col_d1, col_d2 = st.columns(2)
                        with col_d1:
                            st.download_button("📥 Download .txt", data=res['text'], file_name=f"listing_{res['platform']}.txt")
                    else:
                        st.info("👈 Select a product and click Generate to see the magic happen.")
        
        # AI Tab 2: ChatGPT-style Chatbot with streaming
        with ai_tab2:
            # Initialize session state for chat
            if 'chat_sessions' not in st.session_state:
                st.session_state.chat_sessions = {}
            if 'active_session' not in st.session_state:
                st.session_state.active_session = 'default'
            if 'default' not in st.session_state.chat_sessions:
                st.session_state.chat_sessions['default'] = {
                    'name': 'General Chat',
                    'messages': [],
                    'created': datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                }
            
            # Sidebar for session management (using columns since we're in a tab)
            st.markdown("""
            <style>
            /* ChatGPT-style chat interface */
            .chat-container {
                display: flex;
                flex-direction: column;
                height: 600px;
                max-height: 600px;
                border: 1px solid #e5e7eb;
                border-radius: 8px;
                overflow: hidden;
                background: #ffffff;
            }
            .chat-messages {
                flex: 1;
                overflow-y: auto;
                padding: 1rem;
                background: #fafafa;
                max-height: 480px;
                min-height: 480px;
            }
            .chat-messages::-webkit-scrollbar {
                width: 6px;
            }
            .chat-messages::-webkit-scrollbar-track {
                background: #f1f1f1;
                border-radius: 3px;
            }
            .chat-messages::-webkit-scrollbar-thumb {
                background: #cbd5e1;
                border-radius: 3px;
            }
            .chat-messages::-webkit-scrollbar-thumb:hover {
                background: #94a3b8;
            }
            .chat-message {
                margin-bottom: 0.25rem;
                padding: 0.15rem 0;
                animation: fadeIn 0.15s ease-in;
            }
            .chat-message.user {
                padding-bottom: 0.15rem;
            }
            .chat-message.assistant {
                padding-bottom: 0.25rem;
                border-bottom: 1px solid #e5e7eb;
            }
            .chat-header {
                display: flex;
                justify-content: space-between;
                align-items: center;
                margin-bottom: 0.15rem;
                font-size: 0.75rem;
            }
            .chat-role {
                display: flex;
                align-items: center;
                gap: 0.4rem;
                font-weight: 600;
                color: #374151;
            }
            .chat-role svg {
                width: 16px;
                height: 16px;
                flex-shrink: 0;
            }
            .chat-content {
                color: #1f2937;
                line-height: 1.35;
                white-space: pre-wrap;
                word-wrap: break-word;
                font-size: 0.9rem;
                margin-left: 20px;
                margin-bottom: 0;
            }
            .chat-actions {
                display: flex;
                gap: 0.5rem;
                margin-left: 20px;
                margin-top: 0.15rem;
            }
            .action-btn {
                display: inline-flex;
                align-items: center;
                gap: 0.25rem;
                padding: 0.25rem 0.5rem;
                background: #ffffff;
                border: 1px solid #e5e7eb;
                border-radius: 4px;
                font-size: 0.75rem;
                color: #6b7280;
                cursor: pointer;
                transition: all 0.2s;
            }
            .action-btn:hover {
                background: #f9fafb;
                border-color: #d1d5db;
                color: #374151;
            }
            .action-btn svg {
                width: 14px;
                height: 14px;
            }
            .action-btn.active {
                background: #10b981;
                border-color: #10b981;
                color: #ffffff;
            }
            .action-btn.negative {
                background: #ef4444;
                border-color: #ef4444;
                color: #ffffff;
            }
            .streaming-cursor {
                display: inline-block;
                width: 2px;
                height: 14px;
                background: #10b981;
                animation: blink 1s infinite;
                margin-left: 2px;
            }
            @keyframes blink {
                0%, 50% { opacity: 1; }
                51%, 100% { opacity: 0; }
            }
            @keyframes fadeIn {
                from { opacity: 0; }
                to { opacity: 1; }
            }
            .chat-input-area {
                background: #ffffff;
                padding: 0.5rem;
                border-top: 1px solid #e5e7eb;
            }
            .session-badge {
                display: inline-block;
                padding: 0.1rem 0.3rem;
                background: #f3f4f6;
                border-radius: 3px;
                font-size: 0.65rem;
                color: #9ca3af;
                margin-left: 0.2rem;
                font-weight: normal;
            }
            .chat-meta {
                font-size: 0.65rem;
                color: #9ca3af;
                font-weight: normal;
            }
            </style>
            """, unsafe_allow_html=True)
            
            st.markdown("<hr style='margin: 0.5rem 0; border: none; border-top: 1px solid #e5e7eb;'>", unsafe_allow_html=True)


        # --- TAB 2: AI Assistant (Native UI) ---
        with ai_tab2:
            # 1. Context Manager (Top Bar)
            with st.container():
                c1, c2 = st.columns([1, 2])
                with c1:
                    st.markdown("### 🤖 AI Assistant")
                with c2:
                    # Compact context selector
                    product_folders = file_manager.get_existing_product_folders()
                    context_options = ["General (No Context)"] + [f["folder_name"] for f in product_folders]
                    
                    selected_context = st.selectbox(
                        "Product Context",
                        options=context_options,
                        label_visibility="collapsed",
                        help="Select a product to chat about"
                    )

            st.divider()

            # 2. Chat Logic
            if "chat_sessions" not in st.session_state:
                st.session_state.chat_sessions = {0: {"messages": []}}
                st.session_state.active_session = 0
            
            session = st.session_state.chat_sessions[st.session_state.active_session]
            
            # Welcome Screen (if empty)
            if not session['messages']:
                st.markdown("""
                <div style='text-align: center; margin: 3rem 0; color: #4b5563;'>
                    <h3>👋 How can I help you?</h3>
                    <p>I can rewrite descriptions, analyze prices, or give you marketing ideas.</p>
                </div>
                """, unsafe_allow_html=True)
                
                # Preset Questions
                col_q1, col_q2, col_q3 = st.columns(3)
                with col_q1:
                    if st.button("📝 Rewrite Description", use_container_width=True):
                        # We can't auto-submit to chat_input easily in Streamlit, 
                        # so we append to history to trigger "simulated" user message
                         session['messages'].append({"user": "Rewrite the current product description to be more professional.", "assistant": None})
                         st.rerun()
                with col_q2:
                    if st.button("📊 Price Analysis", use_container_width=True):
                         session['messages'].append({"user": "Analyze the pricing strategy for this item.", "assistant": None})
                         st.rerun()
                with col_q3:
                     if st.button("🏷️ Generate Tags", use_container_width=True):
                         session['messages'].append({"user": "Suggest 10 relevant SEO tags for this product.", "assistant": None})
                         st.rerun()

            # Display History
            for msg in session['messages']:
                # User
                with st.chat_message("user"):
                    st.write(msg['user'])
                
                # Assistant
                if msg.get('assistant') is not None:
                    with st.chat_message("assistant"):
                        st.write(msg['assistant'])
                        # Copy Button using native Streamlit
                        copy_key = f"copy_{abs(hash(msg['assistant']))}"
                        if copy_key not in st.session_state:
                            st.session_state[copy_key] = False
                        
                        col_copy, col_spacer = st.columns([1, 5])
                        with col_copy:
                            if st.button("📋 Copy", key=copy_key + "_btn", type="secondary"):
                                st.session_state[copy_key] = True
                                st.toast("✅ Copied to clipboard!", icon="✅")
                        
                        # Show the copyable text in an expander if user wants to manually copy
                        if st.session_state[copy_key]:
                            st.code(msg['assistant'], language=None)
                            st.session_state[copy_key] = False  # Reset after showing
                
                # (Note: Streamlit runs the script top-down. 
                # If we just appended a user msg with None assistant, it renders User message, 
                # then we detect the pending reply logic below)

            # 3. Handle Pending AI Response (from preset buttons or previous interaction if interrupted)
            # Check if last message needs a response
            if session['messages'] and session['messages'][-1]['assistant'] is None:
                with st.chat_message("assistant"):
                    with st.spinner("Thinking..."):
                        try:
                            # Prepare context
                            ctx_text = ""
                            if selected_context and selected_context != "General (No Context)":
                                folder_info = next((f for f in product_folders if f["folder_name"] == selected_context), None)
                                if folder_info:
                                    # Load raw text
                                    raw_f = folder_info.get("text_files", [])
                                    target_f = "raw_scrape.txt" if "raw_scrape.txt" in raw_f else (raw_f[0] if raw_f else None)
                                    if target_f:
                                        content = file_manager.load_product_text(folder_info["folder_path"], target_f)
                                        ctx_text = f"\n\nCONTEXT:\n{content[:4000]}"
                            
                            # API Call
                            groq = GroqProcessor(groq_api_key)
                            
                            system_prompt = (
                                "You are a top-tier E-commerce Manager and Copywriting Expert for this eBay Store project. "
                                "Your goal is to maximize sales and save the user time. "
                                "1. Be highly specific and actionable. Avoid generic advice. "
                                "2. If the user asks about a specific product, use the provided CONTEXT to give precise answers. "
                                "3. If asking for a rewrite, produce the FINAL output immediately (no 'Here is the rewrite' chatter). "
                                "4. Keep answers concise but comprehensive. Speed is key. "
                                "5. You have access to the user's scraped product data context when provided."
                            )
                            
                            prompt = session['messages'][-1]['user'] + ctx_text
                            
                            response_stream = groq.client.chat.completions.create(
                                model=groq.model,
                                messages=[
                                    {"role": "system", "content": system_prompt},
                                    {"role": "user", "content": prompt}
                                ],
                                stream=True
                            )
                            
                            # Stream Output
                            def stream_generator():
                                for chunk in response_stream:
                                    if chunk.choices[0].delta.content is not None:
                                        yield chunk.choices[0].delta.content
                                        
                            full_response = st.write_stream(stream_generator())
                            
                            # Save to history
                            session['messages'][-1]['assistant'] = full_response
                            st.rerun() # Rerun to solidify the state
                            
                        except Exception as e:
                            st.error(f"Error: {e}")
            
            # 4. Input (Pinned to bottom)
            if query := st.chat_input("Ask about your products..."):
                # Append user message
                session['messages'].append({"user": query, "assistant": None})
                st.rerun() # Force rerun to display user message immediately and trigger response logic above

#     # Tab 4: Image Enhancement
#     with tab4:
#         # Clean modern header
#         st.markdown("""
#         <div style='margin-bottom: 2rem;'>
#             <h2 style='color: #000000; font-size: 1.75rem; font-weight: 700; margin-bottom: 0.5rem;'>Image Enhancement</h2>
#             <p style='color: #6b7280; font-size: 1rem; margin: 0;'>Select a folder, choose images, adjust enhancements, and optionally add your logo.</p>
#         </div>
#         """, unsafe_allow_html=True)

#         # Folder selection via dropdowns for better UX
#         st.markdown("<h3 style='color: #000000; font-size: 1.25rem; font-weight: 600; margin-bottom: 1rem; margin-top: 1.5rem;'>📁 Select Folders</h3>", unsafe_allow_html=True)
#         col_folder, col_logo = st.columns([2, 1])
#         with col_folder:
#             # Offer common folders under downloads plus manual typing
#             available_folders = [str(p) for p in file_manager.list_image_folders()]
#             default_folder = str(Path.cwd() / BASE_SAVE_DIR)
#             if default_folder not in available_folders:
#                 available_folders.insert(0, default_folder)
#             base_folder = st.selectbox(
#                 "Select Input Images Folder",
#                 options=available_folders,
#                 index=0
#             )
#         with col_logo:
#             # Logo folder dropdown
#             logos_dir = Path.cwd() / 'logos'
#             logos_path = Path(r'C:\Users\Pret\Downloads\EbayStore\logos')
#             if logos_path.exists():
#                 logos_dir = logos_path
#             logo_files = []
#             try:
#                 logo_files = [p for p in logos_dir.iterdir() if p.suffix.lower() in {'.png', '.webp', '.jpg', '.jpeg'}]
#             except Exception:
#                 logo_files = []
#             logo_names = [p.name for p in logo_files]
#             default_logo = 'transparent.png'
#             default_idx = logo_names.index(default_logo) if default_logo in logo_names else 0 if logo_names else 0
#             selected_logo_name = st.selectbox(
#                 "Select Logo (optional)",
#                 options=logo_names if logo_names else [""],
#                 index=default_idx if logo_names else 0
#             )
#             logo_path_str = str(logos_dir / selected_logo_name) if selected_logo_name else ""

#         # Divider
#         st.markdown("""
#         <hr style='margin: 1.5rem 0; border: none; border-top: 2px solid #e5e7eb;'>
#         """, unsafe_allow_html=True)

#         # List images in folder
#         image_files = []
#         try:
#             folder_path = Path(base_folder)("� Vestiaire", use_container_width=True):
#                     st.session_state.chat_prompt = "Create a comprehensive luxury description for Vestiaire Collective that's professional and highlights authenticity, craftsmanship, and condition. Include all relevant details about materials, dimensions, and unique features. Minimum 250 words."
#             with col_q3:
#                 if st.button("🏷️ eBay", use_container_width=True):
#                     st.session_state.chat_prompt = "Write a detailed eBay listing with complete product information, specifications, condition description, shipping details, and returns policy. Be thorough and professional. At least 300 words."
#             with col_q4:
#                 if st.button("📱 Instagram", use_container_width=True):
#                     st.session_state.chat_prompt = "Create an Instagram caption with emojis, engaging story, product highlights, and 15-20 relevant hashtags. Make it fun and shareable."
            
#             # Context selection
#             st.markdown("<h4 style='color: #000000; font-size: 1.1rem; font-weight: 600; margin-top: 1.5rem; margin-bottom: 1rem;'>🗂️ Add Context (Optional)</h4>", unsafe_allow_html=True)
            
#             col_ctx1, col_ctx2 = st.columns([1, 2])
            
#             with col_ctx1:
#                 use_context = st.checkbox("Use product folder as context", value=False)
            
#             with col_ctx2:
#                 selected_context_folder = None
#                 if use_context:
#                     product_folders = file_manager.get_existing_product_folders()
#                     if product_folders:
#                         selected_context_folder = st.selectbox(
#                             "Select folder:",
#                             options=[f["folder_name"] for f in product_folders],
#                             label_visibility="collapsed"
#                         )
            
#             st.markdown("<hr style='margin: 1.5rem 0; border: none; border-top: 2px solid #e5e7eb;'>", unsafe_allow_html=True)
            
#             # Chat input area
#             st.markdown("<h4 style='color: #000000; font-size: 1.1rem; font-weight: 600; margin-bottom: 1rem;'>💭 Your Message</h4>", unsafe_allow_html=True)
            
#             user_message = st.text_area(
#                 "Message",
#                 value=st.session_state.get('chat_prompt', ''),
#                 placeholder="Ask anything: 'Write a detailed description for this Louis Vuitton bag' or 'Generate email response to customer question about shipping'...",
#                 height=120,
#                 label_visibility="collapsed"
#             )
            
#             # Clear prompt after use
#             if 'chat_prompt' in st.session_state:
#                 del st.session_state.chat_prompt
            
#             col_send1, col_send2 = st.columns([3, 1])
            
#             with col_send1:
#                 send_button = st.button("📤 Send Message", type="primary", use_container_width=True)
            
#             with col_send2:
#                 words_target = st.number_input("Min words", min_value=50, max_value=1000, value=200, step=50, label_visibility="collapsed", help="Minimum word count for AI response")
            
#             # Process message
#             if send_button and user_message.strip():
#                 try:
#                     groq_processor = GroqProcessor(groq_api_key)
                    
#                     # Build context if folder selected
#                     context_text = ""
#                     if use_context and selected_context_folder:
#                         product_folders = file_manager.get_existing_product_folders()
#                         folder_info = next((f for f in product_folders if f["folder_name"] == selected_context_folder), None)
#                         if folder_info and folder_info.get("text_files"):
#                             raw_file = "raw_scrape.txt" if "raw_scrape.txt" in folder_info["text_files"] else folder_info["text_files"][0]
#                             raw_content = file_manager.load_product_text(
#                                 folder_info["folder_path"], raw_file
#                             )
#                             context_text = f"\n\nPRODUCT CONTEXT:\n{raw_content[:3000]}"
                    
#                     # Enhanced prompt for comprehensive responses
#                     enhanced_prompt = f"""{user_message}

# IMPORTANT INSTRUCTIONS:
# - Provide a COMPLETE and DETAILED response (minimum {words_target} words)
# - Include ALL relevant information, specifications, and details
# - Be thorough and comprehensive - don't cut corners
# - Use professional language and proper formatting
# - If describing a product, include: condition, materials, dimensions, features, care instructions
# - Make it ready to use without needing editing{context_text}"""
                    
#                     # Get AI response with spinner
#                     with st.spinner("🤖 AI is crafting a comprehensive response..."):
#                         ai_response = groq_processor.client.chat.completions.create(
#                             model=groq_processor.model,
#                             messages=[
#                                 {"role": "system", "content": "You are a professional product description writer and e-commerce expert. You create detailed, comprehensive, and engaging content that is ready to publish. Always provide complete responses with all necessary details. Never provide short or incomplete responses."},
#                                 {"role": "user", "content": enhanced_prompt}
#                             ],
#                             temperature=0.7,
#                             max_tokens=4000
#                         )
                        
#                         ai_text = ai_response.choices[0].message.content.strip()
                        
#                         # Check word count
#                         word_count = len(ai_text.split())
                        
#                         # Add to chat history
#                         current_session = st.session_state.chat_sessions[st.session_state.active_session]
#                         current_session['messages'].append({
#                             'user': user_message,
#                             'ai': ai_text,
#                             'timestamp': datetime.now().strftime("%H:%M:%S"),
#                             'word_count': word_count,
#                             'context_used': selected_context_folder if use_context else None
#                         })
                        
#                         st.rerun()
                        
#                 except Exception as e:
#                     st.error(f"❌ Chat error: {e}")
#                     logger.error(f"Chat error: {traceback.format_exc()}")
            
#             # Display chat history
#             st.markdown("<hr style='margin: 2rem 0; border: none; border-top: 2px solid #e5e7eb;'>", unsafe_allow_html=True)
#             st.markdown("<h4 style='color: #000000; font-size: 1.1rem; font-weight: 600; margin-bottom: 1rem;'>📜 Conversation History</h4>", unsafe_allow_html=True)
            
#             current_session = st.session_state.chat_sessions[st.session_state.active_session]
            
#             if not current_session['messages']:
#                 st.markdown("""
#                 <div style='background: #f9fafb; padding: 2rem; border-radius: 8px; text-align: center; border: 2px dashed #d1d5db;'>
#                     <p style='color: #6b7280; margin: 0; font-size: 0.95rem;'>💬 No messages yet. Start a conversation!</p>
#                 </div>
#                 """, unsafe_allow_html=True)
#             else:
#                 # Display messages in reverse order (newest first)
#                 for idx, msg in enumerate(reversed(current_session['messages'])):
#                     # User message
#                     st.markdown(f"""
#                     <div style='background: #eff6ff; padding: 1rem; border-radius: 8px; margin-bottom: 0.5rem; border-left: 4px solid #3b82f6;'>
#                         <div style='display: flex; justify-content: space-between; margin-bottom: 0.5rem;'>
#                             <strong style='color: #000000;'>👤 You</strong>
#                             <span style='color: #6b7280; font-size: 0.85rem;'>{msg['timestamp']}</span>
#                         </div>
#                         <p style='color: #374151; margin: 0; font-size: 0.95rem; white-space: pre-wrap;'>{msg['user']}</p>
#                     </div>
#                     """, unsafe_allow_html=True)
                    
#                     # AI response
#                     context_badge = f" | 📁 {msg['context_used']}" if msg.get('context_used') else ""
                    
#                     st.markdown(f"""
#                     <div style='background: #f0fdf4; padding: 1rem; border-radius: 8px; margin-bottom: 1.5rem; border-left: 4px solid #10b981;'>
#                         <div style='display: flex; justify-content: space-between; margin-bottom: 0.5rem;'>
#                             <strong style='color: #000000;'>🤖 AI Assistant</strong>
#                             <span style='color: #6b7280; font-size: 0.85rem;'>{msg['word_count']} words{context_badge}</span>
#                         </div>
#                         <div style='color: #374151; font-size: 0.95rem; white-space: pre-wrap; line-height: 1.6;'>{msg['ai']}</div>
#                     </div>
#                     """, unsafe_allow_html=True)
                    
#                     # Download button for AI response
#                     col_dl1, col_dl2, col_dl3 = st.columns([2, 1, 1])
#                     with col_dl1:
#                         st.download_button(
#                             label=f"💾 Download Response #{len(current_session['messages']) - idx}",
#                             data=msg['ai'],
#                             file_name=f"ai_response_{st.session_state.active_session}_{len(current_session['messages']) - idx}.txt",
#                             mime="text/plain",
#                             key=f"download_{st.session_state.active_session}_{idx}"
#                         )
                
#                 # Clear all history button
#                 st.markdown("<div style='margin-top: 2rem;'></div>", unsafe_allow_html=True)
#                 if st.button("🗑️ Clear All Chat History", use_container_width=True, type="secondary"):
#                     current_session['messages'] = []
#                     st.rerun()

    # Tab 4: Image Enhancement
    with tab4:
        # Clean modern header
        st.markdown("""
        <div style='margin-bottom: 2rem;'>
            <h2 style='color: #000000; font-size: 1.75rem; font-weight: 700; margin-bottom: 0.5rem;'>Image Enhancement</h2>
            <p style='color: #6b7280; font-size: 1rem; margin: 0;'>Select a folder, choose images, adjust enhancements, and optionally add your logo.</p>
        </div>
        """, unsafe_allow_html=True)

        # Folder selection via dropdowns for better UX
        st.markdown("<h3 style='color: #000000; font-size: 1.25rem; font-weight: 600; margin-bottom: 1rem; margin-top: 1.5rem;'>📁 Select Folders</h3>", unsafe_allow_html=True)
        col_folder, col_logo = st.columns([2, 1])
        with col_folder:
            # Offer common folders under downloads plus manual typing
            available_folders = [str(p) for p in file_manager.list_image_folders()]
            default_folder = str(Path.cwd() / BASE_SAVE_DIR)
            if default_folder not in available_folders:
                available_folders.insert(0, default_folder)
            base_folder = st.selectbox(
                "Select Input Images Folder",
                options=available_folders,
                index=0
            )
        with col_logo:
            # Logo upload instead of folder selection (works for deployed apps)
            st.markdown("**Upload Logo (optional)**")
            uploaded_logo = st.file_uploader(
                "Upload your logo",
                type=['png', 'jpg', 'jpeg', 'webp'],
                label_visibility="collapsed",
                help="Upload a logo to watermark your images"
            )
            
            # Store uploaded logo in session state
            logo_image = None
            if uploaded_logo is not None:
                try:
                    from PIL import Image
                    logo_image = Image.open(uploaded_logo)
                    st.image(logo_image, caption="Logo Preview", width=100)
                except Exception as e:
                    st.error(f"Error loading logo: {e}")

        # Quick Presets Section
        st.markdown("""
        <div style='margin-top: 2rem; margin-bottom: 1rem;'>
            <h3 style='color: #000000; font-size: 1.25rem; font-weight: 600; margin-bottom: 0.5rem;'>⚡ Quick Presets</h3>
            <p style='color: #6b7280; font-size: 0.9rem; margin: 0;'>One-click settings for common use cases</p>
        </div>
        """, unsafe_allow_html=True)
        
        # Initialize session state for preset values
        if 'img_brightness' not in st.session_state:
            st.session_state.img_brightness = 1.05
            st.session_state.img_contrast = 1.10
            st.session_state.img_sharpness = 1.10
            st.session_state.img_saturation = 1.05
        
        col_preset1, col_preset2, col_preset3, col_preset4 = st.columns(4)
        with col_preset1:
            if st.button("🛒 eBay Ready", use_container_width=True, help="Clean, bright images for eBay listings"):
                st.session_state.img_brightness = 1.10
                st.session_state.img_contrast = 1.15
                st.session_state.img_sharpness = 1.20
                st.session_state.img_saturation = 1.05
                st.rerun()
        with col_preset2:
            if st.button("📸 Instagram", use_container_width=True, help="Vibrant, eye-catching images for social"):
                st.session_state.img_brightness = 1.05
                st.session_state.img_contrast = 1.20
                st.session_state.img_sharpness = 1.15
                st.session_state.img_saturation = 1.25
                st.rerun()
        with col_preset3:
            if st.button("✨ Professional", use_container_width=True, help="Neutral, premium look"):
                st.session_state.img_brightness = 1.02
                st.session_state.img_contrast = 1.08
                st.session_state.img_sharpness = 1.25
                st.session_state.img_saturation = 0.98
                st.rerun()
        with col_preset4:
            if st.button("🔄 Reset", use_container_width=True, help="Reset to default values"):
                st.session_state.img_brightness = 1.0
                st.session_state.img_contrast = 1.0
                st.session_state.img_sharpness = 1.0
                st.session_state.img_saturation = 1.0
                st.rerun()

        # Enhancement Settings Section (Manual Fine-tuning)
        st.markdown("""
        <div style='margin-top: 2rem; margin-bottom: 1rem;'>
            <h3 style='color: #000000; font-size: 1.25rem; font-weight: 600; margin-bottom: 0.5rem;'>🎨 Fine-tune Settings</h3>
            <p style='color: #6b7280; font-size: 0.9rem; margin: 0;'>Manually adjust brightness, contrast, sharpness, and saturation</p>
        </div>
        """, unsafe_allow_html=True)
        
        col_b, col_c, col_s, col_sat = st.columns(4)
        with col_b:
            brightness = st.slider("☀️ Brightness", 0.1, 2.5, st.session_state.img_brightness, 0.01, key="brightness_slider")
        with col_c:
            contrast = st.slider("◐ Contrast", 0.1, 2.5, st.session_state.img_contrast, 0.01, key="contrast_slider")
        with col_s:
            sharpness = st.slider("🔍 Sharpness", 0.1, 3.0, st.session_state.img_sharpness, 0.01, key="sharpness_slider")
        with col_sat:
            saturation = st.slider("🎨 Saturation", 0.1, 2.5, st.session_state.img_saturation, 0.01, key="saturation_slider")

        # Logo Watermark Settings Section
        st.markdown("""
        <div style='margin-top: 2rem; margin-bottom: 1rem;'>
            <h3 style='color: #000000; font-size: 1.25rem; font-weight: 600; margin-bottom: 0.5rem;'>🏷️ Logo Watermark Settings</h3>
            <p style='color: #6b7280; font-size: 0.9rem; margin: 0;'>Configure logo size, position, and opacity</p>
        </div>
        """, unsafe_allow_html=True)
        
        col_logo1, col_logo2, col_logo3 = st.columns(3)
        with col_logo1:
            logo_ratio = st.slider("Logo Size Ratio", 0.02, 0.40, 0.15, 0.01)
            logo_margin = st.number_input("Logo Margin (px)", min_value=0, max_value=200, value=10, step=1)
        with col_logo2:
            logo_position = st.selectbox(
                "Logo Position",
                options=["bottom-right", "bottom-left", "top-right", "top-left", "center"],
                index=0
            )
        with col_logo3:
            logo_opacity = st.slider("Logo Opacity", 0.1, 1.0, 1.0, 0.05)

        # Image Selection Section
        st.markdown("""
        <div style='margin-top: 2rem; margin-bottom: 1rem;'>
            <h3 style='color: #000000; font-size: 1.25rem; font-weight: 600; margin-bottom: 0.5rem;'>🖼️ Image Selection</h3>
        </div>
        """, unsafe_allow_html=True)

        # List images in folder
        image_files = []
        try:
            folder_path = Path(base_folder)
            if folder_path.exists() and folder_path.is_dir():
                image_files = file_manager.list_images(folder_path)
        except Exception:
            image_files = []

        if not image_files:
            st.markdown("""
            <div style='background: #eff6ff; padding: 1rem 1.25rem; border-radius: 8px; border-left: 4px solid #3b82f6; margin: 1rem 0;'>
                <p style='color: #000000; margin: 0; font-size: 0.95rem;'>📂 No images found in the specified folder.</p>
            </div>
            """, unsafe_allow_html=True)
        else:
            st.markdown(f"""
            <div style='background: #f0fdf4; padding: 1rem 1.25rem; border-radius: 8px; border-left: 4px solid #10b981; margin: 1rem 0;'>
                <p style='color: #000000; margin: 0; font-size: 0.95rem; font-weight: 600;'>✅ Found {len(image_files)} images ready to process</p>
            </div>
            """, unsafe_allow_html=True)
            
            file_names = [p.name for p in image_files]
            selections = st.multiselect("Select images to process", options=file_names, default=file_names)

            out_subdir = st.text_input("Output Subfolder Name", value="Enhanced")
            
            st.markdown("<div style='margin-top: 1.5rem;'></div>", unsafe_allow_html=True)
            col_process, col_preview = st.columns([1, 1])
            with col_process:
                process_btn = st.button("🚀 Enhance Selected Images", type="primary", use_container_width=True)
            with col_preview:
                preview_btn = st.button("👁️ Preview Settings", type="secondary", use_container_width=True)
            
            # Preview functionality
            if preview_btn and selections:
                try:
                    # Preview first selected image
                    preview_img_path = next(p for p in image_files if p.name == selections[0])
                    preview_img = file_manager.enhance_image(
                        preview_img_path, brightness, contrast, sharpness, saturation
                    )
                    
                    # Apply logo if uploaded
                    if logo_image is not None:
                        preview_img = file_manager.overlay_logo_pil(
                            preview_img, logo_image, 
                            size_ratio=logo_ratio, 
                            margin=int(logo_margin),
                            position=logo_position,
                            opacity=logo_opacity
                        )
                    
                    st.image(preview_img, caption="Preview with current settings", use_container_width=True)
                except Exception as e:
                    st.error(f"Preview error: {e}")

            # Process images with progress tracking
            if process_btn and selections:
                try:
                    output_root = folder_path / out_subdir
                    
                    # Filter selected images
                    selected_image_paths = [p for p in image_files if p.name in selections]
                    
                    # Progress tracking
                    progress_bar = st.progress(0)
                    status_text = st.empty()
                    
                    def update_progress(current, total):
                        progress_bar.progress(current / total)
                        status_text.text(f"Processing image {current}/{total}...")
                    
                    # Batch process with progress
                    processed_paths = file_manager.batch_process_images(
                        image_paths=selected_image_paths,
                        output_folder=output_root,
                        logo_image=logo_image,
                        brightness=brightness,
                        contrast=contrast,
                        sharpness=sharpness,
                        saturation=saturation,
                        logo_size_ratio=logo_ratio,
                        logo_margin=int(logo_margin),
                        logo_position=logo_position,
                        logo_opacity=logo_opacity,
                        progress_callback=update_progress
                    )
                    
                    # Complete progress
                    progress_bar.progress(1.0)
                    status_text.text("Processing complete!")
                    
                    st.success(f"✅ Successfully processed {len(processed_paths)} images!")
                    st.info(f"📁 Output folder: {output_root}")
                    
                    # Show sample of processed images
                    if processed_paths:
                        with st.expander("View Processed Images"):
                            cols = st.columns(min(3, len(processed_paths)))
                            for idx, img_path in enumerate(processed_paths[:6]):  # Show max 6 images
                                with cols[idx % 3]:
                                    try:
                                        st.image(str(img_path), caption=img_path.name, use_container_width=True)
                                    except Exception:
                                        pass
                                        
                except Exception as e:
                    st.error(f"❌ Image enhancement error: {e}")
                    logger.error(f"Image enhancement error: {traceback.format_exc()}")

    # Tab 5: Logs
    with tab5:
        st.subheader("📝 System Logs")
        
        col_l1, col_l2 = st.columns([4, 1])
        with col_l1:
            log_lines = 50
        with col_l2:
            if st.button("🔄 Refresh Logs"):
                st.rerun()
                
        try:
            if os.path.exists(log_filename):
                with open(log_filename, "r", encoding='utf-8') as f:
                    lines = f.readlines()
                    last_lines = lines[-50:]
                    log_content = "".join(last_lines)
                    st.code(log_content, language="text")
                    
                with open(log_filename, "rb") as f:
                    st.download_button("💾 Download Full Log", f, file_name="ebay_scraper.log")
            else:
                st.info("No logs found yet.")
        except Exception as e:
            st.error(f"Error reading logs: {e}")
            
    # Footer
    st.markdown("---")
    st.markdown("---")
    col1, col2 = st.columns([1, 1])
    
    with col1:
        # Zip Download Feature
        if st.button("📥 Download All Data (ZIP)"):
            with st.spinner("Zipping files..."):
                try:
                    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
                    zip_path = Path.cwd() / f"ebay_data_{timestamp}"
                    shutil.make_archive(str(zip_path), 'zip', Path.cwd() / BASE_SAVE_DIR)
                    
                    with open(f"{zip_path}.zip", "rb") as f:
                        st.download_button(
                            label="💾 Confirm Download",
                            data=f,
                            file_name=f"ebay_data_{timestamp}.zip",
                            mime="application/zip"
                        )
                    st.success("Ready for download!")
                except Exception as e:
                    st.error(f"Failed to zip: {e}")

    with col2:
        # Safe Folder Opening (Local Only)
        if st.button("📂 Open Downloads Folder (Local)"):
            try:
                import subprocess
                import platform
                
                downloads_path = Path.cwd() / BASE_SAVE_DIR
                
                if platform.system() == "Windows":
                    subprocess.Popen(f'explorer "{downloads_path}"')
                elif platform.system() == "Darwin":  # macOS
                    subprocess.Popen(["open", str(downloads_path)])
                else:  # Linux
                    # Check if running in headless/cloud env (often no xdg-open)
                    if os.getenv("Replit") or os.getenv("huggingface_spaces"):
                        st.warning("Folder opening is not supported in this cloud environment. Please use the Download ZIP button.")
                    else:
                        try:
                            subprocess.Popen(["xdg-open", str(downloads_path)])
                        except:
                            st.warning("Could not open folder automatically.")
                    
                if platform.system() in ["Windows", "Darwin"]:
                    st.success("Downloads folder opened.")
            except Exception as e:
                st.error(f"Could not open folder: {e}")
    
    # Removed verbose About section for a cleaner, minimalist UI

if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        st.error(f"❌ Application error: {e}")
        logger.critical(f"Application startup error: {traceback.format_exc()}")
        
        # Show error details in debug mode
        if st.checkbox("Show Debug Information"):
            st.code(traceback.format_exc())