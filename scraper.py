"""
Job scraper: AI Engineer + GTM Systems Engineer roles
Markets: USA (H1B/visa sponsorship) + UK/London (Skilled Worker Visa)

Sponsorship verification — 3 layers:
  1. Keyword match in job text (all sources)
  2. UK: cross-check against Home Office licensed sponsor register (live CSV)
  3. US: cross-check against known H1B filer list (curated + USCIS-derived)
"""

import os
import io
import re
import json
import csv
import time
import hashlib
import smtplib
import logging
import argparse
import schedule
import zipfile
from datetime import datetime, timezone
from pathlib import Path
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart

from typing import Union

import requests
from bs4 import BeautifulSoup

# ── Config ────────────────────────────────────────────────────────────────────

BASE_DIR  = Path(__file__).parent
DATA_FILE = BASE_DIR / "jobs.json"
CSV_FILE  = BASE_DIR / "jobs.csv"
SEEN_FILE = BASE_DIR / "seen_ids.json"
LOG_FILE  = BASE_DIR / "scraper.log"

# Cache sponsor lists so we don't re-download every run
UK_SPONSOR_CACHE  = BASE_DIR / "uk_sponsors.json"
US_H1B_CACHE      = BASE_DIR / "us_h1b_sponsors.json"
CACHE_TTL_HOURS   = 48

SEARCH_QUERIES = ["AI Engineer", "GTM Systems Engineer", "GTM Engineer", "Growth Engineer AI"]

# Seniority filter — exclude junior/intern/entry-level, keep manager+ (min mid-level)
JUNIOR_EXCLUDE_KEYWORDS = [
    "junior", "jr.", "jr ", "intern", "internship", "entry level", "entry-level",
    "graduate scheme", "graduate programme", "trainee", "apprentice",
    "assistant engineer", "associate engineer",
]

# Consulting / managed-service / staffing / over-enterprise companies to exclude.
# These either hire on behalf of clients (consulting/staffing) or sponsor internally
# only (mega-enterprise IT), not real external visa-sponsored product roles.
CONSULTING_EXCLUDE_COMPANIES = {
    # ── Big 4 / Strategy consulting ─────────────────────────────────────────
    "ey", "ernst & young", "ernst and young",
    "deloitte", "deloitte consulting", "deloitte digital",
    "pwc", "pricewaterhousecoopers", "price waterhouse",
    "kpmg",
    "mckinsey", "mckinsey & company",
    "bcg", "boston consulting group",
    "bain", "bain & company",
    "oliver wyman", "oliver wyman digital",
    "a.t. kearney", "kearney",
    "roland berger",
    "strategy&",
    "l.e.k. consulting", "lek consulting",
    "pa consulting",
    "north highland",
    "guidehouse",
    "west monroe",
    "protiviti",
    "navigant",
    "gartner", "gartner consulting",
    # ── IT consulting / system integrators ──────────────────────────────────
    "accenture", "accenture federal", "accenture song",
    "capgemini", "capgemini engineering", "capgemini invent",
    "ibm consulting", "ibm global services", "ibm services",
    "infosys", "infosys bpm", "infosys consulting",
    "wipro", "wipro technologies", "wipro digital",
    "tata consultancy", "tcs", "tata consulting",
    "hcl technologies", "hcltech", "hcl america",
    "cognizant", "cognizant technology", "cognizant digital",
    "dxc technology",
    "ntt data", "ntt limited", "ntt group",
    "unisys",
    "atos", "atos syntel", "eviden",
    "fujitsu",
    "virtusa",
    "hexaware",
    "mphasis",
    "publicis sapient", "sapient consulting",
    "slalom",
    "thoughtworks",
    "stefanini",
    "mci", "mci group",
    "luxoft",
    "epam systems", "epam",
    "globant",
    "softserve",
    "ciber",
    "igate",
    "mastech", "mastech digital",
    "birlasoft",
    "niit technologies",
    "zensar",
    # ── Government / defence contractors ────────────────────────────────────
    "leidos",
    "booz allen", "booz allen hamilton",
    "saic", "science applications",
    "cgi group", "cgi inc", "cgi federal",
    "peraton",
    "caci", "caci international",
    "general dynamics information technology", "gdit",
    "northrop grumman", "raytheon", "lockheed martin", "bae systems",
    # ── Staffing / recruitment agencies ─────────────────────────────────────
    "randstad", "randstad technologies",
    "manpower", "manpowergroup", "experis",
    "adecco", "adecco group",
    "kelly services", "kelly it",
    "robert half", "robert half technology",
    "modis", "insight global", "apex systems",
    "tek systems", "teksystems",
    "softchoice",
    "hays", "hays technology", "hays specialist",
    "michael page", "page group", "page executive",
    "harvey nash",
    "spring professional",
    "investigo",
    "ambition",
    "computacenter",
    # ── Mega-enterprise IT vendors (sponsor internally, not externally) ──────
    # These post jobs but route visa sponsorship through internal mobility only
    "ibm", "ibm corporation",           # full IBM (not just consulting arm)
    "hp", "hewlett packard", "hewlett-packard", "hpe", "hewlett packard enterprise",
    "dell technologies", "dell",
    "oracle", "oracle corporation",
    "sap", "sap se", "sap america",
    "cisco", "cisco systems",
    "intel", "intel corporation",
    "siemens", "siemens ag", "siemens digital",
    "ericsson",
    "nokia",
    "nec", "nec corporation",
    "xerox",
    "unisys",
}

# Job aggregator/spam domains to exclude — keep only direct company sites + LinkedIn
SPAM_JOB_DOMAINS = {
    "jobrapido", "jobisjob", "jobisjobus", "trovit", "mitula", "neuvoo",
    "careerjet", "jora", "jobleads", "adzuna",   # adzuna results come via API, not URL
    "jobsora", "jobomas", "jobsearchengine", "cleverism", "ziprecruiter",
    "snagajob", "simplyhired", "talent.com", "betterteam", "jobspider",
    "postjobfree", "jobsxl", "jobtome", "jobvertise", "workopolis",
    "jobdiagnosis", "jobhat", "getwork", "jobisite",
}

US_SPONSORSHIP_KEYWORDS = [
    "visa sponsorship", "will sponsor", "h1b", "h-1b", "work authorization",
    "sponsorship available", "we sponsor", "sponsorship provided",
    "open to sponsorship", "sponsoring", "authorize to work",
    "employment authorization", "labor condition application",
]

UK_SPONSORSHIP_KEYWORDS = [
    "visa sponsorship", "skilled worker visa", "tier 2", "sponsor licence",
    "certificate of sponsorship", "cos", "work visa", "sponsorship provided",
    "we sponsor", "sponsorship considered", "right to work sponsorship",
    "skilled worker route",
]

# Adzuna API — free at https://developer.adzuna.com/
ADZUNA_APP_ID  = os.getenv("ADZUNA_APP_ID", "")
ADZUNA_APP_KEY = os.getenv("ADZUNA_APP_KEY", "")

# Backend API — set to push jobs automatically after each run
BACKEND_URL = os.getenv("BACKEND_URL", "http://localhost:8000")

# Reed UK API — free at https://www.reed.co.uk/developers/jobseeker
REED_API_KEY = os.getenv("REED_API_KEY", "")

# Email config (optional — set env vars to enable)
EMAIL_FROM    = os.getenv("NOTIFY_EMAIL_FROM", "")
EMAIL_TO      = os.getenv("NOTIFY_EMAIL_TO", "ilayda@aicro.co")
EMAIL_PASS    = os.getenv("NOTIFY_EMAIL_PASS", "")
EMAIL_ENABLED = bool(EMAIL_FROM and EMAIL_PASS)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s  %(levelname)-7s  %(message)s",
    handlers=[
        logging.FileHandler(LOG_FILE),
        logging.StreamHandler(),
    ],
)
log = logging.getLogger(__name__)

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0.0.0 Safari/537.36"
    )
}

# ── Backend push ──────────────────────────────────────────────────────────────

def push_to_backend(new_jobs: list):
    """POST new jobs to the job application app backend."""
    if not new_jobs or not BACKEND_URL:
        return

    url = f"{BACKEND_URL}/api/sponsored/import"
    try:
        r = requests.post(url, json=new_jobs, headers={"Content-Type": "application/json"}, timeout=30)
        r.raise_for_status()
        data = r.json()
        log.info(f"Backend push: {data.get('imported',0)} imported, {data.get('skipped',0)} skipped")
    except requests.exceptions.ConnectionError:
        log.warning(f"Backend not reachable at {BACKEND_URL} — jobs saved locally only")
    except Exception as e:
        log.error(f"Backend push failed: {e}")


# ── Sponsor registries ────────────────────────────────────────────────────────

def _cache_fresh(path: Path) -> bool:
    if not path.exists():
        return False
    age_h = (time.time() - path.stat().st_mtime) / 3600
    return age_h < CACHE_TTL_HOURS


def load_uk_sponsor_register() -> set:
    """
    UK Home Office: Register of Licensed Sponsors (Workers).
    Page: https://www.gov.uk/government/publications/register-of-licensed-sponsors-workers
    The CSV URL rotates — we scrape the page to find the current link.
    Returns a set of normalised company names.
    """
    if _cache_fresh(UK_SPONSOR_CACHE):
        return set(json.loads(UK_SPONSOR_CACHE.read_text()))

    log.info("Downloading UK Home Office sponsor register...")
    page_url = (
        "https://www.gov.uk/government/publications/"
        "register-of-licensed-sponsors-workers"
    )

    names: set = set()
    try:
        # Step 1: find the CSV/ODS attachment link on the gov.uk page
        r = requests.get(page_url, headers=HEADERS, timeout=20)
        soup = BeautifulSoup(r.text, "html.parser")

        csv_url = None
        for a in soup.find_all("a", href=True):
            href = a["href"]
            # gov.uk serves as ODS or CSV; ODS is actually a zip we can read
            if any(ext in href.lower() for ext in [".csv", ".ods"]):
                csv_url = href if href.startswith("http") else "https://www.gov.uk" + href
                break

        if not csv_url:
            # Try JSON API endpoint as fallback
            api_url = (
                "https://www.gov.uk/api/content/government/publications/"
                "register-of-licensed-sponsors-workers"
            )
            rj = requests.get(api_url, headers=HEADERS, timeout=15)
            data = rj.json()
            for doc in data.get("details", {}).get("documents", []):
                url = doc.get("url", "")
                if any(ext in url.lower() for ext in [".csv", ".ods"]):
                    csv_url = url
                    break

        if not csv_url:
            log.warning("Could not find UK sponsor register download link")
            return names

        log.info(f"Found register at: {csv_url}")
        r2 = requests.get(csv_url, headers=HEADERS, timeout=60)
        r2.raise_for_status()

        content_type = r2.headers.get("content-type", "").lower()
        raw = r2.content

        if "csv" in content_type or csv_url.endswith(".csv"):
            reader = csv.reader(io.StringIO(raw.decode("utf-8", errors="replace")))
            next(reader, None)
            for row in reader:
                if row:
                    names.add(_norm(row[0]))

        elif "zip" in content_type or csv_url.endswith(".zip"):
            with zipfile.ZipFile(io.BytesIO(raw)) as zf:
                for name in zf.namelist():
                    if name.endswith(".csv"):
                        with zf.open(name) as f:
                            reader = csv.reader(io.StringIO(f.read().decode("utf-8", errors="replace")))
                            next(reader, None)
                            for row in reader:
                                if row:
                                    names.add(_norm(row[0]))
                        break

        # ODS is OpenDocument Spreadsheet — parse as XML zip
        elif "ods" in content_type or csv_url.endswith(".ods"):
            with zipfile.ZipFile(io.BytesIO(raw)) as zf:
                if "content.xml" in zf.namelist():
                    xml = zf.read("content.xml").decode("utf-8", errors="replace")
                    xml_soup = BeautifulSoup(xml, "xml")
                    rows = xml_soup.find_all("table:table-row")
                    for row in rows[1:]:  # skip header
                        cells = row.find_all("table:table-cell")
                        if cells:
                            val = cells[0].get_text(strip=True)
                            if val:
                                names.add(_norm(val))

    except Exception as e:
        log.warning(f"Could not load UK sponsor register: {e}")

    if names:
        UK_SPONSOR_CACHE.write_text(json.dumps(list(names)))
        log.info(f"UK sponsor register loaded: {len(names):,} companies")
    else:
        log.warning("UK sponsor register empty — keyword-only mode for UK")

    return names


def load_us_h1b_sponsors() -> set:
    """
    Returns a set of normalised company names known to file H1B petitions.
    Primary: curated list of major tech/AI H1B filers.
    The full USCIS disclosure data is 100MB+ so we use a curated + growing cache.
    """
    if _cache_fresh(US_H1B_CACHE):
        return set(json.loads(US_H1B_CACHE.read_text()))

    # Curated list of companies publicly known to sponsor H1B / offer visa sponsorship
    # Based on USCIS H1B employer data hub + public job postings
    known = {
        # Big Tech
        "google", "meta", "apple", "amazon", "microsoft", "netflix",
        "salesforce", "oracle", "ibm", "intel", "nvidia", "amd", "qualcomm",
        "adobe", "atlassian", "workday", "servicenow", "twilio", "okta",
        "datadog", "cloudflare", "hashicorp", "elastic", "mongodb", "confluent",
        # AI / ML
        "anthropic", "openai", "cohere", "mistral", "scale ai", "scale-ai",
        "hugging face", "huggingface", "databricks", "weights & biases",
        "wandb", "together ai", "together", "perplexity", "inflection",
        "adept", "stability ai", "runway", "midjourney",
        # Fintech
        "stripe", "brex", "ramp", "plaid", "robinhood", "chime", "affirm",
        "square", "block", "coinbase", "ripple",
        # Enterprise SaaS
        "zendesk", "hubspot", "monday.com", "asana", "notion", "figma",
        "linear", "airtable", "coda", "miro",
        # Cloud / Infra
        "snowflake", "databricks", "dbt labs", "fivetran", "airbyte",
        "vercel", "netlify", "supabase", "planetscale", "cockroachdb",
        "clickhouse", "pinecone", "weaviate", "qdrant", "chroma",
        # GTM / Sales tech
        "gong", "outreach", "salesloft", "apollo", "zoominfo", "clearbit",
        "6sense", "demandbase", "drift", "intercom", "mixpanel", "amplitude",
        "segment", "heap", "fullstory", "pendo",
    }

    names = {_norm(n) for n in known}
    US_H1B_CACHE.write_text(json.dumps(list(names)))
    log.info(f"US H1B sponsor list loaded: {len(names):,} companies")
    return names


def _norm(name: str) -> str:
    """Normalise company name for fuzzy matching."""
    return re.sub(r"[^a-z0-9]", "", name.lower().strip())


def company_sponsors(company: str, market: str,
                     uk_register: set, us_h1b: set) -> Union[bool, str]:
    """
    Returns True if company is on the official sponsor register,
    False if definitely not found, 'unknown' if register was unavailable.
    """
    norm = _norm(company)
    if not norm:
        return "unknown"
    if market in ("us", "us+uk"):
        if us_h1b and norm in us_h1b:
            return True
        # Partial match — company name contains a known sponsor
        if us_h1b and any(s in norm or norm in s for s in us_h1b if len(s) > 4):
            return True
    if market in ("uk", "us+uk"):
        if uk_register and norm in uk_register:
            return True
        if uk_register and any(s in norm or norm in s for s in uk_register if len(s) > 4):
            return True
    # Register loaded but company not found
    if (market == "uk" and uk_register) or (market == "us" and us_h1b):
        return False
    return "unknown"


# ── Helpers ───────────────────────────────────────────────────────────────────

def job_id(job: dict) -> str:
    key = f"{job.get('title','')}{job.get('company','')}{job.get('url','')}"
    return hashlib.md5(key.encode()).hexdigest()


def has_sponsorship_text(text: str, market: str) -> bool:
    text = text.lower()
    keywords = US_SPONSORSHIP_KEYWORDS if market == "us" else UK_SPONSORSHIP_KEYWORDS
    return any(kw in text for kw in keywords)


def sponsorship_verdict(
    text: str, company: str, market: str,
    uk_register: set, us_h1b: set
) -> Union[str, bool]:
    """
    Returns:
      True              — confirmed (text keyword OR official register)
      "register-only"   — on official register but job text doesn't mention it
      "text-only"       — keyword in job text but not on register
      "unverified"      — LinkedIn/no-description, couldn't check
      False             — not on register AND no keyword
    """
    text_match    = has_sponsorship_text(text, market)
    register_hit  = company_sponsors(company, market, uk_register, us_h1b)

    if text_match and register_hit is True:
        return True                    # strongest signal
    if register_hit is True:
        return "register-only"         # official list but not mentioned in text
    if text_match:
        return "text-only"             # stated in text, not on register
    if register_hit == "unknown":
        return "unverified"
    return False


# ── Funded SaaS detection ─────────────────────────────────────────────────────

_FUNDING_KEYWORDS = [
    # Round mentions
    "series a", "series b", "series c", "series d", "series e",
    "seed funding", "seed round", "seed stage",
    "pre-seed", "pre-series",
    "venture backed", "venture-backed", "vc backed", "vc-backed",
    "recently funded", "newly funded",
    # Raise amounts
    r"\$\d+[mb] funding", r"raised \$\d+", r"raised £\d+",
    r"funding round", r"closed \$", r"secured \$",
    # Investor signals
    "backed by", "investors include", "portfolio company",
    "y combinator", "yc ", " yc,", "techstars", "a16z", "andreessen",
    "sequoia", "accel", "benchmark", "lightspeed", "tiger global",
    "softbank", "greylock", "index ventures", "balderton",
    # Growth signals
    "hypergrowth", "hyper-growth", "fast-growing", "fast growing",
    "high-growth", "high growth", "scaling rapidly", "rapid growth",
    "rocket ship", "rocketship",
    # SaaS/product signals
    "saas", "software as a service", "b2b saas", "our platform",
    "our product", "product-led", "product led growth",
]

_FUNDING_RE = [re.compile(p, re.IGNORECASE) for p in _FUNDING_KEYWORDS]


def detect_funded_saas(text: str, company_description: str = "") -> bool:
    """Return True if job text signals a funded / high-growth SaaS company."""
    combined = (text + " " + company_description).lower()
    return any(pat.search(combined) for pat in _FUNDING_RE)


def load_seen() -> set:
    if SEEN_FILE.exists():
        return set(json.loads(SEEN_FILE.read_text()))
    return set()


def save_seen(seen: set):
    SEEN_FILE.write_text(json.dumps(list(seen), indent=2))


def load_jobs() -> list:
    if DATA_FILE.exists():
        return json.loads(DATA_FILE.read_text())
    return []


def save_jobs(jobs: list):
    DATA_FILE.write_text(json.dumps(jobs, indent=2, ensure_ascii=False))
    _write_csv(jobs)


def _write_csv(jobs: list):
    if not jobs:
        return
    fields = ["id", "title", "company", "location", "market", "sponsorship",
              "salary", "url", "source", "found_at"]
    with open(CSV_FILE, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
        w.writeheader()
        w.writerows(jobs)


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _is_sponsored(verdict) -> bool:
    """Only include jobs where sponsorship is confirmed or plausible."""
    return verdict in (True, "register-only", "text-only")


def is_consulting_company(company: str) -> bool:
    """Returns True if the company looks like a consulting/MSP/staffing firm."""
    c = company.strip().lower()
    return any(excl in c for excl in CONSULTING_EXCLUDE_COMPANIES)


def is_valid_job(title: str, company: str, url: str = "") -> bool:
    """
    Returns False if:
    - title is empty or looks like a company name placeholder
    - title contains junior/intern/entry-level keywords
    - URL points to a spam aggregator
    - company is a consulting/MSP/staffing firm (not a product/SaaS company)
    """
    if not title or len(title.strip()) < 4:
        return False
    if title.strip().lower() == company.strip().lower():
        return False
    t = title.lower()
    if any(kw in t for kw in JUNIOR_EXCLUDE_KEYWORDS):
        return False
    if url:
        url_lower = url.lower()
        if any(spam in url_lower for spam in SPAM_JOB_DOMAINS):
            return False
    if company and is_consulting_company(company):
        return False
    return True


# ── Source: Adzuna ─────────────────────────────────────────────────────────────

def scrape_adzuna(query: str, country: str, location: str,
                  uk_register: set, us_h1b: set) -> list:
    if not ADZUNA_APP_ID or not ADZUNA_APP_KEY:
        log.warning("Adzuna API keys not set — skipping Adzuna")
        return []

    jobs  = []
    market = "us" if country == "us" else "uk"
    page   = 1

    while page <= 5:
        url = (
            f"https://api.adzuna.com/v1/api/jobs/{country}/search/{page}"
            f"?app_id={ADZUNA_APP_ID}&app_key={ADZUNA_APP_KEY}"
            f"&results_per_page=50&what={requests.utils.quote(query)}"
            f"&content-type=application/json"
        )
        if location:
            url += f"&where={requests.utils.quote(location)}"

        try:
            r = requests.get(url, headers=HEADERS, timeout=15)
            r.raise_for_status()
            data = r.json()
        except Exception as e:
            log.error(f"Adzuna {country} p{page}: {e}")
            break

        results = data.get("results", [])
        if not results:
            break

        for item in results:
            desc    = item.get("description", "")
            title   = item.get("title", "")
            company = item.get("company", {}).get("display_name", "")
            verdict = sponsorship_verdict(
                f"{title} {desc}", company, market, uk_register, us_h1b
            )
            if not _is_sponsored(verdict) or not is_valid_job(title, company, job_url):
                continue

            currency = "£" if country == "gb" else "$"
            mn, mx   = item.get("salary_min"), item.get("salary_max")
            salary   = f"{currency}{int(mn or 0):,} – {currency}{int(mx or 0):,}" if (mn or mx) else ""

            jobs.append({
                "title":       title,
                "company":     company,
                "location":    item.get("location", {}).get("display_name", ""),
                "market":      market,
                "sponsorship": str(verdict),
                "salary":      salary,
                "url":         item.get("redirect_url", ""),
                "description": desc[:500],
                "source":      "adzuna",
                "funded_saas": detect_funded_saas(desc),
                "found_at":    now_iso(),
            })

        page += 1
        time.sleep(1)

    log.info(f"Adzuna [{country}] '{query}' → {len(jobs)} verified sponsored jobs")
    return jobs


# ── Source: Remotive ──────────────────────────────────────────────────────────

def scrape_remotive(query: str, uk_register: set, us_h1b: set) -> list:
    jobs = []
    url  = f"https://remotive.com/api/remote-jobs?search={requests.utils.quote(query)}&limit=100"

    try:
        r = requests.get(url, headers=HEADERS, timeout=15)
        r.raise_for_status()
        data = r.json()
    except Exception as e:
        log.error(f"Remotive '{query}': {e}")
        return []

    for item in data.get("jobs", []):
        desc    = BeautifulSoup(item.get("description", ""), "html.parser").get_text()
        title   = item.get("title", "")
        company = item.get("company_name", "")

        verdict_us = sponsorship_verdict(f"{title} {desc}", company, "us", uk_register, us_h1b)
        verdict_uk = sponsorship_verdict(f"{title} {desc}", company, "uk", uk_register, us_h1b)

        if not (_is_sponsored(verdict_us) or _is_sponsored(verdict_uk)):
            continue

        if _is_sponsored(verdict_us) and _is_sponsored(verdict_uk):
            market  = "us+uk"
            verdict = str(verdict_us)
        elif _is_sponsored(verdict_us):
            market  = "us"
            verdict = str(verdict_us)
        else:
            market  = "uk"
            verdict = str(verdict_uk)

        jobs.append({
            "title":       title,
            "company":     company,
            "location":    item.get("candidate_required_location", "Remote"),
            "market":      market,
            "sponsorship": verdict,
            "salary":      item.get("salary", ""),
            "url":         item.get("url", ""),
            "description": desc[:500],
            "source":      "remotive",
            "found_at":    now_iso(),
        })

    log.info(f"Remotive '{query}' → {len(jobs)} verified sponsored jobs")
    return jobs


# ── Source: Reed UK ───────────────────────────────────────────────────────────

def scrape_reed(query: str, location: str, uk_register: set, us_h1b: set) -> list:
    if not REED_API_KEY:
        log.warning("REED_API_KEY not set — skipping Reed")
        return []

    jobs = []
    url  = (
        "https://www.reed.co.uk/api/1.0/search"
        f"?keywords={requests.utils.quote(query)}"
        f"&location={requests.utils.quote(location)}"
        f"&distancefrom=10"
        f"&resultsToTake=100"
    )

    try:
        r = requests.get(url, auth=(REED_API_KEY, ""), headers=HEADERS, timeout=15)
        r.raise_for_status()
        data = r.json()
    except Exception as e:
        log.error(f"Reed '{query}': {e}")
        return []

    for item in data.get("results", []):
        desc    = item.get("jobDescription", "")
        title   = item.get("jobTitle", "")
        company = item.get("employerName", "")
        verdict = sponsorship_verdict(
            f"{title} {desc}", company, "uk", uk_register, us_h1b
        )
        if not _is_sponsored(verdict) or not is_valid_job(title, company, job_url):
            continue

        mn, mx = item.get("minimumSalary"), item.get("maximumSalary")
        salary = f"£{int(mn or 0):,} – £{int(mx or 0):,}" if (mn or mx) else ""

        jobs.append({
            "title":       title,
            "company":     company,
            "location":    item.get("locationName", location),
            "market":      "uk",
            "sponsorship": str(verdict),
            "salary":      salary,
            "url":         item.get("jobUrl", ""),
            "description": desc[:500],
            "source":      "reed",
            "funded_saas": detect_funded_saas(desc),
            "found_at":    now_iso(),
        })

    log.info(f"Reed '{query}' {location} → {len(jobs)} verified sponsored jobs")
    return jobs


# ── Source: LinkedIn (with description fetch) ─────────────────────────────────

def _fetch_linkedin_description(job_url: str) -> str:
    """Fetch full job description from a LinkedIn job page."""
    try:
        r = requests.get(job_url, headers=HEADERS, timeout=12)
        if r.status_code != 200:
            return ""
        soup = BeautifulSoup(r.text, "html.parser")
        # Try structured description div first
        desc_div = (
            soup.find("div", class_="description__text") or
            soup.find("div", class_="show-more-less-html__markup") or
            soup.find("section", class_="description")
        )
        if desc_div:
            return desc_div.get_text(separator=" ", strip=True)[:1000]
        return ""
    except Exception:
        return ""


def scrape_linkedin(query: str, location: str, market: str,
                    uk_register: set, us_h1b: set) -> list:
    jobs = []
    geo  = "103644278" if market == "us" else "101165590"
    url  = (
        "https://www.linkedin.com/jobs-guest/jobs/api/seeMoreJobPostings/search"
        f"?keywords={requests.utils.quote(query)}"
        f"&location={requests.utils.quote(location)}"
        f"&geoId={geo}&start=0&count=25"
    )

    try:
        r = requests.get(url, headers=HEADERS, timeout=15)
        if r.status_code == 429:
            log.warning("LinkedIn rate-limited — skipping")
            return []
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")
    except Exception as e:
        log.error(f"LinkedIn '{query}' {location}: {e}")
        return []

    cards = soup.find_all("div", class_="base-card")
    log.info(f"LinkedIn '{query}' {location}: fetching descriptions for {len(cards)} cards…")

    for card in cards:
        title_el   = card.find("h3", class_="base-search-card__title")
        company_el = card.find("h4", class_="base-search-card__subtitle")
        loc_el     = card.find("span", class_="job-search-card__location")
        link_el    = card.find("a", class_="base-card__full-link")

        title   = title_el.get_text(strip=True)   if title_el   else ""
        company = company_el.get_text(strip=True) if company_el else ""
        loc     = loc_el.get_text(strip=True)     if loc_el     else location
        job_url = link_el.get("href", "")         if link_el    else ""

        # Fetch full description to check sponsorship text
        desc    = _fetch_linkedin_description(job_url) if job_url else ""
        verdict = sponsorship_verdict(
            f"{title} {desc}", company, market, uk_register, us_h1b
        )

        if not _is_sponsored(verdict) or not is_valid_job(title, company, job_url):
            continue

        jobs.append({
            "title":       title,
            "company":     company,
            "location":    loc,
            "market":      market,
            "sponsorship": str(verdict),
            "salary":      "",
            "url":         job_url,
            "description": desc[:500],
            "source":      "linkedin",
            "funded_saas": detect_funded_saas(desc),
            "found_at":    now_iso(),
        })
        time.sleep(0.5)  # be polite between detail fetches

    log.info(f"LinkedIn '{query}' {location} → {len(jobs)} verified sponsored jobs")
    return jobs


# ── Source: Totaljobs ────────────────────────────────────────────────────────

# Totaljobs uses brotli encoding — exclude it from Accept-Encoding
_HEADERS_NO_BR = {**HEADERS, "Accept-Encoding": "gzip, deflate"}

def scrape_totaljobs(query: str, uk_register: set, us_h1b: set) -> list:
    jobs = []
    url = (
        f"https://www.totaljobs.com/jobs/{requests.utils.quote(query.lower().replace(' ', '-'))}"
        f"/in-london?radius=15&postedWithin=14"
    )
    try:
        r = requests.get(url, headers=_HEADERS_NO_BR, timeout=20)
        if r.status_code != 200:
            return []
        soup = BeautifulSoup(r.text, "html.parser")
    except Exception as e:
        log.error(f"Totaljobs '{query}': {e}")
        return []

    for card in soup.find_all("article", {"data-testid": "job-item"}):
        title_el   = card.find("a", {"data-testid": "job-item-title"})
        company_el = card.find("span", {"data-testid": "job-item-hiring-company-name"})
        loc_el     = card.find("span", {"data-testid": "job-item-location"})
        salary_el  = card.find("span", {"data-testid": "job-item-salary-info"})
        desc_el    = card.find("div", {"data-testid": "job-item-description"})

        title   = title_el.get_text(strip=True)   if title_el   else ""
        company = company_el.get_text(strip=True) if company_el else ""
        loc     = loc_el.get_text(strip=True)     if loc_el     else "London"
        salary  = salary_el.get_text(strip=True)  if salary_el  else ""
        desc    = desc_el.get_text(strip=True)    if desc_el    else ""
        href    = title_el.get("href", "")        if title_el   else ""
        job_url = href if href.startswith("http") else f"https://www.totaljobs.com{href}"

        verdict = sponsorship_verdict(f"{title} {desc}", company, "uk", uk_register, us_h1b)
        if not _is_sponsored(verdict) or not is_valid_job(title, company, job_url):
            continue

        jobs.append({
            "title":       title,
            "company":     company,
            "location":    loc,
            "market":      "uk",
            "sponsorship": str(verdict),
            "salary":      salary,
            "url":         job_url,
            "description": desc[:500],
            "source":      "totaljobs",
            "funded_saas": detect_funded_saas(desc),
            "found_at":    now_iso(),
        })

    log.info(f"Totaljobs '{query}' → {len(jobs)} verified sponsored jobs")
    return jobs


# ── Source: CWJobs (Computer Weekly — IT focused UK) ─────────────────────────

def scrape_cwjobs(query: str, uk_register: set, us_h1b: set) -> list:
    """CWJobs is owned by Totaljobs Group — same structure, IT-focused audience."""
    jobs = []
    url = (
        f"https://www.cwjobs.co.uk/jobs/{requests.utils.quote(query.lower().replace(' ', '-'))}"
        f"/in-london?radius=15&postedWithin=14"
    )
    try:
        r = requests.get(url, headers=_HEADERS_NO_BR, timeout=20)
        if r.status_code != 200:
            return []
        soup = BeautifulSoup(r.text, "html.parser")
    except Exception as e:
        log.error(f"CWJobs '{query}': {e}")
        return []

    for card in soup.find_all("article", {"data-testid": "job-item"}):
        title_el   = card.find("a", {"data-testid": "job-item-title"})
        company_el = card.find("span", {"data-testid": "job-item-hiring-company-name"})
        loc_el     = card.find("span", {"data-testid": "job-item-location"})
        salary_el  = card.find("span", {"data-testid": "job-item-salary-info"})
        desc_el    = card.find("div", {"data-testid": "job-item-description"})

        title   = title_el.get_text(strip=True)   if title_el   else ""
        company = company_el.get_text(strip=True) if company_el else ""
        loc     = loc_el.get_text(strip=True)     if loc_el     else "London"
        salary  = salary_el.get_text(strip=True)  if salary_el  else ""
        desc    = desc_el.get_text(strip=True)    if desc_el    else ""
        href    = title_el.get("href", "")        if title_el   else ""
        job_url = href if href.startswith("http") else f"https://www.cwjobs.co.uk{href}"

        verdict = sponsorship_verdict(f"{title} {desc}", company, "uk", uk_register, us_h1b)
        if not _is_sponsored(verdict) or not is_valid_job(title, company, job_url):
            continue

        jobs.append({
            "title":       title,
            "company":     company,
            "location":    loc,
            "market":      "uk",
            "sponsorship": str(verdict),
            "salary":      salary,
            "url":         job_url,
            "description": desc[:500],
            "source":      "cwjobs",
            "funded_saas": detect_funded_saas(desc),
            "found_at":    now_iso(),
        })

    log.info(f"CWJobs '{query}' → {len(jobs)} verified sponsored jobs")
    return jobs


# ── Source: Greenhouse ────────────────────────────────────────────────────────

GREENHOUSE_COMPANIES = [
    "anthropic", "openai", "scale-ai", "cohere", "mistral",
    "huggingface", "databricks", "snowflake", "figma", "notion",
    "linear", "vercel", "stripe", "brex", "ramp", "gong", "outreach",
    "salesloft", "apollo", "amplitude", "mixpanel", "segment",
]

def scrape_greenhouse(query: str, market: str,
                      uk_register: set, us_h1b: set) -> list:
    jobs        = []
    query_lower = query.lower()

    for company in GREENHOUSE_COMPANIES:
        url = f"https://boards-api.greenhouse.io/v1/boards/{company}/jobs?content=true"
        try:
            r = requests.get(url, headers=HEADERS, timeout=10)
            if r.status_code != 200:
                continue
            data = r.json()
        except Exception:
            continue

        for item in data.get("jobs", []):
            title = item.get("title", "")
            if not any(q.lower() in title.lower() for q in [query_lower, "ai engineer", "gtm"]):
                continue

            location = " | ".join(o.get("name", "") for o in item.get("offices", []))
            loc_lower = location.lower()

            if market == "us" and not any(
                kw in loc_lower for kw in ["united states", " us", "new york", "san francisco", "remote", ""]
            ):
                continue
            if market == "uk" and "london" not in loc_lower:
                continue

            desc    = BeautifulSoup(item.get("content", ""), "html.parser").get_text()
            verdict = sponsorship_verdict(
                f"{title} {desc}", company, market, uk_register, us_h1b
            )
            if not _is_sponsored(verdict) or not is_valid_job(title, company, job_url):
                continue

            jobs.append({
                "title":       title,
                "company":     company.title(),
                "location":    location,
                "market":      market,
                "sponsorship": str(verdict),
                "salary":      "",
                "url":         item.get("absolute_url", ""),
                "description": desc[:500],
                "source":      "greenhouse",
                "funded_saas": detect_funded_saas(desc),
                "found_at":    now_iso(),
            })

        time.sleep(0.3)

    log.info(f"Greenhouse '{query}' [{market}] → {len(jobs)} verified sponsored jobs")
    return jobs


# ── Email notification ─────────────────────────────────────────────────────────

def send_email_notification(new_jobs: list):
    if not EMAIL_ENABLED or not new_jobs:
        return

    rows = []
    for j in new_jobs[:30]:
        confidence = {
            "True":          "✅ Confirmed",
            "register-only": "📋 On official register",
            "text-only":     "📝 Stated in listing",
        }.get(j["sponsorship"], j["sponsorship"])

        rows.append(
            f"<b>{j['title']}</b> @ {j['company']}<br>"
            f"📍 {j['location']} ({j['market'].upper()}) | 💰 {j.get('salary','N/A')}<br>"
            f"🔗 <a href='{j['url']}'>{j['url'][:80]}</a><br>"
            f"Sponsorship: {confidence} | Source: {j['source']}<br><br>"
        )

    body = f"""
    <h2>🚀 {len(new_jobs)} New Sponsored Job(s)</h2>
    <p>Roles: AI Engineer, GTM Systems Engineer | Markets: US + UK/London</p>
    {"".join(rows)}
    <p><i>Full CSV: {CSV_FILE}</i></p>
    """

    msg = MIMEMultipart("alternative")
    msg["Subject"] = (
        f"[Job Alert] {len(new_jobs)} new sponsored roles — "
        f"{datetime.now().strftime('%Y-%m-%d %H:%M')}"
    )
    msg["From"] = EMAIL_FROM
    msg["To"]   = EMAIL_TO
    msg.attach(MIMEText(body, "html"))

    try:
        with smtplib.SMTP_SSL("smtp.gmail.com", 465) as s:
            s.login(EMAIL_FROM, EMAIL_PASS)
            s.sendmail(EMAIL_FROM, EMAIL_TO, msg.as_string())
        log.info(f"Email sent → {EMAIL_TO}")
    except Exception as e:
        log.error(f"Email failed: {e}")


# ── Main run ──────────────────────────────────────────────────────────────────

def run_scrape():
    log.info("=" * 60)
    log.info("Starting scrape run")

    # Load sponsor registers once per run
    uk_register = load_uk_sponsor_register()
    us_h1b      = load_us_h1b_sponsors()

    seen     = load_seen()
    existing = load_jobs()
    raw      = []

    for query in SEARCH_QUERIES:
        # USA
        raw += scrape_adzuna(query, "us", "", uk_register, us_h1b)
        raw += scrape_greenhouse(query, "us", uk_register, us_h1b)
        raw += scrape_linkedin(query, "United States", "us", uk_register, us_h1b)

        # UK / London
        raw += scrape_adzuna(query, "gb", "London", uk_register, us_h1b)
        raw += scrape_reed(query, "London", uk_register, us_h1b)
        raw += scrape_totaljobs(query, uk_register, us_h1b)
        raw += scrape_cwjobs(query, uk_register, us_h1b)
        raw += scrape_greenhouse(query, "uk", uk_register, us_h1b)
        raw += scrape_linkedin(query, "London, United Kingdom", "uk", uk_register, us_h1b)

        time.sleep(2)

    # Deduplicate
    new_jobs = []
    for job in raw:
        jid = job_id(job)
        if jid in seen:
            continue
        job["id"] = jid
        seen.add(jid)
        new_jobs.append(job)

    if new_jobs:
        all_jobs = existing + new_jobs
        save_jobs(all_jobs)
        save_seen(seen)
        log.info(f"✅ {len(new_jobs)} new jobs added (total: {len(all_jobs)})")
        push_to_backend(new_jobs)
        send_email_notification(new_jobs)
        _print_summary(new_jobs)
    else:
        log.info("No new sponsored jobs found this run.")

    log.info("Run complete")


def _print_summary(jobs: list):
    us_jobs = [j for j in jobs if "us" in j.get("market", "")]
    uk_jobs = [j for j in jobs if "uk" in j.get("market", "")]

    confidence_map = {
        "True":          "✅ confirmed",
        "register-only": "📋 official register",
        "text-only":     "📝 stated in listing",
        "unverified":    "❓ unverified",
    }

    print(f"\n{'─'*65}")
    print(f"  NEW SPONSORED JOBS: {len(jobs)}  (🇺🇸 {len(us_jobs)} US  |  🇬🇧 {len(uk_jobs)} UK)")
    print(f"{'─'*65}")

    for j in jobs[:25]:
        flag       = "🇺🇸" if j.get("market") == "us" else ("🇬🇧" if j.get("market") == "uk" else "🌍")
        confidence = confidence_map.get(str(j.get("sponsorship")), j.get("sponsorship",""))
        print(f"  {flag}  {j['title']} @ {j['company']}")
        print(f"       {j['location']} | {j.get('salary','') or 'salary N/A'}")
        print(f"       {confidence} | {j['source']}")
        print(f"       {j['url'][:75]}")

    if len(jobs) > 25:
        print(f"\n  ... +{len(jobs)-25} more → {CSV_FILE}")
    print()


# ── Entry point ───────────────────────────────────────────────────────────────

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--once",     action="store_true", help="Run once and exit")
    parser.add_argument("--interval", type=int, default=6,  help="Hours between runs (default: 6)")
    args = parser.parse_args()

    log.info(f"Scraper starting | interval={args.interval}h | email={'on' if EMAIL_ENABLED else 'off'}")

    run_scrape()

    if not args.once:
        schedule.every(args.interval).hours.do(run_scrape)
        log.info(f"Scheduler active — next run in {args.interval}h")
        while True:
            schedule.run_pending()
            time.sleep(60)
