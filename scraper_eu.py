"""
EU Job Scraper: Germany (Berlin/Munich) + Netherlands (Amsterdam)
Visa types: Germany EU Blue Card / Netherlands Kennismigrant (Highly Skilled Migrant)

Sources: Adzuna DE+NL, Stepstone DE+NL, LinkedIn, Greenhouse
"""

import os
import re
import json
import csv
import time
import hashlib
import logging
import argparse
import schedule
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

import requests
from bs4 import BeautifulSoup

# ── Config ────────────────────────────────────────────────────────────────────

BASE_DIR   = Path(__file__).parent
DATA_FILE  = BASE_DIR / "eu_jobs.json"
CSV_FILE   = BASE_DIR / "eu_jobs.csv"
SEEN_FILE  = BASE_DIR / "eu_seen_ids.json"
LOG_FILE   = BASE_DIR / "eu_scraper.log"

SEARCH_QUERIES = [
    "AI Engineer",
    "GTM Engineer",
    "GTM Systems Engineer",
    "Revenue Operations Engineer",
    "Growth Engineer AI",
    "GTM AI Engineer",
    "Marketing Automation Engineer",
    "Agentic AI Engineer",
]

DE_LOCATIONS = ["Berlin", "Munich", "Hamburg", "Frankfurt"]
NL_LOCATIONS = ["Amsterdam"]

JUNIOR_EXCLUDE_KEYWORDS = [
    "junior", "jr.", "jr ", "intern", "internship", "entry level", "entry-level",
    "graduate scheme", "trainee", "apprentice", "werkstudent", "praktikum",
]

ROLE_EXCLUDE_KEYWORDS = [
    "data analyst", "data analytics", "business analyst", "business intelligence",
    "data scientist", "machine learning scientist",
    "devops", "site reliability", "platform engineer",
    "cloud engineer", "infrastructure engineer", "network engineer",
    "security engineer", "cybersecurity",
    "hardware engineer", "embedded engineer", "firmware engineer",
    "ios engineer", "android engineer", "mobile engineer",
    "qa engineer", "quality assurance", "test engineer",
    "technical writer", "recruiter", "talent acquisition",
    "customer success", "account executive", "account manager",
    "product manager", "product management",
    "marketing manager", "sales manager", "sales specialist",
    "ml engineer", "machine learning engineer",
    "frontend engineer", "front-end engineer",
    " consulting", "consultant",
    "rates vp", "investment banking", "public sector",
    "mandarin", "fluent in thai",
    "data engineering manager", "databricks",
]

CONSULTING_EXCLUDE_COMPANIES = {
    "ey", "ernst young", "deloitte", "pwc", "kpmg", "mckinsey", "bcg",
    "bain", "accenture", "capgemini", "ibm consulting", "infosys", "wipro",
    "tata consultancy", "tcs", "hcl technologies", "cognizant", "dxc",
    "ntt data", "atos", "fujitsu", "epam", "globant", "thoughtworks", "slalom",
    "randstad", "manpower", "adecco", "kelly services", "robert half", "hays",
    "michael page", "harvey nash",
    "oracle", "sap", "cisco", "siemens", "ericsson", "nokia",
    "citi", "jpmorgan", "goldman sachs", "deutsche bank", "commerzbank",
    "ubs", "barclays", "bnp paribas", "societe generale",
}

# ── Sponsorship keywords ──────────────────────────────────────────────────────

DE_SPONSORSHIP_KEYWORDS = [
    "blue card", "eu blue card", "bluecard", "work permit", "arbeitserlaubnis",
    "visa sponsorship", "sponsorship", "relocation support", "relocation package",
    "relocation assistance", "umzugsunterstützung",
    "working permit", "residence permit", "aufenthaltserlaubnis",
    "we sponsor", "sponsoring", "open to relocation",
]

NL_SPONSORSHIP_KEYWORDS = [
    "highly skilled migrant", "kennismigrant", "30% ruling", "30% tax ruling",
    "30%-ruling", "visa sponsorship", "sponsorship", "work permit",
    "relocation package", "relocation support", "relocation assistance",
    "we sponsor", "sponsoring", "IND sponsorship", "residence permit",
    "expat", "open to relocation",
]

# ── API keys ──────────────────────────────────────────────────────────────────

ADZUNA_APP_ID  = os.getenv("ADZUNA_APP_ID", "")
ADZUNA_APP_KEY = os.getenv("ADZUNA_APP_KEY", "")
BACKEND_URL    = os.getenv("BACKEND_URL", "http://localhost:8000")

HEADERS = {
    "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9,de;q=0.8,nl;q=0.7",
    "Accept-Encoding": "gzip, deflate",
}

# ── Logging ───────────────────────────────────────────────────────────────────

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.FileHandler(LOG_FILE), logging.StreamHandler()],
)
log = logging.getLogger("eu_scraper")

# ── Helpers ───────────────────────────────────────────────────────────────────

def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()

def job_id(job: dict) -> str:
    key = f"{job.get('title','')}|{job.get('company','')}|{job.get('url','')}"
    return hashlib.md5(key.encode()).hexdigest()

def has_sponsorship_text(text: str, market: str) -> bool:
    t = text.lower()
    keywords = DE_SPONSORSHIP_KEYWORDS if market == "de" else NL_SPONSORSHIP_KEYWORDS
    return any(kw in t for kw in keywords)

def is_valid_job(title: str, company: str, url: str = "") -> bool:
    if not title or len(title.strip()) < 4:
        return False
    if title.strip().lower() == company.strip().lower():
        return False
    t = title.lower()
    if any(kw in t for kw in JUNIOR_EXCLUDE_KEYWORDS):
        return False
    if any(kw in t for kw in ROLE_EXCLUDE_KEYWORDS):
        return False
    c = company.strip().lower()
    if any(excl in c for excl in CONSULTING_EXCLUDE_COMPANIES):
        return False
    return True

_FUNDING_KEYWORDS = [
    "series a", "series b", "series c", "series d",
    "seed funding", "seed round", "venture backed", "vc backed",
    "y combinator", "yc ", "techstars", "a16z", "sequoia", "accel",
    "benchmark", "lightspeed", "balderton", "index ventures",
    "saas", "software as a service", "b2b saas",
    "hypergrowth", "fast-growing", "high-growth", "scaling rapidly",
    "product-led", "raised", "funded",
]
_FUNDING_RE = [re.compile(p, re.IGNORECASE) for p in _FUNDING_KEYWORDS]

def detect_funded_saas(text: str) -> bool:
    return any(pat.search(text) for pat in _FUNDING_RE)

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
    if jobs:
        fields = ["id", "title", "company", "location", "market", "sponsorship",
                  "salary", "url", "source", "funded_saas", "found_at"]
        with open(CSV_FILE, "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
            w.writeheader()
            w.writerows(jobs)

# ── Source: Adzuna DE / NL ────────────────────────────────────────────────────

def scrape_adzuna_eu(query: str, country: str, location: str) -> list:
    if not ADZUNA_APP_ID or not ADZUNA_APP_KEY:
        log.warning("Adzuna keys not set — skipping")
        return []

    market = country  # "de" or "nl"
    jobs, page = [], 1

    while page <= 3:
        url = (
            f"https://api.adzuna.com/v1/api/jobs/{country}/search/{page}"
            f"?app_id={ADZUNA_APP_ID}&app_key={ADZUNA_APP_KEY}"
            f"&results_per_page=50&what={requests.utils.quote(query)}"
            f"&where={requests.utils.quote(location)}&distance=30"
            f"&content-type=application/json"
        )
        try:
            r = requests.get(url, headers=HEADERS, timeout=15)
            r.raise_for_status()
            data = r.json()
        except Exception as e:
            log.error(f"Adzuna {country} '{query}': {e}")
            break

        results = data.get("results", [])
        if not results:
            break

        for item in results:
            title   = item.get("title", "")
            company = item.get("company", {}).get("display_name", "")
            desc    = item.get("description", "")
            job_url = item.get("redirect_url", "")
            loc     = item.get("location", {}).get("display_name", location)
            salary  = ""
            mn, mx  = item.get("salary_min"), item.get("salary_max")
            if mn or mx:
                curr = "€"
                salary = f"{curr}{int(mn or 0):,} – {curr}{int(mx or 0):,}"

            if not has_sponsorship_text(f"{title} {desc}", market):
                continue
            if not is_valid_job(title, company, job_url):
                continue

            jobs.append({
                "title":       title,
                "company":     company,
                "location":    loc,
                "market":      market,
                "sponsorship": "text-only",
                "salary":      salary,
                "url":         job_url,
                "description": desc[:500],
                "source":      "adzuna",
                "funded_saas": detect_funded_saas(desc),
                "found_at":    now_iso(),
            })

        page += 1
        time.sleep(1)

    log.info(f"Adzuna {country} '{query}' {location} → {len(jobs)} sponsored jobs")
    return jobs

# ── Source: Stepstone DE ──────────────────────────────────────────────────────

def scrape_stepstone_de(query: str, location: str) -> list:
    jobs = []
    encoded_query = requests.utils.quote(query.lower().replace(" ", "-"))
    encoded_loc   = requests.utils.quote(location.lower())
    url = f"https://www.stepstone.de/jobs/{encoded_query}/in-{encoded_loc}?radius=30&days=14"

    try:
        r = requests.get(url, headers=HEADERS, timeout=20)
        r.raise_for_status()
    except Exception as e:
        log.error(f"Stepstone DE '{query}' {location}: {e}")
        return []

    soup = BeautifulSoup(r.text, "html.parser")
    cards = soup.find_all("article", attrs={"data-genesis-element": "BASE"}) or \
            soup.find_all("article", class_=lambda c: c and "job" in c.lower()) or \
            soup.find_all("li", class_=lambda c: c and "job" in c.lower())

    for card in cards[:30]:
        title_el   = card.find(["h2", "h3", "a"], class_=lambda c: c and "title" in str(c).lower())
        company_el = card.find(class_=lambda c: c and "company" in str(c).lower())
        loc_el     = card.find(class_=lambda c: c and ("location" in str(c).lower() or "city" in str(c).lower()))
        link_el    = card.find("a", href=True)
        desc_el    = card.find(class_=lambda c: c and "description" in str(c).lower())

        title   = title_el.get_text(strip=True)   if title_el   else ""
        company = company_el.get_text(strip=True) if company_el else ""
        loc     = loc_el.get_text(strip=True)     if loc_el     else location
        desc    = desc_el.get_text(strip=True)    if desc_el    else ""
        job_url = link_el["href"] if link_el else ""
        if job_url and job_url.startswith("/"):
            job_url = "https://www.stepstone.de" + job_url

        if not has_sponsorship_text(f"{title} {desc}", "de"):
            continue
        if not is_valid_job(title, company, job_url):
            continue

        jobs.append({
            "title":       title,
            "company":     company,
            "location":    loc or location,
            "market":      "de",
            "sponsorship": "text-only",
            "salary":      "",
            "url":         job_url,
            "description": desc[:500],
            "source":      "stepstone_de",
            "funded_saas": detect_funded_saas(desc),
            "found_at":    now_iso(),
        })

    log.info(f"Stepstone DE '{query}' {location} → {len(jobs)} sponsored jobs")
    return jobs

# ── Source: Stepstone NL ──────────────────────────────────────────────────────

def scrape_stepstone_nl(query: str, location: str = "Amsterdam") -> list:
    jobs = []
    encoded_query = requests.utils.quote(query.lower().replace(" ", "-"))
    url = f"https://www.stepstone.nl/vacatures/{encoded_query}/in-{location.lower()}?radius=20&days=14"

    try:
        r = requests.get(url, headers=HEADERS, timeout=20)
        r.raise_for_status()
    except Exception as e:
        log.error(f"Stepstone NL '{query}': {e}")
        return []

    soup = BeautifulSoup(r.text, "html.parser")
    cards = soup.find_all("article", attrs={"data-genesis-element": "BASE"}) or \
            soup.find_all("article", class_=lambda c: c and "job" in c.lower())

    for card in cards[:30]:
        title_el   = card.find(["h2", "h3"], class_=lambda c: c and "title" in str(c).lower())
        company_el = card.find(class_=lambda c: c and "company" in str(c).lower())
        link_el    = card.find("a", href=True)
        desc_el    = card.find(class_=lambda c: c and "description" in str(c).lower())

        title   = title_el.get_text(strip=True)   if title_el   else ""
        company = company_el.get_text(strip=True) if company_el else ""
        desc    = desc_el.get_text(strip=True)    if desc_el    else ""
        job_url = link_el["href"] if link_el else ""
        if job_url and job_url.startswith("/"):
            job_url = "https://www.stepstone.nl" + job_url

        if not has_sponsorship_text(f"{title} {desc}", "nl"):
            continue
        if not is_valid_job(title, company, job_url):
            continue

        jobs.append({
            "title":       title,
            "company":     company,
            "location":    location,
            "market":      "nl",
            "sponsorship": "text-only",
            "salary":      "",
            "url":         job_url,
            "description": desc[:500],
            "source":      "stepstone_nl",
            "funded_saas": detect_funded_saas(desc),
            "found_at":    now_iso(),
        })

    log.info(f"Stepstone NL '{query}' → {len(jobs)} sponsored jobs")
    return jobs

# ── Source: LinkedIn EU ───────────────────────────────────────────────────────

def scrape_linkedin_eu(query: str, location: str, market: str) -> list:
    jobs = []
    url = (
        f"https://www.linkedin.com/jobs/search?keywords={requests.utils.quote(query)}"
        f"&location={requests.utils.quote(location)}&f_TPR=r604800&count=25"
    )
    try:
        r = requests.get(url, headers=HEADERS, timeout=20)
        r.raise_for_status()
    except Exception as e:
        log.error(f"LinkedIn EU '{query}' {location}: {e}")
        return []

    soup = BeautifulSoup(r.text, "html.parser")
    cards = soup.find_all("div", class_=lambda c: c and "job-search-card" in str(c))

    for card in cards[:20]:
        title_el   = card.find("h3", class_=lambda c: c and "title" in str(c).lower())
        company_el = card.find("h4", class_=lambda c: c and "company" in str(c).lower())
        loc_el     = card.find(class_=lambda c: c and "location" in str(c).lower())
        link_el    = card.find("a", class_=lambda c: c and "base-card__full-link" in str(c))

        title   = title_el.get_text(strip=True)   if title_el   else ""
        company = company_el.get_text(strip=True) if company_el else ""
        loc     = loc_el.get_text(strip=True)     if loc_el     else location
        job_url = link_el["href"].split("?")[0]   if link_el    else ""

        if not is_valid_job(title, company, job_url):
            continue

        # Fetch description for sponsorship check
        desc = ""
        if job_url:
            try:
                dr = requests.get(job_url, headers=HEADERS, timeout=12)
                dsoup = BeautifulSoup(dr.text, "html.parser")
                desc_el = dsoup.find(class_=lambda c: c and "description" in str(c).lower())
                desc = desc_el.get_text(strip=True)[:500] if desc_el else ""
            except Exception:
                pass

        if not has_sponsorship_text(f"{title} {desc}", market):
            continue

        jobs.append({
            "title":       title,
            "company":     company,
            "location":    loc,
            "market":      market,
            "sponsorship": "text-only",
            "salary":      "",
            "url":         job_url,
            "description": desc,
            "source":      "linkedin",
            "funded_saas": detect_funded_saas(desc),
            "found_at":    now_iso(),
        })
        time.sleep(0.5)

    log.info(f"LinkedIn '{query}' {location} → {len(jobs)} sponsored jobs")
    return jobs

# ── Source: Greenhouse EU ─────────────────────────────────────────────────────

GREENHOUSE_COMPANIES = [
    "personio", "n26", "gorillas", "trade-republic", "sumup", "contentful",
    "adjust", "thermondo", "taxfix", "nuri", "forto", "chrono24", "doctolib",
    "mollie", "messagebird", "adyen", "booking", "takeaway", "picnic",
    "bunq", "leapsome", "komoot", "pleo", "zavvy", "lano", "payhawk",
    "remote", "deel", "rippling", "workmotion", "omnipresent",
    "framer", "miro", "elastic", "gitlab", "datadog", "segment",
    "hightouch", "census", "clay", "outreach", "salesloft",
]

def scrape_greenhouse_eu(query: str, market: str) -> list:
    jobs = []
    de_kw = ["berlin", "munich", "münchen", "hamburg", "frankfurt", "germany", "deutschland", "remote"]
    nl_kw = ["amsterdam", "netherlands", "nederland", "remote"]
    loc_keywords = de_kw if market == "de" else nl_kw

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
            title   = item.get("title", "")
            loc     = item.get("location", {}).get("name", "")
            job_url = item.get("absolute_url", "")
            desc    = BeautifulSoup(item.get("content", ""), "html.parser").get_text()

            loc_lower = loc.lower()
            if not any(kw in loc_lower for kw in loc_keywords):
                continue

            q_lower = query.lower()
            title_lower = title.lower()
            if not any(kw in title_lower for kw in [
                "ai engineer", "gtm engineer", "gtm systems", "revenue engineer",
                "growth engineer", "automation engineer", "agentic",
            ]):
                continue

            if not is_valid_job(title, company, job_url):
                continue
            if not has_sponsorship_text(f"{title} {desc}", market):
                continue

            jobs.append({
                "title":       title,
                "company":     company.replace("-", " ").title(),
                "location":    loc,
                "market":      market,
                "sponsorship": "text-only",
                "salary":      "",
                "url":         job_url,
                "description": desc[:500],
                "source":      "greenhouse",
                "funded_saas": detect_funded_saas(desc),
                "found_at":    now_iso(),
            })

        time.sleep(0.2)

    log.info(f"Greenhouse EU '{query}' {market} → {len(jobs)} jobs")
    return jobs

# ── Push to backend ───────────────────────────────────────────────────────────

def push_to_backend(jobs: list) -> dict:
    if not jobs:
        return {"imported": 0, "skipped": 0}
    payload = []
    for j in jobs:
        payload.append({
            "id":          j["id"],
            "title":       j["title"],
            "company":     j["company"],
            "location":    j["location"],
            "market":      j["market"],
            "sponsorship": j.get("sponsorship", "text-only"),
            "salary":      j.get("salary", ""),
            "url":         j["url"],
            "description": j.get("description", ""),
            "source":      j["source"],
            "found_at":    j["found_at"],
            "funded_saas": j.get("funded_saas", False),
        })
    try:
        r = requests.post(
            f"{BACKEND_URL}/api/sponsored/import",
            json=payload,
            timeout=60,
        )
        result = r.json()
        log.info(f"Backend import: {result}")
        return result
    except Exception as e:
        log.error(f"Backend push failed: {e}")
        return {"imported": 0, "skipped": 0}

# ── Main run ──────────────────────────────────────────────────────────────────

def run_scrape():
    log.info("=" * 60)
    log.info("Starting EU scrape (Germany + Netherlands)")
    seen = load_seen()
    raw  = []

    for query in SEARCH_QUERIES:
        # Germany
        for loc in DE_LOCATIONS:
            raw += scrape_adzuna_eu(query, "de", loc)
            raw += scrape_stepstone_de(query, loc)
        raw += scrape_linkedin_eu(query, "Berlin, Germany", "de")
        raw += scrape_linkedin_eu(query, "Munich, Germany", "de")
        raw += scrape_greenhouse_eu(query, "de")

        # Netherlands
        raw += scrape_adzuna_eu(query, "nl", "Amsterdam")
        raw += scrape_stepstone_nl(query, "Amsterdam")
        raw += scrape_linkedin_eu(query, "Amsterdam, Netherlands", "nl")
        raw += scrape_greenhouse_eu(query, "nl")

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

    log.info(f"Found {len(new_jobs)} new EU jobs (from {len(raw)} raw)")

    if new_jobs:
        all_jobs = load_jobs() + new_jobs
        save_jobs(all_jobs)
        save_seen(seen)
        result = push_to_backend(new_jobs)
        log.info(f"Pushed to backend: {result}")

    # Summary
    de_count = sum(1 for j in new_jobs if j.get("market") == "de")
    nl_count = sum(1 for j in new_jobs if j.get("market") == "nl")
    log.info(f"DE: {de_count} | NL: {nl_count} | Total new: {len(new_jobs)}")
    print(f"\n{'='*50}")
    print(f"🇩🇪 Germany: {de_count} new sponsored jobs")
    print(f"🇳🇱 Netherlands: {nl_count} new sponsored jobs")
    print(f"{'='*50}")

    for j in new_jobs[:20]:
        flag = "🇩🇪" if j.get("market") == "de" else "🇳🇱"
        funded = " 🚀" if j.get("funded_saas") else ""
        print(f"  {flag}{funded}  {j['title']} @ {j['company']} — {j['location']}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--once", action="store_true", help="Run once and exit")
    parser.add_argument("--interval", type=int, default=6, help="Hours between runs")
    args = parser.parse_args()

    run_scrape()

    if not args.once:
        schedule.every(args.interval).hours.do(run_scrape)
        import time as _time
        while True:
            schedule.run_pending()
            _time.sleep(60)
