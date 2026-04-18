#!/bin/bash
# Run the job scraper
cd "$(dirname "$0")"

# Load env vars if .env exists
if [ -f .env ]; then
  export $(grep -v '^#' .env | xargs)
fi

python3 scraper.py "$@"
