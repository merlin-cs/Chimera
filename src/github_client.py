"""
GitHub API client with caching, rate-limit handling, and retry logic.

Single Responsibility: HTTP communication with the GitHub REST API.
"""

import json
import logging
import os
import re
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Dict, Iterator, Optional

import requests

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Cache helpers
# ---------------------------------------------------------------------------

_DEFAULT_CACHE_EXPIRATION = timedelta(hours=24)


def _safe_cache_key(raw: str) -> str:
    """Sanitise a cache key so it is safe for use as a filename."""
    return re.sub(r"[^a-zA-Z0-9_\-\.]", "_", raw)


class GitHubAPI:
    """Thin wrapper around the GitHub REST API with built-in caching and retry."""

    def __init__(
        self,
        token: Optional[str] = None,
        cache_dir: Optional[Path] = None,
        cache_expiration: timedelta = _DEFAULT_CACHE_EXPIRATION,
        max_retries: int = 5,
    ) -> None:
        self.token = token or os.environ.get("GITHUB_TOKEN", "")
        self.cache_dir = cache_dir or Path.cwd() / ".github_cache"
        self.cache_expiration = cache_expiration
        self.max_retries = max_retries

        self.cache_dir.mkdir(parents=True, exist_ok=True)

        self._session = requests.Session()
        self._session.headers.update({"Accept": "application/vnd.github.v3+json"})
        if self.token:
            self._session.headers["Authorization"] = f"Bearer {self.token}"
        else:
            logger.warning("No GITHUB_TOKEN found. Rate limits will be restricted.")

    # -- Cache -----------------------------------------------------------------

    def _cache_path(self, key: str) -> Path:
        return self.cache_dir / f"{_safe_cache_key(key)}.json"

    def get_cached_data(self, cache_key: str) -> Optional[Any]:
        path = self._cache_path(cache_key)
        if not path.exists():
            return None
        try:
            with open(path, "r", encoding="utf-8") as fh:
                cached = json.load(fh)
            cached_time = datetime.fromisoformat(cached["timestamp"])
            if datetime.now() - cached_time > self.cache_expiration:
                return None
            return cached["data"]
        except (json.JSONDecodeError, KeyError, ValueError) as exc:
            logger.warning("Cache read error for %s: %s", cache_key, exc)
            return None

    def cache_data(self, cache_key: str, data: Any) -> None:
        path = self._cache_path(cache_key)
        payload = {"timestamp": datetime.now().isoformat(), "data": data}
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh)

    # -- Request ---------------------------------------------------------------

    def request(
        self,
        url: str,
        params: Optional[Dict[str, Any]] = None,
        cache_key: Optional[str] = None,
    ) -> Any:
        """GET *url* with optional caching and automatic retry / rate-limit back-off."""
        if cache_key:
            cached = self.get_cached_data(cache_key)
            if cached is not None:
                logger.debug("Cache hit: %s", cache_key)
                return cached

        retry_delay = 1
        for attempt in range(self.max_retries):
            try:
                response = self._session.get(url, params=params, timeout=30)

                # Rate-limit handling
                if response.status_code == 403 and "rate limit" in response.text.lower():
                    reset_ts = int(response.headers.get("X-RateLimit-Reset", 0))
                    wait = max(reset_ts - time.time(), 0) + 1
                    logger.warning("Rate limit exceeded. Waiting %.1fs …", wait)
                    time.sleep(wait)
                    continue

                if response.status_code == 404:
                    return None

                if response.status_code != 200:
                    logger.error("HTTP %d – %s", response.status_code, response.text[:200])
                    if attempt < self.max_retries - 1:
                        wait = retry_delay * (2 ** attempt)
                        logger.info("Retry %d/%d in %ds …", attempt + 1, self.max_retries, wait)
                        time.sleep(wait)
                        continue
                    response.raise_for_status()

                data = response.json()
                if cache_key:
                    self.cache_data(cache_key, data)

                remaining = int(response.headers.get("X-RateLimit-Remaining", 999))
                if remaining < 10:
                    logger.warning("Only %d API requests remaining.", remaining)

                return data

            except requests.RequestException as exc:
                logger.error("Request error: %s", exc)
                if attempt < self.max_retries - 1:
                    time.sleep(retry_delay * (2 ** attempt))
                else:
                    raise

        raise RuntimeError(f"GitHub API request failed after {self.max_retries} retries")


# ---------------------------------------------------------------------------
# Issue iteration
# ---------------------------------------------------------------------------

def iter_repo_issues(
    github: GitHubAPI,
    repo_full_name: str,
    start_date: Optional[datetime] = None,
    chunk_days: int = 90,
) -> Iterator[Dict[str, Any]]:
    """Yield closed issues from *repo_full_name*, paginated in date chunks.

    The GitHub Search API limits results to 1 000 per query; chunking by date
    avoids that ceiling.
    """
    base_url = "https://api.github.com/search/issues"
    base_query = f"repo:{repo_full_name} is:issue state:closed"
    end_date = datetime.now(timezone.utc)

    current_start = (
        start_date.replace(tzinfo=timezone.utc) if start_date else datetime(1970, 1, 1, tzinfo=timezone.utc)
    )
    chunk = timedelta(days=chunk_days)

    while current_start <= end_date:
        current_end = min(current_start + chunk, end_date)

        date_range = (
            f" created:{current_start.strftime('%Y-%m-%d')}..{current_end.strftime('%Y-%m-%d')}"
        )
        query = base_query + date_range

        page = 1
        while True:
            cache_key = f"search_{repo_full_name}_{current_start.strftime('%Y%m%d')}_{page}"
            try:
                data = github.request(
                    base_url,
                    params={"q": query, "per_page": 100, "page": page},
                    cache_key=cache_key,
                )
                items = data.get("items", []) if data else []
                if not items:
                    break
                yield from items
                if len(items) < 100:
                    break
                page += 1
                # Polite sleep when not served from cache
                if not github.get_cached_data(cache_key):
                    time.sleep(1)
            except Exception as exc:
                logger.error("Error fetching issues for %s: %s", repo_full_name, exc)
                break

        current_start = current_end + timedelta(days=1)
