"""
Collector for bug-triggering SMT formulas from solver issue trackers.

Responsibilities:
  - Scrape GitHub issues for SMT2 code blocks.
  - Standardise and classify collected formulas by logic.
  - Export artefacts (buggy seeds, skeletons) for the history fuzzer.
"""

from __future__ import annotations

import argparse
import logging
import multiprocessing
import os
import re
import shutil
import sys
from pathlib import Path
from typing import List, Optional, Set

import z3  # noqa: F401 – used inside SMTLogicDetector (imported below)

# ---------------------------------------------------------------------------
# Project path setup
# ---------------------------------------------------------------------------
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.parsing.Parse import parse_file
from src.parsing.Ast import (
    DeclareFun, Define, DeclareConst, DefineConst, FunDecl,
    Assert, CheckSat, Push, Pop, Term,
)
from src.formula_utils import process_seed
from src.history.building_blocks import export_buggy_seed
from src.history.skeleton import export_skeleton
from src.github_client import GitHubAPI, iter_repo_issues
from src.logic_detector import get_smt_logic

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    handlers=[logging.StreamHandler()],
)
logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
CURRENT_DIR = Path(__file__).parent
CACHE_DIR = CURRENT_DIR / "github_cache"
CACHE_DIR.mkdir(exist_ok=True)

SOLVER_REPO_MAP = {
    "z3": "Z3Prover/z3",
    "cvc5": "cvc5/cvc5",
    "yices2": "SRI-CSL/yices2",
    "opensmt": "usi-verification-and-security/opensmt",
    "cvc5-projects": "cvc5/cvc5",
}

_VALID_AST_TYPES = frozenset({
    Define, DefineConst, DeclareConst, DeclareFun, FunDecl,
    Assert, Push, Pop, CheckSat,
})

_BUG_TITLE_KEYWORDS = frozenset({
    "soundness", "bug", "issue", "invalid", "segfault", "correct",
    "assertion", "failure", "after-free", "leak", "overflow", "use after free",
    "crash", "panic", "abort", "exception", "internal error", "incorrect",
    "unsat", "unexpected", "model",
})

# ---------------------------------------------------------------------------
# Status tracking (incremental scanning)
# ---------------------------------------------------------------------------

def _status_path(solver: str) -> Path:
    """Return the path to the scan-progress file for *solver*."""
    # Sanitise to prevent directory traversal
    safe = re.sub(r"[^a-zA-Z0-9_\-]", "_", solver)
    return CURRENT_DIR / f"status_{safe}.json"


def get_last_scanned_date(solver: str) -> Optional[str]:
    path = _status_path(solver)
    if path.exists():
        try:
            return path.read_text(encoding="utf-8").strip()
        except OSError as exc:
            logger.error("Error reading status file: %s", exc)
    return None


def save_last_scanned_date(solver: str, date_str: str) -> None:
    try:
        _status_path(solver).write_text(date_str, encoding="utf-8")
    except OSError as exc:
        logger.error("Error saving status file: %s", exc)


# ---------------------------------------------------------------------------
# Title filtering
# ---------------------------------------------------------------------------

def check_title(title: str) -> bool:
    """Return ``True`` if *title* looks like a bug report."""
    lower = title.lower()
    return any(kw in lower for kw in _BUG_TITLE_KEYWORDS)


# ---------------------------------------------------------------------------
# SMT2 extraction from Markdown
# ---------------------------------------------------------------------------

_CODE_BLOCK_RE = re.compile(
    r"(?:```|~~~)(?:[\w\-]*)?\r?\n(.*?)[\r\n]+(?:```|~~~)", re.DOTALL
)

_SMT_START_RE = re.compile(
    r"(\((?:set-|declare-|define-|assert|check-sat)|cat\s+\S+\.smt2)"
)


def extract_formulas(content: str) -> List[str]:
    """Extract all SMT2 formulas from Markdown *content*."""
    formulas = []
    for block in _CODE_BLOCK_RE.findall(content):
        smt2 = _clean_smt2_payload(block)
        if smt2:
            formulas.append(smt2)
    if not formulas:
        smt2 = _clean_smt2_payload(content)
        if smt2:
            formulas.append(smt2)
    return formulas


def _clean_smt2_payload(text: str) -> Optional[str]:
    """Locate and return the SMT2 portion of *text*, or ``None``."""
    match = _SMT_START_RE.search(text)
    if not match:
        return None

    start = match.start()
    if text[start:].startswith("cat"):
        nl = text.find("\n", start)
        if nl == -1:
            return None
        start = nl + 1

    candidate = text[start:]
    if "(" in candidate and ")" in candidate:
        return candidate
    return None


# ---------------------------------------------------------------------------
# Formula standardisation & classification
# ---------------------------------------------------------------------------

def standardize_single_instance(file: str) -> Optional[str]:
    """Parse, normalise, and re-write *file* in-place.

    Returns the path on success or ``None`` (file removed) on failure.
    """
    script, _var = process_seed(file)
    if script is None:
        if os.path.exists(file):
            os.remove(file)
        return None

    new_lines: List[str] = []
    with open(file, "r", encoding="utf-8", errors="replace") as fh:
        for line in fh:
            if "declare-sort" in line or "define-sort" in line:
                new_lines.append(line.rstrip("\n"))

    for cmd in script.commands:
        if type(cmd) in _VALID_AST_TYPES:
            new_lines.append(str(cmd))

    # Ensure (check-sat) terminator
    if len(new_lines) >= 2:
        if "(check-sat)" not in new_lines[-1] and "(check-sat)" not in new_lines[-2]:
            new_lines.append("(check-sat)")
    elif len(new_lines) == 1 and "(check-sat)" not in new_lines[-1]:
        new_lines.append("(check-sat)")

    with open(file, "w", encoding="utf-8") as fh:
        for line in new_lines:
            fh.write(line + "\n")
    return file


def classify_and_move(file_path: str):
    """Detect the logic and move *file_path* into a logic-named sub-directory.

    Returns ``(new_path, logic)`` or ``(file_path, "UNKNOWN")`` on failure.
    """
    if not os.path.exists(file_path):
        return file_path, "UNKNOWN"

    try:
        try:
            logic = get_smt_logic(file_path)
        except Exception:
            logic = None
        logic = logic if isinstance(logic, str) and logic else "UNKNOWN"

        directory = os.path.dirname(file_path)
        filename = os.path.basename(file_path)

        if os.path.basename(directory) == logic:
            return file_path, logic

        logic_dir = os.path.join(directory, logic)
        os.makedirs(logic_dir, exist_ok=True)

        base, ext = os.path.splitext(filename)
        new_path = os.path.join(logic_dir, filename)
        counter = 1
        while os.path.exists(new_path):
            new_path = os.path.join(logic_dir, f"{base}_{counter}{ext}")
            counter += 1

        shutil.move(file_path, new_path)
        logger.info("Classified %s as %s", filename, logic)
        return new_path, logic

    except Exception as exc:
        unknown_dir = os.path.join(os.path.dirname(file_path), "UNKNOWN")
        os.makedirs(unknown_dir, exist_ok=True)
        base, ext = os.path.splitext(os.path.basename(file_path))
        dest = os.path.join(unknown_dir, os.path.basename(file_path))
        counter = 1
        while os.path.exists(dest):
            dest = os.path.join(unknown_dir, f"{base}_{counter}{ext}")
            counter += 1
        try:
            shutil.move(file_path, dest)
            logger.error("Failed to classify %s; moved to UNKNOWN: %s", file_path, exc)
            return dest, "UNKNOWN"
        except OSError as exc2:
            logger.error("Failed to move %s to UNKNOWN: %s", file_path, exc2)
            return file_path, "UNKNOWN"


# ---------------------------------------------------------------------------
# Collection orchestration
# ---------------------------------------------------------------------------

def collect_buggy_formula(github_token: str, solver: str, stored_dir: str) -> None:
    """Collect bug-triggering formulas for *solver* into *stored_dir*."""
    from datetime import datetime

    repo_name = SOLVER_REPO_MAP.get(solver)
    if not repo_name:
        logger.error("Unknown solver: %s", solver)
        return

    github_api = GitHubAPI(
        token=github_token,
        cache_dir=CACHE_DIR,
    )

    base_stored_dir = stored_dir
    solver_dir = os.path.join(base_stored_dir, solver)
    os.makedirs(solver_dir, exist_ok=True)

    logger.info("Updating %s from %s …", solver, repo_name)

    csv_path = os.path.join(base_stored_dir, f"results_{solver}.csv")
    if not os.path.exists(csv_path):
        with open(csv_path, "w", encoding="utf-8") as fh:
            fh.write("file,logic\n")

    last_scanned = get_last_scanned_date(solver)
    start_dt = None
    if last_scanned:
        try:
            start_dt = datetime.fromisoformat(last_scanned.replace("Z", "+00:00"))
        except ValueError:
            start_dt = datetime(1970, 1, 1)

    # Pre-scan existing files to avoid re-processing
    existing_files: Set[str] = set()
    for root, _, files in os.walk(base_stored_dir):
        for f in files:
            if f.endswith(".smt2"):
                existing_files.add(f)

    latest_date = last_scanned

    for issue in iter_repo_issues(github_api, repo_name, start_date=start_dt):
        try:
            issue_number = issue["number"]
            issue_title = issue["title"]
            issue_body = issue.get("body", "") or ""
            issue_date = issue["created_at"]

            if not latest_date or issue_date > latest_date:
                latest_date = issue_date
            if last_scanned and issue_date <= last_scanned:
                continue
            if not check_title(issue_title):
                continue

            logger.info("Processing issue %s: %s", issue_number, issue_title)
            count = 0

            contents = [issue_body]
            if issue.get("comments", 0) > 0:
                comments_url = issue.get("comments_url")
                try:
                    comments = github_api.request(
                        comments_url,
                        params={"per_page": 100},
                        cache_key=f"comments_{repo_name}_{issue_number}",
                    )
                    if isinstance(comments, list):
                        contents.extend(c.get("body", "") or "" for c in comments)
                except Exception as exc:
                    logger.error("Error fetching comments for issue %s: %s", issue_number, exc)

            for content in contents:
                if not any(x in content for x in ("```", "~~~", "cat ", "declare-")):
                    continue
                for formula in extract_formulas(content):
                    file_base = f"{solver}_{issue_number}_{count}.smt2"
                    if file_base not in existing_files:
                        file_path = os.path.join(solver_dir, file_base)
                        with open(file_path, "w", encoding="utf-8") as fh:
                            fh.write(formula)
                        std = standardize_single_instance(file_path)
                        if std:
                            final_path, logic = classify_and_move(std)
                            with open(csv_path, "a", encoding="utf-8") as csv_fh:
                                csv_fh.write(f"{final_path},{logic}\n")
                    count += 1

            save_last_scanned_date(solver, issue_date)

        except Exception as exc:
            logger.error("Error processing issue %s: %s", issue.get("number", "?"), exc)


def auto_collect_buggy_formulas(token: Optional[str], store_path: str) -> None:
    """Spawn one process per solver to collect formulas concurrently."""
    solvers = list(SOLVER_REPO_MAP.keys())
    token = token or os.environ.get("GITHUB_TOKEN", "")

    processes = []
    for solver in solvers:
        p = multiprocessing.Process(target=collect_buggy_formula, args=(token, solver, store_path))
        p.start()
        processes.append(p)

    for p in processes:
        p.join()


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Collect bug-triggering SMT formulas from solver bug trackers",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python collect.py --token YOUR_GITHUB_TOKEN --store ./collected_formulas
  python collect.py --store ./collected_formulas   # uses GITHUB_TOKEN env var
""",
    )
    parser.add_argument("--token", type=str, help="GitHub personal access token")
    parser.add_argument("--store", type=str, required=True, help="directory for collected formulas")
    args = parser.parse_args()

    if args.token:
        auto_collect_buggy_formulas(args.token, args.store)
    else:
        logger.info("No token provided – skipping remote collection, using existing files in --store")

    if not os.path.exists(args.store):
        logger.error("Store path %s does not exist. Nothing to export.", args.store)
        sys.exit(1)

    resource_dir = REPO_ROOT / "src" / "history" / "resource"
    skeleton_file = resource_dir / "skeleton.smt2"
    export_buggy_seed(args.store, str(resource_dir))
    export_skeleton(args.store, str(skeleton_file))


if __name__ == "__main__":
    main()