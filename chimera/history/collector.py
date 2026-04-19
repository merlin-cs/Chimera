"""
Collector for bug-triggering SMT formulas from solver issue trackers.

Provides importable functions for:
1. Collecting formulas from GitHub solver issue trackers
2. Standardising and classifying formulas by SMT-LIB logic
3. Extracting HistFuzz corpus (skeletons + building blocks)

Usage from CLI::

    python -m chimera.chimera_cli --mode update-resources \\
        --github-token $GITHUB_TOKEN \\
        --formula-store ./bug_triggering_formulas \\
        --resource-output ./chimera/resources

Or programmatically::

    from chimera.history.collector import update_resources
    update_resources(
        github_token="...",
        formula_store="./bug_triggering_formulas",
        resource_output="./chimera/resources",
    )

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""
from __future__ import annotations

import logging
import os
import re
import shutil
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional, Set, Tuple

logger = logging.getLogger("chimera.collector")

# ---------------------------------------------------------------------------
# GitHub collection
# ---------------------------------------------------------------------------

SOLVER_REPO_MAP = {
    "z3": "Z3Prover/z3",
    "cvc5": "cvc5/cvc5",
    "yices2": "SRI-CSL/yices2",
    "opensmt": "usi-verification-and-security/opensmt",
}

_BUG_TITLE_KEYWORDS = frozenset({
    "soundness", "bug", "issue", "invalid", "segfault", "correct",
    "assertion", "failure", "after-free", "leak", "overflow", "use after free",
    "crash", "panic", "abort", "exception", "internal error", "incorrect",
    "unsat", "unexpected", "model",
})

_CODE_BLOCK_RE = re.compile(
    r"(?:```|~~~)(?:[\w\-]*)?\r?\n(.*?)[\r\n]+(?:```|~~~)", re.DOTALL
)

_SMT_START_RE = re.compile(
    r"(\((?:set-|declare-|define-|assert|check-sat)|cat\s+\S+\.smt2)"
)


def check_title(title: str) -> bool:
    """Return ``True`` if *title* looks like a bug report."""
    lower = title.lower()
    return any(kw in lower for kw in _BUG_TITLE_KEYWORDS)


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
    if "(" not in candidate or ")" not in candidate:
        return None

    candidate = _truncate_at_balanced_end(candidate)
    if candidate is None:
        return None

    return candidate


def _truncate_at_balanced_end(text: str) -> Optional[str]:
    """Truncate after the last top-level balanced S-expression."""
    depth = 0
    last_balanced_end = -1
    in_string = False
    prev = ""
    for i, ch in enumerate(text):
        if ch == '"' and prev != "\\":
            in_string = not in_string
        elif not in_string:
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    last_balanced_end = i + 1
        prev = ch
    if last_balanced_end <= 0:
        return None
    return text[:last_balanced_end]


def _paren_depth(text: str) -> int:
    """Return net parenthesis depth."""
    depth = 0
    in_string = False
    prev = ""
    for ch in text:
        if ch == '"' and prev != "\\":
            in_string = not in_string
        elif not in_string:
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
        prev = ch
    return depth


@dataclass
class CollectionResult:
    """Summary of a formula collection run."""
    formulas_collected: int = 0
    formulas_standardized: int = 0
    formulas_failed: int = 0
    logics_found: Set[str] = None

    def __post_init__(self):
        if self.logics_found is None:
            self.logics_found = set()


def collect_from_github(
    token: str,
    store_dir: str,
    solvers: Optional[List[str]] = None,
    debug: bool = False,
) -> CollectionResult:
    """Collect bug-triggering formulas from solver GitHub issue trackers.

    Parameters
    ----------
    token : str
        GitHub personal access token.
    store_dir : str
        Directory to store collected .smt2 files.
    solvers : list[str], optional
        Which solvers to collect from. Default: all known solvers.
    debug : bool
        Enable verbose logging.

    Returns
    -------
    CollectionResult
        Summary of the collection.
    """
    from datetime import datetime

    from chimera.github_client import GitHubAPI, iter_repo_issues

    if debug:
        logging.getLogger().setLevel(logging.DEBUG)

    solvers = solvers or list(SOLVER_REPO_MAP.keys())
    result = CollectionResult()

    for solver in solvers:
        repo_name = SOLVER_REPO_MAP.get(solver)
        if not repo_name:
            logger.warning("Unknown solver: %s", solver)
            continue

        github_api = GitHubAPI(
            token=token,
            cache_dir=Path(store_dir) / ".github_cache",
        )

        solver_dir = Path(store_dir) / "cases"
        solver_dir.mkdir(parents=True, exist_ok=True)

        csv_path = Path(store_dir) / f"results_{solver}.csv"
        if not csv_path.exists():
            csv_path.write_text("file,logic\n", encoding="utf-8")

        # Status tracking
        status_file = Path(store_dir) / f"status_{solver}.json"
        last_scanned: Optional[str] = None
        if status_file.exists():
            try:
                last_scanned = status_file.read_text(encoding="utf-8").strip()
            except OSError:
                pass

        start_dt = None
        if last_scanned:
            try:
                start_dt = datetime.fromisoformat(last_scanned.replace("Z", "+00:00"))
            except ValueError:
                start_dt = datetime(1970, 1, 1)

        # Pre-scan existing files
        existing_files: Set[str] = set()
        for root, _, files in os.walk(store_dir):
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
                            file_path = str(solver_dir / file_base)
                            with open(file_path, "w", encoding="utf-8") as fh:
                                fh.write(formula)
                            std = standardize_single_instance(file_path)
                            if std:
                                final_path, logic = standardize_and_classify(std)
                                with open(csv_path, "a", encoding="utf-8") as csv_fh:
                                    csv_fh.write(f"{final_path},{logic}\n")
                                result.formulas_collected += 1
                                result.logics_found.add(logic)
                        count += 1

                # Update status
                if latest_date:
                    status_file.write_text(latest_date, encoding="utf-8")

            except Exception as exc:
                logger.error("Error processing issue %s: %s", issue.get("number", "?"), exc)

    return result


# ---------------------------------------------------------------------------
# Formula standardisation
# ---------------------------------------------------------------------------

def standardize_single_instance(file: str) -> Optional[str]:
    """Parse, normalise, and re-write *file* in-place.

    Uses the chimera SMT parser to validate and re-emit the formula.

    Returns the path on success or ``None`` (file removed) on failure.
    """
    from chimera.core.smt_parser import parse_file
    from chimera.core.smt_ast import (
        Assert, DeclareConst, DeclareFun, Define, DefineConst,
        CheckSat, Push, Pop, SMTLIBCommand,
    )

    _VALID_AST_TYPES = frozenset({
        Define, DefineConst, DeclareConst, DeclareFun,
        Assert, Push, Pop, CheckSat,
    })

    result = parse_file(file, silent=True)
    if result is None:
        if os.path.exists(file):
            os.remove(file)
        return None

    script, _global_vars = result

    new_lines: List[str] = []
    with open(file, "r", encoding="utf-8", errors="replace") as fh:
        for line in fh:
            stripped = line.strip()
            if "declare-sort" in stripped or "define-sort" in stripped:
                new_lines.append(stripped)

    for cmd in script.commands:
        if type(cmd) in _VALID_AST_TYPES:
            cmd_str = str(cmd).strip()
            if cmd_str and _paren_depth(cmd_str) == 0:
                new_lines.append(cmd_str)

    new_lines = [ln for ln in new_lines if ln.strip()]

    if not new_lines:
        if os.path.exists(file):
            os.remove(file)
        return None

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


def standardize_and_classify(file_path: str) -> Tuple[str, str]:
    """Detect the logic and move *file_path* into a logic-named sub-directory.

    Returns ``(new_path, logic)``.
    """
    from chimera.core.logic_analyzer import parse_logic, LogicCapability

    if not os.path.exists(file_path):
        return file_path, "UNKNOWN"

    try:
        # Try to detect logic from file content
        logic = _detect_logic_from_file(file_path)

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
        dest = os.path.join(unknown_dir, os.path.basename(file_path))
        counter = 1
        while os.path.exists(dest):
            base, ext = os.path.splitext(os.path.basename(file_path))
            dest = os.path.join(unknown_dir, f"{base}_{counter}{ext}")
            counter += 1
        try:
            shutil.move(file_path, dest)
            logger.error("Failed to classify %s; moved to UNKNOWN: %s", file_path, exc)
            return dest, "UNKNOWN"
        except OSError as exc2:
            logger.error("Failed to move %s to UNKNOWN: %s", file_path, exc2)
            return file_path, "UNKNOWN"


def _detect_logic_from_file(file_path: str) -> str:
    """Infer SMT-LIB logic from file content."""
    from chimera.core.smt_parser import parse_file

    try:
        result = parse_file(file_path, silent=True)
        if result is not None:
            script, _ = result
            script_str = str(script)

            has_quantifiers = "forall" in script_str or "exists" in script_str
            has_bv = "BitVec" in script_str
            has_fp = "FloatingPoint" in script_str
            has_arrays = "Array" in script_str or "select" in script_str or "store" in script_str
            has_uf = False
            has_int = "Int" in script_str
            has_real = "Real" in script_str
            has_nonlinear = "* " in script_str and (has_int or has_real)
            has_strings = "String" in script_str

            for cmd in script.commands:
                from chimera.core.smt_ast import DeclareFun
                if isinstance(cmd, DeclareFun) and cmd.input_sort != "":
                    has_uf = True
                    break

            parts = []
            if not has_quantifiers:
                parts.append("QF")
            if has_arrays:
                parts.append("A")
            if has_uf:
                parts.append("UF")

            if has_int and has_real:
                parts.append("NIRA" if has_nonlinear else "LIRA")
            elif has_int:
                parts.append("NIA" if has_nonlinear else "LIA")
            elif has_real:
                parts.append("NRA" if has_nonlinear else "LRA")

            if has_bv:
                parts.append("BV")
            if has_fp:
                parts.append("FP")
            if has_strings:
                parts.append("S")

            if not parts:
                return "UF"

            logic = "".join(parts)
            # Normalize: QF + single theory without UF -> add UF
            if logic.startswith("QF") and "UF" not in logic and len(parts) == 2:
                logic = logic[:2] + "UF" + logic[2:]

            return logic

    except Exception:
        pass

    return "UNKNOWN"


# ---------------------------------------------------------------------------
# Corpus extraction
# ---------------------------------------------------------------------------

def extract_corpus(
    input_dir: str,
    output_dir: str,
    logic_mapping_file: Optional[str] = None,
) -> CollectionResult:
    """Extract skeletons and building blocks from .smt2 formulas.

    Parameters
    ----------
    input_dir : str
        Directory containing .smt2 files (recursively searched).
    output_dir : str
        Directory to save corpus JSON files.
    logic_mapping_file : str, optional
        CSV file with logic classifications (file,logic).

    Returns
    -------
    CollectionResult
        Summary of the extraction.
    """
    from chimera.history.extract import collect_smt_files, load_logic_mapping
    from chimera.history.extractor import LogicAwareExtractor

    smt_files = collect_smt_files(input_dir)
    logger.info("Found %d .smt2 files in %s", len(smt_files), input_dir)

    if not smt_files:
        logger.warning("No .smt2 files found in %s", input_dir)
        return CollectionResult()

    # Load logic mapping if provided
    logic_mapping = None
    if logic_mapping_file:
        logic_mapping = load_logic_mapping(logic_mapping_file)

    extractor = LogicAwareExtractor(logic_mapping=logic_mapping)

    def progress(current: int, total: int, logic: str) -> None:
        if current % 50 == 0 or current == total:
            logger.info("Processed %d/%d files (current: %s)", current, total, logic)

    logger.info("Starting extraction...")
    corpus = extractor.extract_all(smt_files, progress_callback=progress)

    # Save corpus
    corpus.save(output_dir)
    logger.info("Corpus saved to %s", output_dir)

    stats = corpus.statistics()
    result = CollectionResult(
        formulas_standardized=stats["total_blocks"] + stats["total_skeletons"],
        logics_found=set(stats["logics"]),
    )

    logger.info("Extraction complete:")
    logger.info("  Total blocks: %d", stats["total_blocks"])
    logger.info("  Total skeletons: %d", stats["total_skeletons"])
    logger.info("  Logics: %s", ", ".join(stats["logics"][:10]))

    return result


# ---------------------------------------------------------------------------
# Combined workflow
# ---------------------------------------------------------------------------

def update_resources(
    github_token: Optional[str] = None,
    formula_store: str = "./bug_triggering_formulas",
    resource_output: str = "./chimera/resources",
    solvers: Optional[List[str]] = None,
    skip_collection: bool = False,
    debug: bool = False,
) -> CollectionResult:
    """Run the full resource update pipeline.

    Parameters
    ----------
    github_token : str, optional
        GitHub personal access token. Required unless *skip_collection* is True.
    formula_store : str
        Directory for collected/formula files. Default: ``./bug_triggering_formulas``.
    resource_output : str
        Output directory for HistFuzz corpus. Default: ``./chimera/resources``.
    solvers : list[str], optional
        Which solvers to collect from. Default: all.
    skip_collection : bool
        Skip GitHub collection and only extract from existing files.
    debug : bool
        Enable verbose logging.

    Returns
    -------
    CollectionResult
        Combined summary of collection and extraction.
    """
    combined = CollectionResult()

    # Step 1: Collect from GitHub (optional)
    if not skip_collection:
        if not github_token:
            github_token = os.environ.get("GITHUB_TOKEN", "")
        if not github_token:
            logger.warning(
                "No GitHub token provided. Set --github-token or GITHUB_TOKEN env var, "
                "or use --skip-collection to only extract from existing files."
            )
        else:
            logger.info("Step 1: Collecting bug formulas from GitHub...")
            collect_result = collect_from_github(
                token=github_token,
                store_dir=formula_store,
                solvers=solvers,
                debug=debug,
            )
            combined.formulas_collected = collect_result.formulas_collected
            combined.logics_found |= collect_result.logics_found
            logger.info("  Collected %d new formulas", collect_result.formulas_collected)

    # Step 2: Extract corpus
    input_dir = os.path.join(formula_store, "cases")
    if not os.path.isdir(input_dir):
        # Try the store itself
        if os.path.isdir(formula_store):
            input_dir = formula_store
        else:
            logger.error("No formula directory found at %s or %s", input_dir, formula_store)
            return combined

    logger.info("Step 2: Extracting corpus from %s...", input_dir)
    extract_result = extract_corpus(
        input_dir=input_dir,
        output_dir=resource_output,
    )
    combined.formulas_standardized = extract_result.formulas_standardized
    combined.logics_found |= extract_result.logics_found

    logger.info("Resource update complete:")
    logger.info("  New formulas collected: %d", combined.formulas_collected)
    logger.info("  Total skeletons + blocks: %d", combined.formulas_standardized)
    logger.info("  Logics: %s", ", ".join(sorted(combined.logics_found)))

    return combined
