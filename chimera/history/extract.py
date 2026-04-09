#!/usr/bin/env python3
"""
Chimera Corpus Extraction Tool

Extract logic-classified skeletons and building blocks from historical
bug-triggering formulas.

Usage:
    python -m chimera.history.extract \\
        --input ./bug_triggering_formulas \\
        --output ./chimera_resources \\
        --logic-mapping ./results.csv

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import argparse
import logging
import os
import sys
from pathlib import Path


def setup_logging(verbose: bool = False) -> None:
    """Configure logging."""
    level = logging.DEBUG if verbose else logging.INFO
    fmt = "%(asctime)s %(levelname)s %(message)s"
    logging.basicConfig(level=level, format=fmt, stream=sys.stdout)


def collect_smt_files(input_dir: str) -> list[str]:
    """Recursively collect all .smt2 files."""
    smt_files = []
    for root, _dirs, files in os.walk(input_dir):
        for f in files:
            if f.endswith(".smt2"):
                smt_files.append(os.path.join(root, f))
    return smt_files


def load_logic_mapping(mapping_file: str) -> dict[str, list[str]] | None:
    """Load logic-to-files mapping from CSV.

    Expected CSV format:
        file,logic
        /path/to/file1.smt2,QF_LIA
        /path/to/file2.smt2,QF_BV

    Returns None if file doesn't exist or can't be parsed.
    """
    if not os.path.exists(mapping_file):
        return None

    mapping: dict[str, list[str]] = {}

    try:
        with open(mapping_file, "r", encoding="utf-8") as f:
            lines = f.readlines()

        # Skip header if present
        start = 0
        if lines and lines[0].lower().startswith("file,logic"):
            start = 1

        for line in lines[start:]:
            line = line.strip()
            if not line:
                continue
            parts = line.split(",")
            if len(parts) < 2:
                continue

            file_path = parts[0].strip()
            logic = parts[1].strip().upper()

            if logic not in mapping:
                mapping[logic] = []
            mapping[logic].append(file_path)

        logging.info("Loaded logic mapping: %d logics from %s", len(mapping), mapping_file)
        return mapping

    except Exception as e:
        logging.warning("Failed to load logic mapping: %s", e)
        return None


def main() -> int:
    parser = argparse.ArgumentParser(
        prog="chimera-extract",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )

    parser.add_argument(
        "--input", "-i",
        required=True,
        help="Input directory with .smt2 files (recursively searched).",
    )
    parser.add_argument(
        "--output", "-o",
        required=True,
        help="Output directory for corpus JSON files.",
    )
    parser.add_argument(
        "--logic-mapping", "-m",
        default=None,
        help="CSV file with logic classifications (file,logic).",
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Enable debug logging.",
    )

    args = parser.parse_args()

    setup_logging(args.verbose)

    # Validate input
    if not os.path.isdir(args.input):
        logging.error("Input directory does not exist: %s", args.input)
        return 1

    # Collect files
    smt_files = collect_smt_files(args.input)
    logging.info("Found %d .smt2 files in %s", len(smt_files), args.input)

    if not smt_files:
        logging.warning("No .smt2 files found in %s", args.input)
        return 0

    # Load logic mapping
    logic_mapping = None
    if args.logic_mapping:
        logic_mapping = load_logic_mapping(args.logic_mapping)

    # Import and run extraction
    from chimera.history.extractor import LogicAwareExtractor

    extractor = LogicAwareExtractor(logic_mapping=logic_mapping)

    def progress(current: int, total: int, logic: str) -> None:
        if current % 50 == 0 or current == total:
            logging.info("Processed %d/%d files (current: %s)", current, total, logic)

    logging.info("Starting extraction...")
    corpus = extractor.extract_all(smt_files, progress_callback=progress)

    # Save corpus
    corpus.save(args.output)
    logging.info("Corpus saved to %s", args.output)

    # Print statistics
    stats = corpus.statistics()
    logging.info("Extraction complete:")
    logging.info("  Total blocks: %d", stats["total_blocks"])
    logging.info("  Total skeletons: %d", stats["total_skeletons"])
    logging.info("  Logics: %s", ", ".join(stats["logics"][:10]))
    if len(stats["logics"]) > 10:
        logging.info("  ... and %d more", len(stats["logics"]) - 10)
    logging.info("  QF skeletons: %d", stats["qf_skeletons"])
    logging.info("  Quantified skeletons: %d", stats["quantified_skeletons"])

    return 0


if __name__ == "__main__":
    sys.exit(main())
