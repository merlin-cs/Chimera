"""
Chimera CLI — unified command-line orchestrator.

Usage::

    python -m chimera.chimera_cli \\
        --mode histfuzz \\
        --solver1-name z3 --solver1-bin /usr/bin/z3 \\
        --solver2-name cvc5 --solver2-bin /usr/bin/cvc5 \\
        --seed-dir ./seeds \\
        --output-dir ./bugs \\
        --iterations 10000

Modes:
    histfuzz   — Skeleton enumeration with historical bug-triggering seeds.
    once4all   — LLM-synthesised generator integration.
    aries      — Mimetic mutation + equality saturation.

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import argparse
import logging
import sys
from pathlib import Path
from typing import List, Optional

from chimera.core.solver_manager import SolverConfig, default_cvc5_args, default_z3_args
from chimera.core.differential_oracle import OracleConfig
from chimera.engines.base import FuzzingStrategy, FuzzStats
from chimera.engines.histfuzz_engine import HistFuzzStrategy
from chimera.engines.once4all_engine import Once4AllStrategy
from chimera.engines.aries_engine import AriesStrategy
from chimera.resources import REWRITE_RULES_CSV, REWRITE_CONFIG_DIR
from chimera.history.collector import update_resources as _update_resources

logger = logging.getLogger("chimera")


# ---------------------------------------------------------------------------
# CLI argument parser
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="chimera",
        description="Chimera — differential SMT solver fuzzer.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )

    # -- mode ----------------------------------------------------------------
    p.add_argument(
        "--mode",
        choices=["histfuzz", "once4all", "aries", "update-resources"],
        required=True,
        help="Fuzzing strategy to use, or 'update-resources' to refresh HistFuzz corpus.",
    )

    # -- solvers -------------------------------------------------------------
    # Solver args required for fuzzing modes; validated in _validate_args().
    sol = p.add_argument_group("Solver configuration")
    sol.add_argument("--solver1-name", default="z3", help="Name of solver 1 (default: z3).")
    sol.add_argument("--solver1-bin", default=None, help="Path to solver 1 binary.")
    sol.add_argument("--solver2-name", default="cvc5", help="Name of solver 2 (default: cvc5).")
    sol.add_argument("--solver2-bin", default=None, help="Path to solver 2 binary.")
    sol.add_argument("--solver-timeout", type=float, default=10.0, help="Per-query timeout (seconds).")

    # -- I/O -----------------------------------------------------------------
    io = p.add_argument_group("Input / output")
    io.add_argument("--seed-dir", default="", help="Directory with seed .smt2 files.")
    io.add_argument("--output-dir", default="./chimera_bugs", help="Directory for bug artifacts.")
    io.add_argument("--temp-dir", default="./chimera_temp", help="Scratch directory.")

    # -- campaign ------------------------------------------------------------
    camp = p.add_argument_group("Campaign settings")
    camp.add_argument("--iterations", type=int, default=0, help="Max iterations (0 = unlimited).")

    # -- HistFuzz options ----------------------------------------------------
    hf = p.add_argument_group("HistFuzz options")
    hf.add_argument("--skeleton-files", nargs="*", default=None, help="Pre-exported skeleton files.")
    hf.add_argument("--resource-dir", default=None, help="Resource dir with skeleton/building-block files.")
    hf.add_argument("--num-asserts", type=int, default=3, help="Max assertions per generated formula.")
    hf.add_argument("--logic", type=str, default=None,
                    help="Target SMT-LIB logic (e.g., QF_LIA, AUFLIA). Only use compatible skeletons/blocks.")
    hf.add_argument("--use-new-corpus", action="store_true",
                    help="Use new logic-aware corpus system (experimental).")

    # -- Once4All options ----------------------------------------------------
    o4a = p.add_argument_group("Once4All options")
    o4a.add_argument("--generator-dir", default=None, help="Directory with *_generator.py modules.")
    o4a.add_argument("--theories", nargs="*", default=None, help="Restrict to these theory keys.")
    o4a.add_argument("--merge-skeletons", action="store_true", help="Amplify diversity via skeleton extraction.")

    # -- Aries options -------------------------------------------------------
    ar = p.add_argument_group("Aries options")
    ar.add_argument("--rules-csv", default=str(REWRITE_RULES_CSV), help="Path to RewriteRule.csv.")
    ar.add_argument("--config-dir", default=str(REWRITE_CONFIG_DIR), help="Operator config directory for mimetic mutation.")
    ar.add_argument("--mimetic-rounds", type=int, default=3, help="Mimetic mutation rounds per seed.")
    ar.add_argument("--no-egraph", action="store_true", help="Disable equality saturation.")

    # -- update-resources options ---------------------------------------------
    ur = p.add_argument_group("Resource update options (mode=update-resources)")
    ur.add_argument("--github-token", default=None,
                    help="GitHub personal access token for collecting bug formulas from issue trackers.")
    ur.add_argument("--formula-store", default="./bug_triggering_formulas",
                    help="Directory for collected bug formulas (default: ./bug_triggering_formulas).")
    ur.add_argument("--resource-output", default="./chimera/resources",
                    help="Output directory for HistFuzz corpus (default: ./chimera/resources).")
    ur.add_argument("--collect-solvers", nargs="*", default=None,
                    help="Collect from specific solvers only (default: all known solvers).")
    ur.add_argument("--skip-collection", action="store_true",
                    help="Skip GitHub collection; only extract corpus from existing formula files.")

    # -- oracle --------------------------------------------------------------
    orc = p.add_argument_group("Oracle tuning")
    # New negation flags (preferred)
    orc.add_argument("--no-crash-detection", action="store_true",
                     help="Disable crash detection (enabled by default).")
    orc.add_argument("--no-soundness-detection", action="store_true",
                     help="Disable soundness bug detection (enabled by default).")
    # Deprecated: kept for backward compatibility (no-op, enabled by default)
    orc.add_argument("--detect-crashes", action="store_true", default=True,
                     help=argparse.SUPPRESS)  # Deprecated: crashes detected by default
    orc.add_argument("--detect-soundness", action="store_true", default=True,
                     help=argparse.SUPPRESS)  # Deprecated: soundness checked by default
    orc.add_argument("--detect-invalid-models", action="store_true", default=False,
                     help="Report invalid models.")
    orc.add_argument("--detect-performance", action="store_true", default=False,
                     help="Report perf regressions.")
    orc.add_argument("--performance-ratio", type=float, default=10.0,
                     help="Threshold for perf bugs.")

    # -- logging -------------------------------------------------------------
    p.add_argument("-v", "--verbose", action="store_true", help="DEBUG-level logging.")
    p.add_argument("-q", "--quiet", action="store_true", help="WARNING-level logging only.")

    return p


# ---------------------------------------------------------------------------
# Solver construction helpers
# ---------------------------------------------------------------------------

def _make_solver(name: str, binary: str) -> SolverConfig:
    n = name.strip().lower()
    if n in ("z3",):
        return SolverConfig(name=name, binary=binary, base_args=default_z3_args())
    if n in ("cvc5",):
        return SolverConfig(name=name, binary=binary, base_args=default_cvc5_args())
    # Generic — no special args
    return SolverConfig(name=name, binary=binary)


# ---------------------------------------------------------------------------
# Engine factory
# ---------------------------------------------------------------------------

def _build_strategy(args: argparse.Namespace) -> FuzzingStrategy:
    solver1 = _make_solver(args.solver1_name, args.solver1_bin)
    solver2 = _make_solver(args.solver2_name, args.solver2_bin)

    oracle_cfg = OracleConfig(
        detect_crashes=not args.no_crash_detection,
        detect_soundness=not args.no_soundness_detection,
        detect_invalid_models=args.detect_invalid_models,
        detect_performance=args.detect_performance,
        performance_ratio=args.performance_ratio,
    )

    common = dict(
        output_dir=args.output_dir,
        temp_dir=args.temp_dir,
        timeout=args.solver_timeout,
        oracle_config=oracle_cfg,
    )

    mode = args.mode

    if mode == "histfuzz":
        return HistFuzzStrategy(
            solver1,
            solver2,
            seed_dir=args.seed_dir,
            skeleton_files=args.skeleton_files,
            resource_dir=args.resource_dir,
            logic=args.logic,
            use_new_corpus=args.use_new_corpus,
            num_asserts=args.num_asserts,
            **common,
        )

    if mode == "once4all":
        return Once4AllStrategy(
            solver1,
            solver2,
            generator_dir=args.generator_dir,
            compatible_theories=args.theories,
            merge_skeletons=args.merge_skeletons,
            **common,
        )

    if mode == "aries":
        return AriesStrategy(
            solver1,
            solver2,
            seed_dir=args.seed_dir,
            rules_csv=args.rules_csv,
            config_dir=args.config_dir,
            mimetic_rounds=args.mimetic_rounds,
            use_egraph=not args.no_egraph,
            **common,
        )

    raise ValueError(f"Unknown mode: {mode}")


# ---------------------------------------------------------------------------
# Logging setup
# ---------------------------------------------------------------------------

def _configure_logging(verbose: bool, quiet: bool) -> None:
    level = logging.DEBUG if verbose else (logging.WARNING if quiet else logging.INFO)
    fmt = "%(asctime)s %(name)-14s %(levelname)-7s %(message)s"
    logging.basicConfig(level=level, format=fmt, stream=sys.stderr)


# ---------------------------------------------------------------------------
# Resource update mode
# ---------------------------------------------------------------------------

def _run_update_resources(args: argparse.Namespace) -> int:
    """Execute the resource update pipeline."""
    try:
        result = _update_resources(
            github_token=args.github_token,
            formula_store=args.formula_store,
            resource_output=args.resource_output,
            solvers=args.collect_solvers,
            skip_collection=args.skip_collection,
            debug=args.verbose,
        )
    except KeyboardInterrupt:
        logger.info("Resource update interrupted by user")
        return 1

    print("\n=== Resource Update Summary ===")
    print(f"  Formulas collected from GitHub: {result.formulas_collected}")
    print(f"  Skeletons + blocks in corpus:   {result.formulas_standardized}")
    print(f"  Logics covered:                 {', '.join(sorted(result.logics_found)) if result.logics_found else 'none'}")
    return 0


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------

def main(argv: Optional[List[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    _configure_logging(args.verbose, args.quiet)

    # -- Validate solver args for fuzzing modes -------------------------------
    if args.mode != "update-resources":
        missing = []
        if not args.solver1_bin:
            missing.append("--solver1-bin")
        if not args.solver2_bin:
            missing.append("--solver2-bin")
        if missing:
            parser.error(f"--mode {args.mode} requires: {', '.join(missing)}")

    logger.info("Chimera starting — mode=%s", args.mode)

    # -- resource update mode (no solver / campaign needed) --------------------
    if args.mode == "update-resources":
        return _run_update_resources(args)

    logger.info(
        "Solver 1: %s (%s)  |  Solver 2: %s (%s)",
        args.solver1_name,
        args.solver1_bin,
        args.solver2_name,
        args.solver2_bin,
    )

    strategy = _build_strategy(args)
    # --iterations 0 or unspecified = unlimited campaign (run until interrupted)
    max_iters = args.iterations if args.iterations is not None and args.iterations > 0 else None

    try:
        stats = strategy.run_campaign(max_iterations=max_iters)
    except KeyboardInterrupt:
        logger.info("Campaign interrupted by user")
        stats = strategy.stats  # grab partial stats

    print("\n" + stats.summary())
    return 0


if __name__ == "__main__":
    sys.exit(main())
