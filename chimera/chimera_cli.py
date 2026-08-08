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
import json
import logging
import sys
from dataclasses import asdict, replace
from typing import Any

from chimera import __version__
from chimera.core.campaign import (
    CampaignConfig,
    CampaignRunner,
    StrategyCaseProducer,
    replay_artifact,
)
from chimera.core.solver_manager import SolverConfig, default_cvc5_args, default_z3_args
from chimera.core.differential_oracle import OracleConfig
from chimera.engines.base import FuzzingStrategy, FuzzStats
from chimera.engines.histfuzz_engine import HistFuzzStrategy
from chimera.engines.once4all_engine import Once4AllStrategy
from chimera.engines.aries_engine import AriesStrategy
from chimera.resources import REWRITE_RULES_CSV, REWRITE_CONFIG_DIR
from chimera.history.collector import update_resources as _update_resources
from chimera.history.streaming import export_corpus, validate_corpus
from chimera.doctor import collect_capabilities

logger = logging.getLogger("chimera")


# ---------------------------------------------------------------------------
# CLI argument parser
# ---------------------------------------------------------------------------


class _ChimeraArgumentParser(argparse.ArgumentParser):
    """Accept both modern commands and the pre-P3 ``--mode`` spelling."""

    def parse_args(self, args=None, namespace=None):  # type: ignore[no-untyped-def]
        parsed = super().parse_args(args=args, namespace=namespace)
        if parsed.mode is None and parsed.command is None:
            self.error("provide a command (run/corpus/doctor/replay) or --mode")
        return parsed


def build_parser() -> argparse.ArgumentParser:
    p = _ChimeraArgumentParser(
        prog="chimera",
        description="Chimera — differential SMT solver fuzzer.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )

    # Modern command spelling: ``chimera run histfuzz``.  Options remain
    # shared so old integrations can be migrated without two factories.
    p.add_argument("command", nargs="?", choices=["run", "corpus", "doctor", "replay"])
    p.add_argument("target", nargs="?")
    p.add_argument("--version", action="version", version=f"chimera {__version__}")
    p.add_argument(
        "--dry-run", action="store_true", help="Validate configuration without invoking solvers."
    )
    p.add_argument(
        "--resume", action="store_true", help="Resume a campaign from campaign-summary.json."
    )

    # -- mode ----------------------------------------------------------------
    p.add_argument(
        "--mode",
        choices=["histfuzz", "once4all", "aries", "update-resources"],
        required=False,
        help="Fuzzing strategy to use, or 'update-resources' to refresh HistFuzz corpus.",
    )

    # -- solvers -------------------------------------------------------------
    # Solver args required for fuzzing modes; validated in _validate_args().
    sol = p.add_argument_group("Solver configuration")
    sol.add_argument("--solver1-name", default="z3", help="Name of solver 1 (default: z3).")
    sol.add_argument("--solver1-bin", default=None, help="Path to solver 1 binary.")
    sol.add_argument("--solver2-name", default="cvc5", help="Name of solver 2 (default: cvc5).")
    sol.add_argument("--solver2-bin", default=None, help="Path to solver 2 binary.")
    sol.add_argument(
        "--solver-timeout", type=float, default=10.0, help="Per-query timeout (seconds)."
    )

    # -- I/O -----------------------------------------------------------------
    io = p.add_argument_group("Input / output")
    io.add_argument("--seed-dir", default="", help="Directory with seed .smt2 files.")
    io.add_argument("--output-dir", default="./chimera_bugs", help="Directory for bug artifacts.")
    io.add_argument("--temp-dir", default="./chimera_temp", help="Scratch directory.")

    # -- campaign ------------------------------------------------------------
    camp = p.add_argument_group("Campaign settings")
    camp.add_argument("--iterations", type=int, default=0, help="Max iterations (0 = unlimited).")
    camp.add_argument(
        "--seed",
        type=int,
        default=None,
        help="Campaign RNG seed (config files remain authoritative).",
    )
    camp.add_argument("--config", default=None, help="Versioned JSON campaign configuration.")
    camp.add_argument("--manifest", default=None, help="Artifact manifest to replay.")
    camp.add_argument(
        "--json-summary", action="store_true", help="Print the campaign summary as JSON."
    )

    # -- HistFuzz options ----------------------------------------------------
    hf = p.add_argument_group("HistFuzz options")
    hf.add_argument(
        "--corpus-dir",
        default=None,
        help="Versioned JSONL HistFuzz corpus (defaults to the packaged corpus).",
    )
    hf.add_argument(
        "--skeleton-files", nargs="*", default=None, help="Deprecated; use --corpus-dir."
    )
    hf.add_argument("--resource-dir", default=None, help="Deprecated; use --corpus-dir.")
    hf.add_argument(
        "--num-asserts", type=int, default=3, help="Max assertions per generated formula."
    )
    hf.add_argument(
        "--logic",
        type=str,
        default=None,
        help="Target SMT-LIB logic (e.g., QF_LIA, AUFLIA). Only use compatible skeletons/blocks.",
    )
    hf.add_argument(
        "--use-new-corpus",
        action="store_true",
        help="Deprecated compatibility flag; use --corpus-dir.",
    )

    # -- Once4All options ----------------------------------------------------
    o4a = p.add_argument_group("Once4All options")
    o4a.add_argument(
        "--generator-dir",
        default=None,
        help="Directory with *_generator.py modules (defaults to packaged generators).",
    )
    o4a.add_argument("--theories", nargs="*", default=None, help="Restrict to these theory keys.")
    o4a.add_argument(
        "--generator-timeout",
        type=float,
        default=10.0,
        help="External generator worker timeout (seconds).",
    )
    o4a.add_argument(
        "--merge-skeletons",
        action="store_true",
        help="Reserved; disabled until skeleton hole filling is complete.",
    )

    # -- Aries options -------------------------------------------------------
    ar = p.add_argument_group("Aries options")
    ar.add_argument("--rules-csv", default=str(REWRITE_RULES_CSV), help="Path to RewriteRule.csv.")
    ar.add_argument(
        "--config-dir",
        default=str(REWRITE_CONFIG_DIR),
        help="Operator config directory for mimetic mutation.",
    )
    ar.add_argument(
        "--mimetic-rounds", type=int, default=3, help="Mimetic mutation rounds per seed."
    )
    ar.add_argument("--no-egraph", action="store_true", help="Disable equality saturation.")

    # -- update-resources options ---------------------------------------------
    ur = p.add_argument_group("Resource update options (mode=update-resources)")
    ur.add_argument(
        "--formula-store",
        default="./bug_triggering_formulas",
        help="Directory for collected bug formulas (default: ./bug_triggering_formulas).",
    )
    ur.add_argument(
        "--resource-output",
        default="./chimera/resources/histfuzz",
        help="Output directory for HistFuzz corpus (default: ./chimera/resources/histfuzz).",
    )
    ur.add_argument(
        "--collect-solvers",
        nargs="*",
        default=None,
        help="Collect from specific solvers only (default: all known solvers).",
    )
    ur.add_argument(
        "--skip-collection",
        action="store_true",
        help="Skip GitHub collection; only extract corpus from existing formula files.",
    )

    # -- oracle --------------------------------------------------------------
    orc = p.add_argument_group("Oracle tuning")
    # New negation flags (preferred)
    orc.add_argument(
        "--no-crash-detection",
        action="store_true",
        help="Disable crash detection (enabled by default).",
    )
    orc.add_argument(
        "--no-soundness-detection",
        action="store_true",
        help="Disable soundness bug detection (enabled by default).",
    )
    # Deprecated: kept for backward compatibility (no-op, enabled by default)
    orc.add_argument(
        "--detect-crashes", action="store_true", default=True, help=argparse.SUPPRESS
    )  # Deprecated: crashes detected by default
    orc.add_argument(
        "--detect-soundness", action="store_true", default=True, help=argparse.SUPPRESS
    )  # Deprecated: soundness checked by default
    orc.add_argument(
        "--detect-invalid-models", action="store_true", default=False, help="Report invalid models."
    )
    orc.add_argument(
        "--detect-performance", action="store_true", default=False, help="Report perf regressions."
    )
    orc.add_argument(
        "--performance-ratio", type=float, default=10.0, help="Threshold for perf bugs."
    )

    # -- logging -------------------------------------------------------------
    p.add_argument("-v", "--verbose", action="store_true", help="DEBUG-level logging.")
    p.add_argument("-q", "--quiet", action="store_true", help="WARNING-level logging only.")

    return p


# ---------------------------------------------------------------------------
# Solver construction helpers
# ---------------------------------------------------------------------------


def _make_solver(name: str, binary: str, timeout: float = 10.0) -> SolverConfig:
    """Build a solver configuration whose internal timeout matches the CLI."""
    timeout_ms = max(1, int(timeout * 1000))
    n = name.strip().lower()
    if n in ("z3",):
        return SolverConfig(
            name=name,
            binary=binary,
            base_args=default_z3_args(timeout_ms=timeout_ms),
        )
    if n in ("cvc5",):
        return SolverConfig(
            name=name,
            binary=binary,
            base_args=default_cvc5_args(timeout_ms=timeout_ms),
        )
    # Generic — no special args
    return SolverConfig(name=name, binary=binary)


# ---------------------------------------------------------------------------
# Engine factory
# ---------------------------------------------------------------------------


def _build_strategy(args: argparse.Namespace) -> FuzzingStrategy:
    solver1 = _make_solver(args.solver1_name, args.solver1_bin, args.solver_timeout)
    solver2 = _make_solver(args.solver2_name, args.solver2_bin, args.solver_timeout)

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
            corpus_dir=args.corpus_dir,
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
            generator_timeout=args.generator_timeout,
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
            github_token=None,
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
    print(
        f"  Logics covered:                 {', '.join(sorted(result.logics_found)) if result.logics_found else 'none'}"
    )
    return 0


def _build_strategy_from_config(config: CampaignConfig) -> FuzzingStrategy:
    """Build an engine from a self-contained campaign configuration."""
    if len(config.solvers) < 2:
        raise ValueError("campaign config requires at least two solvers")
    settings: dict[str, Any] = dict(config.engine_settings)
    common: dict[str, Any] = {
        "output_dir": config.output_dir,
        "temp_dir": config.temp_dir,
        "timeout": config.timeout,
        "oracle_config": config.oracle,
    }
    if config.engine == "histfuzz":
        return HistFuzzStrategy(config.solvers[0], config.solvers[1], **settings, **common)
    if config.engine == "once4all":
        if settings.get("merge_skeletons"):
            raise ValueError("merge_skeletons is currently disabled; use a plain generator output")
        return Once4AllStrategy(
            config.solvers[0],
            config.solvers[1],
            solver_configs=config.solvers,
            **settings,
            **common,
        )
    if config.engine == "aries":
        return AriesStrategy(config.solvers[0], config.solvers[1], **settings, **common)
    raise ValueError(f"unknown campaign engine: {config.engine}")


_CONFIG_ALLOWED_OVERRIDES = {
    "--config",
    "--output-dir",
    "--temp-dir",
    "--iterations",
    "--verbose",
    "--quiet",
    "--dry-run",
    "--resume",
    "--json-summary",
}


def _explicit_options(argv: list[str] | None) -> set[str]:
    values = list(sys.argv[1:] if argv is None else argv)
    return {token.split("=", 1)[0] for token in values if token.startswith("--")}


def _reject_config_engine_overrides(
    parser: argparse.ArgumentParser,
    args: argparse.Namespace,
    argv: list[str] | None,
) -> None:
    if not args.config:
        return
    rejected = sorted(
        option
        for option in _explicit_options(argv)
        if option.startswith("--") and option not in _CONFIG_ALLOWED_OVERRIDES
    )
    if rejected:
        parser.error(
            "--config is self-contained; these options cannot override it: " + ", ".join(rejected)
        )


def _campaign_config_from_strategy(
    args: argparse.Namespace, strategy: FuzzingStrategy
) -> CampaignConfig:
    """Build a self-contained config for modern command-line campaigns."""
    settings = {}
    if args.mode == "histfuzz":
        settings = {
            "corpus_dir": args.corpus_dir,
            "logic": args.logic,
            "num_asserts": args.num_asserts,
        }
    elif args.mode == "once4all":
        settings = {
            "generator_dir": args.generator_dir,
            "compatible_theories": args.theories,
            "merge_skeletons": args.merge_skeletons,
            "generator_timeout": args.generator_timeout,
        }
    elif args.mode == "aries":
        settings = {
            "seed_dir": args.seed_dir,
            "rules_csv": args.rules_csv,
            "config_dir": args.config_dir,
            "mimetic_rounds": args.mimetic_rounds,
            "use_egraph": not args.no_egraph,
        }
    settings = {key: value for key, value in settings.items() if value is not None}
    return CampaignConfig(
        engine=args.mode,
        solvers=(strategy.solver1, strategy.solver2),
        engine_settings=settings,
        oracle=strategy.oracle_config,
        output_dir=args.output_dir,
        temp_dir=args.temp_dir,
        timeout=args.solver_timeout,
        iterations=None if args.iterations == 0 else args.iterations,
        seed=0 if args.seed is None else args.seed,
    )


def _print_campaign_result(
    stats: FuzzStats,
    *,
    config: CampaignConfig | None = None,
    json_summary: bool = False,
) -> None:
    if json_summary:
        payload = {"stats": asdict(stats)}
        if config is not None:
            payload["config"] = config.to_dict()
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print("\n" + stats.summary())


def _run_corpus_command(args: argparse.Namespace) -> int:
    if args.target == "extract":
        try:
            manifest = export_corpus(
                args.formula_store,
                args.resource_output,
                source_revision="working-tree",
                replace=True,
            )
        except (FileNotFoundError, ValueError) as exc:
            logger.error("corpus extraction aborted: %s", exc)
            return 1
        print(json.dumps(manifest, indent=2, sort_keys=True))
        return 0
    if args.target == "refresh":
        result = _run_update_resources(args)
        if result:
            return result
        try:
            manifest = validate_corpus(args.resource_output)
        except (OSError, ValueError) as exc:
            logger.error("refreshed corpus is unavailable: %s", exc)
            return 1
        print(json.dumps(manifest, indent=2, sort_keys=True))
        return 0
    raise ValueError("corpus command requires extract or refresh")


def _run_doctor(args: argparse.Namespace) -> int:
    requested_solver_paths = {
        name: path
        for name, path in {
            args.solver1_name: args.solver1_bin,
            args.solver2_name: args.solver2_bin,
        }.items()
        if path
    }
    capabilities = collect_capabilities(
        solver_paths=requested_solver_paths,
        generator_dir=args.generator_dir,
        artifact_dir=args.output_dir,
    )
    print(json.dumps(capabilities, indent=2, sort_keys=True))
    solvers_ok = all(item["ok"] for item in capabilities["solvers"].values())
    return 0 if capabilities["corpus"]["ok"] and solvers_ok else 1


def _run_replay(args: argparse.Namespace) -> int:
    manifest = args.manifest or args.target
    if not manifest:
        raise ValueError("replay requires an artifact manifest path")
    result = replay_artifact(manifest)
    serializable = dict(result)
    serializable["results"] = {
        name: {
            "outcome": value.outcome.name,
            "stdout": value.stdout,
            "stderr": value.stderr,
            "exit_code": value.exit_code,
        }
        for name, value in result["results"].items()
    }
    print(json.dumps(serializable, indent=2, sort_keys=True))
    return 0


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    explicit = _explicit_options(argv)

    _configure_logging(args.verbose, args.quiet)

    # Resolve modern commands to the shared engine factory.
    if args.command == "run":
        if args.target not in ("histfuzz", "once4all", "aries"):
            parser.error("run requires histfuzz, once4all, or aries")
        args.mode = args.target
    elif args.command == "corpus":
        return _run_corpus_command(args)
    elif args.command == "doctor":
        return _run_doctor(args)
    elif args.command == "replay":
        return _run_replay(args)

    _reject_config_engine_overrides(parser, args, argv)

    if args.mode is None:
        parser.error("--mode is required for the legacy command form")

    # -- Validate solver args for fuzzing modes -------------------------------
    if args.mode != "update-resources" and not args.config:
        missing = []
        if not args.solver1_bin:
            missing.append("--solver1-bin")
        if not args.solver2_bin:
            missing.append("--solver2-bin")
        if missing:
            parser.error(f"--mode {args.mode} requires: {', '.join(missing)}")
        if args.merge_skeletons:
            parser.error("--merge-skeletons is currently disabled: hole filling is incomplete")

    logger.info("Chimera starting — mode=%s", args.mode)

    # -- resource update mode (no solver / campaign needed) --------------------
    if args.mode == "update-resources":
        if args.dry_run or args.resume:
            parser.error("--dry-run/--resume are only valid for solver campaigns")
        return _run_update_resources(args)

    logger.info(
        "Solver 1: %s (%s)  |  Solver 2: %s (%s)",
        args.solver1_name,
        args.solver1_bin,
        args.solver2_name,
        args.solver2_bin,
    )

    if args.config:
        config = CampaignConfig.read(args.config)
        # Only operational controls are allowed to override a config file.
        if "--output-dir" in explicit:
            config = CampaignConfig.from_dict({**config.to_dict(), "output_dir": args.output_dir})
        if "--temp-dir" in explicit:
            config = CampaignConfig.from_dict({**config.to_dict(), "temp_dir": args.temp_dir})
        if "--iterations" in explicit:
            config = CampaignConfig.from_dict(
                {
                    **config.to_dict(),
                    "iterations": None if args.iterations == 0 else args.iterations,
                }
            )
        # CampaignRunner executes config.solvers, not the strategy's private
        # copies.  Normalize the stored configuration before building Aries so
        # every cvc5 invocation receives incremental mode.
        if config.engine == "aries":
            config = replace(
                config,
                solvers=AriesStrategy.ensure_incremental_solvers(config.solvers),
            )
        strategy = _build_strategy_from_config(config)
        runner = CampaignRunner(StrategyCaseProducer(strategy), config)
        issues = runner.preflight()
        if issues:
            parser.error(
                "campaign preflight failed:\n  - " + "\n  - ".join(issue.reason for issue in issues)
            )
        if args.dry_run:
            print(
                json.dumps({"config": config.to_dict(), "preflight": []}, indent=2, sort_keys=True)
            )
            return 0
        stats = runner.run(resume=args.resume)
        _print_campaign_result(stats, config=config, json_summary=args.json_summary)
        return 0

    strategy = _build_strategy(args)
    issues = strategy.preflight()
    if issues:
        parser.error(
            "campaign preflight failed:\n  - " + "\n  - ".join(issue.reason for issue in issues)
        )

    # Modern commands always use the structured campaign runner, including
    # injected RNG, N-solver comparison, artifacts, and resume support.
    if args.command == "run":
        config = _campaign_config_from_strategy(args, strategy)
        runner = CampaignRunner(StrategyCaseProducer(strategy), config)
        runner_issues = runner.preflight()
        if runner_issues:
            parser.error(
                "campaign preflight failed:\n  - "
                + "\n  - ".join(issue.reason for issue in runner_issues)
            )
        if args.dry_run:
            print(
                json.dumps({"config": config.to_dict(), "preflight": []}, indent=2, sort_keys=True)
            )
            return 0
        stats = runner.run(resume=args.resume)
        _print_campaign_result(stats, config=config, json_summary=args.json_summary)
        return 0

    if args.dry_run:
        print(json.dumps({"mode": args.mode, "preflight": []}, indent=2, sort_keys=True))
        return 0
    if args.resume:
        parser.error("--resume requires --config or a modern `chimera run ...` command")
    # --iterations 0 or unspecified = unlimited campaign (run until interrupted)
    max_iters = args.iterations if args.iterations is not None and args.iterations > 0 else None

    try:
        stats = strategy.run_campaign(max_iterations=max_iters)
    except KeyboardInterrupt:
        logger.info("Campaign interrupted by user")
        stats = strategy.stats  # grab partial stats

    _print_campaign_result(stats, json_summary=args.json_summary)
    return 0


if __name__ == "__main__":
    sys.exit(main())
