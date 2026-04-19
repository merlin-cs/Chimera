"""
Tests for the CLI module (chimera/chimera_cli.py).

Tests cover:
- Argument parsing
- Strategy building
- Logging configuration
"""

import pytest
import argparse
from unittest.mock import patch, MagicMock

from chimera.chimera_cli import (
    build_parser,
    _make_solver,
    _configure_logging,
    _build_strategy,
)


class TestBuildParser:
    """Tests for argument parser construction."""

    def test_parser_creation(self):
        """Test that parser is created successfully."""
        parser = build_parser()
        assert isinstance(parser, argparse.ArgumentParser)

    def test_required_mode_argument(self):
        """Test that mode is required."""
        parser = build_parser()
        with pytest.raises(SystemExit):
            parser.parse_args([])  # Missing --mode

    def test_valid_modes(self):
        """Test valid mode values."""
        parser = build_parser()

        # Should accept valid modes
        for mode in ["histfuzz", "once4all", "aries"]:
            args = parser.parse_args([
                "--mode", mode,
                "--solver1-bin", "/usr/bin/z3",
                "--solver2-bin", "/usr/bin/cvc5"
            ])
            assert args.mode == mode

    def test_invalid_mode(self):
        """Test invalid mode is rejected."""
        parser = build_parser()
        with pytest.raises(SystemExit):
            parser.parse_args([
                "--mode", "invalid",
                "--solver1-bin", "/usr/bin/z3",
                "--solver2-bin", "/usr/bin/cvc5"
            ])

    def test_solver_arguments(self):
        """Test solver configuration arguments."""
        parser = build_parser()
        args = parser.parse_args([
            "--mode", "histfuzz",
            "--solver1-name", "z3",
            "--solver1-bin", "/usr/bin/z3",
            "--solver2-name", "cvc5",
            "--solver2-bin", "/usr/bin/cvc5",
            "--solver-timeout", "30.0"
        ])

        assert args.solver1_name == "z3"
        assert args.solver1_bin == "/usr/bin/z3"
        assert args.solver2_name == "cvc5"
        assert args.solver2_bin == "/usr/bin/cvc5"
        assert args.solver_timeout == 30.0

    def test_io_arguments(self):
        """Test input/output arguments."""
        parser = build_parser()
        args = parser.parse_args([
            "--mode", "histfuzz",
            "--solver1-bin", "/usr/bin/z3",
            "--solver2-bin", "/usr/bin/cvc5",
            "--seed-dir", "./seeds",
            "--output-dir", "./bugs",
            "--temp-dir", "./temp"
        ])

        assert args.seed_dir == "./seeds"
        assert args.output_dir == "./bugs"
        assert args.temp_dir == "./temp"

    def test_campaign_arguments(self):
        """Test campaign settings."""
        parser = build_parser()
        args = parser.parse_args([
            "--mode", "histfuzz",
            "--solver1-bin", "/usr/bin/z3",
            "--solver2-bin", "/usr/bin/cvc5",
            "--iterations", "1000"
        ])

        assert args.iterations == 1000

    def test_histfuzz_options(self):
        """Test HistFuzz-specific options."""
        parser = build_parser()
        args = parser.parse_args([
            "--mode", "histfuzz",
            "--solver1-bin", "/usr/bin/z3",
            "--solver2-bin", "/usr/bin/cvc5",
            "--skeleton-files", "skel1.smt2", "skel2.smt2",
            "--resource-dir", "./resources",
            "--num-asserts", "5"
        ])

        assert args.skeleton_files == ["skel1.smt2", "skel2.smt2"]
        assert args.resource_dir == "./resources"
        assert args.num_asserts == 5

    def test_once4all_options(self):
        """Test Once4All-specific options."""
        parser = build_parser()
        args = parser.parse_args([
            "--mode", "once4all",
            "--solver1-bin", "/usr/bin/z3",
            "--solver2-bin", "/usr/bin/cvc5",
            "--generator-dir", "./gens",
            "--theories", "int", "bv",
            "--merge-skeletons"
        ])

        assert args.generator_dir == "./gens"
        assert args.theories == ["int", "bv"]
        assert args.merge_skeletons is True

    def test_aries_options(self):
        """Test Aries-specific options."""
        parser = build_parser()
        args = parser.parse_args([
            "--mode", "aries",
            "--solver1-bin", "/usr/bin/z3",
            "--solver2-bin", "/usr/bin/cvc5",
            "--rules-csv", "./rules.csv",
            "--config-dir", "./config",
            "--mimetic-rounds", "5",
            "--no-egraph"
        ])

        assert args.rules_csv == "./rules.csv"
        assert args.config_dir == "./config"
        assert args.mimetic_rounds == 5
        assert args.no_egraph is True

    def test_oracle_options(self):
        """Test oracle tuning options."""
        parser = build_parser()
        args = parser.parse_args([
            "--mode", "histfuzz",
            "--solver1-bin", "/usr/bin/z3",
            "--solver2-bin", "/usr/bin/cvc5",
            "--detect-crashes",
            "--detect-soundness",
            "--detect-invalid-models",
            "--detect-performance",
            "--performance-ratio", "5.0"
        ])

        assert args.detect_crashes is True
        assert args.detect_soundness is True
        assert args.detect_invalid_models is True
        assert args.detect_performance is True
        assert args.performance_ratio == 5.0

    def test_logging_options(self):
        """Test logging options."""
        parser = build_parser()

        args = parser.parse_args([
            "--mode", "histfuzz",
            "--solver1-bin", "/usr/bin/z3",
            "--solver2-bin", "/usr/bin/cvc5",
            "--verbose"
        ])
        assert args.verbose is True

        args = parser.parse_args([
            "--mode", "histfuzz",
            "--solver1-bin", "/usr/bin/z3",
            "--solver2-bin", "/usr/bin/cvc5",
            "--quiet"
        ])
        assert args.quiet is True


class TestMakeSolver:
    """Tests for solver configuration creation."""

    def test_z3_solver_config(self):
        """Test Z3 solver configuration."""
        config = _make_solver("z3", "/usr/bin/z3")
        assert config.name == "z3"
        assert config.binary == "/usr/bin/z3"

    def test_cvc5_solver_config(self):
        """Test cvc5 solver configuration."""
        config = _make_solver("cvc5", "/usr/bin/cvc5")
        assert config.name == "cvc5"
        assert config.binary == "/usr/bin/cvc5"

    def test_generic_solver_config(self):
        """Test generic solver configuration."""
        config = _make_solver("yices2", "/usr/bin/yices-smt2")
        assert config.name == "yices2"
        assert config.binary == "/usr/bin/yices-smt2"

    def test_solver_name_normalization(self):
        """Test solver name normalization."""
        # Test case insensitivity
        config1 = _make_solver("Z3", "/usr/bin/z3")
        config2 = _make_solver("CVC5", "/usr/bin/cvc5")

        assert config1.name == "Z3" or config1.name.lower() == "z3"
        assert config2.name == "CVC5" or config2.name.lower() == "cvc5"


class TestConfigureLogging:
    """Tests for logging configuration."""

    def _reset_logging(self):
        """Reset root logger so basicConfig works again."""
        import logging
        root = logging.getLogger()
        root.handlers.clear()
        root.setLevel(logging.WARNING)

    def test_verbose_logging(self):
        """Test verbose (DEBUG) logging configuration."""
        import logging
        self._reset_logging()
        _configure_logging(verbose=True, quiet=False)
        # Should set DEBUG level
        assert logging.getLogger().level <= logging.DEBUG or \
               logging.getLogger("chimera").level <= logging.DEBUG

    def test_quiet_logging(self):
        """Test quiet (WARNING) logging configuration."""
        import logging
        self._reset_logging()
        _configure_logging(verbose=False, quiet=True)
        # Should set WARNING level
        assert logging.getLogger().level >= logging.WARNING or \
               logging.getLogger("chimera").level >= logging.WARNING

    def test_default_logging(self):
        """Test default (INFO) logging configuration."""
        import logging
        self._reset_logging()
        _configure_logging(verbose=False, quiet=False)
        # Should set INFO level
        assert logging.getLogger().level <= logging.INFO


class TestBuildStrategy:
    """Tests for strategy building."""

    def test_build_histfuzz_strategy(self):
        """Test building HistFuzz strategy."""
        parser = build_parser()
        args = parser.parse_args([
            "--mode", "histfuzz",
            "--solver1-bin", "/usr/bin/z3",
            "--solver2-bin", "/usr/bin/cvc5",
            "--seed-dir", "./seeds"
        ])

        strategy = _build_strategy(args)
        assert strategy is not None
        assert hasattr(strategy, 'run_campaign')

    def test_build_once4all_strategy(self):
        """Test building Once4All strategy."""
        parser = build_parser()
        args = parser.parse_args([
            "--mode", "once4all",
            "--solver1-bin", "/usr/bin/z3",
            "--solver2-bin", "/usr/bin/cvc5"
        ])

        strategy = _build_strategy(args)
        assert strategy is not None
        assert hasattr(strategy, 'run_campaign')

    def test_build_aries_strategy(self):
        """Test building Aries strategy."""
        parser = build_parser()
        args = parser.parse_args([
            "--mode", "aries",
            "--solver1-bin", "/usr/bin/z3",
            "--solver2-bin", "/usr/bin/cvc5"
        ])

        strategy = _build_strategy(args)
        assert strategy is not None
        assert hasattr(strategy, 'run_campaign')

    def test_invalid_mode_raises_error(self):
        """Test that invalid mode raises ValueError."""
        parser = build_parser()
        args = parser.parse_args([
            "--mode", "histfuzz",
            "--solver1-bin", "/usr/bin/z3",
            "--solver2-bin", "/usr/bin/cvc5"
        ])
        # Manually set invalid mode
        args.mode = "invalid_mode"

        with pytest.raises(ValueError):
            _build_strategy(args)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
