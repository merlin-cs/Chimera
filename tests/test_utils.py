"""
Unit tests for utility modules.

Tests cover:
- File handling utilities
- SMT string formatting
- Timeout handling
"""

import os
import time
import pytest
from pathlib import Path

from chimera.utils import (
    get_all_smt_files_recursively,
    get_txt_files_list,
    format_smt_string,
)
from chimera.core.timeout import exit_after


class TestFileHandlers:
    """Tests for file handling utilities."""

    def test_get_smt_files_recursively(self, temp_dir):
        """Test recursive SMT file discovery."""
        # Create nested directory structure
        (temp_dir / "subdir").mkdir()
        (temp_dir / "subdir" / "nested").mkdir()

        # Create SMT files
        (temp_dir / "test1.smt2").write_text("(check-sat)")
        (temp_dir / "test2.smt2").write_text("(check-sat)")
        (temp_dir / "subdir" / "test3.smt2").write_text("(check-sat)")
        (temp_dir / "subdir" / "nested" / "test4.smt2").write_text("(check-sat)")
        (temp_dir / "not_smt.txt").write_text("hello")

        files = get_all_smt_files_recursively(str(temp_dir))

        # Should find all .smt2 files
        assert len(files) == 4
        assert any("test1.smt2" in f for f in files)
        assert any("test2.smt2" in f for f in files)
        assert any("test3.smt2" in f for f in files)
        assert any("test4.smt2" in f for f in files)

    def test_get_smt_files_empty_dir(self, temp_dir):
        """Test handling of empty directory."""
        files = get_all_smt_files_recursively(str(temp_dir))
        assert files == []

    def test_get_smt_files_nonexistent_dir(self, temp_dir):
        """Test handling of nonexistent directory."""
        nonexistent = temp_dir / "nonexistent"
        files = get_all_smt_files_recursively(str(nonexistent))
        # Should return empty list or raise, depending on implementation
        assert files == [] or files is None

    def test_get_txt_files_list(self, temp_dir):
        """Test TXT file discovery."""
        # Create TXT files
        (temp_dir / "file1.txt").write_text("content1")
        (temp_dir / "file2.txt").write_text("content2")
        (temp_dir / "not_txt.smt2").write_text("(check-sat)")

        files = get_txt_files_list(str(temp_dir))

        # Should find all .txt files
        assert len(files) == 2
        assert any("file1.txt" in f for f in files)
        assert any("file2.txt" in f for f in files)


class TestSMTHandlers:
    """Tests for SMT string formatting."""

    def test_format_basic_formula(self):
        """Test formatting basic SMT formula."""
        formula = "(set-logic QF_LIA)\n(assert (> x 0))\n(check-sat)"
        formatted = format_smt_string(formula)

        # Should preserve content
        assert "(set-logic QF_LIA)" in formatted
        assert "(assert (> x 0))" in formatted
        assert "(check-sat)" in formatted

    def test_format_preserves_structure(self):
        """Test that formatting preserves formula structure."""
        formula = """
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and (> x 0) (< y 10)))
(check-sat)
"""
        formatted = format_smt_string(formula)

        # Should have balanced parentheses
        open_count = formatted.count("(")
        close_count = formatted.count(")")
        assert open_count == close_count

    def test_format_multiline_assertion(self):
        """Test formatting assertion spanning multiple lines."""
        formula = "(assert (and\n  (> x 0)\n  (< y 10)\n))"
        formatted = format_smt_string(formula)

        assert "(assert" in formatted
        assert "(and" in formatted


class TestTimeout:
    """Tests for timeout handling."""

    def test_timeout_decorator_imports(self):
        """Test that timeout modules can be imported."""
        # exit_after should be callable
        assert callable(exit_after)

    def test_exit_after_timeout(self):
        """Test that exit_after properly limits execution time."""
        import signal

        @exit_after(1)
        def slow_function():
            time.sleep(5)
            return "completed"

        # Should raise KeyboardInterrupt when timeout expires
        with pytest.raises(KeyboardInterrupt):
            slow_function()

    def test_successful_execution_within_timeout(self):
        """Test that functions complete within timeout."""
        @exit_after(10)
        def fast_function():
            time.sleep(0.01)
            return "completed"

        result = fast_function()
        assert result == "completed"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
