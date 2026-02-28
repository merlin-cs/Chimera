"""
SMT-LIB parser facade — delegates to the existing ANTLR infrastructure.

This module provides a clean, typed interface around the ANTLR-generated
lexer/parser/visitor that already lives in ``src.parsing``.  **No parser
is re-written from scratch**: we wrap, sanitise, and re-export.

Public API
----------
* ``parse_file(path, *, timeout, silent, prepare) -> Optional[Tuple[Script, dict]]``
* ``parse_string(text, *, timeout, silent, prepare) -> Optional[Tuple[Script, dict]]``

Both functions return ``None`` on parse failure or timeout so that callers
never have to deal with exceptions for routine bad input.

Copyright (c) 2020-2021 The yinyang authors (ANTLR glue).
Copyright (c) 2024-2026 The Chimera authors (facade).
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import logging
import sys
import traceback
from pathlib import Path
from typing import Dict, FrozenSet, Optional, Tuple

from antlr4.CommonTokenStream import CommonTokenStream
from antlr4.error.ErrorListener import ErrorListener as _BaseErrorListener
from antlr4.FileStream import FileStream
from antlr4.InputStream import InputStream

# ANTLR artefacts (generated)
from chimera.parsing.SMTLIBv2Lexer import SMTLIBv2Lexer
from chimera.parsing.SMTLIBv2Parser import SMTLIBv2Parser

# Original visitor that builds the AST
from chimera.parsing.AstVisitor import AstVisitor as _AntlrAstVisitor

# Timeout decorator
from chimera.core.timeout import exit_after

# Our refactored AST (the new modules re-export the same classes the visitor
# constructs — they are source-compatible with the originals).
from chimera.core.smt_ast import Script, SmtSort

logger = logging.getLogger(__name__)

# The ANTLR visitor can recurse deeply on large formulas.
sys.setrecursionlimit(100_000)

# ---------------------------------------------------------------------------
# Commands stripped during seed preparation.
# ---------------------------------------------------------------------------
_STRIP_PREFIXES: FrozenSet[str] = frozenset({
    "set-info",
    "set-logic",
    "get-model",
    "get-assertions",
    "get-proof",
    "get-unsat-assumptions",
    "get-unsat-core",
    "get-value",
    "echo",
    "simplify",
})


# ---------------------------------------------------------------------------
# ANTLR error listener (suppresses noisy output by default)
# ---------------------------------------------------------------------------
class _SilentErrorListener(_BaseErrorListener):
    """ANTLR error listener that logs at DEBUG level."""

    def syntaxError(
        self,
        recognizer: object,
        offending_symbol: object,
        line: int,
        column: int,
        msg: str,
        e: object,
    ) -> None:
        logger.debug("ANTLR parse error at %d:%d – %s", line, column, msg)


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

def _prepare_seed(script: Script) -> Script:
    """Strip ``set-info``, ``set-logic`` and output-producing commands.

    This prevents false-positive bug reports caused by ``get-model``-style
    commands that produce output lines the oracle would misinterpret.
    """
    cleaned = []
    for cmd in script.commands:
        cmd_str = str(cmd)
        if any(prefix in cmd_str for prefix in _STRIP_PREFIXES):
            continue
        cleaned.append(cmd)
    script.commands = cleaned
    return script


def _generate_ast(
    stream: object,
    *,
    prepare: bool = True,
) -> Optional[Tuple[Script, Dict[str, SmtSort]]]:
    """Run the ANTLR pipeline on *stream* and return ``(script, globals)``."""
    listener = _SilentErrorListener()

    lexer = SMTLIBv2Lexer(stream)
    lexer.removeErrorListeners()
    lexer.addErrorListener(listener)

    token_stream = CommonTokenStream(lexer)

    parser = SMTLIBv2Parser(token_stream)
    parser.removeErrorListeners()

    tree = parser.start()
    visitor = _AntlrAstVisitor(strict=False)
    formula = visitor.visitStart(tree)

    if not formula or len(formula.commands) == 0:
        return None

    if prepare:
        formula = _prepare_seed(formula)

    return formula, visitor.global_vars


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def parse_file(
    path: str | Path,
    *,
    timeout: int = 30,
    silent: bool = True,
    prepare: bool = True,
) -> Optional[Tuple[Script, Dict[str, SmtSort]]]:
    """Parse an SMT-LIB file and return ``(Script, global_vars)``.

    Parameters
    ----------
    path : str | Path
        Filesystem path to the ``.smt2`` file.
    timeout : int
        Maximum wall-clock seconds before the parser is killed.
    silent : bool
        If ``True``, swallow exceptions and return ``None``.
    prepare : bool
        If ``True``, strip ``set-info`` / ``set-logic`` and output-
        producing commands from the resulting script.

    Returns
    -------
    (Script, dict) or None
        ``None`` when parsing fails, times out, or the file is empty.
    """

    @exit_after(timeout)
    def _inner(p: str) -> Optional[Tuple[Script, Dict[str, SmtSort]]]:
        stream = FileStream(str(p), encoding="utf-8")
        return _generate_ast(stream, prepare=prepare)

    try:
        result = _inner(str(path))
        return result
    except KeyboardInterrupt:
        logger.debug("Parser timed out for %s", path)
    except Exception:
        if not silent:
            traceback.print_exc()
        else:
            logger.debug("Parse error for %s", path, exc_info=True)
    return None


def parse_string(
    text: str,
    *,
    timeout: int = 30,
    silent: bool = True,
    prepare: bool = True,
) -> Optional[Tuple[Script, Dict[str, SmtSort]]]:
    """Parse an SMT-LIB string and return ``(Script, global_vars)``.

    Parameters
    ----------
    text : str
        The SMT-LIB source text.
    timeout, silent, prepare
        Same semantics as :func:`parse_file`.

    Returns
    -------
    (Script, dict) or None
    """

    @exit_after(timeout)
    def _inner(s: str) -> Optional[Tuple[Script, Dict[str, SmtSort]]]:
        stream = InputStream(s)
        return _generate_ast(stream, prepare=prepare)

    try:
        result = _inner(text)
        return result
    except KeyboardInterrupt:
        logger.debug("Parser timed out on string input")
    except Exception:
        if not silent:
            traceback.print_exc()
        else:
            logger.debug("Parse error on string input", exc_info=True)
    return None
