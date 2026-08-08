"""
SMT-LIB parser facade — delegates to the existing ANTLR infrastructure.

This module provides a clean, typed interface around the ANTLR-generated
lexer/parser/visitor that already lives in ``chimera.parsing``.  **No parser
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
from dataclasses import dataclass
from pathlib import Path

# Handle deeply nested ASTs (some formulas have depth > 2000)
sys.setrecursionlimit(100000)
from typing import Callable, Dict, FrozenSet, List, Optional, Tuple, TypeVar, cast

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
from chimera.core.smt_ast import GetValue, Script, Simplify, SmtSort, SMTLIBCommand

logger = logging.getLogger(__name__)

_T = TypeVar("_T")


@dataclass(frozen=True)
class ParserDiagnostic:
    """A syntax or AST-construction issue retained from one parse attempt."""

    line: int
    column: int
    message: str


@dataclass(frozen=True)
class ParseResult:
    """Detailed parse result for callers that need diagnostics."""

    script: Optional[Script]
    global_vars: Dict[str, SmtSort]
    diagnostics: Tuple[ParserDiagnostic, ...]

# ---------------------------------------------------------------------------
# Commands stripped during seed preparation.
# ---------------------------------------------------------------------------

# Typed AST node classes that are always stripped.
_STRIP_TYPES: Tuple[type, ...] = (GetValue, Simplify)

# SMTLIBCommand names (without the leading '(') that should be stripped.
# These are matched against the *start* of the command string so that only
# the command itself is matched, not identifiers that happen to contain one
# of these strings (e.g. ``(declare-const get-model Bool)``).
_STRIP_CMD_NAMES: FrozenSet[str] = frozenset({
    "set-info",
    "set-logic",
    "get-model",
    "get-assertions",
    "get-proof",
    "get-unsat-assumptions",
    "get-unsat-core",
    "echo",
})


# ---------------------------------------------------------------------------
# ANTLR error listener (suppresses noisy output by default)
# ---------------------------------------------------------------------------
class _SilentErrorListener(_BaseErrorListener):
    """ANTLR error listener that records diagnostics and logs at DEBUG."""

    def __init__(self) -> None:
        self.diagnostics: List[ParserDiagnostic] = []

    def syntaxError(
        self,
        recognizer: object,
        offending_symbol: object,
        line: int,
        column: int,
        msg: str,
        e: object,
    ) -> None:
        self.diagnostics.append(ParserDiagnostic(line, column, msg))
        logger.debug("ANTLR parse error at %d:%d – %s", line, column, msg)


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

def _prepare_seed(script: Script) -> Script:
    """Strip ``set-info``, ``set-logic`` and output-producing commands.

    This prevents false-positive bug reports caused by ``get-model``-style
    commands that produce output lines the oracle would misinterpret.

    Typed command nodes (e.g. ``GetValue``, ``Simplify``) are matched by
    type so that unrelated identifiers are never accidentally stripped.
    For ``SMTLIBCommand`` catch-all nodes the match is anchored to the
    *start* of the command string (``(cmd-name``), avoiding false positives
    such as ``(declare-const get-model Bool)``.
    """
    cleaned = []
    for cmd in script.commands:
        if isinstance(cmd, _STRIP_TYPES):
            continue
        if isinstance(cmd, SMTLIBCommand):
            trimmed = cmd.cmd_str.lstrip()
            if any(
                trimmed.startswith(f"({name}") for name in _STRIP_CMD_NAMES
            ):
                continue
        cleaned.append(cmd)
    script.commands = cleaned
    return script


def _generate_ast(
    stream: object,
    *,
    prepare: bool = True,
) -> ParseResult:
    """Run the ANTLR pipeline and retain diagnostics from every stage."""
    listener = _SilentErrorListener()

    lexer = SMTLIBv2Lexer(stream)
    lexer.removeErrorListeners()
    lexer.addErrorListener(listener)

    token_stream = CommonTokenStream(lexer)

    parser = SMTLIBv2Parser(token_stream)
    parser.removeErrorListeners()
    parser.addErrorListener(listener)

    tree = parser.start()
    if listener.diagnostics:
        return ParseResult(None, {}, tuple(listener.diagnostics))

    try:
        visitor = _AntlrAstVisitor(strict=True)
        formula = visitor.visitStart(tree)
    except Exception as exc:
        diagnostic = ParserDiagnostic(0, 0, f"AST construction failed: {exc}")
        logger.debug("AST construction failed", exc_info=True)
        return ParseResult(None, {}, tuple(listener.diagnostics) + (diagnostic,))

    if not formula or len(formula.commands) == 0:
        return ParseResult(None, visitor.global_vars, tuple(listener.diagnostics))

    if prepare:
        formula = _prepare_seed(formula)

    return ParseResult(formula, visitor.global_vars, tuple(listener.diagnostics))


def _parse_detailed(
    loader: Callable[[], object],
    *,
    timeout: int,
    prepare: bool,
) -> ParseResult:
    """Execute a stream loader under the legacy timeout mechanism."""

    @exit_after(timeout)
    def _inner() -> ParseResult:
        return _generate_ast(loader(), prepare=prepare)

    return cast(ParseResult, _inner())


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

    try:
        result = parse_file_detailed(path, timeout=timeout, prepare=prepare)
        if result.script is not None:
            return result.script, result.global_vars
        return None
    except KeyboardInterrupt:
        logger.debug("Parser timed out for %s", path)
    except Exception:
        if not silent:
            traceback.print_exc()
        else:
            logger.debug("Parse error for %s", path, exc_info=True)
    return None


def parse_file_detailed(
    path: str | Path,
    *,
    timeout: int = 30,
    prepare: bool = True,
) -> ParseResult:
    """Parse a file and return diagnostics instead of silently discarding them."""
    try:
        return _parse_detailed(
            lambda: FileStream(str(path), encoding="utf-8"),
            timeout=timeout,
            prepare=prepare,
        )
    except KeyboardInterrupt:
        return ParseResult(None, {}, (ParserDiagnostic(0, 0, "parser timed out"),))
    except Exception as exc:
        logger.debug("Parse error for %s", path, exc_info=True)
        return ParseResult(None, {}, (ParserDiagnostic(0, 0, str(exc)),))


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

    try:
        result = parse_string_detailed(text, timeout=timeout, prepare=prepare)
        if result.script is not None:
            return result.script, result.global_vars
        return None
    except KeyboardInterrupt:
        logger.debug("Parser timed out on string input")
    except Exception:
        if not silent:
            traceback.print_exc()
        else:
            logger.debug("Parse error on string input", exc_info=True)
    return None


def parse_string_detailed(
    text: str,
    *,
    timeout: int = 30,
    prepare: bool = True,
) -> ParseResult:
    """Parse a string and retain syntax/AST diagnostics for the caller."""
    try:
        return _parse_detailed(
            lambda: InputStream(text), timeout=timeout, prepare=prepare
        )
    except KeyboardInterrupt:
        return ParseResult(None, {}, (ParserDiagnostic(0, 0, "parser timed out"),))
    except Exception as exc:
        logger.debug("Parse error on string input", exc_info=True)
        return ParseResult(None, {}, (ParserDiagnostic(0, 0, str(exc)),))
