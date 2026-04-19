"""
Logic-aware corpus dataclasses for HistFuzz.

This module defines the data structures for storing building blocks and
skeletons with full context: logic classification, sort/function dependencies,
and variable declarations.

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import json
import random
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

from chimera.core.smt_ast import Term, Hole, is_hole
from chimera.core.smt_parser import parse_string
from chimera.core.logic_analyzer import parse_logic, is_logic_compatible
from chimera.core.types import UNKNOWN


@dataclass
class FuncInfo:
    """Function signature information.

    Attributes
    ----------
    name : str
        Function name.
    arg_sorts : List[str]
        Argument sort types.
    ret_sort : str
        Return sort type.
    """
    name: str
    arg_sorts: List[str]
    ret_sort: str

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "arg_sorts": self.arg_sorts,
            "ret_sort": self.ret_sort,
        }

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "FuncInfo":
        return cls(
            name=data["name"],
            arg_sorts=data["arg_sorts"],
            ret_sort=data["ret_sort"],
        )


@dataclass
class BuildingBlock:
    """Atomic formula with full context for valid reconstruction.

    A building block is an atomic (non-connective) sub-term extracted from
    a historical bug-triggering formula. It carries all necessary context
    to be safely inserted into a skeleton hole.

    Attributes
    ----------
    term_smt2 : str
        SMT-LIB string representation of the term.
    logic : str
        Source logic (e.g., "QF_LIA", "AUFLIA", "QF_BV").
    sort_deps : Set[str]
        Required sorts (e.g., {"Int", "(_ BitVec 32)"}).
    func_deps : Set[str]
        Required function names (e.g., {"<=", "+", "select"}).
    var_decls : Dict[str, str]
        Variable declarations {name: sort_string}.
    func_decls : Dict[str, FuncInfo]
        Function signatures {name: (arg_sorts, ret_sort)}.
    term : Optional[Term]
        Parsed Term object (lazy-loaded, cached).
    """
    term_smt2: str
    logic: str
    sort_deps: Set[str] = field(default_factory=set)
    func_deps: Set[str] = field(default_factory=set)
    var_decls: Dict[str, str] = field(default_factory=dict)
    func_decls: Dict[str, FuncInfo] = field(default_factory=dict)
    term: Optional[Term] = field(default=None, repr=False)

    def __post_init__(self) -> None:
        """Ensure sort_deps contains only non-built-in sorts."""
        from chimera.core.logic_analyzer import is_builtin_sort

        # Filter to only non-builtin sorts that need declaration
        self.sort_deps = {
            s for s in self.sort_deps
            if not is_builtin_sort(s) and s.strip()
        }

    @property
    def term_obj(self) -> Optional[Term]:
        """Lazy-load the Term object."""
        if self.term is None and self.term_smt2:
            result = parse_string(f"(assert {self.term_smt2})", silent=True)
            if result is not None:
                script, _ = result
                if script and script.assert_cmd:
                    self.term = script.assert_cmd[0].term
        return self.term

    @property
    def type_hint(self) -> Optional[str]:
        """Return the type of this building block."""
        if self.term_obj:
            return str(self.term_obj.type) if self.term_obj.type else "Bool"
        return "Bool"

    def is_quantified(self) -> bool:
        """Check if this block contains quantifiers."""
        if self.term_obj:
            return self._term_has_quantifier(self.term_obj)
        return False

    def _term_has_quantifier(self, term: Term) -> bool:
        """Recursively check if a Term tree contains any quantifier."""
        if term.quantifier is not None:
            return True
        if term.subterms:
            for s in term.subterms:
                if isinstance(s, Term) and self._term_has_quantifier(s):
                    return True
        return False

    def to_dict(self) -> Dict[str, Any]:
        """Serialize to dictionary for JSON storage."""
        return {
            "term_smt2": self.term_smt2,
            "logic": self.logic,
            "sort_deps": list(self.sort_deps),
            "func_deps": list(self.func_deps),
            "var_decls": self.var_decls,
            "func_decls": {k: v.to_dict() for k, v in self.func_decls.items()},
        }

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "BuildingBlock":
        """Deserialize from dictionary."""
        return cls(
            term_smt2=data["term_smt2"],
            logic=data["logic"],
            sort_deps=set(data.get("sort_deps", [])),
            func_deps=set(data.get("func_deps", [])),
            var_decls=data.get("var_decls", {}),
            func_decls={
                k: FuncInfo.from_dict(v)
                for k, v in data.get("func_decls", {}).items()
            },
        )


@dataclass
class Skeleton:
    """Assertion skeleton with HOLE placeholders and requirements.

    A skeleton is an assertion term with atomic sub-terms replaced by
    HOLE placeholders. It tracks the minimum logic required and the
    types expected at each hole position.

    Attributes
    ----------
    term_smt2 : str
        SMT-LIB string representation with HOLE placeholders.
    logic : str
        Minimum logic required (e.g., "QF_LIA", "AUFLIA").
    is_quantified : bool
        True if the skeleton contains quantifiers.
    hole_types : List[str]
        Types expected at each hole position (in order).
    sort_deps : Set[str]
        Required sorts (non-built-in).
    func_deps : Set[str]
        Required function names.
    var_decls : Dict[str, str]
        Variable declarations {name: sort_string}.
    func_decls : Dict[str, FuncInfo]
        Function signatures {name: (arg_sorts, ret_sort)}.
    term : Optional[Term]
        Parsed Term object (lazy-loaded, cached).
    """
    term_smt2: str
    logic: str
    is_quantified: bool = False
    hole_types: List[str] = field(default_factory=list)
    sort_deps: Set[str] = field(default_factory=set)
    func_deps: Set[str] = field(default_factory=set)
    var_decls: Dict[str, str] = field(default_factory=dict)
    func_decls: Dict[str, FuncInfo] = field(default_factory=dict)
    term: Optional[Term] = field(default=None, repr=False)

    def __post_init__(self) -> None:
        """Ensure sort_deps contains only non-built-in sorts."""
        from chimera.core.logic_analyzer import is_builtin_sort

        self.sort_deps = {
            s for s in self.sort_deps
            if not is_builtin_sort(s) and s.strip()
        }

    @property
    def term_obj(self) -> Optional[Term]:
        """Lazy-load the Term object."""
        if self.term is None and self.term_smt2:
            result = parse_string(f"(assert {self.term_smt2})", silent=True)
            if result is not None:
                script, _ = result
                if script and script.assert_cmd:
                    self.term = script.assert_cmd[0].term
        return self.term

    @property
    def num_holes(self) -> int:
        """Return the number of holes in this skeleton."""
        return len(self.hole_types)

    def collect_holes(self) -> List[Term]:
        """Collect all HOLE terms from the parsed term."""
        from chimera.core.smt_ast import HoleCollector

        if self.term_obj is None:
            return []

        collector = HoleCollector()
        collector.visit(self.term_obj)
        return collector.holes

    def to_dict(self) -> Dict[str, Any]:
        """Serialize to dictionary for JSON storage."""
        return {
            "term_smt2": self.term_smt2,
            "logic": self.logic,
            "is_quantified": self.is_quantified,
            "hole_types": self.hole_types,
            "sort_deps": list(self.sort_deps),
            "func_deps": list(self.func_deps),
            "var_decls": self.var_decls,
            "func_decls": {k: v.to_dict() for k, v in self.func_decls.items()},
        }

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "Skeleton":
        """Deserialize from dictionary."""
        return cls(
            term_smt2=data["term_smt2"],
            logic=data["logic"],
            is_quantified=data.get("is_quantified", False),
            hole_types=data.get("hole_types", []),
            sort_deps=set(data.get("sort_deps", [])),
            func_deps=set(data.get("func_deps", [])),
            var_decls=data.get("var_decls", {}),
            func_decls={
                k: FuncInfo.from_dict(v)
                for k, v in data.get("func_decls", {}).items()
            },
        )


@dataclass
class Corpus:
    """Logic-classified collection of skeletons and building blocks.

    The corpus organizes extracted formulas by logic, enabling logic-aware
    filtering during formula generation. It supports both QF and quantified
    formulas, with explicit tracking of dependencies.

    Attributes
    ----------
    blocks : Dict[str, List[BuildingBlock]]
        Building blocks grouped by logic.
    skeletons : Dict[str, List[Skeleton]]
        Skeletons grouped by logic.
    metadata : Dict[str, Any]
        Corpus statistics and metadata.
    """
    blocks: Dict[str, List[BuildingBlock]] = field(default_factory=dict)
    skeletons: Dict[str, List[Skeleton]] = field(default_factory=dict)
    metadata: Dict[str, Any] = field(default_factory=dict)

    def add_block(self, block: BuildingBlock) -> None:
        """Add a building block to the corpus."""
        logic = block.logic.upper()
        if logic not in self.blocks:
            self.blocks[logic] = []
        self.blocks[logic].append(block)

    def add_skeleton(self, skel: Skeleton) -> None:
        """Add a skeleton to the corpus."""
        logic = skel.logic.upper()
        if logic not in self.skeletons:
            self.skeletons[logic] = []
        self.skeletons[logic].append(skel)

    def get_blocks(self, logics: Optional[Set[str]] = None) -> List[BuildingBlock]:
        """Get building blocks, optionally filtered by logics."""
        if logics is None:
            logics = set(self.blocks.keys())

        result = []
        for logic in logics:
            if logic in self.blocks:
                result.extend(self.blocks[logic])
        return result

    def get_skeletons(
        self,
        logics: Optional[Set[str]] = None,
        quantified: Optional[bool] = None,
    ) -> List[Skeleton]:
        """Get skeletons, optionally filtered by logic and quantifier status.

        Parameters
        ----------
        logics : Set[str], optional
            Filter to these logics only.
        quantified : bool, optional
            If True, only quantified skeletons. If False, only QF skeletons.
            If None (default), return all.
        """
        if logics is None:
            logics = set(self.skeletons.keys())

        result = []
        for logic in logics:
            if logic not in self.skeletons:
                continue
            for skel in self.skeletons[logic]:
                if quantified is not None and skel.is_quantified != quantified:
                    continue
                result.append(skel)
        return result

    def get_compatible_logics(self, target_logic: str) -> Set[str]:
        """Find all logics compatible with the target logic.

        A source logic is compatible with target if formulas from the
        source can be safely used in the target context.
        """
        compatible = set()
        for logic in list(self.blocks.keys()) + list(self.skeletons.keys()):
            if is_logic_compatible(logic, target_logic):
                compatible.add(logic)
        return compatible

    def sample_block(self, sort_hint: Optional[str] = None, logic: Optional[str] = None) -> Optional[BuildingBlock]:
        """Sample a random building block, optionally by sort and logic."""
        candidates = self.get_blocks(logics={logic} if logic else None)

        if sort_hint and candidates:
            # Filter by sort compatibility
            sort_hint_upper = sort_hint.upper()
            matching = [
                b for b in candidates
                if b.type_hint and sort_hint_upper in b.type_hint.upper()
            ]
            if matching:
                candidates = matching

        return random.choice(candidates) if candidates else None

    def sample_skeleton(
        self,
        logic: Optional[str] = None,
        quantified: Optional[bool] = None,
    ) -> Optional[Skeleton]:
        """Sample a random skeleton, optionally by logic and quantifier status."""
        candidates = self.get_skeletons(
            logics={logic} if logic else None,
            quantified=quantified,
        )
        return random.choice(candidates) if candidates else None

    def statistics(self) -> Dict[str, Any]:
        """Return corpus statistics."""
        stats = {
            "total_blocks": sum(len(b) for b in self.blocks.values()),
            "total_skeletons": sum(len(s) for s in self.skeletons.values()),
            "logics": list(self.blocks.keys()),
            "blocks_by_logic": {k: len(v) for k, v in self.blocks.items()},
            "skeletons_by_logic": {k: len(v) for k, v in self.skeletons.items()},
        }

        # Quantified vs QF breakdown
        qf_skeletons = sum(
            1 for s in sum(self.skeletons.values(), [])
            if not s.is_quantified
        )
        quant_skeletons = len(sum(self.skeletons.values(), [])) - qf_skeletons
        stats["qf_skeletons"] = qf_skeletons
        stats["quantified_skeletons"] = quant_skeletons

        stats.update(self.metadata)
        return stats

    def to_json(self) -> str:
        """Serialize corpus to JSON string."""
        return json.dumps({
            "blocks": {
                logic: [b.to_dict() for b in blocks]
                for logic, blocks in self.blocks.items()
            },
            "skeletons": {
                logic: [s.to_dict() for s in skeletons]
                for logic, skeletons in self.skeletons.items()
            },
            "metadata": self.metadata,
        }, indent=2)

    @classmethod
    def from_json(cls, json_str: str) -> "Corpus":
        """Deserialize corpus from JSON string."""
        data = json.loads(json_str)

        corpus = cls(metadata=data.get("metadata", {}))

        for logic, block_dicts in data.get("blocks", {}).items():
            for bd in block_dicts:
                corpus.add_block(BuildingBlock.from_dict(bd))

        for logic, skel_dicts in data.get("skeletons", {}).items():
            for sd in skel_dicts:
                corpus.add_skeleton(Skeleton.from_dict(sd))

        return corpus

    def save(self, output_dir: str) -> None:
        """Save corpus to directory as JSON files.

        Creates structure:
            output_dir/
                metadata.json
                blocks/
                    {LOGIC}.json        # Blocks grouped by logic
                skeletons_qf.json       # Quantifier-free skeletons (all logics)
                skeletons_quant.json    # Quantified skeletons (all logics)
        """
        out = Path(output_dir)
        out.mkdir(parents=True, exist_ok=True)

        # Save metadata
        with open(out / "metadata.json", "w") as f:
            json.dump(self.statistics(), f, indent=2)

        # Save blocks grouped by logic
        blocks_dir = out / "blocks"
        blocks_dir.mkdir(parents=True, exist_ok=True)

        for logic, blocks in self.blocks.items():
            if blocks:
                with open(blocks_dir / f"{logic}.json", "w") as f:
                    json.dump([b.to_dict() for b in blocks], f, indent=2)

        # Save skeletons by quantifier status (not by logic)
        qf_skeletons: List[Dict[str, Any]] = []
        quant_skeletons: List[Dict[str, Any]] = []

        for logic, skeletons in self.skeletons.items():
            for skel in skeletons:
                if skel.is_quantified:
                    quant_skeletons.append(skel.to_dict())
                else:
                    qf_skeletons.append(skel.to_dict())

        if qf_skeletons:
            with open(out / "skeletons_qf.json", "w") as f:
                json.dump(qf_skeletons, f, indent=2)

        if quant_skeletons:
            with open(out / "skeletons_quant.json", "w") as f:
                json.dump(quant_skeletons, f, indent=2)

    @classmethod
    def load(cls, input_dir: str) -> "Corpus":
        """Load corpus from directory structure.

        Reads from:
            input_dir/
                metadata.json (optional)
                blocks/
                    {LOGIC}.json
                skeletons_qf.json
                skeletons_quant.json
        """
        corpus = cls()
        inp = Path(input_dir)

        if not inp.exists():
            return corpus

        # Load metadata if present
        meta_file = inp / "metadata.json"
        if meta_file.exists():
            with open(meta_file) as f:
                corpus.metadata = json.load(f)

        # Load blocks from blocks/ directory
        blocks_dir = inp / "blocks"
        if blocks_dir.is_dir():
            for blocks_file in blocks_dir.glob("*.json"):
                logic = blocks_file.stem  # filename without .json
                with open(blocks_file) as f:
                    for bd in json.load(f):
                        block = BuildingBlock.from_dict(bd)
                        # Ensure logic matches filename
                        block.logic = logic
                        corpus.add_block(block)

        # Load QF skeletons
        qf_file = inp / "skeletons_qf.json"
        if qf_file.exists():
            with open(qf_file) as f:
                for sd in json.load(f):
                    corpus.add_skeleton(Skeleton.from_dict(sd))

        # Load quantified skeletons
        quant_file = inp / "skeletons_quant.json"
        if quant_file.exists():
            with open(quant_file) as f:
                for sd in json.load(f):
                    corpus.add_skeleton(Skeleton.from_dict(sd))

        return corpus


class BuildingBlockPool:
    """Type-aware pool of building blocks for hole filling.

    This is a wrapper around Corpus.blocks that provides efficient
    sampling by sort hint.

    Attributes
    ----------
    _blocks : Dict[str, List[BuildingBlock]]
        Blocks indexed by sort string.
    _all : List[BuildingBlock]
        Flat list of all blocks.
    """

    def __init__(self, corpus: Optional[Corpus] = None) -> None:
        self._blocks: Dict[str, List[BuildingBlock]] = {}
        self._all: List[BuildingBlock] = []

        if corpus is not None:
            for logic, blocks in corpus.blocks.items():
                for block in blocks:
                    self._add(block)

    def _add(self, block: BuildingBlock) -> None:
        """Add a block to the pool."""
        sort_key = block.type_hint or "Bool"
        self._blocks.setdefault(sort_key, []).append(block)
        self._all.append(block)

    def sample(self, sort_hint: Optional[str] = None) -> Optional[BuildingBlock]:
        """Sample a random block, optionally matching sort hint."""
        if sort_hint:
            # Try exact match first
            candidates = self._blocks.get(sort_hint, [])
            if not candidates:
                # Try substring match
                candidates = [
                    b for sort, blocks in self._blocks.items()
                    for b in blocks
                    if sort_hint.lower() in sort.lower()
                ]
            if not candidates:
                return None
        else:
            candidates = self._all
            if not candidates:
                return None

        return random.choice(candidates)

    @property
    def total(self) -> int:
        """Return total number of blocks."""
        return len(self._all)

    @property
    def sort_keys(self) -> Set[str]:
        """Return all sort keys in the pool."""
        return set(self._blocks.keys())
