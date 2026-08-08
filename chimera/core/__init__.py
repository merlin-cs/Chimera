"""Core modules shared across all fuzzing engines.

Submodules
----------
smt_ast
    Refactored AST with Visitor / Transformer patterns.
smt_parser
    Clean ANTLR facade for parsing SMT-LIB 2.6 files and strings.
solver_manager
    Safe subprocess wrapper for invoking SMT solvers.
differential_oracle
    Test oracle comparing solver outputs for bug detection.
types
    SMT-LIB type constants and utilities.
timeout
    Timeout decorator for long-running operations.
logic_analyzer
    SMT logic analysis and compatibility checking.
formula_builder
    SMT-LIB formula construction utilities.
"""

from chimera.core.smt_parser import (
    ParseResult,
    ParserDiagnostic,
    parse_file,
    parse_file_detailed,
    parse_string,
    parse_string_detailed,
)
from chimera.core.solver_manager import SolverConfig, SolverResult, run_solver
from chimera.core.differential_oracle import BugKind, BugReport, compare
from chimera.core.types import (
    BOOLEAN_TYPE,
    INTEGER_TYPE,
    REAL_TYPE,
    STRING_TYPE,
    BITVECTOR_TYPE,
    FP_TYPE,
    ARRAY_TYPE,
)
from chimera.core.logic_analyzer import (
    LogicCapability,
    LogicInfo,
    detect_script_logic,
    parse_logic,
    is_logic_compatible,
    get_compatible_logics,
    is_builtin_sort,
    extract_sorts_from_declaration,
    BUILTIN_SORTS,
)
from chimera.core.formula_builder import (
    smt_paren_depth,
    balance_parentheses,
    validate_smt_formula,
    strip_named_annotation,
    format_smt_string,
    insert_push_and_pop,
    is_valid_symbol_name,
    build_type_var_map,
    variable_translocation,
    extract_function_name,
    build_smt_script,
    FormulaValidator,
    validate_generated_formula,
)
from chimera.core.campaign import (
    ARTIFACT_FORMAT_VERSION,
    CAMPAIGN_CONFIG_VERSION,
    ArtifactStore,
    CampaignConfig,
    CampaignRunner,
    CaseProducer,
    StrategyCaseProducer,
    replay_artifact,
)

__all__ = [
    # Parser
    "parse_file",
    "parse_file_detailed",
    "parse_string",
    "parse_string_detailed",
    "ParseResult",
    "ParserDiagnostic",
    # Solver
    "SolverConfig",
    "SolverResult",
    "run_solver",
    # Oracle
    "BugKind",
    "BugReport",
    "compare",
    # Types
    "BOOLEAN_TYPE",
    "INTEGER_TYPE",
    "REAL_TYPE",
    "STRING_TYPE",
    "BITVECTOR_TYPE",
    "FP_TYPE",
    "ARRAY_TYPE",
    # Logic analyzer
    "LogicCapability",
    "LogicInfo",
    "parse_logic",
    "is_logic_compatible",
    "get_compatible_logics",
    "is_builtin_sort",
    "extract_sorts_from_declaration",
    "BUILTIN_SORTS",
    "detect_script_logic",
    # Formula builder
    "smt_paren_depth",
    "balance_parentheses",
    "validate_smt_formula",
    "strip_named_annotation",
    "format_smt_string",
    "insert_push_and_pop",
    "is_valid_symbol_name",
    "build_type_var_map",
    "variable_translocation",
    "extract_function_name",
    "build_smt_script",
    "validate_generated_formula",
    "FormulaValidator",
    # Campaigns
    "ARTIFACT_FORMAT_VERSION",
    "CAMPAIGN_CONFIG_VERSION",
    "ArtifactStore",
    "CampaignConfig",
    "CampaignRunner",
    "CaseProducer",
    "StrategyCaseProducer",
    "replay_artifact",
]
