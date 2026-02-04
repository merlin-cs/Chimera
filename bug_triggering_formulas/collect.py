import multiprocessing
import os
import re
import z3
from typing import Set, Dict, Optional
from pathlib import Path
import sys

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))
from src.parsing.Parse import parse_file
from src.parsing.Ast import DeclareFun, Define, DeclareConst, DefineConst, FunDecl, Assert, CheckSat, Push, Pop, Term
import shutil
import logging
import json
import time
import requests
from datetime import datetime, timedelta
import argparse

# Set up logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler()]
)
logger = logging.getLogger(__name__)

# Cache configuration
CURRENT_DIR = Path(__file__).parent
CACHE_DIR = CURRENT_DIR / "github_cache"
CACHE_EXPIRATION = timedelta(hours=24)
CACHE_DIR.mkdir(exist_ok=True)


def check_title(title: str):
    title = title.lower()
    keywords = [
        "soundness", "bug", "issue", "invalid", "segfault", "correct",
        "assertion", "failure", "after-free", "leak", "overflow", "use after free",
        "crash", "panic", "abort", "exception", "internal error", "incorrect", 
        "unsat", "unexpected", "model"
    ]
    for k in keywords:
        if k in title:
            return True

    return False


def collect_buggy_formula(github_token, solver, stored_dir):
    # Initialize API
    github_api = GitHubAPI(token=github_token)

    # set up repository information
    solver_repo_map = {
        "z3": "Z3Prover/z3",
        "cvc5": "cvc5/cvc5", 
        "yices2": "SRI-CSL/yices2", 
        "opensmt": "usi-verification-and-security/opensmt",
        "cvc5-projects": "cvc5/cvc5"
    }
    
    repo_name = solver_repo_map.get(solver)
    if not repo_name:
        print(f"Unknown solver: {solver}")
        return

    # create directory to store formulas
    stored_dir = stored_dir + "/" + solver
    if not os.path.exists(stored_dir):
        os.makedirs(stored_dir)

    print(f"Updating {solver} from {repo_name}...")

    # Iterate issues
    for issue in get_repo_issues_in_range(github_api, repo_name):
        try:
            issue_number = issue['number']
            issue_title = issue['title']
            issue_body = issue.get('body', '') or ''
            
            if check_title(issue_title):
                print(f"{issue_number} {issue_title}")
                count = 0
                
                # Check Issue Body
                if "```" in issue_body or "~~~" in issue_body or "cat " in issue_body or "declare-" in issue_body:
                    buggy_formulas = extract_formula(issue_body)
                    
                    if buggy_formulas.strip():
                        file_name = f"{stored_dir}/{solver}_{issue_number}_{count}.smt2"
                        if not os.path.exists(file_name):
                            with open(file_name, "w") as output:
                                output.write(buggy_formulas)
                            standardize_single_instance(file_name)
                            classify_and_move(file_name)
                            count += 1
                
                # Check Comments
                comments_count = issue.get('comments', 0)
                if comments_count > 0:
                    comments_url = issue.get('comments_url')
                    # Flatten comments just in case, but usually just fetch
                    comments_cache_key = f"comments_{repo_name}_{issue_number}"
                    try:
                        comments = github_api.request(comments_url, params={"per_page": 100}, cache_key=comments_cache_key)
                        if isinstance(comments, list):
                            for comment in comments:
                                comment_body = comment.get('body', '') or ''
                                if "```" in comment_body or "~~~" in comment_body or "cat " in comment_body or "declare-" in comment_body:
                                    buggy_formulas = extract_formula(comment_body)
                                    if buggy_formulas.strip():
                                        file_name = f"{stored_dir}/{solver}_{issue_number}_{count}.smt2"
                                        if not os.path.exists(file_name):
                                            with open(file_name, "w") as output:
                                                output.write(buggy_formulas)
                                            standardize_single_instance(file_name)
                                            classify_and_move(file_name)
                                            count += 1
                    except Exception as e:
                        logger.error(f"Error fetching comments for issue {issue_number}: {e}")

        except Exception as e:
            logger.error(f"Error processing issue {issue.get('number', 'unknown')}: {e}")
            pass





def extract_formula(content):
    """
    Extracts SMT2 formula from text content (issue body or comment).
    Handles markdown code blocks and heuristic extraction.
    """
    formulas = []
    
    # Regex to find code blocks (``` or ~~~)
    # Use non-greedy match for content
    block_pattern = r"(?:```|~~~)(?:[\w\-]*)?\r?\n(.*?)[\r\n]+(?:```|~~~)"
    blocks = re.findall(block_pattern, content, re.DOTALL)
    
    for block in blocks:
        smt2 = clean_smt2_payload(block)
        if smt2:
            formulas.append(smt2)
            
    # If no blocks found, search in raw content
    if not formulas:
        smt2 = clean_smt2_payload(content)
        if smt2:
            formulas.append(smt2)
            
    return "\n".join(formulas)


def clean_smt2_payload(text):
    """
    Finds the start of SMT2 formula in a text block.
    """
    # Find start index of first common SMT command
    # Valid starts: (set-*, (declare-*, (define-*, (assert, (check-sat
    # Also support 'cat file.smt2' style lead-ins
    
    # Scan for common start commands
    match = re.search(r"(\((?:set-|declare-|define-|assert|check-sat)|cat\s+\S+\.smt2)", text)
    
    if match:
        start_idx = match.start()
        # If it matched 'cat ...', we want to skip that line
        if text[start_idx:].startswith("cat"):
            newline_match = re.search(r"\n", text[start_idx:])
            if newline_match:
                start_idx += newline_match.end()
            else:
                return None # cat command but no content?
        
        candidate = text[start_idx:]
        # Quick validation: should have at least one valid SMT2 command
        if "(" in candidate and ")" in candidate:
             return candidate
             
    return None



def check_ref(issue):
    events = issue.events()
    for e in events:
        if e.event == "referenced":
            return True
    return False



def auto_collect_buggy_formulas(token, store_path):
    """
    This function collects bug-triggering formulas from multiple solvers' bug trackers concurrently
    using Python's multiprocessing library.

    :param token: A GitHub personal access token to access the bug trackers of solvers.
    :param store_path: A string representing the path where the collected formulas will be stored.
    :return: None
    """
    
    # A list of solvers whose bug trackers will be searched for bug-triggering formulas
    solvers = ["z3", "cvc5", "yices2", "opensmt", "cvc5-projects"]
    
    # A list to hold all the processes
    process_pool = []
    
    # Check for token in env if not provided
    if not token:
        token = os.environ.get("GITHUB_TOKEN")

    # Start a new process for each solver and add the process to the process_pool
    for solver in solvers:
        p = multiprocessing.Process(target=collect_buggy_formula, args=(token, solver, store_path))
        p.start()
        process_pool.append(p)
        
    # Wait for all the processes to finish
    while process_pool:
        for index, process in enumerate(process_pool):
            # Check if the process is still alive
            if not process.is_alive():
                # Remove the process from the pool if it has completed
                process_pool.pop(index)
                break

def process_seed(seed):
    script, glob = parse_file(seed, silent=True)
    return script, glob


def standardize_single_instance(file):
    # Process the SMT formula and extract the variable information
    script, var = process_seed(file)
    new_script = []
    if script is not None:
        # Read the original SMT formula from the file
        with open(file, "r") as f:
            content = f.readlines()
        # Add any "declare-sort" or "define-sort" lines to the new script
        for line in content:
            if "declare-sort" in line or "define-sort" in line:
                new_script.append(line)
        # Add each command in the processed script to the new script
        for i in script.commands:
            # Only add commands with common types
            if check_ast_type(type(i)):
                new_script.append(str(i))
        # Ensure that the "check-sat" command is present at the end of the script
        if len(new_script) > 1:
            if "(check-sat)" not in new_script[-1] and "(check-sat)" not in new_script[-2]:
                new_script.append("(check-sat)")
        elif len(new_script) == 1 and "(check-sat)" not in new_script[-1]:
            new_script.append("(check-sat)")
        # Write the new script to the file
        with open(file, "w") as f2:
            for l in new_script:
                f2.write(l + "\n")
    else:
        # If the formula could not be processed, remove the file
        os.remove(file)

def check_ast_type(ast_type):
    if ast_type in [Define, DefineConst, DeclareConst, DeclareFun, FunDecl, Assert, Push, Pop, CheckSat]:
        return True
    else:
        return False

class LogicFeatures:
    """Container for tracking formula features during AST traversal."""
    
    def __init__(self):
        # Quantifier tracking
        self.has_quantifiers = False
        
        # Sort tracking
        self.uses_int = False
        self.uses_real = False
        self.uses_bv = False
        self.uses_array = False
        self.uses_uninterpreted_sorts = False
        
        # Function tracking
        self.uses_uf = False  # Uninterpreted functions
        
        # Arithmetic properties
        self.is_nonlinear = False
        self.is_difference_logic = True  # Assume DL until proven otherwise
        self.has_arithmetic = False
        
        # Array properties
        self.array_index_sort = None
        self.array_value_sort = None
        
    def __repr__(self):
        return (f"LogicFeatures(quantifiers={self.has_quantifiers}, "
                f"int={self.uses_int}, real={self.uses_real}, "
                f"bv={self.uses_bv}, array={self.uses_array}, "
                f"uf={self.uses_uf}, nonlinear={self.is_nonlinear}, "
                f"diff_logic={self.is_difference_logic})")


class SMTLogicDetector:
    """Detects the SMT-LIB logic of a formula through AST traversal."""
    
    def __init__(self):
        self.features = LogicFeatures()
        self.visited = set()
        self.declared_functions = {}
        
    def detect_from_file(self, formula_path: str) -> str:
        """
        Detect logic from a .smt2 file.
        
        Args:
            formula_path: Path to the .smt2 file
            
        Returns:
            String representing the SMT-LIB logic (e.g., "QF_LIA")
        """
        # Create a solver and parse the SMT2 file
        solver = z3.Solver()
        # Parse and load the file into the solver
        formulas = z3.parse_smt2_file(formula_path, sorts={}, decls={}, ctx=solver.ctx)
        
        # Traverse all formulas (assertions)
        for formula in formulas:
            self._traverse(formula)
        
        # Also traverse the solver's assertions to catch all symbols
        for assertion in solver.assertions():
            self._traverse(assertion)
            
        # Check declarations by reading the file directly
        self._analyze_file_declarations(formula_path)
            
        return self._determine_logic()
    
    def _analyze_file_declarations(self, formula_path: str):
        """
        Analyze declarations in an SMT2 file to detect sorts and functions.
        This helps when the file has declarations but no assertions.
        """
        try:
            with open(formula_path, 'r') as f:
                content = f.read()
                
            # Check for array declarations
            if '(Array' in content:
                self.features.uses_array = True
                # Try to determine array element types
                if 'Int' in content:
                    self.features.uses_int = True
                if 'Real' in content:
                    self.features.uses_real = True
                if 'BitVec' in content or '_ BitVec' in content:
                    self.features.uses_bv = True
                    
            # Check for declare-sort (uninterpreted sorts)
            if '(declare-sort' in content:
                self.features.uses_uninterpreted_sorts = True
                self.features.uses_uf = True
                
            # Check for declare-fun with non-zero arity (uninterpreted functions)
            # Pattern: (declare-fun name (arg1 arg2 ...) return)
            # If args is not empty, it's a function
            fun_pattern = r'\(declare-fun\s+\S+\s+\(([^)]*)\)'
            for match in re.finditer(fun_pattern, content):
                args = match.group(1).strip()
                if args:  # Non-empty argument list means it's a function, not a constant
                    self.features.uses_uf = True
                    
            # Check for quantifiers
            if '(forall' in content or '(exists' in content:
                self.features.has_quantifiers = True
                
            # Check for bitvector ops
            if any(op in content for op in ['bvadd', 'bvsub', 'bvmul', 'concat', 'extract']):
                self.features.uses_bv = True
                
        except Exception as e:
            # If file analysis fails, continue with what we have
            pass
    
    def detect_from_formula(self, formula) -> str:
        """
        Detect logic from a Z3 formula object.
        
        Args:
            formula: Z3 expression or list of expressions
            
        Returns:
            String representing the SMT-LIB logic
        """
        if isinstance(formula, list):
            for f in formula:
                self._traverse(f)
        else:
            self._traverse(formula)
            
        return self._determine_logic()
    
    def _traverse(self, expr):
        """
        Recursively traverse the AST to collect features.
        
        Args:
            expr: Z3 expression to traverse
        """
        # Avoid revisiting nodes
        expr_id = id(expr)
        if expr_id in self.visited:
            return
        self.visited.add(expr_id)
        
        # Check if this is a quantifier
        if z3.is_quantifier(expr):
            self.features.has_quantifiers = True
            # Traverse the body
            self._traverse(expr.body())
            return
        
        # Check if this is an expression (not a sort)
        if not z3.is_expr(expr):
            return
            
        # Detect sort (type) of the expression
        self._detect_sort(expr)
        
        # Detect operator and update features
        if z3.is_app(expr):
            self._analyze_application(expr)
        
        # Recursively traverse children
        for child in expr.children():
            self._traverse(child)
    
    def _detect_sort(self, expr):
        """Detect and record the sort (type) of an expression."""
        try:
            sort = expr.sort()
            
            if z3.is_int(expr):
                self.features.uses_int = True
            elif z3.is_real(expr):
                self.features.uses_real = True
            elif z3.is_bv(expr):
                self.features.uses_bv = True
            elif z3.is_array(expr):
                self.features.uses_array = True
                # Track array index and value sorts
                if self.features.array_index_sort is None:
                    self.features.array_index_sort = sort.domain()
                    self.features.array_value_sort = sort.range()
            elif not z3.is_bool(expr):
                # Check if it's an uninterpreted sort
                sort_kind = sort.kind()
                if sort_kind == z3.Z3_UNINTERPRETED_SORT:
                    self.features.uses_uninterpreted_sorts = True
                    self.features.uses_uf = True
        except:
            pass
    
    def _analyze_application(self, expr):
        """Analyze a function application to detect operators and properties."""
        decl = expr.decl()
        kind = decl.kind()
        num_args = expr.num_args()
        
        # Check for quantifiers (though these should be caught earlier)
        # Note: Z3_OP_FORALL and Z3_OP_EXISTS might not exist as constants
        # Quantifiers are handled by is_quantifier check above
        
        # Check for uninterpreted functions
        # A function is uninterpreted if:
        # 1. It has kind Z3_OP_UNINTERPRETED
        # 2. AND it has arguments (arity > 0)
        # Simple constants like Int('x') have arity 0 and should not be treated as UF
        if kind == z3.Z3_OP_UNINTERPRETED and num_args > 0:
            self.features.uses_uf = True
            # Store function info
            func_name = decl.name()
            if func_name not in self.declared_functions:
                self.declared_functions[func_name] = decl
            return
        
        # Check for array operations
        if kind in (z3.Z3_OP_SELECT, z3.Z3_OP_STORE):
            self.features.uses_array = True
            return
        
        # Analyze arithmetic operations
        self._analyze_arithmetic(expr, kind, num_args)
    
    def _analyze_arithmetic(self, expr, kind, num_args):
        """Analyze arithmetic operations to detect linearity and difference logic."""
        
        # Arithmetic operators
        arith_ops = {
            z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS,
            z3.Z3_OP_MUL, z3.Z3_OP_DIV, z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM,
            z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT,
            z3.Z3_OP_TO_REAL, z3.Z3_OP_TO_INT, z3.Z3_OP_IS_INT
        }
        
        if kind not in arith_ops:
            return
            
        self.features.has_arithmetic = True
        
        # Check for non-linear operations
        if kind == z3.Z3_OP_MUL:
            # Check if we're multiplying two non-constant variables
            children = expr.children()
            non_const_vars = [c for c in children if not z3.is_int_value(c) and not z3.is_rational_value(c)]
            if len(non_const_vars) >= 2:
                self.features.is_nonlinear = True
                self.features.is_difference_logic = False
        
        # Division and modulo are non-linear (unless by constant, but we'll be conservative)
        if kind in (z3.Z3_OP_DIV, z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM):
            # Check if divisor is constant
            if num_args >= 2:
                divisor = expr.arg(1)
                if not (z3.is_int_value(divisor) or z3.is_rational_value(divisor)):
                    self.features.is_nonlinear = True
            self.features.is_difference_logic = False
        
        # Check for difference logic pattern: x - y < c or x - y <= c
        # DL requires all arithmetic to be in this form
        if kind in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT):
            if not self._is_difference_logic_constraint(expr):
                self.features.is_difference_logic = False
        elif kind not in (z3.Z3_OP_SUB, z3.Z3_OP_UMINUS):
            # Any arithmetic operation other than subtraction breaks DL
            if kind in arith_ops:
                self.features.is_difference_logic = False
    
    def _is_difference_logic_constraint(self, expr) -> bool:
        """
        Check if an inequality is in difference logic form: x - y < c
        
        Args:
            expr: Z3 inequality expression
            
        Returns:
            True if the constraint is in DL form
        """
        if expr.num_args() != 2:
            return False
        
        lhs = expr.arg(0)
        rhs = expr.arg(1)
        
        # Pattern 1: (x - y) < c or c < (x - y)
        if self._is_difference(lhs) and self._is_constant(rhs):
            return True
        if self._is_constant(lhs) and self._is_difference(rhs):
            return True
        
        # Pattern 2: x < y (equivalent to x - y < 0)
        if self._is_variable(lhs) and self._is_variable(rhs):
            return True
        
        # Pattern 3: x < c (equivalent to x - 0 < c)
        if self._is_variable(lhs) and self._is_constant(rhs):
            return True
        if self._is_constant(lhs) and self._is_variable(rhs):
            return True
        
        return False
    
    def _is_difference(self, expr) -> bool:
        """Check if expression is a difference of two variables: x - y"""
        if not z3.is_app(expr):
            return False
        if expr.decl().kind() != z3.Z3_OP_SUB:
            return False
        if expr.num_args() != 2:
            return False
        return self._is_variable(expr.arg(0)) and self._is_variable(expr.arg(1))
    
    def _is_variable(self, expr) -> bool:
        """Check if expression is a variable (not a constant, not a complex expression)"""
        if z3.is_int_value(expr) or z3.is_rational_value(expr):
            return False
        if not z3.is_const(expr):
            return False
        return True
    
    def _is_constant(self, expr) -> bool:
        """Check if expression is a constant value"""
        return z3.is_int_value(expr) or z3.is_rational_value(expr)
    
    def _determine_logic(self) -> str:
        """
        Map detected features to the appropriate SMT-LIB logic string.
        
        Returns:
            String representing the smallest SMT-LIB logic
        """
        f = self.features
        
        # Determine quantifier prefix
        qf_prefix = "" if f.has_quantifiers else "QF_"
        
        # Special case: Pure boolean or uninterpreted functions only
        if not (f.uses_int or f.uses_real or f.uses_bv or f.uses_array):
            if f.uses_uf:
                return f"{qf_prefix}UF"
            return f"{qf_prefix}UF"  # Default to UF for pure logic
        
        # Bitvector logics
        if f.uses_bv:
            if f.uses_array:
                if f.uses_uf:
                    return f"{qf_prefix}AUFBV"
                return f"{qf_prefix}ABV"
            if f.uses_uf:
                return f"{qf_prefix}UFBV"
            return f"{qf_prefix}BV"
        
        # Array logics (without bitvectors)
        if f.uses_array:
            # Check array index/value sorts
            has_int_array = False
            has_real_array = False
            
            if f.array_index_sort and f.array_value_sort:
                if z3.is_int(f.array_value_sort) or str(f.array_value_sort) == "Int":
                    has_int_array = True
                if z3.is_real(f.array_value_sort) or str(f.array_value_sort) == "Real":
                    has_real_array = True
            
            # Extensionality only
            if not f.has_arithmetic and not f.uses_uf:
                return f"{qf_prefix}AX"
            
            # Arrays with arithmetic
            if f.uses_uf:
                if has_real_array and f.is_nonlinear:
                    return "AUFNIRA" if f.has_quantifiers else f"{qf_prefix}AUFLIA"
                if has_real_array or f.uses_real:
                    return "AUFLIRA" if f.has_quantifiers else f"{qf_prefix}AUFLIA"
                if has_int_array or f.uses_int:
                    return "AUFLIA" if f.has_quantifiers else f"{qf_prefix}AUFLIA"
            
            return f"{qf_prefix}AX"
        
        # Arithmetic logics (no bitvectors, no arrays)
        if f.uses_int or f.uses_real:
            # Determine arithmetic type
            mixed_arith = f.uses_int and f.uses_real
            int_only = f.uses_int and not f.uses_real
            real_only = f.uses_real and not f.uses_int
            
            # Determine linearity
            if f.is_difference_logic and not f.is_nonlinear:
                # Difference Logic
                if f.uses_uf:
                    if int_only:
                        return f"{qf_prefix}UFIDL"
                    # No standard logic for UF + RDL, fall through to LRA
                
                if int_only:
                    return f"{qf_prefix}IDL"
                if real_only:
                    return f"{qf_prefix}RDL"
            
            # Linear arithmetic
            if not f.is_nonlinear:
                if f.uses_uf:
                    if int_only:
                        return "UFLIA" if f.has_quantifiers else f"{qf_prefix}UFLIA"
                    if real_only:
                        return "UFLRA" if f.has_quantifiers else f"{qf_prefix}UFLRA"
                    if mixed_arith:
                        return "UFLRA" if f.has_quantifiers else f"{qf_prefix}UFLRA"
                
                if int_only:
                    return "LIA" if f.has_quantifiers else f"{qf_prefix}LIA"
                if real_only:
                    return "LRA" if f.has_quantifiers else f"{qf_prefix}LRA"
                if mixed_arith:
                    return "LIRA" if f.has_quantifiers else f"{qf_prefix}LIRA"
            
            # Non-linear arithmetic
            else:
                if f.uses_uf:
                    if int_only:
                        return "UFNIA" if f.has_quantifiers else f"{qf_prefix}UFNIA"
                    if real_only:
                        return "UFNRA" if f.has_quantifiers else f"{qf_prefix}UFNRA"
                    if mixed_arith:
                        return "UFNRA" if f.has_quantifiers else f"{qf_prefix}UFNRA"
                
                if int_only:
                    return "NIA" if f.has_quantifiers else f"{qf_prefix}NIA"
                if real_only:
                    return "NRA" if f.has_quantifiers else f"{qf_prefix}NRA"
                if mixed_arith:
                    return "NIRA" if f.has_quantifiers else f"{qf_prefix}NIRA"
        
        # Default fallback
        # return f"{qf_prefix}UF"
        return "UNKNOWN"
 
    


def get_smt_logic(formula) -> str:
    """
    Determine the smallest SMT-LIB logic for a given formula.
    
    This function analyzes a formula (either a file path or Z3 expression)
    to determine which SMT-LIB logic it belongs to. It performs AST traversal
    to detect quantifiers, sorts, operators, and arithmetic properties.
    
    Args:
        formula: Either a string path to a .smt2 file, or a Z3 expression/list of expressions
        
    Returns:
        String representing the SMT-LIB logic (e.g., "QF_LIA", "AUFLIA", "QF_IDL")
        
    Examples:
        >>> # From file
        >>> logic = get_smt_logic("path/to/formula.smt2")
        >>> print(logic)  # e.g., "QF_LIA"
        
        >>> # From Z3 expression
        >>> x = Int('x')
        >>> y = Int('y')
        >>> formula = And(x > 0, x < y)
        >>> logic = get_smt_logic(formula)
        >>> print(logic)  # "QF_IDL"
    """
    detector = SMTLogicDetector()
    
    if isinstance(formula, (str, Path)):
        # File path provided
        return detector.detect_from_file(str(formula))
    else:
        # Z3 expression provided
        return detector.detect_from_formula(formula)


def classify_and_move(file_path):
    """
    Detects the logic of the SMT2 file and moves it to a logic-specific subdirectory.
    """
    if not os.path.exists(file_path):
        return

    try:
        # Detect logic using SMTLogicDetector
        try:
            logic = get_smt_logic(file_path)
        except Exception:
            logic = None

        # Normalize logic string; default to UNKNOWN when detection fails or returns falsy value
        logic = logic if isinstance(logic, str) and logic else "UNKNOWN"

        directory = os.path.dirname(file_path)
        filename = os.path.basename(file_path)

        # If file is already inside the correct logic directory, nothing to do
        if os.path.basename(directory) == logic:
            print(f"{filename} is already in {logic}/, skipping move")
            return file_path

        # Create logic-specific directory structure
        logic_dir = os.path.join(directory, logic)
        os.makedirs(logic_dir, exist_ok=True)

        # Build destination path; avoid overwriting existing files by adding suffix if needed
        base, ext = os.path.splitext(filename)
        new_path = os.path.join(logic_dir, filename)
        counter = 1
        while os.path.exists(new_path):
            new_path = os.path.join(logic_dir, f"{base}_{counter}{ext}")
            counter += 1

        shutil.move(file_path, new_path)
        print(f"Classified {filename} as {logic}")
        return new_path

    except Exception as e:
        # On any unexpected failure, ensure the file ends up under UNKNOWN so it's not lost
        unknown_dir = os.path.join(os.path.dirname(file_path), "UNKNOWN")
        os.makedirs(unknown_dir, exist_ok=True)

        base, ext = os.path.splitext(os.path.basename(file_path))
        dest = os.path.join(unknown_dir, os.path.basename(file_path))
        counter = 1
        while os.path.exists(dest):
            dest = os.path.join(unknown_dir, f"{base}_{counter}{ext}")
            counter += 1

        try:
            shutil.move(file_path, dest)
            logger.error(f"Failed to classify {file_path} cleanly; moved to UNKNOWN: {e}")
            return dest
        except Exception as e2:
            logger.error(f"Failed to move {file_path} to UNKNOWN: {e2}")
            return file_path




class GitHubAPI:
    def __init__(self, token=None):
        self.token = token or os.environ.get("GITHUB_TOKEN")
        self.headers = {"Accept": "application/vnd.github.v3+json"}
        if self.token:
            self.headers["Authorization"] = f"Bearer {self.token}"
        else:
            logger.warning("No GITHUB_TOKEN found. Rate limits will be restricted.")
    
    def get_cached_data(self, cache_key):
        safe_cache_key = re.sub(r'[^a-zA-Z0-9_\-\.]', '_', cache_key)
        cache_file = CACHE_DIR / f"{safe_cache_key}.json"
        if not cache_file.exists():
            return None
        try:
            with open(cache_file, 'r') as f:
                cached = json.load(f)
            cached_time = datetime.fromisoformat(cached['timestamp'])
            if datetime.now() - cached_time > CACHE_EXPIRATION:
                return None
            return cached['data']
        except Exception as e:
            logger.warning(f"Cache error: {e}")
            return None
    
    def cache_data(self, cache_key, data):
        safe_cache_key = re.sub(r'[^a-zA-Z0-9_\-\.]', '_', cache_key)
        cache_file = CACHE_DIR / f"{safe_cache_key}.json"
        cached = {'timestamp': datetime.now().isoformat(), 'data': data}
        with open(cache_file, 'w') as f:
            json.dump(cached, f)
    
    def request(self, url, params=None, cache_key=None):
        if cache_key:
            cached_data = self.get_cached_data(cache_key)
            if cached_data:
                logger.info(f"Using cached data for {cache_key}")
                return cached_data
        
        max_retries = 5
        retry_delay = 1
        for attempt in range(max_retries):
            try:
                response = requests.get(url, params=params, headers=self.headers)
                if response.status_code == 403 and 'rate limit exceeded' in response.text.lower():
                    reset_time = int(response.headers.get('X-RateLimit-Reset', 0))
                    wait_time = max(reset_time - time.time(), 0) + 1
                    logger.warning(f"Rate limit exceeded. Waiting {wait_time:.1f} seconds...")
                    time.sleep(wait_time)
                    continue
                if response.status_code != 200:
                    # Check if 404/410/etc
                    if response.status_code == 404:
                         return None
                    
                    logger.error(f"API error: HTTP {response.status_code} - {response.text}")
                    if attempt < max_retries - 1:
                        wait_time = retry_delay * (2 ** attempt)
                        logger.info(f"Retrying in {wait_time} seconds... (Attempt {attempt+1}/{max_retries})")
                        time.sleep(wait_time)
                        continue
                    
                    response.raise_for_status()
                
                data = response.json()
                if cache_key:
                    self.cache_data(cache_key, data)
                
                # Log usage
                remaining = int(response.headers.get('X-RateLimit-Remaining', 1))
                if remaining < 10:
                    logger.warning(f"Only {remaining} API requests remaining.")
                    
                return data
            except requests.RequestException as e:
                logger.error(f"Request error: {e}")
                if attempt < max_retries - 1:
                    wait_time = retry_delay * (2 ** attempt)
                    logger.info(f"Retrying in {wait_time} seconds...")
                    time.sleep(wait_time)
                else:
                    raise
        raise Exception("Failed after multiple retries")

def get_repo_issues_in_range(github, repo_full_name):
    # Search API approach for better filtering and bulk retrieval
    base_url = "https://api.github.com/search/issues"
    # Basic query: repo and type
    base_query = f'repo:{repo_full_name} is:issue state:closed'
    
    # We chunk by date to avoid the 1000 items limit of Search API
    # Adjust range as needed. 
    # Let's go back 5 years or user configuration? 
    start_date = datetime(2018, 1, 1)
    end_date = datetime.now()
    chunk = timedelta(days=90) # 3 months per chunk
    
    current_start = start_date
    
    while current_start <= end_date:
        current_end = current_start + chunk
        if current_end > end_date:
            current_end = end_date
            
        date_range = f" created:{current_start.strftime('%Y-%m-%d')}..{current_end.strftime('%Y-%m-%d')}"
        query = base_query + date_range
        
        page = 1
        while True:
            # Cache key includes page and query
            cache_key = f"search_{repo_full_name}_{current_start.strftime('%Y%m%d')}_{page}"
            
            try:
                data = github.request(
                    base_url,
                    params={"q": query, "per_page": 100, "page": page},
                    cache_key=cache_key
                )
                
                items = data.get("items", [])
                if not items:
                    break
                    
                for item in items:
                    yield item
                
                if len(items) < 100:
                    break
                    
                page += 1
                # Small sleep to be nice
                if not github.get_cached_data(cache_key):
                    time.sleep(1)
                    
            except Exception as e:
                logger.error(f"Error fetching issues for {repo_full_name}: {e}")
                break
                
        current_start = current_end + timedelta(days=1)



if __name__ == "__main__":
    
    
    parser = argparse.ArgumentParser(
        description='Collect bug-triggering SMT formulas from solver bug trackers',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
Examples:
  # Collect formulas using a GitHub token and store in ./collected_formulas
  python collect.py --token YOUR_GITHUB_TOKEN --store ./collected_formulas
  # Collect formulas using token from environment variable
  python collect.py --store ./collected_formulas
            '''
        )
    
    parser.add_argument('--token', type=str, help='GitHub personal access token (or set GITHUB_TOKEN env variable)')
    parser.add_argument('--store', type=str, required=True, help='Directory to store collected formulas')

    args = parser.parse_args()
    auto_collect_buggy_formulas(args.token, args.store)





# if __name__ == "__main__":
#     import sys
#     import argparse
    
#     parser = argparse.ArgumentParser(
#         description='Determine the smallest SMT-LIB logic for a given formula',
#         formatter_class=argparse.RawDescriptionHelpFormatter,
#         epilog='''
# Examples:
#   # Detect logic from a .smt2 file
#   python smt_logic_detector.py formula.smt2
  
#   # Run test cases
#   python smt_logic_detector.py --test
  
#   # Process multiple files
#   python smt_logic_detector.py file1.smt2 file2.smt2 file3.smt2
#         '''
#     )
    
#     parser.add_argument('files', nargs='*', help='SMT2 files to analyze')
#     parser.add_argument('--test', action='store_true', help='Run test cases')
#     parser.add_argument('-v', '--verbose', action='store_true', help='Show detailed feature detection')
    
#     args = parser.parse_args()
    
#     if args.test:
#         test_logic_detection()
#     elif args.files:
#         for file_path in args.files:
#             try:
#                 detector = SMTLogicDetector()
#                 logic = detector.detect_from_file(file_path)
#                 print(f"{file_path}: {logic}")
#                 if args.verbose:
#                     print(f"  Features: {detector.features}")
#             except Exception as e:
#                 print(f"{file_path}: ERROR - {e}")
#     else:
#         parser.print_help()