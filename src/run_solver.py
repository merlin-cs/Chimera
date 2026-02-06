"""
MIT License

Copyright (c) 2023 The histfuzz authors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"""


import subprocess
import os
import random
import shutil
import multiprocessing
import sys
import time




def record_bug(temp, bug_type, buggy_mutant_path1, buggy_mutant_path2, solver1=None, result1=None, solver2=None,
               result2=None, option=None, rules=None):
    """Record a detected bug to disk.

    Creates a numbered subdirectory under ``<temp>/<bug_type>/`` containing
    copies of the offending SMT files and an ``error_logs.txt`` summary.
    """
    temp_dir = temp
    os.makedirs(temp_dir, exist_ok=True)

    path_to_bug_folder = os.path.join(temp_dir, bug_type)
    os.makedirs(path_to_bug_folder, exist_ok=True)

    # Count existing sub-directories to derive the next index
    try:
        existing = next(os.walk(path_to_bug_folder))[1]
    except StopIteration:
        existing = []

    path_to_bug_dir = os.path.join(path_to_bug_folder, str(len(existing)))
    os.makedirs(path_to_bug_dir, exist_ok=True)

    # Copy relevant files
    for src in (buggy_mutant_path1, buggy_mutant_path2):
        if os.path.isfile(src):
            shutil.copy2(src, path_to_bug_dir)
        tactic_src = src.replace(".smt2", "_tactic.smt2")
        if os.path.isfile(tactic_src):
            shutil.copy2(tactic_src, path_to_bug_dir)

    # Build error log
    lines = [f"Bug type: {bug_type}\n"]
    if isinstance(result1, list):
        result1 = "".join(result1)
    if isinstance(result2, list):
        result2 = "".join(result2)
    if solver1 and result1:
        lines.append(f"{solver1} returned {result1}\n")
    if solver2 and result2:
        lines.append(f"{solver2} returned {result2}\n")
    if option is not None:
        lines.append(f"\nChosen option: {option}\n")
    if rules is not None:
        lines.append(f"\nTransformation:\n{rules}\n")

    log_path = os.path.join(path_to_bug_dir, "error_logs.txt")
    with open(log_path, "w", encoding="utf-8") as fh:
        fh.writelines(lines)


def _write_text(data: str, path: str) -> None:
    """Write *data* to *path* using a context manager."""
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(data)

def run_solver(solver_path, solver, smt_file, timeout, incremental, output_path, temp, opt, default=False, rules=None):
    temp_file = output_path
    if default is True:
        command = command_line(solver_path, solver, smt_file, timeout, incremental, temp_file)
    else:
        add_check_sat_using_flag = random.choice([False, True])
        if default == "options":
            add_check_sat_using_flag = False
        if add_check_sat_using_flag and solver == "z3":
            tactic = z3_tactic(smt_file)
            smt_file = tactic.add_check_sat_using()
        z3_opt, cvc5_option = add_option_to_command("ALL", "regular")
        command = command_line(solver_path, solver, smt_file, timeout, incremental, temp_file, z3_option=z3_opt,
                               cvc5_opt=cvc5_option)
    print(command)
    solver_output, error_msg, exe_time = creat_process_and_get_result(command, temp_file, incremental)
    if solver_output in ["nullpointer", "assertviolation", "segfault", "fatalfailure", "address error", "crash"]:
        record_bug(temp, "crash", smt_file, "", solver, solver_output, "", "", option=command, rules=rules)
        return "crash", error_msg, exe_time
    if os.path.isfile(temp_file):
        os.remove(temp_file)
    return solver_output, error_msg, exe_time, command

def solver_runner(solver1_path, solver2_path, smt_file, timeout, incremental, solver1, solver2,
                  theory, add_option, temp, tactic=None, base_solver1=None, base_solver2=None, target_bug=None):
    # Prepare temporary file names
    print(smt_file)
    if target_bug is not None:
        add_option = "default"
    temp_file_name1 = smt_file
    temp_file_name1 = temp_file_name1.replace(".smt2", "")
    temp_file_name2 = temp_file_name1 + "_output2.txt"
    temp_file_name1 += "_output1.txt"
    temp_file_path1 = temp_file_name1
    temp_file_path2 = temp_file_name2
    # Prepare SMT file names
    smt_file1 = smt_file
    smt_file2 = smt_file
    # If tactic is None, randomly add check-sat-using to the test instance for a Z3 solver
    if tactic is None and target_bug is None:
        add_check_sat_using_flag = random.choice([False, True])
        if add_check_sat_using_flag and solver1 == "z3":
            tactic = z3_tactic(smt_file1)
            smt_file1 = tactic.add_check_sat_using()
        if add_check_sat_using_flag and solver2 == "z3":
            tactic = z3_tactic(smt_file2)
            smt_file2 = tactic.add_check_sat_using()
    elif tactic is not None:
        # Otherwise, add the specific tactic to the SMT file of the corresponding solver
        if solver1 == "z3":
            smt_file1 = add_specific_tactic(smt_file1, tactic)
        if solver2 == "z3":
            smt_file2 = add_specific_tactic(smt_file2, tactic)
    # Prepare solver option notes and commands
    solver1_opt_note, solver2_opt_note = "", ""
    z3_opt, cvc5_option = add_option_to_command(theory, add_option)
    # Add solver options to the option notes of the corresponding solver
    if z3_opt is not None and solver1 == "z3":
        solver1_opt_note += z3_opt + "\n"
    if cvc5_option is not None and solver1 == "cvc5":
        solver1_opt_note += cvc5_option + "\n"
    # Prepare the command for the first solver
    command1 = command_line(solver1_path, solver1, smt_file1, timeout, incremental, temp_file_path1, z3_option=z3_opt,
                            cvc5_opt=cvc5_option, base=base_solver1)
    z3_opt, cvc5_option = add_option_to_command(theory, add_option)
    # Add solver options to the option notes of the corresponding solver
    if z3_opt is not None and solver2 == "z3":
        solver2_opt_note = z3_opt
    if cvc5_option is not None and solver2 == "cvc5":
        solver2_opt_note = cvc5_option
    # Prepare the command for the second solver
    command2 = command_line(solver2_path, solver2, smt_file2, timeout, incremental, temp_file_path2, z3_option=z3_opt,
                            cvc5_opt=cvc5_option, base=base_solver2)

    # Run the solvers and get their outputs
    solver_output1, error_msg1, exe_time1 = creat_process_and_get_result(command1, temp_file_path1, incremental)
    solver_output2, error_msg2, exe_time2 = creat_process_and_get_result(command2, temp_file_path2, incremental)
    print("solver_output1: ", solver_output1)
    print("solver_output2: ", solver_output2)
    # Check the solvers' outputs
    soundness, invalid_model, crash, invalid = check_result(solver_output1, solver_output2, solver1, solver2, smt_file1,
                                                   smt_file2, incremental, temp, error_msg1, error_msg2, solver1_opt_note, solver2_opt_note, exe_time1, exe_time2)
    if "_tactic" in smt_file1:
        os.remove(smt_file1)
    if "_tactic" in smt_file2:
        os.remove(smt_file2)
    if soundness or invalid_model or crash:
        return "bug"
    elif invalid:
        return "invalid"
    else:
        return False


def read_result(file_path, incremental):
    try:
        with open(file_path, 'r', encoding='utf-8', errors='replace') as f:
            lines = f.read().splitlines()
    except OSError:
        return "error"

    # Map of error substrings to result labels
    _ERROR_MAP = [
        ("Parse Error", "parseerror"),
        ("Segmentation fault", "segfault"),
        ("NullPointerException", "nullpointer"),
        ("invalid model", "invalid model"),
        ("ERRORS SATISFYING", "invalid model"),
        ("model doesn't satisfy", "invalid model"),
        ("ASSERTION VIOLATION", "assertviolation"),
        ("AssertionError", "assertviolation"),
        ("option parsing", "option error"),
        ("approximate values", "approximation"),
        ("failure", "failure"),
        ("error", "error"),
        ("unsupported reserved word", "error"),
    ]

    for line in lines:
        for needle, label in _ERROR_MAP:
            if needle in line:
                if os.path.isfile(file_path):
                    os.remove(file_path)
                return label

    # Incremental mode
    if incremental == "incremental":

        result_list = []
        for line in lines:
            result_list.append(line)
        os.remove(file_path)
        if result_list:
            return result_list
        else:
            return "timeout"
    else:

        if len(lines) > 0:
            if lines[0] == "sat" or lines[0] == "unsat" or lines[0] == "unknown":
                os.remove(file_path)
                return lines[0]
            else:
                os.remove(file_path)
                return "error"
        else:
            os.remove(file_path)
            return "timeout"


def check_result(result1, result2, solver1, solver2, bug_file1_path, bug_file2_path,
                 incremental, temp, message1, message2, solver1_opt=None, solver2_opt=None, exe_time1=None, exe_time2=None):
    crash_flag = False
    soundness_flag = False
    invalid_model_flag = False
    invalid_flag = False
    opt = ""
    if solver1_opt is not None:
        opt += "solver1-" + solver1 + ": "
        if solver1 == "z3":
            opt += "model_validate=true " + solver1_opt
        elif solver1 == "cvc5":
            opt += "-i --strings-exp --check-models " + solver1_opt
    if solver2_opt is not None:
        opt += "solver2-" + solver2 + ": "
        if solver2 == "z3":
            opt += "model_validate=true " + solver2_opt
        elif solver2 == "cvc5":
            opt += "-i --strings-exp --check-models " + solver2_opt
    # print("result1: ", result1, "\nresult2: ", result2)
    if result1 in ["timeout", "error", "parseerror", "option error"] and result2 in ["timeout", "error", "parseerror",
                                                                                     "option error"]:
        pass
    if result1 in ["error", "parseerror"]:
        invalid_flag = True
    if result2 in ["error", "parseerror"]:
        invalid_flag = True
    if result1 in ["nullpointer", "assertviolation", "segfault", "fatalfailure", "address error", "crash"]:
        record_bug(temp, "crash", bug_file1_path, bug_file2_path, solver1, result1, "", "", option=opt)
        crash_flag = True
    if result2 in ["nullpointer", "assertviolation", "segfault", "fatalfailure", "address error", "crash"]:
        record_bug(temp, "crash", bug_file1_path, bug_file2_path, "", "", solver2, result2, option=opt)
        crash_flag = True
    if result1 == "invalid model":
        record_bug(temp, "InvalidModel", bug_file1_path, bug_file2_path, solver1, result1, "", "",
                   option=opt)
        invalid_model_flag = True
    if result2 == "invalid model":
        record_bug(temp, "InvalidModel", bug_file1_path, bug_file2_path, "", "", solver2, result2,
                   option=opt)
        invalid_model_flag = True
    if result1 == "completeness":
        record_bug(temp, "completeness", bug_file1_path, bug_file2_path, solver1, result1, "",
                   "regression completeness", option=opt)
    if result2 == "completeness":
       record_bug(temp, "completeness", bug_file1_path, bug_file2_path, "", "regression completeness", solver2, result2,
                   option=opt)
    if result1 == "performance":
        record_bug(temp, "performance", bug_file1_path, bug_file2_path, solver1, result1, "",
                   "regression performance", option=opt)
    if result2 == "performance":
        record_bug(temp, "performance", bug_file1_path, bug_file2_path, "", "regression performance", solver2, result2,
                   option=opt)
    """
    if exe_time1 is not None and exe_time2 is not None:
        if exe_time1 >= exe_time2 * 10 or exe_time2 >= exe_time1 * 10:
            record_bug(temp, "performance", bug_file1_path, bug_file2_path, solver1, result1, solver2,
                       result2, option=opt)
    if result1 == "unknown" and result2 in ["sat", "unsat"]:
        record_bug(temp, "completeness", bug_file1_path, bug_file2_path, solver1, result1, solver2,
                   result2, option=opt)
    if result2 == "unknown" and result1 in ["sat", "unsat"]:
        record_bug(temp, "completeness", bug_file1_path, bug_file2_path, solver1, result1, solver2,
                   result2, option=opt)"""
    if (result1 in ["sat", "unsat"] and result2 in ["sat", "unsat"]) or (
            isinstance(result1, list) and isinstance(result2, list)):
        if solver1 == solver2 or check_special(bug_file1_path):
            if isinstance(result1, list) and isinstance(result2, list):
                result_count = len(result1)
                if result_count > len(result2):
                    result_count = len(result2)
                for idx in range(result_count):
                    if result1[idx] != result2[idx] and result1[idx] in ["sat", "unsat"] and result2[idx] in ["sat",
                                                                                                              "unsat"]:
                        record_bug(temp, "soundness", bug_file1_path, bug_file2_path, solver1, result1, solver2,
                                   result2, opt)
                        soundness_flag = True
                        break
            elif result1 != result2 and result1 in ["sat", "unsat"] and result2 in ["sat", "unsat"]:
                record_bug(temp, "soundness", bug_file1_path, bug_file2_path, solver1, result1, solver2, result2, opt)
                soundness_flag = True
    return soundness_flag, invalid_model_flag, crash_flag, invalid_flag


def command_line(solver_path, solver, smt_file, timeout, incremental, output_path, check_bug_type="model",
                 z3_option=None, cvc5_opt=None, base=None):
    """Build a solver command as a **list** of arguments (no shell needed).

    The ``timeout`` programme is invoked as the first element; all remaining
    elements are the solver binary and its flags.
    """
    cmd = ["timeout", str(timeout) + "s"]

    if solver in ("yices2", "boolector", "bitwuzla") and incremental == "incremental":
        cmd += [solver_path, "--incremental"]
    elif solver == "cvc5":
        cmd += [solver_path, "-q", "--strings-exp"]
        if incremental == "incremental":
            cmd.append("-i")
    else:
        cmd.append(solver_path)

    if solver == "yices2" and random.choice([True, False]):
        cmd.append("--mcsat")

    if check_bug_type == "model":
        if solver == "z3":
            cmd.append("model_validate=true")
        elif solver == "cvc5":
            cmd.append("--check-models")
        elif solver == "bitwuzla":
            cmd.append("--check-model")

    if z3_option and solver == "z3":
        # z3 options may contain multiple space-separated tokens
        cmd.extend(z3_option.split())
    if cvc5_opt and solver == "cvc5":
        cmd.extend(cvc5_opt.split())

    cmd.append(str(smt_file))

    # Redirect stdout to output_path (handled by caller via Popen stdout now,
    # but we keep the path in the list for backward compatibility logging).
    # The actual redirection is done in creat_process_and_get_result.
    return cmd


class z3_tactic:
    def __init__(self, exported_file_path):
        self.tactic_list = ["sat", "smt", "ctx-solver-simplify", "unit-subsume-simplify", "aig", "purify-arith", "fm",
                            "blast-term-ite", "ctx-simplify", "der", "elim-term-ite", "elim-uncnstr", "pb-preprocess",
                            "reduce-args", "nlsat", "nlqsat", "qe-light", "qe", "qsat", "qe2",
                            "simplify", "elim-and", "symmetry-reduce", "default", "cofactor-term-ite",
                            "special-relations", "fix-dl-var", "factor", "distribute-forall",
                            "solve-eqs", "dom-simplify", "sat-preprocess", "degree-shift", "injectivity", "snf", "nnf",
                            "occf", "sat-preprocess", "subpaving", "bit-blast", "propagate-values",
                            "reduce-invertible", "split-clause"]
        self.file = exported_file_path

    def _random_construct_tactic(self):
        tactic_count = random.randint(1, 3)
        tactics = ""
        if tactic_count == 1:
            tactics += random.choice(self.tactic_list)
        else:
            tactics += "(then"
            for i in range(tactic_count):
                tactics += " " + random.choice(self.tactic_list)
            tactics += ")"
        return tactics

    def add_check_sat_using(self):
        """Replace ``(check-sat)`` with ``(check-sat-using <tactic>)``."""
        check_sat_using_option = self._random_construct_tactic()

        try:
            with open(self.file, 'r', encoding='utf-8', errors='replace') as f:
                lines = f.read().splitlines()
        except OSError as exc:
            print(f"ERROR in check_sat_using: {exc}")
            return self.file

        for i in range(len(lines)):
            if "(check-sat)" in lines[i]:
                lines[i] = lines[i].replace(
                    "(check-sat)",
                    f"(check-sat-using {check_sat_using_option})",
                ) + "\n"
            else:
                lines[i] = lines[i] + "\n"

        new_file = self.file.replace(".smt2", "_tactic.smt2")
        with open(new_file, "w", encoding="utf-8") as fh:
            fh.writelines(lines)
        return new_file


def add_specific_tactic(file_path, tactics):
    try:
        with open(file_path, 'r', encoding='utf-8', errors='replace') as f:
            lines = f.read().splitlines()
    except OSError as exc:
        print(f"ERROR in add_specific_tactic: {exc}")
        return file_path

    for i in range(len(lines)):
        if "(check-sat)" in lines[i]:
            lines[i] = f"(check-sat-using {tactics})\n"
        else:
            lines[i] = lines[i] + "\n"

    new_file = file_path.replace(".smt2", "_tactic.smt2")
    with open(new_file, "w", encoding="utf-8") as fh:
        fh.writelines(lines)
    return new_file


def cvc5_candidate_option(theory, mode):
    # Common options (no value unless noted)
    common_options = [
        "check-proofs", "check-unsat-cores", 
        "decision", "full-saturate-quant",
        "proof-granularity", "random-seed"
    ]

    # Common options that require a value (example value ranges)
    common_options_with_value = {
        "dag-thresh": lambda: str(random.randint(1, 10)),
        "decision": lambda: random.choice(["justification", "stoponly"]),
        "decision-mode": lambda: random.choice(["justification", "stoponly"]),
        "expr-depth": lambda: str(random.randint(1, 10)),
        "filename": lambda: f"file{random.randint(1,100)}.smt2",
        "force-logic": lambda: random.choice(["QF_UF", "QF_LIA", "QF_BV"]),
        "input-language": lambda: random.choice(["smt2", "sygus2"]),
        "lang": lambda: random.choice(["smt2", "sygus2"]),
        "output": lambda: f"out{random.randint(1,100)}.txt",
        "output-lang": lambda: random.choice(["smt2", "sygus2"]),
        "output-language": lambda: random.choice(["smt2", "sygus2"]),
        "proof-granularity": lambda: random.choice(["rewrite", "theory-rewrite", "dsl-rewrite", "dsl-rewrite-strict"]),
        "random-seed": lambda: str(random.randint(0, 100000)),
        "reproducible-resource-limit": lambda: str(random.randint(1, 100)),
        "rlimit": lambda: str(random.randint(1, 10000)),
        "rlimit-per": lambda: str(random.randint(1, 10000)),
        "seed": lambda: str(random.randint(0, 100000)),
        "tlimit": lambda: str(random.randint(1, 10000)),
        "tlimit-per": lambda: str(random.randint(1, 10000)),
        "verbosity": lambda: str(random.randint(0, 4)),
    }

    # Regular options (with or without value)
    regular_options = [
        # Boolean flags (with --no- variant)
        "arith-brab", "arith-rewrite-equalities", "arith-static-learning", "arrays-eager-index",
        "bitwise-eq", "bv-eager-eval", "bv-print-consts-as-indexed-symbols", "bv-to-bool",
        "cbqi", "cbqi-all-conflict", "cegqi", "cegqi-bv", "cegqi-innermost", "check-abducts",
        "check-interpolants", "check-synth-sol", "dump-difficulty", 
        "dump-models", "dump-proofs", "dump-unsat-cores", "dump-unsat-cores-lemmas",
        "e-matching", "eager-arith-bv-conv", "elim-taut-quant", "enum-inst-interleave",
        "enum-inst-sum", "ext-rewrite-quant", "finite-model-find", "fmf-bound",
        "fresh-declarations", "global-declarations", "ho-elim", "ho-elim-store-ax",
        "inst-no-entail", "interactive-mode", "learned-rewrite", "mbqi", "mbqi-enum",
        "mbqi-one-inst-per-round", "miniscope-quant", "miniscope-quant-user", "multi-trigger-cache",
        "multi-trigger-linear", "multi-trigger-priority", "multi-trigger-when-single",
        "nl-ext-factor", "nl-ext-rewrite", "nl-ext-tf-tplanes", "nl-ext-tplanes",
        "nl-ext-tplanes-interleave", "pre-skolem-quant", "prenex-quant-user", "print-cores-full",
        "print-inst-full", "produce-abducts", "produce-assertions", "produce-assignments",
        "produce-difficulty", "produce-interpolants", "produce-learned-literals",
        "produce-unsat-assumptions", "quant-alpha-equiv", "relevant-triggers", "solve-real-as-int",
        "static-learning", "stats-every-query", "strings-check-entail-len", "strings-deq-ext",
        "strings-eager-eval", "strings-eager-len-re", "strings-eager-solver", "strings-exp",
        "strings-fmf", "strings-mbr", "strings-regexp-inclusion", "sygus", "sygus-add-const-grammar",
        "sygus-core-connective", "sygus-min-grammar", "sygus-pbe", "sygus-repair-const",
        "sygus-si-abort", "sygus-stream", "sygus-sym-break-pbe", "uf-lazy-ll", "uf-ss-fair",
        "user-pat", "var-elim-quant", "var-ineq-elim-quant",
        # Options with value
        "bitblast", "bool-to-bv", "bv-sat-solver", "bv-solver", "cbqi-mode", "cegis-sample",
        "ee-mode", "fmf-type-completion-thresh", "ieval", "inst-max-rounds", "inst-when",
        "interpolants-mode", "ite-lift-quant", "macros-quant-mode", "model-cores", "model-u-print",
        "nl-ext", "opt-res-reconstruction-size", "preregister-mode", "proof-rewrite-rcons-rec-limit",
        "proof-rewrite-rcons-step-limit", "prop-proof-mode", "quant-dsplit", "sat-random-seed",
        "simplification", "simplification-mode", "solve-bv-as-int", "solve-int-as-bv",
        "strings-process-loop-mode", "sygus-abort-size", "sygus-enum", "sygus-eval-unfold",
        "sygus-fair", "sygus-grammar-cons", "sygus-inst", "sygus-inv-templ", "sygus-out",
        "sygus-rewriter", "sygus-si", "sygus-si-rcons", "sygus-simple-sym-break", "sygus-unif-pi",
        "sygus-verify-timeout", "term-db-mode", "trigger-sel", "uf-ss", "uf-ss-abort-card"
    ]

    # Regular options with value (example values)
    regular_options_with_value = {
        "bitblast": lambda: "eager",
        "bool-to-bv": lambda: random.choice(["ite", "all"]),
        "bv-solver": lambda: "bitblast-internal",
        "cbqi-mode": lambda: "conflict",
        "cegis-sample": lambda: random.choice(["use", "trust"]),
        "ee-mode": lambda: "central",
        "fmf-type-completion-thresh": lambda: str(random.randint(1, 100)),
        "ieval": lambda: random.choice(["off", "use-learn"]),
        "inst-max-rounds": lambda: str(random.randint(1, 100)),
        "inst-when": lambda: random.choice([
            "full-delay", "full", "full-delay-last-call", "last-call"
        ]),
        "interpolants-mode": lambda: random.choice([
            "assumptions", "conjecture", "shared", "all"
        ]),
        "ite-lift-quant": lambda: "all",
        "macros-quant-mode": lambda: random.choice(["all", "ground"]),
        "model-cores": lambda: random.choice(["simple", "non-implied"]),
        "model-u-print": lambda: random.choice(["decl-sort-and-fun", "decl-fun", "dt"]),
        "nl-ext": lambda: random.choice(["none", "light"]),
        "opt-res-reconstruction-size": lambda: str(random.randint(1, 100)),
        "preregister-mode": lambda: "lazy",
        "proof-rewrite-rcons-rec-limit": lambda: str(random.randint(1, 100)),
        "proof-rewrite-rcons-step-limit": lambda: str(random.randint(1, 100)),
        "prop-proof-mode": lambda: "sat-external-prove",
        "quant-dsplit": lambda: random.choice(["none", "agg"]),
        "sat-random-seed": lambda: str(random.randint(0, 100000)),
        "simplification": lambda: "none",
        "simplification-mode": lambda: "none",
        "solve-bv-as-int": lambda: random.choice(["sum", "iand", "bv", "bitwise"]),
        "solve-int-as-bv": lambda: str(random.randint(1, 100)),
        "strings-process-loop-mode": lambda: random.choice([
            "simple", "simple-abort", "none", "abort"
        ]),
        "sygus-abort-size": lambda: str(random.randint(1, 100)),
        "sygus-enum": lambda: random.choice([
            "smart", "fast", "random", "var-agnostic"
        ]),
        "sygus-eval-unfold": lambda: random.choice([
            "none", "single", "multi"
        ]),
        "sygus-fair": lambda: random.choice([
            "direct", "dt-height-bound", "dt-size-bound", "none"
        ]),
        "sygus-grammar-cons": lambda: random.choice([
            "any-const", "any-term", "any-term-concise"
        ]),
        "sygus-inst": lambda: " ",  # No value, just the flag
        "sygus-inv-templ": lambda: random.choice(["none", "pre"]),
        "sygus-out": lambda: random.choice(["status", "status-and-def"]),
        "sygus-rewriter": lambda: random.choice(["none", "basic"]),
        "sygus-si": lambda: random.choice(["use", "all"]),
        "sygus-si-rcons": lambda: random.choice(["none", "try", "all-limit"]),
        "sygus-simple-sym-break": lambda: random.choice(["none", "basic"]),
        "sygus-unif-pi": lambda: random.choice(["complete", "cond-enum", "cond-enum-igain"]),
        "sygus-verify-timeout": lambda: str(random.randint(1, 10000)),
        "term-db-mode": lambda: "all",
        "trigger-sel": lambda: random.choice([
            "max", "min-s-max", "min-s-all", "all"
        ]),
        "uf-ss": lambda: random.choice(["no-minimal", "none"]),
        "uf-ss-abort-card": lambda: str(random.randint(-1, 100)),
    }

    def random_cvc5_options():
        # 1. Pick a random number of common options (possibly zero)
        n_common = random.randint(0, len(common_options))
        selected_common = random.sample(common_options, n_common)
        # Add value if needed
        opts = []
        for opt in selected_common:
            if opt in common_options_with_value:
                opts.append(f"--{opt}={common_options_with_value[opt]()}")
            else:
                opts.append(f"--{opt}")

        # 2. Pick at most one regular option (50% chance to include one)
        if random.choice([True, False]):
            reg_opt = random.choice(regular_options)
            if reg_opt in regular_options_with_value:
                opts.append(f"--{reg_opt}={regular_options_with_value[reg_opt]()}")
            elif reg_opt in [
                # Boolean regular options that support --no- variant
                "arith-brab", "arith-rewrite-equalities", "arith-static-learning", "arrays-eager-index",
                "bitwise-eq", "bv-eager-eval", "bv-print-consts-as-indexed-symbols", "bv-to-bool",
                "cbqi", "cbqi-all-conflict", "cegqi", "cegqi-bv", "cegqi-innermost", "check-abducts",
                "check-interpolants", "check-synth-sol", "dump-difficulty", 
                "dump-models", "dump-proofs", "dump-unsat-cores", "dump-unsat-cores-lemmas",
                "e-matching", "eager-arith-bv-conv", "elim-taut-quant", "enum-inst-interleave",
                "enum-inst-sum", "ext-rewrite-quant", "finite-model-find", "fmf-bound",
                "fresh-declarations", "global-declarations", "ho-elim", "ho-elim-store-ax",
                "inst-no-entail", "interactive-mode", "learned-rewrite", "mbqi", "mbqi-enum",
                "mbqi-one-inst-per-round", "miniscope-quant", "miniscope-quant-user", "multi-trigger-cache",
                "multi-trigger-linear", "multi-trigger-priority", "multi-trigger-when-single",
                "nl-ext-factor", "nl-ext-rewrite", "nl-ext-tf-tplanes", "nl-ext-tplanes",
                "nl-ext-tplanes-interleave", "pre-skolem-quant", "prenex-quant-user", "print-cores-full",
                "print-inst-full", "produce-abducts", "produce-assertions", "produce-assignments",
                "produce-difficulty", "produce-interpolants", "produce-learned-literals",
                "produce-unsat-assumptions", "quant-alpha-equiv", "relevant-triggers", "solve-real-as-int",
                "static-learning", "stats-every-query", "strings-check-entail-len", "strings-deq-ext",
                "strings-eager-eval", "strings-eager-len-re", "strings-eager-solver", "strings-exp",
                "strings-fmf", "strings-mbr", "strings-regexp-inclusion", "sygus", "sygus-add-const-grammar",
                "sygus-core-connective", "sygus-min-grammar", "sygus-pbe", "sygus-repair-const",
                "sygus-si-abort", "sygus-stream", "sygus-sym-break-pbe", "uf-lazy-ll", "uf-ss-fair",
                "user-pat", "var-elim-quant", "var-ineq-elim-quant"
            ]:
                # 50% chance to use --no-
                if random.choice([True, False]):
                    opts.append(f"--{reg_opt}")
                else:
                    opts.append(f"--no-{reg_opt}")
            else:
                opts.append(f"--{reg_opt}")

        return opts
    
    options = random_cvc5_options()
    return " ".join(options)


def z3_candidate_option(theory, mode):
    new_core = [" tactic.default_tactic=smt sat.euf=true "]
    regular_opt = [" rewriter.cache_all=true ", " rewriter.eq2ineq=true ",
                   " rewriter.hoist_mul=true ", " rewriter.pull_cheap_ite=true ",
                   " smt.bv.eq_axioms=false ", " rewriter.expand_nested_stores=true ",
                   " fp.xform.inline_eager=false ", " fp.xform.inline_linear_branch=true ", "rewriter.sort_sums=true",
                   " rewriter.arith_lhs=true ", " smt.bv.size_reduce=true "]
    if theory not in ["fp", "string"]:
        regular_opt += [" tactic.default_tactic=smt sat.euf=true ", " tactic.default_tactic=smt sat.euf=true ",
                        " tactic.default_tactic=smt sat.euf=true "]
    common_opt = [' pi.block_loop_patterns=false', ' pi.pull_quantifiers=false', ' pi.use_database=true',
                  ' pi.warnings=true', ' tactic.solve_eqs.context_solve=false', ' tactic.solve_eqs.ite_solver=false',
                  ' tactic.solve_eqs.theory_solver=false', ' pp.bounded=true', ' pp.bv_literals=false',
                  ' pp.bv_neg=true', ' pp.decimal=true', ' pp.fixed_indent=true', ' pp.flat_assoc=false',
                  ' pp.fp_real_literals=true', ' pp.pretty_proof=true', ' pp.simplify_implies=false',
                  ' pp.single_line=true', ' sat.abce=true', ' sat.acce=true', ' sat.anf=true', ' sat.anf.exlin=true',
                  ' sat.asymm_branch=false', ' sat.asymm_branch.all=true', ' sat.asymm_branch.sampled=false',
                  ' sat.ate=false', ' sat.bca=true', ' sat.bce=true', ' sat.binspr=true',
                  ' sat.branching.anti_exploration=true', ' sat.cardinality.solver=false', ' sat.cce=true',
                  ' sat.core.minimize=true', ' sat.core.minimize_partial=true', ' sat.cut=true', ' sat.cut.aig=true',
                  ' sat.cut.dont_cares=false', ' sat.cut.force=true', ' sat.cut.lut=true', ' sat.cut.npn3=true',
                  ' sat.cut.redundancies=false', ' sat.cut.xor=true', ' sat.dimacs.core=true',
                  ' sat.drat.activity=true', ' sat.drat.binary=true', ' sat.drat.check_sat=true',
                  ' sat.drat.check_unsat=true', ' sat.dyn_sub_res=false', ' sat.elim_vars=false',
                  ' sat.elim_vars_bdd=false', ' sat.enable_pre_simplify=true', ' sat.euf=true',
                  ' sat.force_cleanup=true', ' sat.gc.burst=true', ' sat.gc.defrag=false', ' sat.local_search=true',
                  ' sat.local_search_dbg_flips=true', ' sat.lookahead.double=false',
                  ' sat.lookahead.global_autarky=true', ' sat.lookahead.preselect=true',
                  ' sat.lookahead.use_learned=true', ' sat.lookahead_scores=true', ' sat.lookahead_simplify=true',
                  ' sat.lookahead_simplify.bca=false', ' sat.minimize_lemmas=false', ' sat.override_incremental=true',
                  ' sat.phase.sticky=false', ' sat.prob_search=true', ' sat.probing=false', ' sat.probing_binary=false',
                  ' sat.probing_cache=false', ' sat.propagate.prefetch=false', ' sat.restart.fast=false',
                  ' sat.retain_blocked_clauses=false', ' sat.scc=false', ' sat.scc.tr=false', ' sat.subsumption=false',
                  ' model.compact=false', ' model.completion=true', ' model.inline_def=true', ' model.partial=true',
                  ' model.v1=true', ' model.v2=true', ' opt.dump_benchmarks=true', ' opt.dump_models=true',
                  ' opt.elim_01=false', ' opt.enable_lns=true', ' opt.enable_sat=false', ' opt.enable_sls=true',
                  ' opt.maxlex.enable=false', ' opt.maxres.add_upper_bound_block=true', ' opt.maxres.hill_climb=false',
                  ' opt.maxres.maximize_assignment=true', ' opt.maxres.pivot_on_correction_set=false',
                  ' opt.maxres.wmax=true', ' opt.pb.compile_equality=true', ' opt.pp.neat=false', ' opt.pp.wcnf=true',
                  ' parallel.enable=true', ' nnf.ignore_labels=true', ' nnf.sk_hack=true',
                  ' model_evaluator.array_as_stores=false', ' model_evaluator.array_equalities=false',
                  ' model_evaluator.completion=true', ' rewriter.algebraic_number_evaluator=false',
                  ' rewriter.arith_ineq_lhs=true', ' rewriter.arith_lhs=true', ' rewriter.bit2bool=false',
                  ' rewriter.blast_distinct=true', ' rewriter.blast_eq_value=true', ' rewriter.blast_select_store=true',
                  ' rewriter.bv_extract_prop=true', ' rewriter.bv_ite2id=true', ' rewriter.bv_le_extra=true',
                  ' rewriter.bv_not_simpl=true', ' rewriter.bv_sort_ac=true', ' rewriter.cache_all=true',
                  ' rewriter.coalesce_chars=false', ' rewriter.elim_and=true', ' rewriter.elim_ite=false',
                  ' rewriter.elim_rem=true', ' rewriter.elim_sign_ext=false', ' rewriter.elim_to_real=true',
                  ' rewriter.eq2ineq=true', ' rewriter.expand_nested_stores=true', ' rewriter.expand_power=true',
                  ' rewriter.expand_select_ite=true', ' rewriter.expand_select_store=true',
                  ' rewriter.expand_store_eq=true', ' rewriter.expand_tan=true', ' rewriter.flat=false',
                  ' rewriter.gcd_rounding=true', ' rewriter.hi_div0=false', ' rewriter.hi_fp_unspecified=true',
                  ' rewriter.hoist_ite=true', ' rewriter.hoist_mul=true',
                  ' rewriter.ignore_patterns_on_ground_qbody=false', ' rewriter.ite_extra_rules=true',
                  ' rewriter.local_ctx=true', ' rewriter.mul2concat=true', ' rewriter.mul_to_power=true',
                  ' rewriter.pull_cheap_ite=true', ' rewriter.push_ite_arith=true', ' rewriter.push_ite_bv=true',
                  ' rewriter.push_to_real=false', ' rewriter.rewrite_patterns=true', ' rewriter.som=true',
                  ' rewriter.sort_store=true', ' rewriter.sort_sums=true', ' rewriter.split_concat_eq=true',
                  ' smt.arith.auto_config_simplex=true', ' smt.arith.bprop_on_pivoted_rows=false',
                  ' smt.arith.eager_eq_axioms=false', ' smt.arith.enable_hnf=false',
                  ' smt.arith.greatest_error_pivot=true', ' smt.arith.ignore_int=true', ' smt.arith.int_eq_branch=true',
                  ' smt.arith.min=true', ' smt.arith.nl=false', ' smt.arith.nl.branching=false',
                  ' smt.arith.nl.expp=true', ' smt.arith.nl.grobner=false', ' smt.arith.nl.horner=false',
                  ' smt.arith.nl.nra=false', ' smt.arith.nl.order=false', ' smt.arith.nl.tangents=false',
                  ' smt.arith.print_ext_var_names=true', ' smt.arith.print_stats=true',
                  ' smt.arith.propagate_eqs=false', ' smt.arith.random_initial_value=true',
                  ' smt.array.extensional=false', ' smt.array.weak=true', ' smt.auto_config=false',
                  ' smt.bv.delay=false', ' smt.bv.enable_int2bv=false', ' smt.bv.eq_axioms=false',
                  ' smt.bv.reflect=false', ' smt.bv.watch_diseq=true', ' smt.candidate_models=true',
                  ' smt.clause_proof=true', ' smt.core.extend_nonlocal_patterns=true', ' smt.core.extend_patterns=true',
                  ' smt.core.minimize=true', ' smt.dack.eq=true', ' smt.delay_units=true',
                  ' smt.ematching=false', ' smt.induction=true', ' smt.macro_finder=true', ' smt.mbqi=false',
                  ' smt.mbqi.trace=true', ' smt.pb.learn_complements=false', ' smt.pull_nested_quantifiers=true',
                  ' smt.qi.profile=true', ' smt.quasi_macros=true', ' smt.refine_inj_axioms=false',
                  ' smt.restricted_quasi_macros=true', ' smt.seq.split_w_len=false', ' smt.seq.validate=true',
                  ' smt.str.aggressive_length_testing=true', ' smt.str.aggressive_unroll_testing=false',
                  ' smt.str.aggressive_value_testing=true', ' smt.str.fast_length_tester_cache=true',
                  ' smt.str.fast_value_tester_cache=false', ' smt.str.fixed_length_naive_cex=false',
                  ' smt.str.fixed_length_refinement=true', ' smt.str.string_constant_cache=false',
                  ' smt.str.strong_arrangements=false', ' smt.theory_aware_branching=true',
                  ' smt.theory_case_split=true']

    if theory in ["real", "int"]:
        common_opt = common_opt + [' nlsat.check_lemmas=true', ' nlsat.factor=false', ' nlsat.inline_vars=true',
                                   ' nlsat.minimize_conflicts=true', ' nlsat.randomize=false',
                                   ' nlsat.reorder=false', ' nlsat.shuffle_vars=true',
                                   ' nlsat.simplify_conflicts=false']
    if theory not in ["fp", "string"]:
        common_opt = common_opt + new_core
    if mode == "regular":
        return regular_opt
    else:
        return common_opt


def add_option_to_command(theory, add_flag):
    if add_flag == "default":
        return None, None
    else:
        opt_count = random.choice([0, 1, 2])
        if opt_count == 1:
            z3_opt = random.choice(z3_candidate_option(theory, add_flag))
            # cvc5_option = random.choice(cvc5_candidate_option(theory, add_flag))
            cvc5_option = cvc5_candidate_option(theory, add_flag)
        elif opt_count == 2:
            z3_opt = random.choice(z3_candidate_option(theory, add_flag)) + \
                     random.choice(z3_candidate_option(theory, add_flag))
            cvc5_option = cvc5_candidate_option(theory, add_flag)
        else:
            z3_opt = " "
            cvc5_option = " "
        return z3_opt, cvc5_option


def creat_process_and_get_result(command, temp_file, incremental):
    """Run a solver command and return ``(output, stderr_text, elapsed_seconds)``.

    SECURITY: The command is split into a list and executed **without** a shell
    to prevent shell-injection attacks through crafted file paths or options.
    """
    # Accept both string and list forms; split strings safely via shlex.
    import shlex
    if isinstance(command, str):
        cmd_list = shlex.split(command)
    else:
        cmd_list = list(command)

    exe_time = None
    start_time = time.time()
    try:
        p = subprocess.Popen(
            cmd_list,
            shell=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        stdout_bytes, stderr_bytes = p.communicate()
    except FileNotFoundError:
        return "error", "solver binary not found", 0.0

    exe_time = time.time() - start_time
    terminal_output = stderr_bytes.decode(errors="replace")

    # Write stdout to the expected temp_file so read_result can process it.
    if stdout_bytes:
        try:
            with open(temp_file, "wb") as fh:
                fh.write(stdout_bytes)
        except OSError:
            pass

    solver_output = None
    # elif type(command) is list:
    #     # print(command[0])
    #     start_p1 = time.time()
    #     p1 = subprocess.Popen(command[0], stderr=subprocess.PIPE, shell=True)
    #     terminal_output = p1.stderr.read().decode()
    #     end_p1 = time.time()
    #     p1_time = end_p1 - start_p1
    #     # print(command[1])
    #     start_p2 = time.time()
    #     p2 = subprocess.Popen(command[1], stderr=subprocess.PIPE, shell=True)
    #     temp = p2.stderr.read().decode()
    #     end_p2 = time.time()
    #     p2_time = end_p2 - start_p2
    #     if p1_time >= 9 and p2_time < 5:
    #     # if p1_time >= p2_time * 100 or (p1_time >= 9 and p2_time < 5):
    #         solver_output = "performance"
    #     else:
    #         solver_output = None
    #         exe_time = p1_time
        
    # Process terminal output first before result parsing
    if check_crash(terminal_output) and ignore_crash(terminal_output):
        solver_output = "crash"
        if "Segmentation fault" not in terminal_output:
            err_info.append(terminal_output)
    if terminal_output.find("option parsing") != -1:
        solver_output = "option error"
    if terminal_output.find("approximate values") != -1:
        solver_output = "approximation"
    if terminal_output.find("invalid model") != -1 or terminal_output.find("ERRORS SATISFYING") != -1 or terminal_output.find("model doesn't satisfy") != -1:
        solver_output = "invalid model"
    if terminal_output.find("Error") != -1 and solver_output is None:
        solver_output = "error"
    if solver_output is None:
        # if type(command) is str:
        solver_output = read_result(temp_file, incremental)
        # elif type(command) is list:
        #     temp_output1 = read_result(temp_file, incremental)
        #     temp_output2 = read_result(temp_file, incremental)
        #     # if temp_output1 == "unknown" and temp_output2 in ["sat", "unsat"]:
        #     if temp_output1 == "unknown":
        #         solver_output = "completeness"
        #     else:
        #         solver_output = temp_output1
    return solver_output, terminal_output, exe_time


def save_valid_file_for_differential_test(solver1_path, solver2_path, solver3_path, solver1, solver2, solver3, smt_file,
                                          to):
    temp_file_name = smt_file
    temp_file_name = temp_file_name.replace(".smt2", "_output.txt")
    temp_file_path = temp_file_name
    command1 = command_line(solver1_path, solver1, smt_file, to, "no", temp_file_path)
    command2 = command_line(solver2_path, solver2, smt_file, to, "no", temp_file_path)
    command3 = command_line(solver3_path, solver3, smt_file, to, "no", temp_file_path)

    result1 = creat_process_and_get_result(command1, temp_file_path, "no")
    result2 = creat_process_and_get_result(command2, temp_file_path, "no")
    result3 = creat_process_and_get_result(command3, temp_file_path, "no")

    file_score = 0
    if result1 in ["sat", "unsat", "unknown"]:
        file_score += 1
    if result2 in ["sat", "unsat", "unknown"]:
        file_score += 1
    if result3 in ["sat", "unsat", "unknown"]:
        file_score += 1
    print(command2)
    print(command3)
    print("result1: ", result1, "result2: ", result2, "result3: ", result3)
    if file_score >= 2:
        return smt_file
    else:
        return None


def check_special(buggy_file):
    with open(buggy_file, "r", encoding="utf-8", errors="replace") as f:
        content = f.read()
    return "^" not in content



def check_crash(output: str):
    crash_list = ["Exception", "lang.AssertionError", "lang.Error", "runtime error", "LEAKED", "Leaked",
                  "Segmentation fault", "segmentation fault", "segfault", "ASSERTION", "Assertion", "Fatal failure",
                  "Internal error detected", "an invalid model was generated", "Failed to verify", "failed to verify",
                  "ERROR: AddressSanitizer:", "invalid expression", "Aborted", "AddressSanitizer",
                  "NULL pointer was dereferenced", "ast_manager LEAKED"]
    for c in crash_list:
        if output.find(c) != -1:
            return True
    return False


def ignore_crash(output: str):
    for i in err_info:
        if output.find(i) != -1:
            return False
    return True


def extract_assistant_contents(text):
    """Extract SMT-LIB content from assistant-formatted text."""
    new_text = text[text.find("> Assistant: ") + len("> Assistant: "):]
    new_text = new_text.replace("==================================", "")
    lines = new_text.split("\n")
    new_lines = []
    for line in lines:
        stripped = line.strip()
        if stripped.startswith(("(set-option", "(set-info")):
            continue
        if stripped.startswith(("(set", "(declare", "(define", "(assert", "(check-sat")):
            new_lines.append(line)
    new_lines.append("\n(check-sat)")
    return "\n".join(new_lines).strip()


# Re-export from utils for backward compatibility
from src.utils.file_handlers import get_txt_files_list as get_all_txt_files_recursively


# err_info = ["floatingpoint_literal_symfpu_traits.cpp", "Unimplemented code encountered", "pb_solver.cpp", "pb_constraint.cpp", "bzlafp.cpp:728", "bzlafp.cpp:1891", "smt2_term_parser.cpp"]
err_info = ["floatingpoint_literal_symfpu_traits.cpp", "string.cpp", "theory_model.cpp"]

