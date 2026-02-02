from src.rewrite.mutate import Mutate, mimetic_mutation
from src.utils.file_handlers import get_all_smt_files_recursively as recursively_get_files
from src.config.generator_loader import GENERATORS

from src.run_solver import run_solver, record_bug
from src.rewrite.equality_saturation.helper import RewriteEGG, convert_to_IR, convert_IR_to_str, ALL_RULES
from src.parsing.Parse import parse_file
from src.parsing.TimeoutDecorator import exit_after

import traceback
import os
import random
import sys
import signal
import multiprocessing
import psutil
import shutil
import subprocess
import time
import argparse
from src.argument_parser.parser import MainArgumentParser

from src.parsing.Ast import CheckSat, Assert


GENERAL_THEORYS = [
    # "datatype",
    "fp",
    "int",
    "real",
    "core",
    "strings",
    "bv",
    "array",
    "reals_ints",
]

Z3_THEORYS = [
    "z3_seq",
    ]

CVC5_THEORYS = [
    "bag",
    "datatype",
    "ff",
    "seq",
    "set",
    "ho",
]

BITWUZLA_THEORYS = ["core", "fp", "bv", "array"]

def generator_wrapper(generator):
    gen_func = GENERATORS.get(generator)
    if gen_func:
        return gen_func()
    else:
        return None

def fuzz(seeds, solver, solver_bin, temp_dir, modulo=2, max_iter=10, core=0, bug_type="common", mimetic=0):
    global MIMETIC_TIMES
    MIMETIC_TIMES = mimetic
    @exit_after(300)
    def fuzz_each_file(seed_file, solver, solver_bin, temp_dir, modulo=2, max_iter=10, core=0, bug_type="common"):
        """
        Fuzz a seed file.
        """
        # output_list = []
        # (solver_path, solver, smt_file, timeout, incremental, output_path, temp, opt, default=False)
        print("Fuzzing {}".format(seed_file))
        # creat temp directory for each seed file
        # temp_dir = temp_dir + f"/{seed_file.split('/')[-1].replace('.smt2', '')}"
        script_dir = "{}/script/core{}/{}/".format(temp_dir, str(core), seed_file.split('/')[-1].replace('.smt2', ''))
        if not os.path.exists(script_dir):
            os.makedirs(script_dir)
        initial_seed_filename = seed_file.split("/")[-1]
        soundness_flag = False
        completeness_flag = False
        performance_flag = False
        # logic = get_logic(seed_file)
        logic = None
        # temp_output = "{}/script/core{}/temp.txt".format(temp_dir, str(core))
        # seed_output, _, seed_time, command = run_solver(solver_bin, solver, seed_file, 10, "incremental", temp_output, temp_dir, "None", default=True)
        # print("Seed output: {}".format(seed_output))
        if logic is None:
            logic = "(set-logic ALL)"
        orig_file_path = seed_file

        if MIMETIC_TIMES >= 0:
            original_smt2 = os.path.join(script_dir, "original.smt2")

            if not os.path.exists(original_smt2):
                shutil.copy(seed_file, original_smt2)

            for mimetic_iter in range(MIMETIC_TIMES):
                mutation_flag = mimetic_mutation(seed_file, original_smt2)
                # print("Mimetic mutation flag: {}".format(mutation_flag))
                if not mutation_flag:
                    seed_file = original_smt2
                    orig_file_path = seed_file
        # temp_output = "{}/script/core{}/temp.txt".format(temp_dir, str(core))
        temp_output = script_dir + "/temp.txt"
        orig_output, _, orig_time, command = run_solver(solver_bin, solver, seed_file, 10, "incremental", temp_output, temp_dir, "None", default=True)
        print("Original output: {}".format(orig_output))
        # with open(f"sat_sample_{core}.txt", "a") as f:
        #     f.write(f"initial: {seed_output}\nmimetic: {orig_output}\n")
        # return
        if orig_output == "timeout":
            # return None
            pass
        new_script = []
        
        for iter in range(max_iter):
            # rewrite_type = random.choice(["reverse", "egg"])
            rewrite_type = "egg"
            previous_command = command
            
            # Add retry mechanism for each iteration
            max_retries = 10
            retry_count = 0
            mutated_formula = None
            applied_rules = ""
            
            while retry_count < max_retries:
                mutated_formula = None # Reset for retry
                if rewrite_type == "egg":
                    TargetScript, TargetGlobal = parse_file(seed_file)
                    if TargetScript is None:
                        print("TargetScript is None")
                        return
                    current_ast = TargetScript.assert_cmd
                    if new_script == []:
                        for cmd in TargetScript.commands:
                            if isinstance(cmd, CheckSat) or "(exit)" in str(cmd):
                                # print("CheckSat")
                                pass
                            elif isinstance(cmd, Assert):
                                pass
                            else:
                                new_script.append(str(cmd))
                    replacee_terms = random.sample(TargetScript.op_occs, 3 if len(TargetScript.op_occs) > 3 else len(TargetScript.op_occs))
                    replace_pairs = []
                    attempts = 0
                    max_attempts = len(TargetScript.op_occs) * 2  # Allow more attempts than available terms

                    while len(replace_pairs) < 3 and attempts < max_attempts:
                        # If we've exhausted our initial sample, get more terms
                        if not replacee_terms:
                            remaining_terms = [term for term in TargetScript.op_occs 
                                            if not any(str(term) == pair[0] for pair in replace_pairs)]
                            if not remaining_terms:
                                break  # No more terms to try
                            replacee_terms = random.sample(remaining_terms, 
                                                        min(3, len(remaining_terms)))
                        
                        term = replacee_terms.pop(0)
                        attempts += 1
                        
                        term_ir = convert_to_IR(term)
                        term_str = str(term)
                        subterms = term.get_all_subterms()
                        sexpr = []
                        for subterm in subterms:
                            sexpr.append(str(subterm))
                        
                        transformed_irs = RewriteEGG(term_ir, ALL_RULES, sexpr, 1)
                        if transformed_irs is None or len(transformed_irs) == 0:
                            continue
                        
                        transformed_ir = transformed_irs[0]
                        new_term_str = convert_IR_to_str(transformed_ir)
                        
                        # Skip if transformation failed or resulted in the same term
                        if new_term_str is None or new_term_str == term_str:
                            continue
                        
                        # Additional validation to ensure the new term doesn't contain None or invalid content
                        if "None" in str(new_term_str) or new_term_str.strip() == "":
                            continue
                        
                        replace_pairs.append((term_str, new_term_str))

                    # Check if we have valid transformations
                    if replace_pairs:
                        current_ast_str = ""
                        for ast_cmd in current_ast:
                            current_ast_str += str(ast_cmd) + "\n"
                        for replace_pair in replace_pairs:
                            # Double-check that neither original nor replacement contains None
                            if "None" not in replace_pair[0] and "None" not in replace_pair[1]:
                                current_ast_str = current_ast_str.replace(replace_pair[0], replace_pair[1], 1)
                                applied_rules += "Original term is: {}\nRewritten term is: {}\n".format(replace_pair[0], replace_pair[1])

                        mutated_formula = "\n".join(new_script) + "\n" + current_ast_str + "\n(check-sat)"

                        # Check if the mutated formula contains None
                        if "None" in mutated_formula:
                            print(f"Mutated formula contains None, retrying... (attempt {retry_count + 1})")
                            mutated_formula = None
                            applied_rules = ""
                            retry_count += 1
                            continue

                        # Track new declarations added in this iteration
                        iteration_declarations = []

                        if "any_int" in mutated_formula:
                            # generate a random term
                            if random.choice(["int", "real"]) == "int":
                                def_candidate, term_candidate = GENERATORS["int"]()
                            else:
                                def_candidate, term_candidate = GENERATORS["real"]()
                            
                            # Handle list format for term_candidate
                            if isinstance(term_candidate, list):
                                term_candidate = "\n".join(term_candidate)
                            
                            # Replace "any_int" with the generated term
                            if term_candidate is not None:
                                mutated_formula = mutated_formula.replace("any_int", term_candidate)
                            
                            # Handle declarations properly
                            if isinstance(def_candidate, str):
                                def_candidate = def_candidate.strip().split("\n")
                            if isinstance(def_candidate, list):
                                # Filter out empty declarations and avoid duplicates
                                new_declarations = [
                                    decl for decl in def_candidate 
                                    if decl.strip() and decl.strip() not in mutated_formula
                                ]
                                if new_declarations:
                                    # Update `mutated_formula` to include the new declarations
                                    mutated_formula = "\n".join(new_declarations) + "\n" + mutated_formula
                                    # Track declarations for adding to new_script
                                    iteration_declarations.extend(new_declarations)
                            elif def_candidate is not None:
                                # Handle single declaration string
                                if def_candidate.strip() and def_candidate.strip() not in mutated_formula:
                                    mutated_formula = def_candidate + "\n" + mutated_formula
                                    iteration_declarations.append(def_candidate.strip())

                        if "any_bool" in mutated_formula:
                            # generate a random term
                            if "bitwuzla" == solver:
                                generator_types = BITWUZLA_THEORYS
                            elif solver == "z3":
                                generator_types = Z3_THEORYS + GENERAL_THEORYS
                            elif solver == "cvc5":
                                generator_types = CVC5_THEORYS + GENERAL_THEORYS
                            # generator_type = random.choice(generator_types)
                            generator_type = "int"
                            mutation_result = generator_wrapper(generator_type)
                            if mutation_result is None:
                                retry_count += 1
                                continue
                            def_candidate, term_candidate = mutation_result
                            
                            # Handle list format for term_candidate
                            if isinstance(term_candidate, list):
                                term_candidate = "\n".join(term_candidate)
                            
                            # Replace "any_bool" with the generated term
                            if term_candidate is not None:
                                mutated_formula = mutated_formula.replace("any_bool", term_candidate)
                            
                            # Handle declarations properly
                            if isinstance(def_candidate, str):
                                def_candidate = def_candidate.strip().split("\n")
                            if isinstance(def_candidate, list):
                                # Filter out empty declarations and avoid duplicates
                                new_declarations = [
                                    decl for decl in def_candidate 
                                    if decl.strip() and decl.strip() not in mutated_formula
                                ]
                                if new_declarations:
                                    # Update `mutated_formula` to include the new declarations
                                    mutated_formula = "\n".join(new_declarations) + "\n" + mutated_formula
                                    # Track declarations for adding to new_script
                                    iteration_declarations.extend(new_declarations)
                            elif def_candidate is not None:
                                # Handle single declaration string
                                if def_candidate.strip() and def_candidate.strip() not in mutated_formula:
                                    mutated_formula = def_candidate + "\n" + mutated_formula
                                    iteration_declarations.append(def_candidate.strip())

                        # Add new declarations to new_script for future iterations
                        if iteration_declarations:
                            # Filter out declarations that are already in new_script
                            unique_declarations = [
                                decl for decl in iteration_declarations 
                                if decl not in new_script
                            ]
                            # Add to the beginning of new_script to maintain proper order
                            new_script = unique_declarations + new_script

                    else:
                        # If no valid transformations found, retry
                        print(f"No valid transformations found, retrying... (attempt {retry_count + 1})")
                        retry_count += 1
                        continue
                
                if mutated_formula is None:
                    retry_count += 1
                    continue

                mutant_path = script_dir + "/{}_mutant_{}.smt2".format(initial_seed_filename, str(iter))
                with open(mutant_path, "w") as f:
                    f.write(mutated_formula)
                
                # Perform parsing check
                parse_cmd = ["/home/cvc5/build/bin/cvc5", mutant_path, "--parse-only", "-q"]
                process = subprocess.run(parse_cmd, capture_output=True, text=True, timeout=10)
                
                if "(error \"Parse Error:" in process.stderr or "(error \"Parse Error:" in process.stdout:
                    print(f"Parse error detected, retrying... (attempt {retry_count + 1})")
                    retry_count += 1
                    continue
                else:
                    # Generation successful
                    break

            # Check if mutated_formula is None after retries
            if mutated_formula is None:
                print(f"Failed to generate valid mutated formula after {max_retries} attempts, skipping iteration {iter}")
                continue
            
            mutant_path = script_dir + "/{}_mutant_{}.smt2".format(initial_seed_filename, str(iter))

                
            if bug_type == "common":
                mutant_output, _, mutant_time, command = run_solver(solver_bin, solver, mutant_path, 10, "incremental", temp_output, temp_dir, "None", default=False, rules=applied_rules)
            else:
                if bug_type == "all":
                    # default = "options"
                    default = True
                mutant_output, _, mutant_time, command = run_solver(solver_bin, solver, mutant_path, 10, "incremental", temp_output, temp_dir, "None", default, rules=applied_rules)
            # print("Mutant output: {}".format(mutant_output))
            if bug_type == "all":
                if mutant_time / orig_time > 10 or ("sat" in orig_output and mutant_output == "timeout"):
                    if not performance_flag:
                        performance_flag = True
                        record_bug(temp_dir, "performance", mutant_path, orig_file_path, solver, mutant_output, "", "", option=command + "\n" + previous_command, rules=applied_rules)
                if orig_time / mutant_time > 10 or (orig_output == "timeout" and "sat" in mutant_output ):
                    if not performance_flag:
                        performance_flag = True
                        record_bug(temp_dir, "performance", mutant_path, orig_file_path, solver, mutant_output, "", "", option=command + "\n" + previous_command, rules=applied_rules)
                if ("unknown" not in orig_output and "unknown" in mutant_output) or ("unknown" in orig_output and "unknown" not in mutant_output): 
                    if orig_output not in ["parseerror", "error", "timeout"] and mutant_output not in ["parseerror", "error", "timeout"]:
                        if not completeness_flag:
                            completeness_flag = True
                            record_bug(temp_dir, "completeness", mutant_path, orig_file_path, solver, mutant_output, "", "", option=command + "\n" + previous_command, rules=applied_rules)
            if mutant_output not in [orig_output, "crash", "parseerror", "timeout", "error"]:
                # record_bug(seed_file, mutated_formula, orig_output, mutant_output, orig_time, mutant_time)
                if isinstance(orig_output, list) and isinstance(mutant_output, list):
                    result_len = min(len(orig_output), len(mutant_output))
                    bug_found = False
                    for i in range(result_len):
                        if orig_output[i] != mutant_output[i] and orig_output[i] in ["sat", "unsat"] and mutant_output[i] in ["sat", "unsat"]:
                            bug_found = True
                            break
                    if bug_found and not soundness_flag:
                        soundness_flag = True
                        record_bug(temp_dir, "soundness", mutant_path, orig_file_path, solver, mutant_output, "", "", option=command + "\n" + previous_command, rules=applied_rules)
                            
            seed_file = mutant_path
            orig_file_path = mutant_path

    pro = None
    if not os.path.exists(temp_dir):
        os.makedirs(temp_dir)
    if not os.path.exists("{}/script".format(temp_dir)):
        os.mkdir("{}/script".format(temp_dir))
    if os.path.exists("{}/script/core{}".format(temp_dir, str(core))):
        os.system("rm -r {}/script/core{}".format(temp_dir, str(core)))
    os.mkdir("{}/script/core{}".format(temp_dir, str(core)))
    try:
        for seed in seeds:
            try:
                fuzz_each_file(seed, solver, solver_bin, temp_dir, modulo, max_iter, core, bug_type)
            except AssertionError:
                print("AssertionError")
                traceback.print_exc()
                continue
            except KeyboardInterrupt:
                print(f"Core {core}: KeyboardInterrupt in seed processing")
                # return
                continue
            except Exception as e:
                print("Exception: {}".format(e))
                traceback.print_exc()
                with open(f"{temp_dir}/exception_core_{core}.txt", "w") as f:
                    f.write(str(e))
                    f.write(traceback.format_exc())
                # raise SystemExit
                continue
    except KeyboardInterrupt:
        print(f"Core {core}: KeyboardInterrupt in main loop")
        # return
        pass
    

def get_logic(smt_file):
    with open(smt_file, "r") as f:
        lines = f.readlines()
    for line in lines:
        if line.startswith("(set-logic"):
            return line.split()[1][:-1]
    return None


def main():
    arguments = MainArgumentParser()
    arguments.parse_arguments(argparse.ArgumentParser())
    parsed_arguments = arguments.get_arguments()

    global MIMETIC_TIMES
    MIMETIC_TIMES = parsed_arguments["mimetic"]
    MIMETIC_TIMES = 0
    # seed_dir = "/home/benchmarks/non-incremental"
    # seed_dir = "/home/ET/tests/Bitvectors"
    # seed_dir = "/home/rewriter/oopsla"
    seed_dir = parsed_arguments["seed_dir"]
    # solver = parsed_arguments["solver"]
    # solver_bin = parsed_arguments["solverbin"]
    solver = parsed_arguments["solver"]
    solver_bin = parsed_arguments["solver_bin"]
    # temp_dir = "/root/pldi/coverage/aries/seed100"
    temp_dir = parsed_arguments["temp_dir"]
    # bug_type = "common"
    bug_type = parsed_arguments["bug_type"]
    # print("Fuzzing {}".format(seed_dir))
    seed_files = recursively_get_files(seed_dir, '.smt2')

    # seed_files = get_all_files_recursively(seed_dir)
    core_num = parsed_arguments["core_num"]
    random.shuffle(seed_files)
    # split seed files into core_num parts
    # seed_files = [seed_files[:10]]
    seed_files = [seed_files[i::core_num] for i in range(core_num)]
    # run core_num processes
    processes = []
    
    def signal_handler(signum, frame):
        print("\nReceived interrupt signal, terminating all processes...")
        for process in processes:
            if process.is_alive():
                print(f"Terminating process {process.pid}")
                process.terminate()
        
        # Wait a bit for graceful termination
        time.sleep(2)
        
        # Force kill any remaining processes
        for process in processes:
            if process.is_alive():
                print(f"Force killing process {process.pid}")
                process.kill()
        
        print("All processes terminated. Exiting...")
        sys.exit(0)
    
    # Set up signal handler for main process
    signal.signal(signal.SIGINT, signal_handler)
    
    try:
        for idx in range(core_num):
            print("Starting fuzzing core {}".format(idx))
            p = multiprocessing.Process(target=fuzz, args=(seed_files[idx], solver, solver_bin, temp_dir, 2, 10, idx, bug_type))
            processes.append(p)
            p.start()
        
        # Wait for all processes to complete
        for process in processes:
            process.join()
            
    except KeyboardInterrupt:
        print("\nMain process interrupted")
        signal_handler(signal.SIGINT, None)
        

if __name__ == "__main__":
    main()
    
