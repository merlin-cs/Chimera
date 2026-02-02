from src.rewrite.mutate import Mutate, mimetic_mutation
from src.utils.file_handlers import get_all_smt_files_recursively as recursively_get_files
from src.rewrite.solver_runner import run_solver, record_bug
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

def fuzz(seeds, solver, solver_bin, temp_dir, modulo=2, max_iter=10, core=0, bug_type="common", mimetic=0):
    global MIMETIC_TIMES
    MIMETIC_TIMES = mimetic
    @exit_after(300)
    def fuzz_each_file(seed_file, solver, solver_bin, temp_dir, modulo=2, max_iter=10, core=0, bug_type="common"):
        """
        Fuzz a seed file using only mimetic mutation.
        """
        print("Fuzzing {}".format(seed_file))
        
        script_dir = "{}/script/core{}/{}/".format(temp_dir, str(core), seed_file.split('/')[-1].replace('.smt2', ''))
        if not os.path.exists(script_dir):
            os.makedirs(script_dir)
        initial_seed_filename = seed_file.split("/")[-1]
        soundness_flag = False
        completeness_flag = False
        performance_flag = False
        logic = None
        
        if logic is None:
            logic = "(set-logic ALL)"
        orig_file_path = seed_file

        # Create original copy
        original_smt2 = os.path.join(script_dir, "original.smt2")
        if not os.path.exists(original_smt2):
            shutil.copy(seed_file, original_smt2)

        # Get initial output
        temp_output = script_dir + "/temp.txt"
        orig_output, _, orig_time, command = run_solver(solver_bin, solver, seed_file, 10, "incremental", temp_output, temp_dir, "None", default=True)
        print("Original output: {}".format(orig_output))
        
        if orig_output == "timeout":
            pass
        
        # Current working file starts as the original seed
        current_file = seed_file
        
        for iter in range(max_iter):
            print(f"Iteration {iter + 1}/{max_iter}")
            
            # Perform mimetic mutation on current file
            mutant_path = script_dir + "/{}_mutant_{}.smt2".format(initial_seed_filename, str(iter))
            
            # Apply mimetic mutation
            mutation_flag = mimetic_mutation(current_file, mutant_path)
            
            if not mutation_flag:
                print(f"Mimetic mutation failed for iteration {iter}, using original file")
                shutil.copy(original_smt2, mutant_path)
            
            # Verify the mutant file was created and is valid
            if not os.path.exists(mutant_path):
                print(f"Mutant file not created for iteration {iter}, skipping")
                continue
            
            # Perform parsing check
            try:
                parse_cmd = ["/home/cvc5/build/bin/cvc5", mutant_path, "--parse-only", "-q"]
                process = subprocess.run(parse_cmd, capture_output=True, text=True, timeout=10)
                
                if "(error \"Parse Error:" in process.stderr or "(error \"Parse Error:" in process.stdout:
                    print(f"Parse error detected in iteration {iter}, skipping")
                    continue
            except subprocess.TimeoutExpired:
                print(f"Parse check timeout in iteration {iter}, skipping")
                continue
            except Exception as e:
                print(f"Parse check failed in iteration {iter}: {e}, skipping")
                continue
                
            previous_command = command
            applied_rules = f"Mimetic mutation applied to iteration {iter}"
            
            # Run solver on mutant
            if bug_type == "common":
                mutant_output, _, mutant_time, command = run_solver(solver_bin, solver, mutant_path, 10, "incremental", temp_output, temp_dir, "None", default=False, rules=applied_rules)
            else:
                if bug_type == "all":
                    default = True
                mutant_output, _, mutant_time, command = run_solver(solver_bin, solver, mutant_path, 10, "incremental", temp_output, temp_dir, "None", default, rules=applied_rules)
            
            print(f"Mutant output iteration {iter}: {mutant_output}")
            
            # Bug detection logic for "all" bug type
            if bug_type == "all":
                if mutant_time / orig_time > 10 or ("sat" in orig_output and mutant_output == "timeout"):
                    if not performance_flag:
                        performance_flag = True
                        record_bug(temp_dir, "performance", mutant_path, orig_file_path, solver, mutant_output, "", "", option=command + "\n" + previous_command, rules=applied_rules)
                if orig_time / mutant_time > 10 or (orig_output == "timeout" and "sat" in mutant_output):
                    if not performance_flag:
                        performance_flag = True
                        record_bug(temp_dir, "performance", mutant_path, orig_file_path, solver, mutant_output, "", "", option=command + "\n" + previous_command, rules=applied_rules)
                if ("unknown" not in orig_output and "unknown" in mutant_output) or ("unknown" in orig_output and "unknown" not in mutant_output): 
                    if orig_output not in ["parseerror", "error", "timeout"] and mutant_output not in ["parseerror", "error", "timeout"]:
                        if not completeness_flag:
                            completeness_flag = True
                            record_bug(temp_dir, "completeness", mutant_path, orig_file_path, solver, mutant_output, "", "", option=command + "\n" + previous_command, rules=applied_rules)
            
            # Soundness bug detection
            if mutant_output not in [orig_output, "crash", "parseerror", "timeout", "error"]:
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
            
            # Use the mutant as the seed for the next iteration
            current_file = mutant_path

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
                continue
            except Exception as e:
                print("Exception: {}".format(e))
                traceback.print_exc()
                with open(f"{temp_dir}/exception_core_{core}.txt", "w") as f:
                    f.write(str(e))
                    f.write(traceback.format_exc())
                continue
    except KeyboardInterrupt:
        print(f"Core {core}: KeyboardInterrupt in main loop")
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
    
    seed_dir = parsed_arguments["seed_dir"]
    solver = parsed_arguments["solver"]
    solver_bin = parsed_arguments["solver_bin"]
    temp_dir = parsed_arguments["temp_dir"]
    bug_type = parsed_arguments["bug_type"]
    
    seed_files = recursively_get_files(seed_dir, '.smt2')
    core_num = parsed_arguments["core_num"]
    random.shuffle(seed_files)
    
    # Split seed files into core_num parts
    seed_files = [seed_files[i::core_num] for i in range(core_num)]
    
    # Run core_num processes
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