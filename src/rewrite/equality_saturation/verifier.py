from pathlib import Path
import csv
import os
from snake_egg import EGraph, Rewrite, Var, vars

current_dir = Path(__file__).parent.absolute()
current_parent_dir = current_dir.parent.parent.absolute()

os.sys.path.append(str(current_parent_dir))

from src.parsing.Parse import parse_file, parse_str
from src.parsing.Ast import Const, Script, Term, Var, DeclareFun
from src.parsing.Types import BITVECTOR_TYPE
from src.rewrite.solver_runner import run_solver
from src.rewrite.equality_saturation.helper import ARITH_RULES, BV_RULES, STRING_RULES, CORE_RULES

def parse_csv(file_path):
    with open(file_path, newline='') as csvfile:
        reader = csv.DictReader(csvfile)
        return [row for row in reader]


RULES = parse_csv(str(current_parent_dir) + '/res/RewriteRule.csv')


def instantiate_rule(rule):
    smt2_str = ""

    if ";" in rule:
        contents = rule.split(";")
        # Loop through the contents of the target format
        for idx, content in enumerate(contents):
            if idx == 0:
                # If it's the first content, add it to the smt2_str with an assert command
                ast = content
                smt2_str += "(assert " + ast + ")"
            else:
                # Otherwise, declare a function with the content and add it to the smt2_str
                declare_cmd = "(declare-fun " + content.split(":")[0] + " () " + content.split(":")[1] + ")"
                smt2_str = declare_cmd + "\n" + smt2_str
    else:
        if rule.startswith(":"):
            smt2_str = "(assert \"\")"
        else: 
            contents = rule.split(":")
            smt2_str = "(assert " + contents[0] + ")"
        # Loop through the contents of the target format
        
    # Parse the smt2_str
    s, g = parse_str(smt2_str)
    return s, g


def verify_rule(rule, output):
    lhs_script, lhs_goal = instantiate_rule(rule['Original'])
    rhs_script, rhs_goal = instantiate_rule(rule['Target'])
    new_cmds = []
    for cmd in lhs_script.commands:
        if isinstance(cmd, DeclareFun) and str(cmd) not in new_cmds:
            new_cmds.append(str(cmd))

    for cmd in rhs_script.commands:
        if isinstance(cmd, DeclareFun) and str(cmd) not in new_cmds:
            new_cmds.append(str(cmd))

    new_assert = f"(assert (not (= {lhs_script.assert_cmd[0].term} {rhs_script.assert_cmd[0].term})))"
    new_cmds.append(new_assert)
    with open(output, 'w') as f:
        f.write("(set-logic ALL)\n")
        for cmd in new_cmds:
            f.write(str(cmd) + "\n")
        f.write("(check-sat)\n")
        f.write("(exit)\n")

def convert_class_to_smt2(rule_set, output):
    new_cmds = []
    for rule in rule_set:
        # print the attributes of the rule
        # print(dir(rule))
        print(rule.left)
        break
        # print(rule)
    # for rule in rule_set:
    #     lhs_script, lhs_goal = instantiate_rule(rule['Original'])
    #     rhs_script, rhs_goal = instantiate_rule(rule['Target'])
    #     for cmd in lhs_script.commands:
    #         if isinstance(cmd, DeclareFun) and str(cmd) not in new_cmds:
    #             new_cmds.append(str(cmd))

    #     for cmd in rhs_script.commands:
    #         if isinstance(cmd, DeclareFun) and str(cmd) not in new_cmds:
    #             new_cmds.append(str(cmd))

    #     new_assert = f"(assert (not (= {lhs_script.assert_cmd[0].term} {rhs_script.assert_cmd[0].term})))"
    #     new_cmds.append(new_assert)
    # with open(output, 'w') as f:
    #     f.write("(set-logic ALL)\n")
    #     for cmd in new_cmds:
    #         f.write(str(cmd) + "\n")
    #     f.write("(check-sat)\n")
    #     f.write("(exit)\n")

def transform_csv_to_rewrites(csv_file_path):
    rewrites = []
    with open(csv_file_path, 'r') as csvfile:
        reader = csv.DictReader(csvfile)
        for idx, row in enumerate(reader):
            try:
                print(f"Processing row {idx}...")
                original_field = row['Original']
                target_field = row['Target']
                condition_field = row.get('Condition', '').strip()

                # Parse original expression and variables
                original_parts = original_field.strip().split(';')
                original_expr = original_parts[0].strip()
                variables = {}
                for var in original_parts[1:]:
                    if var:
                        var_name, var_type = var.strip().split(':')
                        variables[var_name.strip()] = var_type.strip()

                # Parse target expression
                target_parts = target_field.strip().split(';')
                target_expr = target_parts[0].strip()

                # Map variables to placeholders (a, b, c, ...)
                var_mapping = {}
                for i, var_name in enumerate(variables.keys()):
                    var_mapping[var_name] = chr(ord('a') + i)

                # Replace variables in expressions
                for var_name, mapped_name in var_mapping.items():
                    original_expr = original_expr.replace(var_name, mapped_name)
                    target_expr = target_expr.replace(var_name, mapped_name)

                # Generate rule name (e.g., "mod-1")
                rule_name = f"rule-{idx}"

                rewrite = Rewrite(original_expr, target_expr, rule_name)
                rewrites.append(rewrite)
            except Exception as e:
                print(f"Error processing row: {row}")
                print(e)
                
    return rewrites


if __name__ == "__main__":
    transform_csv_to_rewrites("/Users/merlin/Documents/GitHub/ewriter-validation/res/RewriteRule.csv")
    # for idx, rule in enumerate(RULES):
    #     if idx < 230:
    #         continue

    #     verify_rule(rule, f'rule{idx}.smt2')
    #     SOLVER = 'z3'
    #     SOLVER_BIN = '/home/z3/build/z3'

    #     solver_output, _, _, _ = run_solver(SOLVER_BIN, SOLVER, f'rule{idx}.smt2', 30, "incremental", 'temp.txt', current_dir, "None", default=True)
    #     if "unsat" in solver_output:
    #         # print(f"Rule {idx} is valid")
    #         # pass
    #         os.remove(f'rule{idx}.smt2')
    #     else:
    #         if idx in [4, 9, 10]:
    #             pass
    #         else:
    #             print(f"Rule {idx} is invalid")
    #             print(f"LHS: {rule['Original']}\nRHS: {rule['Target']}\n")
    #             break
        
