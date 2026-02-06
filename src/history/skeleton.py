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


import random
import os

from src.parsing.Ast import Term, Expr
from src.parsing.Parse import parse_file
from src.parsing.Types import (
    NOT, AND, IMPLIES, OR, XOR, IFF
)
from src.utils.file_handlers import get_all_smt_files_recursively
from src.formula_utils import process_seed, get_basic_subterms, get_all_basic_subformula


def has_let(seed):
    file = open(seed, "r")
    content = file.readlines()
    for line in content:
        if "let " in line:
            return True
    return False


def construct_skeleton(seed, flag=False):
    """
    Dig holes in the formula
    :param flag:
    :param seed:
    :return:
    """
    s, g = process_seed(seed)
    if s is None:
        pass
    else:
        index = [0] * len(s.assert_cmd)
        basic_formula = get_all_basic_subformula(s, flag)
        for i in range(len(basic_formula)):
            basic_formula[i][0].substitute(basic_formula[i][0],
                                           Expr(op="hole " + str(index[basic_formula[i][1]]), subterms=[]))
            index[basic_formula[i][1]] += 1
    return s


def extract_skeleton(seed, skeleton_dic):
    """
    extract the skeletons from a seed and add them to dict
    :param seed:
    :param skeleton_dic:
    :return:
    """
    s = construct_skeleton(seed, flag=True)
    if s is not None:
        for i in range(len(s.assert_cmd)):
            skeleton = str(s.assert_cmd[i])
            if "let " not in skeleton:
                if skeleton_dic.get(skeleton) is None:
                    skeleton_dic[skeleton] = 1
                else:
                    count = skeleton_dic[skeleton]
                    skeleton_dic[skeleton] = count + 1
    return skeleton_dic
    # print(str(s.assert_cmd[i].term))


def _term_has_quantifier(term: Term) -> bool:
    """Recursively check if a Term tree contains any quantifier."""
    if isinstance(term, Term):
        if getattr(term, "quantifier", None) is not None:
            return True
        if term.subterms is not None:
            for s in term.subterms:
                if _term_has_quantifier(s):
                    return True
    return False


def export_skeleton(formula_path, skeleton_file):
    """Export skeletons, splitting quantifier-free vs quantified.

    - Writes quantifier-free skeletons to `skeleton_file` (backward compatible).
    - Writes quantified skeletons to `<stem>_quant.smt2` beside it.
    """
    qf_skeletons = dict()
    q_skeletons = dict()

    files = get_all_smt_files_recursively(formula_path)
    for file in files:
        s = construct_skeleton(file, flag=True)
        if s is None:
            continue
        for i in range(len(s.assert_cmd)):
            term = s.assert_cmd[i]
            sk = str(term)
            if "let " in sk:
                continue
            # Flatten the string to ensure it occupies a single line in the output file
            sk = sk.replace("\n", " ").replace("\r", " ")
            if _term_has_quantifier(term.term):
                q_skeletons[sk] = q_skeletons.get(sk, 0) + 1
            else:
                qf_skeletons[sk] = qf_skeletons.get(sk, 0) + 1

    # Prepare output paths
    if skeleton_file.endswith(".smt2"):
        quant_out = skeleton_file[:-5] + "_quant.smt2"
        qf_out = skeleton_file
    else:
        quant_out = skeleton_file + "_quant"
        qf_out = skeleton_file + "_qf"

    # Write QF skeletons to the original path for compatibility
    with open(qf_out, "w") as f_qf:
        f_qf.writelines([sk + "\n" for sk in qf_skeletons.keys()])
    restruct_skeleton(qf_out)

    # Write quantified skeletons to the suffixed path
    with open(quant_out, "w") as f_q:
        f_q.writelines([sk + "\n" for sk in q_skeletons.keys()])
    restruct_skeleton(quant_out)


def obtain_hole(skeleton):
    """

    :param skeleton: a ast that contains holes
    :return: a list of the holes the skeleton contain
    """
    hole_list = list()
    exprs, typ = get_basic_subterms(skeleton, 0)
    for hole in exprs:
        hole_list.append(hole[0])
    return hole_list


def obtain_local_domain(skeleton):
    local_domain = dict()
    initial_term = skeleton.term

    def recurrently_obtain_local(term, local_dic: dict):
        if isinstance(term, Term):
            if term.quantifier is not None:
                local_var = ""
                for v in term.quantified_vars[0]:
                    local_var += v + " "
                hole_list = list()
                for h in obtain_hole(term):
                    hole_list.append(str(h))
                if isinstance(local_var, str) and isinstance(local_dic, dict) and isinstance(hole_list, list):
                    local_dic[local_var] = hole_list
            if term.subterms is not None:
                for t in term.subterms:
                    local_dic = recurrently_obtain_local(t, local_dic)
            return local_dic

    return recurrently_obtain_local(initial_term, local_domain)


def obtain_skeleton_set(file_list):
    skeleton_set = set()
    for file in file_list:
        s = construct_skeleton(file, flag=True)
        if s is not None:
            for i in range(len(s.assert_cmd)):
                skeleton = str(s.assert_cmd[i])
                skeleton_set.add(skeleton)
    return skeleton_set


class Skeleton(object):
    def __init__(self, path_to_skeleton):
        if isinstance(path_to_skeleton, list):
            paths = path_to_skeleton
        else:
            paths = [path_to_skeleton]

        self.skeleton_list = []
        for path in paths:
            if os.path.exists(path):
                try:
                    script, global_var = parse_file(path)
                    if script and script.assert_cmd:
                        self.skeleton_list.extend(script.assert_cmd)
                except Exception as e:
                    print(f"Error parsing skeleton {path}: {e}")
        
        # self.SEED = random_seed
        # self.dynamic_skeleton_list = self.skeleton_list

    @staticmethod
    def random_choose_skeletons(skeleton_list):
        ast_count = 1
        ast_list = list()
        for i in range(ast_count):
            ast_list.append(random.choice(skeleton_list))
        return ast_list, ast_list

    @staticmethod
    def choose_skeleton_and_remove(skeleton_list, incremental):
        ast_list = list()
        if skeleton_list is not None and len(skeleton_list) > 5:
            ast_count = random.choice([1, 2, 3, 3, 4, 4, 5])
            if incremental == "incremental":
                ast_count = ast_count * random.choice([2, 3])
                if ast_count > len(skeleton_list):
                    ast_count = len(skeleton_list)
                if ast_count > 10:
                    ast_count = 10
            for i in range(ast_count):
                ast = random.choice(skeleton_list)
                ast_list.append(ast)
                skeleton_list.remove(ast)
            # return ast_list
        else:
            ast_list = skeleton_list
            skeleton_list = None

        return ast_list, skeleton_list


def restruct_skeleton(skeleton_path):
    new_content = []
    with open(skeleton_path, "r") as f:
        content = f.readlines()
    for line in content:
        index = 0
        local_count = dict()
        while line.count("VAR" + str(index) + " TYPE" + str(index)) > 0:
            if line.count("VAR" + str(index) + " TYPE" + str(index)) > 1:
                local_count["VAR" + str(index) + " TYPE" + str(index)] = line.count(
                    "VAR" + str(index) + " TYPE" + str(index))
            index += 1
        if len(list(local_count.keys())) > 0:
            # print(line)
            for k in local_count.keys():
                count = local_count[k]
                while count > 1:
                    line = line.replace(k, "VAR" + str(index) + " TYPE" + str(index), 1)
                    count -= 1
                    index += 1
            # print(line)
        new_content.append(line)
    with open(skeleton_path, "w") as f1:
        f1.writelines(new_content)
