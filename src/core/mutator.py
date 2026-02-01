import random
from src.parsing.Parse import parse_file
from src.formula_utils import get_all_basic_subformula

# def formula_mutation(smt_file):
#     with open(smt_file, "r") as f:
#         text = f.read()
#     try:
#         script, glob = parse_file(smt_file, silent=True)
#         expr_list = get_all_basic_subformula(script, rename_flag=True)
#         if len(expr_list) == 0:
#             return text, text
#         else:
#             original_text = text
#             placeholder = random.sample(expr_list, random.randint(1, len(expr_list)))
#             new_text = text
#             assert_text = ""
#             for assert_cmd in script.assert_cmd:
#                 assert_text += assert_cmd.__str__() + "\n"
#             new_assert_text = assert_text
#             for ph in placeholder:
#                 if " " + ph[0].__str__() + " " in new_assert_text:
#                     new_assert_text = new_assert_text.replace(" " + ph[0].__str__() + " ", " <placeholder> ", 1)
#                 elif " " + ph[0].__str__() + ")" in new_assert_text:
#                     new_assert_text = new_assert_text.replace(" " + ph[0].__str__() + ")", " <placeholder>)", 1)
#                 elif "(" + ph[0].__str__() + " " in new_assert_text:
#                     new_assert_text = new_assert_text.replace("(" + ph[0].__str__() + " ", "(<placeholder> ", 1)
#             new_text = new_text.replace(assert_text.strip(), new_assert_text.strip())
#             return original_text, new_text
#     except Exception as e:
#         # print(e)
#         return text, text
