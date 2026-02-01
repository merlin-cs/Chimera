ALARM_TIME = 60
MAX_ITERATIONS = 10
SAMPLE_SIZE = 3
OPTIMIZATION_THRESHOLD = 3
STOP_THRESHOLD = 5
MAX_INDEX = 1000
DEFAULT_TIMEOUT = 10
DEFAULT_INCREMENTAL = "incremental"
DEFAULT_THEORY = "all"
DEFAULT_ADD_OPTION = "default"
DEFAULT_STANDALONE_ITERATIONS = 1000
TEMP_DIRECTORY = "./temp/"
CORRECTION_THRESHOLD = 0
CHECKER_PATH = "/home/cvc5-Linux"

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
    "trans",  # transcendentals (newly added)
    "sep",    # separation logic (newly added)
]

BITWUZLA_THEORYS = ["core", "fp", "bv", "array"]
