
class MainArgumentParser(object):

    def __init__(self):
        self.parsed_arguments = dict()
        self.solverbin1 = None
        self.solverbin2 = None
        self.solver1 = None
        self.solver2 = None
        self.option = None
        self.bugs = None
        self.processes = None
        self.timeout = None
        self.iterations = None

    def parse_arguments(self, parser):

        parser.add_argument("--bugs", help="the directory of the historical bug-triggers, e.g. /home/bugs")
        parser.add_argument("--solverbin1", help="path to the first solver bin.\n"
                                                 "Note that: if only one solver provided, soundness bugs will be missed. "
                                                 "Only invalid model bugs and crashes can be found.")
        parser.add_argument("--solver1", help="the first solver name e.g. z3, cvc5.\n"
                                              "Note that: if only one solver provided, soundness bugs will be missed. "
                                              "Only invalid model bugs and crashes can be found.")
        parser.add_argument("--solverbin2", help="path to the second solver bin")
        parser.add_argument("--solver2", help=" the second solver name e.g. z3, cvc5")
        parser.add_argument("--option", type=str, choices=["default", "regular", "comprehensive"],
                            help=" the tested options of Z3 and cvc5. \n"
                                 "default: the default mode of solvers \n"
                                 "regular: some common options \n "
                                 "comprehensive: almost all the options (enable with caution)")
        parser.add_argument("--processes", "-p", type=int, default=None,
                            help="number of parallel processes (default: number of CPU cores)")
        parser.add_argument("--timeout", "-t", type=int, default=10,
                            help="timeout in seconds for each solver invocation (default: 10)")
        parser.add_argument("--iterations", "-i", type=int, default=10,
                            help="number of mutation iterations per seed file (default: 10)")
        parser.add_argument("--standalone", action="store_true",
                            help="run in standalone mode without seed files")
        parser.add_argument("--generator_path", type=str, default=None,
                            help="path to custom generators")
        parser.add_argument("--temp", type=str, default="./temp/",
                            help="directory for temporary files")
        arguments = vars(parser.parse_args())

        self.solverbin1 = arguments["solverbin1"]
        self.solverbin2 = arguments["solverbin2"]
        self.solver1 = arguments["solver1"]
        self.solver2 = arguments["solver2"]
        self.bugs = arguments["bugs"]
        self.option = arguments["option"] if arguments["option"] is not None else "default"
        self.processes = arguments["processes"]
        self.timeout = arguments["timeout"]
        self.iterations = arguments["iterations"]
        self.standalone = arguments["standalone"]
        self.generator_path = arguments["generator_path"]
        self.temp = arguments["temp"]

    def get_arguments(self):

        self.parsed_arguments["solverbin1"] = self.solverbin1
        self.parsed_arguments["solverbin2"] = self.solverbin2
        self.parsed_arguments["solver1"] = self.solver1
        self.parsed_arguments["solver2"] = self.solver2
        self.parsed_arguments["bugs"] = self.bugs
        self.parsed_arguments["option"] = self.option
        self.parsed_arguments["processes"] = self.processes
        self.parsed_arguments["timeout"] = self.timeout
        self.parsed_arguments["iterations"] = self.iterations

        return self.parsed_arguments
