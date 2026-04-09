[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

<p align="center">
  <img src="./logo.png" alt="Chimera logo" width="120" />
</p>

# Chimera

Chimera is an integrated toolkit for testing, validating, and exploring SMT solvers.  
It brings together techniques from three publications:

1. **Once4All: Skeleton-Guided SMT Solver Fuzzing with LLM-Synthesized Generators**  
   Maolin Sun, Yibiao Yang, Yuming Zhou  
   *ASPLOS 2026*

2. **Validating SMT Rewriters via Rewrite Space Exploration Supported by Generative Equality Saturation**  
   Maolin Sun, Yibiao Yang, Jiangchang Wu, Yuming Zhou  
   *OOPSLA 2025*

3. **Validating SMT Solvers via Skeleton Enumeration Empowered by Historical Bug-Triggering Inputs**  
   Maolin Sun, Yibiao Yang, Ming Wen, Yongcong Wang, Yuming Zhou, Hai Jin  
   *ICSE 2023*

Chimera unifies these lines of work into a single framework for  Discovering bugs in SMT solvers.


---

## Table of Contents

- [Installation](#installation)
- [Usage](#usage)
  - [LLM-based Fuzzing](#llm-based-fuzzing-once4all-mode)
  - [History-based Fuzzing](#history-based-fuzzing-histfuzz-mode)
  - [Rewrite-based Validation](#rewrite-based-validation-aries-mode)
  - [Common Arguments](#common-arguments)
- [Citing Chimera](#citing-chimera)
- [Contributing](#contribution)
- [License](#license)

---


## Installation

### Prerequisites

- Python 3.8+
- [ANTLR4 Python3 Runtime](https://pypi.org/project/antlr4-python3-runtime/) (Recommended version: 4.7.2 or compatible with generated parsers)
- SMT solvers to test (e.g., [Z3](https://github.com/Z3Prover/z3), [cvc5](https://github.com/cvc5/cvc5))

### Setup

```bash
git clone https://github.com/merlin-cs/Chimera.git
cd Chimera
pip install -r requirements.txt  # If available, or install dependencies manually
```

*Note: If you encounter ANTLR4 version mismatches, ensure your `antlr4-python3-runtime` matches the version used to generate the parser.*

---

## Usage

Chimera can be run via the installed command or as a Python module:

```bash
# After installation (pip install -e .)
chimera --mode histfuzz --solver1-bin /path/to/z3 --solver2-bin /path/to/cvc5 ...

# Or run directly
python -m chimera.chimera_cli --mode histfuzz --solver1-bin /path/to/z3 --solver2-bin /path/to/cvc5 ...
```

### LLM-based Fuzzing (Once4All Mode)

This mode uses LLM-synthesized generators to produce formulas.

```bash
python -m chimera.chimera_cli \
  --mode once4all \
  --solver1-bin /path/to/z3 \
  --solver2-bin /path/to/cvc5 \
  --seed-dir ./seeds
```


### History-based Fuzzing (HistFuzz Mode)

Use historical bug-triggering cases to guide the synthesis of new formulas.

```bash
python -m chimera.chimera_cli \
  --mode histfuzz \
  --solver1-bin /path/to/z3 \
  --solver2-bin /path/to/cvc5 \
  --seed-dir ./bug_triggering_formulas
```


### Rewrite-based Validation (Aries Mode)

Mimetic mutation combined with equality saturation for rewrite rule exploration.

```bash
python -m chimera.chimera_cli \
  --mode aries \
  --solver1-bin /path/to/z3 \
  --solver2-bin /path/to/cvc5 \
  --seed-dir ./seeds \
  --rules-csv ./RewriteRule.csv
```

### Common Arguments

- `--mode`: Fuzzing strategy (`histfuzz`, `once4all`, `aries`).
- `--solver1-name` / `--solver2-name`: Solver names (default: z3, cvc5).
- `--solver1-bin` / `--solver2-bin`: Paths to solver binaries (required).
- `--solver-timeout`: Timeout in seconds for each solver invocation (default: 10s).
- `--iterations`: Maximum number of test iterations (0 = unlimited).
- `--output-dir`: Directory for bug artifacts.
- `--seed-dir`: Directory with seed .smt2 files.
- `-v` / `--verbose`: Enable debug logging.


---

## Citing Chimera

If you use Chimera in your research, please cite the following papers:

```bibtex
@article{DBLP:journals/corr/abs-2508-20340,
  author       = {Maolin Sun and
                  Yibiao Yang and
                  Yuming Zhou},
  title        = {Boosting Skeleton-Driven {SMT} Solver Fuzzing by Leveraging {LLM}
                  to Produce Formula Generators},
  journal      = {CoRR},
  volume       = {abs/2508.20340},
  year         = {2025},
  url          = {https://doi.org/10.48550/arXiv.2508.20340},
  doi          = {10.48550/ARXIV.2508.20340},
  eprinttype    = {arXiv},
  eprint       = {2508.20340}
}


@article{sun2025oopsla,
author = {Sun, Maolin and Yang, Yibiao and Wu, Jiangchang and Zhou, Yuming},
title = {Validating SMT Rewriters via Rewrite Space Exploration Supported by Generative Equality Saturation},
year = {2025},
issue_date = {October 2025},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
volume = {9},
number = {OOPSLA2},
url = {https://doi.org/10.1145/3763093},
doi = {10.1145/3763093},
journal = {Proc. ACM Program. Lang.},
month = oct,
articleno = {315},
numpages = {27}
}

@inproceedings{sun2023icse,
  author       = {Maolin Sun and
                  Yibiao Yang and
                  Ming Wen and
                  Yongcong Wang and
                  Yuming Zhou and
                  Hai Jin},
  title        = {Validating {SMT} Solvers via Skeleton Enumeration Empowered by Historical
                  Bug-Triggering Inputs},
  booktitle    = {45th {IEEE/ACM} International Conference on Software Engineering,
                  {ICSE} 2023, Melbourne, Australia, May 14-20, 2023},
  pages        = {69--81},
  publisher    = {{IEEE}},
  year         = {2023},
  url          = {https://doi.org/10.1109/ICSE48619.2023.00018},
  doi          = {10.1109/ICSE48619.2023.00018}
}
```

---

## Contribution

We welcome contributions! Please open an issue or submit a pull request for improvements, bug fixes, or new features.

---

## License

Chimera is released under the MIT License.
