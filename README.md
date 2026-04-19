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
- Snake-egg for equality saturation
- SMT solvers to test (e.g., [Z3](https://github.com/Z3Prover/z3), [cvc5](https://github.com/cvc5/cvc5))

### Setup

```bash
git clone https://github.com/merlin-cs/Chimera.git
cd Chimera
pip install -r requirements.txt 
```
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
  --solver1-name z3 \
  --solver2-name cvc5 \
  --solver1-bin /path/to/z3 \
  --solver2-bin /path/to/cvc5 \
  --seed-dir ./seeds
```


### History-based Fuzzing (HistFuzz Mode)

Use historical bug-triggering cases to guide the synthesis of new formulas.

```bash
python -m chimera.chimera_cli \
  --mode histfuzz \
  --solver1-name z3 \
  --solver2-name cvc5 \
  --solver1-bin /path/to/z3 \
  --solver2-bin /path/to/cvc5 \
  --seed-dir ./bug_triggering_formulas
```


### Rewrite-based Validation (Aries Mode)

Mimetic mutation combined with equality saturation for rewrite rule exploration.

```bash
python -m chimera.chimera_cli \
  --mode aries \
  --solver1-name z3 \
  --solver2-name cvc5 \
  --solver1-bin /path/to/z3 \
  --solver2-bin /path/to/cvc5 \
  --seed-dir ./seeds \
  --rules-csv ./RewriteRule.csv
```


---

## Citing Chimera

If you use Chimera in your research, please cite the following papers:

```bibtex
@inproceedings{sun2026asplos,
  author       = {Maolin Sun and
                  Yibiao Yang and
                  Yuming Zhou},
  editor       = {Benjamin C. Lee and
                  Harry Xu and
                  Mark Silberstein and
                  Bingyao Li},
  title        = {Once4All: Skeleton-Guided {SMT} Solver Fuzzing with LLM-Synthesized
                  Generators},
  booktitle    = {Proceedings of the 31st {ACM} International Conference on Architectural
                  Support for Programming Languages and Operating Systems, Volume 2,
                  {ASPLOS} 2026, Pittsburgh, PA, USA, March 22-26, 2026},
  pages        = {1316--1332},
  publisher    = {{ACM}},
  year         = {2026},
  url          = {https://doi.org/10.1145/3779212.3790195},
  doi          = {10.1145/3779212.3790195},
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
