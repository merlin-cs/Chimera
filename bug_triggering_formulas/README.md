## Overview

This is a tool implemented to collect, standardize, and classify bug-triggering SMT formulas from solver issue trackers. 
It provides a streamlined process for extracting and organizing SMT formulas, making them ready for further analysis and use in fuzzing or testing scenarios.


## Usage

### Collecting Bug-Triggering Formulas

Run the `collect.py` script to collect SMT formulas from solver issue trackers:

```bash
python bug_triggering_formulas/collect.py --token YOUR_GITHUB_TOKEN --store ./collected_formulas
```

- `--token`: (Optional) Your GitHub personal access token. If not provided, the `GITHUB_TOKEN` environment variable will be used.
- `--store`: (Required) Directory where collected formulas will be stored.

### Examples

1. Using a GitHub token:
   ```bash
   python bug_triggering_formulas/collect.py --token YOUR_GITHUB_TOKEN --store ./collected_formulas
   ```

2. Without a GitHub token (uses `GITHUB_TOKEN` environment variable):
   ```bash
   python bug_triggering_formulas/collect.py --store ./collected_formulas
   ```


## Acknowledgments

- [Z3Prover](https://github.com/Z3Prover/z3)
- [cvc5](https://github.com/cvc5/cvc5)
- [Yices2](https://github.com/SRI-CSL/yices2)
- [OpenSMT](https://github.com/usi-verification-and-security/opensmt)

