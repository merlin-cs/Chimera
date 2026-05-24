# generators/

LLM-synthesized SMT-LIB2 formula generators for the Once4All fuzzing engine.

## Layout

```
generators/
├── construct.py              # LLM pipeline: doc → CFG → generator → corrected generator
├── general/                  # Cross-solver generators (both Z3 and cvc5)
│   ├── docs/                 #   Theory reference docs used as LLM prompts
│   └── *_generator.py        #   Generated Python modules
├── cvc5/                     # cvc5-specific generators
│   ├── docs/
│   └── *_generator.py
└── z3/                       # Z3-specific generators
    ├── docs/
    └── *_generator.py
```

## Generator modules

Each `*_generator.py` exports a single function:

```python
generate_<theory>_formula_with_decls() -> (declarations_str, formula_str)
```

- `declarations_str` — SMT-LIB2 `declare-fun`/`declare-const` commands
- `formula_str` — a single Boolean term (no `assert`/`check-sat`/`set-logic`)

The Once4All engine discovers and loads these modules at runtime via
`chimera/config/generator_loader.py` and `chimera/engines/once4all_engine.py`.

## Constructing new generators

Use `construct.py` to synthesize a new generator from a theory doc:

```bash
python generators/construct.py \
    --doc-file generators/general/docs/Ints.txt \
    --theory-name "Ints" --theory-abbrev "ints" \
    --backend gemini \
    --solvers /usr/local/bin/z3 /usr/local/bin/cvc5 \
    --output generators/general/ints_generator.py
```

The pipeline:
1. Summarizes the theory doc into a CFG (LLM call)
2. Generates a Python module from the CFG (LLM call)
3. Self-corrects using solver feedback (iterative LLM calls)

Supported LLM backends: `openai`, `anthropic`, `deepseek`, `gemini`, `qwen`.

## Adding a new theory

1. Add a reference doc to the appropriate `docs/` subdirectory
2. Run `construct.py` with the doc to generate the module
3. Save the output as `<theory>_generator.py` in the same subdirectory
