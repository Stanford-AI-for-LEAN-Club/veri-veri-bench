# Claude Code: read `~/agents-config/INDEX_RULES.md` for all agent documentation and routing.

## Project Overview

**veri-veri-bench** (`imp`) is a Lean 4 formalization of the IMP programming language — a simple imperative language used in programming language theory. The project includes:

- **AST definitions**: arithmetic expressions (`Aexp`), boolean expressions (`Bexp`), and commands (`Com`)
- **Big-step operational semantics**: a `terminate` inductive relation, determinism (`terminate_unique`), and halting/output reasoning
- **Parser & tokenizer**: recursive-descent parser for IMP programs from string input
- **Example proofs**: a summation program with termination and output correctness theorems

## Build / Run

Current status: `lake build` does **not** succeed in this checkout because
`~/veri-veri-bench/Imp.lean` still imports the missing module `Imp.Basic`.

```bash
lake build          # currently fails due to the stale `Imp.Basic` import in `Imp.lean`
lake env lean --version # verify the pinned Lean toolchain via Lake
```

## Key Entry Points

- `Imp/main.lean` — core AST, semantics, and theorems (`Aexp`, `Bexp`, `Com`, `terminate`, equivalence lemmas)
- `Imp/parser.lean` — tokenizer and recursive-descent parser
- `Imp/example.lean` — example IMP program with halting and output proofs
- `Imp.lean` — top-level import file; currently stale because it imports missing `Imp.Basic`

## Toolchain

- **Lean**: `leanprover/lean4:v4.28.0`
- **Mathlib**: `v4.28.0`
- Lake project name: `imp`
