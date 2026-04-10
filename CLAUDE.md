# Claude Code: read `~/agents-config/INDEX_RULES.md` for all agent documentation and routing.
# If `~/agents-config/` is not present, clone it: `git clone https://github.com/brando90/agents-config.git ~/agents-config`

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

---

## Mandatory Post-Experiment Protocol

**TRIGGER:** Any time you finish running a script that produces metrics, model outputs, or evaluation results. This fires AUTOMATICALLY — do not skip any step.

1. **W&B Report** — Push metrics AND create a W&B Report (not just a run). Print the Report URL. See `~/agents-config/workflows/expts-and-results.md` for the API template. A logged run alone is NOT sufficient.
2. **Local results summary** — Save to `results_summary/results_summary_<YYYY-MM-DD__HH-MM-SS>.md` with TL;DR, config table, results table, plots, W&B link.
3. **QA gating** — Dispatch cross-agent QA per Hard Rule 3 in `~/agents-config/INDEX_RULES.md` before telling the user "done."
4. **GPU cleanup** — Kill zombie processes, verify GPUs freed, report `nvidia-smi`.
5. **TLDR** — End your response with `**TLDR:**` (1-2 sentences).

## Mandatory Response Protocol (ALL responses)

These apply to EVERY response, not just experiment completion.

- Every response ends with `**TLDR:**` — no exceptions.
- When a non-trivial task completes, run QA gating before reporting done.
- When unsure whether QA gating applies, run it.
