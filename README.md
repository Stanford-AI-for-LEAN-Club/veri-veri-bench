# veri-veri-bench (`imp`)

> A Lean 4 formalization of PL operational semantics, built up from a toy imperative language (IMP, CS522 style) as a stepping stone toward a fully formal, AI-assisted semantic compiler for a real programming language.

## Project Goal

**Can AI help us write the formal proof system / PL semantics — the "s-piler" (semantics compiler) — for a real, full programming language, and can we actually trust the result?**

### Hypothesis

It is too hard for humans alone to write a formal PL semantics for a real-world programming language. The machinery involved — big-step, small-step, denotational, CHAM, and K-framework operational semantics — is the kind of thing CS522 teaches, but essentially nobody has finished the job for a production language. People stop at toy languages and publish about how nice it would be. So we leverage AI to scale the work, while keeping a small independently-checkable kernel (Lean) as the root of trust.

### Plan

1. **Master the toy case first.** Work through CS522's IMP (a small imperative language) in every semantic style — big-step, small-step, denotational, CHAM, K-framework — in Maude (the course's language) *and* in Lean 4, so we fully understand what writing PL semantics actually looks like.
2. **Formalize IMP in Lean 4.** This repo defines IMP as an abstract syntax tree in Lean, proves a big-step `terminate` inductive relation + determinism + halting/output lemmas, and ships a recursive-descent parser from strings. See `Imp/`.
3. **Extend to a real language.** Once we understand the problem on the toy language, we design AI agents that write PL semantics for languages people actually use (Python, Rust, C).

## Why this project exists (vs. VariBench and Aeneas)

**VariBench** vibe-translates source programs (e.g. Python) to Lean via an LLM. Problem: nothing *formal* connects the resulting Lean file to the original program. A verified Lean proof only verifies the LLM's interpretation, which can hallucinate. What got verified is a mathematical model of the code, not the code itself.

**VariBench-DT** layers differential testing on top of the LLM translation. This is useful, but still relies on test coverage rather than semantic equivalence — it catches bugs, not all bugs.

**Aeneas** (Rust → Lean toolchain) uses its own big-step-style semantics (LLBC) and emits Lean functional code. Its translator is a deterministic program, which is better than an LLM, but the translator itself is not formally proven correct: the output is a Lean program, not a proof-carrying AST equipped with defined operational semantics that you can reason about.

**veri-veri-bench** builds the *inside-Lean* compiler. We parse source into a Lean AST, define operational semantics (big-step / small-step / denotational / CHAM / K) as Lean inductive relations, and state and prove source-to-Lean equivalence *inside Lean*. The translation step is itself a formal object. No LLM in the hot path, no vibe translation, no leap of faith — just a chain of definitions and theorems the Lean kernel (≈8k lines) checks.

That is where the project's name comes from: *very, very* bench.

## Repository layout

- `Imp/main.lean` — core AST (`Aexp`, `Bexp`, `Com`), big-step `terminate` inductive relation, determinism (`terminate_unique`), halting/output lemmas
- `Imp/parser.lean` — tokenizer and recursive-descent parser for IMP programs from strings
- `Imp/example.lean` — example IMP program with halting and output proofs
- `Imp/SEMANTICS.md` — narrative overview of the semantic rules
- `Imp.lean` — top-level import (currently stale — imports the missing `Imp.Basic`; see Build section)
- `cs522/` — CS522 course materials (PDF of *Programming Language Semantics* by Grigore Roșu, plus HW1–HW6 Maude specs and the Extra-Credit assignment). Used as the ground-truth source for what needs to be translated into Lean under `Imp/`.
- `experiments/` — experiment-per-folder workspace for multi-step tasks (e.g. `02_do_all_cs522_in_Lean/`)

## CS522 translation roadmap (active work)

We are porting each CS522 homework from Maude into Lean, one PR at a time, in order:

- **HW1** — Exercises 56 & 70: division-by-zero *error* states in big-step and small-step semantics
- **HW2** — denotational semantics + CPO
- **HW3** — IMP++ (extended language)
- **HW4** — IMP_PP
- **HW5, HW6, Extra-Credit** — additional CS522 topics (threads, locals, type systems, etc.)

Each PR is reviewed via a 3-stage mega QA chain (Claude Code → Codex → Gemini CLI) before merge. See `experiments/02_do_all_cs522_in_Lean/prompt.md` for the full workflow.

## Build

Current status: `lake build` does **not** succeed on this checkout because `Imp.lean` still imports the missing module `Imp.Basic`. Fixing that stale import is one of the first items on the CS522 port.

```bash
lake build                 # currently fails — stale `Imp.Basic` import in Imp.lean
lake env lean --version    # verify pinned Lean toolchain via Lake
```

## Toolchain

- **Lean**: `leanprover/lean4:v4.28.0`
- **Mathlib**: `v4.28.0`
- **Lake project name**: `imp`

## Related projects

- `~/cs522` — Brando's completed CS522 Maude homework submissions (HW1–HW4). This repo's `cs522/` folder holds the course PDF + HW specs; the ported Lean versions live under `Imp/`.
- [Lean Club]([https://github.com/StanfordLeanClub]) — the Stanford group driving this project and VariBench.
