# Experiment 03 — Python → big-step Maude (push it as far as we can)

**TLDR:** **Refocused 2026-04-26**. One target language (real Python), one CS522 framework (big-step / Kahn semantics), one implementation language (Maude). Push the Python subset as wide as possible with iterative add-feature → re-run-diff-harness cycles. Brando's directive: *"let's only try that all of python into big step and let's have it working in maude"*. Other CS522 frameworks (small-step, denotational, MSOS, RSEC, CHAM, K, λ) are **deferred** until the big-step v1 supports a meaningful Python subset end-to-end.

The previous "do all 8 frameworks at once" framing in earlier commits is superseded; that plan is preserved in `expt_v1/cc.md` as the historical record. The active plan is in `expt_v1/maude/` and grows feature-by-feature with each commit.

---

## 1. Goal

> *"Try to translate the real programming language using all the cs522 programming language semantics!"* — Brando, 2026-04-26

Concretely, this experiment answers the question Brando posed in `# veri-veri-bench` on 2026-04-26:

> "Just ask [Claude] to try to write the semantics of a real programming language and have it run for a few days … the only thing we would need is a set of tests or theorems or some way for us to check that the final semantics output is actually correct. … We could tell it to try every semantics framework. As long as we can verify it's right I don't care which framework it uses." — Brando

So this experiment must produce **two** things:

1. **The semantics itself** — Lean 4 modules under `Imp/Real/<Lang>/` defining the AST and one operational/denotational semantics per CS522 framework (8 frameworks total — see `expt_v1/frameworks_matrix.md`).
2. **A verification protocol** — a way for a human (Stepan) and an automated checker to decide whether each semantics is "right". Without this the long Claude run is a vibe-translation exercise. See `expt_v1/verification_spec.md`.

This is the difference between this experiment and Experiment 02: 02 handles toy IMP/IMP++ from the CS522 textbook; 03 scales to a *real* language (initial target: a Python subset; alternates: WebAssembly 1.0, Lua 5.1, MiniML). See `expt_v1/language_candidates.md`.

## 2. Structure

```
experiments/03_real_pl_all_semantics_in_lean/
├── README.md                          ← this file (goal, structure, method, deps, status)
├── cc.md                              ← conversational log / decisions ledger
└── expt_v1/                           ← first iteration
    ├── cc.md                          ← agent prompt (paste into Claude Code)
    ├── prompt.md                      ← canonical, self-contained prompt
    ├── language_candidates.md         ← real-PL targets we considered + recommendation
    ├── frameworks_matrix.md           ← 8 CS522 frameworks × language features
    ├── verification_spec.md           ← how we decide each semantics is "correct"
    ├── templates/                     ← per-framework Lean module skeletons
    │   └── README.md
    └── results/                       ← run outputs (timestamped summaries, plots, W&B link)
```

## 3. Method

The runnable plan lives in `expt_v1/prompt.md`. High-level shape:

1. **Pick the target.** Default: `pythonlite` — the smallest Python subset that still has functions, mutable lists/dicts, exceptions, and `import`. Fallback: WebAssembly 1.0 (already has a fully-formal reference spec we can diff against). See `expt_v1/language_candidates.md`.
2. **Define the AST once** (`Imp/Real/<Lang>/Syntax.lean`) so all 8 framework files share the same syntactic substrate.
3. **Instantiate every CS522 framework** in its own Lean file (`BigStep.lean`, `SmallStep.lean`, `Denotational.lean`, `MSOS.lean`, `RSEC.lean`, `CHAM.lean`, `K.lean`, `Lambda.lean`). One file = one judgment + the equivalence lemma to big-step (so all 8 are tied together).
4. **Verify.** For each framework, run the protocol in `verification_spec.md`:
   - **(a) Ground-truth differential testing** — run a fixed suite of source programs through (i) the language's reference interpreter (CPython / `wasmtime` / `lua5.1` / etc.) and (ii) a Lean executable extracted from each semantics; outputs must match.
   - **(b) Cross-framework equivalence theorems** — Lean proofs that Big-step ⇔ Small-step ⇔ Denotational ⇔ … on terminating programs (this is *the* Stepan-checkable mathematical guarantee).
   - **(c) Stepan + textbook spot-checks** — random sampling against Roșu's textbook rules (`cs522/ProgrammingLangSemantics.pdf`) for IMP-overlapping fragments.
5. **Report.** Per-framework PASS/FAIL counts, equivalence-theorem completion %, and a W&B Report URL. Save as `expt_v1/results/results_summary_<TS>.md`.

## 4. Dependencies

- **Prior work:**
  - `experiments/02_do_all_cs522_in_Lean/` — the IMP/IMP++ ports we build on. HW1 (big-step, small-step), HW2 (denotational), HW3 (IMP++ big-step + small-step), HW4 (MSOS, RSEC, CHAM) provide the patterns to reuse.
  - `experiments/00_aneas_does_pl_semantics/imp_semantics.md` — analysis of which frameworks our existing `Imp/main.lean` covers.
- **Repos / data:**
  - `~/cs522/` — Brando's Maude solutions; provides the Maude reference for any IMP-shaped subproblem.
  - `~/veri-veri-bench/cs522/ProgrammingLangSemantics.pdf` — Roșu textbook, the rule-set ground truth.
  - For each language candidate: a working reference interpreter (CPython 3.x, `wasmtime`, `lua5.1`, ML-of-OCaml).
- **Tools:** Lean 4 (`leanprover/lean4:v4.28.0`), Mathlib `v4.28.0`, Lake. Optionally `maude` (Docker) for K-framework cross-check.
- **Compute:** This is mostly a long-horizon Claude Code run. Brando's note: *"I have a lot of credits to run Claude or Claude 5.5"*. Budget: target ≤ 72 h of agent time per framework × language pair before falling back to a smaller scope. No GPU.
- **Credentials:** W&B (`~/keys/brandos_wandb_key.txt`).

## 5. Status — Python feature support (big-step Maude)

Each **cycle** is one new Python feature, end-to-end (syntax → parser → Maude rules → at least one new test in `expt_v1/maude/tests/` → diff-harness PASS).

| Cycle | Feature added                              | Status      | Diff-harness pass rate after cycle |
|-------|--------------------------------------------|-------------|-----------------------------------:|
| 0     | int, bool, +, -, *, //, %, comparisons, `and`/`or`/`not`, assign, `print`, `if`/`else`, `while` | Done | 7 / 7 |
| 1     | strings (literals, concat with `+`, `len`)  | Done        | (see latest `results_summary_*.md`) |
| 2     | lists (literal, indexing, `len`, `append`) | Done        | " |
| 3     | for-loop over `range(n)` / over list       | Done        | " |
| 4     | augmented assignment (`+=`, `-=`, `*=`)    | Done        | " |
| 5     | functions (`def`, `return`, positional args) | Done      | " |
| 6     | closures + recursion                        | Done        | " |
| 7     | exceptions (`raise`, `try` / `except`)     | Done        | " |
| 8     | tuples + multiple assignment                | Done        | " |
| 9+    | classes / dicts / generators                | TODO (v2)   | — |

(Status reflects the **end of this PR's commit chain**; per-cycle commit hashes are in `expt_v1/maude/results/cycles_log.md`.)

| External                                     | Status      | Notes |
|----------------------------------------------|-------------|-------|
| Stepan sign-off on `verification_spec.md`    | Pending     | requested in PR #7 thread |
| Stepan sign-off on big-step rule shapes      | Pending     | Stepan must be added as a repo collaborator first (Brando) |

## 6. Why this experiment matters (project context)

VeriBench (Stanford, OpenReview `rWkGFmnSNl`) shows that LLMs can vibe-translate Python into Lean — but a verified Lean proof only verifies the LLM's *interpretation* of the Python, not the original Python program. VeriBench-DT bolts on differential testing but still has no semantic equivalence in the kernel. Aeneas does Rust → Lean via a deterministic translator (LLBC), but the translator itself is not formally proven correct.

`veri-veri-bench` is the *inside-Lean* attempt: keep the AST and the operational semantics as Lean objects, prove source-to-Lean equivalence in the kernel. Experiment 03 is the first attempt to push that machinery past the toy CS522 IMP++ examples and onto something a developer would recognize as a real language. Doing it in *every* CS522 semantic framework gives us redundancy (cross-framework equivalence theorems are an extra check) and exercises the full toolbox CS522 teaches.

## 7. Notify

When the run completes (or partially completes), notify Stepan (`stepurik@stanford.edu`, CC `brandojazz@gmail.com` and `brando.science@gmail.com`) per the email template in `~/agents-config/workflows/expts-and-results.md` § Email Notification. Include the W&B Report URL and a per-framework PASS/FAIL table. Stepan's GitHub handle is not yet in `~/ultimate-utils/py_src/uutils/collaborators.py`; once it is, also @-mention him on the PR.
