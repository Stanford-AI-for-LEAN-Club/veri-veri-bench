# Canonical Prompt — Experiment 03 v1: Real PL × All CS522 Semantics in Lean 4

**TLDR:** This is the durable, paste-into-Claude-Code prompt for a long-horizon run that writes the formal semantics of one real programming language in Lean 4 using every CS522 framework (big-step, small-step, denotational, MSOS, RSEC, CHAM, K, λ-calculus) and verifies each output via a three-layer protocol. Edit conservatively — the experiment is reproducible against this file.

---

## 0. Identity & environment

- You are Claude Code (or Codex) operating in `~/veri-veri-bench` on behalf of Brando Miranda (`brandojazz@gmail.com`).
- Bootstrap `~/agents-config` first: `git clone https://github.com/brando90/agents-config.git ~/agents-config 2>/dev/null || git -C ~/agents-config pull 2>/dev/null`.
- Read `~/agents-config/INDEX_RULES.md` into context. Hard Rule 4 (Dual TLDR), Hard Rule 5 (Verification snapshot), Hard Rule 6 (refresh agents-config), Trigger Rule 15 (Title + TLDR on every doc) all apply to every response in this run.
- Lean toolchain: `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0`. Lake project name `imp`.

## 1. Goal (one paragraph)

Write the operational semantics of **one** real programming language in Lean 4, using **all 8** CS522 semantic frameworks, and verify the output is correct against (a) a reference interpreter, (b) cross-framework equivalence theorems, and (c) Roșu-textbook spot-checks. The deliverable is a directory `Imp/Real/<Lang>/` containing one Lean module per framework plus a `Verification.lean` that ties them together, plus `experiments/03_real_pl_all_semantics_in_lean/expt_v1/results/results_summary_<TS>.md` summarizing PASS/FAIL per framework.

## 2. Pre-flight (do these before writing any Lean)

1. **Read the experiment plan.** In order: `experiments/03_real_pl_all_semantics_in_lean/README.md`, this file, `language_candidates.md`, `frameworks_matrix.md`, `verification_spec.md`.
2. **Read the prior art in this repo.**
   - `Imp/main.lean` — base IMP, big-step `terminate`, determinism (the model for new big-step files).
   - `Imp/HW1/{Syntax,BigStep,SmallStep}.lean` — HW1 patterns for big-step + small-step with errors.
   - `Imp/HW2/{Syntax,Denotational}.lean` — HW2 denotational pattern.
   - `Imp/HW3/{Syntax,BigStep,SmallStep}.lean` — IMP++ patterns (input/output, halt, threads, locals).
   - `experiments/00_aneas_does_pl_semantics/imp_semantics.md` — narrative on what big-step looks like in Lean here; the same shape extends to small-step / denotational / etc.
3. **Confirm the target language with the user before writing any Lean.** Default `pythonlite`. Alternates listed in `language_candidates.md`. Print the chosen target + scope and wait for `OK` or `pick <X> instead`.
4. **Confirm the verification protocol with Stepan.** Email `stepurik@stanford.edu` (CC `brandojazz@gmail.com`) with `verification_spec.md` attached and ask explicitly: "is this enough to certify a semantics is correct?". Don't wait synchronously — proceed but flag the dependence.
5. **Fix the stale `Imp.Basic` import in `Imp.lean` if Experiment 02 / HW1 has not.** `lake build` must be green before any new module lands.

## 3. Plan of work (sequential, one framework at a time)

For the chosen language `<Lang>`:

### 3.1. Syntax module (do this first, do it once)

`Imp/Real/<Lang>/Syntax.lean` — the AST shared by every framework. Mirror `Imp/HW3/Syntax.lean`'s shape. One `inductive Expr`, one `inductive Stmt`, plus any language-specific value type (`Value`, `Object`, `Frame`, …). `deriving Repr, DecidableEq` everywhere it is decidable.

Commit & push as soon as it compiles standalone.

### 3.2. One framework per file (in this order)

Order is chosen so easier frameworks first establish reusable lemmas:

1. `Imp/Real/<Lang>/BigStep.lean` — `inductive Step : Config → Config → Prop` (big-step / Kahn). Prove **determinism** (`Step.unique`) and **inversion lemmas** for each constructor. This is the *reference judgment* — every later framework must be proved equivalent to this one (on terminating programs).
2. `Imp/Real/<Lang>/SmallStep.lean` — Plotkin SOS. One reduction step `→`, prove **progress + preservation** if the language is typed, else prove `BigStep ⇔ SmallStep⋆` (transitive closure).
3. `Imp/Real/<Lang>/Denotational.lean` — `⟦·⟧ : Stmt → State → Option State` (or `→ State_⊥` once a CPO is in scope). Prove `BigStep ⇔ ⟦·⟧`.
4. `Imp/Real/<Lang>/MSOS.lean` — Modular SOS (labelled transitions). Re-derive `SmallStep` as a label-erasure projection.
5. `Imp/Real/<Lang>/RSEC.lean` — Reduction Semantics with Evaluation Contexts. Prove `RSEC ⇔ SmallStep`.
6. `Imp/Real/<Lang>/CHAM.lean` — Chemical Abstract Machine. Prove `CHAM ⇔ SmallStep` (or directly to BigStep).
7. `Imp/Real/<Lang>/K.lean` — K-framework / rewriting style (closest to Maude). Prove `K ⇔ SmallStep`.
8. `Imp/Real/<Lang>/Lambda.lean` — λ-calculus / type system. For `pythonlite`: a CBV λ-calculus + simple types; show that a closed core fragment of `<Lang>` translates into and out of it (Felleisen-style "definitional translation" or "well-typed implies progress").

After every file:

- `lake build` green.
- Differential test (layer (a) of `verification_spec.md`) on a fixed suite of source programs.
- At least one direction of the cross-framework equivalence theorem closed (or marked `axiom` with a `TODO(equiv)` comment if it requires a deep induction we will defer to v2).
- Commit + push. **Do not** batch frameworks into one commit.

### 3.3. Glue module

`Imp/Real/<Lang>/Verification.lean` — imports all 8 framework modules, states the diamond of equivalence theorems, and re-exports the executable interpreter that drives the differential tests.

### 3.4. Top-level update

Add `import Imp.Real.<Lang>.Verification` to `Imp.lean`. `lake build` green.

## 4. Verification (run after every framework, gate before commit)

See `verification_spec.md` for full details. Quick gate:

- **Layer (a) — differential test.** Run the test corpus (`expt_v1/templates/test_corpus/`) through both the language's reference interpreter (CPython / `wasmtime` / `lua5.1` / …) and the Lean executable extracted from the framework's interpreter. Outputs must match on every program. ≥ 95% on edge-cases corpus is the gate.
- **Layer (b) — equivalence theorem.** At minimum, the *forward* direction (this-framework → BigStep) must compile. The reverse direction can be deferred to v2 with a `TODO(equiv)` comment.
- **Layer (c) — textbook spot-check.** For at least 5 randomly-chosen rules, point at the corresponding rule in `cs522/ProgrammingLangSemantics.pdf` (Roșu) and confirm the Lean constructor matches by name and shape. Record the citation in the file's docstring.

## 5. QA (mega QA before final merge)

After all 8 frameworks land:

1. `codex exec --full-auto "<QA prompt for Imp/Real/<Lang>/>"` — full correctness + structural pass per `~/agents-config/workflows/qa-correctness.md`.
2. Self-review pass (CC).
3. Gemini CLI clean-eyes pass.

If `CRITICAL_ISSUES > 0`, fix and re-run that stage. Do not merge until all stages PASS.

## 6. Reporting (after the full run)

Produce `expt_v1/results/results_summary_<YYYY-MM-DD__HH-MM-SS>.md` containing:

- TL;DR (1–3 sentences).
- Config table: target language, exact model ID (e.g. `claude-opus-4-7`), backend, runtime, lake / mathlib versions.
- Per-framework PASS/FAIL table:

  | Framework  | (a) Diff-test pass rate | (b) Equiv-thm | (c) Textbook | Lines | Notes |
  |------------|-------------------------|---------------|--------------|-------|-------|
  | BigStep    | n/m | ✔ / ✗ / `axiom` | ✔ / ✗ |   …   |       |
  | SmallStep  | …   | …               | …     |   …   |       |
  | …          |     |                 |       |       |       |

- Plots (if applicable) under `results/plots/` with relative-path PNGs.
- W&B Report URL (created via `wandb_workspaces.reports.v2`) — entity `brando-su`, project `veri-veri-bench-03`.

Then send the email per `~/agents-config/workflows/expts-and-results.md` § Email Notification — `brando.science@gmail.com`, CC `brando9@stanford.edu`, plus Stepan (`stepurik@stanford.edu`) since the artefact is for him to verify.

## 7. Hard rules reminder (lift from `~/agents-config/INDEX_RULES.md`)

- Never commit secrets. Inspect diffs before pushing.
- Dual TLDR (`TLDR-start:` / `TLDR-end:`) on every user-facing response.
- Verification snapshot block after `TLDR-end:`.
- Title + `**TLDR:**` on every doc you write.
- Refresh `~/agents-config` at session start (and mid-run for sessions > 1 h).
- Commit + push immediately after QA passes.
- No `sorry` in production Lean modules. `axiom` is allowed only with an inline `TODO(equiv)` comment naming the theorem to be discharged.
- Email Stepan when a framework lands.

## 8. Failure modes & escape hatches

- **The chosen language is too big.** If after 24 h of agent time you have not got `BigStep` to compile, **stop** and shrink the scope: drop closures, drop exceptions, drop classes — record in `cc.md` what was cut. A small language with all 8 frameworks correct is the win condition; a sprawling language with one half-finished framework is not.
- **Reference interpreter is unavailable.** Note in the results summary; layer (a) becomes "skipped — no reference interpreter on this machine"; do not silently claim PASS.
- **A framework is genuinely the wrong fit for the language** (e.g. CHAM on a language without obvious parallel composition). Implement it anyway — at minimum a degenerate sequential CHAM — and discuss limits in the file's docstring. Do **not** silently skip a framework. Brando's spec says all 8.
- **Compute / credit budget exhausted.** Save a partial `results_summary_<TS>.md`, mark unfinished frameworks `BLOCKED`, and email Brando. Do not delete partial Lean files; commit them under a `*.wip.lean` extension if they don't yet build.

---

*Companion files in this directory: `cc.md` (conversational log), `language_candidates.md`, `frameworks_matrix.md`, `verification_spec.md`, `templates/`.*
