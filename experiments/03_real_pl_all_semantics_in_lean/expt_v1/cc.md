# Agent Prompt — Experiment 03 v1: Real PL × All CS522 Semantics

**TLDR:** Paste this into a fresh Claude Code session running in `~/veri-veri-bench` to launch the long-horizon job that writes the formal semantics of a real programming language in Lean 4 across all 8 CS522 frameworks and verifies the output. The canonical, durable prompt is `prompt.md` next to this file — `cc.md` is the conversational scratchpad / log.

---

## How to use this file

- **`prompt.md`** (next to this file) is the **canonical, self-contained prompt**. Paste *that* into a fresh Claude Code or Codex session. It is the file that should not change once a run is in flight — it is the thing the run is reproducible against.
- **`cc.md`** (this file) is the **conversational log**: starting context, decisions made during the run, follow-ups discovered, partial results. Do edit it as the run progresses. Do not paste it as the prompt.

## Starting context (paste-ready, ~150 words)

You are Claude Code in `~/veri-veri-bench`. Read `experiments/03_real_pl_all_semantics_in_lean/README.md`, then `expt_v1/prompt.md`, `expt_v1/language_candidates.md`, `expt_v1/frameworks_matrix.md`, and `expt_v1/verification_spec.md`. Then bootstrap `~/agents-config` per `CLAUDE.md` and read `~/agents-config/INDEX_RULES.md`.

Pick **one** target language from `language_candidates.md` (default: `pythonlite`) — confirm with the user before starting. Then, for each of the 8 frameworks listed in `frameworks_matrix.md`, create the corresponding Lean module under `Imp/Real/<Lang>/` and run the verification protocol from `verification_spec.md`. Commit per-framework, push to a working branch, and produce `expt_v1/results/results_summary_<TS>.md` + a W&B Report at the end.

Hard rules: dual TLDR + verification snapshot on every response (per agents-config Hard Rule 4 + 5); no `sorry` in production Lean modules; cross-framework equivalence theorems must compile or be marked `axiom` with an explicit comment.

## April 26, 2026 — kickoff conversation log

- 10:58 (Brando, Discord `# veri-veri-bench`): proposes the experiment — long Claude run + verification harness.
- 11:09 (Brando): "We could tell it to try every semantics framework. As long as we can verify it's right I don't care which framework it uses."
- (later) Brando to Claude Code: "the main thing is to try to translate the real programming language a real programming language using all the cs522 programming language semantics! write an experiment folder as we always do".

### Decisions taken in this kickoff (default values — confirm before run)

1. **Numbering:** `03_` (next free slot after `02_do_all_cs522_in_Lean`). `01_` is intentionally unused.
2. **Target language default:** `pythonlite` — see `language_candidates.md`. Alternates ranked: WebAssembly 1.0, Lua 5.1, MiniML.
3. **Frameworks:** the full CS522 set — big-step SOS, small-step SOS, denotational, MSOS, RSEC, CHAM, K (rewriting / Maude), λ-calculus / type system. Detailed responsibility split in `frameworks_matrix.md`.
4. **Verification:** three-layer (differential testing vs reference interpreter, cross-framework equivalence theorems, textbook spot-checks). See `verification_spec.md`.
5. **Notify:** email Stepan when the run finishes (per `~/agents-config/workflows/expts-and-results.md`).

## Follow-ups (track as the run progresses)

- [ ] Stepan: review `verification_spec.md` and confirm it suffices to certify "correct".
- [ ] Brando: confirm `pythonlite` vs WebAssembly choice. WebAssembly has the advantage of an existing fully-formal reference (Watt et al.) — could shortcut layer (a).
- [ ] Once target picked, instantiate `Imp/Real/<Lang>/Syntax.lean` first; all 8 framework files import it.
- [ ] Decide whether to model unrestricted Python `eval`/`exec` reflection (probably **no** for v1 — see `language_candidates.md` § "Out of scope").
- [ ] Coordinate with `experiments/02_do_all_cs522_in_Lean/` so HW4 (MSOS / RSEC / CHAM) lands first — the patterns ported there should be reused, not re-invented.

## Notes on what NOT to do

- Do **not** start writing Lean before the target language is confirmed.
- Do **not** declare a framework "done" without (a) the reference-interpreter differential test passing and (b) at least one direction of the equivalence-to-big-step lemma compiling.
- Do **not** fan out into a full Python implementation. Aim for the smallest subset that exercises every framework feature (control flow, mutable state, exceptions, functions, closures). See `language_candidates.md` § "What `pythonlite` includes / excludes".
- Do **not** commit Maude binaries or `.mol` files; those are tooling, not semantics.
