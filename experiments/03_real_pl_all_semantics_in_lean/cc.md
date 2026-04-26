# Experiment 03 — Conversational Log

**TLDR:** Decisions ledger and partial-progress notes for `experiments/03_real_pl_all_semantics_in_lean/`. The runnable plan is `expt_v1/prompt.md`; this file is the scratchpad / history.

---

## 2026-04-26 — Kickoff

### Discord transcript (`# veri-veri-bench`, transcribed from screenshot)

- **Stepan, 04/22 12:18 PM:** "@Brando it seems like your agent didn't really modify my implementation but instead produced its own separate implementation of various semantics for each of the homeworks."
- **Stepan, 04/22 12:36 PM:** "fyi I started to modify my own code semi-manually, that is, by asking Claude code to do it one step at a time and see if I like the result."
- **Brando, 04/22 2:01 PM (replying to Stepan):** "yes I told it to do that."
- **Brando, 04/26 10:58 AM:** "@Stepan I have an idea. Since I have a lot of credits to run Claude or claude 5.5 I'm thinking that maybe the way to directly test our hypothesis is to just ask it to try to write the semantics of a real programming language and have it run for a few days and the only thing that we would need is a set of tests or theorems or some way for us to check that the final semantics outputs actually correct what do you think of this plan? So concretely the deliverable / what we would need would be for you to know exactly how we could actually verify that the output semantics it proposes is correct."
- **Brando, 04/26 11:09 AM:** "We could tell it to try every semantics framework. As long as we can verify it's right I don't care which framework it uses."
- **Brando, 04/26 (later, to Claude Code):** "the main thing is to try to translate the real programming language a real programming language using all the cs522 programming language semantics! write an experiment folder as we always do check the agents config file please."

### What we built in this kickoff

- `experiments/03_real_pl_all_semantics_in_lean/`
  - `README.md` — goal, structure, method, deps, status table.
  - `cc.md` — this file.
  - `expt_v1/`
    - `cc.md` — agent prompt (paste-into-Claude-Code).
    - `prompt.md` — canonical, durable prompt.
    - `language_candidates.md` — `pythonlite` recommended; WebAssembly 1.0 strong alternate.
    - `frameworks_matrix.md` — 8 CS522 frameworks × language features, with file-per-framework plan.
    - `verification_spec.md` — three-layer protocol (diff-test, equiv-thm, textbook + Stepan).
    - `templates/` — empty for now, will hold the per-framework Lean module skeleton.
    - `results/` — empty, will hold timestamped summaries.

### Resolved scope decisions (this kickoff)

1. **Numbering:** `03_` is the next free experiment slot (`00_aneas_does_pl_semantics`, `02_do_all_cs522_in_Lean` already used; `01_` intentionally unused).
2. **All 8 frameworks.** Big-step, small-step, denotational, MSOS, RSEC, CHAM, K (rewriting), λ-calculus / type system. No exceptions; if a framework is awkward on the chosen language, model a degenerate version and document.
3. **Default target:** `pythonlite` (curated Python subset). Backstop: WebAssembly 1.0 (already-formal reference spec).
4. **Verification ≠ optional.** Three-layer protocol is the gating contract. A framework only counts as "done" when all three layers pass.
5. **Long Claude run.** Brando has the credits. Budget guideline: ≤ 72 h of agent time per framework × language pair before falling back to a smaller scope.

### Open decisions (need Brando + Stepan input)

- [ ] **Target language confirmation.** `pythonlite` vs WebAssembly. Defaults to `pythonlite` unless flipped.
- [ ] **Stepan: verification protocol sign-off.** Email Stepan with `verification_spec.md`; ask whether layer (a) + (b) + (c) is sufficient.
- [ ] **Compute budget cap.** Brando to specify hard cap in dollars or agent-hours.
- [ ] **Where to host the run output.** This repo (`Imp/Real/<Lang>/`) vs a fresh repo. Default: this repo.

### Dependencies & ordering

- This experiment depends on Experiment 02 (CS522 IMP/IMP++ in Lean) being at least partway through. HW1 / HW2 / HW3 patterns are reused. HW4 (MSOS, RSEC, CHAM) is the most-helpful prior work; it is *not* yet done in Lean (only Maude reference exists in `cs522/HW4-Maude/`). If Experiment 03 starts before Experiment 02 HW4 finishes, the agent should port HW4 in `Imp/HW4/` *first* using the IMP++ AST, then reuse the resulting MSOS/RSEC/CHAM patterns when scaling up to `pythonlite`.
- The stale `Imp.Basic` import in `Imp.lean` must be fixed before any new Lean modules are added under `Imp/Real/<Lang>/`. (HW1 already fixes this — confirm.)

## Followups discovered while writing this folder

- The repo's `Imp.lean` already aggregates `Imp.HW1`, `Imp.HW2`, `Imp.HW3`. The CLAUDE.md / README claim it imports a missing `Imp.Basic`; need to re-check whether that's still the case after HW1's port. If not, update `CLAUDE.md` and `README.md` to drop the stale claim.
- Survey of the existing `Imp/HW3/` modules confirms IMP++ already covers I/O buffers, halting, sequential `spawn`, and locals. Concurrent `spawn` is deferred there too — same deferral applies in `pythonlite` v1 (no threads).
- `cs522/HW4-Maude/` is the bridge to MSOS/RSEC/CHAM. When the long run starts, the agent should explicitly port HW4 to `Imp/HW4/` *before* attempting MSOS/RSEC/CHAM on the real language. Otherwise the patterns are invented from scratch.

## Why this experiment matters (one-paragraph elevator)

VeriBench shows LLMs can vibe-translate Python → Lean, but the Lean only verifies the LLM's *interpretation*. Aeneas does Rust → Lean via a deterministic translator (LLBC) but the translator itself is unproven. `veri-veri-bench` is the inside-Lean attempt — keep the AST and the operational semantics as Lean kernel objects. Experiment 03 is the first attempt to push that machinery past the toy CS522 IMP++ examples and onto something a developer would recognize as a real language. Doing it in *every* CS522 framework gives us cross-framework equivalence theorems as a redundancy check and exercises the full toolbox. If the run succeeds, the deliverable is a Lean module that any third party can re-check against (a) the language's reference interpreter, (b) Roșu's textbook, and (c) Stepan's verification.
