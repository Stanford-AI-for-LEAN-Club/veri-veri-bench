# Prompt: translate all of CS522 into Lean 4, one HW at a time

You are Claude Code operating in `~/veri-veri-bench`. The user is Brando Miranda (`brandojazz@gmail.com`). Follow this prompt exactly.

## Goal

For each CS522 homework (HW1 → HW2 → HW3 → HW4 → HW5 → HW6 → Extra-Credit), produce a Lean 4 formalization that faithfully captures the PL semantics the homework defines in Maude. Do the homeworks **sequentially**: each one must be fully merged (PR merged, mega QA passed, Stepan notified) before the next one starts.

This project's thesis (see `README.md`): writing PL semantics for a full real programming language is too hard for humans alone; AI can help, but only if the work is anchored in a small, kernel-checkable formal object — not an LLM vibe translation. The CS522 IMP exercises are the toy case we must master before scaling to Python/Rust/C.

## Sources of truth

- **Course materials + HW specs**: `~/veri-veri-bench/cs522/` — contains `ProgrammingLangSemantics.pdf` (Grigore Roșu's textbook) and `HW1-Maude/hw1.md` … `HW6-Maude/hw6.md` plus `Extra-Credit/`.
- **Brando's existing Maude solutions**: `~/cs522/` (the GitHub repo `brando90/cs522`, default branch `master`). Contains HW1-Maude through HW4. HW5, HW6, and Extra-Credit do **not** have existing Maude solutions here — check with Brando when you reach those.
- **Lean target**: `~/veri-veri-bench/Imp/` (this repo). Default branch `master`. Remote: `git@github.com:Stanford-AI-for-LEAN-Club/veri-veri-bench.git`.
- **Divergence note**: `~/cs522/HW1-Maude/*` and `~/veri-veri-bench/cs522/HW1-Maude/*` are **not** subsets of each other. Read specs from the vvb copy, review Brando's solutions from `~/cs522`. Do not merge the two trees.

## Per-HW workflow

For each HW `N`:

### 1. Document Brando's Maude solution in `~/cs522`

1. Read `~/veri-veri-bench/cs522/HW{N}-Maude/hw{N}.md` (the assignment spec) and the relevant textbook pages in `ProgrammingLangSemantics.pdf`.
2. Read Brando's solution files in `~/cs522/HW{N}-*/` (plus `my_tests.m`, `_original.maude` backups, etc.).
3. **Try to execute the Maude code.** `maude` is not installed on the Mac natively and is not in brew. Options in order of preference:
   - `docker run` a community maude image (e.g. search `iamdaly/maude` or similar). Requires Docker Desktop running.
   - If Docker is unreachable, fall back to **static review only** and say so explicitly in the commit message and PR body — do not claim "verified runs" without execution.
4. Add thorough comments to each `.maude` file:
   - Top-of-file block comment: which exercise(s) this file is for, where in the textbook, and a 2–4 sentence summary of what the file does.
   - Per-rule comments keyed to the spec (e.g. "BigStep-DIV, error propagation, Ex. 56 part (b)").
   - If a rule is *non-obvious* (e.g. handles an edge case like `Error` propagation), explain *why* it is written that way.
   - Do not rewrite the code — only document. If you find a bug, flag it in the commit message; do not silently fix it.
5. Commit with a clear message and push to `master` on the `brando90/cs522` remote.

### 2. Create a Lean PR in `veri-veri-bench`

1. `cd ~/veri-veri-bench && git checkout master && git pull`.
2. Create branch `hw{N}-lean-translation` (or a more descriptive slug, e.g. `hw1-div-by-zero`).
3. Create module `Imp/HW{N}/` with one Lean file per sub-semantics the homework touches:
   - `Imp/HW{N}/Syntax.lean` — AST extensions (if any new syntax is introduced)
   - `Imp/HW{N}/BigStep.lean`, `SmallStep.lean`, `Denotational.lean`, `CHAM.lean`, `TypeSystem.lean`, etc. — one per semantic style present in the Maude solution
   - `Imp/HW{N}/README.md` — short doc tying each Lean file back to the corresponding Maude file and textbook exercise
4. Translate **faithfully**: each Maude rule becomes a constructor of a Lean `inductive` relation (for operational semantics) or a recursive function (for denotational / evaluation). Preserve rule names as constructor names where possible. Prove determinism and any other lemmas Brando proved in Maude.
5. Update `Imp.lean` so the new modules are imported and `lake build` stays green. If the existing `Imp.Basic` stale import is still in the tree, fix it as part of HW1.
6. Run `lake build` locally. If it fails, fix it before pushing.
7. Commit, push, and open a PR against `master`.

### 3. Mega QA (3-stage sequential, per `~/agents-config/INDEX_RULES.md` Rule 10)

Because Claude Code is the builder, the chain is **CC → Codex → Gemini**.

1. Self-review pass (CC). Re-read the diff, look for: missing sub-semantics, off-by-one in inference rules, wrong constructor arity, proof obligations not discharged, `sorry`s.
2. Dispatch Codex:
   ```
   codex exec --full-auto "$QA_PROMPT"
   ```
   where `$QA_PROMPT` points Codex at the PR's diff and asks for full correctness + structural review, with authority to fix. See `~/agents-config/workflows/qa-correctness.md` and `qa-structural.md`.
3. Dispatch Gemini CLI for the final clean-eyes pass.
4. If any stage has `CRITICAL_ISSUES > 0`, fix and re-run that stage before moving on.

### 4. Merge + notify Stepan

1. After all 3 stages return PASS/FIXED with 0 critical issues, merge the PR (per Rule 8: "Commit and push after QA passes").
2. **Notify Stepan**: email `stepurik@stanford.edu` (CC `brandojazz@gmail.com`) with
   - subject: `[veri-veri-bench] HW{N} Lean translation — ready for verification`
   - body: PR URL, short summary of what was translated, and an explicit ask to verify against the CS522 textbook definitions.
3. **Why email instead of GitHub @-mention**: as of this prompt, Stepan's roster entry in `~/ultimate-utils/py_src/uutils/collaborators.py` has `github: null`. If/when his handle becomes known, also add him as a reviewer on the PR and update the roster.
4. Mark the HW's task complete; move to the next HW.

## HW scope notes

| HW  | Content                                               | Brando has Maude solution? |
|-----|-------------------------------------------------------|----------------------------|
| HW1 | Ex. 56 (big-step div-by-zero) + Ex. 70 (small-step)   | Yes (`~/cs522/HW1-Maude/`) |
| HW2 | Denotational + CPO                                    | Yes (`~/cs522/HW2-Maude/`) |
| HW3 | IMP++                                                 | Yes (`~/cs522/HW3/`)       |
| HW4 | IMP_PP                                                | Yes (`~/cs522/HW4/`)       |
| HW5 | (see `cs522/HW5/hw5.md`)                              | **No** — ask Brando        |
| HW6 | (see `cs522/HW6-Maude/hw6.md`)                        | **No** — ask Brando        |
| EC  | Extra-Credit                                          | **No** — ask Brando        |

For HW5/HW6/EC, confirm with Brando whether to (a) skip the Maude-documentation step and go straight to Lean, or (b) write fresh Maude solutions first.

## After the final HW

1. Run one **overall** mega QA across the full `Imp/` directory (not just one HW's diff).
2. Send Stepan a single consolidated email: all PR URLs, overall summary, verification request.
3. Close this experiment — update `experiments/02_do_all_cs522_in_Lean/results.md` with links.

## Hard rules reminder (from `~/agents-config/INDEX_RULES.md`)

- Never commit secrets. Review diffs before pushing.
- Dual TLDR (`TLDR-start:` at top, `TLDR-end:` at bottom) on every user-facing response.
- Verification snapshot after `TLDR-end`.
- Refresh `~/agents-config` at the start of each new user task (`git -C ~/agents-config pull`).
- Commit + push immediately after QA passes; don't wait for the human.

---

*This file is the durable, self-contained prompt for the task. `cc.mnd` in the same folder contains the conversational scratchpad / history.*
