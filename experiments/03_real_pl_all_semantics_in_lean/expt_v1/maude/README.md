# pythonlite — Big-step semantics in Maude (CS522 framework)

**TLDR:** End-to-end implementation of `pythonlite` (a curated Python subset) as a CS522-style big-step / Kahn operational semantics in Maude. Includes a Python → Maude AST parser (`parse.py`), a CPython-vs-Maude differential test harness (`run_diff_test.sh`), and a 7-program test corpus under `tests/`. Current status: **7 / 7 corpus programs match CPython output exactly** (see `results/results_summary_<TS>.md`).

---

## How to run

```bash
cd experiments/03_real_pl_all_semantics_in_lean/expt_v1/maude
./run_diff_test.sh                     # runs every tests/*.py through both CPython
                                       # and the Maude semantics, diffs the outputs
maude -no-prelude -no-banner run_bigstep_tests.maude   # rewrites the hand-written
                                                       # test programs in pythonlite-programs.maude
```

## What's in this directory

| File / dir                         | What it is |
|------------------------------------|------------|
| `pythonlite-syntax.maude`          | AST: integer / boolean / identifier expressions; `+`, `-`, `*`, `//`, `%`, comparisons, short-circuit `and`/`or`/`not`; statements `pass`, `:=`, `print`, `;`, `ifelse`, `while`. Indentation desugared at parse time. |
| `pythonlite-state.maude`           | Variable state (`Id -> Int`) and output buffer (`Out` = list of `Int`). Lookup of unbound = `undefined` (operational analogue of `NameError`). |
| `pythonlite-bigstep.maude`         | Big-step / Kahn-style semantics: judgments `< E, σ, out > => < val, out' >`, `< S, σ, out > => < σ', out' >`, `< Pgm > => < σ, out >`. Output buffer threading mirrors HW3 IMP++. Floor-division & floor-mod (Python semantics, not Maude's truncating ones) defined in `PYTHONLITE-FLOORDIV`. Short-circuit `and`/`or` rules. |
| `pythonlite-programs.maude`        | 7 hand-written Maude AST programs matching the `tests/*.py` files. |
| `run_bigstep_tests.maude`          | Loads the semantics + programs and rewrites each program. |
| `parse.py`                         | Reads a real Python source file via `ast.parse` and emits an equivalent Maude `Pgm` constant. The parser is the layer that converts indentation-based Python into the Maude desugared AST. |
| `extract_out.py`                   | Extracts the `Out` integer-list portion from Maude's `result Configuration:` output for diffing. |
| `run_diff_test.sh`                 | The end-to-end driver. For each `tests/*.py`: run CPython → capture stdout; run `parse.py` → run Maude on the auto-generated AST → extract `Out` → diff. |
| `tests/`                           | Real Python source files. `01_smoke.py`, `02_arith.py`, `03_if.py`, `04_factorial.py` (5! = 120), `05_collatz.py` (steps from 27 = 111), `06_fizzbuzz.py` (sentinel ints in place of strings), `07_shortcirc.py` (validates short-circuit and division-by-zero protection). |
| `builtins.maude`                   | Verbatim copy of `cs522/HW1-Maude/builtins.maude` — Maude prelude (`PL-INT`, `PL-BOOL`, `PL-ID`, etc.). |
| `results/`                         | Test-run outputs: `last_run.json` (most recent machine-readable summary), `results_summary_<TS>.md` (timestamped human-readable summary). |

## Scope (pythonlite v1)

Included:
- Integers (Python `int`), booleans (`True` / `False`), identifiers.
- Arithmetic: `+`, `-`, `*`, `//`, `%`, unary `-`. Floor-div and floor-mod follow Python semantics (sign of divisor for `%`; toward-`-inf` for `//`).
- Comparisons: `<`, `<=`, `>`, `>=`, `==` (encoded `eqq` in Maude), `!=` (encoded `neq`).
- Boolean operators `and`, `or`, `not` — short-circuit at the semantic level (separate rules for the early-exit and right-eval cases).
- Statements: `pass`, `x = e` (encoded `:=` in Maude), `print(e)`, sequencing, `if/else`, `while`.
- Programs print integers to a captured output buffer for differential testing.

Excluded (out of scope for v1, listed in `../language_candidates.md`):
- Strings, floats, lists, dicts, tuples, classes.
- Functions, closures, recursion.
- Exceptions; division-by-zero is currently *stuck* (rule does not apply) rather than raising. v2 should add a `< error, σ, out >` configuration mirroring CS522 HW1 Ex. 56.
- For-loops; replaced by while loops with manual indexing.
- Modules / imports.
- I/O beyond integer `print`.

## Why Maude (and not Lean) for this v1

The user's target is *the CS522 framework*. CS522 uses Maude's rewriting logic as its semantics-implementation language, and the reference HW solutions in `cs522/HW{1..6}-Maude/` are all Maude. Doing the v1 in Maude lets us reuse `cs522/HW1-Maude/builtins.maude` verbatim, reuse the `< Cfg >` configuration shape and `=>` rule format from `cs522/HW1-Maude/imp/0-imp-original/1-imp-bigstep/imp-semantics-bigstep.maude`, and execute the resulting semantics directly — Maude *is* an interpreter for its own definitions. The Lean port lives one level up under `Imp/Real/Pythonlite/` and is a follow-up: this experiment establishes the shape of the answer; the Lean port is the kernel-checked verification of it.

## Verification: how we decide it's "correct"

Per `../verification_spec.md`, the contract has three layers. This v1 implements layer **(a)** in full and layers (b) and (c) partially:

- **(a) Differential testing vs reference interpreter** — fully implemented. `run_diff_test.sh` runs every `tests/*.py` through both CPython 3 and the Maude big-step semantics and diffs the integer outputs. Current pass rate: **7 / 7**.
- **(b) Cross-framework equivalence theorems inside Lean** — deferred until the Lean port lands at `Imp/Real/Pythonlite/`. Big-step is the reference judgment; small-step / denotational / MSOS / RSEC / CHAM / K / λ ports must each prove `↔ BigStep` (forward direction at minimum, no `sorry`).
- **(c) Stepan + Roșu textbook spot-check** — Maude rules are written to mirror `cs522/HW1-Maude/imp/0-imp-original/1-imp-bigstep/imp-semantics-bigstep.maude` shape-by-shape; cross-check in PR review.

## Known limitations / TODOs

- `pythonlite-syntax.maude` emits a few benign `bad format length` warnings on the `format (...)` operator attributes (lines 69, 70, 77, 79). These affect only Maude's pretty-printer; rules and rewriting are unaffected. Fix: trim the `format` attributes on `_:=_`, `print(_)`, `ifelse(_){_}else{_}`, `while(_){_}`.
- Division-by-zero is silently stuck rather than producing `< error, σ, out >`. Add an error configuration in v2.
- The output extractor (`extract_out.py`) assumes pythonlite's "one `|->` binding per variable" state shape and splits on the first top-level `,`. If a future v2 introduces grouped IMP-style `(x,y) |-> 0` declarations, the extractor must switch to a depth counter that ignores `|->`'s `>` glyph.
- No formal proof of determinism yet. Add `crl` → `rl` reduction proof or Lean port + `unique` lemma.

## Reproducing manually (one test)

```bash
# pick a test file
PROG=tests/04_factorial.py
# convert to maude
python3 parse.py "$PROG" mypgm > /tmp/mypgm.maude
# run
cat > /tmp/run.maude <<EOF
in builtins.maude
in pythonlite-syntax.maude
in pythonlite-state.maude
in pythonlite-bigstep.maude
in /tmp/mypgm.maude
mod RUN is including PYTHONLITE-SEMANTICS-BIGSTEP + MYPGM-PROG . endm
rewrite < mypgm > .
quit
EOF
maude -no-prelude -no-banner /tmp/run.maude
# expected:  result Configuration: < 'acc |-> 120 & 'i |-> 6 & 'n |-> 5,120 >
# the trailing "120" is the printed factorial of 5.
python3 "$PROG"
# expected:  120
```
