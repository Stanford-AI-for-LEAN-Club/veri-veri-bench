# CS522 HW1 in Lean 4

Lean 4 port of CS522 Homework 1 — **Exercise 56** (big-step semantics
with division-by-zero) and **Exercise 70** (small-step semantics with
division-by-zero).

## File map

| File                         | Maps to (Maude)                                                                                 |
|------------------------------|-------------------------------------------------------------------------------------------------|
| `Imp/HW1/Syntax.lean`        | `HW1-Maude/imp/0-imp-original/imp-syntax.maude` + `HW1-Maude/imp/state.maude`                   |
| `Imp/HW1/BigStep.lean`       | `HW1-Maude/imp/0-imp-original/1-imp-bigstep/imp-semantics-bigstep.maude`   (Ex. 56)             |
| `Imp/HW1/SmallStep.lean`     | `HW1-Maude/imp/0-imp-original/3-imp-smallstep/imp-semantics-smallstep.maude` (Ex. 70)           |
| `Imp/HW1.lean` (aggregate)   | —                                                                                               |

## Design summary

* **Big-step (Ex. 56).** The Maude solution adds `Error : -> State` and
  "sink" rules that rewrite `< A | B | S , Error >` to `< Error >`. In
  Lean we model error as a value constructor `AVal.err / BVal.err /
  SVal.err` rather than as a state value, so `State : Id → Option Int`
  stays a plain partial map. Rule names mirror the Maude rule labels
  (e.g. `BigStep-DIV` → `evalA.div / .div_zero / .div_err_l / .div_err_r`).
* **Small-step (Ex. 70).** The Maude solution adds syntactic error
  constants `errorAr : -> AExp`, `errorBool : -> BExp`,
  `errorStmt : -> Stmt`. We encode them directly as constructors in
  `Aexp / Bexp / Stmt` in `Syntax.lean`. The error constants are
  terminal (no outgoing `step` rule) which makes our `stepsA / stepsB /
  stepsS` reflexive-transitive closures converge at an error, matching
  Maude's `rew *` behaviour. The headline rule
  `o < I1 / 0, σ > => < errorAr, σ >` lives at `stepA.div_by_zero`.

## Verification status

* `lake build` passes for this checkout.
* Small concrete examples (`example : evalA (.div 1 0) ...`) serve as
  smoke tests at the bottom of `BigStep.lean` and `SmallStep.lean`.
* Maude execution on the original course files has **not** been run in
  this PR (no local `maude`; Docker workflow deferred). Final behavioural
  verification is requested from Stepan Nesterov per the CS522 translation
  protocol.
