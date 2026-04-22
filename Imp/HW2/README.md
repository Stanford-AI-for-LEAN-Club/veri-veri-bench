# CS522 HW2 in Lean 4

Lean 4 port of CS522 Homework 2, **Exercise 83** — denotational semantics
of IMP with silent division-by-zero failure.

(Exercises 80, 81, 82 are paper/PDF proofs; out of scope here.)

## File map

| File                         | Maps to (Maude)                                                                                         |
|------------------------------|---------------------------------------------------------------------------------------------------------|
| `Imp/HW2/Syntax.lean`        | `HW2-Maude/imp/0-imp-original/imp-syntax.maude` + `state.maude` + the HW's reserved `op err : -> Id .` |
| `Imp/HW2/Denotational.lean`  | `HW2-Maude/imp/0-imp-original/4-imp-denotational/imp-semantics-denotational.maude` (Ex. 83)            |
| `Imp/HW2.lean`               | aggregate                                                                                               |

## Design summary

* `denA : Aexp → State → Option Int → Prop` — `some n` = value, `none` =
  Maude's `Error` at AExp level.
* `denB : Bexp → State → Option Bool → Prop` — similarly.
* `denS : Stmt → State → State → Prop` — **total** at the Stmt level: every
  Stmt has an output state. Division-by-zero in an assignment, if-guard, or
  while-guard produces `State.markFailed σ` (i.e. `σ & err |-> 1` with
  `errId := "__err__"`).
* `denS.seq_failed` / `denS.seq_ok` short-circuit the sequencing equation:
  if `s1` returned a failed state, skip `s2`; otherwise continue.
* `denS.while_true` / `.while_body_failed` / `.while_err` implement the
  unfolded fixpoint equation with silent-failure absorption.
* No CPO / `fixCPO` machinery is reproduced here; instead, non-termination
  of `while` corresponds to the absence of a `denS` derivation (same
  convention as `Imp/main.lean`'s `terminate`).

## Verification status

* `lake build` passes.
* Smoke examples at the bottom of `Denotational.lean`: `[[1/0]] = Error`,
  `[[6/2]] = 3`, `[[x = 3/0 ;]](x|->2) = markFailed (x|->2)`.
* Paper exercises 80/81/82 are not formalized (per HW spec, they are PDF-
  submission proofs). Future work in this repo could add them.
* Independent verification is requested from Stepan Nesterov per
  `experiments/02_do_all_cs522_in_Lean/prompt.md`.
