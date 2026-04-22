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

* `denA : Aexp → State → AResult → Prop` — arithmetic results are either a
  value, Ex. 83 `Error`, or ordinary `undefined`.
* `denB : Bexp → State → BResult → Prop` — similarly.
* `denS : Stmt → State → State → Prop` — statement-level silent failure only
  fires on Ex. 83 `Error`. Division-by-zero in an assignment, if-guard, or
  while-guard produces `State.markFailed σ` (i.e. `σ & err |-> 1` with
  `errId := "__err__"`), while plain `undefined` still has no derivation.
* `denS.seq_failed` / `denS.seq_ok` short-circuit the sequencing equation:
  if `s1` returned a failed state, skip `s2`; otherwise continue.
* `denS.while_true` / `.while_body_failed` / `.while_err` implement the
  unfolded fixpoint equation with silent-failure absorption.
* No CPO / `fixCPO` machinery is reproduced here; instead, non-termination
  and ordinary bottom cases correspond to the absence of a `denS`
  derivation (same convention as `Imp/main.lean`'s `terminate`).

## Verification status

* `lake build` passes.
* Smoke examples at the bottom of `Denotational.lean`: `[[1/0]] = Error`,
  `[[6/2]] = 3`, `[[y]](x|->2) = undefined`, and
  `[[x = 3/0 ;]](x|->2) = markFailed (x|->2)`.
* Paper exercises 80/81/82 are not formalized (per HW spec, they are PDF-
  submission proofs). Future work in this repo could add them.
* Independent verification is requested from Stepan Nesterov per
  `experiments/02_do_all_cs522_in_Lean/prompt.md`.
