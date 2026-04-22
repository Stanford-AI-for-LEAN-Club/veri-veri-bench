import Imp.HW2.Syntax
import Imp.HW2.Denotational

/-!
# CS522 HW2 — aggregate module

Re-exports HW2's submodules:

* `Imp.HW2.Syntax`        — IMP AST + `State` + the reserved `errId`
  "silent-failure" flag.
* `Imp.HW2.Denotational`  — Exercise 83 denotational semantics:
  `denA / denB / denS / denP`, where `denA`/`denB` distinguish ordinary
  values, Ex. 83 `Error`, and plain `undefined`, and only the `Error`
  cases inside a Stmt manifest as `State.markFailed σ`, matching the
  Maude solution's use of `σ & err |-> 1`.

Maude source: `brando90/cs522:HW2-Maude/imp/0-imp-original/4-imp-denotational/imp-semantics-denotational.maude`
(commit [`ca03448`](https://github.com/brando90/cs522/commit/ca03448)
for the module-level docstring; rule logic matches the original).

Paper exercises 80/81/82 (equivalence of `if ... s` vs `if(b){s1 s}else{s2 s}`,
well-definedness of `w_k`, fixed-point characterization) are deliberately
**not** formalized here; per the HW spec they belong in a PDF submission.
-/
