import Imp.HW1.Syntax
import Imp.HW1.BigStep
import Imp.HW1.SmallStep

/-!
# CS522 HW1 — aggregate module

Re-exports the three HW1 sub-modules:

* `Imp.HW1.Syntax`   — AST (with `Aexp.errorAr`, `Bexp.errorBool`,
  `Stmt.errorStmt` constants per Ex. 70) and `State`.
* `Imp.HW1.BigStep`  — Exercise 56: big-step `evalA / evalB / evalS / evalP`
  with an `.err` value constructor at each sort.
* `Imp.HW1.SmallStep`— Exercise 70: one-step `stepA / stepB / stepS` and
  their reflexive-transitive closures, in the same namespace as Big-Step
  so both can be used side-by-side.

Source Maude files live in `brando90/cs522` at `master:694db12`, paths:
* `HW1-Maude/imp/0-imp-original/imp-syntax.maude`
* `HW1-Maude/imp/0-imp-original/1-imp-bigstep/imp-semantics-bigstep.maude`
* `HW1-Maude/imp/0-imp-original/3-imp-smallstep/imp-semantics-smallstep.maude`

The narrative and design choices are documented in
`cs522/HW1-Maude/README.md` (course-side) and at the top of each Lean
module below.
-/
