/-!
# CS522 HW1 — IMP syntax (with division + error constants)

Lean 4 port of the IMP abstract syntax used for CS522 Homework 1
(Exercise 56 big-step division-by-zero + Exercise 70 small-step
division-by-zero).

The corresponding Maude files in `brando90/cs522` at `master:694db12` are:

- `HW1-Maude/imp/0-imp-original/imp-syntax.maude`  — original IMP syntax
- `HW1-Maude/imp/state.maude`                       — `State` module
- `HW1-Maude/imp/0-imp-original/1-imp-bigstep/imp-semantics-bigstep.maude`
  (Ex. 56 — adds the `Error : -> State` constant)
- `HW1-Maude/imp/0-imp-original/3-imp-smallstep/imp-semantics-smallstep.maude`
  (Ex. 70 — adds `errorAr : -> AExp`, `errorBool : -> BExp`,
  `errorStmt : -> Stmt`)

## Design choices in Lean

* The big-step Maude solution uses `Error : -> State`, which in Lean we
  model via a separate value domain (`AVal / BVal / SVal` in `BigStep.lean`)
  rather than by extending `State`. This keeps `State : Id → Option Int` as
  a total partial map and matches the textbook's "either a number-result
  or a pure error-result" phrasing.
* The small-step Maude solution introduces a syntactic error constant at
  each sort. We model those faithfully by extending `Aexp`/`Bexp`/`Stmt`
  with `errorAr`/`errorBool`/`errorStmt` constructors. They are only used
  as intermediate terms in the `stepA / stepB / stepS` reductions, but
  Ex. 56 / big-step never builds an error term syntactically — it uses
  the value-level `AVal.err` constructors instead.
-/

namespace Imp.HW1

/-- Program variable names — unconstrained strings, per the Maude spec. -/
abbrev Id := String

/-- Arithmetic expressions.

Original course fragment: `Int`, `Id`, `_+_`, `_/_`. We add `errorAr` as a
syntactic error constant so small-step (Ex. 70) can reduce a failed
sub-expression to it. Big-step never needs to construct `errorAr` in syntax —
it uses `AVal.err` in its value domain (see `BigStep.lean`). -/
inductive Aexp where
  | const   : Int → Aexp
  | var     : Id  → Aexp
  | add     : Aexp → Aexp → Aexp
  | div     : Aexp → Aexp → Aexp
  | errorAr : Aexp
deriving Repr, DecidableEq

/-- Boolean expressions. Add `errorBool` for Ex. 70. -/
inductive Bexp where
  | b         : Bool → Bexp
  | le        : Aexp → Aexp → Bexp
  | not       : Bexp → Bexp
  | and       : Bexp → Bexp → Bexp
  | errorBool : Bexp
deriving Repr, DecidableEq

/-- Statements. Add `errorStmt` for Ex. 70. The empty block `{}` of the
course grammar becomes `skip` here. -/
inductive Stmt where
  | skip      : Stmt
  | assign    : Id → Aexp → Stmt
  | seq       : Stmt → Stmt → Stmt
  | ite       : Bexp → Stmt → Stmt → Stmt
  | while     : Bexp → Stmt → Stmt
  | errorStmt : Stmt
deriving Repr, DecidableEq

/-- A complete IMP program: a list of declared variables and a body. Maude
syntax: `int xl ; s`. -/
structure Pgm where
  vars : List Id
  body : Stmt
deriving Repr

/-- Program state — partial map from variable names to integers.
`none` models an undefined binding, matching Maude's `Sigma(X) = undefined`. -/
abbrev State := Id → Option Int

namespace State

/-- Empty state — no variables bound. -/
def empty : State := fun _ => none

/-- Point-wise update `σ[n/X]`. -/
def update (σ : State) (X : Id) (n : Int) : State :=
  fun Y => if Y = X then some n else σ Y

/-- Initialise a list of variables all to 0 (matches Maude's `Xl |-> 0`). -/
def initZero : List Id → State
  | []      => empty
  | X :: Xs => (initZero Xs).update X 0

end State

end Imp.HW1
