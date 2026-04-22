/-!
# CS522 HW2 — IMP syntax (denotational track)

Lean 4 AST for CS522 Homework 2, Exercise 83 (denotational semantics with
silent division-by-zero failure). Mirrors
`brando90/cs522:HW2-Maude/imp/0-imp-original/imp-syntax.maude`.

Note: unlike HW1's small-step port we do **not** need the syntactic
`errorAr / errorBool / errorStmt` constructors — the HW2 denotational
solution expresses errors via the *value* domain and a reserved `err`
flag in `State`, not via syntax. See `Imp/HW2/Denotational.lean`.
-/

namespace Imp.HW2

/-- Program variable names. -/
abbrev Id := String

/-- Arithmetic expressions — Maude `AExp`. -/
inductive Aexp where
  | const : Int → Aexp
  | var   : Id  → Aexp
  | add   : Aexp → Aexp → Aexp
  | div   : Aexp → Aexp → Aexp
deriving Repr, DecidableEq

/-- Boolean expressions — Maude `BExp`. -/
inductive Bexp where
  | b   : Bool → Bexp
  | le  : Aexp → Aexp → Bexp
  | not : Bexp → Bexp
  | and : Bexp → Bexp → Bexp
deriving Repr, DecidableEq

/-- Statements — Maude `Stmt`. `skip` plays the role of the empty block `{}`. -/
inductive Stmt where
  | skip   : Stmt
  | assign : Id → Aexp → Stmt
  | seq    : Stmt → Stmt → Stmt
  | ite    : Bexp → Stmt → Stmt → Stmt
  | while  : Bexp → Stmt → Stmt
deriving Repr, DecidableEq

/-- A complete IMP program — Maude `int Xl ; S`. -/
structure Pgm where
  vars : List Id
  body : Stmt
deriving Repr

/-- Program state: partial map from variable names to integers.
`none` = undefined binding. -/
abbrev State := Id → Option Int

namespace State

/-- Empty state — no variables bound. -/
def empty : State := fun _ => none

/-- Point-wise update `σ[n/X]`. -/
def update (σ : State) (X : Id) (n : Int) : State :=
  fun Y => if Y = X then some n else σ Y

/-- Initialise a list of variables all to 0 (matches Maude `Xl |-> 0`). -/
def initZero : List Id → State
  | []      => empty
  | X :: Xs => (initZero Xs).update X 0

end State

/-! ## The silent-failure "err" flag

The HW2 Maude solution introduces a reserved `op err : -> Id .` that is
never declared by the user and is used in the denotational equations as a
"silent-failure" flag: when a Stmt would otherwise diverge on an
arithmetic `Error`, the equation instead commits to `sigma & err |-> 1`.

In Lean, since `Id` is just `String`, we pick a reserved string that user
programs are expected not to use. The test battery in `my_test.maude`
matches `red appCPO([[err]], x |-> 3 & err |-> 1)` against our `"__err__"`. -/

/-- Reserved identifier used as a silent-failure flag in the HW2 denotation. -/
def errId : Id := "__err__"

/-- A state has *silently failed* if the reserved `err` identifier is bound
to `1`. -/
def State.isFailed (σ : State) : Prop := σ errId = some 1

/-- Mark a state as silently failed — the Maude move `sigma & err |-> 1`. -/
def State.markFailed (σ : State) : State := σ.update errId 1

@[simp] theorem State.markFailed_isFailed (σ : State) :
    (σ.markFailed).isFailed := by
  unfold State.isFailed State.markFailed State.update
  simp [errId]

end Imp.HW2
