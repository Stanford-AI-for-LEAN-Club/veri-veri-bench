/-
  CS522 HW3: IMP + Abrupt Termination
  =====================================
  Extension 3: Add halt statement and division-by-zero error to IMP.

  This extension introduces abrupt (abnormal) termination:
  - `halt` statement: immediately terminates the entire program
  - Division by zero: causes the program to abort with an error

  Changes from base IMP:
  - Com gains a `halt` constructor
  - The big-step semantics result becomes `Outcome` (either normal termination
    with a state, or abnormal termination/error)
  - Division by zero in Aexp.eval can produce an error
  - Sequential composition, loops, and conditionals must propagate errors

  Key difficulty: The result type changes from State to Outcome, which
  requires restructuring every semantic rule to handle the error case.
  This is another instance of the "one feature requires touching everything"
  problem in language semantics.
-/
import Mathlib.Tactic

namespace CS522.IMPAbort

abbrev Loc := String
abbrev State := Loc → ℤ

def State.update (σ : State) (x : Loc) (v : ℤ) : State :=
  fun y => if y = x then v else σ y

-- ============================================================================
-- Outcome: normal vs abnormal termination
-- ============================================================================

/-- An outcome is either normal termination with a final state,
    or an error (from halt or division-by-zero). -/
inductive Outcome where
  | normal : State → Outcome
  | error : Outcome
deriving Repr, DecidableEq

-- ============================================================================
-- Syntax (changed: Com gains `halt`, Aexp has division)
-- ============================================================================

inductive Aexp where
  | const : ℤ → Aexp
  | var : Loc → Aexp
  | add : Aexp → Aexp → Aexp
  | sub : Aexp → Aexp → Aexp
  | mul : Aexp → Aexp → Aexp
  | div : Aexp → Aexp → Aexp
deriving Repr, DecidableEq

inductive Bexp where
  | true : Bexp
  | false : Bexp
  | eq : Aexp → Aexp → Bexp
  | le : Aexp → Aexp → Bexp
  | neg : Bexp → Bexp
  | and : Bexp → Bexp → Bexp
  | or : Bexp → Bexp → Bexp
deriving Repr, DecidableEq

/-- Commands with halt. -/
inductive Com where
  | skip : Com
  | assign : Loc → Aexp → Com
  | seq : Com → Com → Com
  | ite : Bexp → Com → Com → Com
  | while : Bexp → Com → Com
  | halt : Com                  -- NEW: abrupt termination
deriving Repr, DecidableEq

-- ============================================================================
-- Expression evaluation (now returns Option to handle div-by-zero)
-- ============================================================================

/-- Evaluate an arithmetic expression. Returns none on division by zero. -/
def Aexp.eval (σ : State) : Aexp → Option ℤ
  | const n => some n
  | var x => some (σ x)
  | add a b => do
    let v₁ ← eval σ a
    let v₂ ← eval σ b
    return v₁ + v₂
  | sub a b => do
    let v₁ ← eval σ a
    let v₂ ← eval σ b
    return v₁ - v₂
  | mul a b => do
    let v₁ ← eval σ a
    let v₂ ← eval σ b
    return v₁ * v₂
  | div a b => do
    let v₁ ← eval σ a
    let v₂ ← eval σ b
    if v₂ = 0 then none          -- division by zero → error
    else return v₁ / v₂

/-- Evaluate a boolean expression. Returns none if an arithmetic
    sub-expression causes division by zero. -/
def Bexp.eval (σ : State) : Bexp → Option Bool
  | .true => some Bool.true
  | .false => some Bool.false
  | eq a b => do
    let v₁ ← Aexp.eval σ a
    let v₂ ← Aexp.eval σ b
    return decide (v₁ = v₂)
  | le a b => do
    let v₁ ← Aexp.eval σ a
    let v₂ ← Aexp.eval σ b
    return decide (v₁ ≤ v₂)
  | neg b => do
    let v ← eval σ b
    return !v
  | and b₁ b₂ => do
    let v₁ ← eval σ b₁
    let v₂ ← eval σ b₂
    return (v₁ && v₂)
  | or b₁ b₂ => do
    let v₁ ← eval σ b₁
    let v₂ ← eval σ b₂
    return (v₁ || v₂)

-- ============================================================================
-- Big-step operational semantics (result is Outcome, not State)
-- ============================================================================

/-- Big-step semantics with outcomes.
    ⟨c, σ⟩ ⇓ o where o ∈ {normal(τ), error}. -/
inductive Com.BigStep : State → Com → Outcome → Prop where
  | skip (σ : State) :
      BigStep σ .skip (.normal σ)
  | assign {σ : State} {x : Loc} {a : Aexp} {v : ℤ}
      (ha : Aexp.eval σ a = some v) :
      BigStep σ (.assign x a) (.normal (σ.update x v))
  | assign_err {σ : State} {x : Loc} {a : Aexp}
      (ha : Aexp.eval σ a = none) :
      BigStep σ (.assign x a) .error
  | seq_normal {c₁ c₂ : Com} {σ σ' : State} {o : Outcome}
      (h₁ : BigStep σ c₁ (.normal σ')) (h₂ : BigStep σ' c₂ o) :
      BigStep σ (.seq c₁ c₂) o
  | seq_error {c₁ c₂ : Com} {σ : State}
      (h₁ : BigStep σ c₁ .error) :
      BigStep σ (.seq c₁ c₂) .error
  | ite_true {b : Bexp} {c₁ c₂ : Com} {σ : State} {o : Outcome}
      (hb : Bexp.eval σ b = some Bool.true) (h : BigStep σ c₁ o) :
      BigStep σ (.ite b c₁ c₂) o
  | ite_false {b : Bexp} {c₁ c₂ : Com} {σ : State} {o : Outcome}
      (hb : Bexp.eval σ b = some Bool.false) (h : BigStep σ c₂ o) :
      BigStep σ (.ite b c₁ c₂) o
  | ite_err {b : Bexp} {c₁ c₂ : Com} {σ : State}
      (hb : Bexp.eval σ b = none) :
      BigStep σ (.ite b c₁ c₂) .error
  | while_true {b : Bexp} {c : Com} {σ σ' : State} {o : Outcome}
      (hb : Bexp.eval σ b = some Bool.true)
      (hc : BigStep σ c (.normal σ')) (hw : BigStep σ' (.while b c) o) :
      BigStep σ (.while b c) o
  | while_body_err {b : Bexp} {c : Com} {σ : State}
      (hb : Bexp.eval σ b = some Bool.true)
      (hc : BigStep σ c .error) :
      BigStep σ (.while b c) .error
  | while_false {b : Bexp} {c : Com} {σ : State}
      (hb : Bexp.eval σ b = some Bool.false) :
      BigStep σ (.while b c) (.normal σ)
  | while_guard_err {b : Bexp} {c : Com} {σ : State}
      (hb : Bexp.eval σ b = none) :
      BigStep σ (.while b c) .error
  | halt_step (σ : State) :                              -- NEW
      BigStep σ .halt .error

notation "⟨" c ", " σ "⟩ ⇓ " o => Com.BigStep σ c o

-- ============================================================================
-- Determinism
-- ============================================================================

/-- Determinism still holds with abrupt termination. -/
theorem BigStep_deterministic {σ : State} {c : Com} {o₁ o₂ : Outcome}
    (h₁ : ⟨c, σ⟩ ⇓ o₁) (h₂ : ⟨c, σ⟩ ⇓ o₂) : o₁ = o₂ := by
  induction h₁ generalizing o₂ with
  | skip => cases h₂; rfl
  | assign ha =>
    cases h₂ with
    | assign ha' => rw [ha] at ha'; cases ha'; rfl
    | assign_err ha' => rw [ha] at ha'; cases ha'
  | assign_err ha =>
    cases h₂ with
    | assign ha' => rw [ha] at ha'; cases ha'
    | assign_err => rfl
  | seq_normal _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq_normal h₁' h₂' =>
      have := ih₁ h₁'; cases this; exact ih₂ h₂'
    | seq_error h₁' =>
      have := ih₁ h₁'; cases this
  | seq_error _ ih₁ =>
    cases h₂ with
    | seq_normal h₁' _ =>
      have := ih₁ h₁'; cases this
    | seq_error h₁' => exact ih₁ h₁'
  | ite_true hb _ ih =>
    cases h₂ with
    | ite_true _ h => exact ih h
    | ite_false hb' => rw [hb] at hb'; cases hb'
    | ite_err hb' => rw [hb] at hb'; cases hb'
  | ite_false hb _ ih =>
    cases h₂ with
    | ite_true hb' => rw [hb] at hb'; cases hb'
    | ite_false _ h => exact ih h
    | ite_err hb' => rw [hb] at hb'; cases hb'
  | ite_err hb =>
    cases h₂ with
    | ite_true hb' => rw [hb] at hb'; cases hb'
    | ite_false hb' => rw [hb] at hb'; cases hb'
    | ite_err => rfl
  | while_true hb _ _ ih_body ih_loop =>
    cases h₂ with
    | while_true hb' hc' hw' =>
      rw [hb] at hb'; cases hb'
      have := ih_body hc'; cases this
      exact ih_loop hw'
    | while_body_err hb' hc' =>
      rw [hb] at hb'; cases hb'
      have := ih_body hc'; cases this
    | while_false hb' => rw [hb] at hb'; cases hb'
    | while_guard_err hb' => rw [hb] at hb'; cases hb'
  | while_body_err hb _ ih_body =>
    cases h₂ with
    | while_true hb' hc' _ =>
      rw [hb] at hb'; cases hb'
      have := ih_body hc'; cases this
    | while_body_err hb' hc' =>
      rw [hb] at hb'; cases hb'
      exact ih_body hc'
    | while_false hb' => rw [hb] at hb'; cases hb'
    | while_guard_err hb' => rw [hb] at hb'; cases hb'
  | while_false hb =>
    cases h₂ with
    | while_true hb' => rw [hb] at hb'; cases hb'
    | while_body_err hb' => rw [hb] at hb'; cases hb'
    | while_false => rfl
    | while_guard_err hb' => rw [hb] at hb'; cases hb'
  | while_guard_err hb =>
    cases h₂ with
    | while_true hb' => rw [hb] at hb'; cases hb'
    | while_body_err hb' => rw [hb] at hb'; cases hb'
    | while_false hb' => rw [hb] at hb'; cases hb'
    | while_guard_err => rfl
  | halt_step => cases h₂; rfl

-- ============================================================================
-- Examples
-- ============================================================================

/-- halt immediately produces error. -/
example (σ : State) : ⟨Com.halt, σ⟩ ⇓ Outcome.error := by
  exact Com.BigStep.halt_step σ

/-- halt in a sequence aborts the rest. -/
example (σ : State) :
    ⟨Com.seq .halt (.assign "x" (.const 42)), σ⟩ ⇓ Outcome.error := by
  exact Com.BigStep.seq_error (Com.BigStep.halt_step σ)

/-- Division by zero produces error. -/
example (σ : State) :
    ⟨Com.assign "x" (.div (.const 1) (.const 0)), σ⟩ ⇓ Outcome.error := by
  apply Com.BigStep.assign_err
  simp [Aexp.eval]

/-- Normal division works fine. -/
example (σ : State) :
    ⟨Com.assign "x" (.div (.const 10) (.const 2)), σ⟩ ⇓
      Outcome.normal (σ.update "x" 5) := by
  apply Com.BigStep.assign
  simp [Aexp.eval]

end CS522.IMPAbort
