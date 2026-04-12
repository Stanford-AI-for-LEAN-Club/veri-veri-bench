/-
  CS522 HW1: IMP + Variable Increment
  ====================================
  Extension 1: Add variable increment (++x) to IMP.

  This is the first IMP extension from Rosu's CS522 course. The key insight is
  that ++x introduces SIDE EFFECTS into expressions — the expression both
  evaluates to a value AND modifies the state. This breaks the clean separation
  between expressions (pure) and commands (stateful) that base IMP enjoys.

  Changes from base IMP:
  - Aexp gains a new constructor: `incr : Loc → Aexp` representing ++x
  - Aexp.eval now returns (ℤ × State) instead of just ℤ, since evaluation
    can modify the state
  - The big-step semantics must thread state through expression evaluation

  Key difficulty for formalization:
  - Expression evaluation is no longer a function from State → ℤ; it's a
    relation (or a function returning a pair) because of side effects
  - This is exactly the kind of "small change" that requires large edits
    to the formalization — the core argument PL semanticists make about
    why real language semantics are hard to maintain
-/
import Mathlib.Tactic

namespace CS522.IMPIncr

abbrev Loc := String

-- ============================================================================
-- Syntax (changed: Aexp gains `incr`)
-- ============================================================================

/-- Arithmetic expressions, now with variable increment.
    `incr x` evaluates to (σ(x) + 1) and updates σ(x) := σ(x) + 1. -/
inductive Aexp where
  | const : ℤ → Aexp
  | var : Loc → Aexp
  | add : Aexp → Aexp → Aexp
  | sub : Aexp → Aexp → Aexp
  | mul : Aexp → Aexp → Aexp
  | div : Aexp → Aexp → Aexp
  | incr : Loc → Aexp          -- NEW: ++x
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

inductive Com where
  | skip : Com
  | assign : Loc → Aexp → Com
  | seq : Com → Com → Com
  | ite : Bexp → Com → Com → Com
  | while : Bexp → Com → Com
deriving Repr, DecidableEq

-- ============================================================================
-- State
-- ============================================================================

abbrev State := Loc → ℤ

def State.update (σ : State) (x : Loc) (v : ℤ) : State :=
  fun y => if y = x then v else σ y

@[simp]
theorem State.update_same (σ : State) (x : Loc) (v : ℤ) :
    (σ.update x v) x = v := by simp [State.update]

@[simp]
theorem State.update_other (σ : State) (x y : Loc) (v : ℤ) (h : y ≠ x) :
    (σ.update x v) y = σ y := by simp [State.update, h]

-- ============================================================================
-- Expression evaluation (CHANGED: now returns value AND new state)
-- ============================================================================

/-- Evaluate an arithmetic expression, returning the value and the
    (possibly modified) state. The state changes when we encounter `incr x`.

    NOTE: This is the KEY change — in base IMP, Aexp.eval was State → ℤ.
    Now it's State → ℤ × State. This single change cascades through the
    entire formalization. -/
def Aexp.eval (σ : State) : Aexp → ℤ × State
  | const n => (n, σ)
  | var x => (σ x, σ)
  | add a b =>
    let (v₁, σ₁) := eval σ a
    let (v₂, σ₂) := eval σ₁ b    -- left-to-right evaluation order
    (v₁ + v₂, σ₂)
  | sub a b =>
    let (v₁, σ₁) := eval σ a
    let (v₂, σ₂) := eval σ₁ b
    (v₁ - v₂, σ₂)
  | mul a b =>
    let (v₁, σ₁) := eval σ a
    let (v₂, σ₂) := eval σ₁ b
    (v₁ * v₂, σ₂)
  | div a b =>
    let (v₁, σ₁) := eval σ a
    let (v₂, σ₂) := eval σ₁ b
    (if v₂ = 0 then 0 else v₁ / v₂, σ₂)
  | incr x =>                     -- NEW: ++x increments and returns new value
    let v := σ x + 1
    (v, σ.update x v)

/-- Evaluate a boolean expression, threading state through for ++x in
    arithmetic subexpressions. -/
def Bexp.eval (σ : State) : Bexp → Bool × State
  | .true => (Bool.true, σ)
  | .false => (Bool.false, σ)
  | eq a b =>
    let (v₁, σ₁) := Aexp.eval σ a
    let (v₂, σ₂) := Aexp.eval σ₁ b
    (decide (v₁ = v₂), σ₂)
  | le a b =>
    let (v₁, σ₁) := Aexp.eval σ a
    let (v₂, σ₂) := Aexp.eval σ₁ b
    (decide (v₁ ≤ v₂), σ₂)
  | neg b =>
    let (v, σ') := eval σ b
    (!v, σ')
  | and b₁ b₂ =>
    let (v₁, σ₁) := eval σ b₁
    let (v₂, σ₂) := eval σ₁ b₂
    (v₁ && v₂, σ₂)
  | or b₁ b₂ =>
    let (v₁, σ₁) := eval σ b₁
    let (v₂, σ₂) := eval σ₁ b₂
    (v₁ || v₂, σ₂)

-- ============================================================================
-- Big-step operational semantics (CHANGED: expression evaluation threads state)
-- ============================================================================

/-- Big-step semantics for IMP with increment.
    The key change: assignment and conditionals must account for the state
    changes caused by evaluating expressions with side effects. -/
inductive Com.BigStep : State → Com → State → Prop where
  | skip (σ : State) :
      BigStep σ .skip σ
  | assign {σ σ' : State} {x : Loc} {a : Aexp}
      (ha : Aexp.eval σ a = (v, σ')) :
      BigStep σ (.assign x a) (σ'.update x v)
  | seq {c₁ c₂ : Com} {σ σ' τ : State}
      (h₁ : BigStep σ c₁ σ') (h₂ : BigStep σ' c₂ τ) :
      BigStep σ (.seq c₁ c₂) τ
  | ite_true {b : Bexp} {c₁ c₂ : Com} {σ σ' τ : State}
      (hb : Bexp.eval σ b = (Bool.true, σ')) (h : BigStep σ' c₁ τ) :
      BigStep σ (.ite b c₁ c₂) τ
  | ite_false {b : Bexp} {c₁ c₂ : Com} {σ σ' τ : State}
      (hb : Bexp.eval σ b = (Bool.false, σ')) (h : BigStep σ' c₂ τ) :
      BigStep σ (.ite b c₁ c₂) τ
  | while_true {b : Bexp} {c : Com} {σ σ_b σ' τ : State}
      (hb : Bexp.eval σ b = (Bool.true, σ_b))
      (hc : BigStep σ_b c σ') (hw : BigStep σ' (.while b c) τ) :
      BigStep σ (.while b c) τ
  | while_false {b : Bexp} {c : Com} {σ σ' : State}
      (hb : Bexp.eval σ b = (Bool.false, σ')) :
      BigStep σ (.while b c) σ'

notation "⟨" c ", " σ "⟩ ⇓ " τ => Com.BigStep σ c τ

-- ============================================================================
-- Determinism (still holds — increment is deterministic)
-- ============================================================================

/-- Determinism: big-step semantics still produces a unique final state,
    even with side-effectful expressions. The proof is structurally similar
    to base IMP but must handle the paired return values. -/
theorem BigStep_deterministic {σ τ₁ τ₂ : State} {c : Com}
    (h₁ : ⟨c, σ⟩ ⇓ τ₁) (h₂ : ⟨c, σ⟩ ⇓ τ₂) : τ₁ = τ₂ := by
  induction h₁ generalizing τ₂ with
  | skip => cases h₂; rfl
  | assign ha =>
    cases h₂ with
    | assign ha' => rw [ha] at ha'; cases ha'; rfl
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₁' h₂' =>
      have := ih₁ h₁'; subst this; exact ih₂ h₂'
  | ite_true hb _ ih =>
    cases h₂ with
    | ite_true hb' h => rw [hb] at hb'; cases hb'; exact ih h
    | ite_false hb' => rw [hb] at hb'; cases hb'
  | ite_false hb _ ih =>
    cases h₂ with
    | ite_true hb' => rw [hb] at hb'; cases hb'
    | ite_false hb' h => rw [hb] at hb'; cases hb'; exact ih h
  | while_true hb _ _ ih_body ih_loop =>
    cases h₂ with
    | while_true hb' hc' hw' =>
      rw [hb] at hb'; cases hb'
      have := ih_body hc'; subst this
      exact ih_loop hw'
    | while_false hb' => rw [hb] at hb'; cases hb'
  | while_false hb =>
    cases h₂ with
    | while_true hb' => rw [hb] at hb'; cases hb'
    | while_false hb' => rw [hb] at hb'; cases hb'; rfl

-- ============================================================================
-- Examples demonstrating increment semantics
-- ============================================================================

/-- Example: ++x where x=5 evaluates to 6 and updates x to 6. -/
example : Aexp.eval (fun _ => 5) (.incr "x") = (6, (fun _ => 5).update "x" 6) := by
  simp [Aexp.eval, State.update]

/-- Example: (++x) + (++x) where x=0 evaluates to 1+2=3 with x=2.
    This demonstrates left-to-right evaluation order. -/
example : Aexp.eval (fun _ => 0) (.add (.incr "x") (.incr "x"))
    = (3, ((fun _ => (0 : ℤ)).update "x" 1).update "x" 2) := by
  simp [Aexp.eval, State.update]
  ring_nf
  constructor
  · ring
  · ext y; simp [State.update]; split <;> omega

end CS522.IMPIncr
