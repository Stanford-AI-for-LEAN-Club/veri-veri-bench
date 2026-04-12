/-
  CS522 HW0: Base IMP Language
  =============================
  This is the baseline IMP language from Grigore Rosu's CS522 course at UIUC.
  It serves as the foundation that all subsequent homework extensions build upon.

  Language features:
  - Arithmetic expressions: constants, variables, +, -, *, /
  - Boolean expressions: true, false, =, <=, !, &&, ||
  - Commands: skip, assignment, sequential composition, if-then-else, while

  Semantic approach: Big-step operational semantics (natural semantics)

  This file re-exports and extends Stefan's original IMP formalization from Imp.main
  with division added (needed for HW4's division-by-zero extension).
-/
import Mathlib.Tactic

namespace CS522.IMP

-- ============================================================================
-- Syntax
-- ============================================================================

abbrev Loc := String

/-- Arithmetic expressions with integer division (needed for later extensions). -/
inductive Aexp where
  | const : ℤ → Aexp
  | var : Loc → Aexp
  | add : Aexp → Aexp → Aexp
  | sub : Aexp → Aexp → Aexp
  | mul : Aexp → Aexp → Aexp
  | div : Aexp → Aexp → Aexp
deriving Repr, DecidableEq

/-- Boolean expressions. -/
inductive Bexp where
  | true : Bexp
  | false : Bexp
  | eq : Aexp → Aexp → Bexp
  | le : Aexp → Aexp → Bexp
  | neg : Bexp → Bexp
  | and : Bexp → Bexp → Bexp
  | or : Bexp → Bexp → Bexp
deriving Repr, DecidableEq

/-- Commands (statements). -/
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
    (σ.update x v) x = v := by
  simp [State.update]

@[simp]
theorem State.update_other (σ : State) (x y : Loc) (v : ℤ) (h : y ≠ x) :
    (σ.update x v) y = σ y := by
  simp [State.update, h]

-- ============================================================================
-- Evaluation functions (denotational-style)
-- ============================================================================

/-- Evaluate an arithmetic expression. Division by zero returns 0. -/
def Aexp.eval (σ : State) : Aexp → ℤ
  | const n => n
  | var x => σ x
  | add a b => eval σ a + eval σ b
  | sub a b => eval σ a - eval σ b
  | mul a b => eval σ a * eval σ b
  | div a b => if eval σ b = 0 then 0 else eval σ a / eval σ b

/-- Evaluate a boolean expression. -/
def Bexp.eval (σ : State) : Bexp → Bool
  | .true => Bool.true
  | .false => Bool.false
  | eq a b => decide (Aexp.eval σ a = Aexp.eval σ b)
  | le a b => decide (Aexp.eval σ a ≤ Aexp.eval σ b)
  | neg b => !(eval σ b)
  | and b₁ b₂ => eval σ b₁ && eval σ b₂
  | or b₁ b₂ => eval σ b₁ || eval σ b₂

-- ============================================================================
-- Big-step operational semantics
-- ============================================================================

/-- Big-step semantics: ⟨c, σ⟩ ⇓ τ means command c started in state σ terminates
    with final state τ. -/
inductive Com.BigStep : State → Com → State → Prop where
  | skip (σ : State) :
      BigStep σ .skip σ
  | assign (σ : State) (x : Loc) (a : Aexp) :
      BigStep σ (.assign x a) (σ.update x (a.eval σ))
  | seq {c₁ c₂ : Com} {σ σ' τ : State}
      (h₁ : BigStep σ c₁ σ') (h₂ : BigStep σ' c₂ τ) :
      BigStep σ (.seq c₁ c₂) τ
  | ite_true {b : Bexp} {c₁ c₂ : Com} {σ τ : State}
      (hb : b.eval σ = Bool.true) (h : BigStep σ c₁ τ) :
      BigStep σ (.ite b c₁ c₂) τ
  | ite_false {b : Bexp} {c₁ c₂ : Com} {σ τ : State}
      (hb : b.eval σ = Bool.false) (h : BigStep σ c₂ τ) :
      BigStep σ (.ite b c₁ c₂) τ
  | while_true {b : Bexp} {c : Com} {σ σ' τ : State}
      (hb : b.eval σ = Bool.true) (hc : BigStep σ c σ')
      (hw : BigStep σ' (.while b c) τ) :
      BigStep σ (.while b c) τ
  | while_false {b : Bexp} {c : Com} {σ : State}
      (hb : b.eval σ = Bool.false) :
      BigStep σ (.while b c) σ

notation "⟨" c ", " σ "⟩ ⇓ " τ => Com.BigStep σ c τ

-- ============================================================================
-- Semantic equivalence
-- ============================================================================

def Aexp.equiv (a b : Aexp) : Prop := ∀ σ, a.eval σ = b.eval σ
def Bexp.equiv (a b : Bexp) : Prop := ∀ σ, a.eval σ = b.eval σ
def Com.equiv (c d : Com) : Prop := ∀ σ τ, ⟨c, σ⟩ ⇓ τ ↔ ⟨d, σ⟩ ⇓ τ

-- ============================================================================
-- Core theorems
-- ============================================================================

/-- Determinism: big-step semantics produces a unique final state. -/
theorem BigStep_deterministic {σ τ₁ τ₂ : State} {c : Com}
    (h₁ : ⟨c, σ⟩ ⇓ τ₁) (h₂ : ⟨c, σ⟩ ⇓ τ₂) : τ₁ = τ₂ := by
  induction h₁ generalizing τ₂ with
  | skip => cases h₂; rfl
  | assign => cases h₂; rfl
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₁' h₂' =>
      have := ih₁ h₁'
      subst this
      exact ih₂ h₂'
  | ite_true hb _ ih =>
    cases h₂ with
    | ite_true _ h => exact ih h
    | ite_false hb' => simp [hb] at hb'
  | ite_false hb _ ih =>
    cases h₂ with
    | ite_true hb' => simp [hb] at hb'
    | ite_false _ h => exact ih h
  | while_true hb _ _ ih_body ih_loop =>
    cases h₂ with
    | while_true _ hc' hw' =>
      have := ih_body hc'
      subst this
      exact ih_loop hw'
    | while_false hb' => simp [hb] at hb'
  | while_false hb =>
    cases h₂ with
    | while_true hb' => simp [hb] at hb'
    | while_false => rfl

/-- Skip is a left identity for sequential composition. -/
theorem skip_seq (c : Com) : Com.equiv (.seq .skip c) c := by
  intro σ τ
  constructor
  · intro h; cases h with | seq h₁ h₂ => cases h₁; exact h₂
  · intro h; exact Com.BigStep.seq (Com.BigStep.skip σ) h

/-- Skip is a right identity for sequential composition. -/
theorem seq_skip (c : Com) : Com.equiv (.seq c .skip) c := by
  intro σ τ
  constructor
  · intro h; cases h with | seq h₁ h₂ => cases h₂; exact h₁
  · intro h; exact Com.BigStep.seq h (Com.BigStep.skip τ)

/-- While loop unrolling equivalence. -/
theorem while_unfold (b : Bexp) (c : Com) :
    Com.equiv (.while b c) (.ite b (.seq c (.while b c)) .skip) := by
  intro σ τ
  constructor
  · intro h
    cases h with
    | while_true hb hc hw =>
      exact Com.BigStep.ite_true hb (Com.BigStep.seq hc hw)
    | while_false hb =>
      exact Com.BigStep.ite_false hb (Com.BigStep.skip σ)
  · intro h
    cases h with
    | ite_true hb h =>
      cases h with
      | seq hc hw => exact Com.BigStep.while_true hb hc hw
    | ite_false hb h =>
      cases h; exact Com.BigStep.while_false hb

/-- Non-termination of while true do skip. -/
theorem while_true_skip_diverges (σ τ : State) :
    ¬ ⟨Com.while .true .skip, σ⟩ ⇓ τ := by
  intro h
  suffices ∀ c, ⟨c, σ⟩ ⇓ τ → c ≠ Com.while .true .skip by
    exact this _ h rfl
  intro c heval
  induction heval with
  | skip => intro h; cases h
  | assign => intro h; cases h
  | seq => intro h; cases h
  | ite_true => intro h; cases h
  | ite_false => intro h; cases h
  | while_false hb => intro h; cases h; simp [Bexp.eval] at hb
  | while_true _ _ _ _ ih_loop => intro h; exact ih_loop h

end CS522.IMP
