/-
  CS522 HW5: IMP + Local Variables and Blocks
  =============================================
  Extension 5: Add block-scoped local variable declarations to IMP.

  This extension introduces lexical scoping:
  - `{ int x; c }` declares a local variable x initialized to 0, executes c,
    then restores x to its previous value (or removes it)
  - `{ int x = a; c }` declares x initialized to the value of a

  Changes from base IMP:
  - Com gains `block : Loc → Aexp → Com → Com` constructor
  - State semantics must handle variable scope: on block entry, save the
    old value; on block exit, restore it
  - We model this with an explicit environment/store separation, or
    equivalently, by saving and restoring state entries

  Key difficulty: This requires careful handling of variable shadowing.
  The save/restore pattern adds complexity to the semantic rules and
  creates interesting interactions with other extensions (e.g., if a
  spawned thread accesses a local variable, what happens?).
-/
import Mathlib.Tactic

namespace CS522.IMPLocals

abbrev Loc := String
abbrev State := Loc → ℤ

def State.update (σ : State) (x : Loc) (v : ℤ) : State :=
  fun y => if y = x then v else σ y

@[simp]
theorem State.update_same (σ : State) (x : Loc) (v : ℤ) :
    (σ.update x v) x = v := by simp [State.update]

@[simp]
theorem State.update_other (σ : State) (x y : Loc) (v : ℤ) (h : y ≠ x) :
    (σ.update x v) y = σ y := by simp [State.update, h]

/-- Restore variable x in state τ to its value from state σ.
    This is used on block exit to undo local variable declarations. -/
def State.restore (σ τ : State) (x : Loc) : State :=
  τ.update x (σ x)

-- ============================================================================
-- Syntax (changed: Com gains `block`)
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

/-- Commands with block-scoped local variable declarations.
    `block x a c` represents `{ int x = a; c }`. -/
inductive Com where
  | skip : Com
  | assign : Loc → Aexp → Com
  | seq : Com → Com → Com
  | ite : Bexp → Com → Com → Com
  | while : Bexp → Com → Com
  | block : Loc → Aexp → Com → Com  -- NEW: { int x = a; c }
deriving Repr, DecidableEq

-- ============================================================================
-- Expression evaluation (pure)
-- ============================================================================

def Aexp.eval (σ : State) : Aexp → ℤ
  | const n => n
  | var x => σ x
  | add a b => eval σ a + eval σ b
  | sub a b => eval σ a - eval σ b
  | mul a b => eval σ a * eval σ b
  | div a b => if eval σ b = 0 then 0 else eval σ a / eval σ b

def Bexp.eval (σ : State) : Bexp → Bool
  | .true => Bool.true
  | .false => Bool.false
  | eq a b => decide (Aexp.eval σ a = Aexp.eval σ b)
  | le a b => decide (Aexp.eval σ a ≤ Aexp.eval σ b)
  | neg b => !(eval σ b)
  | and b₁ b₂ => eval σ b₁ && eval σ b₂
  | or b₁ b₂ => eval σ b₁ || eval σ b₂

-- ============================================================================
-- Big-step operational semantics (with block scoping)
-- ============================================================================

/-- Big-step semantics with local variables.
    The block rule:
    1. Evaluate the initializer a in the current state σ
    2. Update σ with x := eval(a) to get σ'
    3. Execute the body c in σ'
    4. Restore x to its original value from σ -/
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
  -- NEW: block with local variable
  | block {x : Loc} {a : Aexp} {c : Com} {σ τ : State}
      (hc : BigStep (σ.update x (a.eval σ)) c τ) :
      BigStep σ (.block x a c) (τ.update x (σ x))

notation "⟨" c ", " σ "⟩ ⇓ " τ => Com.BigStep σ c τ

-- ============================================================================
-- Determinism (still holds — blocks are deterministic)
-- ============================================================================

theorem BigStep_deterministic {σ τ₁ τ₂ : State} {c : Com}
    (h₁ : ⟨c, σ⟩ ⇓ τ₁) (h₂ : ⟨c, σ⟩ ⇓ τ₂) : τ₁ = τ₂ := by
  induction h₁ generalizing τ₂ with
  | skip => cases h₂; rfl
  | assign => cases h₂; rfl
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₁' h₂' =>
      have := ih₁ h₁'; subst this; exact ih₂ h₂'
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
      have := ih_body hc'; subst this; exact ih_loop hw'
    | while_false hb' => simp [hb] at hb'
  | while_false hb =>
    cases h₂ with
    | while_true hb' => simp [hb] at hb'
    | while_false => rfl
  | block hc ih =>
    cases h₂ with
    | block hc' => have := ih hc'; subst this; rfl

-- ============================================================================
-- Scoping examples and properties
-- ============================================================================

/-- Example: local variable shadows outer variable.
    { int x = 10; x := x + 1 }
    If x was 0 before, x is 0 after (restored). -/
example : ∀ σ : State,
    ⟨Com.block "x" (.const 10) (.assign "x" (.add (.var "x") (.const 1))), σ⟩ ⇓
      (σ.update "x" (σ "x") : State) := by
  intro σ
  apply Com.BigStep.block
  constructor

/-- The block body can see the local value. -/
example : ∀ σ : State,
    ⟨Com.block "x" (.const 42) .skip, σ⟩ ⇓ (σ.update "x" (σ "x") : State) := by
  intro σ
  exact Com.BigStep.block (Com.BigStep.skip _)

/-- Nested blocks with different variables don't interfere. -/
theorem block_different_vars_commute (σ : State) (v₁ v₂ : ℤ)
    (hne : "x" ≠ "y") :
    ⟨Com.block "x" (.const v₁) (Com.block "y" (.const v₂) .skip), σ⟩ ⇓
      ((σ.update "y" (σ "y")).update "x" (σ "x") : State) := by
  apply Com.BigStep.block
  apply Com.BigStep.block
  exact Com.BigStep.skip _

end CS522.IMPLocals
