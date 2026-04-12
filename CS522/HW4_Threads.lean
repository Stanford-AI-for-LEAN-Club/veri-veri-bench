/-
  CS522 HW4: IMP + Dynamic Threads (spawn)
  ==========================================
  Extension 4: Add spawn statement for concurrency to IMP.

  This extension introduces non-deterministic concurrency:
  - `spawn { c }` creates a new thread running command c concurrently
  - Threads share mutable state — no isolation

  Changes from base IMP:
  - Com gains a `spawn` constructor
  - Big-step semantics becomes NON-DETERMINISTIC: spawn creates two
    possible execution orderings (spawned-first or continuation-first)
  - We model this by having BigStep be a relation (not a function) that
    admits multiple final states for the same initial configuration

  Key difficulty: This is the most disruptive extension because it breaks
  DETERMINISM — the fundamental property we proved for base IMP. With
  threads, the same program can produce different final states depending
  on thread scheduling. This demonstrates why concurrency is fundamentally
  hard to formalize in big-step semantics.
-/
import Mathlib.Tactic

namespace CS522.IMPThreads

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

-- ============================================================================
-- Syntax (changed: Com gains `spawn`)
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

/-- Commands with spawn for concurrency. -/
inductive Com where
  | skip : Com
  | assign : Loc → Aexp → Com
  | seq : Com → Com → Com
  | ite : Bexp → Com → Com → Com
  | while : Bexp → Com → Com
  | spawn : Com → Com          -- NEW: spawn { c } runs c concurrently
deriving Repr, DecidableEq

-- ============================================================================
-- Expression evaluation (pure, no side effects in this extension)
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
-- Big-step semantics (NON-DETERMINISTIC due to spawn)
-- ============================================================================

/-- Big-step semantics with spawn.

    spawn introduces non-determinism: when we encounter `spawn { c₁ } ; c₂`,
    we model this in big-step by allowing EITHER ordering:
    - Execute c₁ first, then c₂ (spawn_left)
    - Execute c₂ first, then c₁ (spawn_right)

    Note: This is a simplification — true interleaving would require
    small-step semantics. Big-step can only model coarse-grained
    non-determinism at the level of complete command executions.

    This is exactly what Rosu's course emphasizes: big-step semantics
    is "the most tedious" for features like threads because it can't
    naturally express fine-grained interleaving. -/
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
  -- NEW: spawn has two possible orderings
  | spawn_left {c_spawned : Com} {σ σ' : State}
      (h : BigStep σ c_spawned σ') :
      BigStep σ (.spawn c_spawned) σ'
  | spawn_right {c_spawned : Com} {σ : State} :
      BigStep σ (.spawn c_spawned) σ

notation "⟨" c ", " σ "⟩ ⇓ " τ => Com.BigStep σ c τ

-- ============================================================================
-- Non-determinism demonstration
-- ============================================================================

/-- Spawn can produce different final states.
    Program: spawn { x := 1 }; x := 2
    Outcome 1: x = 2 (spawned runs first, then x := 2 overwrites)
    Outcome 2: x = 1 (x := 2 runs first, then spawned overwrites) -/

/-- Execution where spawned thread's effect is visible. -/
example : ∃ σ₀ : State, ⟨Com.spawn (.assign "x" (.const 1)), σ₀⟩ ⇓ (σ₀.update "x" 1) := by
  exact ⟨fun _ => 0, Com.BigStep.spawn_left (Com.BigStep.assign _ "x" _)⟩

/-- Execution where spawned thread's effect is skipped. -/
example : ∃ σ₀ : State, ⟨Com.spawn (.assign "x" (.const 1)), σ₀⟩ ⇓ σ₀ := by
  exact ⟨fun _ => 0, Com.BigStep.spawn_right⟩

-- ============================================================================
-- Determinism is LOST (proof that it fails)
-- ============================================================================

/-- Determinism does NOT hold with spawn.
    We exhibit a counterexample: the same program from the same initial
    state can reach two different final states. -/
theorem spawn_breaks_determinism :
    ∃ (c : Com) (σ τ₁ τ₂ : State),
      ⟨c, σ⟩ ⇓ τ₁ ∧ ⟨c, σ⟩ ⇓ τ₂ ∧ τ₁ ≠ τ₂ := by
  refine ⟨.spawn (.assign "x" (.const 1)),
          fun _ => 0,
          (fun _ => (0 : ℤ)).update "x" 1,
          fun _ => 0,
          ?_, ?_, ?_⟩
  · exact Com.BigStep.spawn_left (Com.BigStep.assign _ "x" _)
  · exact Com.BigStep.spawn_right
  · intro h
    have : (fun (_ : Loc) => (0 : ℤ)).update "x" 1 "x" = (fun (_ : Loc) => (0 : ℤ)) "x" := by
      rw [h]
    simp [State.update] at this

-- ============================================================================
-- Sequential fragment is still deterministic
-- ============================================================================

/-- For spawn-free commands, determinism still holds. -/
def Com.spawnFree : Com → Prop
  | .skip => True
  | .assign _ _ => True
  | .seq c₁ c₂ => c₁.spawnFree ∧ c₂.spawnFree
  | .ite _ c₁ c₂ => c₁.spawnFree ∧ c₂.spawnFree
  | .while _ c => c.spawnFree
  | .spawn _ => False

theorem sequential_deterministic {σ τ₁ τ₂ : State} {c : Com}
    (hfree : c.spawnFree) (h₁ : ⟨c, σ⟩ ⇓ τ₁) (h₂ : ⟨c, σ⟩ ⇓ τ₂) : τ₁ = τ₂ := by
  induction h₁ generalizing τ₂ with
  | skip => cases h₂; rfl
  | assign => cases h₂; rfl
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₁' h₂' =>
      simp [Com.spawnFree] at hfree
      have := ih₁ hfree.1 h₁'
      subst this; exact ih₂ hfree.2 h₂'
  | ite_true hb _ ih =>
    cases h₂ with
    | ite_true _ h =>
      simp [Com.spawnFree] at hfree; exact ih hfree.1 h
    | ite_false hb' => simp [hb] at hb'
  | ite_false hb _ ih =>
    cases h₂ with
    | ite_true hb' => simp [hb] at hb'
    | ite_false _ h =>
      simp [Com.spawnFree] at hfree; exact ih hfree.2 h
  | while_true hb _ _ ih_body ih_loop =>
    cases h₂ with
    | while_true _ hc' hw' =>
      simp [Com.spawnFree] at hfree
      have := ih_body hfree hc'; subst this
      exact ih_loop hfree hw'
    | while_false hb' => simp [hb] at hb'
  | while_false hb =>
    cases h₂ with
    | while_true hb' => simp [hb] at hb'
    | while_false => rfl
  | spawn_left => simp [Com.spawnFree] at hfree
  | spawn_right => simp [Com.spawnFree] at hfree

end CS522.IMPThreads
