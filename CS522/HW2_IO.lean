/-
  CS522 HW2: IMP + Input/Output
  ==============================
  Extension 2: Add read() and print(e) to IMP.

  This extension adds I/O operations:
  - `read()` is an arithmetic expression that consumes the next integer from
    the input stream
  - `print(a)` is a command that evaluates `a` and appends the result to the
    output stream

  Changes from base IMP:
  - Aexp gains `read` constructor
  - Com gains `print` constructor
  - Configuration expands from just State to (State × Input × Output)
    where Input = List ℤ and Output = List ℤ
  - Expression evaluation becomes (Config → ℤ × Config) since read()
    consumes input
  - All semantic rules must thread the I/O buffers

  Key difficulty: The configuration change from State to Config propagates
  through EVERY semantic rule, even those that don't use I/O. This is a
  major illustration of the "extensibility problem" in semantics.
-/
import Mathlib.Tactic

namespace CS522.IMPIO

abbrev Loc := String
abbrev State := Loc → ℤ

def State.update (σ : State) (x : Loc) (v : ℤ) : State :=
  fun y => if y = x then v else σ y

-- ============================================================================
-- I/O Configuration
-- ============================================================================

/-- Input stream: a list of integers waiting to be read. -/
abbrev Input := List ℤ

/-- Output stream: a list of integers that have been printed. -/
abbrev Output := List ℤ

/-- A configuration bundles state with I/O streams. -/
structure Config where
  state : State
  input : Input
  output : Output
deriving Repr

-- ============================================================================
-- Syntax (changed: Aexp gains `read`, Com gains `print`)
-- ============================================================================

/-- Arithmetic expressions with `read()`. -/
inductive Aexp where
  | const : ℤ → Aexp
  | var : Loc → Aexp
  | add : Aexp → Aexp → Aexp
  | sub : Aexp → Aexp → Aexp
  | mul : Aexp → Aexp → Aexp
  | div : Aexp → Aexp → Aexp
  | read : Aexp                  -- NEW: reads from input stream
deriving Repr, DecidableEq

/-- Boolean expressions (unchanged structurally but evaluation changes). -/
inductive Bexp where
  | true : Bexp
  | false : Bexp
  | eq : Aexp → Aexp → Bexp
  | le : Aexp → Aexp → Bexp
  | neg : Bexp → Bexp
  | and : Bexp → Bexp → Bexp
  | or : Bexp → Bexp → Bexp
deriving Repr, DecidableEq

/-- Commands with `print`. -/
inductive Com where
  | skip : Com
  | assign : Loc → Aexp → Com
  | seq : Com → Com → Com
  | ite : Bexp → Com → Com → Com
  | while : Bexp → Com → Com
  | print : Aexp → Com          -- NEW: print(a) outputs value of a
deriving Repr, DecidableEq

-- ============================================================================
-- Expression evaluation (now operates on Config for I/O)
-- ============================================================================

/-- Evaluate an arithmetic expression. Returns value and updated config.
    read() consumes the head of the input stream; if input is empty, returns 0. -/
def Aexp.eval (cfg : Config) : Aexp → ℤ × Config
  | const n => (n, cfg)
  | var x => (cfg.state x, cfg)
  | add a b =>
    let (v₁, cfg₁) := eval cfg a
    let (v₂, cfg₂) := eval cfg₁ b
    (v₁ + v₂, cfg₂)
  | sub a b =>
    let (v₁, cfg₁) := eval cfg a
    let (v₂, cfg₂) := eval cfg₁ b
    (v₁ - v₂, cfg₂)
  | mul a b =>
    let (v₁, cfg₁) := eval cfg a
    let (v₂, cfg₂) := eval cfg₁ b
    (v₁ * v₂, cfg₂)
  | div a b =>
    let (v₁, cfg₁) := eval cfg a
    let (v₂, cfg₂) := eval cfg₁ b
    (if v₂ = 0 then 0 else v₁ / v₂, cfg₂)
  | read =>                       -- NEW: consume from input
    match cfg.input with
    | [] => (0, cfg)              -- empty input → default to 0
    | v :: rest => (v, { cfg with input := rest })

/-- Evaluate a boolean expression, threading I/O config. -/
def Bexp.eval (cfg : Config) : Bexp → Bool × Config
  | .true => (Bool.true, cfg)
  | .false => (Bool.false, cfg)
  | eq a b =>
    let (v₁, cfg₁) := Aexp.eval cfg a
    let (v₂, cfg₂) := Aexp.eval cfg₁ b
    (decide (v₁ = v₂), cfg₂)
  | le a b =>
    let (v₁, cfg₁) := Aexp.eval cfg a
    let (v₂, cfg₂) := Aexp.eval cfg₁ b
    (decide (v₁ ≤ v₂), cfg₂)
  | neg b =>
    let (v, cfg') := eval cfg b
    (!v, cfg')
  | and b₁ b₂ =>
    let (v₁, cfg₁) := eval cfg b₁
    let (v₂, cfg₂) := eval cfg₁ b₂
    (v₁ && v₂, cfg₂)
  | or b₁ b₂ =>
    let (v₁, cfg₁) := eval cfg b₁
    let (v₂, cfg₂) := eval cfg₁ b₂
    (v₁ || v₂, cfg₂)

-- ============================================================================
-- Big-step operational semantics (on Config instead of State)
-- ============================================================================

/-- Big-step semantics for IMP with I/O.
    Judgment form: ⟨c, cfg⟩ ⇓ cfg' -/
inductive Com.BigStep : Config → Com → Config → Prop where
  | skip (cfg : Config) :
      BigStep cfg .skip cfg
  | assign {cfg cfg' : Config} {x : Loc} {a : Aexp} {v : ℤ}
      (ha : Aexp.eval cfg a = (v, cfg')) :
      BigStep cfg (.assign x a) { cfg' with state := cfg'.state.update x v }
  | seq {c₁ c₂ : Com} {cfg cfg' cfg'' : Config}
      (h₁ : BigStep cfg c₁ cfg') (h₂ : BigStep cfg' c₂ cfg'') :
      BigStep cfg (.seq c₁ c₂) cfg''
  | ite_true {b : Bexp} {c₁ c₂ : Com} {cfg cfg_b cfg' : Config}
      (hb : Bexp.eval cfg b = (Bool.true, cfg_b)) (h : BigStep cfg_b c₁ cfg') :
      BigStep cfg (.ite b c₁ c₂) cfg'
  | ite_false {b : Bexp} {c₁ c₂ : Com} {cfg cfg_b cfg' : Config}
      (hb : Bexp.eval cfg b = (Bool.false, cfg_b)) (h : BigStep cfg_b c₂ cfg') :
      BigStep cfg (.ite b c₁ c₂) cfg'
  | while_true {b : Bexp} {c : Com} {cfg cfg_b cfg' cfg'' : Config}
      (hb : Bexp.eval cfg b = (Bool.true, cfg_b))
      (hc : BigStep cfg_b c cfg') (hw : BigStep cfg' (.while b c) cfg'') :
      BigStep cfg (.while b c) cfg''
  | while_false {b : Bexp} {c : Com} {cfg cfg_b : Config}
      (hb : Bexp.eval cfg b = (Bool.false, cfg_b)) :
      BigStep cfg (.while b c) cfg_b
  | print {cfg cfg' : Config} {a : Aexp} {v : ℤ}       -- NEW
      (ha : Aexp.eval cfg a = (v, cfg')) :
      BigStep cfg (.print a) { cfg' with output := cfg'.output ++ [v] }

notation "⟨" c ", " cfg "⟩ ⇓ " cfg' => Com.BigStep cfg c cfg'

-- ============================================================================
-- Determinism
-- ============================================================================

/-- Determinism still holds for IMP with I/O. -/
theorem BigStep_deterministic {cfg cfg₁ cfg₂ : Config} {c : Com}
    (h₁ : ⟨c, cfg⟩ ⇓ cfg₁) (h₂ : ⟨c, cfg⟩ ⇓ cfg₂) : cfg₁ = cfg₂ := by
  induction h₁ generalizing cfg₂ with
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
  | print ha =>
    cases h₂ with
    | print ha' => rw [ha] at ha'; cases ha'; rfl

-- ============================================================================
-- Example: read two numbers, print their sum
-- ============================================================================

/-- Program: x := read(); y := read(); print(x + y) -/
def add_program : Com :=
  .seq (.assign "x" .read)
    (.seq (.assign "y" .read)
      (.print (.add (.var "x") (.var "y"))))

/-- The add_program with input [3, 5] outputs [8]. -/
example : ∃ cfg', ⟨add_program, ⟨fun _ => 0, [3, 5], []⟩⟩ ⇓ cfg' ∧ cfg'.output = [8] := by
  refine ⟨_, ?_, rfl⟩
  unfold add_program
  apply Com.BigStep.seq
  · exact Com.BigStep.assign (by simp [Aexp.eval])
  · apply Com.BigStep.seq
    · apply Com.BigStep.assign
      simp [Aexp.eval, State.update]
    · apply Com.BigStep.print
      simp [Aexp.eval, State.update]

end CS522.IMPIO
