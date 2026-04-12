/-
  CS522 HW6: IMP++ (All Extensions Combined)
  ============================================
  This is the final combined language IMP++ from Rosu's CS522 course.
  It integrates ALL five individual extensions into one language:

  1. Variable increment (++x) — side effects in expressions
  2. Input/Output (read, print) — I/O streams
  3. Abrupt termination (halt, div-by-zero) — error handling
  4. Dynamic threads (spawn) — non-deterministic concurrency
  5. Local variables (blocks) — lexical scoping

  This file is the "experiment" — we want to see how hard it is to combine
  all features into one coherent semantics. The answer, as Rosu emphasizes
  in CS522, is that big-step semantics is "the most tedious" approach for
  this task because every extension touches the judgment form and
  configuration.

  Configuration: (State × Input × Output × Outcome)
  where Outcome ∈ {normal, halted, error}
-/
import Mathlib.Tactic

namespace CS522.IMPPlusPlus

-- ============================================================================
-- Basic types
-- ============================================================================

abbrev Loc := String
abbrev State := Loc → ℤ
abbrev Input := List ℤ
abbrev Output := List ℤ

def State.update (σ : State) (x : Loc) (v : ℤ) : State :=
  fun y => if y = x then v else σ y

@[simp]
theorem State.update_same (σ : State) (x : Loc) (v : ℤ) :
    (σ.update x v) x = v := by simp [State.update]

@[simp]
theorem State.update_other (σ : State) (x y : Loc) (v : ℤ) (h : y ≠ x) :
    (σ.update x v) y = σ y := by simp [State.update, h]

-- ============================================================================
-- Configuration
-- ============================================================================

/-- Full configuration: state + I/O buffers. -/
structure Config where
  state : State
  input : Input
  output : Output
deriving Repr

/-- Outcome of program execution. -/
inductive Outcome where
  | normal : Config → Outcome     -- normal termination
  | halted : Config → Outcome     -- halted via `halt` statement
  | error : Outcome               -- runtime error (e.g., division by zero)
deriving Repr

-- ============================================================================
-- Syntax (ALL extensions combined)
-- ============================================================================

/-- Arithmetic expressions with increment and read.
    This combines extensions 1 (increment) and 2 (I/O). -/
inductive Aexp where
  | const : ℤ → Aexp
  | var : Loc → Aexp
  | add : Aexp → Aexp → Aexp
  | sub : Aexp → Aexp → Aexp
  | mul : Aexp → Aexp → Aexp
  | div : Aexp → Aexp → Aexp
  | incr : Loc → Aexp            -- Extension 1: ++x
  | read : Aexp                  -- Extension 2: read()
deriving Repr, DecidableEq

/-- Boolean expressions (structural same, evaluation changes). -/
inductive Bexp where
  | true : Bexp
  | false : Bexp
  | eq : Aexp → Aexp → Bexp
  | le : Aexp → Aexp → Bexp
  | neg : Bexp → Bexp
  | and : Bexp → Bexp → Bexp
  | or : Bexp → Bexp → Bexp
deriving Repr, DecidableEq

/-- Commands with ALL extensions. -/
inductive Com where
  | skip : Com
  | assign : Loc → Aexp → Com
  | seq : Com → Com → Com
  | ite : Bexp → Com → Com → Com
  | while : Bexp → Com → Com
  | print : Aexp → Com           -- Extension 2: print(a)
  | halt : Com                   -- Extension 3: halt
  | spawn : Com → Com            -- Extension 4: spawn { c }
  | block : Loc → Aexp → Com → Com  -- Extension 5: { int x = a; c }
deriving Repr, DecidableEq

-- ============================================================================
-- Expression evaluation
-- Returns Option (ℤ × Config) to handle:
-- - Side effects from ++x (modifies state)
-- - I/O from read() (consumes input)
-- - Errors from division by zero (returns none)
-- ============================================================================

/-- Evaluate an arithmetic expression.
    Returns none on division by zero; otherwise returns value and updated config. -/
def Aexp.eval (cfg : Config) : Aexp → Option (ℤ × Config)
  | const n => some (n, cfg)
  | var x => some (cfg.state x, cfg)
  | add a b => do
    let (v₁, cfg₁) ← eval cfg a
    let (v₂, cfg₂) ← eval cfg₁ b
    return (v₁ + v₂, cfg₂)
  | sub a b => do
    let (v₁, cfg₁) ← eval cfg a
    let (v₂, cfg₂) ← eval cfg₁ b
    return (v₁ - v₂, cfg₂)
  | mul a b => do
    let (v₁, cfg₁) ← eval cfg a
    let (v₂, cfg₂) ← eval cfg₁ b
    return (v₁ * v₂, cfg₂)
  | div a b => do
    let (v₁, cfg₁) ← eval cfg a
    let (v₂, cfg₂) ← eval cfg₁ b
    if v₂ = 0 then none           -- Extension 3: division by zero error
    else return (v₁ / v₂, cfg₂)
  | incr x =>                     -- Extension 1: ++x
    let v := cfg.state x + 1
    some (v, { cfg with state := cfg.state.update x v })
  | read =>                       -- Extension 2: read()
    match cfg.input with
    | [] => some (0, cfg)
    | v :: rest => some (v, { cfg with input := rest })

/-- Evaluate a boolean expression with side effects. -/
def Bexp.eval (cfg : Config) : Bexp → Option (Bool × Config)
  | .true => some (Bool.true, cfg)
  | .false => some (Bool.false, cfg)
  | eq a b => do
    let (v₁, cfg₁) ← Aexp.eval cfg a
    let (v₂, cfg₂) ← Aexp.eval cfg₁ b
    return (decide (v₁ = v₂), cfg₂)
  | le a b => do
    let (v₁, cfg₁) ← Aexp.eval cfg a
    let (v₂, cfg₂) ← Aexp.eval cfg₁ b
    return (decide (v₁ ≤ v₂), cfg₂)
  | neg b => do
    let (v, cfg') ← eval cfg b
    return (!v, cfg')
  | and b₁ b₂ => do
    let (v₁, cfg₁) ← eval cfg b₁
    let (v₂, cfg₂) ← eval cfg₁ b₂
    return (v₁ && v₂, cfg₂)
  | or b₁ b₂ => do
    let (v₁, cfg₁) ← eval cfg b₁
    let (v₂, cfg₂) ← eval cfg₁ b₂
    return (v₁ || v₂, cfg₂)

-- ============================================================================
-- Big-step operational semantics (ALL extensions)
-- ============================================================================

/-- Big-step semantics for the full IMP++ language.

    This combines all five extensions. Key interactions:
    - Expression evaluation can fail (div-by-zero → error)
    - Expression evaluation has side effects (++x, read)
    - halt produces a halted outcome that propagates upward
    - spawn creates non-determinism (two scheduling orders)
    - block creates lexical scope with save/restore

    Judgment form: ⟨c, cfg⟩ ⇓ outcome -/
inductive Com.BigStep : Config → Com → Outcome → Prop where
  -- Base IMP rules (adapted for Config and Outcome)
  | skip (cfg : Config) :
      BigStep cfg .skip (.normal cfg)

  | assign {cfg : Config} {x : Loc} {a : Aexp} {v : ℤ} {cfg' : Config}
      (ha : Aexp.eval cfg a = some (v, cfg')) :
      BigStep cfg (.assign x a) (.normal { cfg' with state := cfg'.state.update x v })

  | assign_err {cfg : Config} {x : Loc} {a : Aexp}
      (ha : Aexp.eval cfg a = none) :
      BigStep cfg (.assign x a) .error

  | seq_normal {c₁ c₂ : Com} {cfg cfg' : Config} {o : Outcome}
      (h₁ : BigStep cfg c₁ (.normal cfg')) (h₂ : BigStep cfg' c₂ o) :
      BigStep cfg (.seq c₁ c₂) o

  | seq_halt {c₁ c₂ : Com} {cfg cfg' : Config}
      (h₁ : BigStep cfg c₁ (.halted cfg')) :
      BigStep cfg (.seq c₁ c₂) (.halted cfg')

  | seq_error {c₁ c₂ : Com} {cfg : Config}
      (h₁ : BigStep cfg c₁ .error) :
      BigStep cfg (.seq c₁ c₂) .error

  | ite_true {b : Bexp} {c₁ c₂ : Com} {cfg cfg' : Config} {o : Outcome}
      (hb : Bexp.eval cfg b = some (Bool.true, cfg')) (h : BigStep cfg' c₁ o) :
      BigStep cfg (.ite b c₁ c₂) o

  | ite_false {b : Bexp} {c₁ c₂ : Com} {cfg cfg' : Config} {o : Outcome}
      (hb : Bexp.eval cfg b = some (Bool.false, cfg')) (h : BigStep cfg' c₂ o) :
      BigStep cfg (.ite b c₁ c₂) o

  | ite_err {b : Bexp} {c₁ c₂ : Com} {cfg : Config}
      (hb : Bexp.eval cfg b = none) :
      BigStep cfg (.ite b c₁ c₂) .error

  | while_true {b : Bexp} {c : Com} {cfg cfg_b cfg' : Config} {o : Outcome}
      (hb : Bexp.eval cfg b = some (Bool.true, cfg_b))
      (hc : BigStep cfg_b c (.normal cfg'))
      (hw : BigStep cfg' (.while b c) o) :
      BigStep cfg (.while b c) o

  | while_body_halt {b : Bexp} {c : Com} {cfg cfg_b cfg' : Config}
      (hb : Bexp.eval cfg b = some (Bool.true, cfg_b))
      (hc : BigStep cfg_b c (.halted cfg')) :
      BigStep cfg (.while b c) (.halted cfg')

  | while_body_err {b : Bexp} {c : Com} {cfg cfg_b : Config}
      (hb : Bexp.eval cfg b = some (Bool.true, cfg_b))
      (hc : BigStep cfg_b c .error) :
      BigStep cfg (.while b c) .error

  | while_false {b : Bexp} {c : Com} {cfg cfg' : Config}
      (hb : Bexp.eval cfg b = some (Bool.false, cfg')) :
      BigStep cfg (.while b c) (.normal cfg')

  | while_guard_err {b : Bexp} {c : Com} {cfg : Config}
      (hb : Bexp.eval cfg b = none) :
      BigStep cfg (.while b c) .error

  -- Extension 2: print
  | print_ok {cfg cfg' : Config} {a : Aexp} {v : ℤ}
      (ha : Aexp.eval cfg a = some (v, cfg')) :
      BigStep cfg (.print a) (.normal { cfg' with output := cfg'.output ++ [v] })

  | print_err {cfg : Config} {a : Aexp}
      (ha : Aexp.eval cfg a = none) :
      BigStep cfg (.print a) .error

  -- Extension 3: halt
  | halt_step (cfg : Config) :
      BigStep cfg .halt (.halted cfg)

  -- Extension 4: spawn (non-deterministic)
  | spawn_exec {c_spawned : Com} {cfg : Config} {o : Outcome}
      (h : BigStep cfg c_spawned o) :
      BigStep cfg (.spawn c_spawned) o

  | spawn_skip {c_spawned : Com} {cfg : Config} :
      BigStep cfg (.spawn c_spawned) (.normal cfg)

  -- Extension 5: block (local variables)
  | block_normal {x : Loc} {a : Aexp} {c : Com}
      {cfg cfg_init cfg' : Config} {v : ℤ}
      (ha : Aexp.eval cfg a = some (v, cfg_init))
      (hc : BigStep { cfg_init with state := cfg_init.state.update x v } c
            (.normal cfg')) :
      BigStep cfg (.block x a c)
        (.normal { cfg' with state := cfg'.state.update x (cfg.state x) })

  | block_halt {x : Loc} {a : Aexp} {c : Com}
      {cfg cfg_init cfg' : Config} {v : ℤ}
      (ha : Aexp.eval cfg a = some (v, cfg_init))
      (hc : BigStep { cfg_init with state := cfg_init.state.update x v } c
            (.halted cfg')) :
      BigStep cfg (.block x a c)
        (.halted { cfg' with state := cfg'.state.update x (cfg.state x) })

  | block_error {x : Loc} {a : Aexp} {c : Com} {cfg cfg_init : Config} {v : ℤ}
      (ha : Aexp.eval cfg a = some (v, cfg_init))
      (hc : BigStep { cfg_init with state := cfg_init.state.update x v } c .error) :
      BigStep cfg (.block x a c) .error

  | block_init_err {x : Loc} {a : Aexp} {c : Com} {cfg : Config}
      (ha : Aexp.eval cfg a = none) :
      BigStep cfg (.block x a c) .error

notation "⟨" c ", " cfg "⟩ ⇓ " o => Com.BigStep cfg c o

-- ============================================================================
-- Properties
-- ============================================================================

/-- Spawn-free predicate for identifying the deterministic fragment. -/
def Com.spawnFree : Com → Prop
  | .skip => True
  | .assign _ _ => True
  | .seq c₁ c₂ => c₁.spawnFree ∧ c₂.spawnFree
  | .ite _ c₁ c₂ => c₁.spawnFree ∧ c₂.spawnFree
  | .while _ c => c.spawnFree
  | .print _ => True
  | .halt => True
  | .spawn _ => False
  | .block _ _ c => c.spawnFree

-- ============================================================================
-- Example: complete IMP++ program
-- ============================================================================

/-- Example IMP++ program demonstrating multiple extensions:
    { int x = read();          -- Extension 5 (block) + Extension 2 (read)
      while (0 <= x) do {
        print(x);              -- Extension 2 (print)
        x := (x - 1)
      };
      if (x = (0 - 1))
        then skip
        else halt              -- Extension 3 (halt)
    }
-/
def countdown_program : Com :=
  .block "x" .read
    (.seq
      (.while (.le (.const 0) (.var "x"))
        (.seq (.print (.var "x"))
              (.assign "x" (.sub (.var "x") (.const 1)))))
      (.ite (.eq (.var "x") (.sub (.const 0) (.const 1)))
        .skip
        .halt))

-- ============================================================================
-- Edit distance analysis
-- ============================================================================

/-!
## Edit Distance Analysis

This is the key experimental observation: how many lines/definitions changed
when combining all extensions vs. base IMP?

### Base IMP (HW0_IMP.lean):
- Aexp: 6 constructors
- Bexp: 7 constructors
- Com: 5 constructors
- State type: Loc → ℤ
- Aexp.eval: State → ℤ (pure function)
- Bexp.eval: State → Bool (pure function)
- BigStep: 7 rules, judgment State → Com → State

### IMP++ (this file):
- Aexp: 8 constructors (+2: incr, read)
- Bexp: 7 constructors (unchanged)
- Com: 9 constructors (+4: print, halt, spawn, block)
- Config type: State × Input × Output (expanded)
- Outcome type: normal | halted | error (new)
- Aexp.eval: Config → Option (ℤ × Config) (3 type changes!)
- Bexp.eval: Config → Option (Bool × Config) (3 type changes!)
- BigStep: 22 rules, judgment Config → Com → Outcome
  - 7 original rules ALL modified (different types)
  - 8 new error/halt propagation rules
  - 7 new extension-specific rules

### Summary of changes:
- Syntax: +6 constructors across AST types
- Types: State → Config, added Outcome, eval return types changed
- Semantic rules: 7 → 22 (3.1x increase)
- Every single original rule was modified
- Core evaluation functions completely rewritten

This validates the PL semantics community's claim: adding features to
big-step semantics requires touching EVERYTHING. The "extensibility problem"
is real and measurable.
-/

end CS522.IMPPlusPlus
