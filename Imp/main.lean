/-!
# IMP — core syntax and big-step semantics

This file defines the abstract syntax of the IMP imperative language
(arithmetic expressions `Aexp`, boolean expressions `Bexp`, commands `Com`)
together with its big-step operational semantics (the `terminate` relation),
plus the standard meta-theorems:

* `Aexp.eval` / `Bexp.eval` — denotational evaluation of pure expressions.
* `Com.terminate σ c τ` — "command `c`, started in state `σ`, terminates in `τ`".
* `terminate_unique` — big-step evaluation is deterministic.
* `halt` / `output` — total/partial views of the semantics on an `Option State`,
  useful for composing programs that may diverge.
* `terminate_skip`, `terminate_assign`, `terminate_comp`, `terminate_ite`,
  `terminate_while` — inversion/introduction characterisations used as
  `simp` lemmas to drive concrete termination proofs.
-/

import Mathlib.Tactic

namespace Imp

/-- Variable names are strings. -/
abbrev Str := String

/-- Arithmetic expressions: integer constants, variables, and the binary
operations `+`, `-`, `*`. Pure (no side effects); evaluated in a `State`
by `Aexp.eval`. -/
inductive Aexp where
  | const : ℤ → Aexp
  | var : Str → Aexp
  | add : Aexp → Aexp → Aexp
  | sub : Aexp → Aexp → Aexp
  | mul : Aexp → Aexp → Aexp
deriving Repr, DecidableEq

-- Build an AST of the variable x: "x"
def x : Aexp := Aexp.var "x"

-- Build an AST of "x + y"
def x_add_y : Aexp := Aexp.add (Aexp.var "x") (Aexp.var "y")

/-- Boolean expressions: `true`/`false`, the relational tests `=` and `≤`
on `Aexp`, and the propositional connectives `¬`, `∧`, `∨`. Evaluated in a
`State` by `Bexp.eval`. -/
inductive Bexp where
  | true : Bexp
  | false : Bexp
  | eq : Aexp → Aexp → Bexp
  | le : Aexp → Aexp → Bexp
  | neg : Bexp → Bexp
  | and : Bexp → Bexp → Bexp
  | or : Bexp → Bexp → Bexp
deriving Repr, DecidableEq

/-- IMP commands: `skip` (no-op), assignment `x := a`, sequencing `c ; d`
(built as `comp c d`), `if b then c else d`, and `while b do c`.
Meaning is given by the `terminate` relation below. -/
inductive Com where
  | skip : Com
  | assign : Str → Aexp → Com
  | comp : Com → Com → Com
  | ite : Bexp → Com → Com → Com
  | while : Bexp → Com → Com
deriving Repr, DecidableEq

-- Build an AST of the command `while true do x := x + 1` — an infinite
-- loop whose body increments x by 1 on every iteration.
-- AST:
--   (while)
--     (Bexp.true)
--     (Com.assign "x" (Aexp.add (Aexp.var "x") (Aexp.const 1)))
def while_true_add_1 : Com :=
  Com.while Bexp.true
    (Com.assign "x" (Aexp.add (Aexp.var "x") (Aexp.const 1)))

/-- A program state is a total map from variable names to integer values.
Uninitialised variables take whatever value the caller supplies
(see e.g. `zero_state = fun _ => 0` in `Imp/example.lean`). -/
abbrev State := Str → ℤ

namespace Aexp

/-- Denotational evaluation of arithmetic expressions in a state. -/
def eval (σ : State) : Aexp → ℤ
  | const n => n
  | var X => σ X
  | add a b => eval σ a + eval σ b
  | sub a b => eval σ a - eval σ b
  | mul a b => eval σ a * eval σ b

/-- Two `Aexp`s are equivalent if they evaluate to the same integer in
every state. -/
def equiv (a b : Aexp) : Prop := ∀ (σ : State), eval σ a = eval σ b

end Aexp

namespace Bexp

/-- Denotational evaluation of boolean expressions in a state. -/
def eval (σ : State) : Bexp → Bool
  | true => Bool.true
  | false => Bool.false
  | eq a b => decide ((Aexp.eval σ a) = (Aexp.eval σ b))
  | le a b => decide ((Aexp.eval σ a) ≤ (Aexp.eval σ b))
  | neg a => !(eval σ a)
  | and a b => (eval σ a) && (eval σ b)
  | or a b => (eval σ a) || (eval σ b)

/-- Two `Bexp`s are equivalent if they evaluate to the same `Bool` in
every state. -/
def equiv (a b : Bexp) : Prop := ∀ (σ : State), eval σ a = eval σ b

end Bexp

/-- Point-wise update: `σ.assign X m` is the state that agrees with `σ`
everywhere except at `X`, where it returns `m`. -/
def State.assign (σ : State) (X : Str) (m : ℤ) : State :=
  fun Y => if Y = X then m else σ Y

namespace Com

/-- Big-step operational semantics. `terminate σ c τ` reads "running command
`c` in starting state `σ` finishes in state `τ`".

* `skip`        — does nothing.
* `assign X a`  — updates `X` to `a.eval σ`.
* `comp c d`    — run `c`, then run `d` from the intermediate state.
* `ite_true/false` — take the `then`/`else` branch based on the guard.
* `while_true`  — guard holds; run body, then re-enter the loop.
* `while_false` — guard fails; loop terminates in place.

Only terminating runs are reachable; non-termination corresponds to the
absence of any derivation (`¬ halt' σ c`). -/
inductive terminate : State → Com → State → Prop
  | skip (σ : State) : terminate σ skip σ
  | assign (σ : State) (X : Str) (a : Aexp) : terminate σ (assign X a) (σ.assign X (a.eval σ))
  | comp {c d : Com} {ρ σ τ : State} (_ : terminate ρ c σ) (_ : terminate σ d τ) :
    terminate ρ (comp c d) τ
  | ite_true {b : Bexp} {c d : Com} {ρ σ : State} (_ : terminate ρ c σ)
    (_ : b.eval ρ = Bool.true) : terminate ρ (ite b c d) σ
  | ite_false {b : Bexp} {c d : Com} {ρ σ : State} (_ : terminate ρ d σ)
    (_ : b.eval ρ = Bool.false) : terminate ρ (ite b c d) σ
  | while_true {b : Bexp} {ρ σ τ : State} {c : Com} (_ : b.eval ρ = Bool.true)
    (_ : terminate ρ c σ) (_ : terminate σ (Com.while b c) τ) : terminate ρ (Com.while b c) τ
  | while_false {b : Bexp} {σ : State} {c : Com} (_ : b.eval σ = Bool.false) :
    terminate σ (Com.while b c) σ

/-- Two commands are equivalent if they have the same input/output
behaviour on every starting state. -/
def equiv (c d : Com) : Prop := ∀ (σ τ : State), terminate σ c τ ↔ terminate σ d τ

/-- `halt' σ c` : the run of `c` from `σ` terminates in *some* state. -/
def halt' (σ : State) (c : Com) : Prop := ∃ τ : State, terminate σ c τ

/-- The output of running `c` from an `Option State`. `none` propagates as
`none`; from `some σ`, returns `some τ` where `τ` is a `terminate`-successor
if one exists (via classical choice), else `none`. `terminate_unique` makes
the chosen `τ` unique up to propositional equality. Noncomputable because of
`Classical.choose`. -/
open Classical in
noncomputable def output (σ' : Option State) (c : Com) : Option State := match σ' with
  | some σ => if p : halt' σ c then some (Classical.choose p) else none
  | none => none

/-- `halt σ' c` lifts `halt'` through `Option State`: a `none` input never
halts. Useful when chaining commands whose individual runs might diverge. -/
def halt (σ' : Option State) (c : Com) : Prop := match σ' with
  | some σ => halt' σ c
  | none => False

/-- Sanity check that non-termination is actually observable: the program
`while true do skip` never terminates, from any starting state. -/
example (σ τ : State) : ¬ Com.terminate σ (Com.while Bexp.true Com.skip) τ := by
  suffices ∀ (c : Com), c.terminate σ τ → c ≠ (Com.while Bexp.true Com.skip) by
    intro h
    exact this (Com.while Bexp.true Com.skip) h rfl
  intro c p
  induction p with
  | skip _ =>
      intro h; cases h
  | assign _ _ _ =>
      intro h; cases h
  | comp _ _ _ _ =>
      intro h; cases h
  | ite_true _ _ _ =>
      intro h; cases h
  | ite_false _ _ _ =>
      intro h; cases h
  | while_false hb =>
      intro h; cases h; simp [Bexp.eval] at hb
  | while_true _ _ _ _ _ =>
      intro h'
      contradiction

end Com

open Com

/-!
## Inversion/introduction lemmas for `terminate`

Each of the following `terminate_*` lemmas rewrites `terminate σ c τ` into
an equivalent, more-usable form for every shape of `c` (`skip`, `assign`,
`comp`, `ite`, `while`). Tagged `@[simp]` where the rewrite is strictly
progressing; otherwise invoked manually. Together with
`terminate_unique` they drive most concrete proofs in `Imp/example.lean`.
-/

@[simp]
theorem terminate_skip {σ τ : State} : terminate σ skip τ ↔ τ = σ := by
  constructor <;> intro h
  · match h with
      | terminate.skip _ => rfl
  · rw [h]
    exact terminate.skip σ

@[simp]
theorem terminate_assign {σ τ : State} {X : Str} {a : Aexp} :
    terminate σ (assign X a) τ ↔ τ = σ.assign X (a.eval σ) := by
  constructor <;> intro h
  · match h with
      | terminate.assign _ _ _ => rfl
  · rw [h]
    exact terminate.assign σ X a

theorem terminate_comp {σ τ : State} {c d : Com} :
    terminate σ (c.comp d) τ ↔ ∃ ρ : State, terminate σ c ρ ∧ terminate ρ d τ := by
  constructor <;> intro h
  · match h with
      | terminate.comp _ _ =>
        expose_names
        use σ_1
  · obtain ⟨ρ, h⟩ := h
    exact terminate.comp h.1 h.2

theorem terminate_ite {b : Bexp} {c d : Com} {σ τ : State} :
    terminate σ (ite b c d) τ ↔ if b.eval σ then terminate σ c τ else terminate σ d τ := by
  constructor <;> intro h
  · match h with
      | terminate.ite_true h1 h2 =>
        simp only [h2, ↓reduceIte]; exact h1
      | terminate.ite_false h1 h2 =>
        simp only [h2, Bool.false_eq_true, ↓reduceIte]; exact h1
  · cases h' : Bexp.eval σ b with
      | true =>
        simp only [h', ↓reduceIte] at h; exact terminate.ite_true h h'
      | false =>
        simp only [h', Bool.false_eq_true, ↓reduceIte] at h; exact terminate.ite_false h h'

theorem terminate_while {b : Bexp} {c : Com} {σ τ : State} :
    terminate σ (Com.while b c) τ ↔ if b.eval σ then
    ∃ ρ : State, terminate σ c ρ ∧ terminate ρ (Com.while b c) τ else τ = σ := by
  constructor <;> intro h
  · match h with
      | terminate.while_true h _ _ =>
        expose_names
        simp only [h, ↓reduceIte]
        use σ_1
      | terminate.while_false h => simp [h]
  · cases h' : Bexp.eval σ b with
      | true =>
        simp only [h', ↓reduceIte] at h
        obtain ⟨ρ, h1, h2⟩ := h
        exact terminate.while_true h' h1 h2
      | false =>
        simp only [h', Bool.false_eq_true, ↓reduceIte] at h; rw [h]; exact terminate.while_false h'

/-- Big-step semantics is **deterministic**: if `c` terminates from `σ` in
both `τ` and `τ'`, then `τ = τ'`. Proof is by induction on `h'`, with the
`terminate_*` inversion lemmas supplying the outer case analysis. -/
theorem terminate_unique {σ τ τ' : State} {c : Com} (h : terminate σ c τ) (h' : terminate σ c τ') :
    τ = τ' := by
  induction h' generalizing τ with
    | skip =>
      rw [terminate_skip] at h; exact h
    | assign =>
      rw [terminate_assign] at h; exact h
    | comp h1 h2 ih1 ih2 =>
      expose_names
      rw [terminate_comp] at h
      obtain ⟨ρ_1, h_1, h_2⟩ := h
      rw [← ih1 h_1] at ih2
      exact ih2 h_2
    | ite_true =>
      expose_names
      rw [terminate_ite] at h
      simp only [h_2, ↓reduceIte] at h
      exact x_ih h
    | ite_false =>
      expose_names
      rw [terminate_ite] at h
      simp only [h_2, Bool.false_eq_true, ↓reduceIte] at h
      exact x_ih h
    | while_true =>
      expose_names
      rw [terminate_while] at h
      simp only [h_1, ↓reduceIte] at h
      obtain ⟨ρ_1, h_4, h_5⟩ := h
      rw [← x_ih h_4] at x_ih_1
      exact x_ih_1 h_5
    | while_false =>
      expose_names
      rw [terminate_while] at h
      simp only [h_1, Bool.false_eq_true, ↓reduceIte] at h
      exact h

theorem halt_some {σ : State} {c : Com} : halt σ c ↔ halt' σ c := by rfl

theorem halt_iff_output_isSome {σ : State} {c : Com} : halt σ c ↔ (output σ c).isSome := by
  constructor <;> intro h
  · dsimp [halt] at h
    rw [output]
    simp [h]
  · dsimp [halt]
    dsimp [output] at h
    by_cases h' : halt' σ c
    · exact h'
    · exfalso
      simp [h'] at h

theorem terminate_output {σ τ : State} {c : Com} (h : terminate σ c τ) : output σ c = some τ := by
  match h' : output σ c with
    | some ρ =>
      simp only [Option.some.injEq]
      have : halt' σ c := by use τ
      dsimp [output] at h'
      simp only [this, ↓reduceDIte, Option.some.injEq] at h'
      rw [← h']
      symm
      apply terminate_unique h
      exact (Classical.indefiniteDescription (terminate σ c) (of_eq_true (eq_true this))).property
    | none =>
      exfalso
      dsimp [output] at h'
      have : halt' σ c := by use τ
      simp [this] at h'

@[simp]
theorem halt_skip (σ : State) : halt σ skip := by
  use σ
  exact terminate.skip σ

@[simp]
theorem halt_assign (σ : State) (X : Str) (a : Aexp) : halt σ (assign X a) := by
  use σ.assign X (a.eval σ)
  exact terminate.assign σ X a

@[simp]
theorem halt_comp (σ : State) (c d : Com) :
    halt σ (comp c d) ↔ halt σ c ∧ halt (output σ c) d := by
  constructor <;> intro h
  · obtain ⟨ρ, h⟩ := h
    rw [terminate_comp] at h
    obtain ⟨τ, h1, h2⟩ := h
    use (by use τ)
    rw [terminate_output h1]
    use ρ
  · obtain ⟨h1, h2⟩ := h
    dsimp [halt] at h1 ⊢
    obtain ⟨ρ, h1⟩ := h1
    rw [terminate_output h1] at h2
    dsimp [halt] at h2
    obtain ⟨τ, h2⟩ := h2
    use τ
    exact terminate.comp h1 h2

@[simp]
theorem halt_ite (σ : State) (b : Bexp) (c d : Com) :
    halt σ (ite b c d) ↔ if b.eval σ then halt σ c else halt σ d := by
  constructor <;> intro h
  · obtain ⟨ρ, h⟩ := h
    rw [terminate_ite] at h
    cases h' : Bexp.eval σ b with
      | true =>
        simp only [↓reduceIte]; use ρ; simp only [h', ↓reduceIte] at h; exact h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]; use ρ; simp only [h', Bool.false_eq_true,
          ↓reduceIte] at h; exact h
  · cases h' : Bexp.eval σ b with
      | true =>
        simp only [h', ↓reduceIte] at h
        obtain ⟨ρ, h⟩ := h
        use ρ
        rw [terminate_ite]
        simp only [h', ↓reduceIte]
        exact h
      | false =>
        simp only [h', Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨ρ, h⟩ := h
        use ρ
        rw [terminate_ite]
        simp only [h', Bool.false_eq_true, ↓reduceIte]
        exact h

theorem halt_while (σ : State) (b : Bexp) (c : Com) :
    halt σ (Com.while b c) ↔
    if b.eval σ then halt σ c ∧ halt (output σ c) (Com.while b c) else True := by
  constructor <;> intro h
  · obtain ⟨ρ, h⟩ := h
    rw [terminate_while] at h
    cases h' : b.eval σ with
      | true =>
        simp only [↓reduceIte]
        simp only [h', ↓reduceIte] at h
        obtain ⟨τ, h1, h2⟩ := h
        use (by use τ)
        rw [terminate_output h1]
        use ρ
      | false => simp
  · cases h' : b.eval σ with
      | true =>
        simp only [h', ↓reduceIte] at h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨ρ, h1⟩ := h1
        rw [terminate_output h1] at h2
        dsimp [halt] at h2
        obtain ⟨τ, h2⟩ := h2
        dsimp [halt]
        use τ
        exact terminate.while_true h' h1 h2
      | false =>
        use σ; rw [terminate_while]; simp [h']

@[simp]
theorem output_skip {σ' : Option State} : output σ' skip = σ' := by
  match σ' with
    | some σ => exact terminate_output (terminate.skip σ)
    | none => rfl

@[simp]
theorem output_assign {σ : State} {X : Str} {a : Aexp} :
    output σ (assign X a) = (σ.assign X (a.eval σ)) := by
  exact terminate_output (terminate.assign σ X a)

end Imp
