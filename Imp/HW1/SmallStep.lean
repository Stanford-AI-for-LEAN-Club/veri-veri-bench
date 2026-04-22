import Imp.HW1.Syntax

/-!
# CS522 HW1 — Exercise 70: small-step semantics with division-by-zero

Faithful Lean 4 port of
`brando90/cs522:HW1-Maude/imp/0-imp-original/3-imp-smallstep/imp-semantics-smallstep.maude`
(modified version, with the three error constants).

Modelling decisions:

* Maude's `errorAr : -> AExp`, `errorBool : -> BExp`, `errorStmt : -> Stmt`
  are modelled as the syntactic constructors `Aexp.errorAr`, `Bexp.errorBool`,
  `Stmt.errorStmt` in `Imp/HW1/Syntax.lean`. They only appear as intermediate
  reduction targets.
* Three one-step relations (`stepA`, `stepB`, `stepS`) correspond to Maude's
  `o < _, _ > => < _, _ >` at each sort, per Figures 3.14/3.15 of Grigore
  Roșu's textbook.
* The Maude small-step rewrite also models a top-level "error sink" under
  `o_`: `errorAr`/`errorBool`/`errorStmt` rewrite to themselves over
  `.State`. We port those sink steps directly as `error_sink`
  constructors, using `State.empty` for Maude's `.State`.
-/

namespace Imp.HW1.Small

open Imp.HW1

/-! ## One-step reductions

One relation per sort, mirroring Maude's `o < _, _ > => < _, _ >` sequents.
Constructor names follow the Maude rule names (`SmallStep-ADD`,
`SmallStep-DIV`, etc.).
-/

/-- Arithmetic one-step: `stepA a σ a' σ'` ≅ Maude `o < a, σ > => < a', σ' >`.
Note: σ' is rarely different from σ at the `AExp` sort (state changes only
on assignment), but we keep the pairing for uniformity with the Maude shape.
-/
inductive stepA : Aexp → State → Aexp → State → Prop
  /-- `SmallStep-On-Errors` — top-level arithmetic error sink. -/
  | error_sink (σ : State) : stepA .errorAr σ .errorAr State.empty
  /-- `SmallStep-Lookup` — defined variable. -/
  | lookup {σ : State} {X : Id} {n : Int}
      (h : σ X = some n) : stepA (.var X) σ (.const n) σ
  /-- `SmallStep-ADD` — reduce left operand, success. -/
  | add_l {a1 a1' a2 : Aexp} {σ : State}
      (h : stepA a1 σ a1' σ) (hne : a1' ≠ .errorAr) :
      stepA (.add a1 a2) σ (.add a1' a2) σ
  /-- `SmallStep-ADD` — left operand errors. -/
  | add_l_err {a1 a1' a2 : Aexp} {σ : State}
      (h : stepA a1 σ a1' σ) (he : a1' = .errorAr) :
      stepA (.add a1 a2) σ .errorAr σ
  /-- `SmallStep-ADD` — reduce right operand, success. -/
  | add_r {a1 a2 a2' : Aexp} {σ : State}
      (h : stepA a2 σ a2' σ) (hne : a2' ≠ .errorAr) :
      stepA (.add a1 a2) σ (.add a1 a2') σ
  /-- `SmallStep-ADD` — right operand errors. -/
  | add_r_err {a1 a2 a2' : Aexp} {σ : State}
      (h : stepA a2 σ a2' σ) (he : a2' = .errorAr) :
      stepA (.add a1 a2) σ .errorAr σ
  /-- `SmallStep-ADD` axiom: value + value. -/
  | add_axiom {n1 n2 : Int} {σ : State} :
      stepA (.add (.const n1) (.const n2)) σ (.const (n1 + n2)) σ
  /-- `SmallStep-DIV` — reduce left operand, success. -/
  | div_l {a1 a1' a2 : Aexp} {σ : State}
      (h : stepA a1 σ a1' σ) (hne : a1' ≠ .errorAr) :
      stepA (.div a1 a2) σ (.div a1' a2) σ
  /-- `SmallStep-DIV` — left operand errors. -/
  | div_l_err {a1 a1' a2 : Aexp} {σ : State}
      (h : stepA a1 σ a1' σ) (he : a1' = .errorAr) :
      stepA (.div a1 a2) σ .errorAr σ
  /-- `SmallStep-DIV` — reduce right operand, success. -/
  | div_r {a1 a2 a2' : Aexp} {σ : State}
      (h : stepA a2 σ a2' σ) (hne : a2' ≠ .errorAr) :
      stepA (.div a1 a2) σ (.div a1 a2') σ
  /-- `SmallStep-DIV` — right operand errors. -/
  | div_r_err {a1 a2 a2' : Aexp} {σ : State}
      (h : stepA a2 σ a2' σ) (he : a2' = .errorAr) :
      stepA (.div a1 a2) σ .errorAr σ
  /-- `SmallStep-DIV` axiom: value / value, non-zero — normal computation. -/
  | div_axiom {n1 n2 : Int} {σ : State} (hne : n2 ≠ 0) :
      stepA (.div (.const n1) (.const n2)) σ (.const (n1 / n2)) σ
  /-- **Ex. 70 headline rule** — value / 0 reduces to `errorAr`.
  Maude: `crl o < I1 / I2, Sigma > => < errorAr, Sigma > if I2 ==Bool 0 .` -/
  | div_by_zero {n1 : Int} {σ : State} :
      stepA (.div (.const n1) (.const 0)) σ .errorAr σ

/-- Boolean one-step. -/
inductive stepB : Bexp → State → Bexp → State → Prop
  /-- `SmallStep-On-Errors` — top-level boolean error sink. -/
  | error_sink (σ : State) : stepB .errorBool σ .errorBool State.empty
  /-- `SmallStep-LEQ-ARG` — reduce left arithmetic operand. -/
  | le_l {a1 a1' a2 : Aexp} {σ : State}
      (h : stepA a1 σ a1' σ) (hne : a1' ≠ .errorAr) :
      stepB (.le a1 a2) σ (.le a1' a2) σ
  /-- `SmallStep-LEQ-ARG` — left arithmetic errors. -/
  | le_l_err {a1 a1' a2 : Aexp} {σ : State}
      (h : stepA a1 σ a1' σ) (he : a1' = .errorAr) :
      stepB (.le a1 a2) σ .errorBool σ
  /-- `SmallStep-LEQ-ARG` — reduce right arithmetic operand.
  Note Maude requires the left to be a value first (strict left-to-right);
  we faithfully encode that by requiring `I1 : Int` (`Aexp.const`) on the left. -/
  | le_r {n1 : Int} {a2 a2' : Aexp} {σ : State}
      (h : stepA a2 σ a2' σ) (hne : a2' ≠ .errorAr) :
      stepB (.le (.const n1) a2) σ (.le (.const n1) a2') σ
  /-- `SmallStep-LEQ-ARG` — right arithmetic errors. -/
  | le_r_err {n1 : Int} {a2 a2' : Aexp} {σ : State}
      (h : stepA a2 σ a2' σ) (he : a2' = .errorAr) :
      stepB (.le (.const n1) a2) σ .errorBool σ
  /-- `SmallStep-LEQ` axiom: value ≤ value. -/
  | le_axiom {n1 n2 : Int} {σ : State} :
      stepB (.le (.const n1) (.const n2)) σ (.b (decide (n1 ≤ n2))) σ
  /-- `SmallStep-Not-Arg`. -/
  | not_arg {b b' : Bexp} {σ : State}
      (h : stepB b σ b' σ) (hne : b' ≠ .errorBool) :
      stepB (.not b) σ (.not b') σ
  /-- `SmallStep-Not-Arg` — body errors. -/
  | not_arg_err {b b' : Bexp} {σ : State}
      (h : stepB b σ b' σ) (he : b' = .errorBool) :
      stepB (.not b) σ .errorBool σ
  /-- `!true => false`. -/
  | not_true {σ : State} : stepB (.not (.b true)) σ (.b false) σ
  /-- `!false => true`. -/
  | not_false {σ : State} : stepB (.not (.b false)) σ (.b true) σ
  /-- `SmallStep-AND` — reduce left operand. -/
  | and_l {b1 b1' b2 : Bexp} {σ : State}
      (h : stepB b1 σ b1' σ) (hne : b1' ≠ .errorBool) :
      stepB (.and b1 b2) σ (.and b1' b2) σ
  /-- `SmallStep-AND` — left errors. -/
  | and_l_err {b1 b1' b2 : Bexp} {σ : State}
      (h : stepB b1 σ b1' σ) (he : b1' = .errorBool) :
      stepB (.and b1 b2) σ .errorBool σ
  /-- `false && b2 => false`. -/
  | and_false {b2 : Bexp} {σ : State} : stepB (.and (.b false) b2) σ (.b false) σ
  /-- `true && b2 => b2`. -/
  | and_true {b2 : Bexp} {σ : State} : stepB (.and (.b true) b2) σ b2 σ

/-- Statement one-step. -/
inductive stepS : Stmt → State → Stmt → State → Prop
  /-- `SmallStep-On-Errors` — top-level statement error sink. -/
  | error_sink (σ : State) : stepS .errorStmt σ .errorStmt State.empty
  /-- `SmallStep-Assign` — reduce RHS, success. -/
  | assign_red {X : Id} {a a' : Aexp} {σ : State}
      (h : stepA a σ a' σ) (hne : a' ≠ .errorAr) :
      stepS (.assign X a) σ (.assign X a') σ
  /-- `SmallStep-Assign` — RHS errors. -/
  | assign_err {X : Id} {a a' : Aexp} {σ σ' : State}
      (h : stepA a σ a' σ') (he : a' = .errorAr) :
      stepS (.assign X a) σ .errorStmt σ
  /-- `SmallStep-Assign` axiom: `X = I ;` — commits the value. -/
  | assign_axiom {σ : State} {X : Id} {n : Int}
      (hDecl : σ X ≠ none) :
      stepS (.assign X (.const n)) σ .skip (σ.update X n)
  /-- `SmallStep-SEQ` — reduce head, success. -/
  | seq_head {s1 s1' s2 : Stmt} {σ σ' : State}
      (h : stepS s1 σ s1' σ') (hne : s1' ≠ .errorStmt) :
      stepS (.seq s1 s2) σ (.seq s1' s2) σ'
  /-- `SmallStep-SEQ` — head errors. -/
  | seq_head_err {s1 s1' s2 : Stmt} {σ σ' : State}
      (h : stepS s1 σ s1' σ') (he : s1' = .errorStmt) :
      stepS (.seq s1 s2) σ .errorStmt σ'
  /-- `SmallStep-SEQ` axiom: `skip ; s2 => s2`.
  Note: `SmallStep-Block` (`{s} => s`) has no counterpart here — our `Stmt`
  grammar doesn't include an explicit block wrapper (Maude syntax does). -/
  | seq_skip {s2 : Stmt} {σ : State} :
      stepS (.seq .skip s2) σ s2 σ
  /-- `SmallStep-IF` — reduce guard. -/
  | ite_red {b b' : Bexp} {s1 s2 : Stmt} {σ : State}
      (h : stepB b σ b' σ) (hne : b' ≠ .errorBool) :
      stepS (.ite b s1 s2) σ (.ite b' s1 s2) σ
  /-- `SmallStep-IF` — guard errors. -/
  | ite_err {b b' : Bexp} {s1 s2 : Stmt} {σ : State}
      (h : stepB b σ b' σ) (he : b' = .errorBool) :
      stepS (.ite b s1 s2) σ .errorStmt σ
  /-- `if(true) s1 else s2 => s1`. -/
  | ite_true {s1 s2 : Stmt} {σ : State} :
      stepS (.ite (.b true) s1 s2) σ s1 σ
  /-- `if(false) s1 else s2 => s2`. -/
  | ite_false {s1 s2 : Stmt} {σ : State} :
      stepS (.ite (.b false) s1 s2) σ s2 σ
  /-- `while b s => if b then (s ; while b s) else skip`. -/
  | while_unfold {b : Bexp} {s : Stmt} {σ : State} :
      stepS (.while b s) σ (.ite b (.seq s (.while b s)) .skip) σ

/-! ## Transitive closures — Maude's `*` relation.

Reflexive-transitive closure of each one-step relation. This records the same
reachability graph induced by the Lean `stepA`/`stepB`/`stepS` rules, including
the explicit top-level error sinks that reset the state component to
`State.empty` as in the Maude `o_` relation. -/

inductive stepsA : Aexp → State → Aexp → State → Prop
  | refl (a : Aexp) (σ : State) : stepsA a σ a σ
  | cons {a a' a'' : Aexp} {σ σ' σ'' : State}
      (h1 : stepA a σ a' σ') (h2 : stepsA a' σ' a'' σ'') : stepsA a σ a'' σ''

inductive stepsB : Bexp → State → Bexp → State → Prop
  | refl (b : Bexp) (σ : State) : stepsB b σ b σ
  | cons {b b' b'' : Bexp} {σ σ' σ'' : State}
      (h1 : stepB b σ b' σ') (h2 : stepsB b' σ' b'' σ'') : stepsB b σ b'' σ''

inductive stepsS : Stmt → State → Stmt → State → Prop
  | refl (s : Stmt) (σ : State) : stepsS s σ s σ
  | cons {s s' s'' : Stmt} {σ σ' σ'' : State}
      (h1 : stepS s σ s' σ') (h2 : stepsS s' σ' s'' σ'') : stepsS s σ s'' σ''

/-! ## Smoke tests — mirror `my_tests_small.m` entries. -/

section Smoke

/-- `o < 4 / 0 , .State > => < errorAr, .State >`. -/
example : stepA (.div (.const 4) (.const 0)) State.empty .errorAr State.empty :=
  stepA.div_by_zero

/-- `o < 4 / 2 , .State > => < 2, .State >`. -/
example : stepA (.div (.const 4) (.const 2)) State.empty (.const 2) State.empty :=
  stepA.div_axiom (by decide)

/-- `o < 8 + 2 , .State > => < 10, .State >`. -/
example : stepA (.add (.const 8) (.const 2)) State.empty (.const 10) State.empty :=
  stepA.add_axiom

end Smoke

end Imp.HW1.Small
