import Imp.HW1.Syntax

/-!
# CS522 HW1 — Exercise 56: big-step semantics with division-by-zero

Faithful Lean 4 port of
`brando90/cs522:HW1-Maude/imp/0-imp-original/1-imp-bigstep/imp-semantics-bigstep.maude`
(modified version, with Error propagation).

Modelling decisions:

* Maude has three result configuration shapes for each sort: the pure
  `< I >`, `< T >`, `< Sigma >` (values) and the pure `< Error >`. We
  represent each sort's result as a small inductive "value" type,
  `AVal | BVal | SVal`, where the `.err` constructor corresponds to the
  Maude `< Error >` configuration.
* The course-provided state `Sigma` is a total/partial map; we use
  `Imp.HW1.State = Id → Option Int`. Maude's `Error : -> State` is modelled
  separately via `SVal.err`, not by extending `State`.
* Each Maude rule becomes an inductive constructor. Constructor names
  mirror the rule names used in the Maude comments (e.g. `BigStep-DIV` →
  `evalA.div`, `evalA.div_zero`, `evalA.div_err_l`, `evalA.div_err_r`).
-/

namespace Imp.HW1

/-- Arithmetic big-step result: either an integer value or the pure
`< Error >` configuration. -/
inductive AVal where
  | num : Int → AVal
  | err : AVal
deriving Repr, DecidableEq

/-- Boolean big-step result. -/
inductive BVal where
  | bool : Bool → BVal
  | err  : BVal
deriving Repr, DecidableEq

/-- Statement big-step result: either a final state or pure error. -/
inductive SVal where
  | state : State → SVal
  | err   : SVal

/-- Program-level big-step result. -/
inductive PVal where
  | state : State → PVal
  | err   : PVal

/-! ## Big-step evaluation of arithmetic expressions -/

/-- `evalA a σ v` corresponds to the Maude sequent `< a, σ > => < v >`. -/
inductive evalA : Aexp → State → AVal → Prop
  /-- `BigStep-Int` — integer literal. -/
  | const (n : Int) (σ : State) : evalA (.const n) σ (.num n)
  /-- `BigStep-Lookup` — defined variable. -/
  | var_ok {σ : State} {X : Id} {n : Int} (h : σ X = some n) :
      evalA (.var X) σ (.num n)
  /-- `BigStep-ADD` — normal case. -/
  | add {a1 a2 : Aexp} {σ : State} {n1 n2 : Int}
      (h1 : evalA a1 σ (.num n1)) (h2 : evalA a2 σ (.num n2)) :
      evalA (.add a1 a2) σ (.num (n1 + n2))
  /-- `BigStep-ADD` error propagation (left). -/
  | add_err_l {a1 a2 : Aexp} {σ : State}
      (h : evalA a1 σ .err) : evalA (.add a1 a2) σ .err
  /-- `BigStep-ADD` error propagation (right). -/
  | add_err_r {a1 a2 : Aexp} {σ : State}
      (h : evalA a2 σ .err) : evalA (.add a1 a2) σ .err
  /-- `BigStep-DIV` — normal case, divisor non-zero. (Maude: `I2 =/=Bool 0`) -/
  | div {a1 a2 : Aexp} {σ : State} {n1 n2 : Int}
      (h1 : evalA a1 σ (.num n1)) (h2 : evalA a2 σ (.num n2)) (hne : n2 ≠ 0) :
      evalA (.div a1 a2) σ (.num (n1 / n2))
  /-- **Ex. 56 headline rule** — division-by-zero yields `< Error >`.
  Maude: `crl < A1 / A2 , Sigma > => < Error > if < A2,Sigma > => < 0 > .` -/
  | div_zero {a1 a2 : Aexp} {σ : State} {n1 : Int}
      (h1 : evalA a1 σ (.num n1)) (h2 : evalA a2 σ (.num 0)) :
      evalA (.div a1 a2) σ .err
  /-- `BigStep-DIV` error propagation (left operand evaluates to Error). -/
  | div_err_l {a1 a2 : Aexp} {σ : State}
      (h : evalA a1 σ .err) : evalA (.div a1 a2) σ .err
  /-- `BigStep-DIV` error propagation (right operand evaluates to Error). -/
  | div_err_r {a1 a2 : Aexp} {σ : State}
      (h : evalA a2 σ .err) : evalA (.div a1 a2) σ .err

/-! ## Big-step evaluation of boolean expressions -/

/-- `evalB b σ v` — Maude: `< b, σ > => < v >`. -/
inductive evalB : Bexp → State → BVal → Prop
  /-- `BigStep-Bool` — boolean literal. -/
  | b (v : Bool) (σ : State) : evalB (.b v) σ (.bool v)
  /-- `BigStep-LEQ` — normal case. Maude uses sequential strictness on arguments. -/
  | le {a1 a2 : Aexp} {σ : State} {n1 n2 : Int}
      (h1 : evalA a1 σ (.num n1)) (h2 : evalA a2 σ (.num n2)) :
      evalB (.le a1 a2) σ (.bool (decide (n1 ≤ n2)))
  /-- `BigStep-LEQ` error propagation (left). -/
  | le_err_l {a1 a2 : Aexp} {σ : State}
      (h : evalA a1 σ .err) : evalB (.le a1 a2) σ .err
  /-- `BigStep-LEQ` error propagation (right). -/
  | le_err_r {a1 a2 : Aexp} {σ : State}
      (h : evalA a2 σ .err) : evalB (.le a1 a2) σ .err
  /-- `BigStep-Not-True`. -/
  | not_t {b : Bexp} {σ : State}
      (h : evalB b σ (.bool true)) : evalB (.not b) σ (.bool false)
  /-- `BigStep-Not-False`. -/
  | not_f {b : Bexp} {σ : State}
      (h : evalB b σ (.bool false)) : evalB (.not b) σ (.bool true)
  /-- `BigStep-Not` error propagation. -/
  | not_err {b : Bexp} {σ : State}
      (h : evalB b σ .err) : evalB (.not b) σ .err
  /-- `BigStep-And-False` — short-circuit on false. -/
  | and_false {b1 b2 : Bexp} {σ : State}
      (h : evalB b1 σ (.bool false)) : evalB (.and b1 b2) σ (.bool false)
  /-- `BigStep-And-True` — continue to b2 when b1 is true. -/
  | and_true {b1 b2 : Bexp} {σ : State} {v : Bool}
      (h1 : evalB b1 σ (.bool true)) (h2 : evalB b2 σ (.bool v)) :
      evalB (.and b1 b2) σ (.bool v)
  /-- `BigStep-And` error on first operand. -/
  | and_err_l {b1 b2 : Bexp} {σ : State}
      (h : evalB b1 σ .err) : evalB (.and b1 b2) σ .err
  /-- `BigStep-And` error on second operand (only when b1 evaluates to true;
  otherwise the false short-circuit rule fires and erases b2). -/
  | and_err_r {b1 b2 : Bexp} {σ : State}
      (h1 : evalB b1 σ (.bool true)) (h2 : evalB b2 σ .err) :
      evalB (.and b1 b2) σ .err

/-! ## Big-step evaluation of statements -/

/-- `evalS s σ v` — Maude: `< s, σ > => < v >`. -/
inductive evalS : Stmt → State → SVal → Prop
  /-- `BigStep-Empty-Block` — `skip` leaves the state unchanged. -/
  | skip (σ : State) : evalS .skip σ (.state σ)
  /-- `BigStep-ASGN` normal — only defined for declared variables
  (`Sigma(X) =/=Bool undefined`). -/
  | assign_ok {σ : State} {X : Id} {a : Aexp} {n : Int}
      (hDecl : σ X ≠ none) (hA : evalA a σ (.num n)) :
      evalS (.assign X a) σ (.state (σ.update X n))
  /-- `BigStep-ASGN` error — RHS expression evaluates to Error. -/
  | assign_err {σ : State} {X : Id} {a : Aexp}
      (hDecl : σ X ≠ none) (hA : evalA a σ .err) :
      evalS (.assign X a) σ .err
  /-- `BigStep-SEQ` — normal case. -/
  | seq_ok {s1 s2 : Stmt} {σ σ' σ'' : State}
      (h1 : evalS s1 σ (.state σ')) (h2 : evalS s2 σ' (.state σ'')) :
      evalS (.seq s1 s2) σ (.state σ'')
  /-- `BigStep-SEQ` error in first statement. -/
  | seq_err_l {s1 s2 : Stmt} {σ : State}
      (h : evalS s1 σ .err) : evalS (.seq s1 s2) σ .err
  /-- `BigStep-SEQ` error in second statement (after first succeeded). -/
  | seq_err_r {s1 s2 : Stmt} {σ σ' : State}
      (h1 : evalS s1 σ (.state σ')) (h2 : evalS s2 σ' .err) :
      evalS (.seq s1 s2) σ .err
  /-- `BigStep-IF-True`. -/
  | ite_true {b : Bexp} {s1 s2 : Stmt} {σ : State} {r : SVal}
      (hb : evalB b σ (.bool true)) (h : evalS s1 σ r) :
      evalS (.ite b s1 s2) σ r
  /-- `BigStep-IF-False`. -/
  | ite_false {b : Bexp} {s1 s2 : Stmt} {σ : State} {r : SVal}
      (hb : evalB b σ (.bool false)) (h : evalS s2 σ r) :
      evalS (.ite b s1 s2) σ r
  /-- `BigStep-IF` error in guard. -/
  | ite_err_guard {b : Bexp} {s1 s2 : Stmt} {σ : State}
      (h : evalB b σ .err) : evalS (.ite b s1 s2) σ .err
  /-- `BigStep-While-False` — guard is false, loop terminates in place. -/
  | while_false {b : Bexp} {s : Stmt} {σ : State}
      (h : evalB b σ (.bool false)) : evalS (.while b s) σ (.state σ)
  /-- `BigStep-While` — guard errors. -/
  | while_err_guard {b : Bexp} {s : Stmt} {σ : State}
      (h : evalB b σ .err) : evalS (.while b s) σ .err
  /-- `BigStep-While-True` — guard true, unroll one iteration then continue.
  Matches Maude: `if < B,Sigma > => < true > /\ < S while (B) S, Sigma > => < Sigma' >`. -/
  | while_true {b : Bexp} {s : Stmt} {σ σ' : State}
      (hb : evalB b σ (.bool true)) (h : evalS (.seq s (.while b s)) σ (.state σ')) :
      evalS (.while b s) σ (.state σ')
  /-- `BigStep-While-True` with error propagation from the unrolled body. -/
  | while_err_body {b : Bexp} {s : Stmt} {σ : State}
      (hb : evalB b σ (.bool true)) (h : evalS (.seq s (.while b s)) σ .err) :
      evalS (.while b s) σ .err

/-! ## Big-step evaluation of programs

Corresponds to the Maude `BigStep-PGM` rule:

```maude
crl < int Xl ; S > => < Sigma > if < S,(Xl |-> 0) > => < Sigma > .
crl < int Xl ; S > => < Error > if < S,(Xl |-> 0) > => < Error > .
```
-/
inductive evalP : Pgm → PVal → Prop
  | ok {xl : List Id} {s : Stmt} {σ : State}
      (h : evalS s (State.initZero xl) (.state σ)) : evalP ⟨xl, s⟩ (.state σ)
  | err {xl : List Id} {s : Stmt}
      (h : evalS s (State.initZero xl) .err) : evalP ⟨xl, s⟩ .err

/-! ## Smoke tests — concrete instances matching entries of `my_tests.m` -/

section Smoke

/-- `< 1 / 0 , .State > => < Error >` — canonical div-by-zero. -/
example : evalA (.div (.const 1) (.const 0)) State.empty .err :=
  evalA.div_zero (evalA.const 1 _) (evalA.const 0 _)

/-- `< 6 / 2 , .State > => < 3 >`. -/
example : evalA (.div (.const 6) (.const 2)) State.empty (.num 3) :=
  evalA.div (evalA.const 6 _) (evalA.const 2 _) (by decide)

/-- `< 3 + 3 / 0 , .State > => < Error >`. -/
example : evalA (.add (.const 3) (.div (.const 3) (.const 0))) State.empty .err :=
  evalA.add_err_r (evalA.div_zero (evalA.const 3 _) (evalA.const 0 _))

end Smoke

end Imp.HW1
