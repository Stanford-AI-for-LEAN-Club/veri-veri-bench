import Imp.HW2.Syntax

/-!
# CS522 HW2 — Exercise 83: denotational semantics with silent division-by-zero

Faithful Lean 4 port of
`brando90/cs522:HW2-Maude/imp/0-imp-original/4-imp-denotational/imp-semantics-denotational.maude`
(Ex. 83 — "return a state like for correct programs" on division-by-zero,
rather than `bottom`).

## Modelling decisions

* The Maude solution uses `funCPO / appCPO / fixCPO` from a CPO library
  plus a distinguished `Error : -> State` constant for AExp/BExp and a
  reserved `op err : -> Id .` flag for silent-failure at Stmt/Pgm level.
* In Lean we model the denotation **relationally** rather than
  functionally, matching the style of `Imp/main.lean`'s `terminate`.
  This avoids the need to reproduce the CPO / `fixCPO` machinery and
  still captures the silent-failure behaviour faithfully.
* `denA : Aexp → State → AResult → Prop` and
  `denB : Bexp → State → BResult → Prop` distinguish three Maude outcomes:
  an ordinary value, the Ex. 83 `Error`, and ordinary `undefined`.
* `denS : Stmt → State → State → Prop` only converts `Error` to a silent
  failure state (`State.markFailed σ`). Plain `undefined` remains bottom,
  as in the Maude equations.
* Constructor names mirror the Maude equation labels where possible.
-/

namespace Imp.HW2

/-! ## Result domains

The Maude Ex. 83 solution introduces a distinct `Error : -> State` constant
while still retaining the existing `undefined` bottom from the CPO library.
We therefore model arithmetic and boolean denotations with three outcomes:

* a normal value,
* `error` for the Ex. 83 "division by zero" signal that statements turn into
  `markFailed`,
* `undef` for the pre-existing bottom produced by undeclared-variable lookups
  and other partiality already present in the original semantics.
-/

/-- Arithmetic denotation result: value, Ex. 83 `Error`, or ordinary bottom. -/
inductive AResult where
  | val : Int → AResult
  | error : AResult
  | undef : AResult
deriving Repr, DecidableEq

/-- Boolean denotation result: value, Ex. 83 `Error`, or ordinary bottom. -/
inductive BResult where
  | val : Bool → BResult
  | error : BResult
  | undef : BResult
deriving Repr, DecidableEq

/-! ## Arithmetic-expression denotation -/

inductive denA : Aexp → State → AResult → Prop
  /-- `[[I]] = funCPO σ → I`. -/
  | const (n : Int) (σ : State) : denA (.const n) σ (.val n)
  /-- `[[X]] = funCPO σ → σ(X)` when σ(X) is defined. -/
  | var_ok {σ : State} {X : Id} {n : Int} (h : σ X = some n) :
      denA (.var X) σ (.val n)
  /-- Undefined variable lookup remains Maude `undefined`, not Ex. 83 `Error`. -/
  | var_undef {σ : State} {X : Id} (h : σ X = none) :
      denA (.var X) σ .undef
  /-- `[[A1 + A2]]` normal case. -/
  | add {a1 a2 : Aexp} {σ : State} {n1 n2 : Int}
      (h1 : denA a1 σ (.val n1)) (h2 : denA a2 σ (.val n2)) :
      denA (.add a1 a2) σ (.val (n1 + n2))
  /-- `[[A1 + A2]]` — left operand yields `Error`. -/
  | add_err_l {a1 a2 : Aexp} {σ : State}
      (h : denA a1 σ .error) : denA (.add a1 a2) σ .error
  /-- `[[A1 + A2]]` — right operand yields `Error`. -/
  | add_err_r {a1 a2 : Aexp} {σ : State}
      (h : denA a2 σ .error) : denA (.add a1 a2) σ .error
  /-- `[[A1 + A2]]` — left operand is ordinary `undefined`, right is a value. -/
  | add_undef_l_val {a1 a2 : Aexp} {σ : State} {n2 : Int}
      (h1 : denA a1 σ .undef) (h2 : denA a2 σ (.val n2)) :
      denA (.add a1 a2) σ .undef
  /-- `[[A1 + A2]]` — both operands are ordinary `undefined`. -/
  | add_undef_l_undef {a1 a2 : Aexp} {σ : State}
      (h1 : denA a1 σ .undef) (h2 : denA a2 σ .undef) :
      denA (.add a1 a2) σ .undef
  /-- `[[A1 + A2]]` — right operand is ordinary `undefined`. -/
  | add_undef_r {a1 a2 : Aexp} {σ : State} {n1 : Int}
      (h1 : denA a1 σ (.val n1)) (h2 : denA a2 σ .undef) :
      denA (.add a1 a2) σ .undef
  /-- `[[A1 / A2]]` — normal case, divisor non-zero. -/
  | div_ok {a1 a2 : Aexp} {σ : State} {n1 n2 : Int}
      (h1 : denA a1 σ (.val n1)) (h2 : denA a2 σ (.val n2)) (hne : n2 ≠ 0) :
      denA (.div a1 a2) σ (.val (n1 / n2))
  /-- **Ex. 83 headline rule at AExp level** — divisor is 0 ⇒ `Error`.
  Maude: `ifCPO(appCPO([[A2]],σ) ==Bool 0, Error, ...)`. -/
  | div_zero {a1 a2 : Aexp} {σ : State}
      (h : denA a2 σ (.val 0)) : denA (.div a1 a2) σ .error
  /-- `[[A1 / A2]]` — left operand is `Error`. -/
  | div_err_l {a1 a2 : Aexp} {σ : State}
      (h : denA a1 σ .error) : denA (.div a1 a2) σ .error
  /-- `[[A1 / A2]]` — right operand is `Error`. -/
  | div_err_r {a1 a2 : Aexp} {σ : State}
      (h : denA a2 σ .error) : denA (.div a1 a2) σ .error
  /-- `[[A1 / A2]]` — left operand is `undefined`, divisor is a non-zero value. -/
  | div_undef_l_nonzero {a1 a2 : Aexp} {σ : State} {n2 : Int}
      (h1 : denA a1 σ .undef) (h2 : denA a2 σ (.val n2)) (hne : n2 ≠ 0) :
      denA (.div a1 a2) σ .undef
  /-- `[[A1 / A2]]` — both operands are ordinary `undefined`. -/
  | div_undef_l_undef {a1 a2 : Aexp} {σ : State}
      (h1 : denA a1 σ .undef) (h2 : denA a2 σ .undef) :
      denA (.div a1 a2) σ .undef
  /-- `[[A1 / A2]]` — divisor is ordinary `undefined`. -/
  | div_undef_r {a1 a2 : Aexp} {σ : State} {n1 : Int}
      (h1 : denA a1 σ (.val n1)) (h2 : denA a2 σ .undef) :
      denA (.div a1 a2) σ .undef

/-! ## Boolean-expression denotation -/

inductive denB : Bexp → State → BResult → Prop
  /-- `[[T]] = funCPO σ → T`. -/
  | b (v : Bool) (σ : State) : denB (.b v) σ (.val v)
  /-- `[[A1 <= A2]]` normal. -/
  | le {a1 a2 : Aexp} {σ : State} {n1 n2 : Int}
      (h1 : denA a1 σ (.val n1)) (h2 : denA a2 σ (.val n2)) :
      denB (.le a1 a2) σ (.val (decide (n1 ≤ n2)))
  /-- `[[A1 <= A2]]` — left arithmetic yields `Error`. -/
  | le_err_l {a1 a2 : Aexp} {σ : State}
      (h : denA a1 σ .error) : denB (.le a1 a2) σ .error
  /-- `[[A1 <= A2]]` — right arithmetic yields `Error`. -/
  | le_err_r {a1 a2 : Aexp} {σ : State}
      (h : denA a2 σ .error) : denB (.le a1 a2) σ .error
  /-- `[[A1 <= A2]]` — left side is ordinary `undefined`, right is a value. -/
  | le_undef_l_val {a1 a2 : Aexp} {σ : State} {n2 : Int}
      (h1 : denA a1 σ .undef) (h2 : denA a2 σ (.val n2)) :
      denB (.le a1 a2) σ .undef
  /-- `[[A1 <= A2]]` — both sides are ordinary `undefined`. -/
  | le_undef_l_undef {a1 a2 : Aexp} {σ : State}
      (h1 : denA a1 σ .undef) (h2 : denA a2 σ .undef) :
      denB (.le a1 a2) σ .undef
  /-- `[[A1 <= A2]]` — right side is ordinary `undefined`. -/
  | le_undef_r {a1 a2 : Aexp} {σ : State} {n1 : Int}
      (h1 : denA a1 σ (.val n1)) (h2 : denA a2 σ .undef) :
      denB (.le a1 a2) σ .undef
  /-- `[[! B]]` normal. -/
  | not {b : Bexp} {σ : State} {v : Bool}
      (h : denB b σ (.val v)) : denB (.not b) σ (.val (!v))
  /-- `[[! B]]` — operand is `Error`. -/
  | not_err {b : Bexp} {σ : State}
      (h : denB b σ .error) : denB (.not b) σ .error
  /-- `[[! B]]` — operand is ordinary `undefined`. -/
  | not_undef {b : Bexp} {σ : State}
      (h : denB b σ .undef) : denB (.not b) σ .undef
  /-- `[[B1 && B2]]` — short-circuits on false. -/
  | and_false {b1 b2 : Bexp} {σ : State}
      (h : denB b1 σ (.val false)) : denB (.and b1 b2) σ (.val false)
  /-- `[[B1 && B2]]` — continue to b2 when b1 is true. -/
  | and_true {b1 b2 : Bexp} {σ : State} {v : Bool}
      (h1 : denB b1 σ (.val true)) (h2 : denB b2 σ (.val v)) :
      denB (.and b1 b2) σ (.val v)
  /-- `[[B1 && B2]]` — first operand `Error`. -/
  | and_err_l {b1 b2 : Bexp} {σ : State}
      (h : denB b1 σ .error) : denB (.and b1 b2) σ .error
  /-- `[[B1 && B2]]` — second operand `Error` (only when b1 is true). -/
  | and_err_r {b1 b2 : Bexp} {σ : State}
      (h1 : denB b1 σ (.val true)) (h2 : denB b2 σ .error) :
      denB (.and b1 b2) σ .error
  /-- `[[B1 && B2]]` — first operand is ordinary `undefined`. -/
  | and_undef_l {b1 b2 : Bexp} {σ : State}
      (h : denB b1 σ .undef) : denB (.and b1 b2) σ .undef
  /-- `[[B1 && B2]]` — second operand is ordinary `undefined`. -/
  | and_undef_r {b1 b2 : Bexp} {σ : State}
      (h1 : denB b1 σ (.val true)) (h2 : denB b2 σ .undef) :
      denB (.and b1 b2) σ .undef

/-! ## Statement denotation — with silent failure (Ex. 83) -/

inductive denS : Stmt → State → State → Prop
  /-- `[[{}]] = funCPO σ → σ`. -/
  | skip (σ : State) : denS .skip σ σ
  /-- `[[X = A ;]]` — normal. Requires X to be declared, just like Maude's
  `_`(_`)(σ, X) =/=Bool undefined` guard. -/
  | assign_ok {σ : State} {X : Id} {a : Aexp} {n : Int}
      (hDecl : σ X ≠ none) (hA : denA a σ (.val n)) :
      denS (.assign X a) σ (σ.update X n)
  /-- **Silent-failure assignment** — Maude: if `[[A]](σ) == Error` then
  commit to `σ & err |-> 1`. Ordinary `undefined` still stays bottom. -/
  | assign_err {σ : State} {X : Id} {a : Aexp}
      (hA : denA a σ .error) :
      denS (.assign X a) σ σ.markFailed
  /-- `[[S1 S2]]` — S1 fails silently, skip S2. Maude: `ifCPO(
  _`(_`)(appCPO([[S1]],σ), err) ==Bool undefined, ..., appCPO([[S1]],σ))`. -/
  | seq_failed {s1 s2 : Stmt} {σ σ' : State}
      (h1 : denS s1 σ σ') (hFail : σ'.isFailed) :
      denS (.seq s1 s2) σ σ'
  /-- `[[S1 S2]]` — normal case. -/
  | seq_ok {s1 s2 : Stmt} {σ σ' σ'' : State}
      (h1 : denS s1 σ σ') (hOk : ¬ σ'.isFailed) (h2 : denS s2 σ' σ'') :
      denS (.seq s1 s2) σ σ''
  /-- `[[if (B) S1 else S2]]` — guard true. -/
  | ite_true {b : Bexp} {s1 s2 : Stmt} {σ σ' : State}
      (hb : denB b σ (.val true)) (h : denS s1 σ σ') :
      denS (.ite b s1 s2) σ σ'
  /-- `[[if (B) S1 else S2]]` — guard false. -/
  | ite_false {b : Bexp} {s1 s2 : Stmt} {σ σ' : State}
      (hb : denB b σ (.val false)) (h : denS s2 σ σ') :
      denS (.ite b s1 s2) σ σ'
  /-- **Silent-failure if** — guard errors ⇒ silently fail. Maude:
  `ifCPO(appCPO([[B]],σ) ==Bool Error, σ & err |-> 1, ...)`. -/
  | ite_err {b : Bexp} {s1 s2 : Stmt} {σ : State}
      (hb : denB b σ .error) : denS (.ite b s1 s2) σ σ.markFailed
  /-- `[[while (B) S]]` — guard false ⇒ terminate. -/
  | while_false {b : Bexp} {s : Stmt} {σ : State}
      (hb : denB b σ (.val false)) : denS (.while b s) σ σ
  /-- `[[while (B) S]]` — guard true, body fails silently ⇒ absorb failure. -/
  | while_body_failed {b : Bexp} {s : Stmt} {σ σ' : State}
      (hb : denB b σ (.val true)) (h : denS s σ σ') (hFail : σ'.isFailed) :
      denS (.while b s) σ σ'
  /-- `[[while (B) S]]` — guard true, body ok, continue. -/
  | while_true {b : Bexp} {s : Stmt} {σ σ' σ'' : State}
      (hb : denB b σ (.val true)) (h : denS s σ σ') (hOk : ¬ σ'.isFailed)
      (hLoop : denS (.while b s) σ' σ'') :
      denS (.while b s) σ σ''
  /-- **Silent-failure while-guard** — guard errors ⇒ fail silently. -/
  | while_err {b : Bexp} {s : Stmt} {σ : State}
      (hb : denB b σ .error) : denS (.while b s) σ σ.markFailed

/-! ## Program denotation -/

/-- `[[(int Xl ; S)]] = appCPO([[S]], Xl |-> 0)`. -/
inductive denP : Pgm → State → Prop
  | run {xl : List Id} {s : Stmt} {σ : State}
      (h : denS s (State.initZero xl) σ) : denP ⟨xl, s⟩ σ

/-! ## Smoke tests — small instances of `my_test.maude` -/

section Smoke

/-- `[[1/0]](∅) = Error` — Maude `red appCPO([[1 / 0]], .State) .`. -/
example : denA (.div (.const 1) (.const 0)) State.empty .error :=
  denA.div_zero (denA.const 0 _)

/-- `[[6/2]](∅) = 3`. -/
example : denA (.div (.const 6) (.const 2)) State.empty (.val 3) :=
  denA.div_ok (denA.const 6 _) (denA.const 2 _) (by decide)

/-- `[[y]](x|->2) = undefined`, not Ex. 83 `Error`. -/
example : denA (.var "y") ((State.empty).update "x" 2) .undef := by
  apply denA.var_undef
  unfold State.update State.empty
  simp

/-- `[[x = 3/0 ;]](x|->2) = markFailed (x|->2)` — silent failure. -/
example : denS (.assign "x" (.div (.const 3) (.const 0)))
                 ((State.empty).update "x" 2)
                 (((State.empty).update "x" 2).markFailed) :=
  denS.assign_err (denA.div_zero (denA.const 0 _))

end Smoke

end Imp.HW2
