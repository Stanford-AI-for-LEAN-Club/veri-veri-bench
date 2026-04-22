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
* `denA : Aexp → State → Option Int → Prop` — `some n` = arithmetic value,
  `none` = the Maude `Error` result. Same for `denB`.
* `denS : Stmt → State → State → Prop` — a *total* relation (every
  well-behaved program has a final state), with silent-failure encoded
  by `State.isFailed σ` on the output. There is no "bottom" value here;
  instead, non-termination is represented, as in `Imp/main.lean`, by the
  *absence* of any derivation.
* Constructor names mirror the Maude equation labels where possible.
-/

namespace Imp.HW2

/-! ## Arithmetic-expression denotation -/

inductive denA : Aexp → State → Option Int → Prop
  /-- `[[I]] = funCPO σ → I`. -/
  | const (n : Int) (σ : State) : denA (.const n) σ (some n)
  /-- `[[X]] = funCPO σ → σ(X)` when σ(X) is defined. -/
  | var_ok {σ : State} {X : Id} {n : Int} (h : σ X = some n) :
      denA (.var X) σ (some n)
  /-- Undefined variable lookup treated as `undefined`, lifted to Maude `Error`. -/
  | var_err {σ : State} {X : Id} (h : σ X = none) :
      denA (.var X) σ none
  /-- `[[A1 + A2]]` normal case. -/
  | add {a1 a2 : Aexp} {σ : State} {n1 n2 : Int}
      (h1 : denA a1 σ (some n1)) (h2 : denA a2 σ (some n2)) :
      denA (.add a1 a2) σ (some (n1 + n2))
  /-- `[[A1 + A2]]` — left operand yields `Error`. -/
  | add_err_l {a1 a2 : Aexp} {σ : State}
      (h : denA a1 σ none) : denA (.add a1 a2) σ none
  /-- `[[A1 + A2]]` — right operand yields `Error`. -/
  | add_err_r {a1 a2 : Aexp} {σ : State}
      (h : denA a2 σ none) : denA (.add a1 a2) σ none
  /-- `[[A1 / A2]]` — normal case, divisor non-zero. -/
  | div_ok {a1 a2 : Aexp} {σ : State} {n1 n2 : Int}
      (h1 : denA a1 σ (some n1)) (h2 : denA a2 σ (some n2)) (hne : n2 ≠ 0) :
      denA (.div a1 a2) σ (some (n1 / n2))
  /-- **Ex. 83 headline rule at AExp level** — divisor is 0 ⇒ `Error`.
  Maude: `ifCPO(appCPO([[A2]],σ) ==Bool 0, Error, ...)`. -/
  | div_zero {a1 a2 : Aexp} {σ : State}
      (h : denA a2 σ (some 0)) : denA (.div a1 a2) σ none
  /-- `[[A1 / A2]]` — left operand is `Error`. -/
  | div_err_l {a1 a2 : Aexp} {σ : State}
      (h : denA a1 σ none) : denA (.div a1 a2) σ none
  /-- `[[A1 / A2]]` — right operand is `Error`. -/
  | div_err_r {a1 a2 : Aexp} {σ : State}
      (h : denA a2 σ none) : denA (.div a1 a2) σ none

/-! ## Boolean-expression denotation -/

inductive denB : Bexp → State → Option Bool → Prop
  /-- `[[T]] = funCPO σ → T`. -/
  | b (v : Bool) (σ : State) : denB (.b v) σ (some v)
  /-- `[[A1 <= A2]]` normal. -/
  | le {a1 a2 : Aexp} {σ : State} {n1 n2 : Int}
      (h1 : denA a1 σ (some n1)) (h2 : denA a2 σ (some n2)) :
      denB (.le a1 a2) σ (some (decide (n1 ≤ n2)))
  /-- `[[A1 <= A2]]` — left arithmetic yields `Error`. -/
  | le_err_l {a1 a2 : Aexp} {σ : State}
      (h : denA a1 σ none) : denB (.le a1 a2) σ none
  /-- `[[A1 <= A2]]` — right arithmetic yields `Error`. -/
  | le_err_r {a1 a2 : Aexp} {σ : State}
      (h : denA a2 σ none) : denB (.le a1 a2) σ none
  /-- `[[! B]]` normal. -/
  | not {b : Bexp} {σ : State} {v : Bool}
      (h : denB b σ (some v)) : denB (.not b) σ (some (!v))
  /-- `[[! B]]` — operand is `Error`. -/
  | not_err {b : Bexp} {σ : State}
      (h : denB b σ none) : denB (.not b) σ none
  /-- `[[B1 && B2]]` — short-circuits on false. -/
  | and_false {b1 b2 : Bexp} {σ : State}
      (h : denB b1 σ (some false)) : denB (.and b1 b2) σ (some false)
  /-- `[[B1 && B2]]` — continue to b2 when b1 is true. -/
  | and_true {b1 b2 : Bexp} {σ : State} {v : Bool}
      (h1 : denB b1 σ (some true)) (h2 : denB b2 σ (some v)) :
      denB (.and b1 b2) σ (some v)
  /-- `[[B1 && B2]]` — first operand `Error`. -/
  | and_err_l {b1 b2 : Bexp} {σ : State}
      (h : denB b1 σ none) : denB (.and b1 b2) σ none
  /-- `[[B1 && B2]]` — second operand `Error` (only when b1 is true). -/
  | and_err_r {b1 b2 : Bexp} {σ : State}
      (h1 : denB b1 σ (some true)) (h2 : denB b2 σ none) :
      denB (.and b1 b2) σ none

/-! ## Statement denotation — with silent failure (Ex. 83) -/

inductive denS : Stmt → State → State → Prop
  /-- `[[{}]] = funCPO σ → σ`. -/
  | skip (σ : State) : denS .skip σ σ
  /-- `[[X = A ;]]` — normal. Requires X to be declared, just like Maude's
  `_`(_`)(σ, X) =/=Bool undefined` guard. -/
  | assign_ok {σ : State} {X : Id} {a : Aexp} {n : Int}
      (hDecl : σ X ≠ none) (hA : denA a σ (some n)) :
      denS (.assign X a) σ (σ.update X n)
  /-- **Silent-failure assignment** — Maude: if `[[A]](σ) == Error` then
  commit to `σ & err |-> 1`. Every such Stmt has an output state. -/
  | assign_err {σ : State} {X : Id} {a : Aexp}
      (hA : denA a σ none) :
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
      (hb : denB b σ (some true)) (h : denS s1 σ σ') :
      denS (.ite b s1 s2) σ σ'
  /-- `[[if (B) S1 else S2]]` — guard false. -/
  | ite_false {b : Bexp} {s1 s2 : Stmt} {σ σ' : State}
      (hb : denB b σ (some false)) (h : denS s2 σ σ') :
      denS (.ite b s1 s2) σ σ'
  /-- **Silent-failure if** — guard errors ⇒ silently fail. Maude:
  `ifCPO(appCPO([[B]],σ) ==Bool Error, σ & err |-> 1, ...)`. -/
  | ite_err {b : Bexp} {s1 s2 : Stmt} {σ : State}
      (hb : denB b σ none) : denS (.ite b s1 s2) σ σ.markFailed
  /-- `[[while (B) S]]` — guard false ⇒ terminate. -/
  | while_false {b : Bexp} {s : Stmt} {σ : State}
      (hb : denB b σ (some false)) : denS (.while b s) σ σ
  /-- `[[while (B) S]]` — guard true, body fails silently ⇒ absorb failure. -/
  | while_body_failed {b : Bexp} {s : Stmt} {σ σ' : State}
      (hb : denB b σ (some true)) (h : denS s σ σ') (hFail : σ'.isFailed) :
      denS (.while b s) σ σ'
  /-- `[[while (B) S]]` — guard true, body ok, continue. -/
  | while_true {b : Bexp} {s : Stmt} {σ σ' σ'' : State}
      (hb : denB b σ (some true)) (h : denS s σ σ') (hOk : ¬ σ'.isFailed)
      (hLoop : denS (.while b s) σ' σ'') :
      denS (.while b s) σ σ''
  /-- **Silent-failure while-guard** — guard errors ⇒ fail silently. -/
  | while_err {b : Bexp} {s : Stmt} {σ : State}
      (hb : denB b σ none) : denS (.while b s) σ σ.markFailed

/-! ## Program denotation -/

/-- `[[(int Xl ; S)]] = appCPO([[S]], Xl |-> 0)`. -/
inductive denP : Pgm → State → Prop
  | run {xl : List Id} {s : Stmt} {σ : State}
      (h : denS s (State.initZero xl) σ) : denP ⟨xl, s⟩ σ

/-! ## Smoke tests — small instances of `my_test.maude` -/

section Smoke

/-- `[[1/0]](∅) = Error` — Maude `red appCPO([[1 / 0]], .State) .`. -/
example : denA (.div (.const 1) (.const 0)) State.empty none :=
  denA.div_zero (denA.const 0 _)

/-- `[[6/2]](∅) = some 3`. -/
example : denA (.div (.const 6) (.const 2)) State.empty (some 3) :=
  denA.div_ok (denA.const 6 _) (denA.const 2 _) (by decide)

/-- `[[x = 3/0 ;]](x|->2) = markFailed (x|->2)` — silent failure. -/
example : denS (.assign "x" (.div (.const 3) (.const 0)))
                 ((State.empty).update "x" 2)
                 (((State.empty).update "x" 2).markFailed) :=
  denS.assign_err (denA.div_zero (denA.const 0 _))

end Smoke

end Imp.HW2
