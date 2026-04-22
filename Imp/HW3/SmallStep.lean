import Imp.HW3.Syntax

/-!
# CS522 HW3b — IMP++ small-step SOS

Faithful port of
`brando90/cs522:HW3/6-imp++/small_step/imp-semantics-smallstep.maude`
(137-line Maude file).

## Configuration design (mirrors Maude exactly)

Maude distinguishes three configuration shapes at the Stmt level:

* `<Stmt, σ, inB, outB>` — a live reduction state.
* `<halting, σ, inB, outB>` — abrupt termination (from `halt;` **or**
  lifted from a sub-expression error — see note below).
* `<error, σ, inB>` — a pure error at the AExp/BExp level.

We therefore use two sum types:

* `SConfig = running Stmt σ inB outB | halting σ inB outB`
* `AConfig = running Aexp σ inB | error σ inB` (ditto `BConfig`)

## Faithful deviation from our big-step (HW3a)

The Maude small-step file **lifts AExp/BExp `error` to `halting` at Stmt
level**, rather than keeping a separate Stmt-level `err` result. That
matches the semantics' operational intent ("division-by-zero terminates
the program") and we follow it here. The HW3a big-step's separate
`SResult.err` is a benign specialization that distinguishes the two
failure modes for easier reasoning; both are defensible.

## `spawn` simplification — same as HW3a

True concurrent thread-pool semantics require carrying a *set of threads*
in the configuration. That is a substantial extra layer we defer to a
follow-up PR (tentatively HW3b-v2). The present port ports every Maude
`spawn` rule mechanically (spawn S reduces its body sequentially; spawn
of an empty block consumes itself). No interleaving is modeled.
-/

namespace Imp.HW3.Small

open Imp.HW3

/-! ## Configurations -/

/-- Arithmetic-expression one-step target. -/
inductive AConfig where
  | running (a : Aexp) (σ : State) (inB : Buffer) : AConfig
  | error   (σ : State) (inB : Buffer) : AConfig

/-- Boolean-expression one-step target. -/
inductive BConfig where
  | running (b : Bexp) (σ : State) (inB : Buffer) : BConfig
  | error   (σ : State) (inB : Buffer) : BConfig

/-- Statement one-step target. -/
inductive SConfig where
  | running (s : Stmt) (σ : State) (inB outB : Buffer) : SConfig
  | halting (σ : State) (inB outB : Buffer) : SConfig

/-- Restore the outer binding of a local variable after one body step of
`let X = I in S`, matching Maude's `Sigma'[Sigma(X) / X]`. -/
def restoreLocal (σOuter σInner : State) (X : Id) : State :=
  match σOuter X with
  | some n => σInner.update X n
  | none   => σInner.unbind X

/-! ## Arithmetic small-step -/

inductive stepA : Aexp → State → Buffer → AConfig → Prop
  /-- Variable lookup (Maude: `Sigma(X) =/=Bool undefined`). -/
  | lookup {σ : State} {X : Id} {inB : Buffer} {n : Int}
      (h : σ X = some n) : stepA (.var X) σ inB (.running (.const n) σ inB)
  /-- `read()` consumes the head of the input buffer. -/
  | read {σ : State} {n : Int} {inB' : Buffer} :
      stepA .read σ (n :: inB') (.running (.const n) σ inB')
  /-- `+` — reduce left operand. -/
  | add_l {a1 a1' a2 : Aexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepA a1 σ inB (.running a1' σ' inB')) :
      stepA (.add a1 a2) σ inB (.running (.add a1' a2) σ' inB')
  /-- `+` — left errors. -/
  | add_l_err {a1 a2 : Aexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepA a1 σ inB (.error σ' inB')) :
      stepA (.add a1 a2) σ inB (.error σ' inB')
  /-- `+` — reduce right operand. -/
  | add_r {a1 a2 a2' : Aexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepA a2 σ inB (.running a2' σ' inB')) :
      stepA (.add a1 a2) σ inB (.running (.add a1 a2') σ' inB')
  /-- `+` — right errors. -/
  | add_r_err {a1 a2 : Aexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepA a2 σ inB (.error σ' inB')) :
      stepA (.add a1 a2) σ inB (.error σ' inB')
  /-- `+` value axiom. -/
  | add_ax {n1 n2 : Int} {σ : State} {inB : Buffer} :
      stepA (.add (.const n1) (.const n2)) σ inB (.running (.const (n1 + n2)) σ inB)
  /-- `/` — reduce left operand. -/
  | div_l {a1 a1' a2 : Aexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepA a1 σ inB (.running a1' σ' inB')) :
      stepA (.div a1 a2) σ inB (.running (.div a1' a2) σ' inB')
  | div_l_err {a1 a2 : Aexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepA a1 σ inB (.error σ' inB')) :
      stepA (.div a1 a2) σ inB (.error σ' inB')
  | div_r {a1 a2 a2' : Aexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepA a2 σ inB (.running a2' σ' inB')) :
      stepA (.div a1 a2) σ inB (.running (.div a1 a2') σ' inB')
  | div_r_err {a1 a2 : Aexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepA a2 σ inB (.error σ' inB')) :
      stepA (.div a1 a2) σ inB (.error σ' inB')
  /-- `/` non-zero axiom. -/
  | div_ax {n1 n2 : Int} {σ : State} {inB : Buffer} (hne : n2 ≠ 0) :
      stepA (.div (.const n1) (.const n2)) σ inB (.running (.const (n1 / n2)) σ inB)
  /-- `/` divisor-is-zero axiom. Maude: `rl o < I1 / 0, σ, inB > => < error, σ, inB > .` -/
  | div_by_zero {n1 : Int} {σ : State} {inB : Buffer} :
      stepA (.div (.const n1) (.const 0)) σ inB (.error σ inB)
  /-- `/` A1 unevaluated but divisor already 0 — Maude has this as a
  separate rule with `A1 : AExp` (not `I1 : Int`). -/
  | div_by_zero_any {a1 : Aexp} {σ : State} {inB : Buffer} :
      stepA (.div a1 (.const 0)) σ inB (.error σ inB)

/-! ## Boolean small-step -/

inductive stepB : Bexp → State → Buffer → BConfig → Prop
  | le_l {a1 a1' a2 : Aexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepA a1 σ inB (.running a1' σ' inB')) :
      stepB (.le a1 a2) σ inB (.running (.le a1' a2) σ' inB')
  | le_l_err {a1 a2 : Aexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepA a1 σ inB (.error σ' inB')) :
      stepB (.le a1 a2) σ inB (.error σ' inB')
  /-- `I1 <= A2` — reduce right after left is a value (Maude uses `I1 : Int`). -/
  | le_r {n1 : Int} {a2 a2' : Aexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepA a2 σ inB (.running a2' σ' inB')) :
      stepB (.le (.const n1) a2) σ inB (.running (.le (.const n1) a2') σ' inB')
  | le_r_err {n1 : Int} {a2 a2' : Aexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepA a2 σ inB (.error σ' inB')) :
      stepB (.le (.const n1) a2) σ inB (.error σ' inB')
  | le_ax {n1 n2 : Int} {σ : State} {inB : Buffer} :
      stepB (.le (.const n1) (.const n2)) σ inB (.running (.b (decide (n1 ≤ n2))) σ inB)
  | not_arg {b b' : Bexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepB b σ inB (.running b' σ' inB')) :
      stepB (.not b) σ inB (.running (.not b') σ' inB')
  | not_arg_err {b : Bexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepB b σ inB (.error σ' inB')) :
      stepB (.not b) σ inB (.error σ' inB')
  | not_true  {σ : State} {inB : Buffer} : stepB (.not (.b true)) σ inB (.running (.b false) σ inB)
  | not_false {σ : State} {inB : Buffer} : stepB (.not (.b false)) σ inB (.running (.b true) σ inB)
  | and_l {b1 b1' b2 : Bexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepB b1 σ inB (.running b1' σ' inB')) :
      stepB (.and b1 b2) σ inB (.running (.and b1' b2) σ' inB')
  | and_l_err {b1 b2 : Bexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepB b1 σ inB (.error σ' inB')) :
      stepB (.and b1 b2) σ inB (.error σ' inB')
  | and_false {b2 : Bexp} {σ : State} {inB : Buffer} :
      stepB (.and (.b false) b2) σ inB (.running (.b false) σ inB)
  | and_true {b2 : Bexp} {σ : State} {inB : Buffer} :
      stepB (.and (.b true) b2) σ inB (.running b2 σ inB)
  /-- Maude: `crl o < true && B2, σ, inB > => < error, σ', inB' > if < B2, … > => < error, … > .` -/
  | and_true_err_r {b2 : Bexp} {σ σ' : State} {inB inB' : Buffer}
      (h : stepB b2 σ inB (.error σ' inB')) :
      stepB (.and (.b true) b2) σ inB (.error σ' inB')

/-! ## Statement small-step — note: Maude lifts AExp/BExp errors to `halting` -/

inductive stepS : SConfig → SConfig → Prop
  /-- `halt;` rule. -/
  | halt {σ : State} {inB outB : Buffer} :
      stepS (.running .halt σ inB outB) (.halting σ inB outB)
  /-- `X = A ;` — reduce RHS. -/
  | assign_red {X : Id} {a a' : Aexp} {σ σ' : State} {inB inB' outB : Buffer}
      (h : stepA a σ inB (.running a' σ' inB')) :
      stepS (.running (.assign X a) σ inB outB) (.running (.assign X a') σ' inB' outB)
  /-- `X = A ;` — RHS errors ⇒ halting (Maude-faithful lift). -/
  | assign_err_halts {X : Id} {a : Aexp} {σ σ' : State} {inB inB' outB : Buffer}
      (h : stepA a σ inB (.error σ' inB')) :
      stepS (.running (.assign X a) σ inB outB) (.halting σ' inB' outB)
  /-- `X = I ;` axiom. -/
  | assign_ax {X : Id} {n : Int} {σ : State} {inB outB : Buffer}
      (hDecl : σ X ≠ none) :
      stepS (.running (.assign X (.const n)) σ inB outB) (.running .skip (σ.update X n) inB outB)
  /-- `S1 S2` — reduce S1. -/
  | seq_head {s1 s1' s2 : Stmt} {σ σ' : State} {inB inB' outB outB' : Buffer}
      (h : stepS (.running s1 σ inB outB) (.running s1' σ' inB' outB')) :
      stepS (.running (.seq s1 s2) σ inB outB) (.running (.seq s1' s2) σ' inB' outB')
  /-- `S1 S2` — S1 halts ⇒ whole seq halts. -/
  | seq_halt {s1 s2 : Stmt} {σ σ' : State} {inB inB' outB outB' : Buffer}
      (h : stepS (.running s1 σ inB outB) (.halting σ' inB' outB')) :
      stepS (.running (.seq s1 s2) σ inB outB) (.halting σ' inB' outB')
  /-- `skip ; S2 => S2`. -/
  | seq_skip {s2 : Stmt} {σ : State} {inB outB : Buffer} :
      stepS (.running (.seq .skip s2) σ inB outB) (.running s2 σ inB outB)
  /-- `if (B) S1 else S2` — reduce guard. -/
  | ite_red {b b' : Bexp} {s1 s2 : Stmt} {σ σ' : State} {inB inB' outB : Buffer}
      (h : stepB b σ inB (.running b' σ' inB')) :
      stepS (.running (.ite b s1 s2) σ inB outB) (.running (.ite b' s1 s2) σ' inB' outB)
  /-- Guard errors ⇒ halting. -/
  | ite_err_halts {b : Bexp} {s1 s2 : Stmt} {σ σ' : State} {inB inB' outB : Buffer}
      (h : stepB b σ inB (.error σ' inB')) :
      stepS (.running (.ite b s1 s2) σ inB outB) (.halting σ' inB' outB)
  /-- `if (true)`, `if (false)` axioms. -/
  | ite_true  {s1 s2 : Stmt} {σ : State} {inB outB : Buffer} :
      stepS (.running (.ite (.b true)  s1 s2) σ inB outB) (.running s1 σ inB outB)
  | ite_false {s1 s2 : Stmt} {σ : State} {inB outB : Buffer} :
      stepS (.running (.ite (.b false) s1 s2) σ inB outB) (.running s2 σ inB outB)
  /-- `while (B) S => if (B) { S ; while (B) S } else skip` (Maude unfolding). -/
  | while_unfold {b : Bexp} {s : Stmt} {σ : State} {inB outB : Buffer} :
      stepS (.running (.while b s) σ inB outB) (.running (.ite b (.seq s (.while b s)) .skip) σ inB outB)
  /-- `print(A);` — reduce argument. -/
  | print_red {a a' : Aexp} {σ σ' : State} {inB inB' outB : Buffer}
      (h : stepA a σ inB (.running a' σ' inB')) :
      stepS (.running (.print a) σ inB outB) (.running (.print a') σ' inB' outB)
  /-- `print(A);` — argument errors ⇒ halting (faithful Maude lift). -/
  | print_err_halts {a : Aexp} {σ σ' : State} {inB inB' outB : Buffer}
      (h : stepA a σ inB (.error σ' inB')) :
      stepS (.running (.print a) σ inB outB) (.halting σ' inB' outB)
  /-- `print(I);` axiom — append to output buffer. -/
  | print_ax {n : Int} {σ : State} {inB outB : Buffer} :
      stepS (.running (.print (.const n)) σ inB outB) (.running .skip σ inB (outB.snoc n))
  /-- `let X = A in S` — reduce RHS. -/
  | let_red {X : Id} {a a' : Aexp} {s : Stmt} {σ σ' : State} {inB inB' outB : Buffer}
      (h : stepA a σ inB (.running a' σ' inB')) :
      stepS (.running (.letIn X a s) σ inB outB) (.running (.letIn X a' s) σ' inB' outB)
  /-- `let X = A in S` — RHS errors ⇒ halting. -/
  | let_err_halts {X : Id} {a : Aexp} {s : Stmt} {σ σ' : State} {inB inB' outB : Buffer}
      (h : stepA a σ inB (.error σ' inB')) :
      stepS (.running (.letIn X a s) σ inB outB) (.halting σ' inB' outB)
  /-- `let X = I in S` — run the body under the local binding, then restore
  the outer binding in the ambient state while carrying the current local
  value in the syntax (Maude: `let X = Sigma'(X) in S', Sigma'[Sigma(X)/X]`). -/
  | let_body {X : Id} {n n' : Int} {s s' : Stmt} {σ σ' : State}
      {inB inB' outB outB' : Buffer}
      (h : stepS (.running s (σ.update X n) inB outB) (.running s' σ' inB' outB'))
      (hX : σ' X = some n') :
      stepS (.running (.letIn X (.const n) s) σ inB outB)
        (.running (.letIn X (.const n') s') (restoreLocal σ σ' X) inB' outB')
  /-- `let X = I in skip => skip`. -/
  | let_skip {X : Id} {n : Int} {σ : State} {inB outB : Buffer} :
      stepS (.running (.letIn X (.const n) .skip) σ inB outB) (.running .skip σ inB outB)
  /-- `let X = I in S` — halting body; restore the outer binding before
  exposing the halting configuration. -/
  | let_body_halt {X : Id} {n : Int} {s : Stmt} {σ σ' : State}
      {inB inB' outB outB' : Buffer}
      (h : stepS (.running s (σ.update X n) inB outB) (.halting σ' inB' outB')) :
      stepS (.running (.letIn X (.const n) s) σ inB outB)
        (.halting (restoreLocal σ σ' X) inB' outB')
  /-- `spawn {S}` — reduce body; see file docstring for the sequential-
  simplification caveat. -/
  | spawn_red {s s' : Stmt} {σ σ' : State} {inB inB' outB outB' : Buffer}
      (h : stepS (.running s σ inB outB) (.running s' σ' inB' outB')) :
      stepS (.running (.spawn s) σ inB outB) (.running (.spawn s') σ' inB' outB')
  /-- `spawn` of a halting body halts. -/
  | spawn_halt {s : Stmt} {σ σ' : State} {inB inB' outB outB' : Buffer}
      (h : stepS (.running s σ inB outB) (.halting σ' inB' outB')) :
      stepS (.running (.spawn s) σ inB outB) (.halting σ' inB' outB')
  /-- `spawn skip => skip`. -/
  | spawn_done {σ : State} {inB outB : Buffer} :
      stepS (.running (.spawn .skip) σ inB outB) (.running .skip σ inB outB)

/-! ## Reflexive-transitive closure (Maude's `*`) -/

inductive stepsS : SConfig → SConfig → Prop
  | refl (c : SConfig) : stepsS c c
  | cons {c c' c'' : SConfig} (h1 : stepS c c') (h2 : stepsS c' c'') : stepsS c c''

/-! ## Smoke tests -/

section Smoke

private def σxy : State := (State.empty.update "x" 10).update "y" 0

/-- `o < halt; , σ, inB, outB > => < halting, σ, inB, outB >`. -/
example : stepS (.running .halt State.empty [] []) (.halting State.empty [] []) :=
  stepS.halt

/-- `o < 4 / 0, σ, inB > => < error, σ, inB >`. -/
example : stepA (.div (.const 4) (.const 0)) State.empty [] (.error State.empty []) :=
  stepA.div_by_zero

/-- `o < read(), σ, 7::rest > => < 7, σ, rest >`. -/
example : stepA .read State.empty [7, 42] (.running (.const 7) State.empty [42]) :=
  stepA.read

/-- `o < print(5);, σ, inB, outB > => < skip, σ, inB, outB:5 >`. -/
example :
    stepS (.running (.print (.const 5)) State.empty [] [])
          (.running .skip State.empty [] [5]) :=
  stepS.print_ax

/-- `let` steps its body under the local binding and restores the outer
state immediately after the step. -/
example :
    stepS (.running (.letIn "x" (.const 5) (.assign "y" (.var "x"))) σxy [] [])
          (.running (.letIn "x" (.const 5) (.assign "y" (.const 5))) σxy [] []) := by
  have hBody :
      stepS (.running (.assign "y" (.var "x")) (σxy.update "x" 5) [] [])
            (.running (.assign "y" (.const 5)) (σxy.update "x" 5) [] []) := by
    apply stepS.assign_red
    exact stepA.lookup (σ := σxy.update "x" 5) (X := "x") rfl
  have hX : (σxy.update "x" 5) "x" = some 5 := by
    simp [State.update]
  have hRestore : restoreLocal σxy (σxy.update "x" 5) "x" = σxy := by
    funext Y
    by_cases hY : Y = "x"
    · simp [restoreLocal, State.update, σxy, hY]
    · simp [restoreLocal, State.update, σxy, hY]
  simpa [hRestore] using
    (stepS.let_body (X := "x") (n := 5) (n' := 5)
      (s := .assign "y" (.var "x")) (s' := .assign "y" (.const 5))
      (σ := σxy) (σ' := σxy.update "x" 5)
      (inB := []) (inB' := []) (outB := []) (outB' := [])
      hBody hX)

/-- `let` restores an undefined outer binding before exposing `halting`. -/
example :
    stepS (.running (.letIn "x" (.const 5) .halt) State.empty [] [])
          (.halting State.empty [] []) := by
  have hHalt :
      stepS (.running .halt (State.empty.update "x" 5) [] [])
            (.halting (State.empty.update "x" 5) [] []) := by
    simpa using (stepS.halt (σ := State.empty.update "x" 5) (inB := []) (outB := []))
  have hRestore : restoreLocal State.empty (State.empty.update "x" 5) "x" = State.empty := by
    funext Y
    by_cases hY : Y = "x"
    · simp [restoreLocal, State.empty, State.unbind, hY]
    · simp [restoreLocal, State.empty, State.update, State.unbind, hY]
  simpa [hRestore] using
    (stepS.let_body_halt (X := "x") (n := 5) (s := .halt)
      (σ := State.empty) (σ' := State.empty.update "x" 5)
      (inB := []) (inB' := []) (outB := []) (outB' := [])
      hHalt)

end Smoke

end Imp.HW3.Small
