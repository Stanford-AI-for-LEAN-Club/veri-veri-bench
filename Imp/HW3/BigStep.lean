import Imp.HW3.Syntax

/-!
# CS522 HW3a — IMP++ big-step semantics

Faithful Lean 4 port of the big-step SOS in
`brando90/cs522:HW3/6-imp++/big_step/imp-semantics-bigstep.maude`.

## Configurations

The Maude configurations carry `(syntax, State, Buffer)` at entry and
`(State, Buffer_in, Buffer_out)` or `(error, State, Buffer)` or
`(halting, State, Buffer_in, Buffer_out)` at exit. In Lean we split the
result into an `SResult` sum:

- `state σ inB outB`        — normal termination with updated buffers
- `err   σ inB`             — error result (from div-by-zero inside a Stmt)
- `halted σ inB outB`       — the `halt;` statement was executed

and similarly for AExp / BExp (which in Maude return just `(Int, State, Buf)`
or `(error, State, Buf)` — we use `AResult` / `BResult`).

## Simplifications / honest deviations from Maude

1. **`spawn { S }` is modelled sequentially** at big-step level — we
   just reduce the spawned block as if it were an inlined sub-statement.
   This is the standard big-step treatment; truly concurrent semantics
   require small-step and will land in the HW3b follow-up PR.

2. **Local variable declarations** (`int xl ;`) update the state in place
   with zero-initialised bindings. We *do not* implement lexical scoping
   restoration here; that is easier to model in small-step where block
   entry/exit are explicit points in the reduction.

3. **Error propagation** follows Maude: an arithmetic `error` inside a
   Stmt produces an `SResult.err` which the SEQ rule short-circuits on.

4. **Halting propagation**: once the `halt;` statement fires, it produces
   an `SResult.halted` which subsequent Stmts (via SEQ) absorb without
   further effect, matching the Maude `halting` configuration.
-/

namespace Imp.HW3

/-! ## Result domains -/

/-- Big-step result for an arithmetic expression. -/
inductive AResult where
  | num (n : Int) (σ : State) (inB : Buffer) : AResult
  | err           (σ : State) (inB : Buffer) : AResult

/-- Big-step result for a boolean expression. -/
inductive BResult where
  | bool (v : Bool) (σ : State) (inB : Buffer) : BResult
  | err            (σ : State) (inB : Buffer) : BResult

/-- Big-step result for a statement. -/
inductive SResult where
  /-- Normal termination. -/
  | state  : State → Buffer → Buffer → SResult
  /-- Arithmetic error has propagated up to Stmt level. -/
  | err    : State → Buffer → SResult
  /-- The `halt;` statement was reached. Halting freezes the state and
  both buffers. -/
  | halted : State → Buffer → Buffer → SResult

/-! ## Arithmetic-expression big-step (`< A, σ, inB > ⇓ < v >`)

Maude rule names retained in constructor names where practical. -/

inductive evalA : Aexp → State → Buffer → AResult → Prop
  /-- Integer literal. -/
  | const (n : Int) (σ : State) (inB : Buffer) :
      evalA (.const n) σ inB (.num n σ inB)
  /-- Defined variable lookup. -/
  | var_ok {σ : State} {inB : Buffer} {X : Id} {n : Int}
      (h : σ X = some n) : evalA (.var X) σ inB (.num n σ inB)
  /-- `read()` consumes the head of the input buffer. -/
  | read_ok {σ : State} {n : Int} {inB' : Buffer} :
      evalA .read σ (n :: inB') (.num n σ inB')
  /-- `read()` on an empty input buffer is stuck — we model it as `err`.
  (Maude does not specify; this is a modelling choice flagged in the README.) -/
  | read_err {σ : State} : evalA .read σ [] (.err σ [])
  /-- Addition — normal. -/
  | add {a1 a2 : Aexp} {σ σ1 σ2 : State} {inB inB1 inB2 : Buffer} {n1 n2 : Int}
      (h1 : evalA a1 σ inB (.num n1 σ1 inB1))
      (h2 : evalA a2 σ1 inB1 (.num n2 σ2 inB2)) :
      evalA (.add a1 a2) σ inB (.num (n1 + n2) σ2 inB2)
  /-- Addition — left errors. -/
  | add_err_l {a1 a2 : Aexp} {σ σ1 : State} {inB inB1 : Buffer}
      (h : evalA a1 σ inB (.err σ1 inB1)) :
      evalA (.add a1 a2) σ inB (.err σ1 inB1)
  /-- Addition — right errors (after left is a value). -/
  | add_err_r {a1 a2 : Aexp} {σ σ1 σ2 : State} {inB inB1 inB2 : Buffer} {n1 : Int}
      (h1 : evalA a1 σ inB (.num n1 σ1 inB1))
      (h2 : evalA a2 σ1 inB1 (.err σ2 inB2)) :
      evalA (.add a1 a2) σ inB (.err σ2 inB2)
  /-- Division — normal. -/
  | div_ok {a1 a2 : Aexp} {σ σ1 σ2 : State} {inB inB1 inB2 : Buffer} {n1 n2 : Int}
      (h1 : evalA a1 σ inB (.num n1 σ1 inB1))
      (h2 : evalA a2 σ1 inB1 (.num n2 σ2 inB2)) (hne : n2 ≠ 0) :
      evalA (.div a1 a2) σ inB (.num (n1 / n2) σ2 inB2)
  /-- Division — divisor evaluates to 0. -/
  | div_by_zero {a1 a2 : Aexp} {σ σ1 σ2 : State} {inB inB1 inB2 : Buffer} {n1 : Int}
      (h1 : evalA a1 σ inB (.num n1 σ1 inB1))
      (h2 : evalA a2 σ1 inB1 (.num 0 σ2 inB2)) :
      evalA (.div a1 a2) σ inB (.err σ2 inB2)
  /-- Division — left operand errors. -/
  | div_err_l {a1 a2 : Aexp} {σ σ1 : State} {inB inB1 : Buffer}
      (h : evalA a1 σ inB (.err σ1 inB1)) :
      evalA (.div a1 a2) σ inB (.err σ1 inB1)
  /-- Division — right operand errors. -/
  | div_err_r {a1 a2 : Aexp} {σ σ1 σ2 : State} {inB inB1 inB2 : Buffer} {n1 : Int}
      (h1 : evalA a1 σ inB (.num n1 σ1 inB1))
      (h2 : evalA a2 σ1 inB1 (.err σ2 inB2)) :
      evalA (.div a1 a2) σ inB (.err σ2 inB2)

/-! ## Boolean-expression big-step -/

inductive evalB : Bexp → State → Buffer → BResult → Prop
  | b (v : Bool) (σ : State) (inB : Buffer) : evalB (.b v) σ inB (.bool v σ inB)
  /-- `A1 <= A2` normal. -/
  | le {a1 a2 : Aexp} {σ σ1 σ2 : State} {inB inB1 inB2 : Buffer} {n1 n2 : Int}
      (h1 : evalA a1 σ inB (.num n1 σ1 inB1))
      (h2 : evalA a2 σ1 inB1 (.num n2 σ2 inB2)) :
      evalB (.le a1 a2) σ inB (.bool (decide (n1 ≤ n2)) σ2 inB2)
  /-- `A1 <= A2` left errors. -/
  | le_err_l {a1 a2 : Aexp} {σ σ1 : State} {inB inB1 : Buffer}
      (h : evalA a1 σ inB (.err σ1 inB1)) :
      evalB (.le a1 a2) σ inB (.err σ1 inB1)
  /-- `A1 <= A2` right errors. -/
  | le_err_r {a1 a2 : Aexp} {σ σ1 σ2 : State} {inB inB1 inB2 : Buffer} {n1 : Int}
      (h1 : evalA a1 σ inB (.num n1 σ1 inB1))
      (h2 : evalA a2 σ1 inB1 (.err σ2 inB2)) :
      evalB (.le a1 a2) σ inB (.err σ2 inB2)
  /-- `!true` / `!false`. -/
  | not_t {b : Bexp} {σ σ' : State} {inB inB' : Buffer}
      (h : evalB b σ inB (.bool true σ' inB')) :
      evalB (.not b) σ inB (.bool false σ' inB')
  | not_f {b : Bexp} {σ σ' : State} {inB inB' : Buffer}
      (h : evalB b σ inB (.bool false σ' inB')) :
      evalB (.not b) σ inB (.bool true σ' inB')
  | not_err {b : Bexp} {σ σ' : State} {inB inB' : Buffer}
      (h : evalB b σ inB (.err σ' inB')) :
      evalB (.not b) σ inB (.err σ' inB')
  /-- `B1 && B2`. -/
  | and_false {b1 b2 : Bexp} {σ σ1 : State} {inB inB1 : Buffer}
      (h : evalB b1 σ inB (.bool false σ1 inB1)) :
      evalB (.and b1 b2) σ inB (.bool false σ1 inB1)
  | and_true {b1 b2 : Bexp} {σ σ1 σ2 : State} {inB inB1 inB2 : Buffer} {v : Bool}
      (h1 : evalB b1 σ inB (.bool true σ1 inB1))
      (h2 : evalB b2 σ1 inB1 (.bool v σ2 inB2)) :
      evalB (.and b1 b2) σ inB (.bool v σ2 inB2)
  | and_err_l {b1 b2 : Bexp} {σ σ1 : State} {inB inB1 : Buffer}
      (h : evalB b1 σ inB (.err σ1 inB1)) :
      evalB (.and b1 b2) σ inB (.err σ1 inB1)

/-! ## Statement big-step

`evalS s σ inB outB r` ≅ Maude `< s, σ, inB, outB > ⇓ r`. We add `outB` as
an input to `evalS` because statements can both read *and* write buffers
(via nested `read()` expressions and `print(a);` statements respectively). -/

inductive evalS : Stmt → State → Buffer → Buffer → SResult → Prop
  /-- `skip` — no-op. -/
  | skip (σ : State) (inB outB : Buffer) :
      evalS .skip σ inB outB (.state σ inB outB)
  /-- `X = A ;` normal case (Maude: `Sigma(X) =/=Bool undefined`). -/
  | assign_ok {σ σ' : State} {inB inB' outB : Buffer} {X : Id} {a : Aexp} {n : Int}
      (hDecl : σ X ≠ none) (hA : evalA a σ inB (.num n σ' inB')) :
      evalS (.assign X a) σ inB outB (.state (σ'.update X n) inB' outB)
  /-- `X = A ;` — RHS errors. -/
  | assign_err {σ σ' : State} {inB inB' outB : Buffer} {X : Id} {a : Aexp}
      (hA : evalA a σ inB (.err σ' inB')) :
      evalS (.assign X a) σ inB outB (.err σ' inB')
  /-- `S1 S2` — normal case. -/
  | seq_ok {s1 s2 : Stmt} {σ σ' : State} {inB inB' outB outB' : Buffer} {r : SResult}
      (h1 : evalS s1 σ inB outB (.state σ' inB' outB'))
      (h2 : evalS s2 σ' inB' outB' r) :
      evalS (.seq s1 s2) σ inB outB r
  /-- `S1 S2` — first statement errors; skip S2. -/
  | seq_err_l {s1 s2 : Stmt} {σ σ' : State} {inB inB' outB : Buffer}
      (h : evalS s1 σ inB outB (.err σ' inB')) :
      evalS (.seq s1 s2) σ inB outB (.err σ' inB')
  /-- `S1 S2` — first statement halts; skip S2 (halt absorbs). -/
  | seq_halted_l {s1 s2 : Stmt} {σ σ' : State} {inB inB' outB outB' : Buffer}
      (h : evalS s1 σ inB outB (.halted σ' inB' outB')) :
      evalS (.seq s1 s2) σ inB outB (.halted σ' inB' outB')
  /-- `if (B) S1 else S2` — guard true. -/
  | ite_true {b : Bexp} {s1 s2 : Stmt} {σ σ' : State} {inB inB' outB : Buffer} {r : SResult}
      (hb : evalB b σ inB (.bool true σ' inB')) (h : evalS s1 σ' inB' outB r) :
      evalS (.ite b s1 s2) σ inB outB r
  /-- `if (B) S1 else S2` — guard false. -/
  | ite_false {b : Bexp} {s1 s2 : Stmt} {σ σ' : State} {inB inB' outB : Buffer} {r : SResult}
      (hb : evalB b σ inB (.bool false σ' inB')) (h : evalS s2 σ' inB' outB r) :
      evalS (.ite b s1 s2) σ inB outB r
  /-- `if (B) …` — guard errors. -/
  | ite_err {b : Bexp} {s1 s2 : Stmt} {σ σ' : State} {inB inB' outB : Buffer}
      (hb : evalB b σ inB (.err σ' inB')) :
      evalS (.ite b s1 s2) σ inB outB (.err σ' inB')
  /-- `while (B) S` — guard false, loop terminates in place. -/
  | while_false {b : Bexp} {s : Stmt} {σ σ' : State} {inB inB' outB : Buffer}
      (hb : evalB b σ inB (.bool false σ' inB')) :
      evalS (.while b s) σ inB outB (.state σ' inB' outB)
  /-- `while (B) S` — guard errors. -/
  | while_err_guard {b : Bexp} {s : Stmt} {σ σ' : State} {inB inB' outB : Buffer}
      (hb : evalB b σ inB (.err σ' inB')) :
      evalS (.while b s) σ inB outB (.err σ' inB')
  /-- `while (B) S` — guard true, unroll. Matches Maude's recursive
  `< S while (B) S, Sigma, inB, outB > => < r >`. -/
  | while_true {b : Bexp} {s : Stmt} {σ σ' : State} {inB inB' outB : Buffer} {r : SResult}
      (hb : evalB b σ inB (.bool true σ' inB'))
      (h : evalS (.seq s (.while b s)) σ' inB' outB r) :
      evalS (.while b s) σ inB outB r
  /-- `halt;` — freezes the state and both buffers into a `halted` result. -/
  | halt (σ : State) (inB outB : Buffer) :
      evalS .halt σ inB outB (.halted σ inB outB)
  /-- `print(A);` — normal. -/
  | print_ok {σ σ' : State} {inB inB' outB : Buffer} {a : Aexp} {n : Int}
      (hA : evalA a σ inB (.num n σ' inB')) :
      evalS (.print a) σ inB outB (.state σ' inB' (outB.snoc n))
  /-- `print(A);` — argument errors. -/
  | print_err {σ σ' : State} {inB inB' outB : Buffer} {a : Aexp}
      (hA : evalA a σ inB (.err σ' inB')) :
      evalS (.print a) σ inB outB (.err σ' inB')
  /-- `int xl;` — declare-and-zero-initialise each variable. Matches the
  Maude desugaring that turns `int xl` into repeated `let X = 0 in ...`. -/
  | intDecl (σ : State) (inB outB : Buffer) (xl : List Id) :
      evalS (.intDecl xl) σ inB outB (.state (State.initZero xl σ) inB outB)
  /-- `let X = A in S` — bind X, run S (possibly shadowing / overwriting X).
  We do NOT restore X on exit at big-step level — small-step is the better
  place to express that, flagged in the file docstring. -/
  | letIn_ok {σ σA σ' : State} {inB inB' inB'' outB outB' : Buffer}
             {X : Id} {a : Aexp} {n : Int} {s : Stmt} {r : SResult}
      (hA : evalA a σ inB (.num n σA inB'))
      (h : evalS s (σA.update X n) inB' outB r) : evalS (.letIn X a s) σ inB outB r
  /-- `let X = A in S` — binding-RHS errors. -/
  | letIn_err {σ σ' : State} {inB inB' outB : Buffer} {X : Id} {a : Aexp} {s : Stmt}
      (hA : evalA a σ inB (.err σ' inB')) :
      evalS (.letIn X a s) σ inB outB (.err σ' inB')
  /-- `spawn { S }` — executed sequentially in the big-step port (see
  file docstring §"Simplifications"). -/
  | spawn {σ : State} {inB outB : Buffer} {s : Stmt} {r : SResult}
      (h : evalS s σ inB outB r) : evalS (.spawn s) σ inB outB r

/-! ## Program-level

Per Maude `subsort Stmt < Pgm`, an IMP++ program is just a top-level Stmt. -/

/-- Execute an IMP++ program on an input buffer; produce an `SResult`. -/
inductive evalP : Pgm → Buffer → SResult → Prop
  | run {p : Pgm} {inB : Buffer} {r : SResult}
      (h : evalS p State.empty inB Buffer.empty r) : evalP p inB r

/-! ## Smoke tests — small IMP++ programs -/

section Smoke

/-- `halt;` produces a `halted` result with empty state + buffers. -/
example : evalS .halt State.empty [] []
            (.halted State.empty [] []) :=
  evalS.halt _ _ _

/-- `print(1);` on the empty initial config appends `1` to the output buffer. -/
example :
    evalS (.print (.const 1)) State.empty [] []
      (.state State.empty [] [1]) := by
  have := evalS.print_ok (σ := State.empty) (σ' := State.empty)
            (inB := []) (inB' := []) (outB := [])
            (a := .const 1) (n := 1)
            (hA := evalA.const 1 State.empty [])
  simpa [Buffer.snoc] using this

/-- `read()` consumes the head of the input buffer. -/
example :
    evalA .read State.empty [42, 17] (.num 42 State.empty [17]) :=
  evalA.read_ok

end Smoke

end Imp.HW3
