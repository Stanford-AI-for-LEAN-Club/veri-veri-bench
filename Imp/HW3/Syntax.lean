/-!
# CS522 HW3 — IMP++ syntax

Lean 4 AST for the IMP++ language of CS522 Homework 3 — the union of the
five IMP extensions: increment, input/output, halting, threads, locals.

Maude source: `brando90/cs522:HW3/6-imp++/imp-syntax.maude` (commit `3d835de`).

## Over the original IMP we gain

* `halt;`           — abrupt termination (halting extension)
* `spawn { S }`     — thread spawning (threads extension). In this HW3a port
  we model `spawn` with *sequential-execution* semantics for the big-step
  judgement, which is the only honest option at big-step level. A faithful
  concurrent semantics will live in the small-step follow-up (HW3b).
* `int xl;`         — local variable declaration as a *statement*
                      (locals extension). Unlike plain IMP where vars are
                      declared once at program top level, IMP++ lets you
                      introduce them inside a block.
* `read()`          — read-from-input expression (input-output extension)
* `print(a);`       — write-to-output statement (input-output extension)

Plus a desugaring target `let X = A in S` used by the Maude parse-time
equations in `IMP-DESUGARED-SYNTAX`; we carry it as an explicit AST
constructor so Lean users can either build ASTs directly in desugared form
or work with the surface form and invoke `desugar` below.
-/

namespace Imp.HW3

/-- Program variable names. -/
abbrev Id := String

/-- Arithmetic expressions — IMP++ adds `read()`. -/
inductive Aexp where
  | const : Int → Aexp
  | var   : Id  → Aexp
  | add   : Aexp → Aexp → Aexp
  | div   : Aexp → Aexp → Aexp
  | read  : Aexp                          -- ★ IMP++ input extension
deriving Repr, DecidableEq

/-- Boolean expressions — unchanged from IMP. -/
inductive Bexp where
  | b   : Bool → Bexp
  | le  : Aexp → Aexp → Bexp
  | not : Bexp → Bexp
  | and : Bexp → Bexp → Bexp
deriving Repr, DecidableEq

/-- Statements — IMP++ adds `halt`, `spawn`, `int xl;`, `print(a);`, `let`. -/
inductive Stmt where
  | skip    : Stmt
  | assign  : Id → Aexp → Stmt
  | seq     : Stmt → Stmt → Stmt
  | ite     : Bexp → Stmt → Stmt → Stmt
  | while   : Bexp → Stmt → Stmt
  | halt    : Stmt                         -- ★ halting extension
  | spawn   : Stmt → Stmt                  -- ★ threads extension (arg is the spawned block)
  | intDecl : List Id → Stmt               -- ★ locals extension: `int x, y, z ;`
  | print   : Aexp → Stmt                  -- ★ output extension
  | letIn   : Id → Aexp → Stmt → Stmt      -- ★ desugared locals: `let X = A in S`
deriving Repr, DecidableEq

/-- A complete IMP++ program. Per the Maude syntax, `subsort Stmt < Pgm`:
a program is just a top-level statement. -/
abbrev Pgm := Stmt

/-- Program state: partial map from variable names to integers. -/
abbrev State := Id → Option Int

namespace State

/-- Empty state — no variables bound. -/
def empty : State := fun _ => none

/-- Point-wise update `σ[n/X]`. -/
def update (σ : State) (X : Id) (n : Int) : State :=
  fun Y => if Y = X then some n else σ Y

/-- Remove a variable binding (back to undefined) — used by locals on block exit. -/
def unbind (σ : State) (X : Id) : State :=
  fun Y => if Y = X then none else σ Y

/-- Initialise a list of variables all to 0 (matches Maude `Xl |-> 0`). -/
def initZero : List Id → State → State
  | [], σ      => σ
  | X :: Xs, σ => (initZero Xs σ).update X 0

end State

/-! ## Input / Output buffers

The Maude configuration carries two `Buffer` components alongside the
`State`: an input buffer (consumed by `read()`) and an output buffer
(appended to by `print`). We model both as `List Int`, with head = next
to read / most recent output. -/

/-- I/O buffer — a sequence of integers, oldest first. -/
abbrev Buffer := List Int

namespace Buffer

/-- Empty buffer. -/
def empty : Buffer := []

/-- Prepend an integer at the tail of the buffer (`append` for output). -/
def snoc (b : Buffer) (n : Int) : Buffer := b ++ [n]

end Buffer

end Imp.HW3
