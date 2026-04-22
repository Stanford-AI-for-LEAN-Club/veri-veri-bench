# CS522 HW3 in Lean 4 — IMP++

CS522 HW3 asks us to combine the five IMP extensions (increment,
input-output, halting, threads, locals) into **IMP++** and provide a
**type system (big-step)**, a **small-step SOS**, and **one of** big-step
SOS or denotational semantics.

To keep PRs independently reviewable under the mega-QA protocol, we land
HW3 as **several sequential PRs**:

| Part   | Scope                                               | Status          |
|--------|-----------------------------------------------------|-----------------|
| HW3a   | IMP++ **Syntax** + **Big-Step SOS**                 | this PR          |
| HW3b   | IMP++ **Small-Step SOS** — faithful `spawn` concurrency | follow-up     |
| HW3c   | IMP++ **Denotational** (above-spec bonus)           | follow-up       |
| HW3d   | IMP++ **Type-System (big-step)**                    | follow-up       |

## Files in this PR

| File                          | Maps to (Maude)                                                                             |
|-------------------------------|---------------------------------------------------------------------------------------------|
| `Imp/HW3/Syntax.lean`         | `HW3/6-imp++/imp-syntax.maude` (+ `state.maude` + `buffer.maude`)                            |
| `Imp/HW3/BigStep.lean`        | `HW3/6-imp++/big_step/imp-semantics-bigstep.maude`                                          |
| `Imp/HW3.lean`                | aggregate                                                                                    |

## Design summary

### Syntax additions (from IMP to IMP++)

* `Aexp.read` — read-from-input expression
* `Stmt.halt` — abrupt-termination statement
* `Stmt.spawn : Stmt → Stmt` — thread-spawning (modeled sequentially at big-step; see below)
* `Stmt.intDecl : List Id → Stmt` — local variable declaration as a Stmt
* `Stmt.print : Aexp → Stmt` — output statement
* `Stmt.letIn : Id → Aexp → Stmt → Stmt` — desugared form for locals

### Result domains

Maude's `(State, Buffer_in, Buffer_out)` trio + `<error, …>` and
`<halting, …>` become three inductives:

* `AResult = num Int σ inB | err σ inB`
* `BResult = bool Bool σ inB | err σ inB`
* `SResult = state σ inB outB | err σ inB | halted σ inB outB`

### Honest deviations from Maude (flagged)

1. **`spawn { S }` reduced sequentially** at big-step level — see the file
   docstring. Concurrent semantics requires small-step and lands in HW3b.
2. **No lexical-scope restoration** on `let X = A in S` exit at big-step.
   Small-step (HW3b) is the natural place for that.
3. **Empty-input `read()` is `err`** — Maude does not specify; we pick
   `err` for determinism in Lean. Revisit once the small-step port is in.

## Verification status

* `lake build` passes (3114 jobs).
* Smoke examples in `BigStep.lean` cover `halt;`, `print(1);`, and
  `read()` with non-empty input buffer.
* Behavioural verification against the Maude `imp-bigstep.maude` /
  `imp-programs.maude` battery: not run (no local maude binary).
* Independent review requested from Stepan Nesterov per
  `experiments/02_do_all_cs522_in_Lean/prompt.md`.
