# IMP (`veri-veri-bench`) — PL Semantics Notes

**Question:** What PL-semantics framework does our `Imp/` use — big-step,
small-step, denotational, or K?

## Short answer

- **Big-step / natural semantics** (Kahn-style), formalised in Lean 4 as
  an `inductive` relation `Com.terminate : State → Com → State → Prop`.
- **Not** small-step (Plotkin SOS), **not** denotational, **not** K/Maude
  rewriting logic.
- `Aexp.eval` and `Bexp.eval`, by contrast, *are* denotational —
  recursive Lean functions `State → Aexp → ℤ` / `State → Bexp → Bool`.
  So the expression layer is denotational; the command layer is big-step.
  This is the standard split in Winskel / Nielson-Nielson IMP treatments.

## Why it's big-step (evidence from the Lean source)

See `Imp/main.lean`. Every `terminate` rule has the shape:

```
σ  ⊢  c  ⇓  τ
^^^ input state and command                ↑ final state
```

Input state + command go in; the **final** state comes out in a single
derivation. No residual command, no "next configuration" — that is Kahn's
natural semantics = big-step.

In Lean (`Imp/main.lean`):

```lean
inductive terminate : State → Com → State → Prop
  | skip   (σ : State) : terminate σ skip σ
  | assign (σ : State) (X : Str) (a : Aexp) :
      terminate σ (assign X a) (σ.assign X (a.eval σ))
  | comp {c d ρ σ τ} :
      terminate ρ c σ  →  terminate σ d τ  →  terminate ρ (comp c d) τ
  | ite_true  {b c d ρ σ} :
      terminate ρ c σ  →  b.eval ρ = true   →  terminate ρ (ite b c d) σ
  | ite_false {b c d ρ σ} :
      terminate ρ d σ  →  b.eval ρ = false  →  terminate ρ (ite b c d) σ
  | while_true  {b ρ σ τ c} :
      b.eval ρ = true  → terminate ρ c σ → terminate σ (while b c) τ →
      terminate ρ (while b c) τ
  | while_false {b σ c} :
      b.eval σ = false →  terminate σ (while b c) σ
```

### The same rules in inference form (what a textbook would print)

```
───────────────────                      ────────────────────────────────────
σ ⊢ skip ⇓ σ                             σ ⊢ X := a ⇓ σ[X ↦ ⟦a⟧σ]

ρ ⊢ c ⇓ σ     σ ⊢ d ⇓ τ                  ⟦b⟧ρ = true      ρ ⊢ c ⇓ σ
────────────────────────────             ───────────────────────────────
ρ ⊢ c ; d ⇓ τ                            ρ ⊢ if b then c else d ⇓ σ

⟦b⟧ρ = false     ρ ⊢ d ⇓ σ               ⟦b⟧σ = false
─────────────────────────────            ──────────────────────────────
ρ ⊢ if b then c else d ⇓ σ               σ ⊢ while b do c ⇓ σ

⟦b⟧ρ = true    ρ ⊢ c ⇓ σ    σ ⊢ while b do c ⇓ τ
────────────────────────────────────────────────
ρ ⊢ while b do c ⇓ τ
```

### The big-step tells

1. **`ite_true`** evaluates the guard *all the way* to `true`, then the
   branch *all the way* to the final state — two whole sub-derivations
   composed in one step. A small-step / Plotkin-SOS rule would instead
   take one tiny step (`if true then c else d → c`) and leave further
   evaluation to the transitive closure.
2. **`assign`**: the RHS `a` is fully evaluated via `Aexp.eval σ a` in the
   conclusion itself, and the state update happens in one shot.
3. **No residual command** in any conclusion: rules map `(σ, c) → τ`,
   never `(σ, c) → (σ', c')`. That is the defining difference from
   small-step.
4. **`while_true`** mentions `while b do c` *twice* — in the conclusion
   and in the third premise. In a small-step system the unrolling would
   instead be a single rewrite step `while b do c → if b then (c ; while b do c) else skip`
   and evaluation would be left to closure.

Matches Kahn's "natural semantics" (= big-step) as in TAPL ch. 3 or
Nielson-Nielson ch. 2.

## Meta-theorems

In `Imp/main.lean` the `terminate` relation is accompanied by:

- `terminate_unique` — **determinism**:
  `terminate σ c τ → terminate σ c τ' → τ = τ'`.
  Proved by induction on the second derivation, using the `terminate_*`
  inversion lemmas.
- `terminate_skip`, `terminate_assign`, `terminate_comp`, `terminate_ite`,
  `terminate_while` — inversion/introduction characterisations. Turn
  `terminate σ c τ` into an iff on sub-derivations, which drives concrete
  termination proofs.
- `halt` / `output` — total/partial views on `Option State`. `output` is
  `noncomputable` (it uses `Classical.choose` to pick the unique
  terminate-successor); `terminate_unique` then forces the chosen
  successor to be well-defined. Useful when composing programs that may
  diverge, because `none` propagates through `output`.
- `halt_skip`, `halt_assign`, `halt_comp`, `halt_ite`, `halt_while`,
  `halt_iff_output_isSome` — the `halt`-layer analogues.

### Concrete use: the summation example

`Imp/example.lean` uses the framework on:

```
x := 0;
i := 1;
while (i <= n) do { x := x + i; i := i + 1 };
n := 0;
i := 0
```

The file proves:

- `my_program_halts  : ∀ n, halt (some (initial_state n)) my_compiled_program`
- `my_program_output : output (initial_state n) my_compiled_program =
                         some (final_state (∑ i ∈ range (n+1), i))`

The structure of the proof is the one this kind of semantics enables:

1. Model the loop body as a **pure state function** `loopStep`.
2. Show `loopStep` matches the big-step body (`terminate_loopBody`).
3. Prove the loop runs `k = n + 1 - i` times
   (`terminate_while_from`, by induction on `k`).
4. Read off `loopIter_x_start` to get the closed-form sum.

No trace-of-reductions, no continuation, no K configuration — just one
`terminate` derivation plus determinism.

## Where the expression layer is denotational

`Aexp.eval` and `Bexp.eval` are plain total Lean functions
(`State → Aexp → ℤ` and `State → Bexp → Bool`). That is straight
denotational semantics for expressions. It works because `Aexp`/`Bexp` are
pure — no assignment, no loops, no failure — so we don't need a
relational semantics to talk about termination or effects. The big-step
command layer sits on top of this.

## Contrast with the other frameworks

| Framework | Shape of judgment / rule | Our IMP? |
|---|---|---|
| Big-step (Kahn) | `σ ⊢ c ⇓ τ` — whole evaluation in one derivation | **yes** (`Com.terminate`) |
| Small-step (Plotkin SOS) | `⟨c, σ⟩ → ⟨c', σ'⟩` plus transitive closure | no |
| Denotational | `⟦c⟧ : State → State_⊥` as a Lean function | partial — only for `Aexp`/`Bexp` |
| K framework / Maude | Rewriting-logic rules over configurations | no (no Maude in this project) |

## Contrast with cs522 / Grigore

- cs522 (Grigore Roșu, UIUC) defines IMP's semantics in the **K framework**
  via rewriting logic in Maude. The semantics *is* the interpreter —
  `maude` runs it directly.
- Our `Imp/` instead defines a Lean `inductive` proposition and proves
  theorems about it. The semantics is a specification; nothing in `Imp/`
  is itself a runnable IMP interpreter (the parser produces `Com` ASTs but
  there is no `exec : Com → State → State`; you'd have to extract one,
  e.g. from the `output` function, which is noncomputable).

## Contrast with Aeneas (see `notes.md` in this directory)

Both our IMP and Aeneas's LLBC use big-step / natural semantics:

| | Our `Imp/` | Aeneas / LLBC |
|---|---|---|
| Language | toy IMP | Rust (via LLBC subset) |
| Framework | Lean 4 `inductive` relation | Custom calculus (LLBC) in Lean/F\*/Coq/HOL4 |
| Semantics style | Big-step `terminate` | Big-step `Ω ⊢ term ⇒ value ⊣ Ω'` |
| Values | plain `ℤ` in a `State : Str → ℤ` | borrow-centric values (`loan_{s,m}`, `borrow_{s,m}`, `⊥`) |
| Features | skip / assign / comp / ite / while | move/copy/borrow/assign/match/if/... |
| Extras | Determinism, `halt`/`output`, inversion lemmas | Functional translation to pure λ-calculus + symbolic execution |

Same *style* of judgment; very different *value domain* and *tooling*.

## Sources

- Local: `Imp/main.lean`, `Imp/parser.lean`, `Imp/example.lean`.
- `experiments/00_aneas_does_pl_semantics/notes.md` — companion Aeneas analysis.
- Winskel, *The Formal Semantics of Programming Languages*, ch. 2 — IMP big-step.
- Nielson & Nielson, *Semantics with Applications*, ch. 2.
- Pierce, *Types and Programming Languages*, ch. 3 (big-step / natural semantics).
