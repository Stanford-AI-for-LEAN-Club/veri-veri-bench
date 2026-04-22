# Aeneas vs. Grigore / cs522 — PL Semantics Notes

**Question:** Does Aeneas (https://lean-lang.org/use-cases/aeneas/) do for Rust what Grigore Roșu does in cs522 for PL semantics? If yes, what semantics framework — big-step, small-step, denotational, or K?

## Short answer

- **Partially yes**, in the broad sense that both give a formal operational semantics to a real language and enable mechanized reasoning — **but the mechanism is fundamentally different**.
- Aeneas uses a **custom big-step / natural-semantics-style operational semantics** over a calculus called **LLBC** (Low-Level Borrow Calculus).
- **Not** K framework, **not** small-step (Plotkin SOS), **not** denotational.
- Aeneas additionally does something K/cs522 does not: it **translates** Rust to a pure functional program in Lean / F\* / Coq / HOL4 for verification (the "functional translation"). cs522 does semantics directly in Maude/K rewriting logic; Aeneas does semantics + compile-to-pure-λ-calculus.

## Why it's big-step (evidence from Fig. 4 of the ICFP 2022 paper)

Every rule has the shape:

```
Ω ⊢ term  ⇒  value  ⊣  Ω'
^input^      ^final^  ^final^
```

Input term + input environment go in; the **final** value and **final** environment come out in a single derivation. That is Kahn-style natural semantics = big-step.

### Selected rules (arXiv 2206.07185, Fig. 4, p. 15)

```
E-Mut-Borrow                                E-Shared-Or-Reserved-Borrow
  Ω(p) ⇒ v                                    Ω(p) ⇒ v
  {⊥, loan, borrow_r} ∉ v                     {⊥, loan_m, borrow_r} ∉ v
  *s ∉ p   ℓ fresh                            ℓ fresh    Ω' = Ω[p ↦ v']
  Ω(p) ← loan_m ℓ ⇒ Ω'                        (v' = loan_s{ℓ∪ℓ̄}v''  if v=loan_s{ℓ̄}v'')
  ──────────────────────────                  (     loan_s{ℓ}v         otherwise)
  Ω ⊢ &mut p ⇒ borrow_m ℓ v ⊣ Ω'              ──────────────────────────
                                              Ω ⊢ &p ⇒ borrow_{r,s} ℓ ⊣ Ω'

E-Move                                      E-Copy
  Ω(p) ⇒ v                                    Ω(p) ⇒ v
  {⊥, loan, borrow_r} ∉ v                     {⊥, loan_m, borrow_{m,r}} ∉ v
  {*m, *s} ∉ p   Ω(p) ← ⊥ ⇒ Ω'                Ω ⊢ copy v ⇒ v' ⊣ Ω'
  ──────────────────                          ─────────────────────
  Ω ⊢ move p ⇒ v ⊣ Ω'                         Ω ⊢ copy p ⇒ v' ⊣ Ω'

E-IfThenElse-T                              E-Assign
  Ω ⊢ op ⇒ true ⊣ Ω'                          Ω ⊢ rv ⇒ v ⊣ Ω'    Ω'(p) ⇒ v_p
  Ω' ⊢ s1 ⇒ r ⊣ Ω''                           v_p has no outer loans    x_old fresh
  ──────────────────────────────              Ω'(p) ← v ⇒ Ω''   Ω''' = Ω''[x_old ↦ v_p]
  Ω ⊢ if op then s1 else s2 ⇒ r ⊣ Ω''         ─────────────────────────────
                                              Ω ⊢ p := rv ⇒ () ⊣ Ω'''

E-Match
  Ω ⊢ p ⇒_s C[f = v]      Ω ⊢ s ⇒ r ⊣ Ω'
  ────────────────────────────────────────────
  Ω ⊢ match p with … | C → s | … ⇒ r ⊣ Ω'
```

### The big-step tells

1. **E-IfThenElse-T** evaluates the condition *all the way* to `true`, then the branch *all the way* to result `r` — two whole sub-derivations composed in one step. A small-step / Plotkin-SOS rule would instead take one tiny step (`if true then s1 else s2 → s1`) and leave further evaluation to the transitive closure.
2. **E-Assign**: `rv` is fully evaluated to `v` in its premise, then the store is updated in one shot.
3. **No residual term / continuation** in any conclusion: rules map `term → value`, never `term → term'`. That is the defining difference from small-step.

This matches Kahn's "natural semantics" (= big-step) as in Pierce TAPL ch. 3 or Nielson & Nielson ch. 2.

## Honest caveats

- The paper never writes "big-step" or "small-step" itself — I grep'd the PDF, 0 occurrences. The classification comes from the shape of the judgment, which is the standard textbook way to classify.
- The paper's Fig. 4 caption says "Selected **Reduction Rules** for LLBC" — loose terminology; the structure is unambiguously big-step / evaluation semantics, not Plotkin SOS.
- On top of this concrete big-step semantics, Aeneas layers a **symbolic execution** (ICFP 2024 paper "Sound Borrow-Checking for Rust via Symbolic Semantics") that actually drives the tool. That symbolic layer is not itself "big-step" in the same textbook sense — it manipulates symbolic values — but the ground-truth LLBC semantics it is proven sound against *is* the big-step one above.

## What LLBC itself is

- **Value-based, ownership-centric**: environment Ω maps variables to borrow-centric values (`loan_s`, `loan_m`, `borrow_s`, `borrow_m ℓ v`, `⊥`). No heap, no addresses, no pointer arithmetic (per the abstract).
- Soundness of borrows enforced by a **semantic criterion based on loans**, not a syntactic lifetime discipline.
- Targets Lean, F\*, Coq, HOL4 via the functional translation.

## cs522 / Grigore — contrast

- cs522 (Grigore Roșu, UIUC) uses the **K framework** on top of **Maude** (rewriting logic / matching logic).
- Confirmed locally: every `HW{1,2,3,4,6}-Maude/` dir under `/Users/brandomiranda/veri-veri-bench/cs522/` contains `builtins.maude` and `.maude` sources.
- K defines language semantics as **rewrite rules over program configurations**; the semantics *is* the executable interpreter. Directly executable in Maude.
- So: K = rewriting-logic framework; Aeneas = bespoke big-step + functional translation. Different machinery, overlapping goal (formal reasoning about real programs).

## Summary table

| | cs522 / Grigore | Aeneas |
|---|---|---|
| Language | IMP (+ extensions in HWs) | Rust (via LLBC subset) |
| Framework | K framework in Maude | Custom calculus (LLBC) in Lean/F\*/Coq/HOL4 |
| Semantics style | Rewriting logic / matching logic | Big-step / natural semantics |
| Execution | Semantics *is* the interpreter (Maude runs it) | Semantics proven about, plus functional translation to pure λ-calculus |
| Borrow/ownership | n/a | First-class (loan / borrow values in Ω) |

## Sources

- [Aeneas: Rust Verification by Functional Translation — arXiv 2206.07185 (ICFP 2022)](https://arxiv.org/abs/2206.07185)
- [arXiv PDF (Fig. 4 on p. 15)](https://arxiv.org/pdf/2206.07185)
- [Aeneas project site](https://aeneasverif.github.io/)
- [AeneasVerif/aeneas on GitHub](https://github.com/AeneasVerif/aeneas)
- [Sound Borrow-Checking for Rust via Symbolic Semantics (ICFP 2024)](https://dl.acm.org/doi/full/10.1145/3674640)
- [Aeneas: Bridging Rust to Lean — lean-lang.org](https://lean-lang.org/use-cases/aeneas/)
- Local: `/Users/brandomiranda/veri-veri-bench/cs522/HW*-Maude/` (confirms K/Maude usage in cs522)
