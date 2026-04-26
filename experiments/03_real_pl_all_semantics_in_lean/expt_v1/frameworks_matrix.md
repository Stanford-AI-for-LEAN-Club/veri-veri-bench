# CS522 Frameworks × Language Features

**TLDR:** This experiment instantiates **all 8** CS522 semantic frameworks on the chosen real language. This file lists which framework owns which file, what the judgment looks like, what equivalence theorem ties it back to BigStep, and which Maude reference under `cs522/` it ports from.

---

## The 8 frameworks (in implementation order)

Order is: easier → harder, with reusable lemmas accumulating along the way. BigStep is the *reference judgment*; every other framework must be proved equivalent to BigStep on terminating programs (this is *the* mathematical guarantee — see `verification_spec.md` layer (b)).

| # | Framework | Lean file | Judgment shape | Equiv-thm | CS522 / Roșu reference | Existing repo precedent |
|---|---|---|---|---|---|---|
| 1 | **Big-step SOS** (Kahn / natural) | `Imp/Real/<Lang>/BigStep.lean` | `σ ⊢ s ⇓ τ` (Lean: `inductive Eval : State → Stmt → Result → Prop`) | *(reference)* | Roșu ch. 3, Fig. 3.7; CS522 HW1 (Ex. 56) | `Imp/main.lean`, `Imp/HW1/BigStep.lean`, `Imp/HW3/BigStep.lean` |
| 2 | **Small-step SOS** (Plotkin) | `Imp/Real/<Lang>/SmallStep.lean` | `⟨s, σ⟩ → ⟨s', σ'⟩` (Lean: `inductive Step`) + transitive closure `Step⋆` | `Eval s σ τ ↔ Step⋆ ⟨s, σ⟩ ⟨skip, τ⟩` | Roșu ch. 3 §3.5, Fig. 3.14–3.15; HW1 (Ex. 70) | `Imp/HW1/SmallStep.lean`, `Imp/HW3/SmallStep.lean` |
| 3 | **Denotational** (CPO + fixpoint) | `Imp/Real/<Lang>/Denotational.lean` | `⟦s⟧ : State → Option State` (or `→ State_⊥`) | `Eval s σ τ ↔ ⟦s⟧ σ = some τ` | Roșu ch. 3 §3.6, Fig. 3.20; HW2 (Ex. 80–83) | `Imp/HW2/Denotational.lean` |
| 4 | **MSOS** (Modular SOS) | `Imp/Real/<Lang>/MSOS.lean` | Labelled small-step `⟨s, σ⟩ —λ→ ⟨s', σ'⟩` with label algebra `λ` | `MSOS ⇒ SmallStep` (label-erasure projection); reverse direction by induction | Mosses 2004; CS522 HW4 (MSOS section); Roșu ch. 4 | none in repo — new |
| 5 | **RSEC** (Reduction Semantics with Evaluation Contexts) | `Imp/Real/<Lang>/RSEC.lean` | `E[s] → E[s']` with `E ::= □ | E ; s | …` | `RSEC ⇔ SmallStep` | Felleisen-Hieb 1992; CS522 HW4 (RSEC section); Roșu ch. 5 | none in repo — new |
| 6 | **CHAM** (Chemical Abstract Machine) | `Imp/Real/<Lang>/CHAM.lean` | Multiset-rewriting on configuration "solutions" | `CHAM ⇔ SmallStep` (or directly to BigStep) | Berry-Boudol 1992; CS522 HW4 (CHAM section); Roșu ch. 6 | none in repo — new |
| 7 | **K / rewriting logic** | `Imp/Real/<Lang>/K.lean` | Rewriting rules over heterogeneous configurations (cells `〈_〉_`) | `K ⇔ SmallStep` | Roșu ch. 7; cs522/HW*-Maude/*.maude (the Maude files *are* K) | reference: `cs522/HW{1,2,3,4}-Maude/`; Lean port new |
| 8 | **λ-calculus / Type system** | `Imp/Real/<Lang>/Lambda.lean` | (a) CBV λ-calculus translation `T : Stmt → λ` + (b) simple types Γ ⊢ s : τ | `(a)` `Eval s σ τ ↔ T(s) ↓ T(τ)` (Felleisen embed); `(b)` progress + preservation | Roșu ch. 8–9; CS522 HW6, Extra-Credit | none in repo — new |

## Language-feature ownership

For each framework, certain language features are routine and others are research-grade. This table flags which combinations are "do it the standard way" vs. which need a design note in the file's docstring.

| Feature ↓ / Framework → | BigStep | SmallStep | Denot | MSOS | RSEC | CHAM | K | λ |
|---|---|---|---|---|---|---|---|---|
| Pure expressions (arith, bool) | ✓ standard | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Mutable variables (assign) | ✓ standard | ✓ | ✓ (state-monad) | ✓ | ✓ | ✓ (cell) | ✓ | ✓ (refs) |
| `while` / loops | ✓ standard | ✓ standard | ✓ (lfp) | ✓ | ✓ | ✓ | ✓ | ✓ (Y combinator) |
| Exceptions / `raise` | ✓ as result variant | ✓ as halting cfg | ⚠ continuation passing | ✓ via labels | ✓ via "stuck" reduction | ✓ via boiling | ✓ via `K` cell | ✓ (Filinski) |
| Mutable lists / refs / dicts | ✓ heap in `State` | ✓ | ⚠ store-passing | ✓ | ✓ | ✓ (cell) | ✓ | ✓ refs |
| Functions / closures | ✓ env in cfg | ✓ closures | ⚠ requires env-CPO | ✓ | ✓ | ✓ | ✓ | ✓ native |
| Exceptions × closures interaction | ⚠ scoping | ⚠ scoping | ⚠ both | ⚠ | ⚠ | ⚠ | ⚠ | ⚠ |
| I/O (`print`, `read`) | ✓ buffer-threading (HW3 pattern) | ✓ | ⚠ `IO` monad | ✓ via labels (the MSOS use case) | ✓ | ✓ | ✓ | ✓ |
| Threads / `spawn` | ⚠ sequentialised at big-step | ✓ interleaving | ⚠ traces | ✓ labels | ✓ | ✓ native | ✓ native | ⚠ (CCS encoding) |
| Modules / imports | ✓ module env | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |

`✓` = standard pattern, just port it. `⚠` = needs an explicit design choice; document the choice in the file's `/-! ... -/` doc-block at top.

## Implementation strategy per file

Every framework file follows the same skeleton. A template lives at `templates/framework_skeleton.lean.template` (created during the run, not now).

```lean
/-!
# <Lang> — <Framework name>

Faithful port of <CS522 reference: file or chapter>. Owns: <feature list>.

## Judgment shape
<paste judgment shape from table>

## Equivalence to BigStep
<state the theorem; either prove or `axiom` with TODO(equiv) comment>

## Faithful deviations / design notes
<bullet list>
-/

import Imp.Real.<Lang>.Syntax
-- import Imp.Real.<Lang>.BigStep   -- only for the equivalence theorem

namespace Imp.Real.<Lang>

inductive <Judgment> : <args> → <args> → Prop where
  | <constructor1> : ...
  | <constructor2> : ...
  ...

theorem determinism_or_progress_or_preservation : ...
  := ...

theorem equiv_to_bigstep : ∀ ..., <this judgment> ↔ <BigStep judgment>
  := ...

end Imp.Real.<Lang>
```

## Acceptance criteria per framework

A framework file is "done" when:

1. `lake build` compiles the file with no `sorry`. `axiom` is permitted only with `TODO(equiv)` and only on the equivalence theorem.
2. The `verification_spec.md` layer (a) test corpus passes (≥ 95% on edge-cases).
3. At least one direction of the cross-framework equivalence theorem is closed (forward direction `<this> → BigStep`).
4. The file's `/-! ... -/` doc-block cites the relevant Roșu textbook section + (if applicable) the Maude reference file under `cs522/`.

When all 8 frameworks are done, `Imp/Real/<Lang>/Verification.lean` ties them together and gates the diamond of full bi-directional equivalences.
