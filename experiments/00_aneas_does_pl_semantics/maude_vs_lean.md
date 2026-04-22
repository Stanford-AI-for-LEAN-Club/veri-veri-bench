# Maude vs. Lean — why does Lean exist if Maude exists?

**Question:** Maude (used in cs522 and the K framework) and Lean (used
by Aeneas, Mathlib, ...) both let you do formal/mechanized reasoning
about programs and math. They are not the same. Why does each exist if
the other one does?

## TL;DR

- **Maude** is an implementation of **rewriting logic** + order-sorted
  equational logic. It is at heart an **executable specification
  language** — you write rules, Maude *runs them*. Reasoning is mostly
  by execution, search, model checking, and (with add-ons) inductive
  proof.
- **Lean** is a **dependently-typed proof assistant** (Calculus of
  Inductive Constructions + extras). Proofs are **terms** type-checked
  by a small trusted kernel; you build them via tactics. It also
  doubles as a general-purpose functional language (Lean 4).
- They share the goal of "mechanical reasoning about formal systems"
  but answer very different design pressures, so they coexist rather
  than compete.

## What each system *is*

| | Maude | Lean (4) |
|---|---|---|
| Logical foundation | Order-sorted equational logic + rewriting logic (Meseguer) | Dependent type theory (CIC) + propext, quotients, choice |
| Primary artifact | A **rewrite theory** — sorts, ops, equations, rules | A **type-checked term** — usually one whose type is the proposition you want |
| Primary mode | Execute / search / model-check the theory | Construct + check proof terms (interactively, via tactics) |
| "Proof" means | Reduction in rewriting logic; ITP add-ons; external termination/confluence checkers | A term whose type matches; checked by the kernel |
| Built-in concurrency model | Yes — rewriting logic *is* a concurrency calculus | No (you'd model it on top, e.g. as an inductive relation) |
| Reflection | Yes — Maude is reflective (META-LEVEL module) | Yes — Lean 4 has macros / elaborators / metaprogramming in Lean itself |
| Compiles to | Internal rewriter (and Maude programs *are* the executables) | Native code (Lean 4 has a compiler); also serves as a programming language |
| Headline application | K framework, Maude-NPA (security protocols), language semantics teaching, biological systems | Mathlib (formal mathematics), verified software (Aeneas, etc.), research math (Liquid Tensor, Polynomial Freiman–Ruzsa) |
| Origin | OBJ family → Maude (José Meseguer, SRI then UIUC, 1990s) | Lean 1 (Leonardo de Moura, MSR, 2013) → Lean 4 (Lean FRO, AWS, 2021+) |

## Why Lean exists *despite* Maude

Several independent reasons. None of them is "Maude is bad" — they are
about *fit*.

### 1. Different logics fit different problems

- Rewriting logic excels at **transition-like** systems: language
  semantics, concurrent processes, security protocols. The "rules =
  concurrent transitions" intuition is built in. cs522 leans on this.
- Dependent type theory excels at **mathematical structure with
  proofs-as-terms**: types depending on values, large hierarchies of
  structures, theorems whose statement involves arbitrary
  quantification. Mathlib needs this — you can't comfortably state "for
  every Hausdorff topological group..." as a Maude rewrite theory.

You *can* encode either logic in the other in principle. In practice,
the encoding tax is large enough that you pick the host whose
primitives match your problem.

### 2. Proof-checking story

- Maude: the engine **runs** your theory; correctness arguments often
  rest on (a) running it (test/model-check), (b) reasoning meta-level
  about the rules (e.g. confluence + termination ⇒ uniqueness of
  normal forms), (c) tools like ITP for Maude or Maude's narrowing for
  inductive theorems.
- Lean: there is one tiny kernel that **checks** every proof. The
  trusted-base story is unusually small for a modern prover. Tactics
  can be arbitrarily large/complex; their output (a term) is what gets
  trusted, not the tactic itself. This matters when you are formalizing
  PhD-level math and want a single trust anchor.

These are *different* trust models. Maude: "I trust the rewriter and
the meta-tools." Lean: "I trust the kernel; everything else is
elaborated into kernel-checkable terms."

### 3. What "doing math" feels like

- Mathlib (Lean) currently formalizes ~real analysis, measure theory,
  scheme theory, perfectoid spaces, etc. — research-level math. The
  proofs are written as a mix of structured tactic blocks and term-mode
  proofs.
- There is no Maude analogue of Mathlib at this scale. Maude's strong
  suit is *executable spec* + *property checking*, not building a
  hierarchy of mathematical structures.

### 4. Programming-language host

- Lean 4 is also a general-purpose programming language: native
  compilation, IO, performance close to OCaml/Haskell, custom syntax
  via macros. You can write the proof assistant *inside the language*.
  Lean's elaborator and tactic framework are written in Lean.
- Maude is a specification/execution engine for rewrite theories; it
  is not where you'd write a web server or a tensor library.

### 5. Different communities, different deliverables

- Maude community: PL semantics (UIUC, Grigore Roșu), security
  protocols (Maude-NPA), systems biology, formal methods education.
  Deliverables: executable semantics, model-checked properties,
  algebraic specifications.
- Lean community: research mathematicians (Tao, Scholze), formal-
  methods researchers, verified-software groups (Aeneas → Lean
  backend), industry (AWS). Deliverables: formalized math, verified
  programs.

These communities sometimes meet (Aeneas is the obvious bridge: source
language with operational/big-step semantics, target = Lean term where
the *math* of the program lives), but mostly they work on disjoint
problems.

### 6. Historical answer

- Maude (1990s) is the *executable* descendant of the OBJ algebraic
  specification family.
- Lean (2013→) is a redesign in the Coq/Isabelle/HOL lineage, focused
  on performance, metaprogramming, and a friendlier tactic story than
  Coq. It exists because the existing CIC-style provers had ergonomics
  + performance issues for math at scale.

Neither was built to obsolete the other. They started from different
ancestors aimed at different deliverables.

## Where they meet (and where they don't)

- **Both** can express operational semantics. cs522 does it as K/Maude
  rewrite rules; Aeneas does it as a big-step `inductive` in Lean (see
  `notes.md` and `imp_semantics.md` in this directory).
- **Maude** is the more natural choice if your end goal is an
  *executable* semantics or model-checked safety property.
- **Lean** is the more natural choice if your end goal is to *prove a
  theorem* about a program or a piece of math, and you want the
  proof-checking trust base to be a single small kernel.
- The K framework is interesting because it tried to *separate*
  "define semantics" (the K language) from "execute semantics"
  (originally Maude backend; modern K uses LLVM + Haskell backends).
  K-on-Maude is one engineering choice; you could imagine (and people
  have prototyped) K-on-Lean with very different trade-offs.

## Honest caveats

- "Maude can do proofs too" — yes, via ITP for Maude, narrowing-based
  inductive theorem proving, and Reflective Maude metaprogramming.
  These are real but smaller-scale than Lean tactic ecosystems.
- "Lean can do executable semantics too" — yes, you can write a Lean
  function `step : Config → Option Config` and reason about its
  iterates. But you give up Maude's *matching modulo* (assoc, comm,
  identity), which is the killer feature for compact rewrite rules.
- We are comparing tools that overlap in *one* dimension (mechanical
  reasoning) but differ in many (logic, performance model, ecosystem,
  trusted base). Any one-axis "ranking" is misleading.

## One-line answer

Lean exists despite Maude (and vice versa) because they answer
different questions: Maude = "give me an executable spec / rewriter
with built-in concurrency and matching modulo", Lean = "give me a
small-kernel dependent-type-theory prover that scales to research math
and doubles as a programming language." Different logics, different
trust models, different ecosystems — different jobs.

## Sources & pointers

- Maude: <https://maude.cs.illinois.edu/> · "All About Maude"
  (Clavel et al., LNCS 4350, 2007).
- K framework: <https://kframework.org/> (originally on Maude,
  modern backends LLVM/Haskell).
- Lean 4: <https://lean-lang.org/> · "The Lean 4 Theorem Prover and
  Programming Language" (de Moura, Ullrich, CADE 2021).
- Mathlib: <https://leanprover-community.github.io/mathlib4_docs/>.
- Aeneas: <https://lean-lang.org/use-cases/aeneas/> — Rust → Lean
  functional translation, the natural bridge example for this dir.
- Local: `notes.md` (Aeneas / LLBC analysis), `imp_semantics.md`
  (companion IMP big-step analysis),
  `/Users/brandomiranda/veri-veri-bench/cs522/HW*-Maude/` (cs522's
  actual K/Maude homework material).
