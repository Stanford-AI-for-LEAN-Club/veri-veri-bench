# Verification Spec — How We Decide a Semantics is "Correct"

**TLDR:** This is the contract Brando asked for in Discord on 2026-04-26: *"what we would need would be for you to know exactly how we could actually verify that the output semantics it proposes is correct."* The protocol is three layers stacked on top of each other — (a) differential testing against a reference interpreter, (b) cross-framework equivalence theorems inside Lean, (c) Stepan + textbook spot-checks. A framework only counts as "verified" when all three layers pass.

---

## Why three layers (one is not enough)

| Layer alone | What it certifies | What it misses |
|---|---|---|
| Just (a) differential testing | "On the corpus we tried, behaviour matches the reference interpreter." | Bugs on inputs not in the corpus; the kernel never saw the equivalence. |
| Just (b) equivalence theorems | "Inside Lean, all 8 frameworks agree with each other." | They could all be uniformly wrong vs. the real language — a "consistent fantasy". |
| Just (c) Stepan + textbook | "A trained PL-semantics human believes the rules look right." | Human review doesn't catch off-by-one in inversion lemmas; doesn't scale. |

Stack the three and you get: behavioural correctness on real inputs (a), internal mathematical coherence (b), and a human sanity check against the canonical textbook (c). The combination is what differentiates this experiment from VeriBench (which only has one of the three) and from Aeneas (which has (b) but not (a) or (c) at full strength).

## Layer (a) — Differential testing against a reference interpreter

The Lean semantics is *executable* (we can extract a Lean program `interp : Stmt → State → Option State` from any sufficiently constructive framework — BigStep is the easiest source). We run a fixed corpus of source programs through both:

1. **The reference interpreter** for the chosen language.
2. **The extracted Lean interpreter** from each of the 8 frameworks.

Both must produce the same observable output.

### Corpus structure

```
expt_v1/templates/test_corpus/
├── 00_smoke/         ← ~10 trivial programs (assignment, loop, if). Must all pass.
├── 01_arithmetic/    ← integer / float / overflow edge cases
├── 02_control_flow/  ← break, continue, return, deep nesting, boolean shortcut
├── 03_state/         ← mutable lists, dicts, aliasing, deep copy vs reference
├── 04_exceptions/    ← raise, try / except / finally, exception propagation
├── 05_functions/     ← positional args, default args, closures, recursion
├── 06_io/            ← deterministic stdin / stdout (compare on byte level)
└── 07_adversarial/   ← deliberate edge cases lifted from the language's spec test suite
```

Per directory, each test is a tuple `(program.<ext>, stdin.txt, expected_stdout.txt, expected_exit.txt)`. The test harness:

1. Runs `<reference> program.<ext> < stdin.txt`, captures stdout + exit code, asserts against the expected files.
2. Runs the Lean-extracted interpreter on the AST of `program.<ext>` (the parser is a separate concern; for v1 we hand-write the AST or generate it via a small parser script), feeds `stdin.txt`, captures the buffer, compares.
3. Records PASS / FAIL per program × per framework.

### Acceptance gate

| Corpus directory | Required pass rate | Rationale |
|---|---|---|
| 00_smoke | 100% | If smoke tests don't pass, nothing else is meaningful. |
| 01–06 (per directory) | ≥ 95% | Edge cases allowed to leak; investigate the failures. |
| 07_adversarial | ≥ 80% | Deliberately mean tests; partial credit is fine. |

A framework with corpus failures records them in the framework's docstring as `### Known limitations` rather than silently passing.

### Practical execution

- For Python: `python3 program.py < stdin.txt > actual_stdout.txt; echo $? > actual_exit.txt`.
- For Wasm: `wasmtime program.wasm < stdin.txt > actual_stdout.txt`.
- For Lua: `lua5.1 program.lua < stdin.txt > actual_stdout.txt`.
- For Lean side: `lake exe interp_<framework> --input program.ast --stdin stdin.txt`.

Extraction details (how to lift a Lean inductive into an executable interpreter): for BigStep we use `Decidable` instances on the relation; for Denotational it is already a function; for SmallStep / RSEC / CHAM we extract by induction on a step counter (bounded fuel), which is enough for the corpus.

## Layer (b) — Cross-framework equivalence theorems (inside Lean)

This is the layer that turns the semantics from "an LLM's plausible interpretation" into "a kernel-checked mathematical object". The shape:

```lean
-- in Imp/Real/<Lang>/Verification.lean

theorem bigstep_iff_smallstep   : ∀ s σ τ, BigStep.Eval s σ τ ↔ SmallStep.Steps ⟨s, σ⟩ ⟨skip, τ⟩
theorem bigstep_iff_denotational: ∀ s σ τ, BigStep.Eval s σ τ ↔ Denot.eval s σ = some τ
theorem smallstep_iff_msos      : ∀ s σ τ, SmallStep.Steps ⟨s, σ⟩ ⟨skip, τ⟩ ↔ MSOS.Steps ⟨s, σ⟩ ⟨skip, τ⟩
theorem smallstep_iff_rsec      : ∀ ...
theorem smallstep_iff_cham      : ∀ ...
theorem smallstep_iff_k         : ∀ ...
theorem bigstep_iff_lambda      : ∀ s σ τ, BigStep.Eval s σ τ ↔ ⟦T s⟧_β reduces to ⟦τ⟧
```

These are the **diamond of equivalence**. Together they imply all 8 framework agree on terminating programs. Diverging programs are out of scope for v1 — they need step-indexed or trace-based reasoning, which is HW7-grade material.

### Acceptance gate

- Forward direction (`Other → BigStep`) **must** compile, no `sorry`, for all 7 non-BigStep frameworks. This is the easier direction in most cases.
- Reverse direction (`BigStep → Other`) **may** be `axiom` with a `TODO(equiv-rev)` comment if it requires a deep induction we choose to defer to v2. Each `axiom` must name the standard textbook proof it is hand-waving (e.g. `axiom-citation: Roșu ch. 3, Theorem 5`).
- Determinism (`BigStep.Eval s σ τ → BigStep.Eval s σ τ' → τ = τ'`) **must** be proven for the BigStep judgment itself, no axioms.

### Why this is the strongest layer

If layer (b) is fully closed, then layer (a) only needs to pass for **one** framework; the others come for free by transport along the equivalence. In other words: a single corpus pass + closed equivalence diamond ≡ corpus pass on all 8 frameworks.

## Layer (c) — Stepan + textbook spot-check

Layer (a) catches bugs that are visible in observable behaviour. Layer (b) catches bugs that violate cross-framework agreement. Layer (c) catches bugs that are baked uniformly into all frameworks — when the rules themselves are wrong relative to what a PL textbook would write.

### Per-framework checklist

For each framework file, the docstring at top must include:

1. **Textbook citation.** "Roșu, *Programming Language Semantics*, ch. N §M, Fig. K". Page numbers if possible.
2. **5+ rule pointers.** "Constructor `<name>` corresponds to rule `<name>` on page X." For at least 5 randomly-chosen constructors.
3. **Maude reference (where applicable).** For frameworks that have a Maude port in `cs522/HW*-Maude/`, cite the file and the rule name (e.g. `imp-semantics-bigstep.maude:42 (BigStep-DIV)`).
4. **A "departures" section** listing every place the Lean rule is *not* a literal port, with one-sentence justification.

### Stepan's role

Stepan (`stepurik@stanford.edu`) is the human reviewer of last resort. After a framework lands:

1. Email Stepan the PR URL + the framework's docstring + the Verification.lean diff.
2. Ask explicitly: "given the textbook citation, do the Lean constructors match the rules?".
3. Stepan can either:
   - PASS: rules look right.
   - REQUEST CHANGES: list specific constructors + suggested fix.
   - QUESTION: ask for clarification on a specific design choice.
4. We act on Stepan's response before merging.

If Stepan's GitHub handle becomes known, also @-mention him on the PR (per the workflow in `experiments/02_do_all_cs522_in_Lean/prompt.md`).

## Failure handling

A framework "fails verification" if **any** of the three layers fails its acceptance gate. The response:

- **Layer (a) failure** → narrow the failing case, write a minimal repro, fix the offending Lean constructor, re-run the full corpus.
- **Layer (b) failure** → the equivalence theorem caught a real disagreement; this is an *internal* bug in the semantics. Fix.
- **Layer (c) failure** (Stepan rejects) → revise the constructor, update the docstring with the new citation, re-request review.

Do **not** silently lower an acceptance gate to make a framework pass. Either fix the framework or record the failure in `results_summary_<TS>.md` and email Brando.

## What this protocol does NOT certify

Honesty section: the protocol gives high confidence but is not a closed proof of correctness against the *real* language. Specifically:

- Layer (a) only sees behaviour on the test corpus. Programs outside the corpus could still differ from the reference interpreter.
- Layer (b) is internal. It does not connect to the reference interpreter — only to the other frameworks.
- Layer (c) is human, and humans miss things.

Closing the gap between "high confidence" and "kernel-checked correctness against the real language" requires a *formal specification* of the real language to begin with — which exists for WebAssembly (Watt et al.) and almost no one else. That is why WebAssembly is the recommended fallback in `language_candidates.md`. For `pythonlite`, the limit of certifiability is exactly this three-layer protocol; we cannot do better without a formal Python spec, which does not exist.
