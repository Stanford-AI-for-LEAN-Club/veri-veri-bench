# Real PL Target — Candidates

**TLDR:** We need *one* "real" programming language to be the target of the experiment. Default recommendation: `pythonlite` — a curated Python subset with functions, exceptions, mutable lists / dicts, and `import` of pure modules. Strong alternates: WebAssembly 1.0 (already has a fully-formal reference spec), Lua 5.1 (small, fully specified), MiniML (CBV λ + refs + exceptions). The choice should be confirmed with Brando + Stepan before writing any Lean.

---

## Selection criteria (in order)

1. **Realness signal.** A developer should recognize the source as "the language I use", not a toy. Rules out pure IMP / IMP++.
2. **Existence of a reference interpreter** that we can drive in differential testing (layer (a) of `verification_spec.md`).
3. **Tractable size.** All 8 CS522 frameworks × the language must fit in Brando's compute budget. ≤ ~30 AST node kinds is realistic; ≥ ~80 (full Python) is not.
4. **Bonus: existing formal spec.** If someone has already written *one* formal semantics, it shortcuts layer (a) — we can diff against the formal spec instead of just the interpreter.
5. **Project alignment.** VeriBench targets Python; Aeneas targets Rust; CompCert targets C. The first two are the strongest signals because they are the projects we are trying to improve on.

## Candidates

### 1. `pythonlite` — recommended default

A curated Python subset. Same source language as VeriBench, so the comparison story writes itself.

**Includes:**
- Integers, booleans, floats, strings (immutable), `None`.
- Mutable `list` and `dict` (with reference semantics — closes a hole IMP doesn't reach).
- `if` / `elif` / `else`, `while`, `for`-over-iterable, `break`, `continue`, `return`.
- Functions: `def`, positional + default args (no `*args`/`**kwargs` in v1), nested functions, closures over enclosing scope.
- Exceptions: `try` / `except` / `finally`, `raise`, a small fixed exception hierarchy (`Exception`, `ValueError`, `ZeroDivisionError`).
- A toy module system: `import` of pre-loaded modules whose ASTs are baked in. No filesystem.

**Excludes (out of scope for v1):**
- Classes, `__getattr__` / metaclass hooks (would make Pythonlite ≈ full Python).
- `eval`, `exec`, `compile` (reflective; would force us to formalise the interpreter inside the semantics).
- `async` / `await`, generators (complex control structures; defer to v2).
- C extensions, the GIL, threading, multiprocessing.
- Floating-point IEEE-754 corner cases — model floats as `ℝ` initially, then refine if a test needs it.

**Reference interpreter:** CPython 3.x — restrict to constructs listed above and run with `python3 -c "exec(open('prog.py').read())"`.

**Pros:** Direct comparison to VeriBench. Familiar to every developer. Forces the semantics to handle exceptions, mutable references, closures, and a module system.

**Cons:** Even the curated subset is large enough that all 8 frameworks × all features is ambitious. Mitigation: see `prompt.md` § 8 — shrink the subset if BigStep doesn't compile in 24 h.

### 2. WebAssembly 1.0 — strong alternate

The W3C WebAssembly 1.0 spec is fully formal already (Watt, Rossberg, Pichon-Pharabod, Ben-Yelles). That makes layer (a) cheap: we diff our Lean semantics against the official spec instead of an interpreter.

**Pros:** Already-formal reference; small core (~25 instructions in MVP); deterministic; total typed-ness; reference implementations (`wasmtime`, `wabt`) are well-trusted.

**Cons:** Less developer-recognizable than Python. CHAM / threads frameworks are awkward on a language that has no built-in concurrency in 1.0 (would need to model a degenerate sequential CHAM).

**When to pick this:** if Brando wants the cleanest verification story — Wasm has the strongest "we can prove this is right" claim because the W3C spec is itself formal.

### 3. Lua 5.1 — minimalist alternate

Lua 5.1 has 8 keywords, a published reference manual (~50 pages), one canonical interpreter (`lua5.1`), and a community of formal-methods folks (Soldevila et al., Lua-RT formalisation).

**Pros:** Smallest "real" language. Reference interpreter is a single 200 KB binary. Mutable tables (single composite value), first-class functions, coroutines (we'd skip these in v1).

**Cons:** No exception system to speak of (`error` + `pcall`); fewer features per framework. Less recognizable than Python.

### 4. MiniML — fallback

CBV λ-calculus + integer + product/sum types + ref + exceptions, à la Pierce *Types and Programming Languages* ch. 11–14.

**Pros:** Maps directly onto λ-calculus / type-system frameworks (HW6 + Extra-Credit material). Tiny AST (~12 nodes).

**Cons:** Borderline-toy. A skeptical reviewer would say MiniML is just a slightly-richer IMP. Pick this only if the others all fall through compute-wise.

## Recommendation

Start with **`pythonlite`** because of the VeriBench alignment. Hold WebAssembly 1.0 as the immediate fallback if the Python subset proves intractable inside the compute budget.

Either way, write the AST in `Imp/Real/<Lang>/Syntax.lean` *first*, get *one* framework (BigStep) end-to-end + a working reference-interpreter differential test passing, *then* fan out to the other 7 frameworks. Don't fan out before BigStep is green.
