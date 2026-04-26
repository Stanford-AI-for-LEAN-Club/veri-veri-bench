# Templates — Lean Module Skeletons (per framework)

**TLDR:** Empty in this PR. During the long Claude run (per `../prompt.md` § 3), this directory will hold one Lean skeleton per CS522 framework — each is a copy-paste starting point with the file's docstring, `inductive` declaration shape, and the equivalence-to-BigStep theorem stub already in place. Populating these skeletons is the first task of the run; do not pre-populate them in this PR — let the agent generate them so the patterns track the chosen target language.

## Planned contents

```
templates/
├── README.md                      ← this file
├── framework_skeleton.lean.template   ← (TODO) generic Lean module skeleton
├── bigstep_skeleton.lean.template     ← (TODO) shape from Imp/HW3/BigStep.lean, generalized
├── smallstep_skeleton.lean.template   ← (TODO) shape from Imp/HW3/SmallStep.lean
├── denot_skeleton.lean.template       ← (TODO) shape from Imp/HW2/Denotational.lean
├── msos_skeleton.lean.template        ← (TODO) new — based on Mosses 2004
├── rsec_skeleton.lean.template        ← (TODO) new — based on Felleisen-Hieb 1992
├── cham_skeleton.lean.template        ← (TODO) new — based on Berry-Boudol 1992
├── k_skeleton.lean.template           ← (TODO) new — based on Roșu ch. 7
├── lambda_skeleton.lean.template      ← (TODO) new — based on Pierce TAPL
└── test_corpus/                       ← differential-testing programs, one subdir per category
    └── README.md                      ← (TODO) corpus structure spec (mirrors verification_spec.md)
```

When the long run starts, the agent should:

1. Generate `framework_skeleton.lean.template` first — it carries the docstring conventions (Roșu citation, Maude reference, departures section) all later skeletons inherit.
2. Specialize the BigStep / SmallStep / Denotational skeletons by lifting from the corresponding `Imp/HW{1,2,3}` files, removing IMP++-specific bits.
3. Stub MSOS / RSEC / CHAM / K / λ skeletons from textbook references first; then refine while the framework is being implemented.
4. Build out `test_corpus/` directories during layer (a) work — see `../verification_spec.md` § Corpus structure.
