# Extra-Credit

**Due:** Friday, May 03 (AoE)

This can be regarded as "Final exam", but it only counts as HW (and not project) extra-credit and has the same weight as any of the previous HWs. If you got a good score so far for the above, then you do not need to do this extra-credit.

**Choose one, and only one**, of the following and do it well (you will get either **10 or 0** for this extra-credit problem!):

## Option 1: Simply-Typed Lambda Calculus and CCCs

Prove Proposition 8 from the slides on simply-typed lambda calculus:

> **Proposition 8:** TE |= (forall X) E =_t E' iff E |- (forall X) E =_t E'.

Also do Exercises 5 and 6 from the slides on CCCs:

> **Exercise 5:** Prove that C is indeed a (S, Sigma)-CCC, where C is the CCC constructed from a given (S, Sigma)-Henkin model M (objects are M_t for each type t, morphisms C(M_s, M_t) = M_{s->t}, etc.).

> **Exercise 6:** Show that M is indeed an (S, Sigma)-Henkin model, where M is the Henkin model constructed from a given (S, Sigma)-CCC.

## Option 2: PCF with Call-by-Value

Consider the PCF language with call-by-value (note that the slides on Recursion define the call-by-name variant). Give it a **small-step**, a **big-step**, and a **denotational semantics** in Maude, using the representations of these semantic approaches discussed in the first part of the class.

Provide also **5 (five) PCF programs** that can be used to test all three of your semantics. You can use the builtins provided as part of the previous HWs (you should only need the generic substitution from there).

## Option 3: Polymorphic Type Checkers

This has two problems:

1. Define a **type checker for the parametric polymorphic lambda-calculus** (System F).
2. Define a **type checker for the subtype polymorphic lambda-calculus**.

In both cases, make sure that you also include the conditional and a few examples showing that your definition works. Feel free to pick whatever syntax you want for the various constructs (both for terms and for types).
