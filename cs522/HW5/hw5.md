# HW5

**Due:** Tuesday, April 09 (AoE)

This is a **theoretical HW**, requiring you to do two proofs using category theory. You are strongly encouraged to do *all* the exercises in the slides, especially if you did not have prior experience with category theory. If you do the two exercises perfectly, then anything else you do will count for extra-credit.

## Required exercises

1. **(Easy) Exercise 8 on slide 20 in the category theory slides:**
   Prove that C(A, B) is isomorphic to C(*, B^A) whenever the exponential of A and B exists in C.

2. **(Harder) Property 1 on "category theory - 3.png" in the hand written notes on category theory properties:**
   Given morphisms h : D -> A and f : A x B -> C, prove that:

   h ; curry(f) = curry(h x 1_B ; f)

   Redraw the diagram with the correct objects and morphisms where they are deleted (figuring out the problem/diagram is 50% of a category theory proof).

   The diagram involves:
   - D x B --(h x 1_B)--> A x B --(f)--> C
   - D x B --(h x 1_B)--> A x B --(curry(f) x 1_B)--> C^B x B --(app^{B,C})--> C
