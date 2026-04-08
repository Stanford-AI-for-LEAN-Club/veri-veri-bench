# HW2

**Due:** Thursday, February 15 (AoE)

## Paper/PDF exercises

The following exercises related to denotational semantics are from the book material. Write these up on paper, or in a PDF:

- **Exercise 80 (page 168):** Prove that the sequential composition statement `if (b) s1 else s2 s` (i.e., the conditional statement composed sequentially with `s`) and the conditional statement `if(b){s1 s}else{s2 s}` are equivalent, where `s1` and `s2` are blocks and `s` is any statement.

- **Exercise 81 (page 168):** Prove that the functions F : (State -> State) -> (State -> State) associated to IMP `while` loops satisfy the hypotheses of the fixed-point Theorem 12, so that the denotation of IMP loops is indeed well-defined. Also, prove that the partial functions w_k : State -> State defined as

  w_k(sigma) = [[s]]^i sigma, if there is 0 <= i < k s.t. [[b]][[s]]^i sigma = false and [[b]][[s]]^j sigma = true for all 0 <= j < i; bottom otherwise

  are well-defined, that is, that if an i as above exists then it is unique. Then prove that w_k = F^k(bottom).

- **Exercise 82 (page 168):** Describe all the fixed-points of the function F associated to the IMP `while` loop.

## Maude exercise

Do this exercise **only in Maude** (not on paper) by **modifying the provided Maude code for HW2**:

- **Exercise 83 (page 169):** The semantics in Figure 3.20 evaluates a program performing a division-by-zero to bottom. Modify the denotational semantics of IMP so that it returns a state like for correct programs, namely the state in which the division-by-zero took place. In other words, we want a variant of IMP where programs fail silently when they perform illegal operations.
