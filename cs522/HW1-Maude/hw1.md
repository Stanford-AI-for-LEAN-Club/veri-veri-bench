# HW1

**Due:** Thursday, February 1st (AoE)

## Required (submit these)

Do the following exercises **only in Maude** (not on paper) by **modifying the provided Maude code for HW1**:

- **Exercise 56 (page 137):** Add an "error" state and modify the big-step semantics in Figure 3.7 to allow derivations of sequents of the form ⟨s, σ⟩ ⇓ ⟨error⟩ or ⟨p⟩ ⇓ ⟨error⟩ when s evaluated in state σ or when p evaluated in the initial state performs a division by zero.

- **Exercise 70 (page 155):** To handle division-by-zero, add "error" values and statements, and modify the small-step SOS in Figures 3.14 and 3.15 to allow derivations of sequents whose right-hand-side configurations contain "error" as their syntactic component. See also Exercise 56 (same problem but for big-step SOS).

## Optional warm-up (do not submit)

If you are not familiar with Maude, you are encouraged to do these exercises to warm up (**do not include them in your HW1 submission**):

- **Exercise 30 (page 80):** Define a Maude module called INT-SET specifying sets of integers with membership, union, intersection, difference (elements in the first set but not in the second), and symmetric difference (elements in any of the two sets but not in the other).

- **Exercise 32 (page 80):** Recall module FLATTEN (Section 2.5.6) which defines an infix traversal operation on binary trees. Do the same for prefix and for postfix traversals.

- **Exercise 33 (page 80):** Write a Maude module that uses binary trees as defined in module TREE (Section 2.5.6) to sort lists of integers. You should define an operation `btsort : IntList -> IntList`, which sorts the argument list of integers (like the `isort` operation in module ISORT in Section 2.5.6). In order to define `btsort`, define another operation, `bt-insert : IntList Tree -> Tree`, which inserts each integer in the list at its place in the tree, and also use the `flatten` operation already defined in module FLATTEN.

- **Exercise 35 (page 83):** Define in Maude the Turing machines corresponding to the addition, the multiplication, and the power operations on natural numbers in Exercise 12. Do it using three different approaches: (1) using the infinite stream `zeros`, following the representation in Figure 2.10; (2) without using infinite streams but mimicking them with the by-need expansion using the two equations in Figure 2.11; (3) without any equations, following the style suggested right after Theorem 11, at the expense of adding more rules.

- **Exercise 36 (page 83):** Use the Maude definition of the Post correspondence problem in Section 2.5.6 to calculate the least common multiplier of two natural numbers. The idea here is to create an appropriate set of tiles from the two numbers so that the solution to the search command contains the desired least common multiplier.
