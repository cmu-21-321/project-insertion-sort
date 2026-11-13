# Formal Verification of Insertion Sort in Lean 4

## Project Overview

This project implements insertion sort for lists of natural numbers in Lean 4 and formally verifies its correctness using Mathlib.

The primary goal is to prove that insertion sort produces a sorted permutation of its input. This means the resulting list is ordered and contains exactly the same elements, including duplicates.

The project also establishes that insertion sort preserves list length and is idempotent: sorting an already sorted result does not change it.

## Implementation

The implementation consists of two recursive functions:

- `insert`: Inserts a natural number into its correct position in an already sorted list.
- `insertionSort`: Recursively sorts a list by sorting its tail and inserting its head into the sorted result.

Both functions operate on `List Nat` and use the standard ordering relation `≤`.

## Formal Verification

The main correctness results are proved in `InsertionSort/Basic.lean`.

### Permutation Preservation

- `insert_perm`: Inserting an element produces a permutation of the original list with the inserted element added.
- `insertionSort_perm`: Insertion sort returns a permutation of its input.

### Sortedness

- `insert_sorted`: Inserting an element into a sorted list preserves sortedness.
- `insertionSort_sorted`: Insertion sort produces a sorted list.

Sortedness is expressed using `List.Pairwise (· ≤ ·)`, which requires every earlier element to be less than or equal to every later element.

Together, `insertionSort_sorted` and `insertionSort_perm` establish the main correctness property of insertion sort.

### Idempotence

- `insertionSort_idempotent`: Applying insertion sort twice produces the same result as applying it once.

The proof uses permutation preservation, sortedness, and the uniqueness of sorted permutations under the natural-number ordering.

### Length Preservation

Insertion sort preserves the length of its input:

```lean
(insertionSort xs).length = xs.length
```

This property follows from permutation preservation, since permutations contain the same elements with the same multiplicities.

## Proof Techniques

The formalization uses structural induction on lists, case analysis, recursive definitions, and properties of permutations and ordered lists.

The proofs build on previously established lemmas. In particular, the correctness of insertion sort is derived from the properties of the insertion operation.

The implementation and proofs are written for lists of natural numbers, rather than relying on Mathlib's existing insertion sort implementation.

## Project Structure

- `InsertionSort/Basic.lean` — Implementation, theorem statements, formal proofs, and evaluation examples.
- `InsertionSort.lean` — Main module importing the formalization.
- `lakefile.toml` — Lean and Mathlib project configuration.
- `lean-toolchain` — Lean version configuration.

## Building the Project

Install Lean 4 using [elan](https://github.com/leanprover/elan).

Download the Mathlib cache:

```bash
lake exe cache get
```

Build and verify the project:

```bash
lake build
```

A successful build confirms that Lean accepts the definitions and proofs in the project. The formalization is intended to compile without unproved `sorry` placeholders.

## Example Evaluations

The implementation includes examples such as:

```lean
#eval insertionSort [5, 2, 4, 1, 3]
-- [1, 2, 3, 4, 5]

#eval insertionSort [9, 7, 5, 3, 1]
-- [1, 3, 5, 7, 9]

#eval insertionSort [3, 1, 3, 2]
-- [1, 2, 3, 3]
```

These examples illustrate the implementation's behavior. The formal correctness proofs establish the corresponding properties for arbitrary lists of natural numbers, rather than only the tested examples.

## References

- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Mathlib Style Guide](https://leanprover-community.github.io/contribute/style.html)

## Course Context

Carnegie Mellon University — 21-321: Interactive Theorem Proving

Fall 2026