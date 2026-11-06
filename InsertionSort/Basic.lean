import Mathlib

/-!
# Formal Verification of Insertion Sort

This module implements insertion sort for lists of natural numbers
and formally verifies its correctness.

The main results establish that:
- Inserting an element preserves the elements of a list.
- Inserting into a sorted list preserves sortedness.
- Insertion sort produces a sorted list.
- Insertion sort preserves the input elements.
- Insertion sort is idempotent.

The implementation operates on lists of natural numbers using
the usual ordering relation.
-/

namespace InsertionSort

/--
Inserts a natural number into its correct position in an
already sorted list.
-/
def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
      if x ≤ y then
        x :: y :: ys
      else
        y :: insert x ys

/-- Inserting into an empty list produces a singleton list. -/
theorem insert_empty (x : Nat) :
    insert x [] = [x] := by
  rfl

/--
Sorts a list by recursively sorting its tail and inserting
the first element into the sorted result.
-/
def insertionSort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (insertionSort xs)

/--
Inserting an element preserves all original elements,
including their multiplicities.
-/
theorem insert_perm (x : Nat) (xs : List Nat) :
    List.Perm (insert x xs) (x :: xs) := by
  induction xs with
  | nil =>
      simp [insert]
  | cons y ys ih =>
      unfold insert
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

/--
Inserting an element into a sorted list preserves sortedness.
Sortedness is expressed using `List.Pairwise` with the
natural-number ordering relation.
-/
theorem insert_sorted (x : Nat) (xs : List Nat) :
    xs.Pairwise (· ≤ ·) →
    (insert x xs).Pairwise (· ≤ ·) := by
  induction xs with
  | nil =>
      intro h
      simp [insert]
  | cons y ys ih =>
      intro h
      by_cases hxy : x ≤ y
      · simp only [insert, ite_eq_left hxy]
        apply List.Pairwise.cons
        · intro z hz
          exact le_trans hxy (h.rel_head hz)
        · exact h
      · simp only [insert, ite_eq_right hxy]
        apply List.Pairwise.cons
        · intro z hz
          have hperm := insert_perm x ys
          have hz' : z ∈ x :: ys :=
            hperm.mem_iff.mp hz
          rcases List.mem_cons.mp hz' with rfl | hzys
          · exact Nat.le_of_not_ge hxy
          exact h.rel_head (List.mem_cons_of_mem y hzys)
        · exact ih h.tail

/--
Insertion sort produces a sorted list for every input list
of natural numbers.
-/
theorem insertionSort_sorted (xs : List Nat) :
    (insertionSort xs).Pairwise (· ≤ ·) := by
  induction xs with
  | nil =>
      simp [insertionSort]
  | cons x xs ih =>
      simp only [insertionSort]
      exact insert_sorted x (insertionSort xs) ih

/--
Insertion sort preserves all elements of the input list,
including duplicates. The output is a permutation of the input.
-/
theorem insertionSort_perm (xs : List Nat) :
    List.Perm (insertionSort xs) xs := by
  induction xs with
  | nil =>
      simp [insertionSort]
  | cons x xs ih =>
      simp only [insertionSort]
      exact (insert_perm x (insertionSort xs)).trans
        (List.Perm.cons x ih)

/--
Insertion sort is idempotent: sorting an already sorted result
does not change it.

The proof uses sortedness, permutation preservation, and
antisymmetry of the natural-number ordering.
-/
theorem insertionSort_idempotent (xs : List Nat) :
    insertionSort (insertionSort xs) = insertionSort xs := by
  have hsorted := insertionSort_sorted xs
  have hsorted_twice := insertionSort_sorted (insertionSort xs)
  have hperm := insertionSort_perm (insertionSort xs)
  apply hperm.eq_of_pairwise
  · intro a ha b hb hab hba
    exact Nat.le_antisymm hab hba
  · exact hsorted_twice
  · exact hsorted

/-!
## Examples

The following evaluations illustrate insertion sort on lists
with distinct elements, reverse ordering, and duplicates.
-/

#eval insertionSort [5, 2, 4, 1, 3]
#eval insertionSort [9, 7, 5, 3, 1]
#eval insertionSort [3, 1, 3, 2]

end InsertionSort
