import Mathlib

namespace InsertionSort

-- Insert a natural number into its correct position
-- in an already sorted list.
def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
      if x ≤ y then
        x :: y :: ys
      else
        y :: insert x ys

-- Inserting into an empty list gives a singleton list.
theorem insert_empty (x : Nat) :
    insert x [] = [x] := by
  rfl

-- Sort a list by recursively sorting its tail
-- and inserting the first element.
def insertionSort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (insertionSort xs)

-- Inserting an element preserves the original elements.
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

-- Inserting into a sorted list preserves sortedness.
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

-- Insertion sort produces a sorted list.
theorem insertionSort_sorted (xs : List Nat) :
    (insertionSort xs).Pairwise (· ≤ ·) := by
  induction xs with
  | nil =>
      simp [insertionSort]
  | cons x xs ih =>
      simp only [insertionSort]
      exact insert_sorted x (insertionSort xs) ih

-- Insertion sort preserves all elements of the input list.
theorem insertionSort_perm (xs : List Nat) :
    List.Perm (insertionSort xs) xs := by
  induction xs with
  | nil =>
      simp [insertionSort]
  | cons x xs ih =>
      simp only [insertionSort]
      exact (insert_perm x (insertionSort xs)).trans
        (List.Perm.cons x ih)

-- Examples to check the implementation.
#eval insertionSort [5, 2, 4, 1, 3]
#eval insertionSort [9, 7, 5, 3, 1]
#eval insertionSort [3, 1, 3, 2]

#check List.orderedInsert
#check List.insertionSort
#check List.perm_orderedInsert
#check List.perm_insertionSort
#check List.pairwise_insertionSort

end InsertionSort
