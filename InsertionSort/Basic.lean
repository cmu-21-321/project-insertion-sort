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


-- Inserting into a sorted list preserves sortedness.
-- Inserting into a sorted list preserves sortedness.
theorem insert_sorted (x : Nat) (xs : List Nat) :
    xs.Pairwise (· ≤ ·) →
    (insert x xs).Pairwise (· ≤ ·) := by
  sorry

-- Insertion sort produces a sorted list.
-- Insertion sort produces a sorted list.
theorem insertionSort_sorted (xs : List Nat) :
    (insertionSort xs).Pairwise (· ≤ ·) := by
  sorry

-- Inserting an element preserves the original elements.
theorem insert_perm (x : Nat) (xs : List Nat) :
    List.Perm (insert x xs) (x :: xs) := by
  sorry

-- Insertion sort preserves all elements of the input list.
theorem insertionSort_perm (xs : List Nat) :
    List.Perm (insertionSort xs) xs := by
  sorry

-- Examples to check the implementation.
#eval insertionSort [5, 2, 4, 1, 3]
#eval insertionSort [9, 7, 5, 3, 1]
#eval insertionSort [3, 1, 3, 2]

end InsertionSort
