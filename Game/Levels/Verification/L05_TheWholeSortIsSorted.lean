import Game.Levels.Verification.L04_InsertionIsAPermutation

open Cslib

World "Verification"
Level 5

Title "The Whole Sort Is Sorted"

Introduction
"
Insertion sort is insertion, repeated:

```
def isort : List ℕ → List ℕ
  | [] => []
  | x :: xs => ins x (isort xs)
```

Sort the tail, then insert the head into the result. Prove the whole thing returns a sorted
list.

This is where the preparation pays. The induction hypothesis says the sorted tail is sorted;
`ins_sorted` says inserting into a sorted list keeps it sorted; and that is the entire
argument. There is no new reasoning about order anywhere in this level — it was all done once,
for one insertion, in World 3.

That is what *compositional* means, and it is the only reason verifying real programs is
possible at all.
"

/--
`isort_sorted : (isort xs).Pairwise (· ≤ ·)`

Insertion sort returns a sorted list.
-/
TheoremDoc isort_sorted as "isort_sorted" in "Algorithms & Data"

/-- Prove that `isort` always returns a sorted list. -/
Statement isort_sorted (xs : List ℕ) : (isort xs).Pairwise (· ≤ ·) := by
  Hint "Induct on the list."
  induction xs with
  | nil =>
    Hint "Sorting nothing gives nothing, and the empty list is sorted. `simp [isort]`."
    simp [isort]
  | cons x xs ih =>
    Hint "The result is `ins x (isort xs)`. The tail is sorted by `{ih}`, and `ins_sorted`
    says inserting into a sorted list leaves it sorted:
    `exact ins_sorted x (isort xs) ih`."
    exact ins_sorted x (isort xs) ih

Conclusion
"
The first of the two obligations, for the whole algorithm, in three lines.

Count what those three lines rest on: an induction here, `ins_sorted` from World 3, `ins_mem`
underneath that, and `List.pairwise_cons` from the library. Four small results, each proved
where it was easiest, composing into a statement about an algorithm.

Had you tried to prove this directly about `isort`, you would have had to do all of it at
once, inside a single induction, with the comparison case split nested inside the list case
split. That proof exists and people write it. It is about four times as long and nobody can
read it.
"

NewDefinition isort
TheoremTab "Algorithms & Data"
