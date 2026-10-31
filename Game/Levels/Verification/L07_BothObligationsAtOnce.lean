import Game.Levels.Verification.L06_TheWholeSortIsAPermutation

open Cslib

World "Verification"
Level 7

Title "Both Obligations at Once"

Introduction
"
You have the two halves. State the contract from Level 3 and discharge it.

```
List.Pairwise (· ≤ ·) (isort xs)  ∧  (isort xs).Perm xs
```

The proof is the pair of theorems you already have. That is deliberate: a correctness theorem
should be a thin statement over results proved elsewhere, because it is the statement users
read and the statement that must not drift. If this level were hard, the decomposition would
be wrong.
"

/--
`isort_correct : List.Pairwise (· ≤ ·) (isort xs) ∧ (isort xs).Perm xs`

Insertion sort is correct: its output is sorted and is a permutation of its input.
-/
TheoremDoc isort_correct as "isort_correct" in "Algorithms & Data"

/-- Prove `isort` correct against the full two-part contract. -/
Statement isort_correct (xs : List ℕ) :
    List.Pairwise (· ≤ ·) (isort xs) ∧ (isort xs).Perm xs := by
  Hint "Both halves are already theorems. `exact ⟨isort_sorted xs, isort_perm xs⟩`."
  exact ⟨isort_sorted xs, isort_perm xs⟩

Conclusion
"
A verified sorting algorithm, from scratch, in four levels and a lemma borrowed from World 3.

Now the question this world exists to ask. You wrote `ins` and `isort` yourself, and the proofs
followed their structure. What happens when the algorithm is not yours — when it comes from a
library, is written over an arbitrary monad so that it can be instrumented, and does not look
like anything you can induct on directly?

That is CSlib's `List.insertionSortM`, and the rest of this world is about it.
"

NewTheorem isort_sorted isort_perm
TheoremTab "Algorithms & Data"
