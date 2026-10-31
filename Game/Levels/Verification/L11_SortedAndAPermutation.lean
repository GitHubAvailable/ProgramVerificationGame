import Game.Levels.Verification.L10_DiscardingTheCost

open Cslib
open Cslib.Algorithms.Lean (TimeM)

World "Verification"
Level 11

Title "Sorted, and a Permutation"

Introduction
"
Now spend the bridge. The contract is the one from Level 3, applied to CSlib's cost-annotated
sort:

```
List.Pairwise (· ≤ ·) (timedSort xs).ret  ∧  (timedSort xs).ret.Perm xs
```

`timedSort_ret` rewrites both halves into statements about `List.insertionSort`, and Mathlib
has already proved those:

```
List.pairwise_insertionSort : (List.insertionSort r l).Pairwise r
List.perm_insertionSort     : (List.insertionSort r l).Perm l
```

So the whole of Levels 4 to 7 — the insertion lemmas, the two inductions, the composition —
is replaced by a rewrite and two names. That is not a trick; it is what reuse looks like when
it works. You did the long version first so that you would recognise what was saved.
"

/--
`timedSort_correct : List.Pairwise (· ≤ ·) (timedSort xs).ret ∧ (timedSort xs).ret.Perm xs`

The cost-annotated insertion sort returns a sorted list which is a permutation of its input.
-/
TheoremDoc timedSort_correct as "timedSort_correct" in "Algorithms & Data"

/-- Prove the cost-annotated insertion sort correct against the two-part contract: the list
it returns is sorted, **and** it is a permutation of the input. -/
Statement timedSort_correct (xs : List ℕ) :
    List.Pairwise (· ≤ ·) (timedSort xs).ret ∧ (timedSort xs).ret.Perm xs := by
  Hint "Cross the bridge first: `rw [timedSort_ret]` turns both obligations into statements
  about Mathlib's ordinary insertion sort."
  rw [timedSort_ret]
  Hint "Now each half is a library theorem:
  `exact ⟨List.pairwise_insertionSort _ _, List.perm_insertionSort _ _⟩`."
  exact ⟨List.pairwise_insertionSort _ _, List.perm_insertionSort _ _⟩

Conclusion
"
Two genuinely different obligations, discharged against a library implementation you never had
to unfold.

Notice precisely what transferred and what did not. `.ret` transferred, because discarding the
cost is a homomorphism and homomorphisms preserve the result. `.time` did not, and could not:
it is exactly the information the homomorphism forgets. No theorem about `List.insertionSort`
can say anything about it, because `List.insertionSort` does not have it.

So a statement about the comparison count has to be proved in the cost monad, by induction,
from scratch. That is the last level of the core path.
"

NewTheorem timedSort_ret List.pairwise_insertionSort List.perm_insertionSort
TheoremTab "Algorithms & Data"
