import Game.Levels.Properties

open Cslib

World "Verification"
Level 1

Title "What Sorted Means"

Introduction
"
A capstone needs a subject. This world's is insertion sort, and before proving anything about
it the contract has to be written down. That turns out to be the part worth slowing over.

*Sorted* in Mathlib v4.35 is not a definition of its own; it is an instance of a more general
one. `List.Pairwise r` says the relation `r` holds between every element and every element
**after** it:

```
List.Pairwise r []                ↔ True
List.Pairwise r (x :: xs)         ↔ (∀ y ∈ xs, r x y) ∧ List.Pairwise r xs
```

So `List.Pairwise (· ≤ ·) xs` is exactly *ascending order, duplicates allowed*. Note what it
does **not** say: nothing about adjacent pairs only, and nothing about which elements are
present.

Get a feel for it by checking two concrete lists — one that is sorted and one that is not.
Both sides are decidable, so `decide` settles the whole conjunction.
"

/--
`sorted_examples : List.Pairwise (· ≤ ·) [1,2,2,5] ∧ ¬List.Pairwise (· ≤ ·) [2,1]`

A worked example and a worked non-example of the sortedness predicate.
-/
TheoremDoc sorted_examples as "sorted_examples" in "Algorithms & Data"

/-- Confirm that `[1,2,2,5]` satisfies the sortedness predicate and `[2,1]` does not. -/
Statement sorted_examples :
    List.Pairwise (· ≤ ·) [1,2,2,5] ∧ ¬List.Pairwise (· ≤ ·) [2,1] := by
  Hint "Everything here is concrete and decidable. `decide`."
  decide

Conclusion
"
`[1,2,2,5]` is sorted — equal neighbours are fine, because `≤` is reflexive. `[2,1]` is not.

That is one half of the contract. The next two levels show that it is only half, by exhibiting
two programs that each satisfy one half and are plainly not sorting algorithms.
"

TheoremTab "Algorithms & Data"
