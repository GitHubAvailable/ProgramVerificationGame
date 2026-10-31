import Game.Levels.Verification.L01_WhatSortedMeans

open Cslib

World "Verification"
Level 2

Title "Sorted Is Not Enough"

Introduction
"
Here is a sorting algorithm that always returns a sorted list:

```
fun xs => []
```

It is not a joke so much as a test. If *the output is sorted* were the contract, this would
satisfy it, and so the contract is too weak — in exactly the sense of World 2, Level 3, and
you break it the same way: by exhibiting the wrong program.

Produce the function, prove its output is always sorted, and point at an input where the
output is not a rearrangement of it. `List.Perm` is Mathlib's *is a permutation of*; `[]` is
not a permutation of `[1]`, and `simp` knows it.
"

/--
`sorted_not_enough : ∃ f, (∀ xs, List.Pairwise (· ≤ ·) (f xs)) ∧ ∃ xs, ¬(f xs).Perm xs`

Sortedness alone does not specify sorting: a function returning the empty list satisfies it.
-/
TheoremDoc sorted_not_enough as "sorted_not_enough" in "Algorithms & Data"

/-- Show that sortedness alone is too weak a contract for a sorting function, by exhibiting
a function that satisfies it and is not a sorting function. -/
Statement sorted_not_enough :
    ∃ f : List ℕ → List ℕ, (∀ xs, List.Pairwise (· ≤ ·) (f xs)) ∧ ∃ xs, ¬(f xs).Perm xs := by
  Hint "Supply the function, its sortedness proof, and the offending input in one go:
  `refine ⟨fun _ => [], fun xs => by simp, [1], ?_⟩`."
  refine ⟨fun _ => [], fun xs => by simp, [1], ?_⟩
  Hint "What remains is that `[]` is not a permutation of `[1]`, which `simp` decides."
  simp

Conclusion
"
Half a contract admits a program that throws its input away.

The lesson is the one from World 2 restated on a bigger example: ask of every specification
what else satisfies it. And the degenerate programs are always the same few — return nothing,
return the input, return a constant — so they are cheap to check against.
"

NewDefinition List.Perm
TheoremTab "Algorithms & Data"
