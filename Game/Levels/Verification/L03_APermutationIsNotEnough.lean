import Game.Levels.Verification.L02_SortedIsNotEnough

open Cslib

World "Verification"
Level 3

Title "A Permutation Is Not Enough"

Introduction
"
Now the other half, and the other degenerate program:

```
fun xs => xs
```

Its output is always a permutation of its input — the identity permutation. So *the output is
a rearrangement of the input* is too weak as well.

Neither clause is redundant and neither is sufficient. **Sorted** rules out `id`; **permutation**
rules out `fun _ => []`. Only the conjunction says sorting, and that is why the capstone of
this world proves two things rather than one.

`List.Perm.refl` gives the permutation half. For the counterexample, `[2,1]` is unsorted, and
`decide` can see that.
"

/--
`perm_not_enough : ∃ f, (∀ xs, (f xs).Perm xs) ∧ ∃ xs, ¬List.Pairwise (· ≤ ·) (f xs)`

Being a permutation alone does not specify sorting: the identity function satisfies it.
-/
TheoremDoc perm_not_enough as "perm_not_enough" in "Algorithms & Data"

/-- Show that the permutation clause alone is too weak, by exhibiting a function that
satisfies it and is not a sorting function. -/
Statement perm_not_enough :
    ∃ f : List ℕ → List ℕ, (∀ xs, (f xs).Perm xs) ∧ ∃ xs, ¬List.Pairwise (· ≤ ·) (f xs) := by
  Hint "The identity function, its permutation proof, and an unsorted input:
  `refine ⟨id, fun xs => List.Perm.refl _, [2,1], ?_⟩`."
  refine ⟨id, fun xs => List.Perm.refl _, [2,1], ?_⟩
  Hint "`[2,1]` is concretely unsorted, so `decide`."
  decide

Conclusion
"
The contract is settled:

```
List.Pairwise (· ≤ ·) (sort xs)  ∧  (sort xs).Perm xs
```

Two obligations, each ruling out a program the other admits. Everything else in this world is
the work of discharging them for a real algorithm — first one you can see all of, then CSlib's
cost-annotated one.
"

NewTheorem List.Perm.refl
TheoremTab "Algorithms & Data"
