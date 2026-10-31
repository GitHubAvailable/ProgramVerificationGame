import Game.Levels.Verification.L09_BestCaseAndWorstCase

open Cslib
open Cslib.Algorithms.Lean (TimeM)

World "Verification"
Level 10

Title "Discarding the Cost"

Introduction
"
Here is the obstacle. `timedSort` is `List.insertionSortM` at `TimeM ℕ`, and Mathlib's
theorems about sorting are about `List.insertionSort`, which is an entirely different
definition. Nothing connects them syntactically.

What connects them is an idea. Throwing the cost away and keeping the result is a **monad
homomorphism**: it commutes with `pure`, with `>>=`, with everything the `do` notation is made
of. CSlib states both halves of that:

```
TimeM.isMonadHom_pure_ret
  : IsMonadHom (TimeM T) Id (fun x => pure x.ret)

IsMonadHom.map_listInsertionSortM
  : f (List.insertionSortM r xs) = List.insertionSortM (fun x y => f (r x y)) xs
```

The second says a monad homomorphism may be pushed through an entire sort. Apply it to the
first and the instrumented sort collapses to the plain one — which is where Mathlib's theorems
live.

Prove that bridge. It is the single most useful line in this world, and the next two levels
both begin with it.

One wrinkle: the homomorphism leaves a `pure` wrapper on one side and a `decide (x ≤ y) = true`
where the goal wants `(· ≤ ·)`. Simplifying the hypothesis **and** the goal together —
`simp [timedSort, cmpCost] at h ⊢` — clears both. Simplifying only the hypothesis does not.
"

/--
`timedSort_ret : (timedSort xs).ret = xs.insertionSort (· ≤ ·)`

Discarding the cost turns the instrumented sort into Mathlib's ordinary insertion sort.
-/
TheoremDoc timedSort_ret as "timedSort_ret" in "Algorithms & Data"

/-- Prove that the result of the cost-annotated sort is exactly Mathlib's ordinary insertion
sort of the same list. -/
Statement timedSort_ret (xs : List ℕ) : (timedSort xs).ret = xs.insertionSort (· ≤ ·) := by
  Hint "Instantiate the general theorem with the homomorphism that throws the cost away:
  `have h := Cslib.IsMonadHom.map_listInsertionSortM
  (Cslib.Algorithms.Lean.TimeM.isMonadHom_pure_ret (T := ℕ)) cmpCost xs`"
  have h := Cslib.IsMonadHom.map_listInsertionSortM
    (Cslib.Algorithms.Lean.TimeM.isMonadHom_pure_ret (T := ℕ)) cmpCost xs
  Hint "`{h}` is the right statement wrapped in `pure` and phrased with a `decide`. Unfold the
  two definitions in the hypothesis and the goal at once: `simp [timedSort, cmpCost] at h ⊢`."
  simp [timedSort, cmpCost] at h ⊢
  Hint "What is left is exactly `{h}`."
  exact h

Conclusion
"
The two algorithms compute the same list.

This is the game's second clear win from CSlib, and it is a different kind of win from the
first. `mtrInv_of_trInv` in World 3 saved you an induction you knew how to do. This saves you
something you would probably not have thought to do at all: the observation that
instrumentation is a homomorphism, and that homomorphisms commute with the whole algorithm,
turns *reprove everything in the cost monad* into one rewrite.

Neither library states the composite. You built it, out of two general theorems, and the two
levels that follow spend it.
"

NewTheorem Cslib.Algorithms.Lean.TimeM.isMonadHom_pure_ret Cslib.IsMonadHom.map_listInsertionSortM
TheoremTab "Algorithms & Data"
