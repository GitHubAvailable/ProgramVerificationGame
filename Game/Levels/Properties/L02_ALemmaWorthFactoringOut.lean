import Game.Levels.Properties.L01_InductionOnARecursiveFunction

open Cslib

World "Properties"
Level 2

Title "A Lemma Worth Factoring Out"

Introduction
"
Reversing a list does not change its sum. Obvious, and not provable by simply unfolding
anything — `total` recurses from the front, and `reverse` puts the front at the back.

What makes it work is the theorem you just proved. `List.reverse_cons` says

```
(x :: xs).reverse = xs.reverse ++ [x]
```

so the induction step turns the goal into a statement about a concatenation, and
`total_append` is exactly the tool for those.

This is the first time in the game that a previous result is load-bearing rather than
decorative. It will not be the last: the rest of this world, and all of World 4, is built this
way.
"

/--
`total_reverse : total xs.reverse = total xs`

Reversing a list leaves its sum unchanged.
-/
TheoremDoc total_reverse as "total_reverse" in "Algorithms & Data"

/-- Prove that reversing a list does not change its sum, using the concatenation lemma from
the previous level. -/
Statement total_reverse (xs : List ℕ) : total xs.reverse = total xs := by
  Hint "Induct on `{xs}`."
  induction xs with
  | nil =>
    Hint "The reverse of the empty list is itself, so both sides are `total []`. `rfl` closes
    it."
    rfl
  | cons x xs ih =>
    Hint "`List.reverse_cons` turns the reversed list into a concatenation, `total_append`
    splits the sum over it, and `{ih}` handles the reversed tail:
    `rw [List.reverse_cons, total_append, ih]`."
    rw [List.reverse_cons, total_append, ih]
    Hint "What is left is `total {xs} + total [{x}] = {x} + total {xs}`. Unfold `total` on the
    singleton with `simp [total]` and finish with `omega`."
    simp [total]
    omega

Conclusion
"
Two levels, two theorems, and the second needed the first.

That is worth pausing on, because it is the only way large proofs are ever built. `total_append`
is not interesting in itself — nobody wants to know it. It is interesting because it is the
right *shape*: it says what happens to `total` when a list is built by `++`, and anything that
builds lists with `++` can now be reasoned about.

Choosing lemmas by shape rather than by interest is the skill. A good one is stated in terms
of the operations your proofs actually produce.
"

NewTheorem List.reverse_cons total_append
TheoremTab "Algorithms & Data"
