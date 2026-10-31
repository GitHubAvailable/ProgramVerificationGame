import Game.Levels.Verification.L05_TheWholeSortIsSorted

open Cslib

World "Verification"
Level 6

Title "The Whole Sort Is a Permutation"

Introduction
"
The same lift, for the other obligation.

`isort (x :: xs)` is `ins x (isort xs)`. By `ins_perm` that is a permutation of
`x :: isort xs`, and by the induction hypothesis `isort xs` is a permutation of `xs`, so
`x :: isort xs` is a permutation of `x :: xs`. Chain the two and you are done.

`List.Perm.cons` lifts a permutation under a `::`, and `List.Perm.trans` chains. Both appeared
in Level 4; this level is about putting them together in the other order.
"

/--
`isort_perm : (isort xs).Perm xs`

Insertion sort returns a permutation of its input.
-/
TheoremDoc isort_perm as "isort_perm" in "Algorithms & Data"

/-- Prove that `isort` always returns a permutation of its input. -/
Statement isort_perm (xs : List ℕ) : (isort xs).Perm xs := by
  Hint "Induct on the list."
  induction xs with
  | nil =>
    Hint "Sorting nothing gives nothing. `simp [isort]`."
    simp [isort]
  | cons x xs ih =>
    Hint "Two steps, chained. `ins_perm x (isort xs)` moves from `ins x (isort xs)` to
    `x :: isort xs`, and `List.Perm.cons x {ih}` moves from there to `x :: xs`:
    `exact List.Perm.trans (ins_perm x (isort xs)) (List.Perm.cons x ih)`."
    exact List.Perm.trans (ins_perm x (isort xs)) (List.Perm.cons x ih)

Conclusion
"
Both obligations are now proved for `isort`, separately.

Separately is how they should be proved — they are about different things, and mixing them
would make both arguments worse. But separately is not how they should be *stated*: a caller
wants one theorem it can rely on. That is the next level, and it is shorter than this one.
"

TheoremTab "Algorithms & Data"
