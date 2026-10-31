import Game.Levels.Specification

open Cslib

World "Properties"
Level 1

Title "A Proof That Covers Every List"

Introduction
"
World 2 proved contracts of functions that look at their input once. This world is about
functions defined by recursion, and the proofs that follow their shape.

```
def total : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + total xs
```

Here is a fact about it that no finite number of examples establishes: **summing a
concatenation is the same as summing the pieces and adding.**

The proof is induction on the first list, and it works because `++` recurses the same way
`total` does. On `[]` both sides collapse. On `x :: xs` both sides peel off one `x`, and what
is left is the induction hypothesis.

Nothing here needs `generalizing`: the statement quantifies over `ys`, but `ys` never changes
as the recursion proceeds.
"

/--
`total_append : total (xs ++ ys) = total xs + total ys`

The sum of a concatenation is the sum of the parts.
-/
TheoremDoc total_append as "total_append" in "Algorithms & Data"

/-- Prove that summing a concatenation gives the same answer as summing each part and
adding. -/
Statement total_append (xs ys : List ℕ) : total (xs ++ ys) = total xs + total ys := by
  Hint "Induct on the first list: `induction xs with`."
  induction xs with
  | nil =>
    Hint "Appending to the empty list changes nothing, and `total [] = 0`.
    `simp [total]` does both."
    simp [total]
  | cons x xs ih =>
    Hint "Unfold `total` on both sides — `simp [total, ih]` also rewrites with the induction
    hypothesis `{ih}` — and then the two sides differ only in how the additions are
    bracketed, which `omega` settles."
    simp [total, ih]
    omega

Conclusion
"
One theorem, every pair of lists.

Keep an eye on *why* the induction worked: the proof followed the recursion of the function.
That is the general rule. A function defined by cases on a list is proved correct by induction
on a list; a function defined by cases on a number, by induction on a number. When a proof by
induction will not close, the usual reason is that it is inducting on the wrong thing, or
that the statement is too weak to feed itself — a problem you will meet twice more in this
world.
"

NewDefinition total
TheoremTab "Algorithms & Data"
