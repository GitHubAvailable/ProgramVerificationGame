import Game.Levels.Verification.L03_APermutationIsNotEnough

open Cslib

World "Verification"
Level 4

Title "Insertion Is a Permutation"

Introduction
"
World 3 proved that `ins` preserves sortedness. That is the first obligation. Here is the
second, for the same operation: **inserting `a` into `xs` produces a rearrangement of
`a :: xs`.**

`ins_mem` was close but not enough. It says which elements are present; a permutation also has
to account for how many times each occurs. `List.Perm` tracks that.

The induction has the same two branches as before. When `a ≤ x` the result is literally
`a :: x :: xs`, so there is nothing to rearrange. When `a > x` the result is `x :: ins a xs`,
and the induction hypothesis says `ins a xs` is a rearrangement of `a :: xs` — so
`x :: ins a xs` rearranges to `x :: a :: xs`, which is `a :: x :: xs` with the first two
elements swapped.

Three lemmas do it: `List.Perm.cons` puts the same element on the front of both sides,
`List.Perm.swap` exchanges the first two, and `List.Perm.trans` chains them. Write them out by
name rather than with dot notation — `h.trans` is shorter, but the game resolves the field of a
projection as a name in its own right, and `trans` on its own is a different theorem.
"

/--
`ins_perm : (ins a xs).Perm (a :: xs)`

Insertion rearranges rather than changes: the result is a permutation of the input with the
new element added.
-/
TheoremDoc ins_perm as "ins_perm" in "Algorithms & Data"

/-- Prove that inserting `a` into `xs` yields a permutation of `a :: xs`. -/
Statement ins_perm (a : ℕ) (xs : List ℕ) : (ins a xs).Perm (a :: xs) := by
  Hint "Induct on the list."
  induction xs with
  | nil =>
    Hint "Inserting into the empty list gives `[a]`, which is `a :: []`. `simp [ins]`."
    simp [ins]
  | cons x xs ih =>
    Hint "Split on the comparison: `by_cases hax : a ≤ x`."
    by_cases hax : a ≤ x
    · Hint "`a` goes straight to the front, so the two lists are equal and nothing needs
      rearranging. `simp only [ins, hax]`, then `exact List.Perm.refl _`."
      simp only [ins, hax]
      exact List.Perm.refl _
    · Hint "`x` stays in front and `a` is inserted into the tail. `simp only [ins, hax]`,
      then put `x` on the front of the induction hypothesis and swap the first two elements:
      `exact List.Perm.trans (List.Perm.cons x ih) (List.Perm.swap a x xs)`."
      simp only [ins, hax]
      exact List.Perm.trans (List.Perm.cons x ih) (List.Perm.swap a x xs)

Conclusion
"
Insertion satisfies both obligations now: it keeps the list sorted, and it loses nothing.

The two proofs looked quite different — the sortedness one needed `ins_mem` and transitivity
of `≤`, this one needed the permutation algebra — but they share a structure, because both
follow the recursion of `ins`. That is the reward for defining the operation cleanly: every
property of it is proved by the same case split.

Two more levels lift these from the single insertion to the whole sort.
"

NewTheorem List.Perm.cons List.Perm.swap List.Perm.trans ins_sorted
TheoremTab "Algorithms & Data"
