import Game.Levels.Properties.L07_WhereTheNewElementGoes

open Cslib

World "Properties"
Level 8

Title "Sortedness Survives an Insertion"

Introduction
"
Now the data-structure invariant itself: **if the list was sorted, it still is.**

Sortedness in Mathlib is `List.Pairwise (· ≤ ·)` — every element is `≤` every element after
it. The lemma that takes it apart and puts it back together is

```
List.pairwise_cons : (x :: xs).Pairwise r ↔ (∀ y ∈ xs, r x y) ∧ xs.Pairwise r
```

so proving a list sorted means proving its head is below everything after it, and that the
tail is sorted.

Both branches of `ins` need that. When `a ≤ x` the new head is `a`, and you must show `a` is
below `x` and below everything after `x` — the second part by transitivity through `x`. When
`a > x` the head is still `x`, the tail is `ins a xs`, and to show `x` is below everything in
it you need to know what is in it. That is Level 7.
"

/--
`ins_sorted : xs.Pairwise (· ≤ ·) → (ins a xs).Pairwise (· ≤ ·)`

Inserting into a sorted list leaves it sorted.
-/
TheoremDoc ins_sorted as "ins_sorted" in "Algorithms & Data"

/-- Prove that insertion preserves sortedness: inserting into a sorted list yields a sorted
list. -/
Statement ins_sorted (a : ℕ) (xs : List ℕ) (h : xs.Pairwise (· ≤ ·)) :
    (ins a xs).Pairwise (· ≤ ·) := by
  Hint "Induct on the list."
  induction xs with
  | nil =>
    Hint "A one-element list is sorted. `simp [ins]`."
    simp [ins]
  | cons x xs ih =>
    Hint "First take the assumption apart: `rw [List.pairwise_cons] at h` splits `{h}` into
    *`x` is below everything in `xs`* and *`xs` is sorted*."
    rw [List.pairwise_cons] at h
    Hint "Then split on the comparison: `by_cases hax : a ≤ x`."
    by_cases hax : a ≤ x
    · Hint "The result is `a :: x :: xs`. Build it with `pairwise_cons` twice — the inner one
      is just `{h}` again:
      `simp only [ins, hax]`, then
      `refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨h.1, h.2⟩⟩`."
      simp only [ins, hax]
      refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨h.1, h.2⟩⟩
      Hint "What remains: every element of `x :: xs` is at least `a`. Take one with
      `intro c hc`, and `simp at hc` splits it into *it is `x`* or *it is in `xs`*."
      intro c hc
      simp at hc
      rcases hc with rfl | hc
      · Hint "It is `x`, and that is the branch assumption `{hax}`."
        exact hax
      · Hint "It is further along, so it is at least `x` by `{h}`, and `a ≤ x`. Chain them
        with `le_trans`."
        exact le_trans hax (h.1 c hc)
    · Hint "The result is `x :: ins a xs`. The tail is sorted by the induction hypothesis:
      `simp only [ins, hax]`, then `refine List.pairwise_cons.mpr ⟨?_, ih h.2⟩`."
      simp only [ins, hax]
      refine List.pairwise_cons.mpr ⟨?_, ih h.2⟩
      Hint "What remains: every element of `ins a {xs}` is at least `x`. Take one, and use
      `ins_mem` to find out what it is: `intro c hc`, `rw [ins_mem] at hc`."
      intro c hc
      rw [ins_mem] at hc
      rcases hc with rfl | hc
      · Hint "It is `a`, and this branch assumed `¬(a ≤ x)`, so `x ≤ a`. `omega` extracts
        that from `{hax}`."
        omega
      · Hint "It came from `{xs}`, so `{h}` already says it is at least `x`."
        exact h.1 c hc

Conclusion
"
The invariant holds: insertion never breaks sortedness.

Compare the shape with the transition-system proofs earlier in this world. There, an invariant
was a property of states, preserved by each transition. Here it is a property of a data
structure, preserved by each operation. The second is not a metaphor for the first — it is the
same idea, and the reason a `List` does not appear as an `LTS` is only that there is one
operation and no notion of *the current list* persisting between calls.

In World 4 this lemma becomes one of the two halves of a correctness proof for a real sorting
algorithm. The other half is the permutation property, and the structure of its proof will
look familiar.
"

NewTheorem List.pairwise_cons le_trans ins_mem
NewDefinition List.Pairwise
TheoremTab "Algorithms & Data"
