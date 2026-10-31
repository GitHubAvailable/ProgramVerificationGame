import Game.Levels.Properties.L06_StrongEnoughToBeInductive

open Cslib

World "Properties"
Level 7

Title "Where the New Element Goes"

Introduction
"
Invariants are not only for state machines. A **data-structure invariant** is a property every
operation on a structure is supposed to preserve, and the argument has the same shape: check
each operation, inherit the rest.

The structure is a sorted list, and the operation is insertion:

```
def ins (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | x :: xs => if a ≤ x then a :: x :: xs else x :: ins a xs
```

Before proving that insertion preserves sortedness — the next level — prove the smaller fact
the argument will need: insertion adds the new element and nothing else.

That is a lemma of the kind you met in Level 2, chosen for its shape. The sortedness proof
will reach a point where it has an element of `ins a xs` in hand and needs to know where it
came from, and this is the theorem that answers.

The proof is induction, with a case split on the comparison. `by_cases hax : a ≤ x` names the
comparison explicitly, which is what you want, because the two branches of the `if` are the two
cases of the proof.
"

/--
`ins_mem : y ∈ ins a xs ↔ y = a ∨ y ∈ xs`

Inserting `a` into `xs` produces a list whose elements are exactly `a` together with those of
`xs`.
-/
TheoremDoc ins_mem as "ins_mem" in "Algorithms & Data"

/-- Show that `ins a xs` contains exactly the elements of `xs` together with `a`. -/
Statement ins_mem (a : ℕ) (xs : List ℕ) (y : ℕ) : y ∈ ins a xs ↔ y = a ∨ y ∈ xs := by
  Hint "Induct on the list being inserted into."
  induction xs with
  | nil =>
    Hint "Inserting into the empty list gives `[a]`, so membership is just equality with `a`.
    `simp [ins]`."
    simp [ins]
  | cons x xs ih =>
    Hint "Split on the comparison that decides the branch: `by_cases hax : a ≤ x`."
    by_cases hax : a ≤ x
    · Hint "`a` goes at the front, and the rest of the list is untouched, so membership is
      immediate: `simp [ins, hax]`."
      simp [ins, hax]
    · Hint "`x` stays at the front and `a` is inserted into the tail, so the induction
      hypothesis `{ih}` describes the tail. `simp [ins, hax, ih]` gets you to a goal that is
      pure propositional rearrangement, which `tauto` finishes."
      simp [ins, hax, ih]
      tauto

Conclusion
"
Insertion adds one element and loses none.

On its own this says nothing about order, which is deliberate: it is the part of the story
that the *sortedness* argument will need as an ingredient, and keeping the two apart is what
lets each be proved cleanly. Separating a structural fact from an ordering fact, proving each
once, and combining them, is how the whole of World 4 is going to be organised.
"

NewDefinition ins
NewTactic by_cases tauto
TheoremTab "Algorithms & Data"
