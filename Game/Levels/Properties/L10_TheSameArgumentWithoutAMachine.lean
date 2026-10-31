import Game.Levels.Properties.L09_AnAccumulatorNeedsGeneralizing

open Cslib

World "Properties"
Level 10

Title "The Same Argument Without a Machine"

Introduction
"
One last look at the accumulator, because there is an invariant hiding in it.

`totalTR xs acc` starts at `acc` and never looks back: each recursive call adds something to
the accumulator, and nothing ever subtracts. So the value it finally returns is at least the
value it started with.

That is a safety property of a loop — *this variable never decreases* — and the argument is
the one from the first half of this world. The accumulator is the state. Each recursive call
is a transition. The property `acc ≤ result` holds trivially when there are no steps left, and
each step only makes it easier.

What there is **not** is an `LTS`, and so there is no `mtrInv_of_trInv` to reach for. You do
the induction yourself. That is the honest summary of this world: recognise the shape
everywhere, and reach for the general theorem when the system really is a transition system.
"

/--
`totalTR_ge_acc : acc ≤ totalTR xs acc`

The accumulator version of the sum never returns less than it was given.
-/
TheoremDoc totalTR_ge_acc as "totalTR_ge_acc" in "Invariants"

/-- Show that the accumulating sum never returns a value below its starting accumulator. -/
Statement totalTR_ge_acc (xs : List ℕ) (acc : ℕ) : acc ≤ totalTR xs acc := by
  Hint "The accumulator changes as the recursion proceeds, so quantify over it:
  `induction xs generalizing acc with`."
  induction xs generalizing acc with
  | nil =>
    Hint "Nothing left to add; the result is the accumulator itself. `simp [totalTR]`."
    simp [totalTR]
  | cons x xs ih =>
    Hint "One step takes the accumulator from `{acc}` to `{acc} + {x}`, and the induction
    hypothesis bounds the rest from there. `simp only [totalTR]` exposes the step, and then
    `exact le_trans (Nat.le_add_right acc x) (ih (acc + x))` chains the two inequalities."
    simp only [totalTR]
    exact le_trans (Nat.le_add_right acc x) (ih (acc + x))

Conclusion
"
World 3 is done, and it is worth collecting what it was about.

**Induction follows the recursion.** A function defined on lists is proved about by induction
on lists; an execution built by `stepL` is proved about by induction on executions.

**Strengthen until it is inductive.** Three times now the statement you wanted was not the
statement you could prove: the parity automaton's starting state, the two buckets' total, the
accumulator. Each time the repair was to prove more, not less.

**Factor by shape, not by interest.** `total_append` and `ins_mem` are dull theorems that made
two interesting ones easy.

**Reuse theorems, not arguments.** `mtrInv_of_trInv` did for the room exactly what it did for
the account, with nothing rewritten. That is what distinguishes a library from a habit.

World 4 puts all four to work on one algorithm.
"

NewTheorem Nat.le_add_right
TheoremTab "Invariants"
