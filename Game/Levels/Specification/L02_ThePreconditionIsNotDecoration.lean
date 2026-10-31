import Game.Levels.Specification.L01_AContractForAFunction

open Cslib

World "Specification"
Level 2

Title "The Precondition Is Not Decoration"

Introduction
"
`clamp_in_range` carries the assumption `lo ≤ hi`. It is fair to ask whether that assumption is
doing anything, or whether it is there out of habit.

The way to find out is to try to do without it. If the postcondition held regardless, the
precondition would be removable. Show instead that it is **not**: find values of `lo`, `hi`
and `x` for which the conclusion of `clamp_in_range` is false.

Think about what `clamp` does when the range is empty — when `hi < lo`. The first branch fires
on `x < lo` and returns `lo`, which is above `hi`. So `lo = 1`, `hi = 0`, `x = 0` should do it.

As in World 1, an existence claim is settled by producing the thing, and then checking it.
"

/--
`clamp_needs_precondition : ∃ lo hi x, ¬(lo ≤ clamp lo hi x ∧ clamp lo hi x ≤ hi)`

Without `lo ≤ hi`, the conclusion of `clamp_in_range` fails.
-/
TheoremDoc clamp_needs_precondition as "clamp_needs_precondition" in "Specifications"

/-- Show that the precondition of `clamp_in_range` cannot be dropped: exhibit a range and an
input for which the clamped value is not inside the range. -/
Statement clamp_needs_precondition :
    ∃ lo hi x : Int, ¬(lo ≤ clamp lo hi x ∧ clamp lo hi x ≤ hi) := by
  Hint "Supply the three numbers with `refine ⟨1, 0, 0, ?_⟩`, leaving only the check that they
  really are a counterexample."
  refine ⟨1, 0, 0, ?_⟩
  Hint "Unfold `clamp` and compute. `unfold clamp` followed by `norm_num` evaluates the
  branches and finds the contradiction."
  unfold clamp
  norm_num

Conclusion
"
With an empty range there is nowhere inside it to land, so `clamp` cannot put anything there.
The precondition is load-bearing.

This is a habit worth keeping. Every assumption in a theorem is a promise the caller has to
keep, and an assumption nobody needs is a promise you extracted for nothing. When you write a
contract, ask of each hypothesis: what breaks without it? If nothing does, delete it. If
something does, you have just learned what the function actually requires.

The next three levels ask the mirror question — not *is this assumption needed* but *is this
conclusion enough*.
"

NewTactic norm_num
TheoremTab "Specifications"
