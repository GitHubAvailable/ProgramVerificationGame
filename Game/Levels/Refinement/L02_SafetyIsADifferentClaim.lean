import Game.Levels.Refinement.L01_TheSameAnswerWhereItMatters

open Cslib

World "Refinement"
Level 2

Title "Safety Is a Different Claim"

Introduction
"
Level 1 said the checked lookup behaves like the raw one **where the raw one is meaningful**.
It said nothing at all about the other indices — and the other indices are the reason anyone
would make the change.

So here is the second claim, and it is independent of the first: out of range, the checked
lookup returns `none`. It does not invent a value, and it does not return something a caller
could mistake for data.

Two separate properties, and it is worth being precise about why they cannot be merged.
*Behavior preservation under a precondition* is about agreeing with the thing you replaced.
*Safety* is about what you do where the thing you replaced had nothing sensible to do. A
replacement can have the first without the second, and the second without the first.

A caution, since this example is a model of a real situation. In C, reading past the end of an
array is **undefined behavior**: the program may return a value, may crash, may do something
the compiler inferred could never happen. It is not an error return that can be compared with
`none`, and `lookupRaw` is not a model of it. `lookupRaw` is a total Lean function with a
documented default, and the theorems here are about that.
"

/--
`lookupChecked_none : xs.length ≤ i → lookupChecked xs i = none`

Out of range, the checked lookup reports failure rather than inventing a value.
-/
TheoremDoc lookupChecked_none as "lookupChecked_none" in "Refinement & Equivalence"

/-- Show that the checked lookup returns `none` on every out-of-range index. -/
Statement lookupChecked_none (xs : List ℕ) (i : ℕ) (h : xs.length ≤ i) :
    lookupChecked xs i = none := by
  Hint "Unfold the definition: `simp [lookupChecked]`. What is left is the arithmetic side
  condition, which `omega` discharges from `{h}`."
  simp [lookupChecked]
  omega

Conclusion
"
The replacement is safe, and that is a different theorem from the replacement being faithful.

Keep the two apart whenever you argue that one component may stand in for another. *It behaves
the same* and *it fails well* are both worth having, neither implies the other, and conflating
them is how a migration gets signed off on half the evidence.

From here on the systems have state, the observations are sequences rather than single
answers, and *behaves the same* needs a much more careful definition.
"

TheoremTab "Refinement & Equivalence"
