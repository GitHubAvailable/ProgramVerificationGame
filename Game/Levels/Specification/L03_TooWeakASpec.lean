import Game.Levels.Specification.L02_ThePreconditionIsNotDecoration

open Cslib

World "Specification"
Level 3

Title "A Specification That Is Too Weak"

Introduction
"
The last two levels asked whether an implementation meets its contract. This one asks the
harder question: whether the contract is the one you meant.

Suppose someone proposes this specification for a two-argument maximum:

```
def IsUpperBound (f : Int → Int → Int) : Prop :=
  ∀ a b, a ≤ f a b ∧ b ≤ f a b
```

It is true of `max`. It reads plausibly. And it is **too weak**: it pins down an upper bound,
but says nothing about the result being one of the two arguments, or about it being the
*least* such bound.

The way to show a specification is too weak is to exhibit a second implementation that
satisfies it and is nevertheless wrong. Not an argument in prose — a witness.
"

/--
`upperBound_too_weak : ∃ f, IsUpperBound f ∧ ∃ a b, f a b ≠ max a b`

`IsUpperBound` does not characterise `max`: some function satisfies it while disagreeing with
`max` somewhere.
-/
TheoremDoc upperBound_too_weak as "upperBound_too_weak" in "Specifications"

/-- Show that `IsUpperBound` fails to pin down `max`: exhibit a function that satisfies the
proposed specification and yet disagrees with `max` on some input. -/
Statement upperBound_too_weak :
    ∃ f : Int → Int → Int, IsUpperBound f ∧ ∃ a b, f a b ≠ max a b := by
  Hint "You have to *build* a counterexample function. Anything that overshoots will do — try
  `use fun a b => max a b + 1`."
  use fun a b => max a b + 1
  Hint "Two things left: that your function really is an upper bound, and that it differs from
  `max` somewhere. Split them with `constructor`."
  constructor
  · Hint "Take arbitrary `a` and `b` with `intro a b`, then prove both halves of the `∧`."
    intro a b
    constructor
    · Hint "`show a ≤ max a b + 1` makes the goal readable, then `le_max_left` plus `omega`
      finishes it."
      show a ≤ max a b + 1
      have h := le_max_left a b
      omega
    · show b ≤ max a b + 1
      have h := le_max_right a b
      omega
  · Hint "Now pick any concrete pair of numbers where the two disagree. `use 0, 0` is as good
    as any."
    use 0, 0
    show max (0 : Int) 0 + 1 ≠ max 0 0
    simp

Conclusion
"
`fun a b => max a b + 1` satisfies the proposed contract and is not `max`. So the contract
does not say what its author meant.

This is the everyday failure mode of specification: not a *false* statement, but a true one
that permits implementations you would reject. The repair is to say more — that the result is
one of the arguments, or that it is below every other upper bound — and the habit is to
challenge each contract by asking which wrong program could still satisfy it.

Note what you did *not* need: no transition systems, no automata. A pure function's contract
is just a proposition about it. State machines are a model for programs that carry state, not
a prerequisite for verifying everything.
"

NewDefinition IsUpperBound Max.max
NewTheorem le_max_left le_max_right
TheoremTab "Specifications"
