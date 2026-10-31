import Game.Levels.Behavior.L01_ReadingAWord

open Cslib

World "Behavior"
Level 2

Title "Every Starting State at Once"

Introduction
"
Here is a claim that is not about one run but about *all* of them: **reading `11` always
brings the machine back where it started.**

Two flips cancel. That is obvious from the picture, and it is obvious for each of the two
states if you check them one at a time. The point of this level is that *checking them one at
a time is a proof* — as long as there are finitely many of them, and you leave none out.

`cases s` does exactly that: it splits the proof into one goal per constructor of `s`. Since
`s : Bool`, you get two goals, one with `s` replaced by `false` and one with `s` replaced by
`true`. In each, everything is concrete again.

You could write the two cases out with focus dots `·`. It is shorter to write
`cases s <;> rfl`, which means *split into cases, then run `rfl` on every goal the split
produced*.
"

/--
`parity_two_ones : parityDA.mtr s [true, true] = s`

Reading two `1`s returns the parity automaton to whichever state it started in.
-/
TheoremDoc parity_two_ones as "parity_two_ones" in "States & Transitions"

/-- Show that reading the word `[true, true]` leaves the parity automaton in the state it
started in — whichever state that was. -/
Statement parity_two_ones (s : Bool) : parityDA.mtr s [true, true] = s := by
  Hint "`{s}` is a `Bool`, so there are only two possibilities. Split them with `cases s`,
  and each goal becomes a concrete computation that `rfl` closes.

  Write `cases s <;> rfl` to do both at once."
  cases s <;> rfl

Conclusion
"
A statement about every starting state, proved by exhausting the starting states.

That worked because `Bool` has two inhabitants. The *words* the machine reads are a different
matter: there are infinitely many of them, and no amount of case splitting will enumerate
them. For those you need induction, which is the next level.

Knowing which of the two situations you are in is most of the skill. Finite? Split. Infinite
but built up step by step? Induct.
"

NewTheorem Cslib.FLTS.mtr_nil_eq
NewTactic cases
TheoremTab "States & Transitions"
