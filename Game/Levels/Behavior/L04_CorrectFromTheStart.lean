import Game.Levels.Behavior.L03_WhatTheMachineComputes

open Cslib

World "Behavior"
Level 4

Title "Correct from the Start"

Introduction
"
`parity_mtr` is about every starting state. The claim you actually wanted is about one of
them: the machine, started where machines start, computes the parity of its input.

```
parity_mtr : parityDA.mtr s xs = xor s (oddOnes xs)
```

That generality was forced on you by the induction. Now you get it back as a convenience: a
theorem proved for all `s` can be *used* at whichever `s` you like, and `parityDA.start` is
`false`.

So rewrite with `parity_mtr`, and finish by computing `xor false b`.
"

/--
`parity_correct : parityDA.mtr parityDA.start xs = oddOnes xs`

Started in its own start state, the parity automaton computes exactly `oddOnes`.
-/
TheoremDoc parity_correct as "parity_correct" in "States & Transitions"

/-- Specialise the general theorem to the machine's own start state: `parityDA` run from
`parityDA.start` computes `oddOnes`. -/
Statement parity_correct (xs : List Bool) :
    parityDA.mtr parityDA.start xs = oddOnes xs := by
  Hint "`parity_mtr` applies to any starting state, so it applies to this one.
  `rw [parity_mtr]` rewrites the left-hand side."
  rw [parity_mtr]
  Hint "What is left is `xor parityDA.start (oddOnes {xs}) = oddOnes {xs}`. The start state is
  `false`, and `xor false b` is `b` — `simp [parityDA]` unfolds the machine far enough to see
  that and then finishes."
  simp [parityDA]

Conclusion
"
The machine is correct: on every input, the state it stops in is the parity of what it read.

It is worth being precise about what the generalisation bought you. It was not a stronger
*result* — this level's statement is what you cared about, and the general one followed from
nothing extra. It was a stronger *induction hypothesis*. Strengthening the claim to make the
induction go through, then specialising at the end, is a move you will use for the rest of
the game.
"

NewTheorem parity_mtr
TheoremTab "States & Transitions"
