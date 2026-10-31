import Game.Levels.Behavior.L05_TheLanguageOfTheMachine

open Cslib

World "Behavior"
Level 6

Title "Which States Can You Reach"

Introduction
"
A state is **reachable** when some input word drives the machine into it from the start.

That is an existence claim, and existence claims in Lean are proved the way you would prove
them on paper: by producing the thing. `use xs` supplies the word, and then Lean asks you to
check that it works — which, for a concrete word, is a computation.

Both states of `parityDA` are reachable. The empty word leaves the machine in `false`; the
one-letter word `[true]` flips it to `true`. Prove that every state is reachable by handling
the two states separately.
"

/--
`parity_reachable : ∀ s, ∃ xs, parityDA.mtr parityDA.start xs = s`

Every state of the parity automaton is reached by some input word.
-/
TheoremDoc parity_reachable as "parity_reachable" in "States & Transitions"

/-- Show that every state of the parity automaton is reachable: for each `s`, exhibit a word
that drives the machine from its start state into `s`. -/
Statement parity_reachable (s : Bool) : ∃ xs, parityDA.mtr parityDA.start xs = s := by
  Hint "Which word you need depends on which state `{s}` is, so split first: `cases s`."
  cases s
  · Hint "The machine starts in `false`, so it is already there. The empty word will do:
    `use []`, and the remaining goal computes."
    use []
    rfl
  · Hint "One `true` flips the machine out of its start state. `use [true]`."
    use [true]
    rfl

Conclusion
"
Both states reachable, and the proof is the two words that reach them.

It is worth noticing how little this says. *Reachable* is an existence claim, so a single
witness settles it — no induction, no generality. The interesting direction is the other one:
showing a state is **un**reachable means ruling out every word, and no finite list of examples
can do that. That is the next level.
"

NewTactic use
TheoremTab "States & Transitions"
