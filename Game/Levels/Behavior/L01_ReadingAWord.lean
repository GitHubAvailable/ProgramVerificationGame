import Game.Metadata

open Cslib

World "Behavior"
Level 1

Title "Reading a Word"

Introduction
"
A **state machine** is the simplest honest picture of a running program: a set of states, and
a rule saying which state you move to when the next input arrives.

CSlib packages exactly that as `Cslib.Automata.DA` — a transition function `tr` and a `start`
state. Our machine is `parityDA`. It reads a word of bits and keeps one bit of state: whether
it has seen an odd number of `1`s so far.

![The parity automaton](images/en/parity-automaton.svg)

Reading `0` leaves the state alone; reading `1` flips it. The machine starts in `even`, which
in Lean is written `false`.

To *run* the machine over a whole word, CSlib gives you `Cslib.FLTS.mtr`:
`parityDA.mtr s xs` is the state you reach by starting in `s` and reading every symbol of
`xs` in turn.

Before proving anything about every word, run the machine on one. The word
`[true, false, true]` has two `1`s in it, so the machine should finish in `false`.

This is a goal Lean can settle by *computing*: both sides are concrete values, and `decide`
evaluates them and compares.
"

/--
`parity_run : parityDA.mtr parityDA.start [true, false, true] = false`

Reading the word `101` leaves the parity automaton in its `even` state.
-/
TheoremDoc parity_run as "parity_run" in "States & Transitions"

/-- Run the parity automaton from its start state over the word `[true, false, true]` and
confirm it finishes in `false`. -/
Statement parity_run : parityDA.mtr parityDA.start [true, false, true] = false := by
  Hint "Everything here is a concrete value, so there is nothing to reason about — only
  something to compute. `decide` evaluates both sides and checks they agree."
  decide

Conclusion
"
Two `1`s, so the parity is even, so the machine ends in `false`. The automaton agrees.

That is testing, and it is worth doing: it is how you find out that you wrote down the machine
you meant. But notice what it does not tell you. There are infinitely many words, and you have
checked one. The rest of this world is about the other thing you can do.
"

NewDefinition Cslib.Automata.DA Cslib.FLTS.mtr parityDA
NewTactic decide rfl
TheoremTab "States & Transitions"
