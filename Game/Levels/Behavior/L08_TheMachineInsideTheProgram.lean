import Game.Levels.Behavior.L07_AStateYouNeverReach

open Cslib

World "Behavior"
Level 8

Title "The Machine Inside the Program"

Introduction
"
Nobody writes a parity checker as an automaton. They write a loop:

```
count := 0
for b in xs do
  if b then count := count + 1
return count % 2 == 1
```

which in Lean is the recursive function

```
def countOnes : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + countOnes bs
```

This program has a state too — the variable `count` — but it is a natural number, not a bit.
It remembers *how many* `1`s it has seen, where the automaton remembers only *whether the
number is odd*. The automaton is an **abstraction** of the program: it throws away everything
the answer does not depend on.

Prove that the abstraction is faithful: the bit the automaton ends in tells you exactly what
the program's counter would have told you.

This is the bridge out of World 1. State machines are a way of modelling programs; from here
on the game proves things about ordinary Lean functions, and reaches for a machine only when
there is genuinely a state being carried.
"

/--
`parity_abstracts_count : parityDA.mtr parityDA.start xs = true ↔ countOnes xs % 2 = 1`

The parity automaton's final state says exactly whether the counting program's counter would
have ended up odd.
-/
TheoremDoc parity_abstracts_count as "parity_abstracts_count" in "States & Transitions"

/-- Show that the parity automaton abstracts the counting program: it finishes in `true`
exactly when the program's count of `true`s is odd. -/
Statement parity_abstracts_count (xs : List Bool) :
    parityDA.mtr parityDA.start xs = true ↔ countOnes xs % 2 = 1 := by
  Hint "First replace the machine by what it computes, using `parity_correct`. That leaves a
  statement about two ordinary recursive functions."
  rw [parity_correct]
  Hint "Now induct on `{xs}`. No `generalizing` is needed this time: neither function carries
  a state across the recursion."
  induction xs with
  | nil =>
    Hint "Both functions on the empty word are immediate: `simp [oddOnes, countOnes]`."
    simp [oddOnes, countOnes]
  | cons b bs ih =>
    Hint "Split on the first bit: `cases b`. A `false` contributes nothing to either side; a
    `true` flips the parity on one side and adds one to the count on the other."
    cases b
    · Hint "`simpa [oddOnes, countOnes] using ih` rewrites both sides and lands on the
      induction hypothesis."
      simpa [oddOnes, countOnes] using ih
    · Hint "Unfold both definitions, then split on what `oddOnes bs` is. Once that is a
      concrete `true` or `false`, `{ih}` pins down `countOnes bs % 2` and `omega` finishes the
      arithmetic."
      simp only [oddOnes, countOnes]
      cases h : oddOnes bs <;> simp_all <;> omega

Conclusion
"
The machine and the program agree — and they agree even though their states are not the same
kind of thing.

That is what an abstraction is: a map from the states a program really has to a smaller set
that still determines the answer. Picking a good one is most of the art of verification. Too
coarse and the property you want stops following; too fine and you have not simplified
anything.

You now have the whole vocabulary: states, transitions, runs, reachability, invariants, and
abstraction. World 2 changes the subject — from describing what a program does to saying what
it *should* do.
"

NewDefinition countOnes
NewTactic omega simpa
TheoremTab "States & Transitions"
