import Game.Levels.Behavior.L02_EveryStartingState

open Cslib

World "Behavior"
Level 3

Title "What the Machine Computes"

Introduction
"
Now the infinite case.

Separately from the machine, here is an ordinary recursive Lean function saying what the
answer *ought* to be:

```
def oddOnes : List Bool → Bool
  | [] => false
  | b :: bs => xor b (oddOnes bs)
```

These are two very different objects. One steps through the word carrying a state; the other
recurses on the word's structure. One is how the program runs, the other is what the program
means. Your job is to prove they agree — for every word, not for the examples you tried in
Level 1.

Two facts describe how the machine runs, and they are all you need:

```
Cslib.FLTS.mtr_nil_eq : flts.mtr s [] = s
parityDA_mtr_cons     : parityDA.mtr s (b :: xs) = parityDA.mtr (xor s b) xs
```

Nothing is read from the empty word; reading `b :: xs` takes one transition and continues.
That shape — a base case and a step — is what `induction` consumes.

There is a catch, and it is the real lesson of this level. You cannot prove the statement for
the start state alone: after one transition the machine is in a *different* state, so the
induction hypothesis you want is not the one you would get. So prove the stronger statement,
for **every** starting state at once — which is what `generalizing s` is for.
"

/--
`parity_mtr : parityDA.mtr s xs = xor s (oddOnes xs)`

The parity automaton, run from any state over any word, lands in the state obtained by
combining the parity it already had with the parity of the word it read.
-/
TheoremDoc parity_mtr as "parity_mtr" in "States & Transitions"

/-- Running `parityDA` from any state `s` over any word `xs` lands in the state
`xor s (oddOnes xs)`: the parity you had, combined with the parity of what you read. -/
Statement parity_mtr (s : Bool) (xs : List Bool) :
    parityDA.mtr s xs = xor s (oddOnes xs) := by
  Hint "Induct on the word `{xs}`. Remember to write `induction xs generalizing s`, so that the
  induction hypothesis holds for *every* state, not just `{s}`."
  induction xs generalizing s with
  | nil =>
    Hint "The machine read nothing, so it has not moved. `Cslib.FLTS.mtr_nil_eq` says exactly
    that."
    rw [Cslib.FLTS.mtr_nil_eq]
    Hint "Now just compute: `oddOnes []` is `false`, and `xor {s} false` is `{s}`."
    simp [oddOnes]
  | cons b xs ih =>
    Hint "`parityDA_mtr_cons` takes one transition on `{b}` and leaves you running the rest of
    the word from the new state — which is exactly where the induction hypothesis `{ih}`
    applies."
    rw [parityDA_mtr_cons, ih]
    Hint "Unfold `oddOnes` on `{b} :: {xs}`. What is left is a question about how `xor`
    brackets, and `Bool.xor_assoc` answers it."
    rw [oddOnes, Bool.xor_assoc]

Conclusion
"
You proved an **operational** description (step through the word, carrying a state) and a
**denotational** one (recurse on the word's structure) describe the same function — for every
input, not for a handful of examples you tried.

Notice what carried the proof: you never unfolded `mtr` into a `foldl`. You used the two
equations that describe how a machine runs — nothing on the empty word, one transition on a
cons — and the rest was algebra. That is what makes this argument reusable.

Specialising `s` to `parityDA.start` now gives the correctness of the machine itself.
"

NewDefinition oddOnes
NewTheorem parityDA_mtr_cons Bool.xor_assoc
NewTactic induction rw simp
TheoremTab "States & Transitions"
