import Game.Levels.Properties.L08_SortednessSurvivesAnInsertion

open Cslib

World "Properties"
Level 9

Title "An Accumulator Needs Generalizing"

Introduction
"
Two programs, one answer. `total` recurses and adds on the way back out; `totalTR` carries a
running accumulator and returns it at the end — which is what a loop compiles to:

```
def totalTR : List ℕ → ℕ → ℕ
  | [], acc => acc
  | x :: xs, acc => totalTR xs (acc + x)
```

Prove they agree: `totalTR xs 0 = total xs`.

Try it directly and the induction fails, for exactly the reason World 1's `parity_mtr` failed.
The recursive call is `totalTR xs (acc + x)`, not `totalTR xs 0`, so an induction hypothesis
about the accumulator `0` is useless — you need one about *every* accumulator.

So prove the general statement first:

```
totalTR xs acc = acc + total xs
```

and read the answer off at `acc = 0`. This is the same manoeuvre as World 1, in a setting with
no machine in sight: the accumulator is the state, and a statement about one starting state
does not induct.
"

/--
`totalTR_eq : totalTR xs 0 = total xs`

The accumulator version of the sum computes the same answer as the recursive one.
-/
TheoremDoc totalTR_eq as "totalTR_eq" in "Algorithms & Data"

/-- Prove that the accumulator version of the sum agrees with the recursive one. -/
Statement totalTR_eq (xs : List ℕ) : totalTR xs 0 = total xs := by
  Hint "State the general version as an auxiliary fact:
  `have key : ∀ (ys : List ℕ) (acc : ℕ), totalTR ys acc = acc + total ys := by ...`"
  have key : ∀ (ys : List ℕ) (acc : ℕ), totalTR ys acc = acc + total ys := by
    Hint "Introduce the list, then induct on it. The accumulator must stay quantified, so do
    not introduce it before the induction: `intro ys`, then `induction ys with`."
    intro ys
    induction ys with
    | nil =>
      Hint "Both sides are the accumulator: `intro acc` and `simp [totalTR, total]`."
      intro acc
      simp [totalTR, total]
    | cons x xs ih =>
      Hint "Now introduce the accumulator for *this* case, unfold one step of each function,
      and rewrite with `{ih}` — which applies at the new accumulator `acc + x`, not at the old
      one. `intro acc`, then `simp [totalTR, total, ih]`, then `omega` for the bracketing."
      intro acc
      simp [totalTR, total, ih]
      omega
  Hint "Read off the case you wanted: `simpa using key xs 0`."
  simpa using key xs 0

Conclusion
"
The loop and the recursion agree, for every list.

This is **functional equivalence**, and it is the first time in the game two different programs
have been compared rather than one program compared with a specification. It is the question
World 5 is entirely about, in settings where the two programs do not even have the same type.

The technique is worth naming, because you have now used it three times: in World 1 for the
automaton's starting state, in World 1 again for the traffic light, and here for an
accumulator. Whenever a recursive call changes something the statement mentions, the statement
must quantify over that thing before the induction, not after.
"

NewDefinition totalTR
TheoremTab "Algorithms & Data"
