import Game.Levels.Verification.L07_BothObligationsAtOnce

open Cslib
open Cslib.Algorithms.Lean (TimeM)

World "Verification"
Level 8

Title "The Same Algorithm, over a Monad"

Introduction
"
CSlib's insertion sort is written once, over an arbitrary monad:

```
def List.insertionSortM (r : α → α → m Bool) : List α → m (List α)
  | [] => pure []
  | b :: l => do List.orderedInsertM r b (← List.insertionSortM r l)
```

The comparison `r` is a monadic operation, so *what a comparison costs* is a parameter.
Instantiate `m` at `Id` and you get an ordinary sort. Instantiate it at
`Cslib.Algorithms.Lean.TimeM ℕ` — a pair of a result and an accumulated cost — and every
comparison is charged:

```
def cmpCost (a b : ℕ) : TimeM ℕ Bool := do
  TimeM.tick 1
  return (decide (a ≤ b))

def timedSort (xs : List ℕ) : TimeM ℕ (List ℕ) := List.insertionSortM cmpCost xs
```

`(timedSort xs).ret` is the sorted list and `(timedSort xs).time` is the number of comparisons
it performed.

Be clear about what that number is. It is **not** a measurement. It is the value of an
annotation in a declared cost model — *a comparison costs 1, everything else is free* — which
you chose and which the library takes on trust. The theorem you prove about it is a theorem
about the model.

Start by running it.
"

/--
`timedSort_run : (timedSort [3,1,2]).ret = [1,2,3]`

The cost-annotated sort computes what a sort should compute.
-/
TheoremDoc timedSort_run as "timedSort_run" in "Algorithms & Data"

/-- Run the cost-annotated sort on a concrete list and confirm the result. -/
Statement timedSort_run : (timedSort [3,1,2]).ret = [1,2,3] := by
  Hint "Concrete input, concrete output, so this is a computation: `decide`."
  decide

Conclusion
"
It sorts. On one input.

You are back where World 1 started, and for the same reason: the first thing to establish about
an unfamiliar definition is what it does, and the cheapest way to find out is to run it. The
difference is that you now know exactly how far that gets you.

The next level runs it twice, and the two answers differ in a way worth noticing.
"

NewDefinition Cslib.Algorithms.Lean.TimeM List.insertionSortM List.orderedInsertM cmpCost timedSort
TheoremTab "Algorithms & Data"
