import Game.Levels.Properties.L04_OneStepIsEnough

open Cslib

World "Properties"
Level 5

Title "A Different System Entirely"

Introduction
"
The claim was that `mtrInv_of_trInv` is general. Here is the test of it.

A room with a capacity of ten, as a transition system over its occupancy:

```
def room : LTS ℕ Gate where
  Tr := fun n op m => match op with
    | .enter => n < 10 ∧ m = n + 1
    | .leave => 0 < n ∧ m = n - 1
```

Different state type — `ℕ` instead of `ℤ`. Different labels. Different property. Nothing in
common with the bank account except the shape.

Prove that the room never exceeds its capacity. You should find that your proof from the last
level transfers almost unchanged, which is the whole point: you are not reusing an argument,
you are reusing a *theorem*, and a theorem does not care what it is applied to.
"

/--
`room_capacity : n₀ ≤ 10 → room.MTr n₀ ops n → n ≤ 10`

The room's occupancy never exceeds its capacity.
-/
TheoremDoc room_capacity as "room_capacity" in "Invariants"

/-- Show that the room never holds more than ten people, whatever sequence of arrivals and
departures occurs. -/
Statement room_capacity (n₀ n : ℕ) (ops : List Gate)
    (h₀ : n₀ ≤ 10) (h : room.MTr n₀ ops n) : n ≤ 10 := by
  Hint "Same shape as before. State the single-step obligation:
  `have hstep : room.TrInv (fun k => k ≤ 10) := by ...`"
  have hstep : room.TrInv (fun k => k ≤ 10) := by
    Hint "Introduce the two states, the operation, the transition and the assumption."
    intro k op k' htr hk
    Hint "Split on the operation and let `simp` turn each abstract transition into an
    equation, after which it is arithmetic:
    `cases op <;> simp [room] at htr <;> omega`."
    cases op <;> simp [room] at htr <;> omega
  Hint "And inherit the rest: `exact Cslib.LTS.mtrInv_of_trInv hstep n₀ ops n h h₀`."
  exact Cslib.LTS.mtrInv_of_trInv hstep n₀ ops n h h₀

Conclusion
"
The same theorem, a system it was never written for, and no new induction.

This is the first of the game's two demonstrations that a library earns its keep. The saving
is not the handful of lines you did not type. It is that `mtrInv_of_trInv` is stated for an
arbitrary `LTS` and an arbitrary predicate, so the next system you model — and the one after
that — gets its safety proof by the same two steps, forever.

Compare that with Level 3, where the induction was yours and would have to be written again
here. Same result, same difficulty of the interesting part, and a difference that compounds.
"

NewDefinition Gate room
TheoremTab "Invariants"
