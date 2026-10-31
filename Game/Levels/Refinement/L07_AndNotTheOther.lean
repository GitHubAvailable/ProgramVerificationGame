import Game.Levels.Refinement.L06_SimulationInOneDirection

open Cslib

World "Refinement"
Level 7

Title "And Not the Other"

Introduction
"
Now show that there is **no** simulation the other way.

`Cslib.LTS.Similarity lts₁ lts₂ s₁ s₂` says *some* simulation relates `s₁` to `s₂`. Refuting
it means refuting all of them at once, so you do not get to pick the relation — you are handed
one and must find its contradiction.

The argument is the one the last level's conclusion anticipated. Suppose some simulation `r`
relates `l0` to `e0`. Then `l0 -a→ l1` must be answered, so `r` relates `l1` to one of `e1` or
`e3`. But `l1` can do `b` **and** `c`, while `e1` can only do `b` and `e3` can only do `c`. In
either case `r` is obliged to answer a step that its partner cannot take.

`rintro ⟨r, hr, hsim⟩` takes the supposed simulation apart. Applying `hsim` to a step produces
the answering state, which you then split on.
"

/--
`late_not_sim_early : ¬LTS.Similarity chooseLate chooseEarly Late.l0 Early.e0`

No simulation relates the late chooser to the early one: simulation is genuinely
directional.
-/
TheoremDoc late_not_sim_early as "late_not_sim_early" in "Refinement & Equivalence"

/-- Show that no simulation relates `chooseLate`'s initial state to `chooseEarly`'s, so the
simulation of the previous level has no converse. -/
Statement late_not_sim_early :
    ¬Cslib.LTS.Similarity chooseLate chooseEarly Late.l0 Early.e0 := by
  Hint "Assume one exists and name its parts: `rintro ⟨r, hr, hsim⟩`."
  rintro ⟨r, hr, hsim⟩
  Hint "The step `l0 -a→ l1` has to be answered. Ask the simulation for the answer:
  `obtain ⟨e', htr, hr'⟩ := hsim hr Act.a Late.l1 (by trivial)`."
  obtain ⟨e', htr, hr'⟩ := hsim hr Act.a Late.l1 (by trivial)
  Hint "Now split on which state `{e'}` is: `cases e'`. Three of the five cannot be reached by
  an `a` from `e0` at all; the other two each lack one of `l1`'s continuations. Take the five
  goals in constructor order with focus dots."
  cases e'
  · Hint "`e0`. There is no `a`-transition from `e0` to `e0`, so `{htr}` is already false:
    `simp [chooseEarly] at htr`."
    simp [chooseEarly] at htr
  · Hint "`e1` can do `b` but not `c`. Ask the simulation to answer `l1 -c→ l3` and there is
    nowhere for it to go: `obtain ⟨ec, htrc, _⟩ := hsim hr' Act.c Late.l3 (by trivial)`, then
    `cases ec <;> simp [chooseEarly] at htrc`."
    obtain ⟨ec, htrc, _⟩ := hsim hr' Act.c Late.l3 (by trivial)
    cases ec <;> simp [chooseEarly] at htrc
  · Hint "`e2` is not reachable by an `a` from `e0` either."
    simp [chooseEarly] at htr
  · Hint "`e3` can do `c` but not `b`. The mirror image of the `e1` case."
    obtain ⟨eb, htrb, _⟩ := hsim hr' Act.b Late.l2 (by trivial)
    cases eb <;> simp [chooseEarly] at htrb
  · Hint "Nor `e4`."
    simp [chooseEarly] at htr

Conclusion
"
One direction holds, the other is impossible. Similarity is not symmetric, and a one-way
simulation is not evidence that two systems are interchangeable.

This is the fact behind the warning in Level 5. If you prove `A` is simulated by `B` and
conclude *A and B behave the same*, you have asserted something you did not prove, and
sometimes something false.

What makes the two systems differ is not *which* words they can produce — those sets are
identical — but *when* they commit. An observer who may interact rather than merely watch can
tell them apart: offer `chooseEarly` an `a` and then insist on `b`, and it may already have
chosen `c` and be stuck. `chooseLate` never is.

The relation that rules this out is **bisimulation**, and the next level builds one.
"

TheoremTab "Refinement & Equivalence"
