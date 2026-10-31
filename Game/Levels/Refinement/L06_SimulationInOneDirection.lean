import Game.Levels.Refinement.L05_ImplementationRefinesSpec

open Cslib

World "Refinement"
Level 6

Title "Simulation in One Direction"

Introduction
"
Two systems that offer an observer exactly the same words, and differ in when they decide.

`chooseLate` does an `a`, and *then* either a `b` or a `c`:

```
l0 --a--> l1 --b--> l2
          l1 --c--> l3
```

`chooseEarly` has two different `a`-steps, one of which has already committed to `b` and the
other to `c`:

```
e0 --a--> e1 --b--> e2
e0 --a--> e3 --c--> e4
```

An observer sees `a`, then `b` or `c`, from either. But the systems are not interchangeable,
and this level and the next show in which direction they fail to be.

Start with the direction that works. Every move `chooseEarly` makes can be answered by
`chooseLate`, because `l1` can still do whatever `e1` or `e3` can. The relation is

```
def matchEL : Early → Late → Prop
  | .e0, .l0 => True   | .e1, .l1 => True   | .e3, .l1 => True
  | .e2, .l2 => True   | .e4, .l3 => True
  | _, _     => False
```

Prove it is a simulation. Both systems are finite, so splitting on every state, label and
target settles most of it outright; the handful of goals that survive are the real steps, and
each needs the state `chooseLate` answers with.
"

/--
`early_sim_late : LTS.IsSimulation chooseEarly chooseLate matchEL`

The system that chooses early is simulated by the one that chooses late.
-/
TheoremDoc early_sim_late as "early_sim_late" in "Refinement & Equivalence"

/-- Show that `matchEL` is a simulation of `chooseLate` by `chooseEarly`. -/
Statement early_sim_late : Cslib.LTS.IsSimulation chooseEarly chooseLate matchEL := by
  Hint "Introduce the related states, the label and the step: `intro e l hr μ e' htr`."
  intro e l hr μ e' htr
  Hint "Both state spaces are finite, so split on all four and let `simp_all` discard every
  combination that is not a real transition of a related pair:
  `cases e <;> cases l <;> cases μ <;> cases e' <;> simp_all [chooseEarly, chooseLate, matchEL]`."
  cases e <;> cases l <;> cases μ <;> cases e' <;>
    simp_all [chooseEarly, chooseLate, matchEL]
  · Hint "`e0 -a→ e1`, answered by `l0 -a→ l1`. Name the answering state and let `trivial`
    discharge both the transition and the relation:
    `refine ⟨Late.l1, ?_, ?_⟩ <;> trivial`."
    refine ⟨Late.l1, ?_, ?_⟩ <;> trivial
  · Hint "`e0 -a→ e3`, answered by the same step `l0 -a→ l1` — which is exactly why this
    direction works."
    refine ⟨Late.l1, ?_, ?_⟩ <;> trivial
  · Hint "`e1 -b→ e2`, answered by `l1 -b→ l2`."
    refine ⟨Late.l2, ?_, ?_⟩ <;> trivial
  · Hint "`e3 -c→ e4`, answered by `l1 -c→ l3`."
    refine ⟨Late.l3, ?_, ?_⟩ <;> trivial

Conclusion
"
`chooseEarly` is simulated by `chooseLate`, so by `traces_subset` every behavior of the early
chooser is a behavior of the late one.

Look at where the two `a`-steps went. Both `e1` and `e3` were answered by the *same* state
`l1`, because `l1` has kept both options open and can therefore match either commitment. A
simulation is allowed to be many-to-one like that.

Which should make you suspicious about the other direction, where the single state `l1` would
have to be matched by a single state of `chooseEarly` — and neither `e1` nor `e3` can do
everything `l1` can.
"

NewDefinition Act Late Early chooseLate chooseEarly matchEL
NewTactic trivial
TheoremTab "Refinement & Equivalence"
