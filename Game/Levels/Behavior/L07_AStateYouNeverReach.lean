import Game.Levels.Behavior.L06_WhichStatesCanYouReach

open Cslib

World "Behavior"
Level 7

Title "A State You Never Reach"

Introduction
"
Here is a traffic-light controller. It cycles `green → yellow → red → green`, one step per
tick, and it has a fourth state called `broken`:

```
def lightDA : Automata.DA Light Unit where
  tr := fun s _ => match s with
    | .green => .yellow
    | .yellow => .red
    | .red => .green
    | .broken => .broken
  start := .green
```

![The traffic-light controller: green, yellow and red in a cycle, and nothing leading into broken](images/light-automaton.svg)

Nothing leads *into* `broken`. So the controller, started in `green`, never breaks — no matter
how long it runs.

To prove it you cannot exhibit a witness, and you cannot try all the words. You need the first
genuine **safety argument** in the game, and it has a shape you will use for the rest of your
life:

> Find a property that holds at the start and that one transition cannot destroy. Then no
> number of transitions can destroy it either.

Here the property is simply *not being `broken`*. It holds in `green`. And one tick maps every
non-`broken` state to a non-`broken` state. The induction turns those two facts into a
statement about every run.

As in Level 3 you will need the stronger, `generalizing` form: the induction step runs the
machine from a state that is not the one you started in.
"

/--
`light_never_broken : lightDA.mtr lightDA.start xs ≠ Light.broken`

However long the traffic-light controller runs, it never enters its failure state.
-/
TheoremDoc light_never_broken as "light_never_broken" in "States & Transitions"

/-- Show that the traffic-light controller never reaches `broken`, however many ticks it
runs. -/
Statement light_never_broken (xs : List Unit) :
    lightDA.mtr lightDA.start xs ≠ Light.broken := by
  Hint "The statement about the start state is not strong enough to induct on. State the
  strengthened version first:
  `have key : ∀ (s : Light) (ys : List Unit), s ≠ Light.broken → lightDA.mtr s ys ≠ Light.broken := by ...`"
  have key : ∀ (s : Light) (ys : List Unit),
      s ≠ Light.broken → lightDA.mtr s ys ≠ Light.broken := by
    Hint "Introduce the state and the word, then induct on the word — `generalizing s`, so the
    hypothesis covers every state."
    intro s ys
    induction ys generalizing s with
    | nil =>
      Hint "No ticks have happened, so the machine is still in `{s}`, and that is the
      assumption. `Cslib.FLTS.mtr_nil_eq` rewrites the run away."
      intro h
      rwa [Cslib.FLTS.mtr_nil_eq]
    | cons u us ih =>
      Hint "One tick, then the rest. `show lightDA.mtr (lightDA.tr {s} {u}) us ≠ Light.broken`
      makes that visible, because running a word from the front is a transition followed by
      the remaining run."
      intro h
      show lightDA.mtr (lightDA.tr s u) us ≠ Light.broken
      Hint "Now the induction hypothesis applies — provided the state after one tick is still
      not `broken`. `apply ih` leaves exactly that obligation."
      apply ih
      Hint "Check the four states one at a time: `cases {s}`, and in each the transition is a
      concrete value. `cases s <;> simp_all [lightDA]` does all four."
      cases s <;> simp_all [lightDA]
  Hint "The strengthened statement covers the start state too, and `green` is not `broken`."
  exact key _ _ (by simp [lightDA])

Conclusion
"
The controller never breaks, and you proved it without examining a single run.

What carried the argument was not anything about traffic lights. It was the pattern: a
property true at the start, preserved by one step, and therefore true always. The property has
a name — an **invariant** — and the pattern is the single most useful idea in program
verification.

You did the induction by hand here. In World 3 you will meet the same argument again, stated
once and for all as a theorem about transition systems in general, and you will not have to
write it again.
"

NewDefinition Light lightDA
NewTactic «have» intro apply «show» rwa simp_all

TheoremTab "States & Transitions"
