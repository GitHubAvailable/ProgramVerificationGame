import Game.Levels.Refinement.L04_OneStepAnsweredByOneStep

open Cslib

World "Refinement"
Level 5

Title "An Implementation Refines Its Specification"

Introduction
"
**Refinement** is the claim that every behavior the implementation can exhibit is one the
specification already permits:

```
implTraces l ⊆ specTraces n
```

Note the direction, because it is the whole content of the idea. It does **not** say the two
do the same things. The specification may permit behaviors the implementation never produces,
and that is not a defect — it is what lets a specification be loose and still be a promise. A
specification is a bound on behavior, not a description of it.

You have the simulation. `Cslib.LTS.IsSimulation.traces_subset` turns it into the trace
inclusion, given that the starting states are related:

```
IsSimulation.traces_subset : IsSimulation lts₁ lts₂ r → r s₁ s₂ → lts₁.traces s₁ ⊆ lts₂.traces s₂
```

That theorem contains the induction over words that you did not have to do.
"

/--
`stack_refines_counter : l.length = n → implTraces l ⊆ specTraces n`

Every sequence of operations the list-based stack can perform is one the counter
specification permits.
-/
TheoremDoc stack_refines_counter as "stack_refines_counter" in "Refinement & Equivalence"

/-- Show the list-based stack refines the counter specification: when the list has length `n`,
every operation sequence the implementation can perform is permitted by the specification. -/
Statement stack_refines_counter (l : List Unit) (n : ℕ) (h : l.length = n) :
    implTraces l ⊆ specTraces n := by
  Hint "The hard part is already a theorem. `Cslib.LTS.IsSimulation.traces_subset` converts
  `stack_sim_counter` into the trace inclusion, given that the starting states are related by
  `{h}`: `exact stack_sim_counter.traces_subset h`."
  exact stack_sim_counter.traces_subset h

Conclusion
"
A refinement between two systems with different state representations, and the only thing you
reasoned about was a single step.

Three distinctions worth keeping straight, because they are easy to blur and the rest of this
world takes them apart one at a time:

* **Trace inclusion is one-directional.** The specification here happens to permit exactly the
  same behaviors, but in general it may permit more.
* **Simulation implies trace inclusion and is strictly stronger.** It demands a step-by-step
  correspondence; trace inclusion only compares sets of words. Two systems can have the same
  traces with no simulation between them, because a trace set forgets *when* a choice was
  made.
* **A simulation in one direction says nothing about the other.** Levels 6 and 7 exhibit a
  pair where one direction holds and the other provably does not.

And a caution that applies to everything in this world. These are statements about the Lean
models written here, and about nothing else. A proof that this list-based stack refines this
counter is not a proof about any C or Rust program, and a model in which a bad operation
simply has no transition says nothing about what a real language does when a program performs
one.
"

NewTheorem Cslib.LTS.IsSimulation.traces_subset stack_sim_counter
TheoremTab "Refinement & Equivalence"
