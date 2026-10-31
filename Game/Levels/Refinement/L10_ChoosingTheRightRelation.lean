import Game.Levels.Refinement.L09_AStepNobodyCanSee

open Cslib

World "Refinement"
Level 10

Title "Choosing the Right Relation"

Introduction
"
Every level so far told you which relation to prove. This one does not; it tells you what you
need to know about two pairs of systems, and leaves you to notice that the answers come from
different places.

**First.** A caller of the stack wants to know it cannot tell the stack from the counter —
that they are **trace equivalent**, `l ~tr[stackImpl, counterSpec] n`. You could try to compute
both trace sets and compare them. You should not: you proved a bisimulation in Level 8, and
`IsBisimulation.traceEq` says bisimilar states have the same traces. Picking the strong
relation first made the weak one free.

**Second.** Someone proposes replacing `chooseLate` with `chooseEarly`, on the grounds that
they have the same traces — which they do. Show that they are nevertheless **not bisimilar**.
You do not need a new argument: a bisimulation is in particular a simulation, via
`IsBisimulation.isSimulation`, and Level 7 showed there is no simulation in that direction.

Together these are the shape of the whole world. Trace equivalence is what an observer who
only watches can detect. Bisimilarity is what an observer who interacts can detect. They are
different, bisimilarity is strictly stronger, and which one you need is a question about your
setting — not about Lean.
"

/--
`relation_choice`

Bisimilarity gives trace equivalence for free; trace equivalence does not give bisimilarity.
-/
TheoremDoc relation_choice as "relation_choice" in "Refinement & Equivalence"

/-- Establish both halves of the comparison: the stack and the counter are trace equivalent,
and the two choice systems are not bisimilar even though they are. -/
Statement relation_choice :
    (∀ (l : List Unit) (n : ℕ), l.length = n →
      Cslib.LTS.TraceEq stackImpl counterSpec l n)
    ∧ ¬Cslib.LTS.Bisimilarity chooseLate chooseEarly Late.l0 Early.e0 := by
  Hint "Two independent claims. `constructor` splits them."
  constructor
  · Hint "Introduce the states and the relating equation, then hand the bisimulation to
    `IsBisimulation.traceEq`: `intro l n h`, then `exact stack_bisim_counter.traceEq h`."
    intro l n h
    exact stack_bisim_counter.traceEq h
  · Hint "Assume a bisimulation and take it apart: `rintro ⟨r, hr, hb⟩`."
    rintro ⟨r, hr, hb⟩
    Hint "A bisimulation is a simulation, and Level 7 ruled those out:
    `exact late_not_sim_early ⟨r, hr, hb.isSimulation⟩`."
    exact late_not_sim_early ⟨r, hr, hb.isSimulation⟩

Conclusion
"
Four relations, and the discipline for choosing between them.

* **Conditional functional equivalence.** The replacement computes the same answers, on the
  inputs where the original was meaningful. Say which inputs.
* **Trace inclusion — refinement.** Every behavior of the implementation is permitted by the
  specification. One-directional, and that asymmetry is a feature.
* **Simulation.** A local condition implying trace inclusion, and strictly stronger than it.
  A simulation one way says nothing about the other.
* **Bisimulation.** One relation answering challenges from both sides. Implies trace
  equivalence, and is implied by it only under extra assumptions such as determinism. Weakened
  to ignore internal steps, it is the usual notion of *this implementation realises this
  specification*.

The habit to carry away is to ask what an observer of your system can actually do before
choosing. If they only read a log, trace equivalence is what you need and anything stronger is
work you did not have to do. If they can interact — hold a handle, make a request and insist
on a response — trace equivalence is not enough, and proving it would be proving something true
that does not mean what you wanted.

And the caveat from Level 5 one last time, because it is the easiest thing in this world to
overclaim. Everything here is about the Lean models on this page. A relation between two
models is evidence about two programs only to the extent that the models are faithful, and
establishing *that* is a different kind of work than anything this game has asked you to do.
"

NewTheorem Cslib.LTS.IsBisimulation.traceEq Cslib.LTS.IsBisimulation.isSimulation stack_bisim_counter late_not_sim_early
NewDefinition Cslib.LTS.TraceEq Cslib.LTS.Bisimilarity
TheoremTab "Refinement & Equivalence"
