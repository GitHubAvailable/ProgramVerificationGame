import Game.Levels.Refinement.L03_WhatAnObserverSees

open Cslib

World "Refinement"
Level 4

Title "One Step Answered by One Step"

Introduction
"
Comparing trace sets directly means reasoning about words of arbitrary length — the same
problem World 3 had with executions, and it has the same solution: find a local condition and
let a general theorem do the induction.

The local condition is a **simulation**. Relate states of the two systems, and require that
whenever related states are given and the first takes a step, the second can answer with a
step on the same label, landing in related states again:

![A step of the implementation answered by a step of the specification](images/en/simulation.svg)

```
LTS.IsSimulation lts₁ lts₂ r
  ↔ ∀ s₁ s₂, r s₁ s₂ → ∀ μ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂'
```

For the stack and the counter the relation is the obvious one: a list stands for its length.

Prove that it is a simulation. There are two cases, one per operation, and neither mentions
words at all — which is the point.
"

/--
`stack_sim_counter : LTS.IsSimulation stackImpl counterSpec (fun l n => l.length = n)`

Relating a list to its length is a simulation of the counter specification by the list-based
stack.
-/
TheoremDoc stack_sim_counter as "stack_sim_counter" in "Refinement & Equivalence"

/-- Show that *a list stands for its length* is a simulation of `counterSpec` by
`stackImpl`. -/
Statement stack_sim_counter :
    Cslib.LTS.IsSimulation stackImpl counterSpec (fun l n => l.length = n) := by
  Hint "Introduce the related states, the label, the implementation's step, and the evidence
  that it is one: `intro l n hr μ l' htr`."
  intro l n hr μ l' htr
  Hint "Split on the operation `{μ}`: a push and a pop are answered differently."
  cases μ
  · Hint "A push. The specification can always push, so the state it moves to is `{n} + 1`.
    Supply it and the proof that it is a legal step, and leave the relation:
    `refine ⟨n + 1, rfl, ?_⟩`."
    refine ⟨n + 1, rfl, ?_⟩
    Hint "`simp [stackImpl] at htr` tells you what `{l'}` is, and then the lengths match."
    simp [stackImpl] at htr
    simp [htr, ← hr]
  · Hint "A pop. `simp [stackImpl] at htr` tells you exactly what `{l}` looked like; then
    `subst htr` replaces it."
    simp [stackImpl] at htr
    subst htr
    Hint "`simp at hr` turns `{hr}` into a statement about lengths. The specification's pop
    needs `0 < {n}`, which now follows by arithmetic — as does the new length.
    `exact ⟨n - 1, ⟨by omega, rfl⟩, by omega⟩`."
    simp at hr
    exact ⟨n - 1, ⟨by omega, rfl⟩, by omega⟩

Conclusion
"
A one-step condition, checked on two operations, between systems with different state types.

Notice what the relation had to do. It is not a function from one state space to the other —
it is a relation, and nothing requires it to be injective or surjective. Many lists stand for
the same count. That freedom is what makes simulations usable: the implementation may carry
information the specification does not, as long as every step it takes is one the
specification permits.

The next level turns this into the statement about behaviors it was built for.
"

NewDefinition Cslib.LTS.IsSimulation
TheoremTab "Refinement & Equivalence"
