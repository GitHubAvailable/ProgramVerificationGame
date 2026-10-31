import Game.Levels.Refinement.L07_AndNotTheOther

open Cslib

World "Refinement"
Level 8

Title "Bisimulation Across Representations"

Introduction
"
A **bisimulation** is a single relation that works in both directions at once:

```
LTS.IsBisimulation lts₁ lts₂ r ↔ ∀ s₁ s₂, r s₁ s₂ → ∀ μ,
  (∀ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂')
  ∧
  (∀ s₂', lts₂.Tr s₂ μ s₂' → ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ r s₁' s₂')
```

Note that it is not *a simulation whose converse is also a simulation* — it is one relation
required to answer challenges from both sides. That is strictly stronger than mutual
simulation by two unrelated relations, and it is the right notion of *these two systems are
interchangeable*.

Go back to the stack and the counter. In Level 4 you showed that a list standing for its
length simulates. Show now that the **same relation** is a bisimulation: not only can the
specification answer the implementation, the implementation can answer the specification.

The new half is the pop. The specification's pop requires only `0 < n`. To answer it the
implementation must produce an actual list to pop, so you have to get from *the length is
positive* to *the list is non-empty* — which means splitting on the list.
"

/--
`stack_bisim_counter : LTS.IsBisimulation stackImpl counterSpec (fun l n => l.length = n)`

The list-based stack and the counter specification are bisimilar under the relation that a
list stands for its length.
-/
TheoremDoc stack_bisim_counter as "stack_bisim_counter" in "Refinement & Equivalence"

/-- Show that *a list stands for its length* is a bisimulation between `stackImpl` and
`counterSpec`. -/
Statement stack_bisim_counter :
    Cslib.LTS.IsBisimulation stackImpl counterSpec (fun l n => l.length = n) := by
  Hint "Introduce the related states and the label: `intro l n hr μ`."
  intro l n hr μ
  Hint "The first half is exactly the simulation you already proved. Supply it and keep the
  second: `refine ⟨fun l' htr => stack_sim_counter hr μ l' htr, ?_⟩`."
  refine ⟨fun l' htr => stack_sim_counter hr μ l' htr, ?_⟩
  Hint "Now the new direction: the specification steps, and the implementation must answer.
  `intro n' htr`, then `cases μ`."
  intro n' htr
  cases μ
  · Hint "A push. The implementation can always push, producing `() :: {l}`:
    `refine ⟨() :: l, rfl, ?_⟩`, and then the lengths match."
    refine ⟨() :: l, rfl, ?_⟩
    simp [counterSpec] at htr
    simp [htr, ← hr]
  · Hint "A pop. `simp [counterSpec] at htr` gives you `0 < {n}` and what the new count is;
    `obtain ⟨hpos, rfl⟩ := htr` names them."
    simp [counterSpec] at htr
    obtain ⟨hpos, rfl⟩ := htr
    Hint "To answer, the implementation needs a non-empty list. Split: `cases l with`. The
    empty case contradicts `{hr}` together with `{hpos}`, and the non-empty case supplies the
    tail."
    cases l with
    | nil => simp at hr; omega
    | cons u t => exact ⟨t, ⟨t, rfl, rfl⟩, by simp at hr; omega⟩

Conclusion
"
The stack and the counter are bisimilar. Neither can be distinguished from the other by any
observer, however it interacts.

That is a much stronger statement than the refinement of Level 5, and it is the one you would
want before replacing a component in a system you do not control. Refinement promises the
replacement does nothing the specification forbids. Bisimulation promises it does nothing
different at all.

Both were proved from a local, one-step condition, over states that are not even the same
type. The list carries strictly more information than the count — the identity of the items —
and the relation simply ignores it. That is the sense in which the counter is an *abstraction*
of the stack, and it is the same idea you met in World 1, now between two systems rather than
between a machine and a program.
"

NewDefinition Cslib.LTS.IsBisimulation
TheoremTab "Refinement & Equivalence"
