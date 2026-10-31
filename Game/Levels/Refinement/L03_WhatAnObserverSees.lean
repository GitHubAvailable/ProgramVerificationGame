import Game.Levels.Refinement.L02_SafetyIsADifferentClaim

open Cslib

World "Refinement"
Level 3

Title "What an Observer Sees"

Introduction
"
Now two systems with state. The specification is an abstract counter — it only remembers how
many items are stored:

```
def counterSpec : LTS ℕ StackOp where
  Tr := fun n op m => match op with
    | .push => m = n + 1
    | .pop => 0 < n ∧ m = n - 1
```

The implementation keeps the items in a list:

```
def stackImpl : LTS (List Unit) StackOp where
  Tr := fun l op l' => match op with
    | .push => l' = () :: l
    | .pop => ∃ t, l = () :: t ∧ l' = t
```

Their states are not the same type, so there is nothing to compare directly. What *can* be
compared is what an outsider sees: the sequences of operations each system is able to perform.
That set is `Cslib.LTS.traces`, and `implTraces l` is the notation this game uses for the
implementation's traces from state `l`.

A word is a trace exactly when some execution performs it — so proving membership means
exhibiting the execution. `Cslib.LTS.MTr.cons_iff` lets you give it one step at a time:

```
lts.MTr s₁ (μ :: μs) s₃ ↔ ∃ s₂, lts.Tr s₁ μ s₂ ∧ lts.MTr s₂ μs s₃
```

Show that pushing twice and popping once is something the empty stack can do.
"

/--
`stack_trace_example : [StackOp.push, StackOp.push, StackOp.pop] ∈ implTraces []`

A concrete behavior of the list-based stack, exhibited by the execution that performs it.
-/
TheoremDoc stack_trace_example as "stack_trace_example" in "Refinement & Equivalence"

/-- Show that `push, push, pop` is a behavior the empty list-based stack can exhibit. -/
Statement stack_trace_example :
    [StackOp.push, StackOp.push, StackOp.pop] ∈ implTraces [] := by
  Hint "Membership in `traces` means some execution performs the word.
  `rw [Cslib.LTS.mem_traces_iff]` turns the goal into that existential, and the state it ends
  in is a one-element stack: `refine ⟨[()], ?_⟩`."
  rw [Cslib.LTS.mem_traces_iff]
  refine ⟨[()], ?_⟩
  Hint "Now peel off the steps. `rw [Cslib.LTS.MTr.cons_iff]` asks for the state after the
  first push, which is `[()]`: `refine ⟨[()], rfl, ?_⟩`."
  rw [Cslib.LTS.MTr.cons_iff]
  refine ⟨[()], rfl, ?_⟩
  Hint "The second push takes it to `[(), ()]`."
  rw [Cslib.LTS.MTr.cons_iff]
  refine ⟨[(), ()], rfl, ?_⟩
  Hint "And the pop takes it back to `[()]`, where the execution stops. A pop needs a witness
  for the tail: `exact ⟨[()], ⟨[()], rfl, rfl⟩, Cslib.LTS.MTr.refl⟩`."
  rw [Cslib.LTS.MTr.cons_iff]
  exact ⟨[()], ⟨[()], rfl, rfl⟩, Cslib.LTS.MTr.refl⟩

Conclusion
"
One behavior, and the run that produces it.

The set of all such words is the only thing an observer who can see operations but not states
has access to, so it is the natural currency for comparing systems whose states are different
kinds of thing. That is what the next two levels do with it.

One warning about traces, which the end of this world returns to. A trace set records *which*
sequences are possible and forgets *when* the system committed to them. Two systems can offer
an observer exactly the same words and still differ in a way that matters.
"

NewDefinition StackOp counterSpec stackImpl Cslib.LTS.traces implTraces specTraces
NewTheorem Cslib.LTS.mem_traces_iff Cslib.LTS.MTr.cons_iff
TheoremTab "Refinement & Equivalence"
