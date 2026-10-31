import GameServer
import Game.Machines

/-!
# Definition documentation

Curated: only the abstractions a player is expected to use directly appear here. CSlib's
internal helpers are deliberately left out of the inventory.

Every entry names a category (`in "…"`), which becomes a sub-tab of the Definitions inventory.
The categories are the same as the theorem tabs in `Game/Doc/Theorems.lean`, so a concept and
the facts about it are found under the same name.
-/

open Cslib
open Cslib.Algorithms.Lean (TimeM)

/--
`Cslib.Automata.DA State Symbol` is a deterministic automaton: a transition function
`tr : State → Symbol → State` together with a distinguished `start : State`.

It is CSlib's model of a machine whose next state is *determined* by the current state and the
symbol it reads — the operational picture of a program with no choices in it.
-/
DefinitionDoc Cslib.Automata.DA as "DA" in "States & Transitions"

/--
`da.mtr s xs` runs the automaton `da` from state `s` over the whole word `xs`, returning the
state it ends in. It is CSlib's *extended* transition function, defined as
`xs.foldl da.tr s`, so `da.mtr s [] = s` and reading `b :: xs` takes one transition and
continues.
-/
DefinitionDoc Cslib.FLTS.mtr as "mtr" in "States & Transitions"

/--
The parity automaton of World 1: its state is `true` exactly when it has read an odd number of
`true` symbols. Reading `b` from state `s` moves it to `xor s b`, and it starts in `false`.
-/
DefinitionDoc parityDA as "parityDA" in "States & Transitions"

/--
`oddOnes xs` is an ordinary recursive Lean function returning `true` exactly when the word
`xs` contains an odd number of `true`s. It is the *specification* against which the parity
automaton is checked.
-/
DefinitionDoc oddOnes as "oddOnes" in "States & Transitions"

/--
`Cslib.Automata.DA.FinAcc State Symbol` is a `DA` together with a set `accept` of accepting
states — the textbook deterministic finite automaton. It turns a machine that *computes* a
final state into one that *recognises* a set of words.
-/
DefinitionDoc Cslib.Automata.DA.FinAcc as "DA.FinAcc" in "States & Transitions"

/--
`Cslib.Automata.Acceptor.Accepts a xs` is the recognition condition. For a `DA.FinAcc` it
unfolds to `a.mtr a.start xs ∈ a.accept`: run the machine over the word and ask whether it
finished in an accepting state. The set of accepted words is the machine's *language*.
-/
DefinitionDoc Cslib.Automata.Acceptor.Accepts as "Accepts" in "States & Transitions"

/--
The parity automaton read as an acceptor: `parityDA` with `accept = {true}`. The words it
accepts are exactly those containing an odd number of `true`s.
-/
DefinitionDoc parityAcc as "parityAcc" in "States & Transitions"

/--
The four states of World 1's traffic-light controller: `green`, `yellow`, `red`, and the
failure state `broken`.
-/
DefinitionDoc Light as "Light" in "States & Transitions"

/--
The traffic-light controller. Each tick advances `green → yellow → red → green`, and nothing
leads into `broken` — which is why, started in `green`, it never gets there.
-/
DefinitionDoc lightDA as "lightDA" in "States & Transitions"

/--
`countOnes xs` counts the `true`s in `xs`, the way an ordinary program with a counter
variable would. The parity automaton is an *abstraction* of it: it keeps only the parity of
this count, which is all the answer depends on.
-/
DefinitionDoc countOnes as "countOnes" in "States & Transitions"

/--
`IsUpperBound f` says that `f a b` is at least `a` and at least `b`, for all `a` and `b`. It
is a *proposed* specification of a maximum function — and one of World 2's lessons is that it
is too weak to pin one down.
-/
DefinitionDoc IsUpperBound as "IsUpperBound" in "Specifications"

/--
`Cslib.LTS State Label` is a labelled transition system: a relation
`Tr : State → Label → State → Prop`. Unlike an automaton it may offer several transitions for
the same label, or none, which is what makes it the right model for a program whose steps can
be blocked or can choose.
-/
DefinitionDoc Cslib.LTS as "LTS" in "States & Transitions"

/--
`lts.MTr s₁ μs s₂` says there is a finite execution from `s₁` to `s₂` performing exactly the
sequence of labels `μs`. It is built from two rules: an empty execution stays put, and one
transition followed by an execution is an execution.
-/
DefinitionDoc Cslib.LTS.MTr as "MTr" in "States & Transitions"

/--
`lts.TrInv p` says `p` is preserved by *one* transition: whenever `p` holds before a step, it
holds after it. This is the only thing you ever have to check by hand.
-/
DefinitionDoc Cslib.LTS.TrInv as "TrInv" in "Invariants"

/--
`lts.MTrInv p` says `p` is preserved by *entire executions* of any length. `TrInv` implies it,
which is the point of `Cslib.LTS.mtrInv_of_trInv`.
-/
DefinitionDoc Cslib.LTS.MTrInv as "MTrInv" in "Invariants"

/--
The bank-account transition system of World 3. States are balances (`ℤ`), labels are
operations: `Op.deposit n` always steps, `Op.withdraw n` steps only when the balance covers
`n`.
-/
DefinitionDoc account as "account" in "Invariants"

/--
The operations a bank account accepts: `Op.deposit n` and `Op.withdraw n`.
-/
DefinitionDoc Op as "Op" in "Invariants"

/--
`Cslib.Algorithms.Lean.TimeM T α` is the cost-tracking monad: a value `ret : α` paired with an
accumulated cost `time : T`. Binding two computations adds their costs.

The costs are *annotations in a declared cost model*, not measured runtime.
-/
DefinitionDoc Cslib.Algorithms.Lean.TimeM as "TimeM" in "Algorithms & Data"

/--
`List.insertionSortM r xs` is CSlib's insertion sort over an arbitrary monad, with `r` the
(monadic) comparison. Instantiating it at `Id` recovers Mathlib's `List.insertionSort`;
instantiating it at `TimeM ℕ` gives a version that counts comparisons.
-/
DefinitionDoc List.insertionSortM as "insertionSortM" in "Algorithms & Data"

/--
`List.orderedInsertM r a xs` is the step insertion sort repeats: walk along `xs` from the front,
comparing `a` with each element using the monadic comparison `r`, and put `a` in front of the
first element it does not exceed. It stops comparing as soon as it has found the place.
-/
DefinitionDoc List.orderedInsertM as "orderedInsertM" in "Algorithms & Data"

/--
`cmpCost a b` compares two numbers and charges one tick. It fixes World 4's cost model: a
comparison costs `1`, everything else is free.
-/
DefinitionDoc cmpCost as "cmpCost" in "Algorithms & Data"

/--
`timedSort xs` is `List.insertionSortM cmpCost xs`: insertion sort instrumented with the cost
model. `(timedSort xs).ret` is the sorted list, `(timedSort xs).time` the comparison count.
-/
DefinitionDoc timedSort as "timedSort" in "Algorithms & Data"

/--
`List.Pairwise r xs` says `r a b` holds for every pair of elements with `a` occurring before
`b` in `xs`. With `r = (· ≤ ·)` it is exactly "`xs` is sorted".
-/
DefinitionDoc List.Pairwise as "Pairwise" in "Algorithms & Data"

/--
`xs.Perm ys` says `xs` is a permutation of `ys`: same elements, same multiplicities, possibly
different order. A sorting function must return a permutation of its input — otherwise
returning `[]` would be "sorted".
-/
DefinitionDoc List.Perm as "Perm" in "Algorithms & Data"

/--
The operations observable at the interface of a stack: `StackOp.push` and `StackOp.pop`.
-/
DefinitionDoc StackOp as "StackOp" in "Refinement & Equivalence"

/--
The *specification* of World 5: an abstract counter. From `n` it can always `push` to `n + 1`,
and it can `pop` to `n - 1` exactly when `n` is positive.
-/
DefinitionDoc counterSpec as "counterSpec" in "Refinement & Equivalence"

/--
The *implementation* of World 5: a stack held as a list. From `l` it can always `push`, and it
can `pop` exactly when `l` is non-empty. Note its state type differs from the specification's.
-/
DefinitionDoc stackImpl as "stackImpl" in "Refinement & Equivalence"

/--
`Cslib.LTS.traces s` is the set of label sequences the system can actually perform starting
from `s`. It is the *observation model*: two states with the same traces are
indistinguishable to someone who only watches the labels.
-/
DefinitionDoc Cslib.LTS.traces as "traces" in "Refinement & Equivalence"

/--
`implTraces l` is the set of operation sequences the stack implementation can perform from
stack `l`.
-/
DefinitionDoc implTraces as "implTraces" in "Refinement & Equivalence"

/--
`specTraces n` is the set of operation sequences the counter specification permits from
count `n`.
-/
DefinitionDoc specTraces as "specTraces" in "Refinement & Equivalence"

/--
`Cslib.LTS.IsSimulation lts₁ lts₂ r` says `r` is a simulation: whenever `r s₁ s₂` and `s₁`
takes a `μ`-step to `s₁'`, the state `s₂` can answer with a `μ`-step to some `s₂'` with
`r s₁' s₂'` again.

The direction matters. A simulation says the *second* system can match the first, so it bounds
the first system's behavior by the second's.
-/
DefinitionDoc Cslib.LTS.IsSimulation as "IsSimulation" in "Refinement & Equivalence"

/--
`Int` (also written `ℤ`) is the type of integers: whole numbers, positive, negative or zero.
Unlike `ℕ`, subtraction never truncates, which is why World 2's balances and bounds live here.
-/
DefinitionDoc Int as "ℤ" in "Specifications"

/--
`max a b` is the larger of `a` and `b`. World 2 asks what it takes to characterise it: being
an upper bound of both is necessary, but — as you will show — not sufficient.
-/
DefinitionDoc Max.max as "max" in "Specifications"

/-! ## World 2: contracts of ordinary functions -/

/--
`clamp lo hi x` forces `x` into the range `[lo, hi]`: it returns `lo` if `x` is below the
range, `hi` if above, and `x` otherwise. Its contract only makes sense when `lo ≤ hi`.
-/
DefinitionDoc clamp as "clamp" in "Specifications"

/--
`IsMaxSpec f` says that `f a b` is one of `a` and `b`, **and** is at least as large as both.
Unlike `IsUpperBound` it pins its implementation down completely: every function satisfying
it is `max`.
-/
DefinitionDoc IsMaxSpec as "IsMaxSpec" in "Specifications"

/--
`divmod a b` is the pair `(a / b, a % b)`. It exists so that one contract can talk about the
quotient and the remainder together, which is the only way either of them is characterised.
-/
DefinitionDoc divmod as "divmod" in "Specifications"

/--
`scaleNonNeg xs` keeps the non-negative entries of `xs` and doubles them. Its contract has to
be assembled from the contracts of `List.filter` and `List.map`, which is the point of it.
-/
DefinitionDoc scaleNonNeg as "scaleNonNeg" in "Specifications"

/-! ## World 3: recursive functions, more systems, and a data structure -/

/--
`total xs` is the sum of a list of natural numbers, defined by recursion from the front.
-/
DefinitionDoc total as "total" in "Algorithms & Data"

/--
`totalTR xs acc` is the same sum computed the way a loop computes it: carry a running
accumulator and return it at the end. Proving it agrees with `total` is World 3's exercise in
generalising an induction hypothesis.
-/
DefinitionDoc totalTR as "totalTR" in "Algorithms & Data"

/--
The two operations of World 3's room: `enter` and `leave`. A `Gate` label records which
happened.
-/
DefinitionDoc Gate as "Gate" in "Invariants"

/--
`room` is a transition system over a room's occupancy, with a capacity of ten. It exists to
show that `LTS.mtrInv_of_trInv` applies unchanged to a system it was not written for.
-/
DefinitionDoc room as "room" in "Invariants"

/--
A `Move` takes one token from one bucket and puts it in the other: `toA` or `toB`.
-/
DefinitionDoc Move as "Move" in "Invariants"

/--
`tokens` is a transition system over a pair of bucket contents. Nothing in its transition
relation mentions the total, so conservation of the total is something to be proved — and it
is the strengthening that makes the bound on one bucket inductive.
-/
DefinitionDoc tokens as "tokens" in "Invariants"

/--
`ins a xs` inserts `a` into `xs` in front of the first element it does not exceed. If `xs` is
sorted then so is the result, which is the data-structure invariant of World 3.
-/
DefinitionDoc ins as "ins" in "Algorithms & Data"

/--
`isort` is insertion sort written directly: sort the tail, then insert the head into the
result.
-/
DefinitionDoc isort as "isort" in "Algorithms & Data"

/-! ## World 5: two lookups, two choice systems, and an internal step -/

/--
`lookupRaw xs i` reads the `i`-th element of `xs`, returning `0` when the index is out of
range — the behaviour of a language without bounds checks, modelled as a total Lean function
with a documented default.
-/
DefinitionDoc lookupRaw as "lookupRaw" in "Refinement & Equivalence"

/--
`lookupChecked xs i` reads the `i`-th element of `xs` and returns `none` when the index is out
of range, so that a caller cannot mistake a failure for data.
-/
DefinitionDoc lookupChecked as "lookupChecked" in "Refinement & Equivalence"

/--
The observable actions of World 5's choice systems: `a`, then one of `b` and `c`.
-/
DefinitionDoc Act as "Act" in "Refinement & Equivalence"

/--
States of the system that chooses *after* its `a`-step: from `l1` both `b` and `c` are still
available.
-/
DefinitionDoc Late as "Late" in "Refinement & Equivalence"

/--
States of the system that chooses *during* its `a`-step: two different `a`-transitions leave
`e0`, one already committed to `b` and one to `c`.
-/
DefinitionDoc Early as "Early" in "Refinement & Equivalence"

/--
`chooseLate` keeps both continuations open until after the `a`.
-/
DefinitionDoc chooseLate as "chooseLate" in "Refinement & Equivalence"

/--
`chooseEarly` commits to a continuation as part of the `a`. It offers an observer the same
words as `chooseLate` and is nevertheless not interchangeable with it.
-/
DefinitionDoc chooseEarly as "chooseEarly" in "Refinement & Equivalence"

/--
`matchEL` relates each state of `chooseEarly` to the state of `chooseLate` with the same
remaining behavior. It is a simulation in that direction, and no relation is one in the other.
-/
DefinitionDoc matchEL as "matchEL" in "Refinement & Equivalence"

/--
`Cslib.HasTau Label` marks one label `τ` as internal — a step the system really takes that an
observer cannot detect. Weak bisimilarity is bisimilarity that ignores such steps.
-/
DefinitionDoc Cslib.HasTau as "HasTau" in "Refinement & Equivalence"

/--
Labels with an internal action: `tau`, which is `τ`, and the observable `out`.
-/
DefinitionDoc TAct as "TAct" in "Refinement & Equivalence"

/--
States of the implementation that does one invisible step before producing its output.
-/
DefinitionDoc Delayed as "Delayed" in "Refinement & Equivalence"

/--
States of the specification, which produces its output immediately.
-/
DefinitionDoc Direct as "Direct" in "Refinement & Equivalence"

/--
`delayed` performs `d0 -τ→ d1 -out→ d2`: internal preparation, then the visible output.
-/
DefinitionDoc delayed as "delayed" in "Refinement & Equivalence"

/--
`direct` performs `n0 -out→ n1`: the output, with no preparation.
-/
DefinitionDoc direct as "direct" in "Refinement & Equivalence"

/--
`matchDN` relates both `d0` and `d1` to `n0`, because the step between them is invisible. It
is a weak bisimulation, not a bisimulation.
-/
DefinitionDoc matchDN as "matchDN" in "Refinement & Equivalence"

/--
`Cslib.LTS.IsBisimulation lts₁ lts₂ r` requires one relation to answer challenges from **both**
systems: every step of either side is matched by a step of the other on the same label,
landing in related states. It is strictly stronger than a simulation each way by two unrelated
relations.
-/
DefinitionDoc Cslib.LTS.IsBisimulation as "IsBisimulation" in "Refinement & Equivalence"

/--
`Cslib.LTS.Bisimilarity lts₁ lts₂ s₁ s₂` says *some* bisimulation relates `s₁` and `s₂`. It is
the largest bisimulation, so exhibiting any one of them establishes it.
-/
DefinitionDoc Cslib.LTS.Bisimilarity as "Bisimilarity" in "Refinement & Equivalence"

/--
`Cslib.LTS.TraceEq lts₁ lts₂ s₁ s₂` says the two states offer an observer exactly the same
words. Bisimilarity implies it; it does not imply bisimilarity, because a trace set forgets
*when* a choice was made.
-/
DefinitionDoc Cslib.LTS.TraceEq as "TraceEq" in "Refinement & Equivalence"

/--
`Cslib.LTS.STr lts s μ s'` is the *saturated* transition relation: a `μ`-step with any amount
of internal work allowed before and after, and `τ` itself answerable by standing still.
-/
DefinitionDoc Cslib.LTS.STr as "STr" in "Refinement & Equivalence"

/--
`Cslib.LTS.IsSWBisimulation` is CSlib's convenient form of weak bisimulation: the challenge is
a single transition and the answer is a saturated one. `IsSWBisimulation.isWeakBisimulation`
turns it into `WeakBisimilarity`.
-/
DefinitionDoc Cslib.LTS.IsSWBisimulation as "IsSWBisimulation" in "Refinement & Equivalence"
