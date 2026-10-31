import GameServer
import Game.Machines

/-!
# Theorem documentation

Theorems are grouped into thematic tabs that grow with the game:

* **States & Transitions** — running machines and executions (Worlds 1 and 3).
* **Specifications** — ordinary order-theoretic facts used to argue about contracts (World 2).
* **Invariants** — the reusable safety machinery of CSlib (World 3).
* **Algorithms & Data** — correctness of the sorting algorithm (World 4).
* **Refinement & Equivalence** — relating two systems (World 5).
-/

open Cslib
open Cslib.Algorithms.Lean (TimeM)

/-! ## States & Transitions -/

/--
`FLTS.mtr_nil_eq : flts.mtr s [] = s`

Running a machine over the empty word leaves it where it was.
-/
TheoremDoc Cslib.FLTS.mtr_nil_eq as "mtr_nil_eq" in "States & Transitions"

/--
`parityDA_mtr_cons : parityDA.mtr s (b :: xs) = parityDA.mtr (xor s b) xs`

Reading the first symbol of a word performs one transition, and then the rest of the word is
read from the new state. This is the equation that turns "running a machine" into a recursion
you can do induction on.
-/
TheoremDoc parityDA_mtr_cons as "parityDA_mtr_cons" in "States & Transitions"

/--
`Bool.xor_assoc : xor (xor a b) c = xor a (xor b c)`

`xor` is associative, so it does not matter whether you combine the parity you have already
accumulated with the next symbol, or the next symbol with the parity of the rest.
-/
TheoremDoc Bool.xor_assoc as "xor_assoc" in "States & Transitions"

/-! ## Specifications -/

/--
`le_max_left a b : a ≤ max a b`

The maximum of two numbers is at least the first of them.
-/
TheoremDoc le_max_left as "le_max_left" in "Specifications"

/--
`le_max_right a b : b ≤ max a b`

The maximum of two numbers is at least the second of them.
-/
TheoremDoc le_max_right as "le_max_right" in "Specifications"

/-! ## Invariants -/

/--
`LTS.mtrInv_of_trInv : lts.TrInv p → lts.MTrInv p`

**The reusable safety theorem.** If `p` survives one transition, it survives an execution of
any length. You prove the single-step case — a finite, concrete obligation — and CSlib gives
you the statement about all finite executions, with no induction on your side.
-/
TheoremDoc Cslib.LTS.mtrInv_of_trInv as "mtrInv_of_trInv" in "Invariants"

/-! ## Algorithms & Data -/

/--
`TimeM.isMonadHom_pure_ret : IsMonadHom (TimeM T) Id (fun x => pure x.ret)`

Throwing the cost away is a monad homomorphism: the result of a cost-annotated computation is
what you would have got without the annotations. This is what lets correctness proofs about
the plain algorithm carry over to the instrumented one.
-/
TheoremDoc Cslib.Algorithms.Lean.TimeM.isMonadHom_pure_ret as "isMonadHom_pure_ret" in "Algorithms & Data"

/--
`IsMonadHom.map_listInsertionSortM :`
`f (List.insertionSortM r xs) = List.insertionSortM (fun x y => f (r x y)) xs`

A monad homomorphism `f` commutes with `insertionSortM`: pushing `f` through the whole sort is
the same as applying it to each comparison. Combined with `isMonadHom_pure_ret`, this turns
the timed sort into the ordinary one.
-/
TheoremDoc Cslib.IsMonadHom.map_listInsertionSortM as "map_listInsertionSortM" in "Algorithms & Data"

/--
`List.pairwise_insertionSort r l : List.Pairwise r (List.insertionSort r l)`

Mathlib's insertion sort returns a sorted list, provided the order is total and transitive.
-/
TheoremDoc List.pairwise_insertionSort as "pairwise_insertionSort" in "Algorithms & Data"

/--
`List.perm_insertionSort r l : (List.insertionSort r l).Perm l`

Mathlib's insertion sort returns a permutation of its input: nothing is lost, nothing is
invented.
-/
TheoremDoc List.perm_insertionSort as "perm_insertionSort" in "Algorithms & Data"

/-! ## Refinement & Equivalence -/

/--
`LTS.IsSimulation.traces_subset : lts₁.IsSimulation lts₂ r → r s₁ s₂ →`
`LTS.traces s₁ ⊆ LTS.traces s₂`

**Refinement for free.** Once you have exhibited a simulation relating an implementation state
to a specification state, every behavior of the implementation is a behavior the
specification permits. You never have to reason about whole traces directly.
-/
TheoremDoc Cslib.LTS.IsSimulation.traces_subset as "traces_subset" in "Refinement & Equivalence"

/-! ## Order and arithmetic, used to argue about contracts -/

/--
`le_total : a ≤ b ∨ b ≤ a`

Any two elements of a linear order are comparable. Split on it when the answer depends on
which of two values is larger.
-/
TheoremDoc le_total as "le_total" in "Specifications"

/--
`le_trans : a ≤ b → b ≤ c → a ≤ c`

Chain two inequalities. In the sortedness proof it is what carries *`a` is below the head*
through to *`a` is below everything after the head*.
-/
TheoremDoc le_trans as "le_trans" in "Specifications"

/--
`max_eq_left : b ≤ a → max a b = a`

When the first argument dominates, the maximum is the first argument.
-/
TheoremDoc max_eq_left as "max_eq_left" in "Specifications"

/--
`max_eq_right : a ≤ b → max a b = b`

When the second argument dominates, the maximum is the second argument.
-/
TheoremDoc max_eq_right as "max_eq_right" in "Specifications"

/--
`List.length_nil : [].length = 0`

The empty list has no elements — which is why no function can return a valid index into it.
-/
TheoremDoc List.length_nil as "length_nil" in "Specifications"

/--
`Nat.div_add_mod : b * (a / b) + a % b = a`

Nothing is lost by dividing: the quotient times the divisor, plus the remainder, is the
original. The first half of the division contract.
-/
TheoremDoc Nat.div_add_mod as "div_add_mod" in "Specifications"

/--
`Nat.mod_lt : 0 < b → a % b < b`

The remainder is smaller than the divisor — the second half of the division contract, and the
half that needs the divisor to be positive.
-/
TheoremDoc Nat.mod_lt as "mod_lt" in "Specifications"

/--
`Nat.le_add_right : n ≤ n + k`

Adding to a natural number does not decrease it. It is the single-step fact behind *this
accumulator never goes down*.
-/
TheoremDoc Nat.le_add_right as "le_add_right" in "Invariants"

/--
`List.mem_map : b ∈ xs.map f ↔ ∃ a ∈ xs, f a = b`

An element of a mapped list came from an element of the original.
-/
TheoremDoc List.mem_map as "mem_map" in "Specifications"

/--
`List.mem_filter : a ∈ xs.filter p ↔ a ∈ xs ∧ p a`

An element survives a filter exactly when it was there and passes the test. Together with
`List.mem_map` this is how the contract of a composition is assembled from its parts.
-/
TheoremDoc List.mem_filter as "mem_filter" in "Specifications"

/--
`List.reverse_cons : (x :: xs).reverse = xs.reverse ++ [x]`

Reversing moves the head to the end, turning a statement about `reverse` into a statement
about `++`.
-/
TheoremDoc List.reverse_cons as "reverse_cons" in "Algorithms & Data"

/--
`List.getElem?_eq_getElem : (h : i < xs.length) → xs[i]? = some xs[i]`

In range, the checked indexing returns the element the unchecked indexing would.
-/
TheoremDoc List.getElem?_eq_getElem as "getElem?_eq_getElem" in "Refinement & Equivalence"

/-! ## Executions and invariants -/

/--
`LTS.MTr.refl : lts.MTr s [] s`

The execution of no steps, which goes nowhere. One of the two constructors you induct on when
proving a safety property by hand.
-/
TheoremDoc Cslib.LTS.MTr.refl as "MTr.refl" in "Invariants"

/--
`refl : r a a`

Mathlib's general reflexivity lemma, for any relation `r` carrying a `Std.Refl` instance.

It appears in the inventory here for a duller reason than it deserves: `MTr`'s zero-step
constructor is also called `refl`, so writing `| refl => …` as a case name mentions this
name, and the game checks every name a proof mentions.
-/
TheoremDoc refl as "refl" in "Invariants"

/--
`LTS.MTr.stepL : lts.Tr s₁ μ s₂ → lts.MTr s₂ μs s₃ → lts.MTr s₁ (μ :: μs) s₃`

One transition followed by an execution. The other constructor, and the one that carries the
induction step.
-/
TheoremDoc Cslib.LTS.MTr.stepL as "MTr.stepL" in "Invariants"

/--
`LTS.MTr.cons_iff : lts.MTr s₁ (μ :: μs) s₃ ↔ ∃ s₂, lts.Tr s₁ μ s₂ ∧ lts.MTr s₂ μs s₃`

Peel one step off an execution, or build one on. Use it to exhibit a concrete behavior one
transition at a time.
-/
TheoremDoc Cslib.LTS.MTr.cons_iff as "MTr.cons_iff" in "Refinement & Equivalence"

/--
`LTS.mem_traces_iff : μs ∈ lts.traces s ↔ ∃ s', lts.MTr s μs s'`

A word is a trace exactly when some execution performs it. Proving membership therefore means
producing the execution.
-/
TheoremDoc Cslib.LTS.mem_traces_iff as "mem_traces_iff" in "Refinement & Equivalence"

/-! ## Insertion sort, by hand and from the library -/

/--
`List.pairwise_cons : (x :: xs).Pairwise r ↔ (∀ y ∈ xs, r x y) ∧ xs.Pairwise r`

A list is sorted when its head is below everything after it and its tail is sorted. This is
the lemma that takes sortedness apart and puts it back together.
-/
TheoremDoc List.pairwise_cons as "pairwise_cons" in "Algorithms & Data"

/--
`List.Perm.refl : xs.Perm xs`

Every list is a rearrangement of itself — which is exactly why the permutation clause alone
does not specify sorting.
-/
TheoremDoc List.Perm.refl as "Perm.refl" in "Algorithms & Data"

/--
`List.Perm.cons : xs.Perm ys → (x :: xs).Perm (x :: ys)`

Putting the same element on the front of two rearrangements leaves them rearrangements.
-/
TheoremDoc List.Perm.cons as "Perm.cons" in "Algorithms & Data"

/--
`List.Perm.swap : (a :: b :: l).Perm (b :: a :: l)`

Exchanging the first two elements is a rearrangement. With `Perm.cons` and `Perm.trans` it is
all the permutation algebra insertion sort needs.
-/
TheoremDoc List.Perm.swap as "Perm.swap" in "Algorithms & Data"

/--
`List.Perm.trans : xs.Perm ys → ys.Perm zs → xs.Perm zs`

Chain two rearrangements.
-/
TheoremDoc List.Perm.trans as "Perm.trans" in "Algorithms & Data"

/--
`List.orderedInsertM_cons : orderedInsertM r a (b :: l) = do if ← r a b then … else …`

One step of the monadic insertion: compare, then either stop or recurse. Rewriting with it is
how a cost argument gets at the single comparison a step performs.
-/
TheoremDoc List.orderedInsertM_cons as "orderedInsertM_cons" in "Algorithms & Data"

/--
`List.insertionSortM_cons : insertionSortM r (b :: l) = do orderedInsertM r b (← insertionSortM r l)`

One step of the monadic sort: sort the tail, then insert the head.
-/
TheoremDoc List.insertionSortM_cons as "insertionSortM_cons" in "Algorithms & Data"

/--
`List.length_cons : (x :: xs).length = xs.length + 1`

One more element makes a list one longer. It is the arithmetic the cost induction needs when
it moves from `xs` to `x :: xs`.
-/
TheoremDoc List.length_cons as "length_cons" in "Algorithms & Data"

/--
`List.length_insertionSort : (List.insertionSort r l).length = l.length`

Sorting does not change how many elements there are.
-/
TheoremDoc List.length_insertionSort as "length_insertionSort" in "Algorithms & Data"

/--
`TimeM.time_bind : (m >>= f).time = m.time + (f m.ret).time`

Costs add along a sequence of computations. It is the only thing about `TimeM` a cost proof
really needs, and it is why the cost of a sort is the sum of the costs of its insertions.
-/
TheoremDoc Cslib.Algorithms.Lean.TimeM.time_bind as "time_bind" in "Algorithms & Data"

/-! ## Relating two systems -/

/--
`LTS.STr.refl : lts.STr s τ s`

A `τ`-challenge may be answered by standing still: doing nothing is a saturated `τ`-step.
-/
TheoremDoc Cslib.LTS.STr.refl as "STr.refl" in "Refinement & Equivalence"

/--
`LTS.STr.single : lts.Tr s μ s' → lts.STr s μ s'`

Any real transition is in particular a saturated one, with no internal work around it.
-/
TheoremDoc Cslib.LTS.STr.single as "STr.single" in "Refinement & Equivalence"

/--
`delayed_out_step : delayed.STr d0 out d2`

`d0` can perform a saturated `out`: the invisible step, then the visible one. This is the
composite with which the delayed implementation answers the specification's immediate output.
-/
TheoremDoc delayed_out_step as "delayed_out_step" in "Refinement & Equivalence"

/--
`LTS.IsBisimulation.isSimulation : IsBisimulation lts₁ lts₂ r → IsSimulation lts₁ lts₂ r`

A bisimulation answers challenges in both directions, so in particular it answers them in one.
This is how a proof that no simulation exists rules out bisimulation too.
-/
TheoremDoc Cslib.LTS.IsBisimulation.isSimulation as "IsBisimulation.isSimulation"
  in "Refinement & Equivalence"

/--
`LTS.IsBisimulation.traceEq : IsBisimulation lts₁ lts₂ r → r s₁ s₂ → s₁ ~tr[lts₁,lts₂] s₂`

Bisimilar states offer an observer the same words. Proving the strong relation first makes the
weak one free.
-/
TheoremDoc Cslib.LTS.IsBisimulation.traceEq as "IsBisimulation.traceEq"
  in "Refinement & Equivalence"
