import Game

/-!
# Shortcut audit

Each level is supposed to teach something. This file checks that no single automation tactic
the player already has unlocked closes a level's goal outright, which would make the level a
formality rather than an exercise.

Every `example` below states a level's goal, asserts that the obvious one-liners do **not**
close it, and then discharges it with the level's own theorem — so the file compiles only if
the shortcuts genuinely leave work behind *and* the statement is genuinely true.

The assertion is `fail_if_success (tac; done)`, not `fail_if_success tac`: `simp` counts as
succeeding whenever it makes any progress, so the weaker form would pass for a tactic that
simplifies the goal and leaves it open.

This is not a ban on automation: `simp` and `omega` are unlocked and used inside the intended
proofs. It is a check that they do not replace the step the level exists to teach.

Levels whose intended proof *is* a single application — `isort_correct`, `parity_run`,
`sorted_examples` — are deliberately absent: there is no hidden step for a shortcut to skip,
and their teaching value is in the statement rather than the proof.

Run with `lake env lean test/Shortcuts.lean`; it is outside `lean_lib Game` on purpose.
-/

-- A shortcut probe deliberately throws plausible lemmas at the goal, so an argument that
-- turns out not to fire is the point rather than a defect; and the `done` after a tactic
-- that is expected to fail is unreachable by construction.
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Cslib
open Cslib.Algorithms.Lean (TimeM)

/-! ## World 1 -/

/-- Behavior 3 needs the generalised induction; neither simp set finds it. -/
example (s : Bool) (xs : List Bool) : parityDA.mtr s xs = xor s (oddOnes xs) := by
  fail_if_success (simp; done)
  fail_if_success (simp_all; done)
  fail_if_success (decide; done)
  exact parity_mtr s xs

/-- Behavior 7 needs the invariant strengthened over all states before inducting. -/
example (xs : List Unit) : lightDA.mtr lightDA.start xs ≠ Light.broken := by
  fail_if_success (simp [lightDA]; done)
  fail_if_success (simp_all; done)
  fail_if_success (decide; done)
  exact light_never_broken xs

/-- Behavior 8 needs the bridge theorem and then a fresh induction. -/
example (xs : List Bool) :
    parityDA.mtr parityDA.start xs = true ↔ countOnes xs % 2 = 1 := by
  fail_if_success (simp [parityDA, oddOnes, countOnes]; done)
  fail_if_success (omega; done)
  exact parity_abstracts_count xs

/-! ## World 2 -/

/-- Specification 3 needs a witness to be constructed; nothing supplies one. -/
example : ∃ f : Int → Int → Int, IsUpperBound f ∧ ∃ a b, f a b ≠ max a b := by
  fail_if_success (simp; done)
  fail_if_success (omega; done)
  exact upperBound_too_weak

/-- Specification 5 needs the specification instantiated and the order case split. -/
example (f : Int → Int → Int) (hf : IsMaxSpec f) (a b : Int) : f a b = max a b := by
  fail_if_success (simp [IsMaxSpec] at hf ⊢; done)
  fail_if_success (omega; done)
  exact maxSpec_unique f hf a b

/-- Specification 6 needs the empty list to be supplied to the hypothesis. -/
example : ¬∃ f : List ℕ → ℕ, ∀ xs, f xs < xs.length := by
  fail_if_success (simp; done)
  fail_if_success (omega; done)
  exact no_total_index

/-! ## World 3 -/

/-- Properties 3 needs the induction over the execution to be done by hand. -/
example (s₀ s : Int) (ops : List Op) (h₀ : 0 ≤ s₀) (h : account.MTr s₀ ops s) : 0 ≤ s := by
  fail_if_success (simp_all; done)
  fail_if_success (omega; done)
  exact account_safe_by_hand s₀ s ops h₀ h

/-- Properties 4 needs the invariant to be found and `mtrInv_of_trInv` applied. -/
example (s₀ s : Int) (ops : List Op) (h₀ : 0 ≤ s₀) (h : account.MTr s₀ ops s) : 0 ≤ s := by
  fail_if_success (simp_all; done)
  fail_if_success (omega; done)
  exact account_never_overdrawn s₀ s ops h₀ h

/-- Properties 6 needs the invariant *strengthened* before it is inductive. -/
example (p q : ℕ × ℕ) (ms : List Move) (h₀ : p.1 + p.2 = 5) (h : tokens.MTr p ms q) :
    q.1 ≤ 5 := by
  fail_if_success (simp_all [tokens]; done)
  fail_if_success (omega; done)
  exact tokens_bounded p q ms h₀ h

/-- Properties 8 needs the membership lemma and transitivity, not just unfolding. -/
example (a : ℕ) (xs : List ℕ) (h : xs.Pairwise (· ≤ ·)) : (ins a xs).Pairwise (· ≤ ·) := by
  fail_if_success (simp [ins] at h ⊢; done)
  fail_if_success (simp_all; done)
  exact ins_sorted a xs h

/-- Properties 9 needs the accumulator generalised before the induction. -/
example (xs : List ℕ) : totalTR xs 0 = total xs := by
  fail_if_success (simp [totalTR, total]; done)
  fail_if_success (omega; done)
  exact totalTR_eq xs

/-! ## World 4 -/

/-- Verification 10 needs the monad-homomorphism bridge; unfolding does not give it. -/
example (xs : List ℕ) : (timedSort xs).ret = xs.insertionSort (· ≤ ·) := by
  fail_if_success (simp [timedSort, cmpCost]; done)
  fail_if_success (simp_all; done)
  exact timedSort_ret xs

/-- Verification 11 needs the bridge and then both library theorems. -/
example (xs : List ℕ) :
    List.Pairwise (· ≤ ·) (timedSort xs).ret ∧ (timedSort xs).ret.Perm xs := by
  fail_if_success (simp; done)
  fail_if_success (simp [timedSort, cmpCost]; done)
  exact timedSort_correct xs

/-- Verification 12 needs two auxiliary facts and an induction in the cost monad. The bridge
that made correctness free says nothing about `.time`, so it is no shortcut here either. -/
example (xs : List ℕ) : (timedSort xs).time ≤ xs.length * xs.length := by
  fail_if_success (simp [timedSort, cmpCost]; done)
  fail_if_success (omega; done)
  fail_if_success (simp [timedSort_ret]; done)
  exact timedSort_time_le xs

/-! ## World 5 -/

/-- Refinement 5 needs the simulation to be exhibited; unfolding the traces does not do it. -/
example (l : List Unit) (n : ℕ) (h : l.length = n) : implTraces l ⊆ specTraces n := by
  fail_if_success (simp_all; done)
  fail_if_success (simp [implTraces, specTraces, stackImpl, counterSpec, Cslib.LTS.traces]; done)
  exact stack_refines_counter l n h

/-- Refinement 7 refutes *every* simulation, so there is nothing concrete to compute. -/
example : ¬Cslib.LTS.Similarity chooseLate chooseEarly Late.l0 Early.e0 := by
  fail_if_success (simp [Cslib.LTS.Similarity, chooseLate, chooseEarly]; done)
  fail_if_success (decide; done)
  exact late_not_sim_early

/-- Refinement 8 needs the backward direction, where a positive count must be turned into a
non-empty list. -/
example : Cslib.LTS.IsBisimulation stackImpl counterSpec (fun l n => l.length = n) := by
  fail_if_success (simp [Cslib.LTS.IsBisimulation, stackImpl, counterSpec]; done)
  fail_if_success (simp_all; done)
  exact stack_bisim_counter

/-- Refinement 9 needs the saturated transitions to be built. -/
example : Cslib.LTS.IsSWBisimulation delayed direct matchDN := by
  fail_if_success (simp [Cslib.LTS.IsSWBisimulation, delayed, direct, matchDN]; done)
  fail_if_success (decide; done)
  exact delayed_sw_direct

/-- Refinement 10 needs the right relation chosen on each side. -/
example :
    (∀ (l : List Unit) (n : ℕ), l.length = n →
      Cslib.LTS.TraceEq stackImpl counterSpec l n)
    ∧ ¬Cslib.LTS.Bisimilarity chooseLate chooseEarly Late.l0 Early.e0 := by
  fail_if_success (simp_all; done)
  fail_if_success (decide; done)
  exact relation_choice
