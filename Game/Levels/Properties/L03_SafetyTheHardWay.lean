import Game.Levels.Properties.L02_ALemmaWorthFactoringOut

open Cslib

World "Properties"
Level 3

Title "Safety, the Hard Way"

Introduction
"
Back to state. Here is the question every safety argument has to answer: *the account never
goes overdrawn, no matter which sequence of operations a customer performs.* There are
infinitely many such sequences, so you cannot check them.

The account is modelled as a `Cslib.LTS` — a labelled transition system. Unlike World 1's
automaton, a transition here is a **relation** rather than a function, because a withdrawal is
only a legal step when the balance covers it:

```
def account : LTS Int Op where
  Tr := fun s op s' => match op with
    | .deposit n => s' = s + n
    | .withdraw n => (n : Int) ≤ s ∧ s' = s - n
```

`account.MTr s₀ ops s` says there is a finite execution from `s₀` to `s` performing exactly
the operations `ops`. It is an inductive relation with two constructors: `refl`, an execution
of no steps, and `stepL`, one transition followed by an execution. (`refl` is also the name of
a general reflexivity lemma in Mathlib; writing it as a case name here means the constructor,
and the inventory unlocks both.)

Prove the safety property by inducting directly on that execution. This is the honest,
from-first-principles version, and it is the same argument you made for the traffic light in
World 1 — strengthened statement and all. The next level does it again with a library theorem,
and the contrast is the point.
"

/--
`account_safe_by_hand : 0 ≤ s₀ → account.MTr s₀ ops s → 0 ≤ s`

The account stays in credit — proved by induction over the execution, with no library help.
-/
TheoremDoc account_safe_by_hand as "account_safe_by_hand" in "Invariants"

/-- Prove directly, by induction on the execution, that an account starting in credit never
becomes overdrawn. -/
Statement account_safe_by_hand (s₀ s : Int) (ops : List Op)
    (h₀ : 0 ≤ s₀) (h : account.MTr s₀ ops s) : 0 ≤ s := by
  Hint "Induct on the execution itself: `induction h with`. Lean will carry `{h₀}` along,
  re-stating it about whichever state the current case begins in."
  induction h with
  | refl =>
    Hint "No steps were taken, so the final balance is the initial one, and that is `{h₀}`."
    exact h₀
  | @stepL s1 μ s2 μs s3 htr hmtr ih =>
    Hint "One transition from `{s1}` to `{s2}`, then an execution from `{s2}`. The induction
    hypothesis `{ih}` handles the rest, provided you can show `0 ≤ {s2}`. `apply ih` leaves
    exactly that."
    apply ih
    Hint "Now split on which operation `{μ}` was, turn the abstract transition `{htr}` into a
    concrete equation, and let arithmetic finish:
    `cases μ <;> simp [account] at htr <;> omega`."
    cases μ <;> simp [account] at htr <;> omega

Conclusion
"
Proved — and notice how little of that proof was about bank accounts.

The induction on `MTr`, the base case, the appeal to the induction hypothesis: none of it
mentions deposits, withdrawals, or the number zero. Only the last line does. Everything above
it would be word-for-word identical for the traffic light of World 1, for a queue, for a lock,
for any transition system and any property whatsoever.

Which means somebody should write it down once. Somebody has.
"

NewDefinition Cslib.LTS Cslib.LTS.MTr account Op
NewTheorem Cslib.LTS.MTr.refl Cslib.LTS.MTr.stepL refl


TheoremTab "Invariants"
