import Game.Levels.Properties.L03_SafetyTheHardWay

open Cslib

World "Properties"
Level 4

Title "One Step Is Enough"

Introduction
"
Same theorem as the last level. Different proof.

That is the proof you just wrote by hand. You would write it again for the next system, and
again for the next property, and it would be the same proof every time. CSlib has already
written it, once and for all:

```
LTS.TrInv p        -- p survives one transition
LTS.MTrInv p       -- p survives an entire execution
LTS.mtrInv_of_trInv : lts.TrInv p → lts.MTrInv p
```

So your obligation shrinks to the single-step case — a finite check over the two kinds of
operation — and the general theorem does the induction.
"

/--
`account_never_overdrawn : 0 ≤ s₀ → account.MTr s₀ ops s → 0 ≤ s`

An account that starts in credit stays in credit, whatever finite sequence of deposits and
withdrawals is performed.
-/
TheoremDoc account_never_overdrawn as "account_never_overdrawn" in "Invariants"

/-- Starting from a balance that is not negative, no finite sequence of deposits and
withdrawals can leave the account overdrawn. -/
Statement account_never_overdrawn (s₀ s : Int) (ops : List Op)
    (h₀ : 0 ≤ s₀) (h : account.MTr s₀ ops s) : 0 ≤ s := by
  Hint "Do not induct on `{h}`. State the single-step obligation first:
  `have hstep : account.TrInv (fun b => 0 ≤ b) := by ...`"
  have hstep : account.TrInv (fun b => 0 ≤ b) := by
    Hint "`TrInv` unfolds to: for all `s1 μ s2`, if `account.Tr s1 μ s2` and `0 ≤ s1`, then
    `0 ≤ s2`. Introduce all of them."
    intro s1 μ s2 htr hs1
    Hint "Now split on which operation `{μ}` is. `cases μ` gives you the deposit case and the
    withdrawal case."
    cases μ
    · Hint "A deposit. `simp [account] at htr` turns the abstract transition into a concrete
      equation about `{s2}`, and the arithmetic is then routine."
      simp [account] at htr
      omega
    · Hint "A withdrawal. Here `simp [account] at htr` gives you two facts: the withdrawal was
      affordable, and what the new balance is."
      simp [account] at htr
      omega
  Hint "You now have the one-step fact `{hstep}`. `Cslib.LTS.mtrInv_of_trInv` upgrades it to
  the whole execution — apply it to `{h}` and `{h₀}`."
  exact Cslib.LTS.mtrInv_of_trInv hstep s₀ ops s h h₀

Conclusion
"
You proved a property of *every* finite execution of the system, and the only thing you
checked by hand was what one deposit and one withdrawal do.

This is the first of the game's two clear wins from CSlib. The induction over executions is
not hard, but it is the same induction every time, for every system and every invariant. It
lives in `LTS.mtrInv_of_trInv` so that you never write it again — and because it is stated for
an arbitrary `LTS` and an arbitrary predicate, it applies to the next system you model without
any changes.

Keep the shape in mind: **find the invariant, prove it survives one step, inherit the rest.**
"

NewDefinition Cslib.LTS.TrInv Cslib.LTS.MTrInv
NewTheorem Cslib.LTS.mtrInv_of_trInv
TheoremTab "Invariants"
