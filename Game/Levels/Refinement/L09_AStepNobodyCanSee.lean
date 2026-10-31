import Game.Levels.Refinement.L08_BisimulationAcrossRepresentations

open Cslib

World "Refinement"
Level 9

Title "A Step Nobody Can See"

Introduction
"
Real implementations do work that is not part of their interface: a cache lookup, a
reallocation, a bookkeeping update. Those steps are real, and an observer at the interface
cannot see them.

CSlib marks one label as internal with the class `Cslib.HasTau`. The implementation here does
one invisible step before it produces its output; the specification produces the output
straight away:

```
delayed:  d0 --τ--> d1 --out--> d2
direct:   n0 --out--> n1
```

They are **not** bisimilar in the strict sense of Level 8: `d0` can take a `τ`-step and `n0`
cannot match it with a `τ`-step of its own. Under a notion of equivalence that counts
invisible work, every piece of internal bookkeeping would make an implementation inequivalent
to its specification, which is useless.

**Weak bisimilarity** is the repair. A challenge must still be answered, but the answer may be
padded with any number of `τ`-steps before and after — and a `τ`-challenge may be answered by
doing nothing at all. CSlib's convenient formulation is `IsSWBisimulation`, where the challenge
is a single transition and the answer is a *saturated* transition `STr`:

```
LTS.STr.refl   : lts.STr s τ s                     -- answer a τ by standing still
LTS.STr.single : lts.Tr s μ s' → lts.STr s μ s'    -- answer a visible step directly
```

The relation is `matchDN`, which maps both `d0` and `d1` to `n0`, precisely because the step
between them cannot be seen.

For the challenge `n0 -out→ n1`, the implementation must answer from `d0` with a saturated
`out`-transition: a `τ` to `d1`, then the real `out`. That composite is `delayed_out_step`,
built for you from `LTS.STr.tr`.
"

/--
`delayed_sw_direct : LTS.IsSWBisimulation delayed direct matchDN`

The implementation with an internal step and the specification without one answer each
other's visible challenges, up to invisible work.
-/
TheoremDoc delayed_sw_direct as "delayed_sw_direct" in "Refinement & Equivalence"

/-- Show that `matchDN` is a weak bisimulation (in CSlib's single-challenge form) between the
implementation that does internal work and the specification that does not. -/
Statement delayed_sw_direct : Cslib.LTS.IsSWBisimulation delayed direct matchDN := by
  Hint "Introduce the related states and the label, then split the two directions:
  `intro d n hr μ`, then `constructor`."
  intro d n hr μ
  constructor
  · Hint "The implementation challenges. `intro d' htr`, then split on everything and let
    `simp_all` discard the impossible combinations:
    `cases d <;> cases n <;> cases μ <;> cases d' <;> simp_all [delayed, direct, matchDN]`."
    intro d' htr
    cases d <;> cases n <;> cases μ <;> cases d' <;>
      simp_all [delayed, direct, matchDN]
    · Hint "`d0 -τ→ d1`. The specification answers by standing still — `STr.refl` — and `d1`
      still stands for `n0`: `refine ⟨Direct.n0, Cslib.LTS.STr.refl, ?_⟩`, then `trivial`."
      refine ⟨Direct.n0, Cslib.LTS.STr.refl, ?_⟩
      trivial
    · Hint "`d1 -out→ d2`, answered by the specification\'s own `out`:
      `refine ⟨Direct.n1, Cslib.LTS.STr.single (by trivial), ?_⟩`, then `trivial`."
      refine ⟨Direct.n1, Cslib.LTS.STr.single (by trivial), ?_⟩
      trivial
  · Hint "Now the specification challenges, and the implementation must answer."
    intro n' htr
    cases d <;> cases n <;> cases μ <;> cases n' <;>
      simp_all [delayed, direct, matchDN]
    · Hint "From `d0`, answering `out` requires doing the invisible step first. That composite
      is `delayed_out_step`: `refine ⟨Delayed.d2, delayed_out_step, ?_⟩`, then `trivial`."
      refine ⟨Delayed.d2, delayed_out_step, ?_⟩
      trivial
    · Hint "From `d1` the `out` is immediate:
      `refine ⟨Delayed.d2, Cslib.LTS.STr.single (by trivial), ?_⟩`, then `trivial`."
      refine ⟨Delayed.d2, Cslib.LTS.STr.single (by trivial), ?_⟩
      trivial

Conclusion
"
The implementation and the specification are weakly bisimilar: `d0 ≈ n0`, via
`IsSWBisimulation.isWeakBisimulation`.

Weak bisimilarity is what you usually want when comparing an implementation with a
specification, because specifications are written without the implementation's bookkeeping and
should not have to anticipate it. The cost of the weakening is real, though, and worth
knowing: weak bisimilarity cannot see how *much* internal work is done, so a system that
diverges — spinning on `τ` forever and never producing the output — is weakly bisimilar to one
that produces it immediately. If termination matters, weak bisimilarity is not the relation
that establishes it, and CSlib's `Divergence` and `Termination` are where to look instead.

One relation left to discuss, which is the one you have been using all along without being
asked to choose it.
"

NewDefinition TAct Cslib.HasTau Delayed Direct delayed direct matchDN Cslib.LTS.IsSWBisimulation Cslib.LTS.STr
NewTheorem Cslib.LTS.STr.refl Cslib.LTS.STr.single delayed_out_step
TheoremTab "Refinement & Equivalence"
