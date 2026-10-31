import Game.Levels.Specification.L04_MaxMeetsAStrongerSpec

open Cslib

World "Specification"
Level 5

Title "Strong Enough to Pin It Down"

Introduction
"
Here is the sharpest thing you can say about a specification: **it determines the
implementation.** Not *`max` satisfies it*, but *anything satisfying it is `max`*.

That is a much stronger claim, and it is the one that tells you the contract is finished. If
two different functions could both satisfy it, the contract has not decided something it ought
to have decided — which is exactly the defect `IsUpperBound` had, and exactly what your
counterexample in Level 3 exhibited.

So let `f` be *any* function satisfying `IsMaxSpec`, and prove it agrees with `max`
everywhere.

The proof has the shape you would use on paper. The specification tells you `f a b` is `a` or
`b`, and that it is at least both. Those three facts, plus knowing which of `a` and `b` is
larger, leave only one possibility.
"

/--
`maxSpec_unique : IsMaxSpec f → f a b = max a b`

The strengthened specification admits exactly one implementation: any function satisfying it
is `max`.
-/
TheoremDoc maxSpec_unique as "maxSpec_unique" in "Specifications"

/-- Show that `IsMaxSpec` pins down `max`: every function satisfying it agrees with `max` on
every input. -/
Statement maxSpec_unique (f : Int → Int → Int) (hf : IsMaxSpec f) (a b : Int) :
    f a b = max a b := by
  Hint "Instantiate the specification at these particular arguments and name its three
  components: `obtain ⟨hcase, h1, h2⟩ := hf a b`."
  obtain ⟨hcase, h1, h2⟩ := hf a b
  Hint "Now split on which of `{a}` and `{b}` is larger: `rcases le_total a b with h | h`."
  rcases le_total a b with h | h
  · Hint "With `{h} : a ≤ b` the right-hand side is `b`, so `rw [max_eq_right h]` makes the
    goal `f {a} {b} = {b}`. Then `{hcase}`, `{h1}`, `{h2}` and `{h}` together force it, and
    `omega` can see that once the disjunction is in the context."
    rw [max_eq_right h]
    omega
  · Hint "Symmetrically, `rw [max_eq_left h]` and then `omega`."
    rw [max_eq_left h]
    omega

Conclusion
"
Every implementation of this contract is `max`. The specification is tight.

That is the standard you are aiming at, and it is worth saying plainly what it costs. Writing
a contract that *admits* your implementation is easy and nearly worthless; `IsUpperBound` did
that. Writing one that *excludes everything else* is the work, and the way to check you have
done it is to prove uniqueness, or to go hunting for a second implementation and fail.

In practice you often cannot pin a function down completely, and should not want to — a
specification that permits several correct implementations is what lets an implementation be
replaced. World 5 is about exactly that freedom. The skill is knowing which parts of behavior
you meant to fix and which you meant to leave open.
"

NewTactic obtain
TheoremTab "Specifications"
