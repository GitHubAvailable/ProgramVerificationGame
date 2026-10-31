import Game.Levels.Specification.L03_TooWeakASpec

open Cslib

World "Specification"
Level 4

Title "Saying What You Meant"

Introduction
"
`IsUpperBound` was too weak because it forgot to say the result is *one of the arguments*. Add
that clause and you get a specification worth the name:

```
def IsMaxSpec (f : Int → Int → Int) : Prop :=
  ∀ a b, (f a b = a ∨ f a b = b) ∧ a ≤ f a b ∧ b ≤ f a b
```

Before asking whether this one is strong enough, check that it is not *too* strong — that the
function you had in mind actually satisfies it. A specification nothing can meet is useless in
a different way, and you will meet one of those shortly.

So: prove that `max` satisfies `IsMaxSpec`. The bounds are Mathlib's `le_max_left` and
`le_max_right`. For the new clause you have to say which of the two arguments the maximum is,
and that depends on which is bigger — so split on `le_total a b`, which gives you `a ≤ b` in
one branch and `b ≤ a` in the other.
"

/--
`max_isMaxSpec : IsMaxSpec (fun a b => max a b)`

Mathlib's `max` satisfies the strengthened specification.
-/
TheoremDoc max_isMaxSpec as "max_isMaxSpec" in "Specifications"

/-- Show that `max` satisfies `IsMaxSpec`: it returns one of its arguments, and it is at
least as large as both. -/
Statement max_isMaxSpec : IsMaxSpec (fun a b => max a b) := by
  Hint "Take arbitrary arguments with `intro a b`."
  intro a b
  Hint "Two of the three clauses are Mathlib lemmas. `refine ⟨?_, le_max_left a b, le_max_right a b⟩`
  supplies them and leaves you the interesting one."
  refine ⟨?_, le_max_left a b, le_max_right a b⟩
  Hint "Which argument the maximum equals depends on which is bigger.
  `rcases le_total a b with h | h` splits into those two cases."
  rcases le_total a b with h | h
  · Hint "Here `{h} : a ≤ b`, so the maximum is `b` — the right disjunct. `right` selects it,
    and `max_eq_right` proves it."
    right
    exact max_eq_right h
  · Hint "Here `{h} : b ≤ a`, so the maximum is `a`. `left`, then `max_eq_left`."
    left
    exact max_eq_left h

Conclusion
"
The strengthened contract is satisfiable, and `max` satisfies it.

That is only half of what you want to know. A contract can be satisfiable and still be wrong —
`IsUpperBound` was. The question the next level settles is whether this one is tight: whether
it leaves room for any implementation other than the one you meant.
"

NewDefinition IsMaxSpec
NewTheorem le_total max_eq_left max_eq_right
NewTactic left right rcases
TheoremTab "Specifications"
