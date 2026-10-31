import Game.Levels.Specification.L06_ASpecificationNothingCanSatisfy

open Cslib

World "Specification"
Level 7

Title "The Division Contract"

Introduction
"
The most famous contract in programming is the one for integer division, and it has two parts
that only mean something together:

```
b * q + r = a   and   r < b
```

The first says nothing was lost. The second says the remainder was reduced as far as it goes.
Drop the first and `q = 0, r = 0` is fine; drop the second and `q = 0, r = a` is fine. Neither
is division.

`divmod a b` returns the pair `(a / b, a % b)`. Prove it satisfies both clauses — under the
precondition `0 < b`, which you should expect by now to be load-bearing. (It is: Lean defines
`a % 0 = a`, so the second clause fails outright at `b = 0`.)

Two library facts do the work, and the contract is written in the direction they state it:
`Nat.div_add_mod a b : b * (a / b) + a % b = a` is the first clause and
`Nat.mod_lt a : 0 < b → a % b < b` is the second.
"

/--
`divmod_correct : 0 < b → b * (divmod a b).1 + (divmod a b).2 = a ∧ (divmod a b).2 < b`

Quotient and remainder satisfy the two-part division contract whenever the divisor is
positive.
-/
TheoremDoc divmod_correct as "divmod_correct" in "Specifications"

/-- Prove that `divmod` meets the two-part division contract: nothing is lost, and the
remainder is smaller than the divisor. -/
Statement divmod_correct (a b : ℕ) (h : 0 < b) :
    b * (divmod a b).1 + (divmod a b).2 = a ∧ (divmod a b).2 < b := by
  Hint "`unfold divmod` replaces the pair by its components, so the goal becomes a statement
  about `a / b` and `a % b`."
  unfold divmod
  Hint "Both halves are now library facts:
  `exact ⟨Nat.div_add_mod a b, Nat.mod_lt a h⟩`."
  exact ⟨Nat.div_add_mod a b, Nat.mod_lt a h⟩

Conclusion
"
Two obligations, one implementation, and neither obligation would have been enough alone.

That is the pattern you will see again in the capstone. Real contracts are conjunctions,
because a single property is almost never specific enough to rule out the degenerate
implementations: returning nothing, returning the input unchanged, returning zero. When you
write a specification, the useful question is not *is this true of my program* but *what else
is this true of*.
"

NewDefinition divmod
NewTheorem Nat.div_add_mod Nat.mod_lt
TheoremTab "Specifications"
