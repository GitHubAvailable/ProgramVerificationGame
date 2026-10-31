import Game.Levels.Specification.L07_TheDivisionContract

open Cslib

World "Specification"
Level 8

Title "Contracts That Compose"

Introduction
"
Programs are built by composing functions, and so are their contracts.

```
def scaleNonNeg (xs : List Int) : List Int :=
  (xs.filter (fun x => 0 ≤ x)).map (fun x => x * 2)
```

Two steps: discard the negatives, then double what is left. What can you promise about the
output? That every element of it is non-negative and even.

Neither half of the program establishes that on its own. `filter` contributes the sign;
`map` contributes the doubling. The proof has to take an arbitrary element of the result,
trace it back through `map` to the element of the filtered list it came from, and trace that
back through `filter` to learn it was non-negative.

`simp` knows how membership in a `map` and a `filter` unfolds, so the tracing-back is one
simp call. What it leaves you is the element `x` it came from, the fact that `0 ≤ x`, and the
knowledge that your element is `x * 2`.
"

/--
`scaleNonNeg_spec : ∀ y ∈ scaleNonNeg xs, 0 ≤ y ∧ y % 2 = 0`

Every element of the output is non-negative and even.
-/
TheoremDoc scaleNonNeg_spec as "scaleNonNeg_spec" in "Specifications"

/-- Prove the contract of `scaleNonNeg`: every element of its output is non-negative and
even. -/
Statement scaleNonNeg_spec (xs : List Int) : ∀ y ∈ scaleNonNeg xs, 0 ≤ y ∧ y % 2 = 0 := by
  Hint "Take an arbitrary element of the output together with the evidence that it is one:
  `intro y hy`."
  intro y hy
  Hint "Now unfold what membership in the output means: `simp [scaleNonNeg] at hy`. This
  pushes through both `List.map` and `List.filter` at once."
  simp [scaleNonNeg] at hy
  Hint "`{hy}` now says `{y}` is `x * 2` for some non-negative `x`. Name that `x`, keep the
  sign fact, and substitute the equation: `obtain ⟨x, hx0, rfl⟩ := hy`."
  obtain ⟨x, hx0, rfl⟩ := hy
  Hint "Both halves are now arithmetic about `x * 2` given `0 ≤ x`, which `omega` handles."
  omega

Conclusion
"
The contract of a composition, assembled from the contracts of its parts.

That is the only way proofs survive contact with real code. Nobody verifies a thousand-line
function; they verify the twenty functions it calls and compose the results. The composition
step is where the reasoning happens, and you have just done one: the `filter` gave you the
precondition that the `map`'s postcondition needed.

World 2 is done. You can write a contract, check it is satisfiable, check it is tight, check
its assumptions are needed, and assemble it from smaller ones. World 3 is about making the
proofs themselves reusable.
"

NewDefinition scaleNonNeg
NewTheorem List.mem_map List.mem_filter
TheoremTab "Specifications"
