import Game.Levels.Specification.L05_StrongEnoughToPinItDown

open Cslib

World "Specification"
Level 6

Title "A Specification Nothing Can Satisfy"

Introduction
"
A contract can fail in the other direction too: by demanding more than any program could
deliver.

Here is one. *Write a function that, given a list of numbers, returns a valid index into it* —
in other words, a function `f : List ℕ → ℕ` with `f xs < xs.length` for every `xs`.

It sounds reasonable until you think about the empty list. There are no valid indices into
`[]`, so no number `f []` can be below `0`.

Prove that no such function exists. The statement is a negation, so assume you were handed one
and derive a contradiction: `rintro ⟨f, hf⟩` names the supposed function and its supposed
property, and then you only have to ask `hf` about the empty list.
"

/--
`no_total_index : ¬∃ f : List ℕ → ℕ, ∀ xs, f xs < xs.length`

No total function can return a valid index into every list, because the empty list has none.
-/
TheoremDoc no_total_index as "no_total_index" in "Specifications"

/-- Show that the contract *returns a valid index into its argument* is unsatisfiable, by
refuting the existence of any function meeting it. -/
Statement no_total_index : ¬∃ f : List ℕ → ℕ, ∀ xs, f xs < xs.length := by
  Hint "Assume such a function exists and take it apart: `rintro ⟨f, hf⟩`."
  rintro ⟨f, hf⟩
  Hint "`{hf}` is supposed to hold for *every* list. Ask it about the empty one:
  `have h := hf []`."
  have h := hf []
  Hint "`{h}` now says some natural number is smaller than `[].length`, which is `0`.
  `simp at h` evaluates the length and finds the contradiction."
  simp at h

Conclusion
"
The contract is not merely hard to meet — it is impossible, and the empty list is the whole
reason.

Both failures you have now seen come from the same place: the contract and the intention came
apart at a case nobody pictured. Too weak, and `IsUpperBound` let through a function that
overshoots. Too strong, and this one lets through nothing at all. Neither mistake is visible
from reading the proposition; both are visible the moment you ask about the boundary.

The repair here is not to weaken the postcondition but to add a precondition — `xs ≠ []` —
or to change the return type to `Option ℕ` so the function can say *no answer*. That second
option is a real design choice, and World 5 comes back to it.
"

NewTheorem List.length_nil
NewTactic rintro
TheoremTab "Specifications"
