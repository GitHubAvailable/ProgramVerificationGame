import Game.Levels.Properties

open Cslib

World "Refinement"
Level 1

Title "The Same Answer, Where It Matters"

Introduction
"
*Optional branch.* Nothing in the core path depends on this world, and you can come back to it
whenever you like.

The question it asks is the one that comes up every time a component is rewritten: **may I
replace this with that?** The answer is almost never a plain yes, and the interesting part is
what qualifies it.

Start with the smallest version. Two ways to read an element out of a list:

```
def lookupRaw     (xs : List ℕ) (i : ℕ) : ℕ        := xs.getD i 0
def lookupChecked (xs : List ℕ) (i : ℕ) : Option ℕ := xs[i]?
```

The first is what a language without bounds checks gives you: out of range it quietly hands
back a default. The second reports the failure instead.

They do not even have the same return type, so *equal* is not available. What is available is
a claim about the inputs where both behave: **when the index is in range, the checked version
returns exactly what the raw version returns.** That is **conditional functional equivalence**,
and the condition is the whole content of it.
"

/--
`lookupChecked_agrees : i < xs.length → lookupChecked xs i = some (lookupRaw xs i)`

On indices that are in range, the checked lookup returns exactly the unchecked one's answer.
-/
TheoremDoc lookupChecked_agrees as "lookupChecked_agrees" in "Refinement & Equivalence"

/-- Show that on in-range indices the checked lookup agrees with the unchecked one. -/
Statement lookupChecked_agrees (xs : List ℕ) (i : ℕ) (h : i < xs.length) :
    lookupChecked xs i = some (lookupRaw xs i) := by
  Hint "Unfold both definitions and use the in-range assumption to evaluate the indexing:
  `simp [lookupChecked, lookupRaw, List.getD, List.getElem?_eq_getElem h]`."
  simp [lookupChecked, lookupRaw, List.getD, List.getElem?_eq_getElem h]

Conclusion
"
On its domain, the replacement computes what the original computed.

Say exactly that and no more. The theorem does not claim the two functions are the same — they
are not, and could not be, since one of them can report failure. It claims that a caller who
only ever passes in-range indices cannot tell them apart.

That qualified form is what *equivalence* almost always means in practice, and the next level
is about the part the qualification leaves out.
"

NewDefinition lookupRaw lookupChecked
NewTheorem List.getElem?_eq_getElem
TheoremTab "Refinement & Equivalence"
