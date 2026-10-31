import Game.Levels.Behavior.L04_CorrectFromTheStart

open Cslib
open Cslib.Automata

World "Behavior"
Level 5

Title "The Words It Accepts"

Introduction
"
So far the machine computes a value. Classically, machines are used to *recognise* words: you
mark some states as accepting, and the machine accepts a word when it finishes in one of them.

CSlib's `Cslib.Automata.DA.FinAcc` is that — a `DA` together with a set `accept` of accepting
states — and `Cslib.Automata.Acceptor.Accepts` is the recognition condition:

```
Accepts a xs  ↔  a.mtr a.start xs ∈ a.accept
```

`parityAcc` is our machine with `accept = {true}`, so the words it accepts should be exactly
the words with an odd number of `1`s. Prove it.

This is the first statement in the game about an *infinite set* — the language — rather than
about a single run. The proof, though, is short, because you already did the work: unfolding
the acceptance condition turns the goal into `parity_correct`.
"

/--
`parity_language : Acceptor.Accepts parityAcc xs ↔ oddOnes xs = true`

The language recognised by the parity automaton is exactly the set of words containing an odd
number of `true`s.
-/
TheoremDoc parity_language as "parity_language" in "States & Transitions"

/-- Show that `parityAcc` accepts exactly the words with an odd number of `true`s. -/
Statement parity_language (xs : List Bool) :
    Acceptor.Accepts parityAcc xs ↔ oddOnes xs = true := by
  Hint "Unfold the acceptance condition and the machine:
  `simp [Cslib.Automata.Acceptor.Accepts, parityAcc]`. Membership in the one-element set
  `{true}` is just an equation, so simp will clear that away too."
  simp [Cslib.Automata.Acceptor.Accepts, parityAcc]
  Hint "What remains is `parityDA.mtr parityDA.start {xs} = oddOnes {xs}` — the theorem you
  proved one level ago."
  exact parity_correct xs

Conclusion
"
You have characterised the machine's language: not *these words are accepted*, but *these and
no others*.

Notice the division of labour. `Acceptor` contributed the definition of acceptance, which is
the same for every deterministic automaton anyone will ever write. `parity_correct`
contributed the one fact specific to this machine. The general definition and the specific
theorem met, and the result was a statement about an infinite set of words.

That division is what a library is for, and it is the shape of everything that follows.
"

NewDefinition Cslib.Automata.DA.FinAcc Cslib.Automata.Acceptor.Accepts parityAcc
NewTheorem parity_correct
NewTactic exact
TheoremTab "States & Transitions"
