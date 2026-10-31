import Game.Levels.Behavior

open Cslib

World "Specification"
Level 1

Title "A Contract for a Function"

Introduction
"
A specification is a claim about an implementation. In Lean you can write one as an ordinary
proposition — no special logic required. The pattern that covers almost everything is

```
P x → Q x (f x)
```

*if the input satisfies the precondition `P`, then the input and the output together satisfy
the postcondition `Q`.* You do not need Hoare triples for a pure function; the arrow **is** the
contract, and `→` is the only connective involved.

Here is the function. `clamp lo hi x` forces `x` into the range `[lo, hi]`:

```
def clamp (lo hi x : Int) : Int :=
  if x < lo then lo else if hi < x then hi else x
```

Its contract: *given `lo ≤ hi`, the result lies between `lo` and `hi`.* The precondition is
`lo ≤ hi`; the postcondition is the conjunction of the two bounds.

To prove it, unfold the definition and consider the three branches of the nested `if`. That is
what `split_ifs` does: it replaces the goal with one goal per branch, each carrying the
condition that led there as a hypothesis. After that it is arithmetic, and `omega` does
arithmetic.
"

/--
`clamp_in_range : lo ≤ hi → lo ≤ clamp lo hi x ∧ clamp lo hi x ≤ hi`

Clamping into a non-empty range produces a value inside that range.
-/
TheoremDoc clamp_in_range as "clamp_in_range" in "Specifications"

/-- Prove that `clamp` meets its contract: when the range is non-empty, the clamped value
lies inside it. -/
Statement clamp_in_range (lo hi x : Int) (h : lo ≤ hi) :
    lo ≤ clamp lo hi x ∧ clamp lo hi x ≤ hi := by
  Hint "Start by replacing `clamp` with its definition: `unfold clamp`."
  unfold clamp
  Hint "Now there is a nested `if`. `split_ifs` gives you one goal per branch, each with the
  comparison that chose it available as a hypothesis — and every one of them is then linear
  arithmetic, which `omega` settles. Write `split_ifs <;> omega`."
  split_ifs <;> omega

Conclusion
"
A precondition, a postcondition, an arrow between them, and a proof. That is a verified
function.

Two things to notice. The contract is an ordinary `Prop`, so everything you already know about
proving propositions applies — there is no separate program logic to learn. And the
precondition did real work: it appears in the proof, because without it the statement is
false. The next level makes that concrete.
"

NewDefinition clamp Int
NewTactic unfold split_ifs constructor refine
TheoremTab "Specifications"
