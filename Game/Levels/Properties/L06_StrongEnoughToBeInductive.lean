import Game.Levels.Properties.L05_ADifferentSystemEntirely

open Cslib

World "Properties"
Level 6

Title "Strong Enough to Be Inductive"

Introduction
"
Two buckets hold five tokens between them. A move takes one token from one bucket and puts it
in the other:

```
def tokens : LTS (ℕ × ℕ) Move where
  Tr := fun p m q => match m with
    | .toA => 0 < p.2 ∧ q = (p.1 + 1, p.2 - 1)
    | .toB => 0 < p.1 ∧ q = (p.1 - 1, p.2 + 1)
```

You want: *the first bucket never holds more than five.*

Try to prove that the way you proved the last two, with the property `fun p => p.1 ≤ 5`, and
it fails — and the failure is instructive rather than technical. From the state `(5, 3)` the
property holds, a `toA` move is legal because the second bucket is non-empty, and it leads to
`(6, 2)` where the property is false. One step destroys it. The property is **not inductive**.

Of course `(5, 3)` is not a state the system can actually be in: there are only five tokens.
But the single-step obligation does not know that. It asks about *every* state satisfying the
property, including the unreachable ones.

The repair is to prove something stronger — the thing that is actually true of every reachable
state, namely that the total is conserved:

```
fun p => p.1 + p.2 = 5
```

*That* survives a move, and it implies what you wanted. Finding such a strengthening is the
central difficulty of invariant-based verification, and there is no recipe; the honest advice
is that your invariant must explain why the bad states cannot arise, not merely assert they do
not.
"

/--
`tokens_bounded : p.1 + p.2 = 5 → tokens.MTr p ms q → q.1 ≤ 5`

The first bucket never holds more than five tokens — proved via the stronger, inductive
property that the total is conserved.
-/
TheoremDoc tokens_bounded as "tokens_bounded" in "Invariants"

/-- Show that the first bucket never exceeds five tokens, by strengthening the property to
the conservation of the total. -/
Statement tokens_bounded (p q : ℕ × ℕ) (ms : List Move)
    (h₀ : p.1 + p.2 = 5) (h : tokens.MTr p ms q) : q.1 ≤ 5 := by
  Hint "State the *strengthened* invariant, not the one you want:
  `have hstep : tokens.TrInv (fun r => r.1 + r.2 = 5) := by ...`"
  have hstep : tokens.TrInv (fun r => r.1 + r.2 = 5) := by
    Hint "Introduce everything, then split on the move."
    intro r m r' htr hr
    cases m
    · Hint "A `toA` move. `simp [tokens] at htr` gives you that the second bucket was
      non-empty and what the new pair is; `obtain ⟨h1, h2⟩ := htr` names both, and `subst h2`
      replaces `{r'}` by it."
      simp [tokens] at htr
      obtain ⟨h1, h2⟩ := htr
      subst h2
      Hint "Now the goal is arithmetic about the components of `{r}`. `simp` exposes them and
      `omega` finishes — but note that you need `{h1}`, because subtraction on `ℕ` truncates
      and the equation is only true when the bucket really was non-empty."
      simp
      omega
    · Hint "The mirror image."
      simp [tokens] at htr
      obtain ⟨h1, h2⟩ := htr
      subst h2
      simp
      omega
  Hint "Inherit the strengthened property over the whole execution, then weaken it to what
  you were asked for: `have hq := Cslib.LTS.mtrInv_of_trInv hstep p ms q h h₀`, and `omega`."
  have hq := Cslib.LTS.mtrInv_of_trInv hstep p ms q h h₀
  omega

Conclusion
"
The bound you wanted, by way of a statement you did not ask for.

This is the standard shape of a real invariant proof, and it is worth naming the two
directions that can go wrong. An invariant too weak is not preserved by a step, and the
single-step obligation simply fails — that is what happened to `p.1 ≤ 5`. An invariant too
strong is preserved but false at the start, and the initial obligation fails instead. You are
looking for something in between, and `p.1 + p.2 = 5` is it: true initially because that is
how the tokens were distributed, preserved because moving a token conserves the total, and
strong enough to give you the bound.

Notice also that truncated subtraction on `ℕ` is quietly doing work here. `p.2 - 1` when
`p.2 = 0` is `0`, not `-1`, so without the guard `0 < p.2` the total would not be conserved.
The transition relation carries that guard, and your proof used it.
"

NewDefinition Move tokens
NewTactic subst
TheoremTab "Invariants"
