import Game.Levels.Verification.L11_SortedAndAPermutation

open Cslib
open Cslib.Algorithms.Lean (TimeM)

World "Verification"
Level 12

Title "A Bound on the Comparisons"

Introduction
"
The capstone. Prove that sorting a list of `n` elements never costs more than `n²`
comparisons.

Nothing you have done so far helps directly. `timedSort_ret` is about `.ret`, and the whole
point of the previous level was that it says nothing about `.time`. There is no theorem in
either library whose statement is this one. You are going to do an induction, and you need two
ingredients before you can start.

**One insertion is linear.** `List.orderedInsertM` compares the new element with the elements
of the list from the front and stops when it finds its place, so it performs at most as many
comparisons as the list is long. That is an induction on the list, using
`List.orderedInsertM_cons` to expose one step and `TimeM`'s `time_bind` to see that costs add.

**The sorted list has the same length.** Insertion sort's recursive call produces a list the
same length as its input, which is what makes the first ingredient useful at each step. You
could prove that by a second induction, but you do not have to — `timedSort_ret` says the
result is `List.insertionSort`, and `List.length_insertionSort` says that preserves length.
A use for the bridge in a proof that is otherwise entirely about cost.

With both in hand, the induction is arithmetic: sorting `x :: xs` costs what sorting `xs` cost,
plus at most `xs.length` for the insertion, and `n² + n ≤ (n+1)²`.
"

/--
`timedSort_time_le : (timedSort xs).time ≤ xs.length * xs.length`

The cost-annotated insertion sort performs at most quadratically many comparisons, in the
declared cost model.
-/
TheoremDoc timedSort_time_le as "timedSort_time_le" in "Algorithms & Data"

/-- Prove a quadratic bound on the number of comparisons the cost-annotated insertion sort
performs. -/
Statement timedSort_time_le (xs : List ℕ) : (timedSort xs).time ≤ xs.length * xs.length := by
  Hint "First ingredient: one insertion costs at most the length of the list it inserts into.
  `have hoi : ∀ (a : ℕ) (ys : List ℕ), (List.orderedInsertM cmpCost a ys).time ≤ ys.length := by ...`"
  have hoi : ∀ (a : ℕ) (ys : List ℕ),
      (List.orderedInsertM cmpCost a ys).time ≤ ys.length := by
    intro a ys
    Hint "Induct on `{ys}`."
    induction ys with
    | nil =>
      Hint "Inserting into the empty list compares nothing. `simp`."
      simp
    | cons y ys ih =>
      Hint "`rw [List.orderedInsertM_cons]` exposes the single comparison, and
      `simp [cmpCost, TimeM.tick]` charges it and pushes the cost through the bind."
      rw [List.orderedInsertM_cons]
      simp [cmpCost, TimeM.tick]
      Hint "Then split on the comparison: if the element belongs here the recursion stops, and
      otherwise the induction hypothesis `{ih}` bounds the rest.
      `by_cases h : a ≤ y`."
      by_cases h : a ≤ y
      · simp [h]
      · simp [h]
        omega
  Hint "Second ingredient: sorting does not change the length. The bridge gives it to you:
  `have hlen : ∀ ys : List ℕ, (timedSort ys).ret.length = ys.length := by
  intro ys; rw [timedSort_ret, List.length_insertionSort]`"
  have hlen : ∀ ys : List ℕ, (timedSort ys).ret.length = ys.length := by
    intro ys
    rw [timedSort_ret, List.length_insertionSort]
  Hint "Now unfold `timedSort` everywhere — in the goal and in `{hlen}` — and induct on
  `{xs}`: `unfold timedSort at *`, then `induction xs with`."
  unfold timedSort at *
  induction xs with
  | nil =>
    Hint "Sorting nothing costs nothing. `simp`."
    simp
  | cons x xs ih =>
    Hint "`rw [List.insertionSortM_cons]` exposes one recursive call followed by one
    insertion, and `simp only [TimeM.time_bind, List.length_cons]` shows that their costs
    add."
    rw [List.insertionSortM_cons]
    simp only [TimeM.time_bind, List.length_cons]
    Hint "Collect the three facts the arithmetic needs: the insertion's cost, the length of
    what it inserts into, and the expansion of `(n+1)²`.
    `have h1 := hoi x (List.insertionSortM cmpCost xs).ret`,
    `have h2 := hlen xs`,
    `have h3 : (xs.length + 1) * (xs.length + 1) = xs.length * xs.length + 2 * xs.length + 1 := by ring`"
    have h1 := hoi x (List.insertionSortM cmpCost xs).ret
    have h2 := hlen xs
    have h3 : (xs.length + 1) * (xs.length + 1)
        = xs.length * xs.length + 2 * xs.length + 1 := by ring
    Hint "With `{ih}`, `{h1}`, `{h2}` and `{h3}` in the context the goal is linear. `omega`."
    omega

Conclusion
"
A cost bound on a library algorithm, proved where the cost actually lives.

This is the level the whole world was built to reach, and it is worth saying why it could not
have been shorter. No existing theorem states it. The bridge that made correctness free is
useless for cost by construction, and could only be borrowed here for an incidental fact about
lengths. Everything else — that one insertion is linear, that the costs of a bind add, that
the recursion accumulates them — you established yourself, using exactly the techniques of
Worlds 1 to 3: follow the recursion, strengthen until the hypothesis is usable, factor the
ingredients out before the induction that needs them.

Two last cautions about what you have proved. The bound is quadratic and insertion sort really
is quadratic in the worst case, but `n²` is not tight — the true worst case is `n(n-1)/2`, and
proving *that* is a different and harder induction. And the number counted is comparisons in a
model you declared, not time on a machine. `TimeM`'s own documentation is blunt about this:
the annotations are trusted, not verified. A cost model is a specification like any other, and
like any other it can be wrong about the thing it was meant to describe.

That is the core path. World 5 is optional, and asks a question none of this has touched: when
may one implementation replace another?
"

NewTheorem List.orderedInsertM_cons List.insertionSortM_cons List.length_insertionSort List.length_cons Cslib.Algorithms.Lean.TimeM.time_bind
NewTactic ring
TheoremTab "Algorithms & Data"
