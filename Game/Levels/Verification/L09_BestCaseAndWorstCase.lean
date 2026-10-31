import Game.Levels.Verification.L08_TheSameAlgorithmOverAMonad

open Cslib
open Cslib.Algorithms.Lean (TimeM)

World "Verification"
Level 9

Title "Best Case and Worst Case"

Introduction
"
`.ret` is what the algorithm computes. `.time` is what it cost.

Insertion sort's cost depends on the input, not only its size. On an already-sorted list every
insertion stops at the first comparison, so sorting `n` elements costs `n - 1`. On a
reverse-sorted list every insertion walks the whole prefix, so the cost grows quadratically.

Both lists below have four elements. Show that the second costs strictly more than the first.

This is the observation that makes a cost model worth having: it distinguishes inputs that an
`O(·)` statement about the worst case does not.
"

/--
`timedSort_cost_differs : (timedSort [1,2,3,4]).time < (timedSort [4,3,2,1]).time`

Insertion sort's comparison count depends on the input, not only on its length.
-/
TheoremDoc timedSort_cost_differs as "timedSort_cost_differs" in "Algorithms & Data"

/-- Show that the cost-annotated sort charges strictly more for a reverse-sorted list than
for an already-sorted list of the same length. -/
Statement timedSort_cost_differs :
    (timedSort [1,2,3,4]).time < (timedSort [4,3,2,1]).time := by
  Hint "Both costs are concrete numbers, so this is a computation: `decide`."
  decide

Conclusion
"
Three comparisons against six.

Keep the two fields apart in your head, because they behave very differently under the
reasoning that follows. `.ret` is the answer, and the answer does not depend on the
instrumentation — which is exactly what the next level turns into a theorem. `.time` is the
instrumentation, and nothing about the plain algorithm can tell you anything about it.

That asymmetry is the shape of the rest of this world: one obligation that transfers for free,
and one that has to be proved where it lives.
"

TheoremTab "Algorithms & Data"
