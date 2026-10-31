import Game.Levels.Verification.L12_ABoundOnTheComparisons

World "Verification"
Title "Verify a Complete Implementation"

Introduction
"
Everything so far has been one technique at a time. This world puts them together on one
algorithm, and follows it all the way through.

It starts with the contract, because that is where verification starts: what does *sorted*
mean, and why is it not enough on its own? Two degenerate programs will show you that it takes
two obligations to say *sorting*.

Then insertion sort, twice. First a version you write and prove yourself, so that every step
of the argument is visible. Then CSlib's `List.insertionSortM`, which is written over a monad
so that the same code can run plainly or with its comparisons counted — and which you will
relate to Mathlib's ordinary sort by a general theorem about monad homomorphisms, getting both
correctness obligations for almost nothing.

The world ends where that shortcut runs out. Cost is exactly the information the shortcut
discards, so a bound on the number of comparisons has to be proved from first principles, in
the cost monad, by an induction of your own. Cost here is something you *model* and prove
about, never something measured.
"
