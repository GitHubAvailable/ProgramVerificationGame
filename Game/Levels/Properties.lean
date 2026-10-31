import Game.Levels.Properties.L10_TheSameArgumentWithoutAMachine

World "Properties"
Title "Prove and Reuse Properties"

Introduction
"
Worlds 1 and 2 gave you one model and one contract at a time. This world is about proofs that
do not have to be redone.

The central idea is the **invariant**: a property that holds at the start and survives every
single step, and therefore holds forever. Stated that way it is a theorem about transition
systems in general, not about your program — which means somebody can prove it once and
everybody can use it. CSlib has, and you will prove the same safety property twice, once by
hand and once by appealing to it, so that the difference is visible rather than asserted.

You will also meet the other kinds of reuse: a helper lemma factored out because the larger
argument needs it, an invariant of a data structure rather than of a machine, and an
equivalence between two functions that lets you transport what you know about one onto the
other.

And you will meet the thing that makes invariant proofs hard — that the property you want is
usually not the property you can prove, and has to be strengthened first.
"
