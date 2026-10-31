import Game.Levels.Specification.L08_ContractsThatCompose

World "Specification"
Title "Specify Correct Behavior"

Introduction
"
You can now describe what a program does. This world is about saying what it *should* do.

A specification in Lean is an ordinary proposition: a precondition on the input, a
postcondition relating input to output, and an arrow between them. No separate program logic,
no Hoare triples — for a pure function the arrow *is* the contract.

The work is rarely in proving a contract. It is in noticing that the contract you wrote is not
the one you meant. So this world spends its time on the ways a specification goes wrong: too
weak, and it admits programs you would reject; too strong, and no program can satisfy it; and
missing an assumption, so that it is simply false.

By the end you will have seen the sharpest standard there is — a contract that pins its
implementation down completely — and the reason you do not always want it.
"
