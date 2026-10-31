import Game.Levels.Refinement.L10_ChoosingTheRightRelation

World "Refinement"
Title "Refinement and Behavioral Equivalence"

Introduction
"
*Optional branch.* You can finish the core path without this world, and nothing later depends
on it. It is here because the question it asks comes up constantly in practice: **may I
replace this component with that one?**

Sometimes the honest answer is *yes, they compute the same thing* — but only on inputs that
satisfy some condition. Sometimes it is *the replacement is safer, and that is a different
claim from behaving the same*. Sometimes the two systems do not even have the same notion of
state, and the only thing you can compare is what an outside observer sees. And sometimes the
implementation does internal work that no observer can see at all, and the right notion of
equivalence has to ignore it.

So this world is about choosing the right relation: conditional equivalence, trace inclusion,
one-way simulation, bisimulation, and weak bisimulation. They are not interchangeable, and
picking the wrong one is how people end up proving something true that does not mean what they
wanted. You will see a pair of systems that are related in one direction and provably not in
the other, and a pair that offer an observer identical behavior and are still not
interchangeable.

A caution before you start. These are statements about the Lean models written here, and about
nothing else. A proof that this list-based stack refines this counter is not a proof about any
C or Rust program, and a model in which a bad operation simply has no transition says nothing
about what a real language does when a program performs one.
"

/- No world `Image`: it would sit behind every level of the world, and the simulation square
only belongs to Levels 4–9. The figure is embedded, localised, in the Level 4 introduction. -/
