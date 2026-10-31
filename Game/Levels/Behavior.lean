import Game.Levels.Behavior.L08_TheMachineInsideTheProgram

World "Behavior"
Title "Understand Program Behavior"

Introduction
"
Before you can say what a program *should* do, you need a way to say what it *does*.

This world introduces the vocabulary: **states**, **transitions**, **runs**, **reachability**
and **invariants**. We work with a deterministic automaton from CSlib, small enough to hold in
your head, and build up from running it on one word to proving properties that hold for every
possible input — and for a second machine, properties that hold for every possible run.

The machine here reads bits and tracks parity. It is a toy, but the move you make in this
world is the one you will make for the rest of the game: replace *I ran it and it looked
right* with *here is an argument covering all runs*.

The last level is the bridge. A state machine is a model of a program, not a replacement for
one, and World 2 onwards proves things about ordinary Lean functions.
"

/- The world picture uses the language-neutral variant on purpose: a world-level `Image`
path is written straight into the generated game data and never reaches `Game.pot`, so it
cannot follow the player's language. Its labels are Lean values and identifiers, which stay
in English in every locale. The `en`/`zh` variants of this figure are embedded as Markdown
inside the level introduction, where they *are* translatable. -/
Image "images/parity-automaton.svg"
