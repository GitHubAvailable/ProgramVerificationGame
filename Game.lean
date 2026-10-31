import Game.Levels.Behavior
import Game.Levels.Specification
import Game.Levels.Properties
import Game.Levels.Verification
import Game.Levels.Refinement

open Cslib
open Cslib.Algorithms.Lean (TimeM)

Title "Introduction to Program Verification"

Introduction
"
Most programmers test. This game is about the other thing you can do: **prove**.

You will start by describing what a program *does* — states, transitions, runs — then learn to
say what it *should* do, then prove that it does. The examples stay small on purpose; the
arguments are the point, and the arguments are the ones that scale.

Along the way you will use [CSlib](https://github.com/leanprover/cslib), Lean's library of
computer-science abstractions. You will work with automata and labelled transition systems,
apply theorems to prove invariants, verify algorithm correctness, and explore simulation and
refinement. Part of the lesson is *why* a library like that is worth having — twice in the core
path you will get a theorem for nothing that would otherwise have cost you an induction.

**The core path** is Worlds 1 to 4. **World 5 is optional**: it opens once you have met
transition systems in World 3, and asks when one implementation may replace another.

No prior formal-methods, automata or CSlib knowledge is assumed. Some basic Lean tactic
experience will help: `intro`, `exact`, `rw`, `simp`, and elementary induction.
"

Info "
**Introduction to Program Verification**

An introduction to program verification in Lean 4, built on
[CSlib](https://github.com/leanprover/cslib) abstractions.

Available in English and Simplified Chinese — switch under *Menu → Preferences*.

Built with the [Lean 4 Game Server](https://github.com/leanprover-community/lean4game).
Diagrams are original and shipped with the game.
"

/-! The world tree. The core path runs Behavior → Specification → Properties → Verification.
The optional refinement branch opens off Properties, because transition systems are its only
real prerequisite — it must not be gated behind the World 4 capstone. -/
Dependency Behavior → Specification → Properties → Verification
Dependency Properties → Refinement

/-! Information to be displayed on the server's landing page. -/
Languages "en" "zh"
CaptionShort "Specify, reason about, and verify programs in Lean 4."
CaptionLong "Learn program verification with CSlib abstractions: explore state-based models,
write specifications that describe intended behavior, prove invariants that hold across executions,
and verify a complete sorting implementation. An optional branch covers refinement, simulation and
bisimulation."
CoverImage "images/cover.png"

/-! Build the game. Shows warnings if it found a problem with your game. -/
MakeGame
