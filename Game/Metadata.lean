import GameServer
import Game.Machines
import Game.Doc.Tactics
import Game.Doc.Definitions
import Game.Doc.Theorems

/-!
Everything that should be available in every level of the game.

Keeping the imports here means a level file contains only its own exercise, and that the
inventory documentation is declared once rather than repeated per level.
-/

open Cslib
open Cslib.Algorithms.Lean (TimeM)
