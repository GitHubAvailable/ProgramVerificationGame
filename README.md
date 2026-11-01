# Introduction to Program Verification

A [Lean 4 Game Server](https://github.com/leanprover-community/lean4game) game that teaches
program verification using [CSlib](https://github.com/leanprover/cslib) abstractions.

Players model programs as state machines, learn to write specifications that describe intended
behavior, prove invariants across executions, and verify a complete sorting implementation. An
optional branch covers refinement, simulation and bisimulation.

Playable in **English** and **Simplified Chinese**.

## Audience and prerequisites

Programmers comfortable with functions, branches, recursion and lists. **No** prior
formal-methods, automata or CSlib knowledge is assumed. Some basic Lean tactic experience
helps — `intro`, `exact`, `rw`, `simp`, and elementary induction. The curriculum is specified
in [`GAME_DESIGN.md`](GAME_DESIGN.md).

## The world tree

```
Behavior ──▶ Specification ──▶ Properties ──┬──▶ Verification   (core capstone)
                                            └──▶ Refinement     (optional branch)
```

The core path is Behavior → Specification → Properties → Verification. Refinement opens as
soon as transition systems have been taught in Properties, and nothing in the core path
depends on it.

**48 levels**: 8 in Behavior, 8 in Specification, 10 in Properties, 12 in Verification and 10
in Refinement. The edges above are the ones `MakeGame` generates, which is not quite the same
thing as the ones `Game.lean` declares — `MakeGame` also derives an edge whenever a level uses
an inventory item introduced in another world, so introducing an elementary tactic late can
silently reroute the tree. `python3 test/check_game.py` compares the generated graph against
the intended one.

## Dependencies

Pinned to Lean **v4.35.0**, the newest release for which the Game Server, CSlib and Mathlib
all publish a matching tag. Exact revisions are in [`lake-manifest.json`](lake-manifest.json);
`lake build` resolves from that manifest and never re-resolves, so builds are reproducible.

| component | version |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.35.0` |
| GameServer (lean4game) | tag `v4.35.0` |
| CSlib | tag `v4.35.0` |
| Mathlib | tag `v4.35.0` (via CSlib) |

CSlib has no build cache, but only the modules this game imports are built. Mathlib comes from
the public cache.

## Build

```bash
git clone https://github.com/GitHubAvailable/ProgramVerificationGame ProgramVerificationGame
cd ProgramVerificationGame
lake exe cache get      # fetch the Mathlib cache (~7 GB); skip and it will build from source
lake build
```

`lake build` runs the `MakeGame` command, which reports inventory and dependency problems as
warnings, and regenerates `.i18n/en/Game.pot`.

A clean build still prints 18 warnings of the form *No world introducing `X`, but required by
`World`*. `MakeGame` counts every name in a reference proof as a required inventory item, and
these are ordinary names nobody documents: `List`, `Unit`, `id`, constructors such as
`Light.broken`. They do not affect play. A **new** one after an edit is worth a look: it
usually means a `DefinitionDoc` was written but the level that should introduce it has no
`NewDefinition`, so the entry never appears in the inventory.

Do **not** run `lake update` unless you intend to move the pins: it re-resolves the manifest.

## Play locally

The Game Server client is a separate repository that must sit **next to** this one:

```bash
cd ..
git clone --branch v4.35.0 https://github.com/leanprover-community/lean4game.git
cd lean4game
npm install
npm start
```

Then open <http://localhost:3000/#/g/local/ProgramVerificationGame>.

After editing any Lean file, run `lake build` in this repository and reload the browser.

**Restart `npm start` after a `lake build` that changes level files.** The server keeps the
game it loaded at startup; against rebuilt game data it serves a level with no title, an empty
inventory and *Waiting for Lean server to start…* that never resolves. A reload does not fix
it — the server process has to come back up.

### Choosing the language

Use *Menu* (☰) → *Preferences* → language, or append `?lang=zh` to the URL. English is the
source language; `zh` is a complete translation of all player-facing text.

## Tests

```bash
# Everything that does not need a browser: the build and its MakeGame diagnostics, the
# axioms behind every reference solution, the world tree and inventory, the shortcut audit,
# and translation integrity. Writes one log per check under test/results/.
bash test/run_checks.sh

# In-game test: plays every level in Chromium against a locally running server
pip install playwright && playwright install chromium
python3 test/play_levels.py          # requires `npm start` from ../lean4game

# Inventory documentation as the player sees it, in each language
python3 test/check_inventory_docs.py
```

The individual checks can also be run on their own: `python3 test/check_axioms.py`,
`python3 test/check_game.py`, `python3 test/check_names.py`, `lake env lean test/Shortcuts.lean`,
`python3 .i18n/tools/check_i18n.py`.

`test/extract_proofs.py` derives each level's player-facing proof from its Lean source by
stripping the `Hint` tactics; `test/play_levels.py` types exactly that into the in-game editor,
so a pass means the level is completable with what the player actually has — something
`lake build` cannot show.

`test/check_inventory_docs.py` opens an inventory entry in each language and records the
documentation panel, which is the only place a `TacticDoc`/`TheoremDoc`/`DefinitionDoc` body
is visible — neither the build nor the generated game data shows it.

Results land in `test/results/`: one log per offline check, screenshots of every level and
of both languages at desktop and mobile width, and JSON recording for each level what was
pasted, the statement the page displayed, and the inventory the player had. Every log opens
with the toolchain, the resolved dependency revisions and a digest of the game sources, so it
can be matched to the tree it describes. The folder is regenerated by every run and is not
tracked. On GitHub, both workflows run `test/run_checks.sh` and write its logs to the run's
summary page rather than uploading them: the Game Server imports a repository's newest
artifact whatever its name, so the built game must stay the only artifact.

## Translation

The pipeline follows the Game Server's
[guide for maintainers](https://github.com/leanprover-community/lean4game/blob/main/doc/translation-guide-for-game-maintainers.md):

1. `lake build` regenerates `.i18n/en/Game.pot`.
2. Translators work on `.i18n/<lang>/Game.po`, with `.i18n/en/glossary.csv` as the term list
   and `.i18n/zh/glossary.csv` as the agreed renderings.
3. `lake exe i18n --export-json` writes `.i18n/<lang>/Game.json`, which the server reads.
4. `python3 .i18n/tools/check_i18n.py` verifies coverage, `§n` placeholder integrity,
   Markdown structure, and that every image a translation points at exists.

When English source text changes, its `msgid` changes with it and the old translation no
longer matches. `python3 .i18n/tools/merge_po.py zh` carries every unchanged translation
across to the regenerated template and leaves the changed strings empty, listing them so a
translator sees exactly what needs work. `--fill fills.json` supplies translations for the
changed strings in the same commit that changes them.

Only player-facing text is translated. Code, identifiers, and all repository documentation
stay in English.

### Authoring constraints worth knowing

Every tactic and theorem a reference proof types must be declared visibly in the level
(`NewTactic` / `NewTheorem`) and documented (`TacticDoc` / `TheoremDoc`). `test/Shortcuts.lean`
and `test/play_levels.py` between them catch violations: the first checks that automation does
not trivialise a level, the second that the level is completable with the inventory the player
actually has.

Every `TheoremDoc` and `DefinitionDoc` names its inventory tab with `in "…"`. Both use the same
five tabs — *States & Transitions*, *Specifications*, *Invariants*, *Algorithms & Data*,
*Refinement & Equivalence* — so a concept and the facts about it are filed together; a new
topic gets a new tab rather than a new item in an unrelated one. Tab names are shown as
written in every language. Each level picks its theorem tab with `TheoremTab`; there is no
equivalent for definitions, whose tab opens on the category of the alphabetically first entry.

### Localised diagrams

An image written as Markdown inside a translatable string — a world or level `Introduction`,
a `Statement` docstring, a `Hint`, a `Conclusion` — carries its path into the `msgid`, so the
Chinese text can point at `images/zh/…` instead of `images/en/…`. This is verified by
`test/play_levels.py`, which records the asset each locale actually requests.

The world-level `Image "…"` command is **not** translatable: its path is written straight into
the generated game data and never reaches `Game.pot`. Use it only for assets with no words in
them.

## Images

All diagrams in `images/` are original SVGs written for this game and are covered by the
repository's licence. Text-bearing diagrams ship as `images/en/…` and `images/zh/…` pairs with
identical geometry.

The landing-page cover, `images/cover.png`, was created for this game with the help of AI
image tools and is not based on any existing image. It is distributed under the repository's
licence.

## Publishing

Play online at <https://adam.math.hhu.de/#/g/GitHubAvailable/ProgramVerificationGame>.

To publish a new version, follow the Game Server's
[publishing guide](https://github.com/leanprover-community/lean4game/blob/main/doc/publish_game.md):
push to this public GitHub repository, let `.github/workflows/build.yml` build the game
artifact (it also runs `test/run_checks.sh`), then open
`https://adam.math.hhu.de/import/trigger/GitHubAvailable/ProgramVerificationGame` in a browser
to import it. Nothing in this repository performs the import by itself.

The import URL is written as code rather than a link on purpose: opening it starts an import,
and a clickable link invites crawlers and link previews to do that.

## Troubleshooting

* **`lake build` starts compiling Mathlib from source** — the cache was not fetched. Abort and
  run `lake exe cache get`, or `lake exe cache get!` to invalidate a damaged cache.
* **`unknown module prefix 'Cslib'`** — the CSlib modules have not been built yet. Run
  `lake build`.
* **`version? is not a field of structure Dependency`** — the `lakefile.lean` is an older
  GameSkeleton copy. Lake 4.35 renamed that field to `version : InputVer`.
* **A level says a tactic is locked** — it is introduced in a world that is not on the current
  branch. `python3 test/check_game.py` prints the per-level inventory and the world tree.
* **A level's proof elaborates, the info view says *No goals*, and the level still does not
  complete** — the proof mentions a name the level has not unlocked. The Game Server reports
  that as an ordinary message rather than as a failed proof, so it is easy to miss. Note that
  `NewHiddenTactic` does **not** help: in this release a hidden item is dropped from the
  inventory entirely, so a reference proof may only use tactics declared with `NewTactic`.
  The check also reads induction case labels: `| refl =>` mentions Mathlib's `refl` lemma, and
  `case`/`next`/`first` are read as tactic names.
* **The local game shows an old version** — run `lake build`, then hard-reload the browser.
  If the level comes up titled `Level 1 / undefined` with an empty inventory and
  *Waiting for Lean server to start…*, the server is holding game data from before the build:
  restart `npm start`.
* **`model is disposed` after quickly moving between levels** (Next → Previous → Next) in a
  local `npm start` — a race in the Game Server's client, not in this game: leaving a level
  disposes its editor while the next one is still starting, and development mode runs each
  setup twice, which makes it likely. Reloading may not clear it; opening the same link in a
  new tab does.

## Acknowledgements

The initial implementation was developed with the assistance of [Argus](https://argusbot.cn),
an AI agent framework.

## Licence

See [`LICENSE`](LICENSE).
