# CSlib Game -- Game Design Specification

**Version:** 1.0
**Status:** Approved curriculum baseline; concrete exercises and module paths remain to be validated
**Working title:** Introduction to Program Verification

## 1. Mission and learning outcomes

Build an accessible, interactive **Lean 4 game using CSlib APIs** that teaches programmers how to specify and verify software. The goal is to help learners move from reasoning about state and execution to writing specifications, proving invariants, and verifying a complete implementation. An optional advanced path introduces relationships *between* implementations, including refinement and behavioral equivalence.

By the end of the **core path**, a learner should be able to:

1. Model simple computations with states, transitions, and reachable states.
2. State meaningful preconditions and postconditions; distinguish a correct specification from an incorrect or incomplete one.
3. Use induction, invariant preservation, supporting lemmas, and modular reasoning to prove program properties.
4. Prove that a nontrivial Lean implementation satisfies a multi-part specification, leveraging actual CSlib abstractions or implementations.
5. Explain where CSlib reduces duplicated proof engineering compared with starting from ordinary Lean alone.

After the **optional advanced path**, a learner should distinguish conditional functional equivalence, trace inclusion/refinement, simulation, bisimulation, and (when the APIs support it) abstraction of internal steps.

**Scope:** an educational game, not the creation of a new general-purpose verifier, Hoare-logic library, memory model, C/Rust translator, or research result.

## 2. Audience and pedagogical assumptions

- Learners understand ordinary programming concepts (functions, branches, recursion, lists); they need **no prior formal-methods, automata, or CSlib knowledge**.
- Assume basic Lean tactic experience (e.g., `intro`, `exact`, `rw`, `simp`, and elementary induction). Provide a concise refresher/links and in-game reminders as needed rather than duplicating an entire beginner Lean game.
- Introduce each unfamiliar CS concept and CSlib abstraction **before** requiring learners to use it independently.
- Do not assume access to Rust, C, C++, operating-systems knowledge, or external proof assistants.
- Use English as the source language and provide a complete Simplified Chinese (`zh`) translation of all player-facing content (see Section 6). Other repository documentation and development materials remain in English.

## 3. Curriculum and initial world tree

The five **content groups** below are required curricular coverage, not necessarily five distinct Game Server **world nodes**. A content group is a thematic obligation; a world is a playable node in the dependency tree; a level is one playable exercise. Content Group 5 is **optional for learners but mandatory to implement, translate, and test to the same standards as the core content**.

```text
World 1 -- Understand Program Behavior (core)
  |
World 2 -- Specify Correct Behavior (core)
  |
World 3 -- Prove and Reuse Properties (core)
  |                         \
  |                          \-- World 5 -- Refinement and Behavioral Equivalence (optional path)
  |
World 4 -- Verify a Complete Implementation (core capstone)
```

The optional branch should unlock once its **actual prerequisites** are covered, ordinarily after the content taught in initial World 3. Do not force learners to finish World 4 or complexity-analysis material to access World 5 unless a concrete prerequisite genuinely requires it. Check that the implemented Game Server dependency graph matches the intended progression.

### Level targets and hard minimums

| Required content group (initially one world each) | Target | Hard minimum | Core / optional to learner |
|---|---:|---:|---|
| Content Group 1 -- Understand Program Behavior | 7 | 6 | Core |
| Content Group 2 -- Specify Correct Behavior | 7 | 6 | Core |
| Content Group 3 -- Prove and Reuse Properties | 10 | 8 | Core |
| Content Group 4 -- Verify a Complete Implementation | 12 | 10 | Core |
| Content Group 5 -- Refinement and Behavioral Equivalence | 9 | 7 | Optional |
| **Total** | **45** | **37** | **All five groups must be implemented** |

These are **meaningful, unique, playable, completable** levels, not file counts or superficial variants. Aim for the targets; do not drop below any group minimum without explicit owner authorization. If a group is split into several worlds, its **combined** number of levels still meets its original minimum, and all mandatory topics remain present.

### Content Group 1 -- Understand Program Behavior (initial World 1)

**Learning goal:** What are states, transitions, executions, and reachability?

**Required coverage:**

- A small, intuitive deterministic automaton (e.g., parity of `1`s in a binary string) as the introductory example, not a full theory-of-computation course.
- State/transition definitions, running an input, simple reachability or unreachability.
- At least one general property over executions/accepted inputs rather than only evaluating specific examples.
- A clear bridge from abstract automata to **state transformations** in programs.

**CSlib role:** Use actual deterministic automata and/or labeled transition system (LTS) definitions if available and appropriate. Avoid overwhelming beginners with the full generality of an abstract type before an example is understandable.

### Content Group 2 -- Specify Correct Behavior (initial World 2)

**Learning goal:** How do we say what an implementation must do?

**Required coverage:**

- Predicates, preconditions, postconditions, input/output relationships.
- Boundary cases and why assumptions matter.
- A counterexample to an **incorrect** proposed specification; distinguish too-weak and too-strong specifications when pedagogically suitable.
- Prove correctness of simple Lean functions by expressing contracts as ordinary propositions.
- Clarify that `P x → Q x (f x)` is a useful specification pattern and that formal Hoare triples are **not necessary** for pure Lean functions.

**CSlib role:** Ordinary Lean is acceptable here; no forced or decorative CSlib dependency.

### Content Group 3 -- Prove and Reuse Properties (initial World 3)

**Learning goal:** How do proofs scale beyond one-off examples?

**Required coverage:**

- Nontrivial induction on a recursive function or data structure.
- An invariant and proof that one transition preserves it.
- Reuse a general CSlib LTS theorem to obtain a multistep safety/invariant result.
- A data-structure invariant and/or a modular helper lemma reused in a larger proof.
- Basic **functional equivalence** between two ordinary Lean functions, under an appropriate input condition if relevant.
- At least one explicit learning sequence comparing a manual/specialized argument with a reusable CSlib-based proof.

**CSlib role:** Genuine use of available LTS/invariant abstractions and reusable theorems, with exact API names checked against the pinned version rather than assumed from this document.

### Content Group 4 -- Verify a Complete Implementation (initial World 4)

**Learning goal:** Complete a realistic, multi-obligation program-verification task.

**Required coverage:**

- An actual (possibly pedagogically simplified) CSlib algorithm, data structure, or verification abstraction as the backbone of a **connected capstone case study**.
- Explain and formalize the specification before presenting its final proof.
- Supporting lemmas, compositional reasoning, and an implementation-correctness theorem requiring multiple previously learned techniques.
- At least two meaningfully distinct correctness obligations (for example, sortedness **and** permutation preservation, or functional result **and** invariant preservation).
- A final challenge that is not solved by a single invocation of an existing CSlib theorem whose statement is the entire target.
- Include computational-cost reasoning with `TimeM` **if compatible and pedagogically sound**; otherwise select another substantive CSlib-backed property and document why `TimeM` was deferred. Cost annotations must be presented as a model, not automatically measured runtime.

**Candidate:** a small sorting algorithm or data structure, selected only after API and prerequisite inspection. A complete formalization of the existing CSlib merge-sort proof is **not** required; students may prove a simplified but meaningful theorem about a CSlib component.

**CSlib role:** Depend on concrete CSlib algorithms or abstractions and show their practical benefit rather than merely importing the package.

### Content Group 5 -- Refinement and Behavioral Equivalence (initial World 5; optional path)

**Learning goal:** Choose and establish useful relationships between two implementations or two behavioral models, even when they are not literally identical.

**Required coverage:**

- Conditional functional equivalence on a specified valid input domain.
- A checked/total replacement for a partial operation, distinguishing **behavior preservation under a precondition** from an **independent safety property**.
- Trace inclusion / behavioral refinement and its direction: implementation behaviors are contained in specification-permitted behaviors, under a stated observation model.
- One-way simulation, and an example showing why one-way simulation need not imply bisimulation.
- Bisimulation with a relation between different state representations.
- Where supported, internal/unobservable steps and weak bisimulation; if unavailable, teach the concept via a suitably explicit model, without claiming nonexistent APIs.
- A culminating level where students choose a suitable relation rather than being told to prove equivalence blindly.

**CSlib role:** Use genuine LTS trace, simulation, and bisimulation infrastructure where supported by the pinned library.

**Important semantic caveats:**

- Do not claim actual C/Rust program equivalence or memory safety has been proved by a toy Lean example.
- A C out-of-bounds read has **undefined behavior**, not a normal error return that may be compared like an ordinary result.
- Simulation, trace inclusion, safety, termination, and bisimulation have different meanings; use the correct observation model and assumptions.
- Real cross-language migration is motivation only; this game does not require C/Rust translation or low-level semantics.

## 4. Cross-world coherence

- Prefer a few recurring examples to show how ideas grow (e.g., a small state machine, a stateful counter/queue, and a simple verified list algorithm).
- Do **not** force the same example into every world. Replace it where doing so improves clarity.
- Make the transition from World 1's operational models to Worlds 2–4's proof of ordinary Lean functions explicit. State machines are useful models, **not prerequisites** for verifying all pure Lean functions.
- World 3 should explicitly bridge stateful invariant proofs and functional proofs; World 4 should integrate previous techniques.
- Emphasize not only *how* to use CSlib, but *why*: reusable domain-specific specifications, general theorems, existing verified components, and cost models.

### Visual aids and diagrams

- Add **educationally useful diagrams** when they materially clarify a state machine, execution/reachability relation, invariant, algorithm, data structure, or relationship between systems. Prioritize Content Groups **1 (Program Behavior)** and **5 (Refinement and Behavioral Equivalence)**; diagrams in Groups 2–4 are optional where text or code is clearer.
- No image count or per-level image requirement. Avoid decorative graphics, redundant figures, and diagrams that replace rather than explain a proof obligation. Diagrams must have accurate labels, sensible layout, and a concise textual explanation so exercises remain understandable without the image.
- Prefer small, maintainable, mathematically precise diagrams, especially SVG **when supported by the pinned Game Server**. Use original assets or assets with appropriate licenses and attribution. Store assets in the game repository; use supported Game Server image/Markdown mechanisms rather than fragile external links.
- Prefer **language-neutral diagrams** (symbols, small state labels, formulas) where feasible. If meaningful text is embedded in an image, provide **English and Simplified Chinese (`zh`) variants** rather than leaving English-only labels in the Chinese experience.
- For localized image variants, prefer translatable Markdown image references with per-language asset paths **only after checking that this works with the pinned Game Server/i18n version**. A possible layout is `images/en/...` and `images/zh/...`; these are conventions, not guaranteed magic paths. Do not assume that a world-level `Image` declaration automatically chooses a language-specific file.
- Translate captions, Markdown alt text, and descriptions; preserve valid asset references and translation placeholders. Verify **actual English and `zh` rendering** of localized figures, including in the optional branch. If image swapping is unsupported, choose a documented compatible fallback (such as a language-neutral diagram plus localized surrounding text) and record the limitation.

## 5. Inventory design: theorems, definitions, and tactics

The Game Server presents a **cumulative inventory** of unlocked tactics, theorems, and definitions in both the world-selection view and individual levels. The inventory is a navigable learning reference, **not** a list of every declaration imported by Lean/CSlib.

**Selection and documentation**

- **Essential:** show and explain concepts or tools explicitly introduced or used for educational objectives, especially reusable CSlib interfaces.
- **Supporting:** include general lemmas students are likely to reuse in later levels; avoid redundant synonyms and low-value helpers.
- **Internal:** do not clutter the inventory with incidental implementation helpers, deeply internal declarations, or APIs learners are not expected to use directly.
- Give each displayed item an accurate English and Simplified Chinese description, its relevant formal statement/signature, and a brief explanation or example of when it helps. For related tactic variants, document them under the principal tactic where appropriate; hiding a tactic does not automatically document it.
- Introduce items at their first relevant learning step. Unlocks should be **cumulative along the actual dependency paths**, without re-declaring the entire inventory for every level. Audit optional branches independently; never assume one branch has unlocked items from another branch.
- Prefer presenting interfaces and reusable lemmas to repeatedly unfolding CSlib's underlying implementations. Include at least two exercises that illustrate the savings from a CSlib theorem or abstraction compared with a manual approach.

**Organization**

- Organize **theorems** into stable, thematic tabs as the inventory grows (for example: Logic, States & Transitions, Specifications, Invariants, Algorithms & Data, Refinement & Equivalence). These are illustrative, not required empty tabs; avoid excessive fragmentation and select helpful default tabs for relevant levels.
- Keep **definitions** curated and understandable; explain their purpose and relationship rather than exposing every internal declaration. Group them under the same thematic tabs as theorems (`DefinitionDoc … in "<tab>"`), so a concept and the facts about it share a name; add a tab only when a new topic (for example, Hoare or separation logic) needs one. The pinned Game Server has no per-level `DefinitionTab`: the Definitions tab opens on the category of the alphabetically first entry, and the "new" marker shows the player where newly unlocked definitions are.
- Keep **tactics** in a compact list rather than creating artificial categories. Closely related variants (e.g., `rw`, `rwa`, `nth_rewrite`) may be usable via hidden-tactic entries while explained together under a visible `rw` entry. Distinct proof methods deserve distinct descriptions.

**Tool access, automation, and educational freedom**

- Use gradual introduction and later reuse. Do not impose full per-level allowlists or gratuitous restrictions; level-specific `Only*` / `Disabled*` controls are exceptions with a stated teaching purpose.
- Guided early exercises may temporarily restrict a tactic or theorem that defeats their primary goal. Later levels should increasingly allow normal Lean proof style, including `simp`, `omega`, `aesop`, or `grind` where compatible and educationally appropriate.
- Automation is **encouraged for routine subgoals**, but should not eliminate the one concept the level is designed to teach. Audit obvious one-line shortcuts, pre-existing imported results, and helper lemmas that would make flagship exercises trivial. Do not ban an otherwise valid proof merely for differing from the intended script.
- Check that each reference proof uses **only what is actually available** in the player's inventory and branch, and that documented items/unlock timing match the real game behavior. Formal availability and inventory display may differ; test the actual player environment.

## 6. Localization and language policy

- **English (`en`) is the source language** for gameplay text, code, identifiers, repository documentation, contribution guides, development notes, and implementation reports.
- Provide a **complete Simplified Chinese (`zh`) translation** of *all player-facing material*, including game/world/level titles and introductions, natural-language exercise descriptions, hints, conclusions, inventory names/descriptions, and other localized player UI strings controlled by the game. The optional advanced content group is **equally required** to be translated.
- Follow the Lean Game Server's established localization pipeline and the Robo translation-guide conventions, using the `zh` locale (not assuming separate `zh_CN`/`zh_TW` support). Maintain `.i18n/zh/Game.po`, a curated glossary such as `.i18n/zh/glossary.csv`, and the generated runtime translations as required by the pinned Game Server version.
- Preserve verbatim Lean code, declarations, tactic syntax, mathematical notation, LaTeX, formatting, references, and **translation placeholders** such as `§0`, `§1`, etc. Keep placeholder order/meaning and line breaks correct; do not translate or corrupt code snippets.
- Translate terminology consistently (e.g., state, invariant, specification, refinement, simulation, bisimulation). Make the wording instructional and natural, not literal at the expense of correctness. Machine assistance is permitted, but translations require careful review.
- Localize image-associated labels, captions, alt text, and explanations; where a figure requires language-specific artwork, use the verified language-specific asset mechanism described under Visual aids and diagrams. Test image selection separately from ordinary text translation.
- Validate completeness, placeholder integrity, export/build, UI rendering, and navigation in **both English and `zh`**, covering all worlds and levels, inventory tabs, hints, and optional content. Record untranslated or untestable strings as failures/limitations, not successful localization.
- Traditional Chinese is not required for the initial release and may be added later without altering the English source or `zh` content.

## 7. Level design contract

Each level must have:

1. **One primary, explicit learning objective**, plus listed prerequisites.
2. A concrete example/context and a short, accurate introduction.
3. A precise Lean exercise whose proposition matches the described lesson.
4. A valid, kernel-checked reference proof using tools actually available to the learner.
5. Appropriate hints (preferably escalating from conceptual to tactical), usable in the game's actual proof state.
6. A conclusion explaining what was proved and why it matters.
7. A justified difficulty step: what is **new** compared with its prerequisites.
8. Exact CSlib declarations used, where relevant; avoid unused imports masquerading as integration.
9. A traceable record of the level's implementation, available inventory, tested reference solution, and translation status, maintained with the game.

**No fake levels:** A change in variable names, small constants, or cosmetic notation does not constitute a distinct level. Repetition is acceptable when it teaches transfer to a genuinely different structure, introduces a new lemma, or removes scaffolding in a purposeful way.

**Avoid proof spoilers:** Do not give the entire proof away in introductory text or the first hint. Learners must solve genuine goals. Where a level is meant to illustrate a reusable theorem, show its applicability rather than hiding all learning behind `exact`.

**Maintain accessibility:** Prefer small proof obligations building toward substantial ones. If a level requires several unintroduced ideas, add intermediate instruction and levels. Provide a clear vocabulary for technical terms.

## 8. Allowed curriculum expansion and world splitting

**Adding levels is encouraged** when it repairs a prerequisite gap, introduces a necessary technique, builds a substantively different application, or combines prior techniques at greater depth. The target is **not a ceiling**.

- Each added level must state its new learning value relative to adjacent levels and have the same proof/test standards as original levels.
- Maintain an increasing challenge with appropriately reduced scaffolding; do not multiply elementary examples to inflate counts.
- Expansion is welcome when it improves learning, not merely the count. Implementers may add levels within the project owner's agreed scope and autonomy limits; larger expansions and changes to hard minima require explicit owner approval.
- Contributors may split or reorder worlds if a coherent, independently teachable concept cluster has approximately **four or more meaningful levels** and the split improves the dependency structure. The Game Server guide notes that worlds above approximately 16 levels may become awkward to display; do not split solely to reach a cosmetic level count.
- An independent world branch must unlock after its *real* prerequisites only, and must not inadvertently block the core capstone or the optional advanced path.
- Splits do **not** reset level minimums: retain all five topic-group requirements in aggregate. Do not silently reclassify core content as optional.
- Keep the agreed requirements intact; document implemented structural changes, the new dependency tree, and rationale in a maintained curriculum record (for example `docs/IMPLEMENTED_CURRICULUM.md`).

If a proposed restructure materially changes learning goals, required coverage, minimum counts, or core/optional status, seek owner approval. Routine level additions/splits satisfying the above rules need no approval.

## 9. Objective quality gates

A game is not complete merely because a Lean compilation succeeds.

**Coverage gates**

- Every required topic in Section 3 has a concrete implemented level or connected sequence.
- At least **two** sequences visibly demonstrate a CSlib advantage over a manual/special-case proof.
- Every group's hard minimum is met with *distinct* qualifying levels.
- The core capstone proves multiple meaningful obligations, and optional-for-learners Content Group 5 is fully implemented, translated, and tested, not deferred.

**Correctness gates**

- Every level's theorem is correctly stated and has a complete, checkable reference proof; no proof holes, extra unsound axioms, or unapproved shortcuts in reference solutions.
- Exercises use CSlib APIs from the pinned dependency revision, with exact module/declaration paths recorded.
- No silently weakened properties: if a theorem is changed to avoid a hard proof, document the change and verify that the original learning objective is preserved; otherwise request approval.

**Inventory and localization gates**

- The cumulative inventory is discoverable in the world-selection view and during levels, with theorem categories, useful documentation, consistent unlock behavior, and no essential missing tools on the optional branch.
- All player-facing text is provided in both English and Simplified Chinese (`zh`), including optional content and curated inventory entries; terminology/placeholder correctness is checked.
- Educational diagrams render correctly with understandable captions/text alternatives; any localized images select the correct English/`zh` asset (or a verified language-neutral fallback), including in optional content.
- Relevant restrictions and prominent automation shortcuts are audited for their educational effect, without unnecessarily limiting standard Lean proof methods.

**Game-experience gates**

- The actual world dependency tree and cumulative player inventory (tactics, theorems, definitions) are coherent in the world-selection view and in each playable level.
- All reference proofs succeed under the **same player-visible statements and available tools**, via genuine in-game tests or a demonstrably equivalent player-side harness; build-only checks are insufficient.
- Hints and explanations describe the actual goal, not a different or obsolete theorem.
- A learner can finish the core path without first completing optional content, and can complete the entire optional path after its actual prerequisites. All content groups have the same proof, playability, translation, and test requirements.
- Where feasible, solicit beginner feedback; if unavailable, mark educational usability as *not human-validated*, rather than asserting otherwise.

## 10. Deferred / out-of-scope topics

Do not require these in the initial release: new foundational Hoare/separation logic, imperative-language VC generation with Boole, pointer-level memory semantics, concurrency proof infrastructure, verified compiler translations, Rust/C/C++ source verification, or new CSlib internals. These can become **later worlds** if the underlying APIs mature and the educational use case is compelling.

## 11. Source-of-truth references

These are **research starting points**, not guarantees that particular declarations or commands exist in a future revision. Implementers must inspect the pinned, installed source and verify claims.

- CSlib repository: https://github.com/leanprover/cslib
- CSlib website/API docs: https://www.cslib.io/ and https://api.cslib.io/
- Lean Game Server authoring: https://github.com/leanprover-community/lean4game/blob/main/doc/create_game.md
- Local testing: https://github.com/leanprover-community/lean4game/blob/main/doc/running_locally.md
- GameSkeleton: https://github.com/hhu-adam/GameSkeleton
- Game publishing: https://github.com/leanprover-community/lean4game/blob/main/doc/publish_game.md
- Game development guidance: https://github.com/leanprover-community/lean4game/blob/main/doc/create_game.md
- Robo translation guide: https://github.com/hhu-adam/Robo/blob/main/docs/TranslationGuide.md

**Priority:** The educational requirements and scope restrictions in this file are authoritative for the project, regardless of the implementation agent. Exact examples, verified API names, and reasonable world splits are implementation decisions subject to the rules above.
