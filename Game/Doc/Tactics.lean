import GameServer

/-!
# Tactic documentation

One entry per tactic the game introduces.

Every tactic a reference solution uses has an entry here and is unlocked with `NewTactic`.
That is not a stylistic choice: in this Game Server release a `NewHiddenTactic` item is
dropped from the inventory altogether, so the runtime check reports it as unavailable and the
level never registers as completed. A tactic the player must type is therefore always
visible.
-/

/--
`intro h` moves the assumption of an implication, or the bound variable of a `∀`, into the
context under the name `h`. Use it whenever the goal starts with `→` or `∀`.
-/
TacticDoc intro

/--
`exact e` closes the goal with the term `e`. It is the most direct way to finish a proof once
you know which theorem applies.
-/
TacticDoc exact

/--
`refine e` is `exact` with holes: write `?_` wherever you want to leave a subgoal open.
`refine ⟨?_, ?_⟩` is the usual way to split a goal `A ∧ B` while supplying structure at once.
-/
TacticDoc refine

/--
`rfl` closes a goal `a = b` when both sides compute to the same value.
-/
TacticDoc rfl

/--
`rw [h]` rewrites the goal using the equation `h`, left to right. `rw [← h]` rewrites right to
left, and `rw [h] at h'` rewrites in a hypothesis instead of the goal.

See also `rwa`, which rewrites and then closes the goal with an assumption.
-/
TacticDoc rw

/--
`simp` simplifies the goal using the library's simplification lemmas. `simp [f]` additionally
unfolds the definition `f` or uses the extra lemma `f`, and `simp at h` simplifies a hypothesis.
`simp only [h]` restricts it to exactly the lemmas you list, which is how you unfold one step
without the rest of the simp set rearranging the goal.

See also `simp_all` and `simpa`.
-/
TacticDoc simp

/--
`show t` restates the current goal as `t`, which must be definitionally equal to it. It is
useful to make an unfolding step visible, or to tell Lean how you want to read the goal.
-/
TacticDoc «show»

/--
`have h : t := by ...` proves an auxiliary fact `t` and adds it to the context as `h`. This is
how you build a proof out of lemmas you establish along the way.
-/
TacticDoc «have»

/--
`induction xs with ...` proves a goal by structural induction. Write
`induction xs generalizing s` to put `s` back under the induction hypothesis — essential when
the statement must hold for *every* starting state, not just the one you began with.
-/
TacticDoc induction

/--
`cases x with ...` splits the proof into one case per constructor of `x`. Each case can be
focused with a bullet `·`, in constructor order.

For taking apart a hypothesis rather than a value, see `rcases` and `obtain`.
-/
TacticDoc cases

/--
`constructor` applies the single constructor of the goal. For `A ∧ B` it produces the two
goals `A` and `B`.
-/
TacticDoc constructor

/--
`use a` supplies the witness `a` for a goal `∃ x, p x` and then tries to discharge what
remains. `use a, b` supplies several witnesses at once.
-/
TacticDoc use

/--
`subst h` eliminates a variable using an equation `h : x = e` (or `e = x`), replacing `x`
everywhere. Use it after inverting a transition to learn what the next state is.
-/
TacticDoc subst

/--
`omega` discharges goals about linear arithmetic over `ℕ` and `ℤ`, including `<`, `≤`, `+`,
`-` and numerals. It is meant for routine arithmetic side conditions, and it knows that
subtraction on `ℕ` truncates.

For numeric goals beyond linear arithmetic see `norm_num`; for a goal Lean can simply compute,
see `decide`.
-/
TacticDoc omega

/--
`decide` proves a goal whose truth Lean can compute outright: a statement about concrete
values, built from decidable predicates. It is how you check a worked example — and its limit
is the reason the rest of the game exists, since no computation settles a statement about
infinitely many inputs.
-/
TacticDoc decide

/--
`apply h` reduces the goal to the hypotheses of `h`. If `h : A → B` and the goal is `B`, what
remains is `A`. Use it to work backwards from the goal towards what you already know.
-/
TacticDoc apply

/--
`unfold f` replaces `f` by its definition. Useful when a contract is stated about a defined
function and the proof needs to see the branches inside it.
-/
TacticDoc unfold

/--
`split_ifs` splits a goal containing `if … then … else …` into one goal per branch, adding the
condition (or its negation) as a hypothesis in each. Pair it with `omega` when the branches
differ only arithmetically.
-/
TacticDoc split_ifs

/--
`left` and `right` choose which side of a goal `A ∨ B` you intend to prove. `left` leaves `A`;
`right` leaves `B`.
-/
TacticDoc left

/--
`right` chooses the second disjunct of a goal `A ∨ B`, leaving `B`. See also `left`.
-/
TacticDoc right

/--
`by_cases h : P` splits the proof into the case where `P` holds and the case where it does
not, naming the assumption `h` in each. Prefer it to `split_ifs` when you want the condition under
a name you choose, which is usually when the condition is what the proof turns on.
-/
TacticDoc by_cases

/--
`tauto` closes goals that are true by propositional logic alone — rearrangements of `∧`, `∨`,
`→` and `¬` over facts already in the context. It is for the bookkeeping at the end of a
`simp`, not for the mathematics.
-/
TacticDoc tauto

/--
`trivial` closes a goal that holds by definition, in particular `True`. It is what proves that
a concrete transition of a small system really is a transition, when the transition relation
was defined by a `match` returning `True`.
-/
TacticDoc trivial

/--
`ring` proves identities that hold in any commutative ring — expanding products, collecting
terms, rearranging sums. Use it for the algebraic step `omega` cannot do, such as expanding
`(n + 1) * (n + 1)`.
-/
TacticDoc ring

/--
`rwa [h]` rewrites with `h` and then closes the goal with a hypothesis from the context. It is
a rewrite and an assumption lookup in one step, and it is the usual way to finish once a
rewrite has made the goal match something you already have.
-/
TacticDoc rwa

/--
`simp_all` simplifies every hypothesis and the goal together, using each to simplify the
others. Reach for it when a case split has left several concrete facts lying around and you
want them combined; reach for plain `simp` when you know which one matters.
-/
TacticDoc simp_all

/--
`simpa using e` simplifies both the term `e` and the goal, then closes the goal with the
result. `simpa [f] using e` additionally unfolds `f`. It is the way to land on an induction
hypothesis that is almost, but not syntactically, the goal.
-/
TacticDoc simpa

/--
`norm_num` evaluates and proves numeric goals, including ones beyond the linear arithmetic
`omega` handles. Use it to discharge a concrete computation that a counterexample depends on.
-/
TacticDoc norm_num

/--
`rcases h with p` takes a hypothesis apart according to a pattern: `⟨a, b⟩` splits a
conjunction or an existential, and `h₁ | h₂` splits a disjunction into two goals. `rfl` in a
pattern position substitutes an equation instead of naming it.
-/
TacticDoc rcases

/--
`obtain ⟨a, b⟩ := h` is `rcases` written the other way round, and reads better when you are
naming the parts of a fact you just proved. `obtain ⟨a, rfl⟩ := h` names one component and
substitutes the other.
-/
TacticDoc obtain

/--
`rintro p` is `intro` with an `rcases` pattern: it introduces a hypothesis and takes it apart
in one step. `rintro ⟨f, hf⟩` is how you assume an existential and immediately name its
witness and its property — which is what proving a negation usually starts with.
-/
TacticDoc rintro
