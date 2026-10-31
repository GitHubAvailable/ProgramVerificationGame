import Mathlib.Tactic
import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Semantics.LTS.Simulation
import Cslib.Foundations.Semantics.LTS.Bisimulation
import Cslib.Foundations.Semantics.LTS.TraceEq
import Cslib.Computability.Automata.DA.Basic
import Cslib.Algorithms.Lean.Sort.Insertion
import Cslib.Algorithms.Lean.TimeM

/-!
# The systems the game reasons about

Every world of the game studies one small running example. This file defines those examples
once, so that the level files contain only the exercises themselves.

The definitions here are deliberately tiny: the point of the game is that the *reasoning*
scales, not the examples.
-/

open Cslib
open Cslib.Algorithms.Lean (TimeM)

/-! ## World 1: a parity automaton

`Cslib.Automata.DA State Symbol` is CSlib's deterministic automaton: a transition function
`tr : State → Symbol → State` together with a `start` state. We read a word of booleans and
track whether we have seen an odd number of `true`s.
-/

/-- The parity automaton. Its state is `true` exactly when it has read an odd number of
`true` symbols so far, and reading a symbol flips the state exactly when the symbol is `true`. -/
def parityDA : Automata.DA Bool Bool where
  tr := fun s b => xor s b
  start := false

/-- A *specification* of the parity automaton, written as an ordinary recursive Lean function:
`oddOnes xs` is `true` exactly when `xs` contains an odd number of `true`s. -/
def oddOnes : List Bool → Bool
  | [] => false
  | b :: bs => xor b (oddOnes bs)

/-- Reading one more symbol from the front of a word performs one transition of the
automaton. This is how `Cslib.FLTS.mtr` runs a whole word, one symbol at a time. -/
theorem parityDA_mtr_cons (s b : Bool) (xs : List Bool) :
    parityDA.mtr s (b :: xs) = parityDA.mtr (xor s b) xs := rfl

/-- The parity automaton read as an *acceptor*: the same machine, plus a set of accepting
states. `Cslib.Automata.DA.FinAcc` is CSlib's DFA, and the word `xs` is accepted when
`mtr start xs` lands in `accept`. Here the accepting state is `true`, so the accepted words
are exactly those with an odd number of `true`s. -/
def parityAcc : Automata.DA.FinAcc Bool Bool where
  toDA := parityDA
  accept := {true}

/-- The states of a traffic light. `broken` is a state the controller can describe but, as
World 1 asks you to prove, never actually enters. -/
inductive Light where
  /-- Traffic may pass. -/
  | green
  /-- Traffic is about to be stopped. -/
  | yellow
  /-- Traffic must stop. -/
  | red
  /-- The failure state. -/
  | broken
deriving DecidableEq, Repr

/-- The traffic-light controller. Every tick advances `green → yellow → red → green`; nothing
leads into `broken`. -/
def lightDA : Automata.DA Light Unit where
  tr := fun s _ => match s with
    | .green => .yellow
    | .yellow => .red
    | .red => .green
    | .broken => .broken
  start := .green

/-- An ordinary program's way of answering the same question the automaton answers: walk the
word and keep a running count of the `true`s in an integer variable. -/
def countOnes : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + countOnes bs

/-! ## World 2: specifications as predicates on implementations

Nothing from CSlib is needed to talk about the contract of a pure function, so World 2 uses
ordinary Lean. `IsUpperBound f` is a *proposed* specification of a "maximum" function.
-/

/-- A proposed specification for a two-argument maximum: the result is at least as large as
both arguments. -/
def IsUpperBound (f : Int → Int → Int) : Prop :=
  ∀ a b, a ≤ f a b ∧ b ≤ f a b

/-- Force `x` into the range `[lo, hi]`. The contract it is supposed to satisfy only makes
sense when `lo ≤ hi`, which is World 2's lesson about preconditions. -/
def clamp (lo hi x : Int) : Int :=
  if x < lo then lo else if hi < x then hi else x

/-- A specification of a two-argument maximum strong enough to be worth the name: the result
is one of the two arguments, **and** it is at least as large as both. Contrast
`IsUpperBound`, which drops the first clause and is satisfied by functions that are not
maxima at all. -/
def IsMaxSpec (f : Int → Int → Int) : Prop :=
  ∀ a b, (f a b = a ∨ f a b = b) ∧ a ≤ f a b ∧ b ≤ f a b

/-- Quotient and remainder, packaged together so that one contract can talk about both. -/
def divmod (a b : ℕ) : ℕ × ℕ := (a / b, a % b)

/-- A function built by composing two others: keep the non-negative entries, then double
them. Its contract has to be assembled from the contracts of `List.filter` and `List.map`. -/
def scaleNonNeg (xs : List Int) : List Int :=
  (xs.filter (fun x => 0 ≤ x)).map (fun x => x * 2)

/-! ## World 3: a bank account as a labelled transition system

`Cslib.LTS State Label` is a labelled transition relation `Tr : State → Label → State → Prop`.
Here a state is a balance and a label is the operation performed.
-/

/-- The operations a bank account accepts. -/
inductive Op where
  /-- Pay `n` into the account. -/
  | deposit (n : ℕ)
  /-- Take `n` out of the account; only possible when the balance covers it. -/
  | withdraw (n : ℕ)
deriving DecidableEq, Repr

/-- The bank account transition system. A deposit always succeeds; a withdrawal is only a legal
transition when the balance covers the requested amount. -/
def account : LTS Int Op where
  Tr := fun s op s' => match op with
    | .deposit n => s' = s + n
    | .withdraw n => (n : Int) ≤ s ∧ s' = s - n

/-- The operations a room's door counter observes. -/
inductive Gate where
  /-- Somebody comes in. The room holds at most ten people, so this is only a legal step
  when there is space. -/
  | enter
  /-- Somebody leaves, which is only a legal step when the room is not empty. -/
  | leave
deriving DecidableEq, Repr

/-- A room with a capacity of ten, as a transition system over its occupancy. It is a
*different* system from `account` — different state type, different operations — which is
the point: the same CSlib invariant theorem applies to it unchanged. -/
def room : LTS ℕ Gate where
  Tr := fun n op m => match op with
    | .enter => n < 10 ∧ m = n + 1
    | .leave => 0 < n ∧ m = n - 1

/-- Moving a token between two buckets. -/
inductive Move where
  /-- Move one token from the second bucket to the first. -/
  | toA
  /-- Move one token from the first bucket to the second. -/
  | toB
deriving DecidableEq, Repr

/-- Five tokens distributed between two buckets. Tokens are only ever moved, never created
or destroyed — but notice that the transition relation says nothing about the total, so the
fact that the total is conserved is something you have to prove. -/
def tokens : LTS (ℕ × ℕ) Move where
  Tr := fun p m q => match m with
    | .toA => 0 < p.2 ∧ q = (p.1 + 1, p.2 - 1)
    | .toB => 0 < p.1 ∧ q = (p.1 - 1, p.2 + 1)

/-- The sum of a list, written as an ordinary recursive Lean function. -/
def total : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + total xs

/-- The same sum, written the way a loop would compute it: carry a running accumulator and
return it at the end. `totalTR xs acc` is the accumulator's final value. -/
def totalTR : List ℕ → ℕ → ℕ
  | [], acc => acc
  | x :: xs, acc => totalTR xs (acc + x)

/-- Insert `a` into `xs` in front of the first element it does not exceed. If `xs` is sorted
then so is the result — a *data-structure invariant*, and the heart of insertion sort. -/
def ins (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | x :: xs => if a ≤ x then a :: x :: xs else x :: ins a xs

/-- Insertion sort, written directly: sort the tail, then insert the head into it. World 4
proves this correct and then relates it to CSlib's monadic version. -/
def isort : List ℕ → List ℕ
  | [] => []
  | x :: xs => ins x (isort xs)

/-! ## World 4: a cost-annotated insertion sort

`Cslib.Algorithms.Lean.TimeM T α` pairs a result with an accumulated cost, and
`List.insertionSortM` is CSlib's insertion sort over an arbitrary monad. Instantiating it at
`TimeM ℕ` gives a sort that counts its comparisons.
-/

/-- Comparing two numbers costs one tick. This is the cost model: a comparison costs `1`,
everything else is free. -/
def cmpCost (a b : ℕ) : TimeM ℕ Bool := do
  TimeM.tick 1
  return (decide (a ≤ b))

/-- Insertion sort instrumented with the cost model of `cmpCost`. Its `.ret` field is the
sorted list and its `.time` field is the number of comparisons performed. -/
def timedSort (xs : List ℕ) : TimeM ℕ (List ℕ) :=
  List.insertionSortM cmpCost xs

/-! ## World 5: a stack implementation against a counter specification

Two labelled transition systems over the same labels but with *different state types*: the
specification counts how many items are stored, the implementation keeps the items in a list.
-/

/-- The operations observable at the interface of a stack. -/
inductive StackOp where
  /-- Push one item. -/
  | push
  /-- Pop one item; only possible when the stack is non-empty. -/
  | pop
deriving DecidableEq, Repr

/-- The specification: an abstract counter. It permits a `pop` exactly when the count is
positive. -/
def counterSpec : LTS ℕ StackOp where
  Tr := fun n op m => match op with
    | .push => m = n + 1
    | .pop => 0 < n ∧ m = n - 1

/-- The implementation: a list of items. It permits a `pop` exactly when the list is
non-empty. -/
def stackImpl : LTS (List Unit) StackOp where
  Tr := fun l op l' => match op with
    | .push => l' = () :: l
    | .pop => ∃ t, l = () :: t ∧ l' = t

/-- The behaviors the implementation can exhibit from stack `l`: the words of operations it
can actually perform. -/
abbrev implTraces (l : List Unit) : Set (List StackOp) := LTS.traces (lts := stackImpl) l

/-- The behaviors the specification permits from count `n`. -/
abbrev specTraces (n : ℕ) : Set (List StackOp) := LTS.traces (lts := counterSpec) n

/-! ### Two ways to read past the end of a list

The first operation is the one a language without bounds checks gives you: out of range it
quietly returns a default. The second reports the failure. World 5 asks in what sense the
second may replace the first.
-/

/-- Unchecked lookup: out of range it returns `0`, which is indistinguishable from a list
that really does hold `0` at that index. -/
def lookupRaw (xs : List ℕ) (i : ℕ) : ℕ := xs.getD i 0

/-- Checked lookup: out of range it returns `none`. -/
def lookupChecked (xs : List ℕ) (i : ℕ) : Option ℕ := xs[i]?

/-! ### Choosing early and choosing late

Two systems offering the same words to an observer, which nevertheless differ in *when* the
choice between `b` and `c` is made. They are the standard counterexample separating
simulation from trace inclusion, and trace equivalence from bisimilarity.
-/

/-- The observable actions of the two choice systems. -/
inductive Act where
  /-- The first action, common to both branches. -/
  | a
  /-- One of the two continuations. -/
  | b
  /-- The other continuation. -/
  | c
deriving DecidableEq, Repr

/-- States of the system that chooses *after* the `a`. -/
inductive Late where
  /-- Before the `a`. -/
  | l0
  /-- After the `a`, with both `b` and `c` still available. -/
  | l1
  /-- After `b`. -/
  | l2
  /-- After `c`. -/
  | l3
deriving DecidableEq, Repr

/-- States of the system that chooses *during* the `a`. -/
inductive Early where
  /-- Before the `a`. -/
  | e0
  /-- After the `a` that committed to `b`. -/
  | e1
  /-- After `b`. -/
  | e2
  /-- After the `a` that committed to `c`. -/
  | e3
  /-- After `c`. -/
  | e4
deriving DecidableEq, Repr

/-- `l0 -a→ l1`, and from `l1` both `b` and `c` are available: the choice happens late. -/
def chooseLate : LTS Late Act where
  Tr := fun s μ s' => match s, μ, s' with
    | .l0, .a, .l1 => True
    | .l1, .b, .l2 => True
    | .l1, .c, .l3 => True
    | _, _, _ => False

/-- Two different `a`-transitions leave `e0`, one committing to `b` and one to `c`: the
choice happens early. -/
def chooseEarly : LTS Early Act where
  Tr := fun s μ s' => match s, μ, s' with
    | .e0, .a, .e1 => True
    | .e1, .b, .e2 => True
    | .e0, .a, .e3 => True
    | .e3, .c, .e4 => True
    | _, _, _ => False

/-- A candidate relation between the early and the late system: each early state stands for
the late state with the same remaining behavior. -/
def matchEL : Early → Late → Prop := fun e l => match e, l with
  | .e0, .l0 => True
  | .e1, .l1 => True
  | .e3, .l1 => True
  | .e2, .l2 => True
  | .e4, .l3 => True
  | _, _ => False

/-! ### A step nobody can see

`Cslib.HasTau` marks one label as *internal*: a step the system really takes but an observer
cannot detect. Weak bisimilarity is bisimilarity that ignores those steps.
-/

/-- Labels with an internal action. -/
inductive TAct where
  /-- The internal step, invisible to an observer. -/
  | tau
  /-- The one observable action. -/
  | out
deriving DecidableEq, Repr

instance : HasTau TAct where τ := TAct.tau

/-- States of the implementation that does some internal work first. -/
inductive Delayed where
  /-- Before the internal step. -/
  | d0
  /-- Internal work done, ready to output. -/
  | d1
  /-- Output produced. -/
  | d2
deriving DecidableEq, Repr

/-- States of the specification, which outputs immediately. -/
inductive Direct where
  /-- Ready to output. -/
  | n0
  /-- Output produced. -/
  | n1
deriving DecidableEq, Repr

/-- `d0 -τ→ d1 -out→ d2`: one invisible step of preparation before the visible output. -/
def delayed : LTS Delayed TAct where
  Tr := fun s μ s' => match s, μ, s' with
    | .d0, .tau, .d1 => True
    | .d1, .out, .d2 => True
    | _, _, _ => False

/-- `n0 -out→ n1`: the output, with no preparation. -/
def direct : LTS Direct TAct where
  Tr := fun s μ s' => match s, μ, s' with
    | .n0, .out, .n1 => True
    | _, _, _ => False

/-- A candidate relation between the delayed implementation and the direct specification.
Both `d0` and `d1` stand for `n0`, because the step between them is invisible. -/
def matchDN : Delayed → Direct → Prop := fun d n => match d, n with
  | .d0, .n0 => True
  | .d1, .n0 => True
  | .d2, .n1 => True
  | _, _ => False

/-- The invisible step of `delayed`, as a saturated τ-path: `d0` reaches `d1` by internal
work alone. -/
theorem delayed_tau_step : delayed.τSTr Delayed.d0 Delayed.d1 :=
  Relation.ReflTransGen.single (by trivial)

/-- `d0` can perform a *saturated* `out`: do the invisible step, then the visible one. This is
the composite an observer sees as a bare `out`, and it is what `direct`'s immediate `out` has
to be answered with. -/
theorem delayed_out_step : delayed.STr Delayed.d0 TAct.out Delayed.d2 :=
  LTS.STr.tr delayed_tau_step
    (show delayed.Tr Delayed.d1 TAct.out Delayed.d2 from trivial) .refl
