import Mathlib
import Cslib.Computability.Distributed.Byzantine.LockStep.Parallel

/-!
# Synchronous randomized protocols against strongly adaptive omission adversaries

Model for the lower bound of Abraham, Chan, Dolev, Nayak, Pass, Ren, Shi, *Communication Complexity
of Byzantine Agreement, Revisited* (PODC 2019), Section 3 (Theorems 1 and 4).

* `n` nodes `P` (a `Fintype`), lock-step synchronous rounds `0, 1, 2, …` (infinite executions).
* **Randomness.** One probability space `(Ω, μ)`. Node `p`'s code may depend on `ω : Ω` in an
  arbitrary way, so `Ω` covers private coins, shared coins and any trusted setup (PKI, common
  random string, random oracle). This only makes the class of protocols larger, hence the lower
  bound stronger.
* **Protocol.** History based (inboxes and histories are those of CSLib's lock-step model): in round `r`, node `p` with input `x` and history `h` (the list of
  its inboxes in rounds `0, …, r-1`) sends `send p x ω h q : Option M` to each `q ≠ p`
  (self-messages are local computation and are not modelled); its *output* is the first
  `decide p x ω h = some b` along its histories (`none` forever = no output).
* **Adversary** (`Adversary P f`): a *strongly adaptive omission adversary*, i.e. the most
  restricted adversary of the paper's lower bound ("even under a more constrained omission
  adversary", Section 1). It observes the communication pattern (who sends to whom), including the
  pattern of the current round (rushing), and then
  - corrupts nodes (monotonically, at most `f` in total), possibly a node that has *just* sent;
  - drops any message of the current round whose sender or receiver is corrupted *after* this
    round's corruptions: this is the **after-the-fact removal** capability;
  corrupted nodes otherwise run the protocol (omission failures). Adversaries are deterministic;
  since a protocol must resist every adversary, this only weakens the hypothesis "the protocol is
  secure", hence strengthens the lower bound.
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open Cslib.Byzantine.LockStep (Inbox History firstSome?)

namespace CommComplexityBA

/-- Communication pattern of one round: `pat p q = true` iff `p` sends a message to `q`. -/
abbrev Pattern (P : Type*) := P → P → Bool

/-- A synchronous randomized protocol with inputs `I`, messages `M` and randomness `Ω`. -/
structure Protocol (P I M Ω : Type*) where
  /-- Message sent by `p` (input `x`, randomness `ω`, history `h`) to `q`, if any. -/
  send : P → I → Ω → History P M → P → Option M
  /-- Decision of `p` after history `h`, if any (only the first one counts). -/
  decide : P → I → Ω → History P M → Option Bool

-- CSLib candidate (randomized synchronous protocols vs. adaptive omission adversaries)
/-- A deterministic strongly adaptive omission adversary corrupting at most `f` nodes.
`corrupt l` / `drop l` are its decisions in the round whose pattern is the last entry of `l`
(`l` = patterns of all rounds so far, oldest first). -/
structure Adversary (P : Type*) (f : ℕ) where
  /-- Nodes corrupted so far, after observing the patterns `l`. -/
  corrupt : List (Pattern P) → Finset P
  /-- Messages of the current round that are omitted. -/
  drop : List (Pattern P) → P → P → Bool
  corrupt_mono : ∀ l x, corrupt l ⊆ corrupt (l ++ [x])
  card_corrupt : ∀ l, (corrupt l).card ≤ f
  /-- Only messages from or to corrupted nodes can be omitted (after-the-fact removal allowed:
  the sender may have been corrupted in this very round). -/
  drop_spec : ∀ l p q, drop l p q = true → p ∈ corrupt l ∨ q ∈ corrupt l

/-- Global state: histories of all nodes and the communication patterns so far. -/
abbrev State (P M : Type*) := (P → History P M) × List (Pattern P)

variable {P I M Ω : Type*} [DecidableEq P] {f : ℕ}

namespace Protocol

variable (π : Protocol P I M Ω) (inp : P → I) (ω : Ω)

/-- Message sent from `p` to `q` given the histories `h` (none to itself). -/
def msg (h : P → History P M) (p q : P) : Option M :=
  if p = q then none else π.send p (inp p) ω (h p) q

/-- One round, with omission rule `drop`. -/
def stepD (drop : List (Pattern P) → P → P → Bool) (s : State P M) : State P M :=
  let pats := s.2 ++ [fun p q => (π.msg inp ω s.1 p q).isSome]
  (fun q => s.1 q ++ [fun p => if drop pats p q then none else π.msg inp ω s.1 p q], pats)

/-- The execution, as a function of the omission rule only. -/
def runD (drop : List (Pattern P) → P → P → Bool) : ℕ → State P M
  | 0 => (fun _ => [], [])
  | r + 1 => π.stepD inp ω drop (runD drop r)

/-- The execution against adversary `A`: state after `r` rounds. -/
def run (A : Adversary P f) (r : ℕ) : State P M := π.runD inp ω A.drop r

/-- `p` is never corrupted (forever-honest). -/
def Honest (A : Adversary P f) (p : P) : Prop :=
  ∀ r, p ∉ A.corrupt (π.run inp ω A (r + 1)).2

end Protocol

namespace Protocol

variable (π : Protocol P I M Ω) (inp : P → I) (ω : Ω)

/-- Output of `p`: its first decision (`none` = never outputs). -/
noncomputable def output (A : Adversary P f) (p : P) : Option Bool :=
  firstSome? fun r => π.decide p (inp p) ω ((π.run inp ω A r).1 p)

/-- Output of `p` (input `x`) in a run where it never receives any message. -/
noncomputable def silentOut (p : P) (x : I) (ω : Ω) : Option Bool :=
  firstSome? fun r => π.decide p x ω (List.replicate r fun _ => none)

/-- Does `p` send a message to `q` in round `r`? -/
def sentAt (A : Adversary P f) (r : ℕ) (p q : P) : Bool :=
  (π.msg inp ω (π.run inp ω A r).1 p q).isSome

/-- Total number of messages sent by forever-honest nodes (over the whole infinite execution). -/
noncomputable def honestMsgs [Fintype P] (A : Adversary P f) : ENNReal := by
  classical exact
    ∑' r, ∑ p, ∑ q, if π.Honest inp ω A p ∧ π.sentAt inp ω A r p q = true then 1 else 0

end Protocol

/-! ### Specifications -/

/-- Termination and consistency for the nodes satisfying `H` (the forever-honest ones). -/
def TermCons (out : P → Option Bool) (H : P → Prop) : Prop :=
  (∀ p, H p → (out p).isSome) ∧
    ∀ p q x y, H p → H q → out p = some x → out q = some y → x = y

/-- Byzantine broadcast inputs: the designated sender `s` has `b`, nobody else has an input. -/
def bbInput (s : P) (b : Bool) : P → Option Bool := fun p => if p = s then some b else none

/-- Byzantine broadcast succeeds in the execution (sender `s` with input `b`, adversary `A`). -/
def BBGood (π : Protocol P (Option Bool) M Ω) (s : P) (b : Bool) (A : Adversary P f) (ω : Ω) :
    Prop :=
  TermCons (π.output (bbInput s b) ω A) (π.Honest (bbInput s b) ω A) ∧
    (π.Honest (bbInput s b) ω A s →
      ∀ p, π.Honest (bbInput s b) ω A p → π.output (bbInput s b) ω A p = some b)

/-- Byzantine agreement succeeds in the execution (inputs `inp`, adversary `A`). -/
def BAGood (π : Protocol P Bool M Ω) (inp : P → Bool) (A : Adversary P f) (ω : Ω) : Prop :=
  TermCons (π.output inp ω A) (π.Honest inp ω A) ∧
    ∀ v, (∀ p, π.Honest inp ω A p → inp p = v) → ∀ p, π.Honest inp ω A p → π.output inp ω A p = some v

variable [MeasurableSpace Ω]

/-- `π` solves Byzantine broadcast (sender `s`) with probability `q` against every strongly
adaptive omission adversary corrupting at most `f` nodes. The failure event need not be measurable;
`μ` of it is then its outer measure. -/
def SolvesBB (π : Protocol P (Option Bool) M Ω) (μ : Measure Ω) (s : P) (f : ℕ) (q : ℝ) : Prop :=
  ∀ (A : Adversary P f) (b : Bool), μ {ω | ¬ BBGood π s b A ω} ≤ ENNReal.ofReal (1 - q)

/-- `π` solves Byzantine agreement with probability `q` against every strongly adaptive omission
adversary corrupting at most `f` nodes, for all inputs. -/
def SolvesBA (π : Protocol P Bool M Ω) (μ : Measure Ω) (f : ℕ) (q : ℝ) : Prop :=
  ∀ (A : Adversary P f) (inp : P → Bool), μ {ω | ¬ BAGood π inp A ω} ≤ ENNReal.ofReal (1 - q)

/-- Regularity: for every fixed local history, sending and deciding are measurable functions of
the randomness. -/
def Protocol.IsMeasurable (π : Protocol P I M Ω) : Prop :=
  (∀ p x h q m, MeasurableSet {ω | π.send p x ω h q = m}) ∧
    ∀ p x h o, MeasurableSet {ω | π.decide p x ω h = o}

end CommComplexityBA
