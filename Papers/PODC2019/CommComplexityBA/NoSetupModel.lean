import Papers.PODC2019.CommComplexityBA.Model

/-!
# Plain authenticated channels without setup (Section 7, Theorem 13)

Model for Theorem 13 of the paper (the Byzantine-broadcast form of Theorem 3).

* `n` nodes `P`, lock-step synchronous rounds `0, 1, 2, …` (infinite executions).
* **No setup.** Every node `p` has a private random tape `ω p : T`, the tapes are independent with
  laws `ν p` (`Measure.pi ν`). There is no shared randomness, no PKI, no common random string.
* **Plain authenticated channels.** In round `r` a node sends to each other node a *multiset* of
  messages (several messages per channel and round are allowed); the receiver learns the true
  sender. Protocols are history based (`send`, `decide`), as in `Model.lean`.
* **Adversary** (`Adversary P M R C`): it has its own randomness `ρ : R` (we use `R = P → T`, i.e.
  it can sample fresh tapes, and `ρ` is independent of the nodes' tapes), observes all messages
  sent in previous rounds (no private channels), corrupts nodes adaptively (monotonically, at most
  `C`), and *injects* additional messages on channels with a corrupted endpoint. Corrupted nodes
  otherwise keep running the protocol. This is a restriction of the Byzantine adaptive adversary of
  the paper (it can neither remove nor alter messages), so it makes the impossibility *stronger*.
* **Communication.** `FewSpeakers C`: at most `C` forever-honest nodes ever send a message. A
  multicast protocol with multicast complexity `≤ C` has at most `C` speakers, so this covers the
  paper's measure and its remark "at most `C` nodes send messages".
-/

set_option linter.unusedSectionVars false

open MeasureTheory

namespace CommComplexityBA.NoSetup

/-- Messages received in one round, indexed by the (authenticated) sender. -/
abbrev MInbox (P M : Type*) := P → Multiset M

/-- Local history: inboxes so far, oldest first. -/
abbrev MHistory (P M : Type*) := List (MInbox P M)

/-- Messages sent in one round: `tr p q` is what `p` sends to `q`. -/
abbrev Traffic (P M : Type*) := P → P → Multiset M

/-- A protocol in which node `p` uses its private tape `t : T`. -/
structure Protocol (P I M T : Type*) where
  send : P → I → T → MHistory P M → P → Multiset M
  decide : P → I → T → MHistory P M → Option Bool

/-- An adaptive message-injecting adversary with randomness `R` corrupting at most `C` nodes. The
decisions for round `r` depend on its randomness and on all messages sent in rounds `< r`
(`l`, oldest first). -/
structure Adversary (P M R : Type*) (C : ℕ) where
  corrupt : R → List (Traffic P M) → Finset P
  inject : R → List (Traffic P M) → P → P → Multiset M
  corrupt_mono : ∀ ρ l x, corrupt ρ l ⊆ corrupt ρ (l ++ [x])
  card_corrupt : ∀ ρ l, (corrupt ρ l).card ≤ C
  inject_spec : ∀ ρ l p q, inject ρ l p q ≠ 0 → p ∈ corrupt ρ l ∨ q ∈ corrupt ρ l

variable {P I M T R : Type*} [DecidableEq P] {C : ℕ}

namespace Protocol

variable (π : Protocol P I M T) (inp : P → I) (ω : P → T)

/-- Messages sent in a round by honest code, given the histories (nothing to oneself). -/
def sent (h : P → MHistory P M) : Traffic P M :=
  fun p q => if p = q then 0 else π.send p (inp p) (ω p) (h p) q

/-- Execution with injection rule `inj`: histories and the list of past traffic. -/
def runI (inj : List (Traffic P M) → P → P → Multiset M) :
    ℕ → (P → MHistory P M) × List (Traffic P M)
  | 0 => (fun _ => [], [])
  | r + 1 =>
    ((fun q => (runI inj r).1 q ++ [fun p => π.sent inp ω (runI inj r).1 p q + inj (runI inj r).2 p q]),
      (runI inj r).2 ++ [π.sent inp ω (runI inj r).1])

/-- Execution against adversary `A` with adversary randomness `ρ`. -/
def run (A : Adversary P M R C) (ρ : R) (r : ℕ) : (P → MHistory P M) × List (Traffic P M) :=
  π.runI inp ω (A.inject ρ) r

/-- `p` is never corrupted. -/
def Honest (A : Adversary P M R C) (ρ : R) (p : P) : Prop :=
  ∀ r, p ∉ A.corrupt ρ (π.run inp ω A ρ r).2

/-- First decision of `p`. -/
noncomputable def output (A : Adversary P M R C) (ρ : R) (p : P) : Option Bool :=
  firstSome fun r => π.decide p (inp p) (ω p) ((π.run inp ω A ρ r).1 p)

/-- `p` sends at least one message at some point. -/
def Speaks (A : Adversary P M R C) (ρ : R) (p : P) : Prop :=
  ∃ r q, π.sent inp ω (π.run inp ω A ρ r).1 p q ≠ 0

end Protocol

/-- Byzantine broadcast succeeds (sender `s` with input `b`). -/
def BBGood (π : Protocol P (Option Bool) M T) (s : P) (b : Bool) (A : Adversary P M R C)
    (ω : P → T) (ρ : R) : Prop :=
  TermCons (π.output (bbInput s b) ω A ρ) (π.Honest (bbInput s b) ω A ρ) ∧
    (π.Honest (bbInput s b) ω A ρ s →
      ∀ p, π.Honest (bbInput s b) ω A ρ p → π.output (bbInput s b) ω A ρ p = some b)

/-- At most `C` forever-honest nodes ever send a message. -/
def FewSpeakers (π : Protocol P (Option Bool) M T) (s : P) (b : Bool) (A : Adversary P M R C)
    (ω : P → T) (ρ : R) : Prop :=
  {p | π.Honest (bbInput s b) ω A ρ p ∧ π.Speaks (bbInput s b) ω A ρ p}.ncard ≤ C

variable [MeasurableSpace T]

/-- The probability space: node tapes `ω` and adversary randomness `ρ` (fresh tapes),
independent. -/
noncomputable def μ2 [Fintype P] (ν : P → Measure T) : Measure ((P → T) × (P → T)) :=
  (Measure.pi ν).prod (Measure.pi ν)

/-- `π` solves Byzantine broadcast (sender `s`) with probability `q` against every adaptive
adversary corrupting at most `C` nodes. -/
def SolvesBB [Fintype P] (π : Protocol P (Option Bool) M T) (ν : P → Measure T) (s : P) (C : ℕ)
    (q : ℝ) : Prop :=
  ∀ (A : Adversary P M (P → T) C) (b : Bool),
    μ2 ν {x | ¬ BBGood π s b A x.1 x.2} ≤ ENNReal.ofReal (1 - q)

/-- With probability `q`, at most `C` honest nodes speak, against every adaptive adversary
corrupting at most `C` nodes. -/
def FewSpeakersWP [Fintype P] (π : Protocol P (Option Bool) M T) (ν : P → Measure T) (s : P)
    (C : ℕ) (q : ℝ) : Prop :=
  ∀ (A : Adversary P M (P → T) C) (b : Bool),
    μ2 ν {x | ¬ FewSpeakers π s b A x.1 x.2} ≤ ENNReal.ofReal (1 - q)

end CommComplexityBA.NoSetup
