import Podc.Computability.Distributed.PopulationProtocols.Phases
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option

/-!
# The model: population protocols with or without a leader, and the naming problem

Burman, Beauquier, Sohier, *Space-Optimal Naming in Population Protocols* (PODC 2018 brief
announcement; full version HAL hal-01790517v3 / DISC 2019), Section 2.

* Protocols are CSLib's deterministic population protocols (`Cslib.PopulationProtocol.Protocol`)
  on labelled configurations `A → Q`; executions, weak fairness (every unordered pair of agents
  interacts infinitely often) and global fairness are CSLib's.
* A protocol is *symmetric* (`IsSymmetric`) if `δ q p = (δ p q).swap`; in particular two
  homonyms stay homonyms.
* Protocols with a leader (`LeaderProtocol L Q`): mobile agents have states `Q`, the unique leader
  has states `L` (any type: the leader may be "as powerful as needed"). Such a protocol is turned
  into a CSLib protocol on `L ⊕ Q` (`LeaderProtocol.toProtocol`) whose agents are `Option A`
  (`none` is the leader); configurations of the paper are `ofLM l c`.
* **Naming** (`Execution.Stabilizes names Function.Injective`): the names of the mobile agents are
  eventually constant and pairwise distinct. The name of a mobile agent is a function `name` of
  its state (the paper's "variable called a name").
* `SolvesWeak P I names` / `SolvesGlobal P I names`: every weakly / globally fair execution
  starting in `I` (the allowed initial configurations) solves naming.
-/

namespace Podc.PPNaming

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

variable {S Ag A Q L N : Type*}

/-- A protocol is *symmetric* if exchanging the roles of the two agents exchanges the results:
`(p, q) → (p', q')` implies `(q, p) → (q', p')`. -/
def IsSymmetric (P : Protocol S) : Prop := ∀ p q, P.δ q p = (P.δ p q).swap

lemma IsSymmetric.diag {P : Protocol S} (h : IsSymmetric P) (s : S) :
    (P.δ s s).2 = (P.δ s s).1 := by
  have := congrArg Prod.fst (h s s); simpa using this.symm

lemma IsSymmetric.interact_comm [DecidableEq Ag] {P : Protocol S} (h : IsSymmetric P)
    (C : Config Ag S) {a b : Ag} (hab : a ≠ b) : P.interact C b a = P.interact C a b := by
  funext x
  simp only [Protocol.interact]
  by_cases hxa : x = a
  · subst hxa; simp [hab, h (C x) (C b)]
  · by_cases hxb : x = b
    · subst hxb; simp [hxa, h (C a) (C x)]
    · simp [hxa, hxb]

/-- Every weakly fair execution starting in `I` solves naming: the names `names C` of the mobile
agents are eventually constant and pairwise distinct. -/
def SolvesWeak [DecidableEq Ag] (P : Protocol S) (I : Set (Config Ag S))
    (names : Config Ag S → A → N) : Prop :=
  ∀ E : P.Execution Ag, E.config 0 ∈ I → E.WeaklyFair → E.Stabilizes names Function.Injective

/-- Every globally fair execution starting in `I` solves naming. -/
def SolvesGlobal [DecidableEq Ag] (P : Protocol S) (I : Set (Config Ag S))
    (names : Config Ag S → A → N) : Prop :=
  ∀ E : P.Execution Ag, E.config 0 ∈ I → E.GloballyFair → E.Stabilizes names Function.Injective

/-- Names in a population without leader: every agent is mobile and named by its state. -/
def nameOut (name : Q → N) : Config A Q → A → N := fun C a => name (C a)

/-- A configuration is *stably named*: the names are pairwise distinct and never change again. -/
abbrev StablyNamed [DecidableEq Ag] (P : Protocol S) (names : Config Ag S → A → N)
    (C : Config Ag S) : Prop :=
  P.StablyGood names Function.Injective C

/-! ### Protocols with a leader -/

/-- A population protocol with a (unique) leader: transition functions for two mobile agents,
for the leader initiating with a mobile agent, and for a mobile agent initiating with the
leader. -/
structure LeaderProtocol (L Q : Type*) where
  /-- Two mobile agents (initiator, responder). -/
  mm : Q → Q → Q × Q
  /-- The leader (initiator) meets a mobile agent (responder). -/
  lm : L → Q → L × Q
  /-- A mobile agent (initiator) meets the leader (responder). -/
  ml : Q → L → Q × L

namespace LeaderProtocol

variable (LP : LeaderProtocol L Q)

/-- The protocol on `L ⊕ Q` (leader states on the left). Two leader states never meet (there is
a single leader); this case is a null transition. -/
def toProtocol : Protocol (L ⊕ Q) where
  δ x y := match x, y with
    | .inr p, .inr q => (.inr (LP.mm p q).1, .inr (LP.mm p q).2)
    | .inl l, .inr q => (.inl (LP.lm l q).1, .inr (LP.lm l q).2)
    | .inr q, .inl l => (.inr (LP.ml q l).1, .inl (LP.ml q l).2)
    | .inl l, .inl l' => (.inl l, .inl l')

/-- Symmetric leader protocols: mobile-mobile rules are symmetric and the leader rules do not
depend on who initiates. -/
def Symmetric : Prop := (∀ p q, LP.mm q p = (LP.mm p q).swap) ∧ ∀ l q, LP.ml q l = (LP.lm l q).swap

variable {LP}

lemma Symmetric.isSymmetric (h : LP.Symmetric) : IsSymmetric LP.toProtocol := by
  intro x y
  rcases x with l | p <;> rcases y with l' | q
  · rfl
  · simp [toProtocol, h.2]
  · simp [toProtocol, h.2]
  · simp [toProtocol, h.1 p q]

end LeaderProtocol

/-- The configuration with leader in state `l` and mobile agents in states `c`. -/
def ofLM (l : L) (c : A → Q) : Config (Option A) (L ⊕ Q)
  | none => .inl l
  | some a => .inr (c a)

@[simp] lemma ofLM_none (l : L) (c : A → Q) : ofLM l c none = .inl l := rfl
@[simp] lemma ofLM_some (l : L) (c : A → Q) (a : A) : ofLM l c (some a) = .inr (c a) := rfl

lemma ofLM_injective {l l' : L} {c c' : A → Q} (h : ofLM l c = ofLM l' c') : l = l' ∧ c = c' := by
  refine ⟨?_, funext fun a => ?_⟩
  · have := congrFun h none; simpa using this
  · have := congrFun h (some a); simpa using this

/-- The name of a mobile agent's state (`none` for leader states, which never occur at mobile
agents). -/
def mobName (name : Q → N) : L ⊕ Q → Option N := Sum.elim (fun _ => none) (fun q => some (name q))

/-- Names of the mobile agents of a population with a leader. -/
def leaderNames (name : Q → N) : Config (Option A) (L ⊕ Q) → A → Option N :=
  fun C a => mobName name (C (some a))

@[simp] lemma leaderNames_ofLM (name : Q → N) (l : L) (c : A → Q) (a : A) :
    leaderNames name (ofLM l c) a = some (name (c a)) := rfl

lemma leaderNames_ofLM_injective_iff (name : Q → N) (l : L) (c : A → Q) :
    Function.Injective (leaderNames name (ofLM l c)) ↔ Function.Injective (fun a => name (c a)) := by
  constructor
  · intro h a b hab; exact h (by simp [hab])
  · intro h a b hab; exact h (by simpa using hab)

/-! #### Initializations -/

/-- Initialized leader (in state `l₀`), arbitrarily initialized mobile agents. -/
def initLeader (l₀ : L) : Set (Config (Option A) (L ⊕ Q)) := {C | ∃ c, C = ofLM l₀ c}

/-- Arbitrary initialization of everybody (self-stabilization), with a leader. -/
def initArb : Set (Config (Option A) (L ⊕ Q)) := {C | ∃ l c, C = ofLM l c}

/-- Arbitrarily initialized leader, uniformly initialized (state `q₀`) mobile agents. -/
def initArbLeaderUniform (q₀ : Q) : Set (Config (Option A) (L ⊕ Q)) :=
  {C | ∃ l, C = ofLM l (fun _ => q₀)}

/-- Initialized leader (`l₀`) and uniformly initialized mobile agents (`q₀`). -/
def initUniform (l₀ : L) (q₀ : Q) : Set (Config (Option A) (L ⊕ Q)) :=
  {ofLM l₀ (fun _ => q₀)}

/-! #### Interactions in configurations `ofLM l c` -/

section Interact

variable [DecidableEq A] (LP : LeaderProtocol L Q)

lemma interact_leader_mobile (l : L) (c : A → Q) (a : A) :
    LP.toProtocol.interact (ofLM l c) none (some a) =
      ofLM (LP.lm l (c a)).1 (Function.update c a (LP.lm l (c a)).2) := by
  funext x
  rcases x with _ | x
  · simp [Protocol.interact, LeaderProtocol.toProtocol]
  · by_cases hx : x = a
    · subst hx; simp [Protocol.interact, LeaderProtocol.toProtocol]
    · simp [Protocol.interact, LeaderProtocol.toProtocol, hx]

lemma interact_mobile_leader (l : L) (c : A → Q) (a : A) :
    LP.toProtocol.interact (ofLM l c) (some a) none =
      ofLM (LP.ml (c a) l).2 (Function.update c a (LP.ml (c a) l).1) := by
  funext x
  rcases x with _ | x
  · simp [Protocol.interact, LeaderProtocol.toProtocol]
  · by_cases hx : x = a
    · subst hx; simp [Protocol.interact, LeaderProtocol.toProtocol]
    · simp [Protocol.interact, LeaderProtocol.toProtocol, hx]

/-- The mobile configuration after an interaction of mobile agents `a ≠ b`. -/
def LeaderProtocol.mmUpd (LP : LeaderProtocol L Q) (c : A → Q) (a b : A) : A → Q :=
  Function.update (Function.update c a (LP.mm (c a) (c b)).1) b (LP.mm (c a) (c b)).2

lemma interact_mobile_mobile (l : L) (c : A → Q) {a b : A} (hab : a ≠ b) :
    LP.toProtocol.interact (ofLM l c) (some a) (some b) = ofLM l (LP.mmUpd c a b) := by
  funext x
  rcases x with _ | x
  · simp [Protocol.interact]
  · by_cases hxa : x = a
    · subst hxa; simp [Protocol.interact, LeaderProtocol.toProtocol, LeaderProtocol.mmUpd, hab]
    · by_cases hxb : x = b
      · subst hxb; simp [Protocol.interact, LeaderProtocol.toProtocol, LeaderProtocol.mmUpd, hxa]
      · simp [Protocol.interact, LeaderProtocol.toProtocol, LeaderProtocol.mmUpd, hxa, hxb]

/-- Every interaction maps a configuration `ofLM l c` to a configuration of the same form. -/
lemma exists_ofLM_of_step {l : L} {c : A → Q} {D : Config (Option A) (L ⊕ Q)}
    (h : LP.toProtocol.Step (ofLM l c) D) : ∃ l' c', D = ofLM l' c' := by
  obtain ⟨x, y, hxy, rfl⟩ := h
  rcases x with _ | a <;> rcases y with _ | b
  · exact absurd rfl hxy
  · exact ⟨_, _, interact_leader_mobile LP l c b⟩
  · exact ⟨_, _, interact_mobile_leader LP l c a⟩
  · exact ⟨_, _, interact_mobile_mobile LP l c (fun h => hxy (by rw [h]))⟩

lemma exists_ofLM_of_reachable {l : L} {c : A → Q} {D : Config (Option A) (L ⊕ Q)}
    (h : LP.toProtocol.Reachable (ofLM l c) D) : ∃ l' c', D = ofLM l' c' := by
  induction h with
  | refl => exact ⟨l, c, rfl⟩
  | tail _ hst ih =>
    obtain ⟨l', c', rfl⟩ := ih
    exact exists_ofLM_of_step LP hst

end Interact

end Podc.PPNaming
