import Papers.PODC2015.CrashConsensusDigraph.Graph

/-!
# Synchronous crash-prone message passing on a directed graph

The system model of Sections 1.2 and 2 of Tseng–Vaidya (PODC 2015).

* Nodes `V` (finite), static communication digraph `G`: `u` can send to `w` iff `G.Adj u w`.
  Links are reliable. Every node knows `G` and its own identity (the algorithm may depend on both).
* A deterministic synchronous algorithm (`Algorithm V I M S O`): local state `S`, initial state
  from the input, in each round `r = 0, 1, …` node `u` sends `send u s w` (or nothing) to every
  out-neighbour `w`, then computes its new state from its old state and its *inbox*
  (`V → Option M`: the message received from each in-neighbour, if any). `out u s` is the
  (optional) output; the first output is the node's decision.
* Crash faults (`Adversary`): `crash u = some c` means that `u` crashes in round `c`: it behaves
  correctly in rounds `< c`, in round `c` its message reaches only the out-neighbours `w` with
  `part u w` (an arbitrary subset), and from round `c + 1` on it sends nothing. At most `f` nodes
  crash (`Admissible`). The crash pattern is arbitrary (it may depend on the inputs).
* `SolvesOn G f In alg` — *crash consensus* for inputs in `In`: for every admissible adversary and
  all inputs in `In`, every fault-free node decides (termination), fault-free nodes decide the same
  value (agreement), and every decision of a fault-free node is the input of some node
  (validity). These are the three properties of Section 1.
-/

open Finset

-- CSLib candidate (synchronous crash-prone message passing on digraphs)

set_option linter.unusedSectionVars false

namespace CrashConsensusDigraph

/-- A deterministic synchronous algorithm with inputs `I`, messages `M`, states `S`, outputs `O`. -/
structure Algorithm (V I M S O : Type*) where
  /-- Initial state of a node with a given input. -/
  init : V → I → S
  /-- `send u s w`: the message `u` (in state `s`) sends to its out-neighbour `w` (if any). -/
  send : V → S → V → Option M
  /-- `trans u s inbox`: the new state of `u`; `inbox w` is the message received from `w`. -/
  trans : V → S → (V → Option M) → S
  /-- The output in a given state (`none` = not decided yet). -/
  out : V → S → Option O

/-- A crash pattern. -/
structure Adversary (V : Type*) where
  /-- `crash u = some c`: `u` crashes in round `c`. -/
  crash : V → Option ℕ
  /-- In its crash round, the message of `u` reaches exactly the out-neighbours `w` with
  `part u w`. -/
  part : V → V → Prop

namespace Adversary

variable {V : Type*} (adv : Adversary V)

/-- At most `f` nodes crash. -/
def Admissible (f : ℕ) : Prop :=
  ∃ F : Finset V, F.card ≤ f ∧ ∀ u c, adv.crash u = some c → u ∈ F

/-- `u` still sends (possibly only partially) in round `r`. -/
def Alive (r : ℕ) (u : V) : Prop := ∀ c, adv.crash u = some c → r ≤ c

theorem Alive.of_succ {adv : Adversary V} {r : ℕ} {u : V} (h : adv.Alive (r + 1) u) :
    adv.Alive r u := fun c hc => Nat.le_of_succ_le (h c hc)

theorem Alive.mono {adv : Adversary V} {r r' : ℕ} {u : V} (h : adv.Alive r' u) (hr : r ≤ r') :
    adv.Alive r u := fun c hc => hr.trans (h c hc)

theorem alive_of_correct {adv : Adversary V} {u : V} (h : adv.crash u = none) (r : ℕ) :
    adv.Alive r u := fun c hc => by simp [h] at hc

end Adversary

variable {V I M S O : Type*}

/-- The message of `u` sent in round `r` reaches `w`. -/
def Delivers (G : Digraph V) (adv : Adversary V) (r : ℕ) (u w : V) : Prop :=
  G.Adj u w ∧ ∀ c, adv.crash u = some c → r < c ∨ (r = c ∧ adv.part u w)

theorem Delivers.adj {G : Digraph V} {adv : Adversary V} {r : ℕ} {u w : V}
    (h : Delivers G adv r u w) : G.Adj u w := h.1

theorem Delivers.alive {G : Digraph V} {adv : Adversary V} {r : ℕ} {u w : V}
    (h : Delivers G adv r u w) : adv.Alive r u := fun c hc => by
  rcases h.2 c hc with h | h
  · exact h.le
  · exact h.1.le

/-- A node that is still alive after round `r` delivered its round-`r` message to all its
out-neighbours. -/
theorem delivers_of_alive {G : Digraph V} {adv : Adversary V} {r : ℕ} {u w : V}
    (h : adv.Alive (r + 1) u) (e : G.Adj u w) : Delivers G adv r u w :=
  ⟨e, fun c hc => Or.inl (h c hc)⟩

section Run

variable (G : Digraph V) (alg : Algorithm V I M S O) (adv : Adversary V) (inp : V → I)

open Classical in
/-- The inbox of `w` in round `r`, given the states `st` at the start of the round. -/
noncomputable def inbox (st : V → S) (r : ℕ) (w : V) : V → Option M := fun u =>
  if Delivers G adv r u w then alg.send u (st u) w else none

/-- `state G alg adv inp r u`: the state of `u` after `r` rounds. (The states of crashed nodes
are irrelevant: they are never observed.) -/
noncomputable def state : ℕ → V → S
  | 0, u => alg.init u (inp u)
  | r + 1, w => alg.trans w (state r w) (inbox G alg adv (state r) r w)

theorem state_zero (u : V) : state G alg adv inp 0 u = alg.init u (inp u) := rfl

theorem state_succ (r : ℕ) (w : V) :
    state G alg adv inp (r + 1) w = alg.trans w (state G alg adv inp r w)
      (inbox G alg adv (state G alg adv inp r) r w) := rfl

/-- `u`'s first output is `o`. -/
def Decides (u : V) (o : O) : Prop :=
  ∃ r, alg.out u (state G alg adv inp r u) = some o ∧
    ∀ r' < r, alg.out u (state G alg adv inp r' u) = none

end Run

/-- **Crash consensus** (Section 1) for inputs in `In`, with at most `f` crash faults. -/
def SolvesOn (G : Digraph V) (f : ℕ) (In : Set I) (alg : Algorithm V I M S I) : Prop :=
  ∀ adv : Adversary V, adv.Admissible f → ∀ inp : V → I, (∀ u, inp u ∈ In) →
    -- termination
    (∀ u, adv.crash u = none → ∃ o, Decides G alg adv inp u o) ∧
    -- agreement
    (∀ u w o o', adv.crash u = none → adv.crash w = none → Decides G alg adv inp u o →
      Decides G alg adv inp w o' → o = o') ∧
    -- validity
    (∀ u o, adv.crash u = none → Decides G alg adv inp u o → ∃ w, inp w = o)

/-- Crash consensus for arbitrary inputs. -/
def Solves (G : Digraph V) (f : ℕ) (alg : Algorithm V I M S I) : Prop :=
  SolvesOn G f Set.univ alg

/-! ## Basic facts -/

section Facts

variable {G : Digraph V} {alg : Algorithm V I M S O} {adv : Adversary V}

theorem decides_unique {inp : V → I} {u : V} {o o' : O} (h : Decides G alg adv inp u o)
    (h' : Decides G alg adv inp u o') : o = o' := by
  obtain ⟨r, hr, hlt⟩ := h
  obtain ⟨r', hr', hlt'⟩ := h'
  rcases lt_trichotomy r r' with hrr | rfl | hrr
  · simp [hlt' r hrr] at hr
  · exact Option.some_injective _ (hr.symm.trans hr')
  · simp [hlt r' hrr] at hr'

/-- Decisions only depend on the node's own sequence of states. -/
theorem decides_congr {inp inp' : V → I} {u : V}
    (h : ∀ r, state G alg adv inp r u = state G alg adv inp' r u) {o : O} :
    Decides G alg adv inp u o ↔ Decides G alg adv inp' u o := by
  simp [Decides, h]

/-- A node has a decision as soon as it has some output. -/
theorem decides_of_out {inp : V → I} {u : V} {r : ℕ} {o : O}
    (h : alg.out u (state G alg adv inp r u) = some o) : ∃ o', Decides G alg adv inp u o' := by
  classical
  have hex : ∃ r, (alg.out u (state G alg adv inp r u)).isSome := ⟨r, by simp [h]⟩
  obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp (Nat.find_spec hex)
  refine ⟨o', Nat.find hex, ho', fun r' hr' => ?_⟩
  have := Nat.find_min hex hr'
  simpa using this

/-- **Indistinguishability.** If the inputs agree on a set `X` of nodes that only hears from
`X` (every delivery into `X` comes from `X`), then the states agree on `X` forever. -/
theorem state_eq_of_closed {inp inp' : V → I} {X : Set V}
    (hX : ∀ r u w, Delivers G adv r u w → w ∈ X → u ∈ X) (hinp : ∀ u ∈ X, inp u = inp' u) :
    ∀ r, ∀ u ∈ X, state G alg adv inp r u = state G alg adv inp' r u := by
  intro r
  induction r with
  | zero => intro u hu; simp [state_zero, hinp u hu]
  | succ r ih =>
    intro w hw
    rw [state_succ, state_succ, ih w hw]
    congr 1
    funext u
    unfold inbox
    split_ifs with h
    · rw [ih u (hX r u w h hw)]
    · rfl

end Facts

end CrashConsensusDigraph
