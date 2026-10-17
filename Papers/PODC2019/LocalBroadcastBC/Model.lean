import Cslib.Computability.Distributed.Byzantine.LockStep.Cover
import Podc.Computability.Distributed.Byzantine.LockStep.Basic
import Podc.Computability.Distributed.Byzantine.LockStep.Cover
import Cslib.Computability.Distributed.Byzantine.LockStep.Agreement
import Cslib.Foundations.Combinatorics.SimpleGraph.VertexConnectivity
import Mathlib
import Cslib.Computability.Distributed.Byzantine.LockStep.Parallel
import Podc.Computability.Distributed.Byzantine.Specs

/-!
# The local broadcast model (Khan–Naqvi–Vaidya, PODC 2019), on top of CSLib's lock-step model

We reuse CSLib's synchronous lock-step model `Cslib.Byzantine.LockStep` (history-based
deterministic protocols on a `SimpleGraph`, static Byzantine set, adversary messages
`adv r p q`). The *local broadcast* model is the restriction in which **every** message is received
identically by all neighbours of its sender:

* honest parties broadcast: `Protocol.IsBroadcast` (the message does not depend on the receiver);
* Byzantine parties broadcast as well: `Scenario.IsLocalBroadcast` (`adv r p q` does not depend
  on `q`); this is the whole restriction of the adversary (no equivocation).

`SolvesLB G alg Z spec` / `SolvableLB G Z spec` are the corresponding solvability notions;
the threshold adversary is the shared `atMost f` (at most `f` Byzantine nodes) and `Consensus` is
the specification of Section 3 of the paper (agreement, validity "the output is the input of some
non-faulty node", termination).

The impossibility proofs use FLM-style covering systems (CSLib `CoverSystem`) in which every
Byzantine node is simulated by a *single* node of the cover; the corresponding adversary is a
local broadcast adversary (`CoverSystem.lbScenario`, `decides_lbScenario_iff`). Two-copy covers
`twoCopy` (every node has copies `(u, false)` and `(u, true)`) suffice for the paper.
-/

open Cslib.Byzantine.LockStep

namespace LocalBroadcastBC

universe u

variable {V I M O : Type*}

/-- Honest messages are local broadcasts: a party sends the same message to all neighbours. -/
def IsBroadcast (alg : Protocol V I M O) : Prop :=
  ∀ p x h q q', alg.send p x h q = alg.send p x h q'

/-- The adversary obeys local broadcast: a Byzantine party sends the same message to all its
neighbours in every round. -/
def IsLocalBroadcast (s : Scenario V I M) : Prop :=
  ∀ r p q q', s.adv r p q = s.adv r p q'

/-- `alg` solves `spec` on `G` in the local broadcast model, against every admissible Byzantine
set of `Z` (reliable links, no equivocation). -/
def SolvesLB (G : SimpleGraph V) (alg : Protocol V I M O) (Z : AdvStructure V)
    (spec : Spec V I O) : Prop :=
  ∀ s : Scenario V I M, s.byz ∈ Z → s.Reliable → IsLocalBroadcast s →
    spec s.input s.honest (Decides G alg s)

/-- A problem is solvable on `G` in the local broadcast model if some broadcast protocol (with
some message type) solves it. -/
def SolvableLB {V : Type u} {I O : Type*} (G : SimpleGraph V) (Z : AdvStructure V) (spec : Spec V I O) :
    Prop :=
  ∃ (M : Type u) (alg : Protocol V I M O), IsBroadcast alg ∧ SolvesLB G alg Z spec

open Cslib.Byzantine in
/-- Byzantine consensus as in Section 3 of [KNV19]: termination, validity (the output of each
non-faulty node is the input of some non-faulty node) and agreement. -/
def Consensus {W : Type*} : Spec V W W := fun x H dec =>
  Problem.Termination H dec ∧
  Problem.InputValidity x H dec ∧
  Problem.Agreement H dec

/-- For binary values the paper's consensus specification is CSLib's Byzantine agreement `BA`
(as long as some node is non-faulty). -/
theorem consensus_iff_BA {x : V → Bool} {H : Set V} {dec : V → Bool → Prop}
    (hdec : ∀ p ∈ H, ∀ v w, dec p v → dec p w → v = w) :
    Consensus x H dec ↔ BA x H dec := by
  constructor
  · rintro ⟨hT, hV, hA⟩
    refine ⟨hT, fun v hv p hp => ?_, hA⟩
    obtain ⟨w, hw⟩ := hT p hp
    obtain ⟨q, hq, rfl⟩ := hV p hp w hw
    rwa [hv q hq] at hw
  · rintro ⟨hT, hV, hA⟩
    refine ⟨hT, fun p hp v hpv => ?_, hA⟩
    by_contra hne
    push Not at hne
    have hall : ∀ q ∈ H, x q = !v := fun q hq => by
      have := hne q hq; cases v <;> simpa using this
    have := hdec p hp _ _ hpv (hV (!v) hall p hp)
    cases v <;> simp at this

/-! ### Covering systems with a single copy of every Byzantine node -/

variable {Q : Type*}

namespace CoverSystem'

variable (C : CoverSystem V I Q) (G : SimpleGraph V) (alg : Protocol V I M O)

open Classical in
/-- The real scenario in which Byzantine parties `B` simulate the covering system: the honest
party `p` runs as the node `σ p`, the Byzantine party `b` *broadcasts* what the node `τ b` sends.
-/
noncomputable def lbScenario (B : Set V) (σ τ : V → Q) (x₀ : V → I) : Scenario V I M where
  byz := B
  input := fun p => if p ∈ B then x₀ p else C.xq (σ p)
  adv := fun r b _ => alg.send (C.φ (τ b)) (C.xq (τ b)) (C.hist G alg r (τ b)) b

/-- A lift of the honest parties in which all honest neighbours of a Byzantine party `b` listen
to the same node `τ b`. -/
structure LBLift (B : Set V) (σ τ : V → Q) : Prop where
  φ_σ : ∀ p, p ∉ B → C.φ (σ p) = p
  nbr_σ : ∀ p q, p ∉ B → q ∉ B → G.Adj p q → C.nbr (σ q) p = some (σ p)
  nbr_τ : ∀ b q, b ∈ B → q ∉ B → G.Adj b q → C.nbr (σ q) b = some (τ b)

variable {C G alg}

lemma lbScenario_isLocalBroadcast (B : Set V) (σ τ : V → Q) (x₀ : V → I) :
    IsLocalBroadcast (lbScenario C G alg B σ τ x₀) := fun _ _ _ _ => rfl

lemma lbScenario_reliable (B : Set V) (σ τ : V → Q) (x₀ : V → I) :
    (lbScenario C G alg B σ τ x₀).Reliable := fun _ _ _ h => h

/-- **Simulation lemma** (local broadcast version): honest parties have the histories of their
lifts. By local broadcast, the run is indistinguishable for honest parties from CSLib's covering
run `CoverSystem.scenario` (`hist_honest_congr`), which is the FLM simulation lemma. -/
theorem hist_lbScenario (hb : IsBroadcast alg) {B : Set V} {σ τ : V → Q}
    (hL : LBLift C G B σ τ) (x₀ : V → I) :
    ∀ r p, p ∉ B → hist G alg (lbScenario C G alg B σ τ x₀) r p = C.hist G alg r (σ p) := by
  intro r p hp
  refine (hist_honest_congr G alg (s := lbScenario C G alg B σ τ x₀)
    (s' := C.scenario G alg B σ x₀) rfl (fun _ _ => rfl) (fun _ _ _ _ _ _ => Iff.rfl)
    (fun r b q hb' hq hbq => ?_) r p hp).trans (C.hist_scenario ⟨hL.φ_σ, hL.nbr_σ⟩ x₀ r p hp)
  simp only [lbScenario, CoverSystem.scenario, hL.nbr_τ b q hb' hq hbq, Option.bind_some]
  exact hb _ _ _ _ _

/-- Honest parties decide exactly as their lifts do in the covering system. -/
theorem decides_lbScenario_iff (hb : IsBroadcast alg) {B : Set V} {σ τ : V → Q}
    (hL : LBLift C G B σ τ) (x₀ : V → I) {p : V} (hp : p ∉ B) (o : O) :
    Decides G alg (lbScenario C G alg B σ τ x₀) p o ↔ C.Decides G alg (σ p) o := by
  classical
  unfold Decides CoverSystem.Decides status
  apply FirstSome.congr
  intro r
  rw [hist_lbScenario hb hL x₀ r p hp]
  simp [lbScenario, hp, hL.φ_σ p hp]

lemma lbScenario_input (B : Set V) (σ τ : V → Q) (x₀ : V → I) {p : V} (hp : p ∉ B) :
    (lbScenario C G alg B σ τ x₀).input p = C.xq (σ p) := by
  classical
  simp [lbScenario, hp]

end CoverSystem'

/-- The two-copy covering system: node `(u, i)` runs the code of `u` with input `xq (u, i)` and
listens to the copy `(v, c u i v)` of each neighbour `v`. -/
def twoCopy (c : V → Bool → V → Bool) (xq : V × Bool → I) : CoverSystem V I (V × Bool) :=
  CoverSystem.doubleCover (fun u i v => some (c u i v)) xq

/-- Lifts into a two-copy cover: honest `p` runs as `(p, ℓ p)`, Byzantine `b` is simulated by
`(b, κ b)`. -/
theorem twoCopy_lift {G : SimpleGraph V} (c : V → Bool → V → Bool) (xq : V × Bool → I)
    (B : Set V) (ℓ κ : V → Bool)
    (hh : ∀ p q, p ∉ B → q ∉ B → G.Adj p q → c q (ℓ q) p = ℓ p)
    (hb : ∀ b q, b ∈ B → q ∉ B → G.Adj b q → c q (ℓ q) b = κ b) :
    CoverSystem'.LBLift (twoCopy c xq) G B (fun p => (p, ℓ p)) (fun b => (b, κ b)) where
  φ_σ _ _ := rfl
  nbr_σ p q hp hq hpq := by simp [twoCopy, hh p q hp hq hpq]
  nbr_τ b q hb' hq hbq := by simp [twoCopy, hb b q hb' hq hbq]

end LocalBroadcastBC
