import Papers.PODC2020.SSLERegular.EulerMain
import Papers.PODC2020.SSLERegular.StateCount

/-!
# Chen–Chen, *Self-Stabilizing Leader Election in Regular Graphs* (PODC 2020): main results

* SS-EulerCycle **as printed** fails (Lemma 3.1 / Theorem 3.3): `literal_not_solvesSSLE`
  (any graph with degrees `> k`), instance `literal_fails_on_complete` (`K_{2k+1}`).
* SS-EulerCycle **repaired** (virtual edge also usable when the scheduler picks its head as the
  initiator) is correct: `repaired_solvesSSLE` (global fairness), `repaired_selfStab`
  (reachability), `repaired_prob_one` (random scheduler, probability 1).
* SS-Tree fails (Theorem 4.3 / Lemma 4.2): `ssTree_not_solvesSSLE`, `ssTree_fails_on_complete`,
  `ssTree_prob_zero` (random scheduler).
* Lemma 2.1: `GProtocol.derc_lemma`. State counts: `card_estate`, `card_tstate`.
-/

open Finset Filter Topology

namespace SSLERegular

universe u

/-- **SS-EulerCycle as printed fails on `K_{2k+1}`** (a connected `2k`-regular graph), for every
`k ≥ 1` and every finite ring protocol with a leader and a non-leader state: no configuration is
valid output-stable and the protocol does not solve SSLE. -/
theorem literal_fails_on_complete {RS : Type*} [Finite RS] (R : RingProtocol RS) {k : ℕ}
    (hk : 1 ≤ k) (hR : ∀ a b, (R.δ a b).Nonempty) {r0 r1 : RS} (hr0 : R.lead r0 = false)
    (hr1 : R.lead r1 = true) :
    (⊤ : SimpleGraph (Fin (2 * k + 1))).IsRegularOfDegree (2 * k) ∧
    ¬ (ssEuler false k R).SolvesSSLE (⊤ : SimpleGraph (Fin (2 * k + 1))) (EState.out R) := by
  have hreg : (⊤ : SimpleGraph (Fin (2 * k + 1))).IsRegularOfDegree (2 * k) := by
    intro v; rw [SimpleGraph.complete_graph_degree]; simp
  refine ⟨hreg, (literal_not_solvesSSLE hR hk (fun v => by rw [hreg v]; omega)
    ⟨0, 1, by simp; omega⟩ hr0 hr1).1⟩

/-- **Repaired SS-EulerCycle under a random scheduler**: for every Markov kernel on
configurations whose positive-probability moves are exactly the protocol's steps (e.g. a uniformly
random ordered adjacent pair and a random outcome with full support), from every configuration
the probability of not being in a valid output-stable configuration after `t` steps tends to `0`. -/
theorem repaired_prob_one {RS : Type*} {k : ℕ} {V : Type u} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {R : RingProtocol RS}
    [Fintype (V → EState k RS)] [DecidableEq (V → EState k RS)]
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 2 * k) (hk : 1 ≤ k)
    (hR : ∀ a b, (R.δ a b).Nonempty) (hRS : RingSpec.{u} R) (r0 : RS)
    {T : Matrix (V → EState k RS) (V → EState k RS) ℝ} (hT : T ∈ Matrix.rowStochastic ℝ _)
    (hstep : ∀ C D, 0 < T C D → (ssEuler true k R).Step G C D)
    (hpos : ∀ C D, (ssEuler true k R).Step G C D → 0 < T C D) (C : V → EState k RS) :
    Tendsto (fun t => ∑ D ∈ (TS.setOf ((ssEuler true k R).ValidStable G (EState.out R)))ᶜ,
      (T ^ t) C D) atTop (𝓝 0) :=
  TS.tendsto_compl_of_reach GProtocol.validStable_closed hT hstep hpos
    (repaired_selfStab hconn hdeg hk hR hRS r0) C

/-- **SS-Tree under a random scheduler**: from the bad configuration of
`ssTree_all_roots_forever`, a valid output-stable configuration is reached with probability `0`
(at every time), for every Markov kernel supported on the protocol's steps. -/
theorem ssTree_prob_zero {RS : Type*} {k : ℕ} {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {R : RingProtocol RS}
    [Fintype (V → TState k RS)] [DecidableEq (V → TState k RS)]
    (hk : 2 ≤ k) (hV : 2 ≤ Fintype.card V) (hdeg : ∀ v, G.degree v ≤ k) (c : V → Fin (k ^ 2))
    (hinj : ∀ x u v, G.Adj x u → G.Adj x v → c u = c v → u = v) {r0 : RS}
    (hr0 : R.lead r0 = false) :
    ∃ C0 : V → TState k RS, ∀ {T : Matrix (V → TState k RS) (V → TState k RS) ℝ},
      T ∈ Matrix.rowStochastic ℝ _ → (∀ C D, 0 < T C D → (ssTree k R).Step G C D) →
      ∀ t, ∑ D ∈ TS.setOf ((ssTree k R).ValidStable G TState.isLeader), (T ^ t) C0 D = 0 := by
  obtain ⟨C0, hC0⟩ := ssTree_all_roots_forever (G := G) (R := R) hk hdeg c hinj hr0
  refine ⟨C0, fun hT hstep t => TS.prob_eq_zero_of_not_reach hT hstep (fun D hD hv => ?_) t⟩
  have h1 := hv.2
  unfold GProtocol.numLeaders at h1
  rw [Finset.filter_true_of_mem (fun v _ => hC0 D hD v), Finset.card_univ] at h1
  omega

end SSLERegular
