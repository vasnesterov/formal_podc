import Papers.PODC2016.DynamicMIS.Theorem1
import Podc.Local.LocallyIterative
import Podc.Local.Locality
import Mathlib

/-!
# Corollary 6: the direct distributed implementation

The *direct* implementation of the template (Algorithm 1) in the synchronous model: after the
topology change, in every round every node recomputes its MIS state from its earlier neighbours'
current states by the greedy rule (`v ∈ M ↔ v present ∧ no earlier neighbour in M`), starting from
the old states. This is a SET-LOCAL algorithm on the new graph (`directAlg`, `run_directAlg`; model
`Cslib/Computability/Distributed/Local/LocallyIterative.lean`, the state of a node is its rank, presence and MIS bit).

We show (`directRun_eq_of_le`, `directRun_notMem_infl`) that the run reaches the new greedy MIS
after
at most `|S|` rounds and that only nodes of `S` ever change state, so by Theorem 1 the expected
number of rounds and of adjustments are both at most one (`corollary6_rounds`,
`expected_adjustments_le_one`). The asynchronous variant of Corollary 6 is not formalized.
-/

open Finset SimpleGraph
open scoped BigOperators

namespace DynamicMIS

variable {V : Type*}

/-- One synchronous round of the direct implementation on `G[A]` with ranks `r`. -/
def directStep (G : SimpleGraph V) (A : Set V) (r : V → ℕ) (s : Set V) : Set V :=
  {v | v ∈ A ∧ ∀ w, G.Adj w v → r w < r v → w ∉ s}

/-- The states after `t` rounds of the direct implementation, starting from `s₀`. -/
def directRun (G : SimpleGraph V) (A : Set V) (r : V → ℕ) (s₀ : Set V) (t : ℕ) : Set V :=
  (directStep G A r)^[t] s₀

theorem directRun_succ (G : SimpleGraph V) (A : Set V) (r : V → ℕ) (s₀ : Set V) (t : ℕ) :
    directRun G A r s₀ (t + 1) = directStep G A r (directRun G A r s₀ t) :=
  Function.iterate_succ_apply' _ _ _

/-! ### The direct implementation as a SET-LOCAL algorithm -/

open Classical in
/-- The direct implementation as a locally-iterative (SET-LOCAL) algorithm: a node's state is
`(rank, present, inMIS)`; it joins iff it is present and no neighbour of smaller rank is in. -/
noncomputable def directAlg : Cslib.LocallyIterative.Algorithm (ℕ × Bool × Bool) :=
  Cslib.LocallyIterative.Algorithm.ofStep fun x N =>
    (x.1, x.2.1, decide (x.2.1 = true ∧ ∀ y ∈ N, y.1 < x.1 → y.2.2 = false))

open Classical in
/-- Encoding of a state vector. -/
noncomputable def encode (A : Set V) (r : V → ℕ) (s : Set V) : V → ℕ × Bool × Bool :=
  fun v => (r v, decide (v ∈ A), decide (v ∈ s))

theorem run_directAlg (G : SimpleGraph V) (A : Set V) (r : V → ℕ) (s₀ : Set V) (t : ℕ) :
    directAlg.run G (encode A r s₀) t = encode A r (directRun G A r s₀ t) := by
  classical
  refine Cslib.LocallyIterative.Algorithm.run_semiconj G _ (F := directStep G A r)
    (e := encode A r) (fun s => ?_) s₀ t
  funext v
  simp only [encode, directStep, Cslib.LocallyIterative.forall_mem_nbrColors, Prod.mk.injEq,
    true_and]
  congr 1
  apply propext
  simp only [decide_eq_true_eq, Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ⟨fun h w hw hr hws => ?_, fun h w hw hr => ?_⟩
  · have := h w hw.symm hr
    simp [hws] at this
  · simpa using h w hw.symm hr

/-- The direct implementation is a LOCAL algorithm: the state of a node after `t` rounds only
depends on the graph and the initial states within distance `t`. -/
theorem directAlg_isLocal (t : ℕ) :
    Cslib.Local.IsLocal (V := V) t fun G s₀ v => directAlg.run G s₀ t v :=
  Cslib.LocallyIterative.Algorithm.run_isLocal _ _

/-! ### Convergence -/

variable [DecidableEq V] {c : Change V} {cfg : Config V} {r : V → ℕ}

/-- Shorthand: the run of the direct implementation after the change. -/
def directAfter (c : Change V) (cfg : Config V) (r : V → ℕ) : ℕ → Set V :=
  directRun (c.apply cfg).graph (c.apply cfg).nodes r (cfg.graph.greedyMIS cfg.nodes r)

omit [DecidableEq V] in
theorem directStep_greedyMIS (G : SimpleGraph V) (A : Set V) (r : V → ℕ) :
    directStep G A r (G.greedyMIS A r) = G.greedyMIS A r := by
  ext v; exact (greedyMIS_iff G A r).symm

open Classical in
/-- Main convergence statement: after `t` rounds, every node outside `S` and every node of `S`
with at most `t` nodes of `S` at or before it (in the order) has its final state. -/
theorem directAfter_mem_iff [Fintype V] (hr : Function.Injective r) (t : ℕ) (u : V)
    (hu : u ∉ infl c cfg r ∨
      #{w | w ∈ infl c cfg r ∧ r w ≤ r u} ≤ t) :
    u ∈ directAfter c cfg r t ↔ u ∈ (c.apply cfg).graph.greedyMIS (c.apply cfg).nodes r := by
  classical
  have hd := flipData c cfg hr
  by_cases hinv : InvariantAt (c.apply cfg).graph (c.apply cfg).nodes r
      (cfg.graph.greedyMIS cfg.nodes r) (c.vStar r)
  · -- nothing to do: the old states are already the new greedy MIS
    have heq : cfg.graph.greedyMIS cfg.nodes r =
        (c.apply cfg).graph.greedyMIS (c.apply cfg).nodes r := by
      refine eq_greedyMIS_of_isGreedy _ _ _ fun u => ?_
      by_cases hu : u = c.vStar r
      · subst hu; exact hinv
      · rw [hd.isGreedyExcept_old u hu, ← hd.rule_new_iff hu]
    have : ∀ t, directAfter c cfg r t = (c.apply cfg).graph.greedyMIS (c.apply cfg).nodes r := by
      intro t
      induction t with
      | zero => exact heq
      | succ t ih => rw [directAfter, directRun_succ, ← directAfter, ih, directStep_greedyMIS]
    rw [this]
  obtain ⟨-, hU⟩ := infl_eq hr hinv
  rw [hU] at hu
  have hfin := hd.isGreedyExcept_new
  have hold := hd.isGreedyExcept_old
  set U := (c.baseGraph cfg).influenced (c.baseNodes cfg) r (c.vStar r) with hUdef
  set fin := (c.apply cfg).graph.greedyMIS (c.apply cfg).nodes r with hfindef
  -- the counting function
  have hcount : ∀ w v, v ∈ U → r w < r v →
      #{w' | w' ∈ U ∧ r w' ≤ r w} < #{w' | w' ∈ U ∧ r w' ≤ r v} := by
    intro w v hv hwv
    refine Finset.card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact ⟨hy.1, hy.2.trans hwv.le⟩
    · have hvv : v ∈ ({w' | w' ∈ U ∧ r w' ≤ r v} : Finset V) := by simp [hv]
      have := hsub hvv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      omega
  -- membership in `fin` for determined nodes
  have hdet : ∀ u b, (c.baseGraph cfg).partialGreedy (c.baseNodes cfg) r (c.vStar r) u = some b →
      (u ∈ fin ↔ b = true) := fun u b h => mem_iff_of_partialGreedy_eq_some hfin u b h
  induction t generalizing u with
  | zero =>
    by_cases huU : u ∈ U
    · exfalso
      rcases hu with hu | hu
      · exact hu huU
      · have : u ∈ ({w | w ∈ U ∧ r w ≤ r u} : Finset V) := by simp [huU]
        have := Finset.card_pos.2 ⟨u, this⟩
        omega
    · by_contra hne
      by_cases h₁ : u ∈ cfg.graph.greedyMIS cfg.nodes r
      · exact huU (mem_influenced_of_mem_of_notMem hold hfin h₁ fun h₂ => hne (iff_of_true h₁ h₂))
      · exact huU (mem_influenced_of_mem_of_notMem hfin hold
          (by_contra fun h₂ => hne (iff_of_false h₁ h₂)) h₁)
  | succ t ih =>
    rw [directAfter, directRun_succ, ← directAfter]
    change u ∈ directStep _ _ _ _ ↔ _
    simp only [directStep, Set.mem_ofPred_eq]
    by_cases huU : u ∈ U
    · have hle : #{w | w ∈ U ∧ r w ≤ r u} ≤ t + 1 := hu.resolve_left (not_not.2 huU)
      rw [greedyMIS_iff]
      refine and_congr_right fun _ => forall_congr' fun w => forall_congr' fun hw =>
        forall_congr' fun hwr => not_congr (ih w ?_)
      by_cases hwU : w ∈ U
      · exact Or.inr (by have := hcount w u huU hwr; omega)
      · exact Or.inl hwU
    · have hux : u ≠ c.vStar r := fun h => huU (h ▸ self_mem_influenced _)
      rcases hval : (c.baseGraph cfg).partialGreedy (c.baseNodes cfg) r (c.vStar r) u with _ | b
      · exact absurd hval huU
      rw [hdet u b hval]
      cases b with
      | true =>
        obtain ⟨-, huA, hpred⟩ := partialGreedy_eq_some_true_iff.1 hval
        simp only [iff_true]
        refine ⟨(hd.nodes_new u hux).2 huA, fun w hw hwr hws => ?_⟩
        have hH := ((hd.pred_new u hux w).1 ⟨hw, hwr⟩).1
        have hwf := hpred w hH hwr
        have hwU : w ∉ U := fun h => by change _ = none at h; simp [h] at hwf
        exact absurd ((hdet w false hwf).1 ((ih w (Or.inl hwU)).1 hws)) (by simp)
      | false =>
        obtain ⟨-, h | ⟨z, hz, hzr, hzt⟩⟩ := partialGreedy_eq_some_false_iff.1 hval
        · simp only [Bool.false_eq_true, iff_false, not_and]
          exact fun hA => absurd ((hd.nodes_new u hux).1 hA) h
        · simp only [Bool.false_eq_true, iff_false, not_and, not_forall, not_not]
          intro _
          have hzU : z ∉ U := fun h => by change _ = none at h; simp [h] at hzt
          refine ⟨z, ((hd.pred_new u hux z).2 ⟨hz, hzr⟩).1, hzr, ?_⟩
          exact (ih z (Or.inl hzU)).2 ((hdet z true hzt).2 rfl)

/-- After `|S|` rounds the direct implementation has reached the new greedy MIS. -/
theorem directAfter_eq_of_le [Fintype V] (hr : Function.Injective r) {t : ℕ}
    (ht : (infl c cfg r).ncard ≤ t) :
    directAfter c cfg r t = (c.apply cfg).graph.greedyMIS (c.apply cfg).nodes r := by
  classical
  ext u
  refine directAfter_mem_iff hr t u (Or.inr (le_trans ?_ ht))
  rw [Set.ncard_eq_toFinset_card']
  exact Finset.card_le_card fun w hw => by simp_all

/-- Nodes outside `S` never change state during the direct implementation. -/
theorem directAfter_notMem_infl [Fintype V] (hr : Function.Injective r) (t : ℕ) {u : V}
    (hu : u ∉ infl c cfg r) :
    u ∈ directAfter c cfg r t ↔ u ∈ cfg.graph.greedyMIS cfg.nodes r :=
  (directAfter_mem_iff hr t u (Or.inl hu)).trans (directAfter_mem_iff hr 0 u (Or.inl hu)).symm

/-- The round complexity of the direct implementation: the first round from which on the states
are the new greedy MIS. -/
noncomputable def directRounds (c : Change V) (cfg : Config V) (r : V → ℕ) : ℕ :=
  sInf {T | ∀ t, T ≤ t →
    directAfter c cfg r t = (c.apply cfg).graph.greedyMIS (c.apply cfg).nodes r}

theorem directRounds_le [Fintype V] (hr : Function.Injective r) :
    directRounds c cfg r ≤ (infl c cfg r).ncard :=
  Nat.sInf_le fun _ ht => directAfter_eq_of_le hr ht

/-- **Corollary 6** (rounds). The direct synchronous implementation of the template stabilises in
at most one round in expectation. -/
theorem corollary6_rounds [Fintype V] (c : Change V) (cfg : Config V) :
    𝔼 π : V ≃ Fin (Fintype.card V), (directRounds c cfg (orderRank π) : ℚ) ≤ 1 :=
  expect_le_one_of_sum_le ((Finset.sum_le_sum fun π _ =>
    directRounds_le (orderRank_injective π)).trans (sum_ncard_infl_le c cfg))

/-- **Corollary 6** (adjustments): in expectation at most one node changes its output; see
`expected_adjustments_le_one`. Moreover, every node that changes its state in some round of the
direct implementation belongs to `S`. -/
theorem corollary6_changing_subset [Fintype V] (hr : Function.Injective r) (t : ℕ) :
    {u | ¬ (u ∈ directAfter c cfg r t ↔ u ∈ cfg.graph.greedyMIS cfg.nodes r)} ⊆ infl c cfg r :=
  fun _ hu => by_contra fun h => hu (directAfter_notMem_infl hr t h)

end DynamicMIS
