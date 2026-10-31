import Papers.PODC2010.TruncatedGaleShapley.Theorems

/-!
# Convergence to a stable matching (§5.1) and the stable matching `M_∞`

* `exists_quiet`: some round `z ≥ 1` loses no edge; then every unmatched red node has an empty
  list (`Quiet`), `M_z` is stable (`Inv.isStable_of_quiet`, §5.1) and the run is constant from `z`
  on (`run_eq_of_quiet`). `M_∞ = M_z`.
* §6.3: `card_matched_mono` (`|M_j| ≤ |M_i|` for `1 ≤ j ≤ i`: a matched blue node stays matched)
  and `card_matched_le_add_potR` (`|M_i| ≤ |M_j| + f_j(R)` for `1 ≤ j ≤ i`, unit weights: a red node
  with an empty list stays unmatched).
-/

namespace Podc.TruncatedGaleShapley

open Finset

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Bicoloured

variable {I : Bicoloured V}

/-- Every unmatched red node has an empty candidate list. -/
def Quiet (I : Bicoloured V) (s : State V) : Prop :=
  ∀ r, I.red r = true → s.p r = none → s.C r = ∅

/-- In a quiet state no edge is unstable (§5.1). -/
lemma Inv.isStable_of_quiet {s : State V} (hs : I.Inv s) (hq : I.Quiet s) : I.IsStable s.p := by
  rintro u v ⟨hv, hu1, hu2⟩
  -- orient the edge red → blue
  wlog hu : I.red u = true generalizing u v
  · have hvr : I.red v = true := red_of_mem_blue hv (by simpa using hu)
    exact this v u (I.symm hv) hu2 hu1 hvr
  by_cases hvC : v ∈ s.C u
  · rcases hpu : s.p u with _ | b
    · rw [hq u hu hpu] at hvC; simp at hvC
    · rw [hpu] at hu1
      have hbest := (hs.red_matched u b hu hpu).2
      exact absurd ((I.best_spec hbest).2 v hvC) (not_le.2 hu1)
  · obtain ⟨r₀, h₀, hlt⟩ := hs.lost u v hu hv hvC
    rw [h₀] at hu2
    exact absurd hu2 (not_lt.2 hlt.le)

/-- A quiet state is a fixed point of the rounds. -/
lemma Inv.round_eq_of_quiet {s : State V} (hs : I.Inv s) (hq : I.Quiet s) : I.round s = s := by
  -- no red node has an outstanding proposal
  have hc : ∀ r, I.red r = true → s.c r = none := by
    intro r hr
    rcases hp : s.p r with _ | b
    · rw [hs.red_unmatched r hr hp, hq r hr hp]; exact (I.best_eq_none).2 rfl
    · exact hs.c_eq_none hr hp
  have hbt : ∀ v, I.red v = false → (I.blueTurn s).p v = s.p v := by
    intro v hv
    apply I.blueTurn_p_empty
    rintro ⟨r, hr⟩
    obtain ⟨hrN, hcr⟩ := I.mem_proposers.1 hr
    rw [hc r (red_of_mem_blue hrN hv)] at hcr; cases hcr
  -- every red node keeps its state
  have hred : ∀ v, I.red v = true →
      (I.round s).C v = s.C v ∧ (I.round s).p v = s.p v ∧ (I.round s).c v = s.c v := by
    intro v hv
    rcases hs.red_outcome hv with ⟨hC, hp, hc', -⟩ | ⟨b, -, hcb, -⟩ | ⟨b, -, hcb, hbt', -⟩
    · exact ⟨hC, hp, hc'⟩
    · rw [hc v hv] at hcb; cases hcb
    · exfalso
      rcases hcb with hcb | hcb
      · rw [hc v hv] at hcb; cases hcb
      · have hb := blue_of_mem_red (hs.p_mem v b hcb) hv
        rw [hbt b hb, hs.p_symm v b hcb] at hbt'; exact hbt' rfl
  ext1 <;> funext v <;> cases hv : I.red v
  · exact I.round_C_blue s hv
  · exact (hred v hv).1
  · exact (I.redTurn_blue _ hv).2.1
  · exact (hred v hv).2.2
  · rw [round_p_blue _ _ hv, hbt v hv]
  · exact (hred v hv).2.1

/-! ### Existence of a quiet round -/

/-- The total length of the candidate lists. -/
def listSum (I : Bicoloured V) (s : State V) : ℕ := ∑ r ∈ I.reds, (s.C r).card

lemma Inv.card_C_round_le {s : State V} (hs : I.Inv s) {r : V} (hr : I.red r = true) :
    ((I.round s).C r).card ≤ (s.C r).card ∧
      (((I.round s).C r).card = (s.C r).card → (I.round s).p r = none → (I.round s).C r = ∅) := by
  rcases hs.red_outcome hr with ⟨hC, hp, -, ⟨b, hb, -⟩ | ⟨-, -, hCe⟩⟩ |
      ⟨b, -, -, -, hC, hp, -⟩ | ⟨b, hbest, -, -, hC, -, -⟩
  · refine ⟨by rw [hC], fun _ h => ?_⟩; rw [hp, hb] at h; cases h
  · exact ⟨by rw [hC], fun _ _ => hC.trans hCe⟩
  · refine ⟨by rw [hC], fun _ h => ?_⟩; rw [hp] at h; cases h
  · have hb := I.best_mem hbest
    rw [hC, card_erase_of_mem hb]
    have : 0 < (s.C r).card := card_pos.2 ⟨b, hb⟩
    exact ⟨Nat.sub_le _ _, fun h => by omega⟩

lemma Inv.listSum_round_le {s : State V} (hs : I.Inv s) :
    listSum I (I.round s) ≤ listSum I s :=
  sum_le_sum fun _ hr => (hs.card_C_round_le (I.mem_reds.1 hr)).1

lemma Inv.quiet_of_listSum_eq {s : State V} (hs : I.Inv s)
    (h : listSum I (I.round s) = listSum I s) : I.Quiet (I.round s) := by
  intro r hr hp
  have heq := (sum_eq_sum_iff_of_le fun r hr => (hs.card_C_round_le (I.mem_reds.1 hr)).1).1 h
  exact (hs.card_C_round_le hr).2 (heq r (I.mem_reds.2 hr)) hp

/-- §5.1: some round `z ≥ 1` is quiet. -/
theorem exists_quiet (I : Bicoloured V) : ∃ z, 1 ≤ z ∧ I.Quiet (I.run z) := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hlt : ∀ k, listSum I (I.run (k + 1 + 1)) < listSum I (I.run (k + 1)) := by
    intro k
    have hs := I.inv_run (i := k + 1) (by omega)
    rw [run_succ]
    refine lt_of_le_of_ne hs.listSum_round_le fun h => ?_
    have hq := hs.quiet_of_listSum_eq h
    rw [← run_succ] at hq
    exact hne (k + 1 + 1) (by omega) hq
  have hk : ∀ k, listSum I (I.run (k + 1)) + k ≤ listSum I (I.run 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => have := hlt k; omega
  have := hk (listSum I (I.run 1) + 1)
  omega

/-- Once quiet, the run stays constant. -/
lemma run_eq_of_quiet {z : ℕ} (hz : 1 ≤ z) (hq : I.Quiet (I.run z)) {i : ℕ} (hi : z ≤ i) :
    I.run i = I.run z := by
  induction i, hi using Nat.le_induction with
  | base => rfl
  | succ i hi ih => rw [run_succ, ih, (I.inv_run hz).round_eq_of_quiet hq]

/-- **§5.1.** The algorithm converges: there is a round `z` after which the state no longer changes,
and the matching `M_z` (`= M_∞`) is stable. -/
theorem exists_stable (I : Bicoloured V) :
    ∃ z, 1 ≤ z ∧ I.IsStable (I.run z).p ∧ ∀ i, z ≤ i → I.run i = I.run z := by
  obtain ⟨z, hz, hq⟩ := exists_quiet I
  exact ⟨z, hz, (I.inv_run hz).isStable_of_quiet hq, fun i hi => run_eq_of_quiet hz hq hi⟩

/-! ### Size of the matching across rounds (§6.3) -/

lemma blueW_round_mono {s : State V} (hs : I.Inv s) :
    I.blueW s (fun _ => 1) ≤ I.blueW (I.round s) (fun _ => 1) := by
  refine sum_le_sum fun b hb => ?_
  have hb := I.mem_blues.1 hb
  rcases hp : s.p b with _ | r₀
  · have : nodeW s (fun _ => 1) b = 0 := by simp [nodeW, hp]
    rw [this]; exact nodeW_nonneg I.respectsPrefs_one _ _
  · obtain ⟨q, hq, -⟩ := hs.blue_mono hb hp
    simp [nodeW, hp, round_p_blue _ _ hb, hq]

/-- `|M_j| ≤ |M_i|` for `1 ≤ j ≤ i`: matched blue nodes stay matched. -/
theorem size_mono {j i : ℕ} (hj : 1 ≤ j) (hji : j ≤ i) :
    I.blueW (I.run j) (fun _ => 1) ≤ I.blueW (I.run i) (fun _ => 1) := by
  induction i, hji using Nat.le_induction with
  | base => exact le_rfl
  | succ i hi ih =>
    rw [run_succ]; exact ih.trans (blueW_round_mono (I.inv_run (hj.trans hi)))

/-- A red node that is unmatched with an empty list stays so. -/
lemma Inv.stuck_round {s : State V} (hs : I.Inv s) {r : V} (hr : I.red r = true)
    (hp : s.p r = none) (hC : s.C r = ∅) : (I.round s).p r = none ∧ (I.round s).C r = ∅ := by
  rcases hs.red_outcome hr with ⟨hC', hp', -⟩ | ⟨b, -, hcb, -⟩ | ⟨b, hbest, -⟩
  · exact ⟨hp'.trans hp, hC'.trans hC⟩
  · have := hs.red_unmatched r hr hp
    rw [hC, hcb, (I.best_eq_none).2 rfl] at this; cases this
  · rw [hC, (I.best_eq_none).2 rfl] at hbest; cases hbest

lemma stuck_run {j i : ℕ} (hj : 1 ≤ j) (hji : j ≤ i) {r : V} (hr : I.red r = true)
    (hp : (I.run j).p r = none) (hC : (I.run j).C r = ∅) :
    (I.run i).p r = none ∧ (I.run i).C r = ∅ := by
  induction i, hji using Nat.le_induction with
  | base => exact ⟨hp, hC⟩
  | succ i hi ih =>
    rw [run_succ]; exact (I.inv_run (hj.trans hi)).stuck_round hr ih.1 ih.2

/-- `|M_i| ≤ |M_j| + f_j(R)` (unit weights) for `1 ≤ j ≤ i`: a red node matched at the end of
round `i` was matched at the end of round `j` or had a nonempty list then (§6.3). -/
theorem size_le_add_potR {j i : ℕ} (hj : 1 ≤ j) (hji : j ≤ i) :
    I.blueW (I.run i) (fun _ => 1) ≤
      I.blueW (I.run j) (fun _ => 1) + I.potR (I.run j) (fun _ => 1) := by
  have hred : ∀ k, I.blueW (I.run k) (fun _ => 1) = ∑ r ∈ I.reds, nodeW (I.run k) (fun _ => 1) r :=
    fun k => by
      rw [← sum_matchingEdges_eq_blueW (isMatching_run k), matchingEdges_sum (isMatching_run k) _ true]
      rfl
  rw [hred, hred, potR, ← sum_add_distrib]
  refine sum_le_sum fun r hr => ?_
  have hr := I.mem_reds.1 hr
  have hle1 : nodeW (I.run i) (fun _ => 1) r ≤ 1 := by unfold nodeW; split <;> simp
  rcases hp : (I.run j).p r with _ | b
  · have h0 : nodeW (I.run j) (fun _ => 1) r = 0 := by simp [nodeW, hp]
    rw [h0, zero_add, pot_of_unmatched hp]
    rcases hb : I.best r ((I.run j).C r) with _ | x
    · have hC := (I.best_eq_none).1 hb
      have := (stuck_run hj hji hr hp hC).1
      simp [nodeW, this]
    · simpa using hle1
  · have h1 : nodeW (I.run j) (fun _ => 1) r = 1 := by simp [nodeW, hp]
    rw [h1, pot_of_matched hp]; simpa using hle1

end Bicoloured

end Podc.TruncatedGaleShapley
