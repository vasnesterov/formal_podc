import Papers.PODC2022.DominatingSetArboricity.PartialDS

/-!
# The deterministic `(2α+1)(1+ε)`-approximation (Theorems 1.1 and 3.1, Claim 3.3)

Phase 1 is the partial dominating set procedure of Lemma 4.1 with `λ = 1/((2α+1)(1+ε))`;
phase 2 adds, for every vertex `v` not dominated by `S`, a vertex of `N⁺_v` of weight `τ_v`.
-/

set_option linter.unusedSectionVars false

namespace DominatingSetArboricity

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Phase 2: one minimum-weight dominator `tauNode v ∈ N⁺_v` for every vertex `v ∉ N⁺_S`. -/
noncomputable def completion (w : V → ℝ) (S : Finset V) : Finset V :=
  (univ.filter fun v => v ∉ dom G S).image (tauNode G w)

/-- The parameter `λ = 1/((2α+1)(1+ε))` of Theorem 1.1. -/
noncomputable def detLam (α : ℕ) (ε : ℝ) : ℝ := 1 / ((2 * α + 1) * (1 + ε))

/-- The output of the deterministic algorithm of Theorem 1.1. -/
noncomputable def detDS (α : ℕ) (ε : ℝ) (w : V → ℝ) : Finset V :=
  (partialDS G ε (detLam α ε) w).S ∪ completion G w (partialDS G ε (detLam α ε) w).S

variable {G}

theorem isDominating_union_completion (w : V → ℝ) (S : Finset V) :
    IsDominating G (S ∪ completion G w S) := by
  intro v
  by_cases hv : v ∈ dom G S
  · obtain ⟨u, hu, h⟩ := mem_dom.1 hv
    exact ⟨u, mem_union_left _ hu, h⟩
  · exact ⟨tauNode G w v, mem_union_right _ (mem_image.2 ⟨v, by simp [hv], rfl⟩),
      tauNode_mem w v⟩

theorem wt_union_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A B : Finset V) :
    wt w (A ∪ B) ≤ wt w A + wt w B := by
  unfold wt
  rw [← sum_union_inter]
  linarith [sum_nonneg fun v (_ : v ∈ A ∩ B) => hw v]

theorem wt_completion_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (S : Finset V) :
    wt w (completion G w S) ≤ ∑ v ∈ univ.filter (fun v => v ∉ dom G S), tau G w v := by
  unfold wt completion
  refine (sum_image_le_of_nonneg fun u _ => hw u).trans (le_of_eq ?_)
  exact sum_congr rfl fun v _ => w_tauNode w v

/-- **Theorem 1.1** (approximation part; Claim 3.3 for unit weights). Let `G` have an orientation
with out-degree `≤ α` (e.g. arboricity `≤ α`, see `theorem_1_1_arboricity`), `α ≥ 1`, `ε > 0`, and
`w ≥ 0`. The deterministic algorithm outputs a dominating set whose weight is at most
`(2α+1)(1+ε)` times the weight of any dominating set. The number of iterations of phase 1 is
`numIter G ε (detLam α ε) ≤ 1 + 2 log(max 1 ((Δ+1)/((2α+1)(1+ε))))/ε` (`numIter_le`). -/
theorem theorem_1_1 {α : ℕ} (o : G.OutOrientation α) (hα : 1 ≤ α) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {ε : ℝ} (hε : 0 < ε) :
    IsDominating G (detDS G α ε w) ∧
      ∀ D, IsDominating G D → wt w (detDS G α ε w) ≤ (2 * α + 1) * (1 + ε) * wt w D := by
  refine ⟨isDominating_union_completion _ _, fun D hD => ?_⟩
  set lam := detLam α ε
  set p := partialDS G ε lam w
  have hαr : (1 : ℝ) ≤ α := by exact_mod_cast hα
  have hlam0 : 0 < lam := by unfold lam detLam; positivity
  have hlam' : lam < 1 / ((α + 1) * (1 + ε)) := by
    unfold lam detLam
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  obtain ⟨hpack, ha, hb⟩ := lemma_4_1 o hw hε hlam0.le hlam'
  set K : ℝ := (2 * α + 1) * (1 + ε)
  have hK : α * (1 / (1 + ε) - lam * (α + 1))⁻¹ = K := by
    unfold lam detLam K
    have : (1 : ℝ) + ε ≠ 0 := by linarith
    have : (2 * α + 1 : ℝ) ≠ 0 := by positivity
    have : (α : ℝ) ≠ 0 := by positivity
    field_simp
    ring_nf
    field_simp
  have hKlam : K * lam = 1 := by
    unfold K lam detLam; field_simp
  rw [hK] at ha
  -- phase 2 is paid by the packing values of the undominated vertices
  have h2 : ∑ v ∈ univ.filter (fun v => v ∉ dom G p.S), tau G w v ≤
      K * ∑ v ∈ univ.filter (fun v => v ∉ dom G p.S), p.x v := by
    rw [mul_sum]
    refine sum_le_sum fun v hv => ?_
    have := hb v (mem_filter.1 hv).2
    calc tau G w v = K * (lam * tau G w v) := by rw [← mul_assoc, hKlam, one_mul]
      _ ≤ K * p.x v := by gcongr
  have hsplit : ∑ v ∈ dom G p.S, p.x v + ∑ v ∈ univ.filter (fun v => v ∉ dom G p.S), p.x v =
      ∑ v, p.x v := by
    rw [← sum_filter_add_sum_filter_not univ (fun v => v ∈ dom G p.S)]
    simp
  calc wt w (detDS G α ε w) ≤ wt w p.S + wt w (completion G w p.S) := wt_union_le hw _ _
    _ ≤ K * ∑ v ∈ dom G p.S, p.x v + K * ∑ v ∈ univ.filter (fun v => v ∉ dom G p.S), p.x v := by
        gcongr
        exact (wt_completion_le hw _).trans h2
    _ = K * ∑ v, p.x v := by rw [← mul_add, hsplit]
    _ ≤ K * wt w D := by
        gcongr
        exact sum_le_wt_of_isPacking G hpack hD

/-- **Theorem 1.1**, stated for graphs of arboricity at most `α` (Observation 3.5 provides the
orientation used in the analysis). -/
theorem theorem_1_1_arboricity {α : ℕ} (hG : G.ArboricityLE α) (hα : 1 ≤ α) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {ε : ℝ} (hε : 0 < ε) :
    IsDominating G (detDS G α ε w) ∧
      ∀ D, IsDominating G D → wt w (detDS G α ε w) ≤ (2 * α + 1) * (1 + ε) * wt w D :=
  theorem_1_1 hG.hasOutDegLE.some hα hw hε

/-- **Theorem 3.1** (unweighted case, approximation part): with unit weights the output is a
dominating set of size at most `(2α+1)(1+ε)` times the size of any dominating set. -/
theorem theorem_3_1 {α : ℕ} (hG : G.ArboricityLE α) (hα : 1 ≤ α) {ε : ℝ} (hε : 0 < ε) :
    IsDominating G (detDS G α ε 1) ∧
      ∀ D, IsDominating G D → ((detDS G α ε 1).card : ℝ) ≤ (2 * α + 1) * (1 + ε) * D.card := by
  obtain ⟨h1, h2⟩ := theorem_1_1_arboricity (w := 1) hG hα (fun _ => zero_le_one) hε
  refine ⟨h1, fun D hD => ?_⟩
  simpa [wt] using h2 D hD

/-- Non-vacuity of the orientation hypothesis: every graph has an orientation with out-degree
`≤ Δ` (orient every edge both ways). -/
def trivialOrientation (G : SimpleGraph V) [DecidableRel G.Adj] : G.OutOrientation G.maxDegree where
  out v := G.neighborFinset v
  adj_of_mem _ _ h := (mem_neighborFinset _ _ _).1 h
  mem_or_mem _ _ h := Or.inl ((mem_neighborFinset _ _ _).2 h)
  card_out_le v := (card_neighborFinset_eq_degree G v).le.trans (G.degree_le_maxDegree v)

/-- The number of iterations of phase 1 in Theorem 1.1: `O(log(Δ/α)/ε)`. -/
theorem numIter_detLam_le {α : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (numIter G ε (detLam α ε) : ℝ) ≤
      1 + 2 * Real.log (max 1 ((G.maxDegree + 1) / (2 * α + 1))) / ε := by
  refine (numIter_le hε hε1).trans ?_
  have h : detLam α ε * (G.maxDegree + 1) ≤ (G.maxDegree + 1) / (2 * α + 1) := by
    unfold detLam
    rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : (0 : ℝ) ≤ (G.maxDegree + 1) * (2 * α + 1) := by positivity
    nlinarith
  have := Real.log_le_log (by positivity) (max_le_max (le_refl (1 : ℝ)) h)
  gcongr

end DominatingSetArboricity
