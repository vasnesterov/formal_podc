import Papers.PODC2018.LocalISApproximation.Theorem1

/-!
# Theorem 3: the Turán bound has performance ratio `(2Δ+1)²/(8Δ)`

* `turan_le_caroWei`: `Turán(G) ≤ CaroWei(G)` (Lemma 1 = Cauchy–Schwarz with `w = 1`,
  `x_v = d(v)+1`), hence `turan_le_indepNum` (Turán's theorem).
* `indepNum_le_turan`: the upper bound `α ≤ (2Δ+1)²/(8Δ) · Turán(G)` (proof of Theorem 3).
* `tight_of_params`: any graph with `Δ(G) ≤ Δ`, `n = 4Δ`, `|E| = (2Δ-1)Δ` and an independent set of
  size `2Δ+1` attains the ratio; `exampleGraph D` (`Δ = D+1`) is the paper's example: a
  `Δ`-regular bipartite circulant on `A ∪ B` (`|A| = |B| = 2Δ-1`) plus two isolated vertices `C`.
* `theorem3`: Theorem 3 with tightness, for every `Δ ≥ 1`.
-/

open Finset SimpleGraph

namespace Podc.LocalISApproximation

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- `∑_v (d(v)+1) = 2|E| + n`. -/
theorem sum_degree_add_one :
    ∑ v, ((G.degree v : ℝ) + 1) = 2 * (#G.edgeFinset : ℝ) + Fintype.card V := by
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
  have := G.sum_degrees_eq_twice_card_edges
  rw [← Nat.cast_sum, this]; push_cast; ring

omit [DecidableEq V] in
/-- `Turán(G) ≤ CaroWei(G)`: Lemma 1 (Cauchy–Schwarz) with `w_v = 1`, `x_v = d(v)+1`. -/
theorem turan_le_caroWei : turan G ≤ caroWei G := by
  have h := Finset.sq_sum_div_le_sum_sq_div (univ : Finset V) (fun _ => (1 : ℝ))
    (g := fun v => (G.degree v : ℝ) + 1) (fun v _ => by positivity)
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, one_pow] at h
  rw [turan, ← sum_degree_add_one]
  exact h

/-- Turán's theorem `α(G) ≥ Turán(G)`. -/
theorem turan_le_indepNum : turan G ≤ G.indepNum := turan_le_caroWei.trans caroWei_le_indepNum

/-- **Theorem 3 (upper bound).** If `Δ ≥ 1` and all degrees are at most `Δ`, then
`α(G) ≤ (2Δ+1)²/(8Δ) · Turán(G)`. -/
theorem indepNum_le_turan {Δ : ℕ} (hΔ : 1 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) :
    (G.indepNum : ℝ) ≤ (2 * Δ + 1) ^ 2 / (8 * Δ) * turan G := by
  obtain ⟨I, hI, hcard⟩ := exists_indep_card_eq_indepNum (G := G)
  have hE := card_edgeFinset_le hI hdeg
  rw [card_compl, hcard] at hE
  have hαn := indepNum_le_card (G := G)
  have hE' : (#G.edgeFinset : ℝ) ≤ Δ * ((Fintype.card V : ℝ) - G.indepNum) := by
    have : ((Fintype.card V - G.indepNum : ℕ) : ℝ) = (Fintype.card V : ℝ) - G.indepNum :=
      Nat.cast_sub hαn
    rw [← this]; exact_mod_cast hE
  have hΔ' : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
  · have : G.indepNum = 0 := by omega
    simp [this, turan, hn]
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hα0 : (0 : ℝ) ≤ G.indepNum := Nat.cast_nonneg _
  have hE0 : (0 : ℝ) ≤ #G.edgeFinset := Nat.cast_nonneg _
  rw [turan, div_mul_div_comm, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg ((2 * (Δ : ℝ) + 1) * Fintype.card V - 4 * Δ * G.indepNum),
    mul_le_mul_of_nonneg_left hE' (by positivity : (0 : ℝ) ≤ 16 * Δ * G.indepNum)]

/-- `(2Δ+1)²/(8Δ) = (Δ+1)/2 + 1/(8Δ)`: Turán's ratio is strictly worse than Caro–Wei's. -/
theorem turan_ratio_eq {Δ : ℕ} (hΔ : 1 ≤ Δ) :
    ((2 * Δ + 1) ^ 2 / (8 * Δ) : ℝ) = (Δ + 1) / 2 + 1 / (8 * Δ) := by
  have : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  field_simp; ring

omit [DecidableEq V] in
/-- Tightness of Theorem 3 for any graph with the parameters of the paper's example. -/
theorem tight_of_params {Δ : ℕ} (hΔ : 1 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (hn : Fintype.card V = 4 * Δ) (hE : #G.edgeFinset = (2 * Δ - 1) * Δ) {I : Finset V}
    (hI : G.IsIndepSet (I : Set V)) (hIcard : #I = 2 * Δ + 1) :
    G.indepNum = 2 * Δ + 1 ∧ turan G = 8 * Δ / (2 * Δ + 1) := by
  classical
  constructor
  · apply le_antisymm
    · obtain ⟨J, hJ, hcard⟩ := exists_indep_card_eq_indepNum (G := G)
      have h := card_edgeFinset_le hJ hdeg
      rw [card_compl, hcard, hE, hn] at h
      rw [mul_comm] at h
      have h2 : (2 * Δ - 1) ≤ 4 * Δ - G.indepNum := Nat.le_of_mul_le_mul_left h (by omega)
      have := indepNum_le_card (G := G)
      omega
    · rw [← hIcard]; exact hI.card_le_indepNum
  · rw [turan, hn, hE]
    have : (((2 * Δ - 1 : ℕ)) : ℝ) = 2 * Δ - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    push_cast [this]
    have : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    rw [div_eq_div_iff (by nlinarith) (by positivity)]
    ring

/-! ### The paper's example graph -/

/-- Vertices of the example for `Δ = D+1`: `A = Fin (2D+1)`, `B = Fin (2D+1)`, `C = Fin 2`. -/
abbrev ExV (D : ℕ) := (Fin (2 * D + 1) ⊕ Fin (2 * D + 1)) ⊕ Fin 2

/-- Edge relation of the example: `aᵢ ~ bⱼ` iff `j - i ∈ {0, …, Δ-1}` (mod `2Δ-1`). -/
def exRel (D : ℕ) : ExV D → ExV D → Prop
  | .inl (.inl i), .inl (.inr j) => ((j - i : Fin (2 * D + 1)) : ℕ) < D + 1
  | _, _ => False

instance (D : ℕ) : DecidableRel (exRel D) := fun a b => by
  rcases a with (i | i) | c <;> rcases b with (j | j) | c' <;> simp only [exRel] <;>
    infer_instance

/-- The paper's example for Theorem 3 (with `Δ = D+1`): a `Δ`-regular bipartite graph on
`A ∪ B` with `|A| = |B| = 2Δ-1`, plus two isolated vertices. -/
def exampleGraph (D : ℕ) : SimpleGraph (ExV D) := SimpleGraph.fromRel (exRel D)

instance (D : ℕ) : DecidableRel (exampleGraph D).Adj := fun a b => by
  unfold exampleGraph; infer_instance

theorem card_filter_sub_lt (D : ℕ) (i : Fin (2 * D + 1)) :
    #(univ.filter fun j : Fin (2 * D + 1) => ((j - i : Fin (2 * D + 1)) : ℕ) < D + 1) = D + 1 := by
  have : (univ.filter fun j : Fin (2 * D + 1) => ((j - i : Fin (2 * D + 1)) : ℕ) < D + 1) =
      (univ.filter fun k : Fin (2 * D + 1) => (k : ℕ) < D + 1).map (Equiv.addRight i).toEmbedding := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_map_equiv, Equiv.addRight_symm,
      Equiv.coe_addRight]
    rw [sub_eq_add_neg]
  rw [this, card_map, Fin.card_filter_val_lt]
  omega

theorem card_filter_sub_lt' (D : ℕ) (j : Fin (2 * D + 1)) :
    #(univ.filter fun i : Fin (2 * D + 1) => ((j - i : Fin (2 * D + 1)) : ℕ) < D + 1) = D + 1 := by
  have : (univ.filter fun i : Fin (2 * D + 1) => ((j - i : Fin (2 * D + 1)) : ℕ) < D + 1) =
      (univ.filter fun k : Fin (2 * D + 1) => (k : ℕ) < D + 1).image (fun k => j - k) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h; exact ⟨j - i, h, sub_sub_cancel j i⟩
    · rintro ⟨k, hk, rfl⟩; rwa [sub_sub_cancel]
  rw [this, card_image_of_injective _ (sub_right_injective), Fin.card_filter_val_lt]
  omega

@[simp] theorem exampleGraph_adj_ab (D : ℕ) (i j : Fin (2 * D + 1)) :
    (exampleGraph D).Adj (.inl (.inl i)) (.inl (.inr j)) ↔ ((j - i : Fin (2 * D + 1)) : ℕ) < D + 1 := by
  simp [exampleGraph, exRel]

@[simp] theorem exampleGraph_adj_ba (D : ℕ) (i j : Fin (2 * D + 1)) :
    (exampleGraph D).Adj (.inl (.inr j)) (.inl (.inl i)) ↔ ((j - i : Fin (2 * D + 1)) : ℕ) < D + 1 := by
  simp [exampleGraph, exRel]

@[simp] theorem exampleGraph_not_adj_aa (D : ℕ) (i j : Fin (2 * D + 1)) :
    ¬ (exampleGraph D).Adj (.inl (.inl i)) (.inl (.inl j)) := by
  simp [exampleGraph, exRel]

@[simp] theorem exampleGraph_not_adj_bb (D : ℕ) (i j : Fin (2 * D + 1)) :
    ¬ (exampleGraph D).Adj (.inl (.inr i)) (.inl (.inr j)) := by
  simp [exampleGraph, exRel]

@[simp] theorem exampleGraph_not_adj_c (D : ℕ) (c : Fin 2) (x : ExV D) :
    ¬ (exampleGraph D).Adj (.inr c) x := by
  rcases x with (a | b) | c' <;> simp [exampleGraph, exRel]

@[simp] theorem exampleGraph_not_adj_c' (D : ℕ) (c : Fin 2) (x : ExV D) :
    ¬ (exampleGraph D).Adj x (.inr c) := fun h => exampleGraph_not_adj_c D c x h.symm

theorem exampleGraph_degree (D : ℕ) (v : ExV D) :
    (exampleGraph D).degree v = match v with
      | .inl _ => D + 1
      | .inr _ => 0 := by
  rw [← card_neighborFinset_eq_degree]
  rcases v with (i | j) | c
  · rw [← card_filter_sub_lt D i]
    have : (exampleGraph D).neighborFinset (.inl (.inl i)) =
        (univ.filter fun j : Fin (2 * D + 1) => ((j - i : Fin (2 * D + 1)) : ℕ) < D + 1).map
          (Function.Embedding.inr.trans Function.Embedding.inl) := by
      ext x; rcases x with (a | b) | c <;> simp
    rw [this, card_map]
  · rw [← card_filter_sub_lt' D j]
    have : (exampleGraph D).neighborFinset (.inl (.inr j)) =
        (univ.filter fun i : Fin (2 * D + 1) => ((j - i : Fin (2 * D + 1)) : ℕ) < D + 1).map
          (Function.Embedding.inl.trans Function.Embedding.inl) := by
      ext x; rcases x with (a | b) | c <;> simp
    rw [this, card_map]
  · simp only [card_eq_zero]
    ext x
    simp

theorem exampleGraph_degree_le (D : ℕ) (v : ExV D) : (exampleGraph D).degree v ≤ D + 1 := by
  rw [exampleGraph_degree]; rcases v with _ | _ <;> simp

theorem exampleGraph_maxDegree (D : ℕ) : (exampleGraph D).maxDegree = D + 1 := by
  apply le_antisymm (maxDegree_le_of_forall_degree_le _ _ (exampleGraph_degree_le D))
  have := (exampleGraph D).degree_le_maxDegree (.inl (.inl 0))
  rwa [exampleGraph_degree] at this

theorem exampleGraph_card_edges (D : ℕ) :
    #(exampleGraph D).edgeFinset = (2 * (D + 1) - 1) * (D + 1) := by
  have h := (exampleGraph D).sum_degrees_eq_twice_card_edges
  simp only [exampleGraph_degree, Fintype.sum_sum_type, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_zero, add_zero, Fintype.card_sum] at h
  have : 2 * (D + 1) - 1 = 2 * D + 1 := by omega
  rw [this]
  nlinarith

theorem exampleGraph_indep (D : ℕ) :
    (exampleGraph D).IsIndepSet
      (((univ : Finset (Fin (2 * D + 1))).map
          (Function.Embedding.inl.trans Function.Embedding.inl) ∪
        (univ : Finset (Fin 2)).map Function.Embedding.inr : Finset (ExV D)) : Set (ExV D)) := by
  intro x hx y hy _ hadj
  simp only [coe_union, coe_map, coe_univ, Set.image_univ, Set.mem_union, Set.mem_range,
    Function.Embedding.trans_apply, Function.Embedding.inl_apply,
    Function.Embedding.inr_apply] at hx hy
  rcases hx with ⟨i, rfl⟩ | ⟨c, rfl⟩ <;> rcases hy with ⟨j, rfl⟩ | ⟨c', rfl⟩ <;>
    simp [exampleGraph, exRel] at hadj

/-- **Theorem 3.** For every `Δ ≥ 1`, the Turán bound has (tight) performance ratio
`(2Δ+1)²/(8Δ) = (Δ+1)/2 + 1/(8Δ)` on graphs of maximum degree `Δ`. -/
theorem theorem3 {Δ : ℕ} (hΔ : 1 ≤ Δ) :
    HasTightPerformanceRatio turanBound Δ ((2 * Δ + 1) ^ 2 / (8 * Δ)) := by
  refine ⟨?_, ?_⟩
  · intro W _ _ H _ hmax
    simp only [turanBound]
    exact ⟨turan_le_indepNum, indepNum_le_turan hΔ (fun v => hmax ▸ H.degree_le_maxDegree v)⟩
  · intro ρ hρ h
    obtain ⟨D, rfl⟩ : ∃ D, Δ = D + 1 := ⟨Δ - 1, by omega⟩
    obtain ⟨-, hα⟩ := h _ (exampleGraph D) (exampleGraph_maxDegree D)
    simp only [turanBound] at hα
    have hI := exampleGraph_indep D
    obtain ⟨hα', hT⟩ := tight_of_params (G := exampleGraph D) hΔ (exampleGraph_degree_le D)
      (by simp; ring) (exampleGraph_card_edges D) hI (by
        rw [card_union_of_disjoint]
        · simp; ring
        · rw [Finset.disjoint_left]; intro x hx hx'; simp at hx hx'
          obtain ⟨i, rfl⟩ := hx; simp at hx')
    rw [hα', hT] at hα
    push_cast at hα hρ
    have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    rw [mul_div_assoc', le_div_iff₀ (by positivity)] at hα
    rw [div_eq_mul_inv] at hρ
    have hρ' : ρ * (8 * ((D : ℝ) + 1)) < (2 * ((D : ℝ) + 1) + 1) ^ 2 := by
      rwa [← div_eq_mul_inv, lt_div_iff₀ (by positivity)] at hρ
    nlinarith

end Podc.LocalISApproximation
