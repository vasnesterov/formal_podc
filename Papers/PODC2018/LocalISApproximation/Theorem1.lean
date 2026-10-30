import Papers.PODC2018.LocalISApproximation.Boppana

/-!
# Theorem 1: Caro–Wei (= Boppana's algorithm) has performance ratio `(Δ+1)/2`

* `caroWei_ge_of_degree_le`: the proof of Theorem 1, `CaroWei(G) ≥ 2α(G)/(Δ+1)` whenever `Δ ≥ 1`
  and all degrees are `≤ Δ`.
* `regular_bipartite`: in a `Δ`-regular bipartite graph `CaroWei(G) = n/(Δ+1)` and `α(G) = n/2`
  (the lower-bound part of the proof).
* `theorem1`: Theorem 1 as stated, with tightness, for every `Δ ≥ 1`.
* `theorem1_false_zero`: the statement fails for `Δ = 0` (graphs without edges: `CaroWei = α`).
* `boppana_ratio`: the corresponding statement for Boppana's algorithm (expected output size).
-/

open Finset SimpleGraph

namespace Podc.LocalISApproximation

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The pointwise inequality behind Theorem 1: `1/(d+1) + d/(Δ(Δ+1)) ≥ 2/(Δ+1)` for integers
`0 ≤ d ≤ Δ`, `Δ ≥ 1`. -/
theorem two_div_le (d Δ : ℕ) (hΔ : 1 ≤ Δ) (hd : d ≤ Δ) :
    2 / ((Δ : ℝ) + 1) ≤ 1 / ((d : ℝ) + 1) + d / ((Δ : ℝ) * (Δ + 1)) := by
  have hΔ' : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hdΔ : (d : ℝ) ≤ Δ := by exact_mod_cast hd
  have key : 0 ≤ ((Δ : ℝ) - d) * ((Δ : ℝ) - d - 1) := by
    rcases Nat.eq_or_lt_of_le hd with h | h
    · subst h; simp
    · have : (d : ℝ) + 1 ≤ Δ := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by linarith)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [key]

/-- **Theorem 1 (upper bound).** If `Δ ≥ 1` and every degree is at most `Δ`, then
`CaroWei(G) ≥ 2 α(G)/(Δ+1)`. -/
theorem caroWei_ge_of_degree_le {Δ : ℕ} (hΔ : 1 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) :
    2 * (G.indepNum : ℝ) / (Δ + 1) ≤ caroWei G := by
  obtain ⟨I, hI, hcard⟩ := exists_indep_card_eq_indepNum (G := G)
  have hΔ' : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  -- eq. (4)
  have h4 : (∑ v ∈ I, (G.degree v : ℝ)) ≤ Δ * #Iᶜ := by
    exact_mod_cast sum_degree_indep_le hI hdeg
  have hc : (#Iᶜ : ℝ) / (Δ + 1) ≤ ∑ v ∈ Iᶜ, 1 / ((G.degree v : ℝ) + 1) := by
    calc (#Iᶜ : ℝ) / (Δ + 1) = ∑ _v ∈ Iᶜ, 1 / ((Δ : ℝ) + 1) := by
          rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := by
          refine sum_le_sum fun v _ => one_div_le_one_div_of_le (by positivity) ?_
          have := hdeg v
          have : (G.degree v : ℝ) ≤ Δ := by exact_mod_cast this
          linarith
  have hsum : 2 * (G.indepNum : ℝ) / (Δ + 1) ≤
      ∑ v ∈ I, 1 / ((G.degree v : ℝ) + 1) + (∑ v ∈ I, (G.degree v : ℝ)) / (Δ * (Δ + 1)) := by
    calc 2 * (G.indepNum : ℝ) / (Δ + 1) = ∑ _v ∈ I, 2 / ((Δ : ℝ) + 1) := by
          rw [sum_const, nsmul_eq_mul, hcard]; ring
      _ ≤ ∑ v ∈ I, (1 / ((G.degree v : ℝ) + 1) + (G.degree v : ℝ) / (Δ * (Δ + 1))) :=
          sum_le_sum fun v _ => two_div_le _ _ hΔ (hdeg v)
      _ = _ := by rw [sum_add_distrib, sum_div]
  have h4' : (∑ v ∈ I, (G.degree v : ℝ)) / (Δ * (Δ + 1)) ≤ (#Iᶜ : ℝ) / (Δ + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc 2 * (G.indepNum : ℝ) / (Δ + 1)
      ≤ ∑ v ∈ I, 1 / ((G.degree v : ℝ) + 1) + ∑ v ∈ Iᶜ, 1 / ((G.degree v : ℝ) + 1) := by
        linarith
    _ = caroWei G := by rw [caroWei, sum_add_sum_compl]

omit [DecidableEq V] in
/-- On a `Δ`-regular graph, `CaroWei(G) = n/(Δ+1)` (each vertex contributes `1/(Δ+1)`). -/
theorem caroWei_regular {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    caroWei G = Fintype.card V / ((Δ : ℝ) + 1) := by
  simp only [caroWei, hreg.degree_eq, sum_const, card_univ, nsmul_eq_mul]
  ring

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A colour class of a proper colouring is independent. -/
theorem isIndepSet_colorClass {α : Type*} [DecidableEq α] (C : G.Coloring α) (i : α) :
    G.IsIndepSet ((univ.filter fun v => C v = i : Finset V) : Set V) := by
  intro u hu v hv _ hadj
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu hv
  exact C.valid hadj (hu.trans hv.symm)

omit [DecidableRel G.Adj] in
/-- A bipartite graph has an independent set with at least half of the vertices. -/
theorem card_le_two_mul_indepNum (hbip : G.Colorable 2) : Fintype.card V ≤ 2 * G.indepNum := by
  obtain ⟨C⟩ := hbip
  have h0 := (isIndepSet_colorClass C 0).card_le_indepNum
  have h1 := (isIndepSet_colorClass C 1).card_le_indepNum
  have : #(univ.filter fun v => C v = 0) + #(univ.filter fun v => C v = 1) = Fintype.card V := by
    rw [← card_union_of_disjoint]
    · rw [← card_univ]; congr 1; ext v; simp only [mem_union, mem_filter, mem_univ, true_and,
        iff_true]; omega
    · rw [disjoint_filter]; intro v _ h; rw [h]; decide
  omega

/-- **Lower-bound part of Theorem 1**: on a `Δ`-regular bipartite graph (`Δ ≥ 1`),
`CaroWei(G) = n/(Δ+1)` while `α(G) = n/2`. -/
theorem regular_bipartite {Δ : ℕ} (hΔ : 1 ≤ Δ) (hreg : G.IsRegularOfDegree Δ)
    (hbip : G.Colorable 2) :
    caroWei G = Fintype.card V / ((Δ : ℝ) + 1) ∧ 2 * G.indepNum = Fintype.card V := by
  refine ⟨caroWei_regular hreg, le_antisymm ?_ (card_le_two_mul_indepNum hbip)⟩
  have h := caroWei_ge_of_degree_le hΔ (fun v => (hreg.degree_eq v).le)
  rw [caroWei_regular hreg, div_le_div_iff_of_pos_right (by positivity)] at h
  exact_mod_cast h

/-! ### The complete bipartite graph `K_{Δ,Δ}` -/

-- CSLib candidate (Mathlib has no `DecidableRel` instance for `completeBipartiteGraph`)
instance instDecidableRelCompleteBipartite (α β : Type*) :
    DecidableRel (completeBipartiteGraph α β).Adj := fun v w =>
  inferInstanceAs (Decidable (v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft))

theorem degree_completeBipartite_inl {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (a : α) : (completeBipartiteGraph α β).degree (Sum.inl a) = Fintype.card β := by
  rw [← card_neighborFinset_eq_degree]
  have : (completeBipartiteGraph α β).neighborFinset (Sum.inl a) = univ.map Function.Embedding.inr := by
    ext x; cases x <;> simp
  rw [this, card_map, card_univ]

theorem degree_completeBipartite_inr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (b : β) : (completeBipartiteGraph α β).degree (Sum.inr b) = Fintype.card α := by
  rw [← card_neighborFinset_eq_degree]
  have : (completeBipartiteGraph α β).neighborFinset (Sum.inr b) = univ.map Function.Embedding.inl := by
    ext x; cases x <;> simp
  rw [this, card_map, card_univ]

theorem completeBipartite_colorable (α β : Type*) : (completeBipartiteGraph α β).Colorable 2 :=
  ⟨Coloring.mk (fun x => Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) x) (by
    rintro (a | a) (b | b) h <;> simp_all)⟩

theorem completeBipartite_regular (Δ : ℕ) :
    (completeBipartiteGraph (Fin Δ) (Fin Δ)).IsRegularOfDegree Δ := by
  rintro (a | b)
  · rw [degree_completeBipartite_inl, Fintype.card_fin]
  · rw [degree_completeBipartite_inr, Fintype.card_fin]

/-- **Theorem 1.** For every `Δ ≥ 1`, `CaroWei` has (tight) performance ratio `(Δ+1)/2` on graphs of
maximum degree `Δ`: `α(G) ≥ CaroWei(G) ≥ α(G)/((Δ+1)/2)` for all `G` with `Δ(G) = Δ`, and
`K_{Δ,Δ}` shows that no smaller ratio holds. -/
theorem theorem1 {Δ : ℕ} (hΔ : 1 ≤ Δ) :
    HasTightPerformanceRatio caroWeiBound Δ (((Δ : ℝ) + 1) / 2) := by
  refine ⟨?_, ?_⟩
  · intro W _ _ H _ hmax
    simp only [caroWeiBound]
    refine ⟨caroWei_le_indepNum, ?_⟩
    have h := caroWei_ge_of_degree_le hΔ (fun v => hmax ▸ H.degree_le_maxDegree v)
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  · intro ρ hρ h
    have hreg := completeBipartite_regular Δ
    have : Nonempty (Fin Δ ⊕ Fin Δ) := ⟨Sum.inl ⟨0, hΔ⟩⟩
    obtain ⟨-, hα⟩ := h _ (completeBipartiteGraph (Fin Δ) (Fin Δ)) hreg.maxDegree_eq
    simp only [caroWeiBound] at hα
    obtain ⟨hcw, hα2⟩ := regular_bipartite hΔ hreg (completeBipartite_colorable _ _)
    rw [hcw] at hα
    simp only [Fintype.card_sum, Fintype.card_fin] at hα hα2
    have : ((completeBipartiteGraph (Fin Δ) (Fin Δ)).indepNum : ℝ) = Δ := by
      have : (completeBipartiteGraph (Fin Δ) (Fin Δ)).indepNum = Δ := by omega
      exact_mod_cast this
    rw [this] at hα
    have hΔ' : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    push_cast at hα
    rw [mul_div_assoc'] at hα
    rw [le_div_iff₀ (by positivity)] at hα
    nlinarith

/-- Theorem 1 is false for `Δ = 0`: on a graph without edges `CaroWei(G) = α(G) = n`, so no
ratio below `1` (in particular not `(0+1)/2`) holds. -/
theorem theorem1_false_zero : ¬ HasPerformanceRatio caroWeiBound 0 ((0 + 1) / 2) := by
  intro h
  have hreg : (⊥ : SimpleGraph (Fin 1)).IsRegularOfDegree 0 := fun v => by simp
  obtain ⟨-, hα⟩ := h (Fin 1) ⊥ (maxDegree_bot_eq_zero)
  simp only [caroWeiBound] at hα
  rw [caroWei_regular hreg] at hα
  have : (⊥ : SimpleGraph (Fin 1)).indepNum = 1 := by
    apply le_antisymm
    · simpa using indepNum_le_card (G := (⊥ : SimpleGraph (Fin 1)))
    · have := (show (⊥ : SimpleGraph (Fin 1)).IsIndepSet ((univ : Finset (Fin 1)) : Set (Fin 1))
        from fun _ _ _ _ _ h => h.elim).card_le_indepNum
      simpa using this
  rw [this] at hα
  norm_num at hα

/-- Theorem 1 for Boppana's algorithm: if `Δ ≥ 1` and all degrees are `≤ Δ`, then the expected
size of the output (uniformly random ordering) is at least `2α(G)/(Δ+1)`. -/
theorem boppana_ratio {Δ : ℕ} (hΔ : 1 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) :
    2 * (G.indepNum : ℝ) / (Δ + 1) ≤
      (∑ σ : V ≃ Fin (Fintype.card V), (#(boppana G σ) : ℝ)) / (Fintype.card V).factorial := by
  rw [expected_card_boppana]
  exact caroWei_ge_of_degree_le hΔ hdeg

end Podc.LocalISApproximation
