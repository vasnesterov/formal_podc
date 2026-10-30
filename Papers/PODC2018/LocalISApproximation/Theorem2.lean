import Papers.PODC2018.LocalISApproximation.Theorem3

/-!
# Theorem 2: Caro–Wei in terms of the average degree

Theorem 2 of the paper claims that `CaroWei` has performance ratio at most `(d̄+2)/1.657`, where
`d̄ = 2|E|/n`, i.e. `1.657 · α(G) ≤ (d̄+2) · CaroWei(G)` for every graph. The proof actually yields
the constant `4(√2-1) = 1.65685…` and then rounds it the wrong way
(`(d̄+2)/(4(√2-1)) ≤ (d̄+2)/1.657` is false, since `4(√2-1) < 1.657`).

* `theorem2_false`: the statement with `1.657` is false; the complete bipartite graph
  `K_{24000,10000}` is a counterexample (it is the paper's own extremal family "bipartite with
  regular sides" with `τ = 12/17 ≈ 1/√2` and large `d̄`).
* `theorem2_corrected`: the statement with `4(√2-1)` holds for every graph (the paper's proof).
* `four_mul_sqrt_two_sub_one_lt`: `4(√2-1) < 1.657`.
-/

open Finset SimpleGraph

namespace Podc.LocalISApproximation

/-- `4(√2-1) < 1.657`: the paper rounds `4(√2-1) = 1.65685…` up, which weakens the denominator in
the wrong direction. -/
theorem four_mul_sqrt_two_sub_one_lt : 4 * (Real.sqrt 2 - 1) < 1.657 := by
  have h : Real.sqrt 2 < 1.41425 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

/-! ### The counterexample -/

/-- **Theorem 2 as stated is false.** The claim "`CaroWei` has performance ratio at most
`(d̄+2)/1.657`", i.e. `α(G) ≤ (d̄+2)/1.657 · CaroWei(G)` for all graphs, fails for
`G = K_{24000,10000}`: there `α = 24000`, `d̄ = 2·24000·10000/34000 ≈ 14118` and
`(d̄+2)/1.657 · CaroWei(G) ≈ 23999.2 < 24000`. -/
theorem theorem2_false :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (G.indepNum : ℝ) ≤ (avgDegree G + 2) / 1.657 * caroWei G := by
  intro h
  let K := completeBipartiteGraph (Fin 24000) (Fin 10000)
  have hα : (24000 : ℝ) ≤ K.indepNum := by
    have hI : K.IsIndepSet (((univ : Finset (Fin 24000)).map Function.Embedding.inl :
        Finset (Fin 24000 ⊕ Fin 10000)) : Set (Fin 24000 ⊕ Fin 10000)) := by
      intro x hx y hy _ hadj
      simp only [coe_map, coe_univ, Set.image_univ, Set.mem_range,
        Function.Embedding.inl_apply] at hx hy
      obtain ⟨i, rfl⟩ := hx; obtain ⟨j, rfl⟩ := hy
      simp [K] at hadj
    have := hI.card_le_indepNum
    simp only [card_map, card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have hcw : caroWei K = 24000 / 10001 + 10000 / 24001 := by
    simp only [caroWei, Fintype.sum_sum_type, K, degree_completeBipartite_inl,
      degree_completeBipartite_inr, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hE : (#K.edgeFinset : ℝ) = 240000000 := by
    have h2 := K.sum_degrees_eq_twice_card_edges
    simp only [Fintype.sum_sum_type, K, degree_completeBipartite_inl,
      degree_completeBipartite_inr, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h2
    have : #(completeBipartiteGraph (Fin 24000) (Fin 10000)).edgeFinset = 240000000 := by omega
    exact_mod_cast this
  have hd : avgDegree K = 2 * 240000000 / 34000 := by
    simp only [avgDegree, hE, Fintype.card_sum, Fintype.card_fin]; norm_num
  have := h _ K
  rw [hcw, hd] at this
  have := hα.trans this
  norm_num at this

/-! ### The corrected statement -/

/-- The monotonicity step of the proof of Theorem 2 (the derivative argument for (5), plus
"rounding up the lower order terms"): for `0 < b ≤ a` (sizes of `V'` and `opt`) and
`0 ≤ x ≤ m` (`x = m_opt`), `(a²+b²)/(m+a+b) ≤ a²/(x+a) + b²/(2m-x+b)`. -/
theorem key_ineq {a b m x : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hab : b ≤ a) (hx : 0 ≤ x)
    (hxm : x ≤ m) : (a ^ 2 + b ^ 2) / (m + a + b) ≤ a ^ 2 / (x + a) + b ^ 2 / (2 * m - x + b) := by
  rcases hb.eq_or_lt with rfl | hb
  · rw [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_div, add_zero, add_zero, add_zero]
    exact div_le_div_of_nonneg_left (sq_nonneg a) (by linarith) (by linarith)
  have h1 : a ^ 2 / (m + a + b) ≤ a ^ 2 / (m + a) :=
    div_le_div_of_nonneg_left (sq_nonneg a) (by linarith) (by linarith)
  have h2 : b ^ 2 / (m + a + b) ≤ b ^ 2 / (m + b) :=
    div_le_div_of_nonneg_left (sq_nonneg b) (by linarith) (by linarith)
  have h3 : a ^ 2 / (m + a) + b ^ 2 / (m + b) ≤ a ^ 2 / (x + a) + b ^ 2 / (2 * m - x + b) := by
    have e1 : a ^ 2 / (x + a) - a ^ 2 / (m + a) = (m - x) * (a ^ 2 / ((x + a) * (m + a))) := by
      rw [div_sub_div _ _ (ne_of_gt (by linarith)) (ne_of_gt (by linarith)), ← mul_div_assoc]
      congr 1; ring
    have e2 : b ^ 2 / (m + b) - b ^ 2 / (2 * m - x + b) =
        (m - x) * (b ^ 2 / ((m + b) * (2 * m - x + b))) := by
      have : 0 < 2 * m - x + b := by linarith
      rw [div_sub_div _ _ (ne_of_gt (by linarith)) (ne_of_gt this), ← mul_div_assoc]
      congr 1; ring
    have hcmp : b ^ 2 / ((m + b) * (2 * m - x + b)) ≤ a ^ 2 / ((x + a) * (m + a)) := by
      rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
      have p1 : b * (x + a) ≤ a * (2 * m - x + b) := by nlinarith
      have p2 : b * (m + a) ≤ a * (m + b) := by nlinarith
      have := mul_le_mul p1 p2 (by nlinarith) (by nlinarith)
      nlinarith
    have := mul_le_mul_of_nonneg_left hcmp (by linarith : 0 ≤ m - x)
    linarith
  rw [add_div]
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Theorem 2, corrected constant.** For every graph,
`4(√2-1) · α(G) ≤ (d̄+2) · CaroWei(G)`, i.e. `CaroWei` has performance ratio at most
`(d̄+2)/(4(√2-1)) ≈ (d̄+2)/1.65685`. -/
theorem theorem2_corrected :
    4 * (Real.sqrt 2 - 1) * G.indepNum ≤ (avgDegree G + 2) * caroWei G := by
  obtain ⟨I, hI, hcard⟩ := exists_indep_card_eq_indepNum (G := G)
  set n := Fintype.card V
  set m : ℕ := #G.edgeFinset
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs15 : Real.sqrt 2 < 1.5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hcw0 : 0 ≤ caroWei G := sum_nonneg fun v _ => by positivity
  have hαn := indepNum_le_card (G := G)
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have : G.indepNum = 0 := by omega
    rw [this]; simp only [Nat.cast_zero, mul_zero]
    exact mul_nonneg (by unfold avgDegree; positivity) hcw0
  have hn : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hd : avgDegree G + 2 = (2 * m + 2 * n) / n := by
    show 2 * (m : ℝ) / n + 2 = (2 * m + 2 * n) / n
    field_simp
  rw [hd]
  set a : ℝ := ((G.indepNum : ℕ) : ℝ) with ha_def
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have han : a ≤ n := by rw [ha_def]; exact_mod_cast hαn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  by_cases hhalf : 2 * a ≤ n
  · -- `α ≤ n/2`: use Turán's bound.
    have hT : (n : ℝ) ^ 2 / (2 * m + n) ≤ caroWei G := turan_le_caroWei
    have h1 : (n : ℝ) ≤ (2 * m + 2 * n) / n * ((n : ℝ) ^ 2 / (2 * m + n)) := by
      rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ (2 * m + 2 * n) / n)
    nlinarith
  · -- `α > n/2`: Lemma 1 on `opt` and on `V'` separately.
    push Not at hhalf
    set b : ℝ := n - a with hb_def
    have hab : b ≤ a := by linarith
    have hb0 : 0 ≤ b := by linarith
    have ha : 0 < a := by linarith
    set x : ℝ := ∑ v ∈ I, (G.degree v : ℝ) with hx_def
    have hx0 : 0 ≤ x := sum_nonneg fun v _ => Nat.cast_nonneg _
    have hsumc : ∑ v ∈ Iᶜ, (G.degree v : ℝ) = 2 * m - x := by
      have h := G.sum_degrees_eq_twice_card_edges
      rw [← sum_add_sum_compl I] at h
      have : (∑ v ∈ I, (G.degree v : ℝ)) + ∑ v ∈ Iᶜ, (G.degree v : ℝ) = 2 * m := by
        exact_mod_cast h
      linarith
    have hxm : x ≤ m := by
      have := sum_degree_indep_le_compl hI
      have : x ≤ ∑ v ∈ Iᶜ, (G.degree v : ℝ) := by rw [hx_def]; exact_mod_cast this
      linarith
    have hIcard : (#I : ℝ) = a := by rw [ha_def, hcard]
    have hIccard : (#Iᶜ : ℝ) = b := by
      rw [hb_def, card_compl, Nat.cast_sub (card_le_univ I), hIcard]
    have hS1 : a ^ 2 / (x + a) ≤ ∑ v ∈ I, 1 / ((G.degree v : ℝ) + 1) := by
      have := Finset.sq_sum_div_le_sum_sq_div I (fun _ => (1 : ℝ))
        (g := fun v => (G.degree v : ℝ) + 1) (fun v _ => by positivity)
      simp only [sum_const, nsmul_eq_mul, mul_one, one_pow, sum_add_distrib, hIcard] at this
      rwa [← hx_def] at this
    have hS2 : b ^ 2 / (2 * m - x + b) ≤ ∑ v ∈ Iᶜ, 1 / ((G.degree v : ℝ) + 1) := by
      have := Finset.sq_sum_div_le_sum_sq_div Iᶜ (fun _ => (1 : ℝ))
        (g := fun v => (G.degree v : ℝ) + 1) (fun v _ => by positivity)
      simp only [sum_const, nsmul_eq_mul, mul_one, one_pow, sum_add_distrib, hIccard] at this
      rwa [hsumc] at this
    have hCW : (a ^ 2 + b ^ 2) / (m + a + b) ≤ caroWei G := by
      have := key_ineq ha hb0 hab hx0 hxm
      rw [caroWei, ← sum_add_sum_compl I]
      linarith
    have hnab : (n : ℝ) = a + b := by rw [hb_def]; ring
    have hsq : 4 * (Real.sqrt 2 - 1) * a * n ≤ 2 * (a ^ 2 + b ^ 2) := by
      have e : ((2 - Real.sqrt 2) * a - Real.sqrt 2 * b) ^ 2 =
          (6 - 4 * Real.sqrt 2) * a ^ 2 - (4 * Real.sqrt 2 - 4) * a * b + 2 * b ^ 2 := by
        linear_combination (a ^ 2 + 2 * a * b + b ^ 2) * hs2
      rw [hnab]
      nlinarith [sq_nonneg ((2 - Real.sqrt 2) * a - Real.sqrt 2 * b)]
    have hfin : 4 * (Real.sqrt 2 - 1) * a ≤
        (2 * m + 2 * n) / n * ((a ^ 2 + b ^ 2) / (m + a + b)) := by
      have hmab : (m : ℝ) + a + b = m + n := by rw [hnab]; ring
      rw [div_mul_div_comm, le_div_iff₀ (mul_pos hn (by linarith)), hmab]
      have := mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ m + n)
      nlinarith
    have := mul_le_mul_of_nonneg_left hCW (div_nonneg (by linarith) hn.le :
      (0 : ℝ) ≤ (2 * m + 2 * n) / n)
    linarith

end Podc.LocalISApproximation
