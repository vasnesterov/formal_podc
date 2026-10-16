import Papers.PODC2016.VertexCoverLocalRatio.Correctness

/-!
# Number of iterations (Lemma 3.3)

Key fact (first claim in the proof of Lemma 3.3, in exact form): if `v` keeps running after
iteration `i`, then every neighbour that keeps running answered `v`'s request in full, so
`w_i(v) - w_{i+1}(v) ≥ vault(v)·d_{i+1}(v)/d_i(v)` (`drop`).

Counting (`count_bound`, pure real arithmetic): for every real `K > 1`, iterations with
`d_{i+1} ≤ d_i/K` number at most `log d(v)/log K`, the others at most `K(1-θ)/a`. Hence
(`active_bound`): if `v` is still running at the beginning of iteration `n`, then
`n ≤ K(1-θ)/a + log d(v)/log K`. With the paper's parameters `(1-θ)/a = 2/ε`.

`lemma_3_3_small` / `lemma_3_3_large`: the two cases of Lemma 3.3 with explicit constants, for
`0 < ε ≤ E` (the paper's "`ε = O(1)`").
-/

set_option linter.unusedSectionVars false

namespace VertexCoverLocalRatio

open Finset SimpleGraph

/-! ### Counting -/

/-- Pure counting core of Lemma 3.3. -/
theorem count_bound {d : ℕ → ℕ} {w : ℕ → ℝ} {n : ℕ} {W a θ K : ℝ} (hK : 1 < K) (ha : 0 < a)
    (hθ : θ ≤ 1) (hW : 0 ≤ W)
    (hd : ∀ i, i + 1 ≤ n → 1 ≤ d (i + 1))
    (hmono : ∀ i < n, d (i + 1) ≤ d i)
    (hdrop : ∀ i < n, a * W * d (i + 1) / d i ≤ w i - w (i + 1))
    (h0 : w 0 = W) (hn : 0 < n → θ * W < w n) :
    (n : ℝ) ≤ K * (1 - θ) / a + Real.log (d 0) / Real.log K := by
  have hlogK : 0 < Real.log K := Real.log_pos hK
  have hlogd : 0 ≤ Real.log (d 0) := Real.log_natCast_nonneg _
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · simp only [CharP.cast_eq_zero]
    have : 0 ≤ K * (1 - θ) / a := div_nonneg (mul_nonneg (by linarith) (by linarith)) ha.le
    have : 0 ≤ Real.log (d 0) / Real.log K := div_nonneg hlogd hlogK.le
    linarith
  have hdpos : ∀ i ≤ n, (1 : ℝ) ≤ d i := by
    intro i hi
    rcases i with _ | i
    · exact_mod_cast (hd 0 (by omega)).trans (hmono 0 hnpos)
    · exact_mod_cast hd i hi
  have hdropnn : ∀ i < n, 0 ≤ w i - w (i + 1) := fun i hi =>
    le_trans (div_nonneg (mul_nonneg (mul_nonneg ha.le hW) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) (hdrop i hi)
  have hwmono : ∀ i ≤ n, w i ≤ w 0 := by
    intro i hi
    induction i with
    | zero => exact le_refl _
    | succ i ih => have := hdropnn i (by omega); have := ih (by omega); linarith
  have hWpos : 0 < W := by
    have h1 := hn hnpos; have h2 := hwmono n le_rfl
    rcases hW.lt_or_eq with h | h
    · exact h
    · rw [← h] at h1; rw [h0, ← h] at h2; simp at h1; linarith
  have hθ1 : 0 < 1 - θ := by
    have h1 := hn hnpos; have h2 := hwmono n le_rfl; rw [h0] at h2
    by_contra hc; push Not at hc; nlinarith
  -- split the iterations
  set P : ℕ → Prop := fun i => K * d (i + 1) ≤ d i
  set B := (range n).filter P
  set H := (range n).filter fun i => ¬ P i
  have hcard : B.card + H.card = n := by
    rw [card_filter_add_card_filter_not, card_range]
  -- heavy iterations
  have hH : (H.card : ℝ) < K * (1 - θ) / a := by
    have htel : ∑ i ∈ range n, (w i - w (i + 1)) = W - w n := by
      rw [sum_range_sub', h0]
    have h1 : ∑ i ∈ H, a * W / K ≤ ∑ i ∈ range n, (w i - w (i + 1)) := by
      calc ∑ i ∈ H, a * W / K ≤ ∑ i ∈ H, (w i - w (i + 1)) := by
            refine sum_le_sum fun i hi => ?_
            simp only [H, mem_filter, mem_range, P, not_le] at hi
            refine le_trans ?_ (hdrop i hi.1)
            have hdi : (0 : ℝ) < d i := by linarith [hdpos i hi.1.le]
            rw [div_le_div_iff₀ (by linarith) hdi]
            have : 0 < a * W := mul_pos ha hWpos
            nlinarith
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun i hi _ => hdropnn i (mem_range.1 hi)
    rw [sum_const, nsmul_eq_mul, htel] at h1
    have h2 := hn hnpos
    rw [lt_div_iff₀ ha]
    have hK0 : 0 < K := by linarith
    have : (H.card : ℝ) * (a * W / K) < (1 - θ) * W := by linarith
    rw [mul_div_assoc', div_lt_iff₀ hK0] at this
    nlinarith
  -- degree-dropping iterations
  have hB : ∀ m ≤ n, (d m : ℝ) * K ^ ((range m).filter P).card ≤ d 0 := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      have ih := ih (by omega)
      have hKc : (0 : ℝ) ≤ K ^ ((range m).filter P).card := pow_nonneg (by linarith) _
      rw [range_add_one, filter_insert]
      by_cases hP : P m
      · rw [if_pos hP, card_insert_of_notMem (by simp), pow_succ]
        have : (K * d (m + 1) : ℝ) ≤ d m := hP
        nlinarith
      · rw [if_neg hP]
        have : (d (m + 1) : ℝ) ≤ d m := by exact_mod_cast hmono m (by omega)
        nlinarith
  have hB' : (B.card : ℝ) ≤ Real.log (d 0) / Real.log K := by
    have h1 := hB n le_rfl
    have h2 := hdpos n le_rfl
    have hKc : (1 : ℝ) ≤ K ^ B.card := one_le_pow₀ hK.le
    have h3 : K ^ B.card ≤ (d 0 : ℝ) := by nlinarith
    rw [le_div_iff₀ hlogK, ← Real.log_pow]
    exact Real.log_le_log (by positivity) h3
  have : (n : ℝ) = B.card + H.card := by exact_mod_cast hcard.symm
  linarith

/-! ### Application to Algorithm 1 -/

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {θ a σ : ℝ} {R : Rule V} {w0 : V → ℝ}

theorem actN_init (v : V) : actN G (init w0) v = G.neighborFinset v := by
  ext u; simp [actN, init]

theorem dg_init (v : V) : dg G (init w0) v = G.degree v := by
  rw [dg, actN_init, card_neighborFinset_eq_degree]

theorem actN_step_subset {s : GState V} (v : V) :
    actN G (step G θ a R w0 s) v ⊆ actN G s v := fun u hu => by
  rw [mem_actN] at hu ⊢; exact ⟨hu.1, active_of_step hu.2⟩

/-- A vertex that keeps running still has a running neighbour. -/
theorem one_le_dg_step {s : GState V} {v : V} (hv : (step G θ a R w0 s).st v = .active) :
    1 ≤ dg G (step G θ a R w0 s) v := by
  obtain ⟨hv0, hvn, u, hu, hnc⟩ := step_active_iff.1 hv
  have hu0 := (mem_actN.1 hu).2
  have hua : (step G θ a R w0 s).st u = .active :=
    step_active_iff.2 ⟨hu0, fun hle => hnc ⟨hu0, hle⟩, v, actN_symm hv0 hu,
      fun hc => hvn hc.2⟩
  exact card_pos.2 ⟨u, mem_actN.2 ⟨(mem_actN.1 hu).1, hua⟩⟩

/-- First claim of the proof of Lemma 3.3 (exact form). -/
theorem drop (h : Hyp θ a σ R w0) {s : GState V} (hs : Inv G θ a w0 s) {v : V}
    (hv : (step G θ a R w0 s).st v = .active) :
    a * w0 v * dg G (step G θ a R w0 s) v / dg G s v ≤ s.w v - (step G θ a R w0 s).w v := by
  have hv0 := active_of_step hv
  rw [step_w, newW_active h hs hv0]
  have hg := given_nonneg h hs hv0
  have hfull : ∑ u ∈ actN G (step G θ a R w0 s) v, bud G a R w0 s u v =
      dg G (step G θ a R w0 s) v * (a * w0 v / dg G s v) := by
    rw [dg, ← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl fun u hu => ?_
    have hu' := (mem_actN.1 hu)
    have hus : u ∈ actN G s v := actN_step_subset v hu
    have hnc : ¬ cov G θ a R w0 s u := fun hc => by
      have := (step_active_iff.1 hu'.2).2.1; exact this hc.2
    rw [bud_eq_req_of_active h hs hv0 hus hnc]; rfl
  have hle : ∑ u ∈ actN G (step G θ a R w0 s) v, bud G a R w0 s u v ≤ recv G a R w0 s v :=
    sum_le_sum_of_subset_of_nonneg (actN_step_subset v) fun u hu _ =>
      bud_nonneg h hs (mem_actN.1 hu).2 (actN_symm hv0 hu)
  rw [hfull] at hle
  rw [mul_div_assoc', mul_comm] at hle
  rw [mul_comm (a * w0 v)] at hle ⊢
  linarith

/-- If `v` is still running at the beginning of iteration `n`, then for every `K > 1`,
`n ≤ K(1-θ)/a + log d(v) / log K`. -/
theorem active_bound (h : Hyp θ a σ R w0) {v : V} {n : ℕ}
    (hv : (run G θ a R w0 n).st v = .active) {K : ℝ} (hK : 1 < K) :
    (n : ℝ) ≤ K * (1 - θ) / a + Real.log (G.degree v) / Real.log K := by
  rw [← dg_init (w0 := w0) (G := G)]
  have hact : ∀ i ≤ n, (run G θ a R w0 i).st v = .active := fun i hi => active_of_le hi hv
  refine count_bound (d := fun i => dg G (run G θ a R w0 i) v)
    (w := fun i => (run G θ a R w0 i).w v) (W := w0 v) hK h.ha h.hθ.le (h.hw0 v)
    (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) rfl (fun hn => ?_)
  · have := hact (i + 1) hi
    rw [run_succ] at this ⊢
    exact one_le_dg_step this
  · simp only [run_succ]
    exact card_le_card (actN_step_subset v)
  · have := hact (i + 1) hi
    simp only [run_succ] at this ⊢
    exact drop h (inv_run h i) this
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := hv
    rw [run_succ] at this ⊢
    have hn := (step_active_iff.1 this).2.1
    push Not at hn
    exact hn

/-- Every vertex eventually returns: it is not running at the beginning of iteration `n` for any
`n > 2(1-θ)/a + log d(v)/log 2`. -/
theorem terminates (h : Hyp θ a σ R w0) (v : V) {n : ℕ}
    (hn : 2 * (1 - θ) / a + Real.log (G.degree v) / Real.log 2 < n) :
    (run G θ a R w0 n).st v ≠ .active := fun hv =>
  absurd (active_bound h hv one_lt_two) (not_le.2 hn)

/-- There is an iteration by whose beginning every vertex has returned. -/
theorem exists_all_returned (h : Hyp θ a σ R w0) :
    ∃ T, ∀ v, (run G θ a R w0 T).st v ≠ .active := by
  obtain ⟨T, hT⟩ := exists_nat_gt (2 * (1 - θ) / a + Real.log (Fintype.card V) / Real.log 2)
  refine ⟨T, fun v => terminates h v (lt_of_le_of_lt ?_ hT)⟩
  have hd : Real.log (G.degree v) ≤ Real.log (Fintype.card V) := by
    rcases Nat.eq_zero_or_pos (G.degree v) with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast (G.degree_lt_card_verts v).le)
  have := div_le_div_of_nonneg_right hd (Real.log_pos one_lt_two).le
  linarith

end VertexCoverLocalRatio
