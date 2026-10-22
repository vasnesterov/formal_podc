import Papers.PODC2019.CoveringPrimalDual.Correctness

/-!
# Number of iterations (Section 4.2: Lemmas 4.6, 4.7, Theorem 4.8)

* `lemma_4_6`: the number of `e`-raise iterations is at most `log_α(Δ · 2^{f z})`.
* `lemma_4_7`: for every vertex `v` and level `ℓ`, the number of `v`-stuck iterations at level `ℓ`
  is `< α/κ + 1`, i.e. at most `⌈α/κ⌉` (`lemma_4_7_ceil`). The paper states `≤ α` (`κ = 1`) and
  `≤ 2α` (Lemma C.2, `κ = 1/2`), which holds for integral `α` but not in general (see
  `Counterexamples.lean`).
* `theorem_4_8`: every edge is covered, i.e. the algorithm has terminated, by the end of iteration
  `⌊log_α(Δ·2^{fz}/(2c₀))⌋ + f·z·⌈α/κ⌉ + 1`; `theorem_4_8_bound` gives the
  `O(log_α Δ + f·z·α)` form.
-/

set_option linter.unusedSectionVars false

namespace Podc.CoveringPrimalDual

open Finset Cslib.Hypergraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {I : Inst V E} {P : Params}

theorem C_run_mono (I : Inst V E) (P : Params) {i j : ℕ} (h : i ≤ j) :
    (run I P i).C ⊆ (run I P j).C := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (C_subset_step I P _)

theorem level_run_mono (I : Inst V E) (P : Params) (i : ℕ) (v : V) :
    (run I P i).level v ≤ (run I P (i + 1)).level v := le_lvl1 I P _ v

/-! ### Lemma 4.6 -/

open Classical in
/-- The number of `e`-raise iterations among iterations `1, …, n`. -/
noncomputable def raiseCount (I : Inst V E) (P : Params) (e : E) (n : ℕ) : ℕ :=
  ((Icc 1 n).filter (RaiseIter I P e)).card

theorem raiseCount_zero (e : E) : raiseCount I P e 0 = 0 := by simp [raiseCount]

open Classical in
theorem raiseCount_succ (e : E) (n : ℕ) :
    raiseCount I P e (n + 1) =
      raiseCount I P e n + if RaiseEdge I P (run I P n) e then 1 else 0 := by
  classical
  unfold raiseCount
  rw [show Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) by ext; simp; omega, filter_insert]
  have hn : n + 1 ∉ (Icc 1 n).filter (RaiseIter I P e) := by simp
  by_cases h : RaiseEdge I P (run I P n) e
  · have h' : RaiseIter I P e (n + 1) := ⟨by omega, by simpa using h⟩
    simp only [h', h, ↓reduceIte]
    rw [card_insert_of_notMem hn]
  · have h' : ¬ RaiseIter I P e (n + 1) := fun h' => h (by simpa using h'.2)
    simp only [h', h, ↓reduceIte, add_zero]

/-- While `e` is uncovered, `deal_n(e) = deal_0(e) · α^{#raises} · 2^{-∑_{v ∈ e} ℓ_n(v)}`. -/
theorem deal_formula (e : E) :
    ∀ n, ¬ I.Covered (run I P n).C e →
      (run I P n).deal e = deal0 I P e * P.α ^ raiseCount I P e n *
        (1 / 2 : ℝ) ^ (∑ v ∈ I.inc e, (run I P n).level v)
  | 0, _ => by simp [raiseCount_zero, run, init]
  | n + 1, h => by
    have hjoin : ¬ I.Covered (joinC I P (run I P n)) e := h
    have hprev : ¬ I.Covered (run I P n).C e := fun hc =>
      h (I.covered_mono (C_subset_step I P _) hc)
    have ih := deal_formula e n hprev
    have hsum : ∑ v ∈ I.inc e, lvl1 I P (run I P n) v =
        ∑ v ∈ I.inc e, (run I P n).level v +
          ∑ v ∈ I.inc e, (lvl1 I P (run I P n) v - (run I P n).level v) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun v _ => by have := le_lvl1 I P (run I P n) v; omega
    change deal2 I P (run I P n) e = _
    rw [raiseCount_succ]
    simp only [deal2, deal1, hjoin, ite_false]
    change _ = _ * _ * (1 / 2 : ℝ) ^ (∑ v ∈ I.inc e, lvl1 I P (run I P n) v)
    rw [hsum, ih, pow_add]
    split_ifs <;> ring

theorem exists_deal0_eq (e : E) :
    ∃ v ∈ I.inc e, deal0 I P e = P.c₀ * (I.w v / I.deg v) := by
  obtain ⟨v, hv, h⟩ := exists_mem_eq_inf' (I.inc_nonempty e) (fun v => I.w v / I.deg v)
  exact ⟨v, hv, by rw [deal0, h]⟩

/-- The key inequality of Lemma 4.6: `α^{#raises} ≤ Δ · 2^{f z} / (2 c₀)`. -/
theorem pow_raiseCount_le (hP : P.Valid I) (e : E) {Δ : ℕ} (hΔ : ∀ v, I.deg v ≤ Δ) :
    ∀ n, P.α ^ raiseCount I P e n ≤ Δ * 2 ^ (P.f * P.z) / (2 * P.c₀) := by
  intro n
  induction n with
  | zero =>
    -- `e` is uncovered at the end of iteration 0; handled by the general case below
    rw [raiseCount_zero, pow_zero]
    obtain ⟨v, hv, -⟩ := exists_deal0_eq (I := I) (P := P) e
    have h1 : (1 : ℝ) ≤ Δ := by exact_mod_cast (I.deg_pos hv).trans_le (hΔ v)
    have h2 : (1 : ℝ) ≤ 2 ^ (P.f * P.z) := one_le_pow₀ (by norm_num)
    have hc := hP.c₀_le; have hc0 := hP.c₀_pos
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  | succ n ih =>
    by_cases hcov : I.Covered (run I P (n + 1)).C e
    · rw [raiseCount_succ]
      have : ¬ RaiseEdge I P (run I P n) e := fun h => h.1 hcov
      simp only [this, ↓reduceIte, add_zero]; exact ih
    · have hf := deal_formula e (n + 1) hcov
      obtain ⟨v, hv, h0⟩ := exists_deal0_eq (I := I) (P := P) e
      have hvC : v ∉ (run I P (n + 1)).C := fun h => hcov ⟨v, hv, h⟩
      have h41 := claim_4_1 hP (n + 1) hvC
      have he : e ∈ I.uncov (run I P (n + 1)).C v := I.mem_uncov.2 ⟨hv, hcov⟩
      have hle1 : (run I P (n + 1)).deal e ≤ (1 / 2 : ℝ) * I.w v := by
        refine (single_le_sum (fun e' _ => ((inv_run hP (n + 1)).deal_pos e').le) he).trans
          (h41.trans ?_)
        apply mul_le_mul_of_nonneg_right _ (I.w_pos v).le
        exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega) |>.trans (by norm_num)
      -- bound on the total number of halvings
      have hL : ∑ u ∈ I.inc e, (run I P (n + 1)).level u ≤ P.f * P.z := by
        calc ∑ u ∈ I.inc e, (run I P (n + 1)).level u ≤ ∑ _u ∈ I.inc e, P.z :=
              sum_le_sum fun u _ => (claim_4_4 hP _ u).le
          _ = (I.inc e).card * P.z := by rw [sum_const, smul_eq_mul]
          _ ≤ P.f * P.z := Nat.mul_le_mul_right _ (hP.rank_le e)
      set L := ∑ u ∈ I.inc e, (run I P (n + 1)).level u
      set R := raiseCount I P e (n + 1)
      have hdeg : (0 : ℝ) < I.deg v := by exact_mod_cast I.deg_pos hv
      have hdegΔ : (I.deg v : ℝ) ≤ Δ := by exact_mod_cast hΔ v
      have hw := I.w_pos v
      have hc0 := hP.c₀_pos
      have h2L : (2 : ℝ) ^ L * (1 / 2 : ℝ) ^ L = 1 := by
        rw [← mul_pow]; norm_num
      have h2Lle : (2 : ℝ) ^ L ≤ 2 ^ (P.f * P.z) := pow_le_pow_right₀ (by norm_num) hL
      rw [hf, h0] at hle1
      -- `c₀ w/deg · α^R · 2^{-L} ≤ w/2`, hence `α^R ≤ deg · 2^L / (2 c₀)`
      have hαR : P.α ^ R ≤ I.deg v * 2 ^ L / (2 * P.c₀) := by
        rw [le_div_iff₀ (by positivity)]
        have h3 : P.c₀ * (I.w v / I.deg v) * P.α ^ R * (1 / 2 : ℝ) ^ L * (2 ^ L * I.deg v)
            ≤ 1 / 2 * I.w v * (2 ^ L * I.deg v) :=
          mul_le_mul_of_nonneg_right hle1 (by positivity)
        have h4 : P.c₀ * (I.w v / I.deg v) * P.α ^ R * (1 / 2 : ℝ) ^ L * (2 ^ L * I.deg v)
            = P.c₀ * I.w v * P.α ^ R := by
          field_simp
          rw [mul_assoc, ← mul_pow]; norm_num
        rw [h4] at h3
        have h5 : P.c₀ * I.w v * P.α ^ R * 2 ≤ I.w v * (2 ^ L * I.deg v) := by linarith
        have h6 : I.w v * (P.α ^ R * (2 * P.c₀)) ≤ I.w v * (I.deg v * 2 ^ L) := by
          nlinarith
        exact le_of_mul_le_mul_left h6 hw
      refine hαR.trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul hdegΔ h2Lle (by positivity) (by positivity)

/-- Lemma 4.6 (general initial factor `c₀`): the number of `e`-raise iterations is at most
`log_α(Δ · 2^{f z} / (2 c₀))`. -/
theorem lemma_4_6_general (hP : P.Valid I) (e : E) {Δ : ℕ} (hΔ : ∀ v, I.deg v ≤ Δ) (n : ℕ) :
    (raiseCount I P e n : ℝ) ≤ Real.logb P.α (Δ * 2 ^ (P.f * P.z) / (2 * P.c₀)) := by
  have hα := hP.one_lt_α
  obtain ⟨v, hv, -⟩ := exists_deal0_eq (I := I) (P := P) e
  have h1 : (0 : ℝ) < Δ := by exact_mod_cast (I.deg_pos hv).trans_le (hΔ v)
  have hc0 := hP.c₀_pos
  rw [Real.le_logb_iff_rpow_le hα (by positivity), Real.rpow_natCast]
  exact pow_raiseCount_le hP e hΔ n

/-- Lemma 4.6: the number of `e`-raise iterations is bounded by `log_α(Δ · 2^{f·z})` (for the
paper's initial deal `deal₀(e) = 0.5 · min_{v ∈ e} w(v)/|E(v)|`, i.e. `c₀ = 1/2`). -/
theorem lemma_4_6 (hP : P.Valid I) (hc : P.c₀ = 1 / 2) (e : E) {Δ : ℕ}
    (hΔ : ∀ v, I.deg v ≤ Δ) (n : ℕ) :
    (raiseCount I P e n : ℝ) ≤ Real.logb P.α (Δ * 2 ^ (P.f * P.z)) := by
  have := lemma_4_6_general hP e hΔ n
  rwa [hc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, div_one] at this

/-! ### Lemma 4.7 -/

open Classical in
/-- The number of `v`-stuck iterations among `1, …, n` in which `v` has level `ℓ`. -/
noncomputable def stuckCount (I : Inst V E) (P : Params) (v : V) (ℓ n : ℕ) : ℕ :=
  ((Icc 1 n).filter fun i => StuckIter I P v i ∧ (run I P i).level v = ℓ).card

theorem sum_Ioc_incr (Φ : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) :
    ∑ i ∈ Ioc a b, (Φ i - Φ (i - 1)) = Φ b - Φ a := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ioc_succ_top hab, ih, Nat.add_sub_cancel]; ring

/-- Telescoping for a monotone sequence: the increments over a subset `S ⊆ (a, b]` sum to at most
`Φ b - Φ a`. -/
theorem sum_incr_le {Φ : ℕ → ℝ} (hΦ : ∀ j, Φ j ≤ Φ (j + 1)) {a b : ℕ} (hab : a ≤ b)
    {S : Finset ℕ} (hS : S ⊆ Ioc a b) : ∑ i ∈ S, (Φ i - Φ (i - 1)) ≤ Φ b - Φ a := by
  have hnn : ∀ i ∈ Ioc a b, 0 ≤ Φ i - Φ (i - 1) := fun i hi => by
    have := hΦ (i - 1); rw [show i - 1 + 1 = i by have := (mem_Ioc.1 hi).1; omega] at this
    linarith
  rw [← sum_Ioc_incr Φ hab]
  exact sum_le_sum_of_subset_of_nonneg hS fun i hi _ => hnn i hi

/-- In a `v`-stuck iteration `i` at level `ℓ`, the load of `v` grows by more than
`κ α⁻¹ 2^{-(ℓ+1)} w(v)`. -/
theorem stuck_incr (hP : P.Valid I) {v : V} {j : ℕ} (hst : StuckIter I P v (j + 1)) :
    P.κ * P.α⁻¹ * (1 / 2 : ℝ) ^ ((run I P (j + 1)).level v + 1) * I.w v <
      I.load (run I P (j + 1)).δ v - I.load (run I P j).δ v := by
  obtain ⟨-, -, hnr⟩ := hst
  simp only [Nat.add_sub_cancel] at hnr
  have hs := inv_run hP j
  change P.κ * P.α⁻¹ * (1 / 2 : ℝ) ^ (lvl1 I P (run I P j) v + 1) * I.w v <
    I.load (step I P (run I P j)).δ v - _
  rw [load_step]
  have hα := hP.one_lt_α
  have hκ := hP.κ_pos
  have hlt : P.α⁻¹ * (1 / 2 : ℝ) ^ (lvl1 I P (run I P j) v + 1) * I.w v <
      ∑ e ∈ I.uncov (joinC I P (run I P j)) v, deal1 I P (run I P j) e := lt_of_not_ge hnr
  have hle : ∑ e ∈ I.uncov (joinC I P (run I P j)) v, deal1 I P (run I P j) e ≤
      ∑ e ∈ I.uncov (joinC I P (run I P j)) v, deal2 I P (run I P j) e := by
    refine sum_le_sum fun e _ => ?_
    have h1 : 0 ≤ deal1 I P (run I P j) e := by
      unfold deal1; split_ifs
      · exact (hs.deal_pos e).le
      · exact mul_nonneg (hs.deal_pos e).le (by positivity)
    unfold deal2; split_ifs
    · exact le_mul_of_one_le_left h1 hα.le
    · exact le_rfl
  have := mul_lt_mul_of_pos_left (hlt.trans_le hle) hκ
  linarith

/-- Lemma 4.7 (corrected bound): for every vertex `v` and level `ℓ`, the number of `v`-stuck
iterations at level `ℓ` is `< α/κ + 1` (`κ = 1` in Section 3, `κ = 1/2` in Appendix C). -/
theorem lemma_4_7 (hP : P.Valid I) (v : V) (ℓ n : ℕ) :
    (stuckCount I P v ℓ n : ℝ) < P.α / P.κ + 1 := by
  classical
  have hα := hP.one_lt_α
  have hκ := hP.κ_pos
  have hακ : 0 < P.α / P.κ := div_pos (by linarith) hκ
  set S := (Icc 1 n).filter fun i => StuckIter I P v i ∧ (run I P i).level v = ℓ with hSdef
  have hcard : stuckCount I P v ℓ n = S.card := by
    unfold stuckCount; rw [hSdef]
  rw [hcard]
  by_cases hk : S.card ≤ 1
  · have : (S.card : ℝ) ≤ 1 := by exact_mod_cast hk
    linarith
  push Not at hk
  have hne : S.Nonempty := card_pos.1 (by omega)
  set Φ : ℕ → ℝ := fun j => I.load (run I P j).δ v
  have hΦ : ∀ j, Φ j ≤ Φ (j + 1) := fun j => load_le_load_step hP (inv_run hP j) v
  have hmemS : ∀ i ∈ S, 1 ≤ i ∧ StuckIter I P v i ∧ (run I P i).level v = ℓ := fun i hi => by
    have := mem_filter.1 hi; exact ⟨(mem_Icc.1 this.1).1, this.2⟩
  set i1 := S.min' hne
  set ik := S.max' hne
  have hi1 := hmemS i1 (min'_mem S hne)
  have hik := hmemS ik (max'_mem S hne)
  -- bounds from Claim 4.2
  have hlow : I.w v * (1 - (1 / 2 : ℝ) ^ ℓ) ≤ Φ (i1 - 1) := by
    have := (claim_4_2 hP hi1.1 hi1.2.1.2.1).1; rwa [hi1.2.2] at this
  have hup : Φ (ik - 1) ≤ (1 - (1 / 2 : ℝ) ^ (ℓ + 1)) * I.w v := by
    have := (claim_4_2 hP hik.1 hik.2.1.2.1).2; rwa [hik.2.2] at this
  set S' := S.erase ik
  have hS'card : S'.card = S.card - 1 := card_erase_of_mem (max'_mem S hne)
  have hS'ne : S'.Nonempty := card_pos.1 (by omega)
  have hsub : S' ⊆ Ioc (i1 - 1) (ik - 1) := by
    intro i hi
    obtain ⟨hne', hiS⟩ := mem_erase.1 hi
    have h1 : i1 ≤ i := min'_le S i hiS
    have h2 : i ≤ ik := le_max' S i hiS
    have h3 := (hmemS i hiS).1
    rw [mem_Ioc]; omega
  have htel := sum_incr_le hΦ (by have := min'_le S ik (max'_mem S hne); omega) hsub
  set c := P.κ * P.α⁻¹ * (1 / 2 : ℝ) ^ (ℓ + 1) * I.w v
  have hlt : ∑ _i ∈ S', c < ∑ i ∈ S', (Φ i - Φ (i - 1)) := by
    refine sum_lt_sum_of_nonempty hS'ne fun i hi => ?_
    have hiS := (mem_erase.1 hi).2
    obtain ⟨h1, hst, hl⟩ := hmemS i hiS
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have := stuck_incr hP hst
    rw [hl] at this
    show c < Φ (j + 1) - Φ (j + 1 - 1)
    rw [Nat.add_sub_cancel]
    exact this
  rw [sum_const, nsmul_eq_mul, hS'card] at hlt
  have hw := I.w_pos v
  have hpow : (1 / 2 : ℝ) ^ (ℓ + 1) * I.w v > 0 := by positivity
  have key : ((S.card - 1 : ℕ) : ℝ) * c < (1 / 2 : ℝ) ^ (ℓ + 1) * I.w v := by
    have : (1 / 2 : ℝ) ^ ℓ = 2 * (1 / 2 : ℝ) ^ (ℓ + 1) := by ring
    rw [this] at hlow
    linarith
  have hc : c = P.κ / P.α * ((1 / 2 : ℝ) ^ (ℓ + 1) * I.w v) := by
    simp only [c]; field_simp
  rw [hc, ← mul_assoc] at key
  have key2 : ((S.card - 1 : ℕ) : ℝ) * (P.κ / P.α) < 1 := by
    by_contra hh; push Not at hh
    nlinarith
  have hcast : ((S.card - 1 : ℕ) : ℝ) = S.card - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast] at key2
  have : (S.card - 1 : ℝ) < P.α / P.κ := by
    rw [lt_div_iff₀ hκ]
    have : (S.card - 1 : ℝ) * (P.κ / P.α) * P.α = (S.card - 1) * P.κ := by field_simp
    nlinarith
  linarith

/-- Lemma 4.7 in natural numbers: at most `⌈α/κ⌉` `v`-stuck iterations per level. -/
theorem lemma_4_7_ceil (hP : P.Valid I) (v : V) (ℓ n : ℕ) :
    stuckCount I P v ℓ n ≤ ⌈P.α / P.κ⌉₊ := by
  have h := lemma_4_7 hP v ℓ n
  have h2 := Nat.le_ceil (P.α / P.κ)
  have : (stuckCount I P v ℓ n : ℝ) < ⌈P.α / P.κ⌉₊ + 1 := by linarith
  exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)

/-- Lemma 4.7 as stated in the paper (`≤ α`), valid when `α` is an integer (`κ = 1`). -/
theorem lemma_4_7_of_nat (hP : P.Valid I) (hκ : P.κ = 1) {m : ℕ} (hm : P.α = m) (v : V)
    (ℓ n : ℕ) : stuckCount I P v ℓ n ≤ m := by
  have := lemma_4_7_ceil hP v ℓ n
  rwa [hκ, div_one, hm, Nat.ceil_natCast] at this

/-- Lemma C.2 as stated in the paper (`≤ 2α`, Appendix C variant `κ = 1/2`), valid when `α` is an
integer. -/
theorem lemma_C_2_of_nat (hP : P.Valid I) (hκ : P.κ = 1 / 2) {m : ℕ} (hm : P.α = m) (v : V)
    (ℓ n : ℕ) : stuckCount I P v ℓ n ≤ 2 * m := by
  have := lemma_4_7_ceil hP v ℓ n
  rwa [hκ, hm, show (m : ℝ) / (1 / 2) = ((2 * m : ℕ) : ℝ) by push_cast; ring,
    Nat.ceil_natCast] at this

/-! ### Theorem 4.8 -/

/-- Every iteration in which `e` is still uncovered is an `e`-raise iteration or a `v`-stuck
iteration for some `v ∈ e`. -/
theorem raise_or_stuck {e : E} {i : ℕ} (hi : 1 ≤ i) (he : ¬ I.Covered (run I P i).C e) :
    RaiseIter I P e i ∨ ∃ v ∈ I.inc e, StuckIter I P v i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  by_cases hr : RaiseEdge I P (run I P j) e
  · exact Or.inl ⟨hi, by simpa using hr⟩
  · right
    have hjoin : ¬ I.Covered (joinC I P (run I P j)) e := he
    have : ∃ v ∈ I.inc e, ¬ Raise I P (run I P j) v := by
      by_contra h; push Not at h; exact hr ⟨hjoin, h⟩
    obtain ⟨v, hv, hnr⟩ := this
    exact ⟨v, hv, hi, I.active_of_mem he hv, by simpa using hnr⟩

/-- The iteration bound of Theorem 4.8: `⌊log_α(Δ·2^{fz}/(2c₀))⌋ + f·z·⌈α/κ⌉ + 1`. -/
noncomputable def iterBound (P : Params) (Δ : ℕ) : ℕ :=
  ⌊Real.logb P.α (Δ * 2 ^ (P.f * P.z) / (2 * P.c₀))⌋₊ + P.f * P.z * ⌈P.α / P.κ⌉₊ + 1

theorem terminated_mono {i j : ℕ} (h : Terminated I P i) (hij : i ≤ j) : Terminated I P j :=
  fun e => I.covered_mono (C_run_mono I P hij) (h e)

/-- Theorem 4.8: for every `α > 1` (the paper: `α ≥ 2`), Algorithm MWHVC has terminated (every
edge is covered) by the end of iteration `⌊log_α(Δ·2^{fz}/(2c₀))⌋ + f·z·⌈α/κ⌉ + 1`, where `Δ`
bounds the vertex degrees. -/
theorem theorem_4_8 (hP : P.Valid I) {Δ : ℕ} (hΔ : ∀ v, I.deg v ≤ Δ) :
    Terminated I P (iterBound P Δ) := by
  classical
  intro e
  by_contra he
  set N := iterBound P Δ
  have hcov : Icc 1 N ⊆ (Icc 1 N).filter (RaiseIter I P e) ∪
      (I.inc e).biUnion fun v => (range P.z).biUnion fun ℓ =>
        (Icc 1 N).filter fun i => StuckIter I P v i ∧ (run I P i).level v = ℓ := by
    intro i hi
    have hi1 := (mem_Icc.1 hi).1
    have hei : ¬ I.Covered (run I P i).C e := fun h =>
      he (I.covered_mono (C_run_mono I P (mem_Icc.1 hi).2) h)
    rcases raise_or_stuck hi1 hei with h | ⟨v, hv, h⟩
    · exact mem_union_left _ (mem_filter.2 ⟨hi, h⟩)
    · refine mem_union_right _ (mem_biUnion.2 ⟨v, hv, mem_biUnion.2 ⟨(run I P i).level v,
        mem_range.2 (claim_4_4 hP i v), mem_filter.2 ⟨hi, h, rfl⟩⟩⟩)
  have hR : raiseCount I P e N ≤ ⌊Real.logb P.α (Δ * 2 ^ (P.f * P.z) / (2 * P.c₀))⌋₊ :=
    Nat.le_floor (lemma_4_6_general hP e hΔ N)
  have hS : ∀ v, (∑ ℓ ∈ range P.z, stuckCount I P v ℓ N) ≤ P.z * ⌈P.α / P.κ⌉₊ := fun v => by
    calc ∑ ℓ ∈ range P.z, stuckCount I P v ℓ N ≤ ∑ _ℓ ∈ range P.z, ⌈P.α / P.κ⌉₊ :=
          sum_le_sum fun ℓ _ => lemma_4_7_ceil hP v ℓ N
      _ = P.z * ⌈P.α / P.κ⌉₊ := by rw [sum_const, card_range, smul_eq_mul]
  have hcard := card_le_card hcov
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  have h1 := card_union_le ((Icc 1 N).filter (RaiseIter I P e))
    ((I.inc e).biUnion fun v => (range P.z).biUnion fun ℓ =>
        (Icc 1 N).filter fun i => StuckIter I P v i ∧ (run I P i).level v = ℓ)
  have h2 := card_biUnion_le (s := I.inc e) (t := fun v => (range P.z).biUnion fun ℓ =>
        (Icc 1 N).filter fun i => StuckIter I P v i ∧ (run I P i).level v = ℓ)
  have h3 : ∀ v, ((range P.z).biUnion fun ℓ =>
        (Icc 1 N).filter fun i => StuckIter I P v i ∧ (run I P i).level v = ℓ).card ≤
        P.z * ⌈P.α / P.κ⌉₊ := fun v =>
    (card_biUnion_le).trans (by
      refine le_of_eq_of_le ?_ (hS v)
      refine sum_congr rfl fun ℓ _ => ?_
      unfold stuckCount
      congr 1)
  have h4 : ∑ v ∈ I.inc e, ((range P.z).biUnion fun ℓ =>
        (Icc 1 N).filter fun i => StuckIter I P v i ∧ (run I P i).level v = ℓ).card ≤
        P.f * (P.z * ⌈P.α / P.κ⌉₊) :=
    (sum_le_sum fun v _ => h3 v).trans (by
      rw [sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ (hP.rank_le e))
  have h5 : ((Icc 1 N).filter (RaiseIter I P e)).card = raiseCount I P e N := by
    unfold raiseCount; congr 1
  have hN : N = ⌊Real.logb P.α (Δ * 2 ^ (P.f * P.z) / (2 * P.c₀))⌋₊ +
      P.f * P.z * ⌈P.α / P.κ⌉₊ + 1 := rfl
  rw [h5] at h1
  have : N ≤ ⌊Real.logb P.α (Δ * 2 ^ (P.f * P.z) / (2 * P.c₀))⌋₊ +
      P.f * (P.z * ⌈P.α / P.κ⌉₊) := by omega
  rw [← mul_assoc] at this
  omega

/-- Theorem 4.8, asymptotic form: for `c₀ = 1/2` and `α ≥ 2` the bound of `theorem_4_8` is at most
`log_α Δ + f·z·(α/κ + 2) + 1 = O(log_α Δ + f·z·α)`. -/
theorem iterBound_le (hP : P.Valid I) (hc : P.c₀ = 1 / 2) (hα : 2 ≤ P.α) {Δ : ℕ} (hΔ : 1 ≤ Δ) :
    (iterBound P Δ : ℝ) ≤ Real.logb P.α Δ + P.f * P.z * (P.α / P.κ + 2) + 1 := by
  have hκ := hP.κ_pos
  have hα1 : 1 < P.α := by linarith
  have hΔ' : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hlog : Real.logb P.α (Δ * 2 ^ (P.f * P.z) / (2 * P.c₀)) =
      Real.logb P.α Δ + (P.f * P.z : ℕ) * Real.logb P.α 2 := by
    rw [hc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, div_one,
      Real.logb_mul (by positivity) (by positivity), Real.logb_pow]
  have hl2 : Real.logb P.α 2 ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow hα1 (by norm_num), Real.rpow_one]; exact hα
  have hl0 : 0 ≤ Real.logb P.α Δ := Real.logb_nonneg hα1 hΔ'
  have hl20 : 0 ≤ Real.logb P.α 2 := Real.logb_nonneg hα1 (by norm_num)
  have hfl : (⌊Real.logb P.α (Δ * 2 ^ (P.f * P.z) / (2 * P.c₀))⌋₊ : ℝ) ≤
      Real.logb P.α Δ + P.f * P.z := by
    refine (Nat.floor_le (by rw [hlog]; positivity)).trans ?_
    rw [hlog]; push_cast
    have : (0 : ℝ) ≤ P.f * P.z := by positivity
    nlinarith
  have hce : (⌈P.α / P.κ⌉₊ : ℝ) < P.α / P.κ + 1 := Nat.ceil_lt_add_one (by positivity)
  unfold iterBound
  push_cast
  have : (0 : ℝ) ≤ P.f * P.z := by positivity
  nlinarith

/-- `z = O(log(f/ε))`: `z ≤ log₂((f+ε)/ε) + 1`. -/
theorem z_le (hP : P.Valid I) : (P.z : ℝ) ≤ Real.logb 2 ((P.f + P.ε) / P.ε) + 1 := by
  have h := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    ((one_le_inv₀ hP.β_pos).2 hP.β_lt_one.le) : 0 ≤ Real.logb 2 P.β⁻¹)
  unfold Params.z
  have : P.β⁻¹ = (P.f + P.ε) / P.ε := by unfold Params.β; rw [inv_div]
  rw [this] at h ⊢
  exact h.le

end Podc.CoveringPrimalDual
