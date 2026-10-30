import Papers.PODC2024.PPGameDynamics.IGT
import Podc.Probability.Markov.Mixing

/-!
# Mixing time of the Ehrenfest process (Theorem 2.5)

`IsMixedAt T π t` is `d(t) ≤ 1/4`, so `t_mix ≤ t` iff `IsMixedAt T π t'` for some `t' ≤ t`.

* `theorem_2_5_lower`: `t_mix ≥ (k-1) m / 2` (the `Ω(km)` lower bound; Proposition A.9, with the
  diameter `(k-1)m` instead of the paper's `km`);
* `isMixedAt_two_two`: for `k = m = 2` and `b ≤ a`, `d(t) ≤ 1/4` forces `t ≥ 1/(2a)`: each step is
  null with probability `≥ 1 - a`;
* `theorem_2_5_upper_false`, `theorem_2_5_upper_false_ne`: hence the upper bounds
  `t_mix = O(k² m log m)` (`a = b`) and `t_mix = O(min{k/|a-b|, k²} m log m)` (`a ≠ b`) of
  Theorem 2.5 fail when `a + b → 0`: the constant must depend on `a + b` (the correct bounds
  carry a factor `1/(a+b)` on the `k²` terms; Prop. A.7 ignores the laziness of the walk `Z_t`);
* `lemma_A_8_false`: the explicit, constant-free bound `d(2Φ log(4m)) ≤ 1/4` of Lemma A.8 fails at
  the fixed parameters `k = m = 2`, `a = 1/100`, `b = 1/200`.
-/

open Finset Matrix Cslib.Probability.Markov

namespace Podc.PPGameDynamics

variable {k m : ℕ} {a b : ℝ}

/-- One step of the Ehrenfest process changes the potential `∑ j x_j` by at most `1`. -/
lemma pot_le_of_ehrenfest_pos {x y : Simplex k m} (h : 0 < ehrenfest k a b m x y) :
    y.pot ≤ x.pot + 1 ∧ x.pot ≤ y.pot + 1 := by
  by_cases hxy : x = y
  · subst hxy; omega
  rw [ehrenfest, urnKernel_offDiag _ hxy] at h
  have hex : ∃ i j, x.move i j = y ∧ ehrRate a b i j ≠ 0 := by
    by_contra hc
    push Not at hc
    have h0 : ∑ i, ∑ j, (if x.move i j = y then ehrRate a b i j * (x.1 i / m) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
        split_ifs with h
        · rw [hc i j h]; ring
        · rfl
    linarith
  obtain ⟨i, j, hm, hr⟩ := hex
  obtain ⟨hi, hij⟩ := Simplex.genuine_of_move_eq hm hxy
  have hp := x.pot_move hi hij
  rw [hm] at hp
  have hij' : j.val = i.val + 1 ∨ i.val = j.val + 1 := by
    unfold ehrRate at hr
    split_ifs at hr with h1 h2
    · exact Or.inl h1
    · exact Or.inr h2
    · exact absurd rfl hr
  omega

/-- `t` steps change the potential by at most `t`. -/
lemma pot_le_of_pow_pos (hab : 0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1) (t : ℕ) {x y : Simplex k m}
    (h : 0 < (ehrenfest k a b m ^ t) x y) : y.pot ≤ x.pot + t ∧ x.pot ≤ y.pot + t := by
  induction t generalizing y with
  | zero =>
    have : x = y := by
      by_contra hne; simp [hne] at h
    subst this; omega
  | succ t ih =>
    rw [pow_succ, mul_apply] at h
    have hT := ehrenfest_mem (k := k) (m := m) hab.1 hab.2.1 hab.2.2
    obtain ⟨z, -, hz⟩ : ∃ z ∈ (univ : Finset (Simplex k m)),
        0 < (ehrenfest k a b m ^ t) x z * ehrenfest k a b m z y := by
      by_contra hc
      push Not at hc
      exact absurd (Finset.sum_nonpos hc) (not_le.2 h)
    have h1 : 0 < (ehrenfest k a b m ^ t) x z :=
      pos_of_mul_pos_left hz (nonneg_of_mem_rowStochastic hT)
    have h2 : 0 < ehrenfest k a b m z y :=
      pos_of_mul_pos_right hz (pow_apply_nonneg (fun _ _ => nonneg_of_mem_rowStochastic hT) _ _ _)
    have := ih h1
    have := pot_le_of_ehrenfest_pos h2
    omega

/-- All balls in the last urn. -/
def Simplex.top (hk : 0 < k) : Simplex k m :=
  ⟨Pi.single ⟨k - 1, by omega⟩ m, by simp⟩

lemma Simplex.pot_top (hk : 0 < k) : (Simplex.top (m := m) hk).pot = (k - 1) * m := by
  unfold Simplex.pot Simplex.top
  rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
  · simp
  · intro l _ hl; simp [hl]
  · simp

lemma Simplex.pot_base (hk : 0 < k) : (Simplex.base (m := m) hk).pot = 0 := by
  unfold Simplex.pot Simplex.base
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = ⟨0, hk⟩
  · subst hl; simp
  · simp [hl]

/-- **Theorem 2.5, lower bound** (`t_mix = Ω(km)`, via Proposition A.9): if `d(t) ≤ 1/4` then
`(k-1) m ≤ 2t`. This holds for every distribution `π` and all `a, b`. -/
theorem theorem_2_5_lower (hk : 0 < k) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    {π : Simplex k m → ℝ} (hπ : ∑ s, π s = 1) {t : ℕ}
    (hmix : IsMixedAt (ehrenfest k a b m) π t) : (k - 1) * m ≤ 2 * t := by
  by_contra hlt
  push Not at hlt
  refine not_isMixedAt_of_disjoint (ehrenfest_mem ha hb hab) hπ t (Simplex.base hk)
    (Simplex.top hk) (univ.filter fun s => s.pot ≤ t) ?_ ?_ hmix
  · intro s hs
    have := (pot_le_of_pow_pos ⟨ha, hb, hab⟩ t hs).1
    rw [Simplex.pot_base] at this
    simpa using this
  · intro s hs
    have := (pot_le_of_pow_pos ⟨ha, hb, hab⟩ t hs).2
    rw [Simplex.pot_top] at this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    omega

/-- For `k = m = 2` and `b ≤ a`: `d(t) ≤ 1/4` forces `1 ≤ 2 a t`. -/
theorem isMixedAt_two_two (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hab : a + b ≤ 1) {t : ℕ}
    (hmix : IsMixedAt (ehrenfest 2 a b 2) (multinomialPMF (ehrParam 2 (a / b))) t) :
    1 ≤ 2 * a * t := by
  have hT := ehrenfest_mem (k := 2) (m := 2) ha.le hb.le hab
  set x : Simplex 2 2 := Simplex.base (by norm_num)
  -- `P(x, x) = 1 - a`
  have hxx : ehrenfest 2 a b 2 x x = 1 - a := by
    rw [ehrenfest_apply_self]
    simp [x, Simplex.base, Fin.sum_univ_two, Pi.single_apply]
  -- `π(x) ≤ 1/4`
  have hπx : multinomialPMF (ehrParam 2 (a / b)) x ≤ 1 / 4 := by
    rw [multinomialPMF_base_two]
    simp only [ehrParam, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have hL : 1 ≤ a / b := by rw [le_div_iff₀ hb]; linarith
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- `P^t(x, x) ≥ (1 - a)^t ≥ 1 - t a`
  have hpow := pow_apply_self_ge (T := ehrenfest 2 a b 2)
    (fun i j => nonneg_of_mem_rowStochastic (i := i) (j := j) hT) x t
  rw [hxx] at hpow
  have hbern : 1 + (t : ℝ) * (-a) ≤ (1 + -a) ^ t := one_add_mul_le_pow (by linarith) t
  -- total variation
  have hsum1 : ∑ s, (ehrenfest 2 a b 2 ^ t) x s = 1 :=
    sum_row_of_mem_rowStochastic (pow_mem_rowStochastic hT t) x
  have hπd := isDistribution_multinomialPMF (m := 2)
    (fun j => (ehrParam_pos (k := 2) (by norm_num) (div_pos ha hb) j).le)
    (sum_ehrParam (by norm_num) (div_pos ha hb))
  have htv := sub_le_tvDist (μ := fun s => (ehrenfest 2 a b 2 ^ t) x s)
    (ν := multinomialPMF (ehrParam 2 (a / b))) (by rw [hsum1, hπd.2]) {x}
  simp only [Finset.sum_singleton] at htv
  have := hmix x
  have h1 : (1 + -a) ^ t = (1 - a) ^ t := by ring
  nlinarith

/-- The bound `f(k, a, b, m)` of Theorem 2.5 (without the `O`). -/
noncomputable def thm25Bound (k : ℕ) (a b : ℝ) (m : ℕ) : ℝ :=
  (if a = b then (k : ℝ) ^ 2 else min (k / |a - b|) ((k : ℝ) ^ 2)) * m * Real.log m

/-- **Theorem 2.5, upper bound, is false as stated** (case `a = b`): there is no constant `C`
with `t_mix ≤ C k² m log m` for all `a = b` (here `k = m = 2`), since `t_mix ≥ 1/(2a)`. -/
theorem theorem_2_5_upper_false :
    ¬ ∃ C : ℝ, ∀ a b : ℝ, 0 < a → 0 < b → a + b ≤ 1 → ∃ t : ℕ,
      (t : ℝ) ≤ C * thm25Bound 2 a b 2 ∧
      IsMixedAt (ehrenfest 2 a b 2) (multinomialPMF (ehrParam 2 (a / b))) t := by
  rintro ⟨C, hC⟩
  set F : ℝ := 4 * 2 * Real.log 2
  have hF : 0 ≤ F := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  set ε : ℝ := 1 / (4 * (|C| * F + 1))
  have hε : 0 < ε := by positivity
  have hε2 : ε ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg C]
  obtain ⟨t, ht, hmix⟩ := hC ε ε hε hε (by linarith)
  have hbd : thm25Bound 2 ε ε 2 = F := by simp only [thm25Bound, ↓reduceIte, F]; push_cast; ring
  rw [hbd] at ht
  have h1 := isMixedAt_two_two hε hε le_rfl (by linarith) hmix
  have h2 : C * F ≤ |C| * F := mul_le_mul_of_nonneg_right (le_abs_self C) hF
  have h3 : 2 * ε * (t : ℝ) ≤ 2 * ε * (|C| * F) := by
    have := mul_le_mul_of_nonneg_left (ht.trans h2) (by positivity : (0 : ℝ) ≤ 2 * ε)
    linarith
  have h4 : 2 * ε * (|C| * F) < 1 := by
    have : 2 * ε * (|C| * F + 1) = 1 / 2 := by simp only [ε]; field_simp; ring
    nlinarith [abs_nonneg C]
  linarith

/-- **Theorem 2.5, upper bound, case `a ≠ b`, is false as stated**: with `a = 2b`,
`min{k/|a-b|, k²} = k²` for small `b`, but `t_mix ≥ 1/(2a)`. -/
theorem theorem_2_5_upper_false_ne :
    ¬ ∃ C : ℝ, ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b → a + b ≤ 1 → ∃ t : ℕ,
      (t : ℝ) ≤ C * thm25Bound 2 a b 2 ∧
      IsMixedAt (ehrenfest 2 a b 2) (multinomialPMF (ehrParam 2 (a / b))) t := by
  rintro ⟨C, hC⟩
  set F : ℝ := 4 * 2 * Real.log 2
  have hF : 0 ≤ F := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  set ε : ℝ := 1 / (8 * (|C| * F + 1))
  have hε : 0 < ε := by positivity
  have hε2 : ε ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg C]
  obtain ⟨t, ht, hmix⟩ := hC (2 * ε) ε (by positivity) hε (by intro h; linarith) (by linarith)
  have hbd : thm25Bound 2 (2 * ε) ε 2 = F := by
    have hne : 2 * ε ≠ ε := by intro h; linarith
    have habs : |2 * ε - ε| = ε := by rw [show 2 * ε - ε = ε by ring, abs_of_pos hε]
    have hmin : min (((2 : ℕ) : ℝ) / ε) (((2 : ℕ) : ℝ) ^ 2) = 4 := by
      rw [min_eq_right]
      · norm_num
      · rw [le_div_iff₀ hε]; push_cast; nlinarith
    simp only [thm25Bound, hne, ↓reduceIte, habs, hmin, F]
    push_cast; ring
  rw [hbd] at ht
  have h1 := isMixedAt_two_two (by positivity) hε (by linarith) (by linarith) hmix
  have h2 : C * F ≤ |C| * F := mul_le_mul_of_nonneg_right (le_abs_self C) hF
  have h3 : 2 * (2 * ε) * (t : ℝ) ≤ 2 * (2 * ε) * (|C| * F) := by
    have := mul_le_mul_of_nonneg_left (ht.trans h2) (by positivity : (0 : ℝ) ≤ 2 * (2 * ε))
    linarith
  have h4 : 2 * (2 * ε) * (|C| * F) < 1 := by
    have : 2 * (2 * ε) * (|C| * F + 1) = 1 / 2 := by simp only [ε]; field_simp; ring
    nlinarith [abs_nonneg C]
  linarith

/-- **Lemma A.8 is false** (and so are the explicit bounds of Lemma A.5 and Proposition A.7 it rests
on). Lemma A.8 (for `a > b > 0`, `a + b ≤ 1`, `k, m ≥ 2`) claims
`Pr[τ_couple > 2Φ·log(4m)] ≤ 1/4` with `Φ = min{k/|a-b|, k²}·m`, and the paper concludes
`d(2Φ·log(4m)) ≤ 1/4` via the standard coupling inequality (22). For `k = m = 2`, `a = 1/100`,
`b = 1/200` we get `Φ = 8` and `2Φ·log₂(4m) = 48` (with the natural logarithm it is even smaller), but
`d(t) > 1/4` for every `t ≤ 48` (indeed `t ≥ 1/(2a) = 50` is needed). Unlike
`theorem_2_5_upper_false`, this refutes an explicit, constant-free inequality at fixed `a, b`. -/
theorem lemma_A_8_false : ∀ t : ℕ,
    (t : ℝ) ≤ 2 * (min ((2 : ℝ) / |1 / 100 - 1 / 200|) (2 ^ 2) * 2) * Real.logb 2 (4 * 2) →
    ¬ IsMixedAt (ehrenfest 2 (1 / 100) (1 / 200) 2)
      (multinomialPMF (ehrParam 2 ((1 / 100) / (1 / 200)))) t := by
  intro t ht hmix
  have h1 := isMixedAt_two_two (a := 1 / 100) (b := 1 / 200) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hmix
  have hlog : Real.logb 2 (4 * 2) = 3 := by
    rw [show (4 * 2 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hmin : min ((2 : ℝ) / |1 / 100 - 1 / 200|) (2 ^ 2) = 4 := by
    rw [abs_of_pos (by norm_num)]; norm_num
  rw [hlog, hmin] at ht
  linarith

end Podc.PPGameDynamics
