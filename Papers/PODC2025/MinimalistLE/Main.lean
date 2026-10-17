import Papers.PODC2025.MinimalistLE.Probability

/-!
# Main theorems: Theorem 2 (almost-sure part) and Theorem 3

Model: connected finite graph `G`, initial configuration satisfying Eq. (2) (all nodes waiting,
at least one leader; the paper's `W•` everywhere is `initAll`), i.i.d. `Bernoulli(p)` coins
(`coinMeasure p` on `ℕ × V → Bool`). `UniqueFrom G init T ω` is Definition 1 from round `T` on.

* `theorem2_ae` — for every `p ∈ (0,1)`, BFW solves Eventual Leader Election almost surely.
* `theorem2_tail` — explicit bound
  `P(no unique leader from round k(2D+3)) ≤ n²·(1 - (1-(1-p)^{D+1})(1-p)^{2D+3})^k`
  for every `D ≥` the diameter. (For constant `p` this only gives time `exp(O(D))·log n`; the
  paper's `O(D² log n)` bound is `theorem2_whp` in `Theorem2.lean`.)
* `theorem3` / `theorem3_whp` — for `p = 1/(D+1)`, `D ≥ 1` any upper bound on the diameter:
  `P(no unique leader from round k(2D+3)) ≤ n²·(127/128)^k`, hence with probability
  `≥ 1 - 1/n²` a single leader is elected from round `(2D+3)·⌈512 ln n⌉` on: `O(D log n)` rounds.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory unitInterval Cslib.Probability
open scoped ENNReal

namespace MinimalistLE

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {init : V → St}

theorem toReal_r (p : I) : ((toNNReal (σ p) : ℝ≥0∞)).toReal = 1 - p := by
  simp [coe_symm_eq]

theorem r_le_one (p : I) : ((toNNReal (σ p) : ℝ≥0∞)) ≤ 1 := by
  rw [← ENNReal.coe_one, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]; simp [coe_symm_eq, p.2.1]

theorem goodProb_le_one (p : I) (D : ℕ) : goodProb p D ≤ 1 := by
  unfold goodProb
  calc _ ≤ (1 : ℝ≥0∞) * 1 := by
        gcongr
        · exact tsub_le_self
        · exact pow_le_one₀ (zero_le) (r_le_one p)
    _ = 1 := one_mul 1

theorem toReal_goodProb (p : I) (D : ℕ) :
    (goodProb p D).toReal = (1 - (1 - (p : ℝ)) ^ (D + 1)) * (1 - p) ^ (2 * D + 3) := by
  unfold goodProb
  have h1 : (toNNReal (σ p) : ℝ≥0∞) ^ (D + 1) ≤ 1 := pow_le_one₀ (zero_le) (r_le_one p)
  rw [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le h1 ENNReal.one_ne_top, ENNReal.toReal_pow,
    ENNReal.toReal_pow, toReal_r, ENNReal.toReal_one]

theorem goodProb_pos (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (D : ℕ) : 0 < goodProb p D := by
  have hr : (goodProb p D).toReal > 0 := by
    rw [toReal_goodProb]
    apply mul_pos
    · have : (1 - (p : ℝ)) ^ (D + 1) < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
      linarith
    · exact pow_pos (by linarith) _
  exact ENNReal.toReal_pos_iff.1 hr |>.1

/-- **Theorem 2, explicit tail bound** (`D` any upper bound on the diameter, `n = |V|`):
`P(no single leader from round k(2D+3) on) ≤ n²·(1 - (1-(1-p)^{D+1})(1-p)^{2D+3})^k`. -/
theorem theorem2_tail (hconn : G.Connected) (hI : GoodInit init) (p : I) {D : ℕ}
    (hD : ∀ a b, G.dist a b ≤ D) (k : ℕ) :
    (coinMeasure p).real {ω | ¬ UniqueFrom G init (k * (2 * D + 3)) ω} ≤
      (Fintype.card V : ℝ) ^ 2 * (1 - (1 - (1 - (p : ℝ)) ^ (D + 1)) * (1 - p) ^ (2 * D + 3)) ^ k := by
  have h := not_uniqueFrom_le hconn hI p hD k
  have hfin : (Fintype.card V : ℝ≥0∞) ^ 2 * (1 - goodProb p D) ^ k ≠ ⊤ := by
    apply ENNReal.mul_ne_top (by simp)
    exact ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  calc _ ≤ ((Fintype.card V : ℝ≥0∞) ^ 2 * (1 - goodProb p D) ^ k).toReal :=
        ENNReal.toReal_mono hfin h
    _ = _ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
          ENNReal.toReal_sub_of_le (goodProb_le_one p D) ENNReal.one_ne_top, toReal_goodProb]
        simp

/-- **Theorem 2 (almost-sure part).** For every `p ∈ (0, 1)` and every connected graph, BFW solves
Eventual Leader Election almost surely: a.s. there are a round `T` and a node `u⋆` such that `u⋆`
is the only leader in every round `t ≥ T`. -/
theorem theorem2_ae (hconn : G.Connected) (hI : GoodInit init) (p : I) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : ∀ᵐ ω ∂(coinMeasure p), ∃ T, UniqueFrom G init T ω := by
  obtain ⟨D, hD⟩ : ∃ D, ∀ a b, G.dist a b ≤ D :=
    ⟨Finset.univ.sup fun x : V × V => G.dist x.1 x.2, fun a b =>
      Finset.le_sup (f := fun x : V × V => G.dist x.1 x.2) (Finset.mem_univ (a, b))⟩
  rw [ae_iff]
  set B := {ω | ¬ ∃ T, UniqueFrom G init T ω}
  have hle : ∀ k : ℕ, coinMeasure p B ≤ (Fintype.card V : ℝ≥0∞) ^ 2 * (1 - goodProb p D) ^ k :=
    fun k => by
      refine (measure_mono ?_).trans (not_uniqueFrom_le hconn hI p hD k)
      intro ω hω h
      exact hω ⟨_, h⟩
  have hlt : 1 - goodProb p D < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (goodProb_pos p hp0 hp1 D).ne'
  have ht : Filter.Tendsto (fun k : ℕ => (Fintype.card V : ℝ≥0∞) ^ 2 * (1 - goodProb p D) ^ k)
      Filter.atTop (nhds 0) := by
    have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt)
      (a := (Fintype.card V : ℝ≥0∞) ^ 2) (Or.inr (by simp))
    simpa using this
  exact le_antisymm (ge_of_tendsto' ht hle) zero_le

/-- The paper's parameter of Theorem 3: `p = 1/(D+1)`. -/
noncomputable def pD (D : ℕ) : I :=
  ⟨1 / (D + 1), by positivity, by rw [div_le_one (by positivity)]; linarith [(D.cast_nonneg : (0:ℝ) ≤ D)]⟩

theorem q_bound {D : ℕ} (hD1 : 1 ≤ D) :
    1 / 128 ≤ (1 - (1 - (pD D : ℝ)) ^ (D + 1)) * (1 - pD D) ^ (2 * D + 3) := by
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  set a : ℝ := 1 - pD D with ha
  have hpD : (pD D : ℝ) = 1 / (D + 1) := rfl
  have ha' : a = D / (D + 1) := by rw [ha, hpD]; field_simp; ring
  have ha0 : 0 ≤ a := by rw [ha']; positivity
  have hahalf : 1 / 2 ≤ a := by rw [ha', le_div_iff₀ (by positivity)]; linarith
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  -- (i) `a^{D+1} ≤ e^{-1} ≤ 1/2`
  have h1 : a ^ (D + 1) ≤ 1 / 2 := by
    have : a ≤ Real.exp (-(1 / (D + 1))) := by
      have := Real.add_one_le_exp (-(1 / ((D : ℝ) + 1))); rw [ha, hpD]; linarith
    calc a ^ (D + 1) ≤ Real.exp (-(1 / (D + 1))) ^ (D + 1) := pow_le_pow_left₀ ha0 this _
      _ = Real.exp (-1) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
      _ ≤ 1 / 2 := by
          rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]; linarith
  -- (ii) `a^D ≥ e^{-1}`, hence `a^{2D+3} ≥ e^{-2}/8 ≥ 1/64`
  have h2 : Real.exp (-1) ≤ a ^ D := by
    have hinv : 1 / a ≤ Real.exp (1 / D) := by
      have := Real.add_one_le_exp (1 / (D : ℝ))
      rw [ha', one_div_div]; rw [show ((D : ℝ) + 1) / D = 1 / D + 1 by field_simp; ring]; exact this
    have hpos : 0 < a := by linarith
    have : (1 / a) ^ D ≤ Real.exp 1 := by
      calc (1 / a) ^ D ≤ Real.exp (1 / D) ^ D := pow_le_pow_left₀ (by positivity) hinv _
        _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; congr 1; field_simp
    rw [one_div_pow, div_le_iff₀ (pow_pos hpos _)] at this
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀' (Real.exp_pos 1)]; linarith
  have h3 : 1 / 64 ≤ a ^ (2 * D + 3) := by
    have hexp2 : Real.exp (-1) * Real.exp (-1) ≥ 1 / 8 := by
      rw [← Real.exp_add, show (-1 : ℝ) + -1 = -2 by norm_num, Real.exp_neg, ge_iff_le,
        le_inv_comm₀ (by norm_num) (Real.exp_pos 2), show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    have : a ^ (2 * D + 3) = a ^ D * a ^ D * a ^ 3 := by ring
    rw [this]
    have hea := Real.exp_pos (-1)
    calc (1 : ℝ) / 64 = 1 / 8 * (1 / 8) := by norm_num
      _ ≤ (Real.exp (-1) * Real.exp (-1)) * (1 / 2) ^ 3 := by
          apply mul_le_mul hexp2 (by norm_num) (by norm_num) (by positivity)
      _ ≤ (a ^ D * a ^ D) * a ^ 3 := by
          apply mul_le_mul (mul_le_mul h2 h2 hea.le (by positivity))
            (pow_le_pow_left₀ (by norm_num) hahalf _) (by positivity) (by positivity)
  have : 1 / 2 ≤ 1 - a ^ (D + 1) := by linarith
  calc (1 : ℝ) / 128 = 1 / 2 * (1 / 64) := by norm_num
    _ ≤ _ := mul_le_mul this h3 (by norm_num) (by linarith)

/-- **Theorem 3.** With `p = 1/(D+1)` (`D ≥ 1` an upper bound on the diameter),
`P(no single leader from round k(2D+3) on) ≤ n²·(127/128)^k`. -/
theorem theorem3 (hconn : G.Connected) (hI : GoodInit init) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : ∀ a b, G.dist a b ≤ D) (k : ℕ) :
    (coinMeasure (pD D)).real {ω | ¬ UniqueFrom G init (k * (2 * D + 3)) ω} ≤
      (Fintype.card V : ℝ) ^ 2 * (127 / 128) ^ k := by
  refine (theorem2_tail hconn hI (pD D) hD k).trans ?_
  have hq := q_bound hD1
  have hq1 : (1 - (1 - (pD D : ℝ)) ^ (D + 1)) * (1 - pD D) ^ (2 * D + 3) ≤ 1 := by
    have := toReal_goodProb (pD D) D
    rw [← this]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using goodProb_le_one _ _)
  gcongr
  linarith

/-- **Theorem 3 (w.h.p. form).** With `p = 1/(D+1)`, with probability at least `1 - 1/n²` a single
leader is elected by round `(2D+3)·⌈512 ln n⌉`, i.e. within `O(D log n)` rounds. -/
theorem theorem3_whp (hconn : G.Connected) (hI : GoodInit init) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : ∀ a b, G.dist a b ≤ D) :
    (coinMeasure (pD D)).real
        {ω | ¬ UniqueFrom G init (⌈512 * Real.log (Fintype.card V)⌉₊ * (2 * D + 3)) ω} ≤
      1 / (Fintype.card V : ℝ) ^ 2 := by
  set n : ℝ := (Fintype.card V : ℝ)
  have hn : 1 ≤ n := by
    obtain ⟨v, -⟩ := hI.leader
    have := Fintype.card_pos_iff.2 ⟨v⟩
    simp only [n]; exact_mod_cast this
  set k := ⌈512 * Real.log n⌉₊
  refine (theorem3 hconn hI hD1 hD k).trans ?_
  have hk : 512 * Real.log n ≤ k := Nat.le_ceil _
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn
  -- `(127/128)^k ≤ exp(-k/128) ≤ exp(-4 log n) = n^{-4}`
  have h1 : (127 / 128 : ℝ) ^ k ≤ Real.exp (-(k / 128)) := by
    have : (127 / 128 : ℝ) ≤ Real.exp (-(1 / 128)) := by
      have := Real.add_one_le_exp (-(1 / 128 : ℝ)); linarith
    calc (127 / 128 : ℝ) ^ k ≤ Real.exp (-(1 / 128)) ^ k := pow_le_pow_left₀ (by norm_num) this _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h2 : Real.exp (-(k / 128)) ≤ Real.exp (-(4 * Real.log n)) := by
    apply Real.exp_le_exp.2; linarith
  have h3 : Real.exp (-(4 * Real.log n)) = 1 / n ^ 4 := by
    rw [Real.exp_neg, show (4 : ℝ) * Real.log n = (4 : ℕ) * Real.log n by norm_num,
      Real.exp_nat_mul, Real.exp_log (by linarith), one_div]
  have hn2 : 0 < n ^ 2 := by positivity
  calc n ^ 2 * (127 / 128) ^ k ≤ n ^ 2 * (1 / n ^ 4) := by
        gcongr; exact h1.trans (h2.trans h3.le)
    _ = 1 / n ^ 2 := by field_simp

end MinimalistLE
