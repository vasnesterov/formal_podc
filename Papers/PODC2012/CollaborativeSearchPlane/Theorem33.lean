import Papers.PODC2012.CollaborativeSearchPlane.Geometry
import Papers.PODC2012.CollaborativeSearchPlane.Summation

/-!
# Theorem 3.3: a uniform `O(log^{1+ε} k)`-competitive algorithm

Algorithm `A_uniform` (Algorithm 1): for big stage `ℓ = 0, 1, …`, stage `i = 0, …, ℓ`, phase
`j = 0, …, i`: go to a uniform node of `B(D_{i,j})`, `D_{i,j} = √(2^(i+j)/j^(1+ε))`, spiral for
`t_{i,j} = 2^(i+2)/j^(1+ε)` steps, return. For `j = 0` the paper's formulas divide by
`0^(1+ε) = 0`; we use `(j+1)^(1+ε)` instead of `j^(1+ε)` (and round down to integers).

`theorem_3_3`: for every `ε > 0` there is `C` with
`T(D, k) ≤ C · (1 + log₂ k)^(1+ε) · (D + D²/k)` for all `k ≥ 1` and `D ≥ 1` — the algorithm is
`O(log^{1+ε} k)`-competitive (the `1 +` only matters for `k = 1`, where `log^{1+ε} k = 0`).

The proof follows the paper: big stage `ℓ` lasts `O(2^ℓ)` (`uBlockDur_le`); with
`j* = ⌊log₂ min(k, D)⌋` and `s` such that `2^s ≈ D² (j*+1)^(1+ε) / 2^(j*)`, every phase `(i, j*)`
with `i ≥ s` is found by one of the `k ≥ 2^(j*)` agents with probability bounded away from `0`
(`u_succ_ge`), and big stage `s + m` contains `m + 1` such phases. (The paper first reduces
`k > D` to `D` agents; choosing `j*` from `min(k, D)` does the same.)
-/

namespace Podc.CollaborativeSearchPlane

open MeasureTheory Finset
open scoped ENNReal

/-- The phases of big stage `ℓ`: pairs `(i, j)` with `j ≤ i ≤ ℓ` (phase `j` of stage `i`). -/
abbrev BigP (ℓ : ℕ) : Type := {x : Fin (ℓ + 1) × Fin (ℓ + 1) // x.2 ≤ x.1}

/-- `2^(i+j) / (j+1)^(1+ε)`, the square of the sampling radius `D_{i,j}`. -/
noncomputable def uX (ε : ℝ) (i j : ℕ) : ℝ := (2 : ℝ) ^ (i + j) / ((j : ℝ) + 1) ^ (1 + ε)

/-- Sampling radius `⌊D_{i,j}⌋` of phase `(i, j)`. -/
noncomputable def uRad (ε : ℝ) (x : Σ ℓ, BigP ℓ) : ℕ :=
  ⌊Real.sqrt (uX ε x.2.1.1 x.2.1.2)⌋₊

/-- Spiral length `⌊2^(i+2) / (j+1)^(1+ε)⌋` of phase `(i, j)`. -/
noncomputable def uSpiral (ε : ℝ) (x : Σ ℓ, BigP ℓ) : ℕ :=
  ⌊(2 : ℝ) ^ ((x.2.1.1 : ℕ) + 2) / (((x.2.1.2 : ℕ) : ℝ) + 1) ^ (1 + ε)⌋₊

/-- Expected running time of `k` agents running `A_uniform` (parameter `ε`, spiral constant
`σ`): the parameters do not depend on `k`. -/
noncomputable def uniformTime (σ : ℕ) (ε : ℝ) (k : ℕ) (τ : Node) : ℝ≥0∞ :=
  phasedTime (P := BigP) (k := k) σ (uRad ε) (fun i => uSpiral ε i.2) τ

/-- `ζ(1+ε) = ∑_j 1/(j+1)^(1+ε)`. -/
noncomputable def zeta1 (ε : ℝ) : ℝ := ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ (1 + ε)

theorem summable_zeta1 {ε : ℝ} (hε : 0 < ε) :
    Summable fun j : ℕ => 1 / ((j : ℝ) + 1) ^ (1 + ε) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_rpow.2 (by linarith : 1 < 1 + ε))
  simpa using h

theorem sum_zeta1_le {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ∑ j ∈ range n, 1 / ((j : ℝ) + 1) ^ (1 + ε) ≤ zeta1 ε :=
  (summable_zeta1 hε).sum_le_tsum _ fun j _ => by positivity

theorem zeta1_nonneg (ε : ℝ) : 0 ≤ zeta1 ε := tsum_nonneg fun j => by positivity

/-- `∑_{j ≤ i} √(2^(i+j)) ≤ 4 · 2^i`. -/
theorem sum_sqrt_le (i : ℕ) :
    ∑ j ∈ range (i + 1), Real.sqrt ((2 : ℝ) ^ (i + j)) ≤ 4 * 2 ^ i := by
  set x := Real.sqrt 2
  have hx2 : x ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg 2
  have hx43 : 4 / 3 ≤ x := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have e : ∀ n : ℕ, Real.sqrt ((2 : ℝ) ^ n) = x ^ n := by
    intro n
    rw [show (2 : ℝ) ^ n = (x ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, hx2]]
    exact Real.sqrt_sq (by positivity)
  simp_rw [e, pow_add, ← Finset.mul_sum]
  have hg := geom_sum_mul x (i + 1)
  have hsum0 : 0 ≤ ∑ j ∈ range (i + 1), x ^ j := by positivity
  have h1 : (∑ j ∈ range (i + 1), x ^ j) * (x - 1) ≤ x ^ (i + 1) := by linarith
  have hxi : (x ^ i) ^ 2 = 2 ^ i := by rw [← pow_mul, mul_comm, pow_mul, hx2]
  have hxi0 : 0 ≤ x ^ i := by positivity
  -- `x^i * ∑ ≤ x^i * x^(i+1) / (x - 1) = 2^i * x/(x-1) ≤ 4 * 2^i`
  have h2 : (∑ j ∈ range (i + 1), x ^ j) * (x - 1) ≤ x ^ i * x := by rw [← pow_succ]; exact h1
  have h3 : x ^ i * (∑ j ∈ range (i + 1), x ^ j) * (x - 1) ≤ 2 ^ i * x := by
    rw [← hxi]; nlinarith
  have h4 : 2 ^ i * x ≤ 4 * 2 ^ i * (x - 1) := by
    have : (0 : ℝ) < 2 ^ i := by positivity
    nlinarith
  have hx1 : 0 < x - 1 := by linarith
  have := le_trans h3 h4
  exact le_of_mul_le_mul_right this hx1

theorem sum_bigP (ℓ : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ p : BigP ℓ, F p.1.1 p.1.2 = ∑ i ∈ range (ℓ + 1), ∑ j ∈ range (i + 1), F i j := by
  rw [← Finset.sum_subtype ((univ : Finset (Fin (ℓ + 1) × Fin (ℓ + 1))).filter
      fun x => x.2 ≤ x.1) (by simp) (fun x => F x.1 x.2), Finset.sum_filter,
    Fintype.sum_prod_type]
  simp only [Fin.le_def]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin (ℓ + 1),
      if j.val ≤ i then F i j else 0) (ℓ + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Fin.sum_univ_eq_sum_range (fun j => if j ≤ i then F i j else 0) (ℓ + 1),
    ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  have := Finset.mem_range.1 hi
  omega

/-- Big stage `ℓ` lasts at most `16 (1 + ζ(1+ε)) 2^ℓ`. -/
theorem uBlockDur_le {ε : ℝ} (hε : 0 < ε) {k : ℕ} (ℓ : ℕ) :
    (blockDur (P := BigP) (k := k) (uRad ε) (fun i => uSpiral ε i.2) ℓ : ℝ)
      ≤ 16 * (1 + zeta1 ε) * 2 ^ ℓ := by
  have hle : blockDur (P := BigP) (k := k) (uRad ε) (fun i => uSpiral ε i.2) ℓ
      ≤ ∑ p : BigP ℓ, phaseDur (uRad ε ⟨ℓ, p⟩) (uSpiral ε ⟨ℓ, p⟩) :=
    Finset.sum_le_sum fun p _ => Finset.sup_le fun _ _ => le_rfl
  have hphase : ∀ p : BigP ℓ, (phaseDur (uRad ε ⟨ℓ, p⟩) (uSpiral ε ⟨ℓ, p⟩) : ℝ)
      ≤ 2 * Real.sqrt ((2 : ℝ) ^ ((p.1.1 : ℕ) + (p.1.2 : ℕ)))
        + 8 * 2 ^ (p.1.1 : ℕ) * (1 / (((p.1.2 : ℕ) : ℝ) + 1) ^ (1 + ε)) := by
    intro p
    have hden : (1 : ℝ) ≤ (((p.1.2 : ℕ) : ℝ) + 1) ^ (1 + ε) :=
      Real.one_le_rpow (by linarith [(Nat.cast_nonneg (p.1.2 : ℕ) : (0 : ℝ) ≤ _)]) (by linarith)
    have hR : (uRad ε ⟨ℓ, p⟩ : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ ((p.1.1 : ℕ) + (p.1.2 : ℕ))) := by
      unfold uRad uX
      refine (Nat.floor_le (Real.sqrt_nonneg _)).trans (Real.sqrt_le_sqrt ?_)
      exact div_le_self (by positivity) hden
    have ht : (uSpiral ε ⟨ℓ, p⟩ : ℝ)
        ≤ 4 * 2 ^ (p.1.1 : ℕ) * (1 / (((p.1.2 : ℕ) : ℝ) + 1) ^ (1 + ε)) := by
      unfold uSpiral
      refine (Nat.floor_le (by positivity)).trans (le_of_eq ?_)
      rw [pow_add]; ring
    unfold phaseDur
    push_cast
    linarith
  calc (blockDur (P := BigP) (k := k) (uRad ε) (fun i => uSpiral ε i.2) ℓ : ℝ)
      ≤ ∑ p : BigP ℓ, (phaseDur (uRad ε ⟨ℓ, p⟩) (uSpiral ε ⟨ℓ, p⟩) : ℝ) := by exact_mod_cast hle
    _ ≤ ∑ p : BigP ℓ, (2 * Real.sqrt ((2 : ℝ) ^ ((p.1.1 : ℕ) + (p.1.2 : ℕ)))
          + 8 * 2 ^ (p.1.1 : ℕ) * (1 / (((p.1.2 : ℕ) : ℝ) + 1) ^ (1 + ε))) :=
        Finset.sum_le_sum fun p _ => hphase p
    _ = ∑ i ∈ range (ℓ + 1), ∑ j ∈ range (i + 1), (2 * Real.sqrt ((2 : ℝ) ^ (i + j))
          + 8 * 2 ^ i * (1 / ((j : ℝ) + 1) ^ (1 + ε))) :=
        sum_bigP ℓ fun i j => 2 * Real.sqrt ((2 : ℝ) ^ (i + j))
          + 8 * 2 ^ i * (1 / ((j : ℝ) + 1) ^ (1 + ε))
    _ ≤ ∑ i ∈ range (ℓ + 1), 8 * (1 + zeta1 ε) * 2 ^ i := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have h1 := sum_sqrt_le i
        have h2 := sum_zeta1_le hε (i + 1)
        have : (0 : ℝ) < 2 ^ i := by positivity
        nlinarith
    _ ≤ 16 * (1 + zeta1 ε) * 2 ^ ℓ := by
        rw [← Finset.mul_sum]
        have hg := geom_sum_mul (2 : ℝ) (ℓ + 1)
        norm_num at hg
        rw [pow_succ] at hg
        have := zeta1_nonneg ε
        have : ∑ i ∈ range (ℓ + 1), (2 : ℝ) ^ i ≤ 2 * 2 ^ ℓ := by linarith
        nlinarith

/-- A good phase: phase `(i, j)` with `D² ≤ 2^(i+j)/(j+1)^(1+ε)` (the treasure lies in the
sampling ball) succeeds for each agent with probability `≥ 1/(18(σ+1) 2^j)`. -/
theorem u_succ_ge {ε : ℝ} {σ : ℕ} (hσ : 1 ≤ σ) {τ : Node} (hτ : 1 ≤ dist τ)
    (x : Σ ℓ, BigP ℓ) (hX : (dist τ : ℝ) ^ 2 ≤ uX ε x.2.1.1 x.2.1.2) :
    ENNReal.ofReal (1 / (18 * (σ + 1) * 2 ^ (x.2.1.2 : ℕ))) ≤
      uniformBall (uRad ε x) (spiralSucc σ τ (uSpiral ε x)) := by
  set i : ℕ := x.2.1.1.val
  set j : ℕ := x.2.1.2.val
  set d : ℝ := ((j : ℝ) + 1) ^ (1 + ε)
  have hd : 0 < d := by positivity
  set X := uX ε i j
  have hX0 : 0 ≤ X := by simp only [X, uX]; positivity
  have hτR : dist τ ≤ uRad ε x := by
    unfold uRad
    apply Nat.le_floor
    exact Real.le_sqrt_of_sq_le hX
  have hRX : ((uRad ε x : ℕ) : ℝ) ^ 2 ≤ X := by
    unfold uRad
    calc ((⌊Real.sqrt X⌋₊ : ℕ) : ℝ) ^ 2 ≤ (Real.sqrt X) ^ 2 := by
          gcongr; exact Nat.floor_le (Real.sqrt_nonneg _)
      _ = X := Real.sq_sqrt hX0
  have hY : (2 : ℝ) ^ (i + 2) / d < uSpiral ε x + 1 := Nat.lt_floor_add_one _
  refine le_trans ?_ (uniformBall_succ_ge' hσ (hτ.trans hτR) hRX hY hτR)
  apply ENNReal.ofReal_le_ofReal
  have e : (2 : ℝ) ^ (i + 2) / d / (72 * σ * X) = 1 / (18 * σ * 2 ^ j) := by
    simp only [X, uX]
    rw [pow_add, pow_add]
    field_simp
    ring
  rw [e]
  have hσ' : (1 : ℝ) ≤ σ := by exact_mod_cast hσ
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  refine le_min ?_ ?_
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · apply one_div_le_one_div_of_le (by positivity); nlinarith

theorem two_pow_clog_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ Nat.clog 2 n ≤ 2 * n := by
  rcases Nat.lt_or_ge 1 n with h | h
  · have h1 : 2 ^ (Nat.clog 2 n).pred < n := Nat.pow_pred_clog_lt_self (by norm_num) h
    have hs1 : 1 ≤ Nat.clog 2 n := Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) h)
    have : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
      rw [← pow_succ']; congr 1; exact (Nat.succ_pred_eq_of_pos hs1).symm
    omega
  · have : n = 1 := le_antisymm h hn
    subst this; simp

/-- **Theorem 3.3** of [Feinerman–Korman–Lotker–Sereni]: for every `ε > 0` the uniform algorithm
`A_uniform` is `O(log^{1+ε} k)`-competitive: `T(D, k) ≤ C (1 + log₂ k)^(1+ε) (D + D²/k)`. -/
theorem theorem_3_3 {ε : ℝ} (hε : 0 < ε) {σ : ℕ} (hσ : 1 ≤ σ) : ∃ C : ℝ, 0 < C ∧
    ∀ {k : ℕ}, 1 ≤ k → ∀ τ : Node, 1 ≤ dist τ → uniformTime σ ε k τ ≤
      ENNReal.ofReal (C * (1 + Real.logb 2 k) ^ (1 + ε) * (dist τ + (dist τ : ℝ) ^ 2 / k)) := by
  set β : ℝ := 1 / (18 * (σ + 1))
  have hβ : 0 < β := by positivity
  set A : ℝ := 16 * (1 + zeta1 ε)
  have hA : 0 < A := by have := zeta1_nonneg ε; positivity
  refine ⟨9 * A * (1 + gaussConst β), by have := gaussConst_nonneg β; positivity, ?_⟩
  intro k hk τ hτ
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set D := dist τ
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast hτ
  set m := min k D
  have hm1 : 1 ≤ m := le_min hk hτ
  set js := Nat.log 2 m
  have h2js : 2 ^ js ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hm2 : m < 2 ^ (js + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hjsk : 2 ^ js ≤ k := h2js.trans (min_le_left _ _)
  set dj : ℝ := ((js : ℝ) + 1) ^ (1 + ε)
  have hdj : 1 ≤ dj := Real.one_le_rpow (by linarith [(Nat.cast_nonneg js : (0 : ℝ) ≤ js)])
    (by linarith)
  set W : ℝ := (D : ℝ) ^ 2 * dj / 2 ^ js
  have hW1 : 1 ≤ W := by
    have h1 : ((2 : ℝ) ^ js) ≤ D := by
      have := h2js.trans (min_le_right k D); exact_mod_cast this
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  set s := max js (Nat.clog 2 ⌈W⌉₊)
  have hgood : ∀ i, s ≤ i → (D : ℝ) ^ 2 ≤ uX ε i js := by
    intro i hi
    have h1 : ⌈W⌉₊ ≤ 2 ^ i :=
      (Nat.le_pow_clog (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num)
        (le_trans (le_max_right _ _) hi))
    have h2 : W ≤ 2 ^ i := (Nat.le_ceil W).trans (by exact_mod_cast h1)
    unfold uX
    rw [le_div_iff₀ (by positivity), pow_add]
    simp only [W] at h2
    rw [div_le_iff₀ (by positivity)] at h2
    exact h2
  rw [uniformTime, phasedTime_eq]
  refine (tsum_le_of_gauss hβ A 0 hA.le le_rfl s _ ?_).trans ?_
  · intro b
    rw [ENNReal.ofReal_mul (by positivity)]
    gcongr
    · rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (by simpa using uBlockDur_le hε (k := k) b)
    · refine prod_le_gauss s _ (blockFail_le_one _ _ _ _) ?_ b
      intro b hb
      set q : ℝ := 1 / (18 * (σ + 1) * 2 ^ js)
      have hq0 : 0 ≤ q := by positivity
      refine (blockFail_le_exp σ (uRad ε) (fun i => uSpiral ε i.2) τ b
        ((univ : Finset (BigP b)).filter fun p => p.1.2.val = js ∧ s ≤ p.1.1.val) q hq0
        ?_ ?_).trans ?_
      · rw [div_le_one (by positivity)]
        have : (1 : ℝ) ≤ 2 ^ js := one_le_pow₀ (by norm_num)
        have : (0 : ℝ) ≤ σ := by positivity
        nlinarith
      · intro p hp a
        rw [Finset.mem_filter] at hp
        have := u_succ_ge (ε := ε) hσ hτ ⟨b, p⟩ (by
          simp only [hp.2.1]; exact hgood _ hp.2.2)
        simp only [hp.2.1] at this
        exact this
      · apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        -- `q k ≥ β` and `|G| ≥ b - s + 1`
        have hqk : β ≤ q * k := by
          simp only [q, β]
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
          have : ((2 : ℝ) ^ js) ≤ k := by exact_mod_cast hjsk
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
          nlinarith
        have hcard : b + 1 - s ≤ ((univ : Finset (BigP b)).filter
            fun p => p.1.2.val = js ∧ s ≤ p.1.1.val).card := by
          have hjs : js ≤ s := le_max_left _ _
          have := Finset.card_le_card_of_injOn (s := range (b + 1 - s))
            (t := (univ : Finset (BigP b)).filter fun p => p.1.2.val = js ∧ s ≤ p.1.1.val)
            (fun n => (⟨(⟨min (s + n) b, by omega⟩, ⟨min js b, by omega⟩), by
              rw [Fin.mk_le_mk]; omega⟩ : BigP b)) ?_ ?_
          · simpa using this
          · intro n hn
            have := mem_range.1 hn
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
            omega
          · intro n hn n' hn' h
            have h1 := mem_range.1 hn
            have h2 := mem_range.1 hn'
            have := congrArg (fun p : BigP b => p.1.1.val) h
            simp only at this
            omega
        have hc' : (((b - s : ℕ) : ℝ) + 1) ≤ (((univ : Finset (BigP b)).filter
            fun p => p.1.2.val = js ∧ s ≤ p.1.1.val).card : ℝ) := by
          have : b - s + 1 = b + 1 - s := by omega
          exact_mod_cast this ▸ hcard
        have h0 : (0 : ℝ) ≤ ((b - s : ℕ) : ℝ) + 1 := by positivity
        nlinarith
  · apply ENNReal.ofReal_le_ofReal
    have hG := gaussConst_nonneg β
    set L : ℝ := (1 + Real.logb 2 k) ^ (1 + ε)
    have hlog0 : 0 ≤ Real.logb 2 k := Real.logb_nonneg (by norm_num) (by exact_mod_cast hk)
    have hL1 : 1 ≤ L := Real.one_le_rpow (by linarith) (by linarith)
    have hdjL : dj ≤ L := by
      apply Real.rpow_le_rpow (by positivity) _ (by linarith)
      have h1 : (js : ℝ) ≤ Real.logb 2 m := by
        have := Real.natLog_le_logb m 2; push_cast at this; exact this
      have h2 : Real.logb 2 (m : ℝ) ≤ Real.logb 2 k :=
        Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hm1)
          (by exact_mod_cast min_le_left k D)
      linarith
    -- `2^s ≤ 9 L (D + D²/k)`
    have hm' : (m : ℝ) < 2 * 2 ^ js := by
      have : (m : ℝ) < (2 : ℝ) ^ (js + 1) := by exact_mod_cast hm2
      rw [pow_succ] at this; linarith
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hDm : (D : ℝ) ^ 2 / m ≤ D + D ^ 2 / k := by
      rcases le_total k D with h | h
      · have : m = k := min_eq_left h
        rw [this]; linarith
      · have : m = D := min_eq_right h
        have e : (D : ℝ) ^ 2 / D = D := by field_simp
        rw [this, e]
        have : (0 : ℝ) ≤ D ^ 2 / k := by positivity
        linarith
    have hWle : W ≤ 2 * L * (D + D ^ 2 / k) := by
      simp only [W]
      have h1 : (D : ℝ) ^ 2 * dj / 2 ^ js ≤ (D : ℝ) ^ 2 * L / (m / 2) := by
        apply div_le_div₀ (by positivity) (by gcongr) (by positivity) (by linarith)
      have h2 : (D : ℝ) ^ 2 * L / (m / 2) = 2 * L * ((D : ℝ) ^ 2 / m) := by
        field_simp
      have : 2 * L * ((D : ℝ) ^ 2 / m) ≤ 2 * L * (D + D ^ 2 / k) := by gcongr
      linarith
    have hs : (2 : ℝ) ^ s ≤ 9 * L * (D + D ^ 2 / k) := by
      have h1 : 2 ^ s ≤ 2 ^ js + 2 ^ Nat.clog 2 ⌈W⌉₊ := by
        rcases le_total js (Nat.clog 2 ⌈W⌉₊) with h | h
        · have e : s = Nat.clog 2 ⌈W⌉₊ := max_eq_right h
          rw [e]; exact Nat.le_add_left _ _
        · have e : s = js := max_eq_left h
          rw [e]; exact Nat.le_add_right _ _
      have h2 : 2 ^ Nat.clog 2 ⌈W⌉₊ ≤ 2 * ⌈W⌉₊ :=
        two_pow_clog_le (Nat.succ_le_of_lt (Nat.ceil_pos.2 (by linarith)))
      have h3 : (⌈W⌉₊ : ℝ) ≤ 2 * W := by
        have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ W); linarith
      have h4 : ((2 ^ js : ℕ) : ℝ) ≤ D := by
        have := h2js.trans (min_le_right k D); exact_mod_cast this
      have h1' : ((2 ^ s : ℕ) : ℝ) ≤ ((2 ^ js : ℕ) : ℝ) + 2 * (⌈W⌉₊ : ℝ) := by
        have := h1.trans (Nat.add_le_add_left h2 _)
        exact_mod_cast this
      push_cast at h1' h4
      have hpos : (0 : ℝ) ≤ D ^ 2 / k := by positivity
      nlinarith
    have hpos : 0 ≤ 1 + gaussConst β := by linarith
    calc (A * 2 ^ s + 0 * 4 ^ s) * (1 + gaussConst β)
        = A * (1 + gaussConst β) * 2 ^ s := by ring
      _ ≤ A * (1 + gaussConst β) * (9 * L * (D + D ^ 2 / k)) := by gcongr
      _ = _ := by ring

end Podc.CollaborativeSearchPlane
