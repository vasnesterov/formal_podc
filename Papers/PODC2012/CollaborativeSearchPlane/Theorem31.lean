import Papers.PODC2012.CollaborativeSearchPlane.Geometry
import Papers.PODC2012.CollaborativeSearchPlane.Summation

/-!
# Theorem 3.1 and Corollary 3.2: `O(D + D²/k)` with (approximate) knowledge of `k`

Algorithm `A_k` (Appendix A): in stage `j = 0, 1, 2, …` the agent performs the phases
`i = 0, …, j`; phase `i` picks a uniform node of `B(2ⁱ)`, spirals for `⌊4^(i+1)/k⌋` steps and
returns. (The paper indexes stages and phases from `1` and takes the spiral length `2^(2i+2)/k`;
lengths must be integers, so we round down.)

* `akTime_le` — if agent `a` runs `A_{κ a}` with `k/λ ≤ κ a ≤ k`, the expected running time is
  at most `C_σ (D + λ D²/k)`;
* `theorem_3_1` — `κ a = k`: `T = O(D + D²/k)`;
* `corollary_3_2` — a `ρ`-approximation `k/ρ ≤ k_a ≤ kρ` and `κ a = k_a/ρ`: `O(1)`-competitive.

The analysis follows the paper: with `s = ⌈log₂ D⌉`, every phase `i ≥ s` succeeds with
probability `≥ β/k` for each agent (`ak_succ_ge`, `β = 1/(18(σ+1))`), stage `s + m` contains
`m + 1` such phases, and stage `j` lasts `O(2ʲ + 4ʲ/k)`.
-/

namespace Podc.CollaborativeSearchPlane

open MeasureTheory Finset
open scoped ENNReal

/-- The phases `i = 0, …, j` of stage `j` of Algorithm `A_k`. -/
abbrev StageP (j : ℕ) : Type := Fin (j + 1)

/-- Phase `i` samples in `B(2ⁱ)`. -/
def akRad (x : Σ j, StageP j) : ℕ := 2 ^ (x.2 : ℕ)

/-- Agent `a`, running `A_{κ a}`, spirals for `⌊4^(i+1)/κ a⌋` steps in phase `i`. -/
noncomputable def akSpiral {k : ℕ} (κ : Fin k → ℝ) (i : Fin k × Σ j, StageP j) : ℕ :=
  ⌊(4 : ℝ) ^ ((i.2.2 : ℕ) + 1) / κ i.1⌋₊

/-- Expected running time of `k` agents, agent `a` running `A_{κ a}` (spiral constant `σ`). -/
noncomputable def akTime (σ : ℕ) {k : ℕ} (κ : Fin k → ℝ) (τ : Node) : ℝ≥0∞ :=
  phasedTime (P := StageP) σ akRad (akSpiral κ) τ

theorem akBlockDur_le {k : ℕ} (hk : 1 ≤ k) {lam : ℝ} (hlam : 1 ≤ lam) {κ : Fin k → ℝ}
    (hκ : ∀ a, (k : ℝ) / lam ≤ κ a) (j : ℕ) :
    (blockDur (P := StageP) akRad (akSpiral κ) j : ℝ) ≤ 4 * 2 ^ j + 11 * lam / k * 4 ^ j := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hphase : ∀ p : StageP j, (((univ : Finset (Fin k)).sup fun a =>
      phaseDur (akRad ⟨j, p⟩) (akSpiral κ (a, ⟨j, p⟩)) : ℕ) : ℝ)
        ≤ 2 * 2 ^ (p : ℕ) + 8 * lam / k * 4 ^ (p : ℕ) := by
    intro p
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin k)) ⟨⟨0, hk⟩, mem_univ _⟩
      fun a => phaseDur (akRad ⟨j, p⟩) (akSpiral κ (a, ⟨j, p⟩))
    rw [ha]
    have hκa : 0 < κ a := lt_of_lt_of_le (by positivity) (hκ a)
    have h1 : ((akSpiral κ (a, ⟨j, p⟩) : ℕ) : ℝ) ≤ 4 ^ ((p : ℕ) + 1) * lam / k := by
      unfold akSpiral
      refine (Nat.floor_le (by positivity)).trans ?_
      rw [div_le_iff₀ hκa, mul_div_assoc]
      calc (4 : ℝ) ^ ((p : ℕ) + 1) = 4 ^ ((p : ℕ) + 1) * (lam / k * (k / lam)) := by
            field_simp
        _ ≤ 4 ^ ((p : ℕ) + 1) * (lam / k * κ a) := by gcongr; exact hκ a
        _ = _ := by ring
    unfold phaseDur akRad
    push_cast
    rw [pow_succ] at h1
    have e1 : (4 : ℝ) ^ (p : ℕ) * 4 * lam / k = 4 * (lam / k * 4 ^ (p : ℕ)) := by ring
    have e2 : 8 * lam / k * (4 : ℝ) ^ (p : ℕ) = 8 * (lam / k * 4 ^ (p : ℕ)) := by ring
    rw [e1] at h1
    rw [e2]
    linarith
  unfold blockDur
  push_cast
  refine (Finset.sum_le_sum fun p _ => hphase p).trans ?_
  rw [Fin.sum_univ_eq_sum_range (fun p => 2 * (2 : ℝ) ^ p + 8 * lam / k * 4 ^ p) (j + 1),
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h2 := geom_sum_mul (2 : ℝ) (j + 1)
  have h4 := geom_sum_mul (4 : ℝ) (j + 1)
  norm_num at h2 h4
  have hl : 0 ≤ 8 * lam / k := by positivity
  rw [pow_succ] at h2 h4
  have : ∑ i ∈ range (j + 1), (4 : ℝ) ^ i ≤ 4 * 4 ^ j / 3 := by linarith
  have : 8 * lam / k * ∑ i ∈ range (j + 1), (4 : ℝ) ^ i ≤ 8 * lam / k * (4 * 4 ^ j / 3) := by
    gcongr
  have e : 8 * lam / k * (4 * 4 ^ j / 3) = 32 / 3 * (lam / k) * 4 ^ j := by ring
  have e2 : 11 * lam / k * 4 ^ j = 11 * (lam / k) * 4 ^ j := by ring
  have : 0 ≤ lam / k * 4 ^ j := by positivity
  nlinarith

/-- Every phase `i ≥ s` (`2^s ≥ d(s, τ)`) of `A_{κ a}`, `κ a ≤ k`, succeeds with probability
`≥ 1/(18(σ+1)k)`. -/
theorem ak_succ_ge {σ : ℕ} (hσ : 1 ≤ σ) {k : ℕ} (hk : 1 ≤ k) {κ : Fin k → ℝ} (a : Fin k)
    (hκ0 : 0 < κ a) (hκk : κ a ≤ k) {τ : Node} {s : ℕ} (hs : dist τ ≤ 2 ^ s)
    (x : Σ j, StageP j) (hx : s ≤ (x.2 : ℕ)) :
    ENNReal.ofReal (1 / (18 * (σ + 1) * k)) ≤
      uniformBall (akRad x) (spiralSucc σ τ (akSpiral κ (a, x))) := by
  obtain ⟨j, p⟩ := x
  simp only at hx
  set R := 2 ^ (p : ℕ) with hR
  set t0 := ⌊(4 : ℝ) ^ ((p : ℕ) + 1) / k⌋₊
  set n := t0 / σ
  set r := min (Nat.sqrt n) R
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hτR : dist τ ≤ R := hs.trans (Nat.pow_le_pow_right (by norm_num) hx)
  have hrR : r ≤ R := min_le_right _ _
  have ht0 : t0 ≤ akSpiral κ (a, ⟨j, p⟩) := by
    unfold akSpiral
    apply Nat.floor_le_floor
    exact div_le_div_of_nonneg_left (by positivity) hκ0 hκk
  have hrt : σ * r ^ 2 ≤ akSpiral κ (a, ⟨j, p⟩) := by
    have h1 : r ^ 2 ≤ n := (Nat.pow_le_pow_left (min_le_left _ _) 2).trans (Nat.sqrt_le' n)
    calc σ * r ^ 2 ≤ σ * n := Nat.mul_le_mul_left σ h1
      _ ≤ t0 := Nat.mul_div_le t0 σ
      _ ≤ _ := ht0
  refine le_trans ?_ (uniformBall_succ_ge hrR hrt hτR)
  apply ENNReal.ofReal_le_ofReal
  set X := (r / 2 + 1) * (r / 2 + 2)
  have hX : (r + 1) ^ 2 ≤ 4 * X := by
    have h1 : r + 1 ≤ 2 * (r / 2 + 1) := by omega
    have h2 : r + 1 ≤ 2 * (r / 2 + 2) := by omega
    calc (r + 1) ^ 2 = (r + 1) * (r + 1) := by ring
      _ ≤ (2 * (r / 2 + 1)) * (2 * (r / 2 + 2)) := Nat.mul_le_mul h1 h2
      _ = 4 * X := by ring
  have hR1 : 1 ≤ R := Nat.one_le_two_pow
  have hRsq : (R : ℝ) ^ 2 = 4 ^ (p : ℕ) := by
    rw [hR]; push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hσ' : (1 : ℝ) ≤ σ := by exact_mod_cast hσ
  have hX' : ((r : ℝ) + 1) ^ 2 ≤ 4 * X := by exact_mod_cast hX
  have hden : (0 : ℝ) < 2 * (2 * R + 1) ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) hden, one_mul]
  rcases le_total (Nat.sqrt n) R with hsq | hsq
  · -- `r = √n`: the spiral covers a ball of radius `≈ 2^(i+1)/√(σk)`
    have hr : r = Nat.sqrt n := min_eq_left hsq
    have h1 : n + 1 ≤ (r + 1) ^ 2 := by rw [hr]; exact Nat.lt_succ_sqrt' n
    have h2 : t0 < σ * (n + 1) := Nat.lt_mul_div_succ t0 (by omega)
    have h3 : (4 : ℝ) ^ ((p : ℕ) + 1) / k < t0 + 1 := Nat.lt_floor_add_one _
    have h1' : ((n : ℝ) + 1) ≤ ((r : ℝ) + 1) ^ 2 := by exact_mod_cast h1
    have h2' : (t0 : ℝ) + 1 ≤ σ * ((n : ℝ) + 1) := by exact_mod_cast h2
    have h4 : (4 : ℝ) * 4 ^ (p : ℕ) < k * (σ * (4 * X)) := by
      rw [div_lt_iff₀ hk', pow_succ] at h3
      have : (t0 + 1 : ℝ) * k ≤ σ * (4 * X) * k := by
        gcongr
        calc (t0 : ℝ) + 1 ≤ σ * ((n : ℝ) + 1) := h2'
          _ ≤ σ * (((r : ℝ) + 1) ^ 2) := by gcongr
          _ ≤ σ * (4 * X) := by gcongr
      nlinarith
    have h5 : (2 * (R : ℝ) + 1) ^ 2 ≤ 9 * 4 ^ (p : ℕ) := by
      have : (1 : ℝ) ≤ R := by exact_mod_cast hR1
      nlinarith
    have hX0 : (0 : ℝ) ≤ X := by positivity
    nlinarith
  · -- `r = R`: the spiral covers a ball of radius `≈ R`
    have hr : r = R := min_eq_right hsq
    have hR0 : (0 : ℝ) ≤ R := by positivity
    have h5 : (2 * (R : ℝ) + 1) ^ 2 ≤ 4 * ((R : ℝ) + 1) ^ 2 := by nlinarith
    rw [hr] at hX'
    have hX0 : (0 : ℝ) ≤ X := by positivity
    have : (36 : ℝ) ≤ 18 * (σ + 1) * k := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    nlinarith

theorem card_filter_ge (b s : ℕ) :
    b + 1 - s ≤ ((univ : Finset (Fin (b + 1))).filter fun p : Fin _ => s ≤ p.val).card := by
  have := Finset.card_le_card_of_injOn (s := range (b + 1 - s))
    (t := (univ : Finset (Fin (b + 1))).filter fun p : Fin _ => s ≤ p.val)
    (fun m => (⟨min (s + m) b, by omega⟩ : Fin (b + 1))) ?_ ?_
  · simpa using this
  · intro m hm
    have hm' := mem_range.1 hm
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    omega
  · intro m hm m' hm' h
    have hm1 := mem_range.1 hm
    have hm2 := mem_range.1 hm'
    have := congrArg Fin.val h
    simp only at this
    omega

/-- **Theorem 3.1 / Corollary 3.2, general form.** If agent `a` runs `A_{κ a}` with
`k/λ ≤ κ a ≤ k` (`λ ≥ 1`), then the expected running time is at most `C (D + λ D²/k)` for a
constant `C` depending only on the spiral constant `σ`. -/
theorem akTime_le {σ : ℕ} (hσ : 1 ≤ σ) : ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ}, 1 ≤ k → ∀ (lam : ℝ),
    1 ≤ lam → ∀ κ : Fin k → ℝ, (∀ a, (k : ℝ) / lam ≤ κ a ∧ κ a ≤ k) → ∀ τ : Node,
    1 ≤ dist τ → akTime σ κ τ ≤
      ENNReal.ofReal (C * (dist τ + lam * (dist τ : ℝ) ^ 2 / k)) := by
  set β : ℝ := 1 / (18 * (σ + 1))
  have hβ : 0 < β := by positivity
  refine ⟨44 * (1 + gaussConst β), by have := gaussConst_nonneg β; positivity, ?_⟩
  intro k hk lam hlam κ hκ τ hτ
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hκ0 : ∀ a, 0 < κ a := fun a => lt_of_lt_of_le (by positivity) (hκ a).1
  set D := dist τ
  set s := Nat.clog 2 D
  have hsD : D ≤ 2 ^ s := Nat.le_pow_clog (by norm_num) D
  have h2s : (2 : ℝ) ^ s ≤ 2 * D := by
    rcases Nat.lt_or_ge 1 D with h | h
    · have h1 : 2 ^ s.pred < D := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
      have hs1 : 1 ≤ s := Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) h)
      have : 2 ^ s = 2 * 2 ^ s.pred := by
        rw [← pow_succ']; congr 1; exact (Nat.succ_pred_eq_of_pos hs1).symm
      have : 2 ^ s ≤ 2 * D := by omega
      exact_mod_cast this
    · have hD1 : D = 1 := le_antisymm h hτ
      have : s = 0 := by simp [s, hD1]
      rw [this, hD1]; norm_num
  rw [akTime, phasedTime_eq]
  refine (tsum_le_of_gauss hβ 4 (11 * lam / k) (by norm_num) (by positivity) s _ ?_).trans ?_
  · intro b
    rw [ENNReal.ofReal_mul (by positivity)]
    gcongr
    · rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (akBlockDur_le hk hlam (fun a => (hκ a).1) b)
    · refine prod_le_gauss s _ (blockFail_le_one _ _ _ _) ?_ b
      intro j hj
      refine (blockFail_le_exp σ akRad (akSpiral κ) τ j
        ((univ : Finset (Fin (j + 1))).filter fun p : Fin _ => s ≤ p.val) (β / k) (by positivity)
        ?_ ?_).trans ?_
      · rw [div_le_one hk']
        have : β ≤ 1 := by
          simp only [β]; rw [div_le_one (by positivity)]
          have : (0 : ℝ) ≤ σ := by positivity
          linarith
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      · intro p hp a
        rw [Finset.mem_filter] at hp
        have := ak_succ_ge hσ hk a (hκ0 a) (hκ a).2 hsD ⟨j, p⟩ hp.2
        convert this using 2
        simp only [β]; field_simp
      · apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        have hc := card_filter_ge j s
        have hc' : (((j - s : ℕ) : ℝ) + 1) ≤ (((univ : Finset (Fin (j + 1))).filter
            fun p : Fin _ => s ≤ p.val).card : ℝ) := by
          have : j - s + 1 = j + 1 - s := by omega
          exact_mod_cast this ▸ hc
        have e : β / k * k = β := by field_simp
        rw [e]
        nlinarith
  · apply ENNReal.ofReal_le_ofReal
    have hG := gaussConst_nonneg β
    have h4s : (4 : ℝ) ^ s ≤ 4 * (D : ℝ) ^ 2 := by
      have : (4 : ℝ) ^ s = (2 ^ s) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [this]
      have : (0 : ℝ) ≤ 2 ^ s := by positivity
      nlinarith
    have hD : (1 : ℝ) ≤ D := by exact_mod_cast hτ
    have : 4 * (2 : ℝ) ^ s + 11 * lam / k * 4 ^ s ≤ 44 * (D + lam * (D : ℝ) ^ 2 / k) := by
      have h1 : 11 * lam / k * 4 ^ s ≤ 11 * lam / k * (4 * (D : ℝ) ^ 2) := by gcongr
      have h2 : 11 * lam / k * (4 * (D : ℝ) ^ 2) = 44 * (lam * (D : ℝ) ^ 2 / k) := by ring
      nlinarith
    have : 0 ≤ 1 + gaussConst β := by linarith
    nlinarith

/-- **Theorem 3.1** of [Feinerman–Korman–Lotker–Sereni]: if the agents know `k`, Algorithm `A_k`
finds the treasure in expected time `O(D + D²/k)`. -/
theorem theorem_3_1 {σ : ℕ} (hσ : 1 ≤ σ) : ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ}, 1 ≤ k → ∀ τ : Node,
    1 ≤ dist τ → akTime σ (fun _ : Fin k => (k : ℝ)) τ ≤
      ENNReal.ofReal (C * (dist τ + (dist τ : ℝ) ^ 2 / k)) := by
  obtain ⟨C, hC, h⟩ := akTime_le hσ
  refine ⟨C, hC, fun {k} hk τ hτ => ?_⟩
  have := h hk 1 le_rfl (fun _ => (k : ℝ)) (fun _ => ⟨by simp, le_rfl⟩) τ hτ
  simpa using this

/-- **Corollary 3.2** of [Feinerman–Korman–Lotker–Sereni]: if every agent `a` receives a
`ρ`-approximation `k/ρ ≤ kₐ ≤ kρ` of `k` and runs `A_{kₐ/ρ}`, the expected running time is
`O(D + D²/k)` (the algorithm is `O(1)`-competitive). -/
theorem corollary_3_2 {σ : ℕ} (hσ : 1 ≤ σ) {ρ : ℝ} (hρ : 1 ≤ ρ) : ∃ C : ℝ, 0 < C ∧
    ∀ {k : ℕ}, 1 ≤ k → ∀ est : Fin k → ℝ, (∀ a, (k : ℝ) / ρ ≤ est a ∧ est a ≤ k * ρ) →
    ∀ τ : Node, 1 ≤ dist τ → akTime σ (fun a => est a / ρ) τ ≤
      ENNReal.ofReal (C * (dist τ + (dist τ : ℝ) ^ 2 / k)) := by
  obtain ⟨C, hC, h⟩ := akTime_le hσ
  refine ⟨C * ρ ^ 2, by positivity, fun {k} hk est hest τ hτ => ?_⟩
  have hρ0 : 0 < ρ := by linarith
  refine (h hk (ρ ^ 2) (by nlinarith) _ (fun a => ⟨?_, ?_⟩) τ hτ).trans ?_
  · rw [le_div_iff₀ hρ0, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have := (hest a).1
    rw [div_le_iff₀ hρ0] at this
    nlinarith
  · rw [div_le_iff₀ hρ0]; exact (hest a).2
  · apply ENNReal.ofReal_le_ofReal
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have : (dist τ : ℝ) + ρ ^ 2 * (dist τ : ℝ) ^ 2 / k
        ≤ ρ ^ 2 * ((dist τ : ℝ) + (dist τ : ℝ) ^ 2 / k) := by
      have : (1 : ℝ) ≤ ρ ^ 2 := by nlinarith
      have h0 : (0 : ℝ) ≤ dist τ := by positivity
      rw [mul_add, mul_div_assoc]
      nlinarith
    calc C * ((dist τ : ℝ) + ρ ^ 2 * (dist τ : ℝ) ^ 2 / k)
        ≤ C * (ρ ^ 2 * ((dist τ : ℝ) + (dist τ : ℝ) ^ 2 / k)) := by gcongr
      _ = _ := by ring

end Podc.CollaborativeSearchPlane
