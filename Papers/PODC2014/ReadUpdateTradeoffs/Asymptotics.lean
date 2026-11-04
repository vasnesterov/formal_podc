import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Asymptotic lemmas for the read/update tradeoffs (PODC 2014, Hendler–Khait)

Pure-math lemmas used to turn the combinatorial lower bounds into the asymptotic statements
of the paper.

* Max register (Theorem 4 style): the construction yields sets `E_0 ⊇ E_1 ⊇ …` with
  `|E_{j+1}| ≥ gStep m |E_j|`, where `gStep m x = ⌊√(x - m)⌋ / 3 - 1`. We show
  `x ^ (1/3) ≤ gStep m x` for `x ≥ max (2m) X₀`, iterate it, and choose the number of
  iterations `t = ⌊log₃ (log s₀ / log T)⌋`; with `m = O(log s₀)` this gives `t = Ω(log log s₀)`.
* Counter (Theorem 2 style): `N - 1 ≤ R * 3 ^ s` gives `s ≥ log₃ ((N - 1) / R)`, and with
  `R = O(log N)` this is `Ω(log N)`.
-/

namespace Podc.ReadUpdateTradeoffs

open Real

/-! ### The step function of the max-register construction -/

/-- One step of the max-register construction: from a set of size `x` one keeps a subset of
size at least `⌊√(x - m)⌋ / 3 - 1` (all operations on natural numbers, truncated). -/
def gStep (m x : ℕ) : ℕ := Nat.sqrt (x - m) / 3 - 1

/-- `gStep m` is monotone. -/
theorem gStep_mono (m : ℕ) : Monotone (gStep m) := by
  intro x y hxy
  unfold gStep
  have := Nat.sqrt_le_sqrt (Nat.sub_le_sub_right hxy m)
  have := Nat.div_le_div_right (c := 3) this
  omega

/-- The threshold above which `x ^ (1/3) ≤ gStep m x` (for `x ≥ 2m`). -/
def X₀ : ℕ := 10 ^ 6

theorem two_le_X₀ : 2 ≤ X₀ := by unfold X₀; norm_num

/-- Natural-number core of `gStep_ge_rpow`: `x ≤ (gStep m x) ^ 3` once `x ≥ max (2m) X₀`. -/
theorem le_gStep_pow_three (m x : ℕ) (hx : max (2 * m) X₀ ≤ x) : x ≤ gStep m x ^ 3 := by
  have h2m : 2 * m ≤ x := le_trans (le_max_left _ _) hx
  have hX : X₀ ≤ x := le_trans (le_max_right _ _) hx
  unfold X₀ at hX
  set r := Nat.sqrt (x - m) with hr
  have hlt : x - m < (r + 1) * (r + 1) := Nat.lt_succ_sqrt (x - m)
  set q := r / 3 with hq
  have hrq : r + 1 ≤ 3 * q + 3 := by omega
  -- `x < 2 (r+1)^2 ≤ 18 (q+1)^2`
  have hx18 : x < 18 * ((q + 1) * (q + 1)) := by
    have h1 : x < 2 * ((r + 1) * (r + 1)) := by omega
    have h2 : (r + 1) * (r + 1) ≤ (3 * q + 3) * (3 * q + 3) := Nat.mul_le_mul hrq hrq
    nlinarith
  -- hence `q` is large
  have hq74 : 74 ≤ q := by
    by_contra h
    push Not at h
    have : (q + 1) * (q + 1) ≤ 74 * 74 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hg : gStep m x = q - 1 := rfl
  rw [hg]
  obtain ⟨p, hp⟩ : ∃ p, q = p + 74 := ⟨q - 74, by omega⟩
  have : q - 1 = p + 73 := by omega
  rw [this]
  rw [hp] at hx18
  nlinarith

/-- For `x ≥ max (2m) X₀`, one step of the construction keeps at least `x ^ (1/3)` elements. -/
theorem gStep_ge_rpow (m x : ℕ) (hx : max (2 * m) X₀ ≤ x) :
    (x : ℝ) ^ ((1 : ℝ) / 3) ≤ gStep m x := by
  have h := le_gStep_pow_three m x hx
  have h' : (x : ℝ) ≤ (gStep m x : ℝ) ^ ((3 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast h
  calc (x : ℝ) ^ ((1 : ℝ) / 3) ≤ ((gStep m x : ℝ) ^ ((3 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (by positivity) h' (by norm_num)
    _ = gStep m x := by
        rw [← Real.rpow_mul (by positivity)]; norm_num

/-! ### Iteration -/

/-- Iterating `gStep_ge_rpow`: if `gStep m (s j) ≤ s (j+1)` for `j < t` and
`max (2m) X₀ ≤ (s 0) ^ (1 / 3^t)`, then for every `j ≤ t` we have `(s 0) ^ (1 / 3^j) ≤ s j`
and `max (2m) X₀ ≤ s j`. -/
theorem rpow_le_iterate (m : ℕ) (s : ℕ → ℕ) (t : ℕ)
    (hs : ∀ j < t, gStep m (s j) ≤ s (j + 1))
    (h0 : ((max (2 * m) X₀ : ℕ) : ℝ) ≤ (s 0 : ℝ) ^ ((1 : ℝ) / 3 ^ t)) :
    ∀ j ≤ t, (s 0 : ℝ) ^ ((1 : ℝ) / 3 ^ j) ≤ s j ∧ max (2 * m) X₀ ≤ s j := by
  have hT : (2 : ℝ) ≤ ((max (2 * m) X₀ : ℕ) : ℝ) := by
    have := le_trans two_le_X₀ (le_max_right (2 * m) X₀)
    exact_mod_cast this
  -- `s 0 ≥ 1`
  have hs0 : (1 : ℝ) ≤ s 0 := by
    rcases Nat.eq_zero_or_pos (s 0) with h | h
    · rw [h, Nat.cast_zero, Real.zero_rpow (by positivity)] at h0
      linarith
    · exact_mod_cast h
  -- the threshold is below `(s 0) ^ (1 / 3^j)` for every `j ≤ t`
  have hTj : ∀ j ≤ t, ((max (2 * m) X₀ : ℕ) : ℝ) ≤ (s 0 : ℝ) ^ ((1 : ℝ) / 3 ^ j) := by
    intro j hj
    refine le_trans h0 (Real.rpow_le_rpow_of_exponent_le hs0 ?_)
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) hj
  have key : ∀ j ≤ t, (s 0 : ℝ) ^ ((1 : ℝ) / 3 ^ j) ≤ s j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih := ih (by omega)
      have hTsj : max (2 * m) X₀ ≤ s j := by
        have := le_trans (hTj j (by omega)) ih
        exact_mod_cast this
      calc (s 0 : ℝ) ^ ((1 : ℝ) / 3 ^ (j + 1))
          = ((s 0 : ℝ) ^ ((1 : ℝ) / 3 ^ j)) ^ ((1 : ℝ) / 3) := by
            rw [← Real.rpow_mul (by positivity)]; congr 1; rw [pow_succ]; field_simp
        _ ≤ (s j : ℝ) ^ ((1 : ℝ) / 3) :=
            Real.rpow_le_rpow (by positivity) ih (by norm_num)
        _ ≤ gStep m (s j) := gStep_ge_rpow m (s j) hTsj
        _ ≤ s (j + 1) := by exact_mod_cast hs j (by omega)
  intro j hj
  refine ⟨key j hj, ?_⟩
  have := le_trans (hTj j hj) (key j hj)
  exact_mod_cast this

/-! ### Choice of the number of iterations -/

/-- The number of iterations: `t = ⌊log₃ (log s₀ / log T)⌋`. -/
noncomputable def tChoice (T s₀ : ℝ) : ℕ := ⌊Real.logb 3 (Real.log s₀ / Real.log T)⌋₊

/-- With `t = tChoice T s₀` (for `2 ≤ T ≤ s₀`) we still have `T ≤ s₀ ^ (1 / 3^t)`, and
`t ≥ log₃ (log s₀ / log T) - 1`. -/
theorem tChoice_spec (T s₀ : ℝ) (hT : 2 ≤ T) (hs : T ≤ s₀) :
    T ≤ s₀ ^ ((1 : ℝ) / 3 ^ tChoice T s₀) ∧
      Real.logb 3 (Real.log s₀ / Real.log T) - 1 ≤ tChoice T s₀ := by
  have hT0 : 0 < T := by linarith
  have hs0 : 0 < s₀ := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlog : Real.log T ≤ Real.log s₀ := Real.log_le_log hT0 hs
  have hL : 1 ≤ Real.log s₀ / Real.log T := by rw [le_div_iff₀ hlogT]; linarith
  set t := tChoice T s₀ with ht
  constructor
  · have h1 : (t : ℝ) ≤ Real.logb 3 (Real.log s₀ / Real.log T) :=
      Nat.floor_le (Real.logb_nonneg (by norm_num) hL)
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_natCast,
      le_div_iff₀ hlogT] at h1
    rw [← Real.log_le_log_iff hT0 (by positivity), Real.log_rpow hs0]
    rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    linarith
  · have : Real.logb 3 (Real.log s₀ / Real.log T) < (t : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith

/-- The doubly-logarithmic bound of the max-register construction: if
`gStep m (s j) ≤ s (j+1)` for all `j` and `s 0 ≥ T := max (2m) X₀`, then after
`t ≥ log₃ (log (s 0) / log T) - 1` steps the set still has size `≥ T` (in particular
`≥ 2m`). The witness is `t = tChoice T (s 0)`. -/
theorem doubly_log_bound (m : ℕ) (s : ℕ → ℕ) (hs : ∀ j, gStep m (s j) ≤ s (j + 1))
    (h0 : max (2 * m) X₀ ≤ s 0) :
    ∃ t : ℕ, Real.logb 3 (Real.log (s 0) / Real.log ((max (2 * m) X₀ : ℕ) : ℝ)) - 1 ≤ t ∧
      max (2 * m) X₀ ≤ s t := by
  have hT : (2 : ℝ) ≤ ((max (2 * m) X₀ : ℕ) : ℝ) := by
    have := le_trans two_le_X₀ (le_max_right (2 * m) X₀)
    exact_mod_cast this
  obtain ⟨h1, h2⟩ := tChoice_spec ((max (2 * m) X₀ : ℕ) : ℝ) (s 0 : ℝ) hT (Nat.cast_le.mpr h0)
  exact ⟨_, h2, (rpow_le_iterate m s _ (fun j _ => hs j) h1 _ le_rfl).2⟩

/-- `u² / 256 ≤ exp √u` for `u ≥ 0`. -/
theorem sq_div_le_exp_sqrt (u : ℝ) (hu : 0 ≤ u) : u ^ 2 / 256 ≤ Real.exp (Real.sqrt u) := by
  have h1 : Real.sqrt u / 4 ≤ Real.exp (Real.sqrt u / 4) := by
    have := Real.add_one_le_exp (Real.sqrt u / 4); linarith
  have h2 : (Real.sqrt u / 4) ^ 4 ≤ Real.exp (Real.sqrt u / 4) ^ 4 :=
    pow_le_pow_left₀ (by positivity) h1 4
  rw [← Real.exp_nat_mul] at h2
  have h3 : (Real.sqrt u / 4) ^ 4 = u ^ 2 / 256 := by
    have := Real.sq_sqrt hu
    rw [div_pow, show Real.sqrt u ^ 4 = (Real.sqrt u ^ 2) ^ 2 by ring, this]; norm_num
  have h4 : ((4 : ℕ) : ℝ) * (Real.sqrt u / 4) = Real.sqrt u := by push_cast; ring
  rw [h3, h4] at h2
  exact h2

/-- Theorem 4 style corollary (`Ω(log log)`): for every `c` there are `K₀` and `c' > 0` such
that if `s 0 ≥ K₀`, `m ≤ c · log (s 0)` and `gStep m (s j) ≤ s (j+1)` for all `j`, then there is
`t ≥ c' · log log (s 0)` with `max (2m) X₀ ≤ s t`. -/
theorem loglog_bound (c : ℝ) :
    ∃ K₀ : ℕ, ∃ c' > (0 : ℝ), ∀ (m : ℕ) (s : ℕ → ℕ),
      (∀ j, gStep m (s j) ≤ s (j + 1)) → K₀ ≤ s 0 → (m : ℝ) ≤ c * Real.log (s 0) →
      ∃ t : ℕ, c' * Real.log (Real.log (s 0)) ≤ t ∧ max (2 * m) X₀ ≤ s t := by
  set U : ℝ := max 16000 (512 * c) with hU
  refine ⟨⌈Real.exp U⌉₊, 1 / (4 * Real.log 3), by positivity, ?_⟩
  intro m s hs hK hm
  have hexp : Real.exp U ≤ (s 0 : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hK)
  have hs0 : 0 < (s 0 : ℝ) := lt_of_lt_of_le (Real.exp_pos U) hexp
  set u := Real.log (s 0) with hu
  have hUu : U ≤ u := by rw [Real.le_log_iff_exp_le hs0]; exact hexp
  have hu1 : 16000 ≤ u := le_trans (le_max_left _ _) hUu
  have hu2 : 512 * c ≤ u := le_trans (le_max_right _ _) hUu
  set T : ℝ := ((max (2 * m) X₀ : ℕ) : ℝ) with hTdef
  have hT2 : (2 : ℝ) ≤ T := by
    have := le_trans two_le_X₀ (le_max_right (2 * m) X₀)
    rw [hTdef]; exact_mod_cast this
  -- `T ≤ u² / 256`
  have hTu : T ≤ u ^ 2 / 256 := by
    rw [hTdef, Nat.cast_max]
    apply max_le
    · push_cast; nlinarith
    · unfold X₀; push_cast; nlinarith
  have hsqrt : Real.sqrt u ≤ u := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hTexp : T ≤ Real.exp (Real.sqrt u) := le_trans hTu (sq_div_le_exp_sqrt u (by linarith))
  have hTs0 : T ≤ s 0 := by
    refine le_trans hTexp ?_
    rw [← Real.exp_log hs0]; exact Real.exp_le_exp.mpr hsqrt
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogTu : Real.log T ≤ Real.sqrt u := by
    rw [Real.log_le_iff_le_exp (by linarith)]; exact hTexp
  obtain ⟨h1, h2⟩ := tChoice_spec T (s 0) hT2 hTs0
  refine ⟨tChoice T (s 0), ?_, ?_⟩
  · -- `log (u / log T) ≥ log √u = log u / 2`
    have hsqpos : 0 < Real.sqrt u := Real.sqrt_pos.mpr (by linarith)
    have hL : Real.sqrt u ≤ u / Real.log T := by
      rw [le_div_iff₀ hlogT]
      calc Real.sqrt u * Real.log T ≤ Real.sqrt u * Real.sqrt u :=
            mul_le_mul_of_nonneg_left hlogTu hsqpos.le
        _ = u := Real.mul_self_sqrt (by linarith)
    have hlogL : Real.log u / 2 ≤ Real.log (u / Real.log T) := by
      rw [← Real.log_sqrt (by linarith)]
      exact Real.log_le_log hsqpos hL
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hlogu : 4 * Real.log 3 ≤ Real.log u := by
      rw [← Real.log_rpow (by norm_num)]
      apply Real.log_le_log (by positivity)
      norm_num; linarith
    rw [Real.logb, ← hu] at h2
    have h3 : Real.log u / 2 / Real.log 3 ≤ Real.log (u / Real.log T) / Real.log 3 :=
      div_le_div_of_nonneg_right hlogL hlog3.le
    have h4 : 1 / (4 * Real.log 3) * Real.log u = Real.log u / 2 / Real.log 3
        - Real.log u / (4 * Real.log 3) := by
      field_simp; ring
    have h5 : 1 ≤ Real.log u / (4 * Real.log 3) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    rw [h4]
    linarith
  · exact (rpow_le_iterate m s _ (fun j _ => hs j) h1 _ le_rfl).2

/-! ### Counter side -/

/-- If `N - 1 ≤ R · 3^s` (with `N ≥ 2`, `R ≥ 1`) then `log₃ ((N - 1) / R) ≤ s`. -/
theorem logb_le_of_mul_pow (N R s : ℕ) (hN : 2 ≤ N) (hR : 1 ≤ R) (h : N - 1 ≤ R * 3 ^ s) :
    Real.logb 3 (((N : ℝ) - 1) / R) ≤ s := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by apply div_pos <;> linarith), Real.rpow_natCast,
    div_le_iff₀ hR']
  have : ((N - 1 : ℕ) : ℝ) ≤ ((R * 3 ^ s : ℕ) : ℝ) := by exact_mod_cast h
  push_cast [Nat.cast_sub (by omega : 1 ≤ N)] at this
  linarith

/-- Theorem 2 style corollary (`Ω(log N)`): for every `c` there is `N₀` such that
`N ≥ N₀`, `1 ≤ R ≤ c · log N` and `N - 1 ≤ R · 3^s` imply `log₃ N / 2 ≤ s`. -/
theorem log_bound_of_mul_pow (c : ℝ) :
    ∃ N₀ : ℕ, ∀ N R s : ℕ, N₀ ≤ N → 1 ≤ R → (R : ℝ) ≤ c * Real.log N →
      N - 1 ≤ R * 3 ^ s → Real.logb 3 N / 2 ≤ s := by
  refine ⟨max 2 ⌈Real.exp (32 * c)⌉₊, ?_⟩
  intro N R s hN hR hRc h
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hexp : Real.exp (32 * c) ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hN)
  set u := Real.log N with hu
  have hu32 : 32 * c ≤ u := by rw [Real.le_log_iff_exp_le (by linarith)]; exact hexp
  have hu0 : 0 < u := Real.log_pos (by linarith)
  have hcu : 1 ≤ c * u := le_trans hR' hRc
  have hmain := logb_le_of_mul_pow N R s hN2 hR h
  -- `log N / 2 ≤ log ((N - 1) / R)`
  have h2cu : 2 * (c * u) ≤ Real.exp (u / 2) := by
    have e1 : u / 4 ≤ Real.exp (u / 4) := by have := Real.add_one_le_exp (u / 4); linarith
    have e2 : (u / 4) ^ 2 ≤ Real.exp (u / 4) ^ 2 := pow_le_pow_left₀ (by positivity) e1 2
    rw [← Real.exp_nat_mul] at e2
    have e3 : ((2 : ℕ) : ℝ) * (u / 4) = u / 2 := by push_cast; ring
    rw [e3] at e2
    nlinarith
  have hlog2cu : Real.log 2 + Real.log (c * u) ≤ u / 2 := by
    rw [← Real.log_mul (by norm_num) (by linarith), Real.log_le_iff_le_exp (by linarith)]
    exact h2cu
  have hN1 : Real.log N - Real.log 2 ≤ Real.log ((N : ℝ) - 1) := by
    rw [← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hlogR : Real.log R ≤ Real.log (c * u) := Real.log_le_log (by linarith) hRc
  have hkey : u / 2 ≤ Real.log (((N : ℝ) - 1) / R) := by
    rw [Real.log_div (by linarith) (by linarith)]
    linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [Real.logb] at hmain ⊢
  have : u / 2 / Real.log 3 ≤ Real.log (((N : ℝ) - 1) / R) / Real.log 3 :=
    div_le_div_of_nonneg_right hkey hlog3.le
  calc u / Real.log 3 / 2 = u / 2 / Real.log 3 := by ring
    _ ≤ _ := this
    _ ≤ s := hmain

end Podc.ReadUpdateTradeoffs
