import Papers.PODC2021.UltraSparseEmulators.Main

/-!
# Corollary 2.15: ultra-sparse emulators (`n + o(n)` edges)

Elkin, Matar. *Ultra-Sparse Near-Additive Emulators.* PODC 2021 (arXiv:2106.01036v1).

The paper sets `κ = f(n) log n` with `f(n) = ω(1)`. The size bound `n^{1+1/κ} = n · 2^{1/f(n)}
= n + o(n)` holds for every such `f`; the claimed `β = (log log n / ε)^{(1+o(1)) log log n}` needs
`f` to grow slowly (`log f(n) = o(log log n)`; e.g. for `f(n) = n` it fails). We take
`f(n) = log₂ log₂ n`, i.e. `κ(n) = ⌈log₂ n · log₂ log₂ n⌉`.
-/

namespace Podc.UltraSparseEmulators

open SimpleGraph Real Filter Asymptotics Topology
open scoped Classical

/-- The choice `κ(n) = ⌈log₂ n · log₂ log₂ n⌉` (i.e. `f(n) = log₂ log₂ n`). -/
noncomputable def kappa (n : ℕ) : ℕ := ⌈logb 2 n * logb 2 (logb 2 n)⌉₊

/-! ### Asymptotic helpers

`t` stands for `log₂ log₂ n`. Since `κ(n) ≤ 2 log₂ n · t`, we have `log₂ κ(n) ≤ M(t) := t + log₂ t + 1`,
so `β = 30 (34 log₂ κ / ε)^{log₂ κ - 1} ≤ exp (num ε t)`, and `h(n) := φ ε t` is chosen so that
`(t/ε)^{(1 + h(n)) t} = exp (num ε t)` exactly. -/

namespace Cor215

/-- `M(t) = t + log₂ t + 1`. -/
noncomputable def M (t : ℝ) : ℝ := t + logb 2 t + 1

/-- `num ε t = log 30 + M(t) log(34 M(t)/ε)`. -/
noncomputable def num (ε t : ℝ) : ℝ := log 30 + M t * log (34 * M t / ε)

/-- `φ ε t = num ε t / (t log(t/ε)) - 1`. -/
noncomputable def φ (ε t : ℝ) : ℝ := num ε t / (t * log (t / ε)) - 1

/-- `M(t)/t → 1`. -/
lemma tendsto_M_div : Tendsto (fun t => M t / t) atTop (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ => logb 2 t / t) atTop (𝓝 0) := by
    have h2 := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.div_const (log 2)
    simp only [zero_div] at h2
    refine h2.congr' (Eventually.of_forall fun t => ?_)
    simp only [Real.logb, id]
    ring
  have h3 : Tendsto (fun t : ℝ => 1 + logb 2 t / t + t⁻¹) atTop (𝓝 (1 + 0 + 0)) :=
    (tendsto_const_nhds.add h1).add tendsto_inv_atTop_zero
  rw [add_zero, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [M]
  field_simp

/-- `log(t/ε) → ∞`. -/
lemma tendsto_log_div {ε : ℝ} (hε : 0 < ε) : Tendsto (fun t => log (t / ε)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const hε)

/-- `M(t) > 0` for `t > 1`. -/
lemma M_pos {t : ℝ} (ht : 1 < t) : 0 < M t := by
  have := Real.logb_pos (by norm_num : (1 : ℝ) < 2) ht
  simp only [M]; linarith

/-- `log(34 M(t)/ε) / log(t/ε) → 1`. -/
lemma tendsto_log_ratio {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun t => log (34 * M t / ε) / log (t / ε)) atTop (𝓝 1) := by
  have hA : Tendsto (fun t => log (34 * (M t / t))) atTop (𝓝 (log (34 * 1))) :=
    ((tendsto_M_div.const_mul 34).log (by norm_num))
  have hB : Tendsto (fun t => 1 + log (34 * (M t / t)) / log (t / ε)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (hA.div_atTop (tendsto_log_div hε))
  rw [add_zero] at hB
  refine hB.congr' ?_
  filter_upwards [eventually_gt_atTop 1, eventually_gt_atTop ε] with t ht1 htε
  have ht : 0 < t := by linarith
  have hM := M_pos ht1
  have hlog : 0 < log (t / ε) := Real.log_pos ((one_lt_div hε).2 htε)
  have : 34 * M t / ε = (t / ε) * (34 * (M t / t)) := by field_simp
  rw [this, Real.log_mul (x := t / ε) (y := 34 * (M t / t)) (by positivity) (by positivity),
    add_div, div_self hlog.ne']

/-- `φ ε t → 0`, i.e. `num ε t ~ t log(t/ε)`. -/
lemma tendsto_φ {ε : ℝ} (hε : 0 < ε) : Tendsto (φ ε) atTop (𝓝 0) := by
  have hD : Tendsto (fun t => t * log (t / ε)) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ (tendsto_log_div hε)
  have h1 : Tendsto (fun t => log 30 / (t * log (t / ε)) +
      (M t / t) * (log (34 * M t / ε) / log (t / ε)) - 1) atTop (𝓝 (0 + 1 * 1 - 1)) :=
    ((tendsto_const_nhds.div_atTop hD).add (tendsto_M_div.mul (tendsto_log_ratio hε))).sub
      tendsto_const_nhds
  norm_num at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 1, eventually_gt_atTop ε] with t ht1 htε
  have ht : 0 < t := by linarith
  have hlog : 0 < log (t / ε) := Real.log_pos ((one_lt_div hε).2 htε)
  simp only [φ, num]
  field_simp

/-- `log₂ n → ∞`. -/
lemma tendsto_logb_nat : Tendsto (fun n : ℕ => logb 2 (n : ℝ)) atTop atTop :=
  (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop

/-- `log₂ log₂ n → ∞`. -/
lemma tendsto_L : Tendsto (fun n : ℕ => logb 2 (logb 2 (n : ℝ))) atTop atTop :=
  (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_logb_nat

/-- `log₂ n · log₂ log₂ n ≤ κ(n)`. -/
lemma kappa_ge (n : ℕ) : logb 2 (n : ℝ) * logb 2 (logb 2 (n : ℝ)) ≤ (kappa n : ℝ) :=
  Nat.le_ceil _

/-- `κ(n) ≤ log₂ n · log₂ log₂ n + 1`. -/
lemma kappa_le {n : ℕ} (h : 0 ≤ logb 2 (n : ℝ) * logb 2 (logb 2 (n : ℝ))) :
    (kappa n : ℝ) ≤ logb 2 (n : ℝ) * logb 2 (logb 2 (n : ℝ)) + 1 :=
  (Nat.ceil_lt_add_one h).le

/-- If `y = log₂ x` and `y L ≤ K`, then `x^{1/K} ≤ 2^{1/L}`. -/
lemma rpow_inv_le {x y L K : ℝ} (hx : 0 < x) (hy : y = logb 2 x) (hL : 0 < L) (hK0 : 0 < K)
    (hK : y * L ≤ K) : x ^ (1 / K) ≤ (2 : ℝ) ^ L⁻¹ := by
  have hx2 : x = (2 : ℝ) ^ y := by
    rw [hy, Real.rpow_logb (by norm_num) (by norm_num) hx]
  rw [hx2, ← Real.rpow_mul (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [mul_one_div, div_le_iff₀ hK0, inv_mul_eq_div, le_div_iff₀ hL]
  exact hK

/-- `n^{1/κ(n)} → 1`. -/
lemma tendsto_rpow_kappa :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (kappa n : ℝ)) - 1) atTop (𝓝 0) := by
  have hup : Tendsto (fun n : ℕ => (2 : ℝ) ^ (logb 2 (logb 2 (n : ℝ)))⁻¹ - 1) atTop (𝓝 0) := by
    have h := ((Real.continuousAt_const_rpow (a := (2 : ℝ)) (b := 0) (by norm_num)).tendsto.comp
      (tendsto_inv_atTop_zero.comp tendsto_L)).sub_const 1
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simpa using Real.one_le_rpow this (by positivity)
  · filter_upwards [eventually_ge_atTop 1, tendsto_logb_nat.eventually_ge_atTop 4,
      tendsto_L.eventually_ge_atTop 2] with n hn hy hL
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hK := kappa_ge n
    have hyL : 8 ≤ logb 2 (n : ℝ) * logb 2 (logb 2 (n : ℝ)) := by nlinarith
    exact sub_le_sub_right (rpow_inv_le hn' rfl (by linarith) (by linarith) hK) 1

/-- The `β` of Corollary 2.14 for `κ = K ∈ [yL, yL + 1]`, `L = log₂ y`, is at most
`(L/ε)^{(1 + φ ε L) L}`. -/
lemma beta_le {ε y L K : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hy : 4 ≤ y) (hLy : L = logb 2 y)
    (hL : 2 ≤ L) (hK1 : y * L ≤ K) (hK2 : K ≤ y * L + 1) :
    30 * (34 * logb 2 K / ε) ^ (logb 2 K - 1) ≤ (L / ε) ^ ((1 + φ ε L) * L) := by
  have hyL : 8 ≤ y * L := by nlinarith
  have hK0 : 0 < K := by linarith
  set Λ := logb 2 K with hΛ
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ, Real.le_logb_iff_rpow_le (by norm_num) hK0]; norm_num; linarith
  have hΛM : Λ ≤ M L := by
    have h2 : K ≤ 2 * y * L := by linarith
    have h3 : Λ ≤ logb 2 (2 * y * L) := Real.logb_le_logb_of_le (by norm_num) hK0 h2
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num) (by positivity),
      Real.logb_self_eq_one (by norm_num), ← hLy] at h3
    simp only [M]; linarith
  have hM1 : 1 ≤ M L := hΛ1.trans hΛM
  have hLε : 1 < L / ε := (one_lt_div hε0).2 (by linarith)
  have hlogLε : 0 < log (L / ε) := Real.log_pos hLε
  have hb : 0 < 34 * Λ / ε := div_pos (by linarith) hε0
  have hβ : 0 < 30 * (34 * Λ / ε) ^ (Λ - 1) := mul_pos (by norm_num) (Real.rpow_pos_of_pos hb _)
  have hR : (L / ε) ^ ((1 + φ ε L) * L) = exp (num ε L) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    congr 1
    simp only [φ]
    field_simp
    ring
  rw [hR, ← Real.exp_log hβ]
  apply Real.exp_le_exp.2
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hb _).ne', Real.log_rpow hb]
  simp only [num]
  have h1 : 0 ≤ log (34 * Λ / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε0]; linarith)
  have h2 : log (34 * Λ / ε) ≤ log (34 * M L / ε) :=
    Real.log_le_log hb (by gcongr)
  nlinarith

end Cor215

/-- **Corollary 2.15.** For every `0 < ε < 1` there are `g(n) = o(n)` and `h(n) → 0` such that, for
all large `n`, Algorithm 1 (with `κ = κ(n)`, run with `ε/(34ℓ)`, in any order) outputs for every
`n`-vertex graph a `(1 + ε, β)`-emulator with at most `n + g(n)` edges, where
`β = (log₂ log₂ n / ε)^{(1 + h(n)) log₂ log₂ n}`. -/
theorem corollary_2_15 {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ g h : ℕ → ℝ, g =o[atTop] (fun n => (n : ℝ)) ∧ Tendsto h atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, 2 ≤ kappa n ∧
        ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (ord : ℕ → List V),
          (∀ i x, x ∈ ord i) → Fintype.card V = n →
          ((ultraSparseEmulator G (ε / (34 * numPhases (kappa n))) (kappa n) ord).edgeFinset.card
              : ℝ) ≤ n + g n ∧
          G.IsEmulator (ultraSparseEmulator G (ε / (34 * numPhases (kappa n))) (kappa n) ord)
            G.distW (1 + ε)
            ((logb 2 (logb 2 n) / ε) ^ ((1 + h n) * logb 2 (logb 2 n))) := by
  refine ⟨fun n => (n : ℝ) * ((n : ℝ) ^ (1 / (kappa n : ℝ)) - 1),
    fun n => Cor215.φ ε (logb 2 (logb 2 (n : ℝ))), ?_,
    (Cor215.tendsto_φ hε0).comp Cor215.tendsto_L, ?_⟩
  · have := (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO
      ((isLittleO_one_iff ℝ).2 Cor215.tendsto_rpow_kappa)
    simpa using this
  · filter_upwards [eventually_ge_atTop 1, Cor215.tendsto_logb_nat.eventually_ge_atTop 4,
      Cor215.tendsto_L.eventually_ge_atTop 2] with n hn hy hL
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hK := Cor215.kappa_ge n
    have hyL : 8 ≤ logb 2 (n : ℝ) * logb 2 (logb 2 (n : ℝ)) := by nlinarith
    have hK2 : 2 ≤ kappa n := by
      have : (2 : ℝ) ≤ kappa n := by linarith
      exact_mod_cast this
    refine ⟨hK2, fun V _ G ord hord hcard => ?_⟩
    obtain ⟨hs, he⟩ := corollary_2_14 (G := G) (ord := ord) hε0 hε1 hK2 hord
    rw [hcard] at hs
    refine ⟨hs.trans (le_of_eq ?_), he.mono le_rfl
      (Cor215.beta_le hε0 hε1 hy rfl hL hK (Cor215.kappa_le (by linarith)))⟩
    rw [Real.rpow_add hn', Real.rpow_one]
    ring

end Podc.UltraSparseEmulators
