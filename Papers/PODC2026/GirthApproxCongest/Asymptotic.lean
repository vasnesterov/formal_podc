import Papers.PODC2026.GirthApproxCongest.LowerBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Choice of parameters for Theorem 6.2

For `n` nodes and `k ≥ 3` we take `a = ⌊n^{(k-1)/(2k-1)}⌋` (side size of `H`), tree depth
`d = ⌊log₂ n⌋ + 1` and `q = ⌊n / (2a + d + 1)⌋` layers; the lower-bound graph then has at most `n`
nodes (padding makes up the rest). `core` turns the alternative `q ≤ 2T + 1` or
`κ · m ≤ T · 2 (d + 1) B + 2` (with `m ≥ c · a^{k/(k-1)}` edges in `H`) into
`C · n^{k/(2k-1)} ≤ (T + 1)(B + 1)(log₂ n + 2)`.
-/

namespace Podc.GirthApproxCongest

open Filter Real

/-- Side size of `H` for `n` nodes. -/
noncomputable def aOf (k n : ℕ) : ℕ := ⌊(n : ℝ) ^ (((k : ℝ) - 1) / (2 * k - 1))⌋₊

/-- Depth of the shortcut tree for `n` nodes. -/
def dOf (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- Number of layers for `n` nodes. -/
noncomputable def qOf (k n : ℕ) : ℕ := n / (2 * aOf k n + dOf n + 1)

lemma qOf_mul_le (k n : ℕ) : qOf k n * (2 * aOf k n + dOf n + 1) ≤ n :=
  Nat.div_mul_le_self _ _

lemma le_two_pow_dOf (n : ℕ) : n ≤ 2 ^ dOf n := (Nat.lt_pow_succ_log_self (by norm_num) n).le

/-- Eventually, `n^r ≥ M`. -/
lemma eventually_rpow_ge {r : ℝ} (hr : 0 < r) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, M ≤ (n : ℝ) ^ r :=
  ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop M

/-- Eventually, `log₂ n + 2 ≤ n^r`. -/
lemma eventually_dOf_le {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, (dOf n : ℝ) + 1 ≤ (n : ℝ) ^ r := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (Real.log 2 / 2) * ‖x ^ r‖ :=
    (isLittleO_log_rpow_atTop hr).bound (by positivity)
  have h1' := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h1', eventually_rpow_ge hr 4, eventually_ge_atTop 1] with n hn h4 hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlog : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
    have := Real.natLog_le_logb n 2
    simpa [Real.logb] using this
  have hpos : 0 ≤ (n : ℝ) ^ r := by positivity
  have hln : Real.log n ≤ Real.log 2 / 2 * (n : ℝ) ^ r := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos] at hn
    exact (le_abs_self _).trans hn
  have : Real.log n / Real.log 2 ≤ (n : ℝ) ^ r / 2 := by
    rw [div_le_iff₀ hl2]; nlinarith
  simp only [dOf]; push_cast
  linarith

/-- **Parameter bookkeeping for Theorem 6.2.** -/
lemma core {k : ℕ} (hk : 3 ≤ k) {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, 1 ≤ aOf k n ∧ 2 ≤ qOf k n ∧
      ∀ (T B : ℕ) (m : ℝ), c * (aOf k n : ℝ) ^ (1 + 1 / ((k : ℝ) - 1)) ≤ m →
        (qOf k n ≤ 2 * T + 1 ∨ κ * m ≤ T * (2 * ((dOf n + 1) * B)) + 2) →
        C * (n : ℝ) ^ ((k : ℝ) / (2 * k - 1)) ≤ (T + 1) * (B + 1) * (Nat.log 2 n + 2) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  set γ : ℝ := ((k : ℝ) - 1) / (2 * k - 1) with hγ
  set β : ℝ := (k : ℝ) / (2 * k - 1) with hβ
  set ε : ℝ := 1 + 1 / ((k : ℝ) - 1) with hε
  have h2k : (0 : ℝ) < 2 * k - 1 := by linarith
  have hγ0 : 0 < γ := div_pos (by linarith) h2k
  have hβ0 : 0 < β := div_pos (by linarith) h2k
  have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith
  have hk2 : 2 * (k : ℝ) - 1 ≠ 0 := by linarith
  have hβγ : β = 1 - γ := by
    rw [hβ, hγ, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hk2]; ring
  have hγε : γ * ε = β := by
    rw [hγ, hε, hβ]; field_simp; ring
  have hε2 : ε ≤ 2 := by
    have : 1 / ((k : ℝ) - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    rw [hε]; linarith
  have hε0 : 0 ≤ ε := by
    have : 0 ≤ 1 / ((k : ℝ) - 1) := by apply div_nonneg <;> linarith
    rw [hε]; linarith
  refine ⟨min (1 / 12) (κ * c / 16), lt_min (by norm_num) (by positivity), ?_⟩
  filter_upwards [eventually_rpow_ge hγ0 2, eventually_dOf_le hγ0, eventually_rpow_ge hβ0 12,
    eventually_rpow_ge hβ0 (16 / (κ * c)), eventually_ge_atTop 1] with n hγn hdn hβn hβn' hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set x := (n : ℝ) ^ γ with hx
  have hx0 : 0 < x := by positivity
  -- bounds on `a`
  have ha1 : (aOf k n : ℝ) ≤ x := Nat.floor_le hx0.le
  have ha2 : x / 2 ≤ (aOf k n : ℝ) := by
    have := Nat.lt_floor_add_one x
    simp only [aOf] at *
    linarith
  have ha : 1 ≤ aOf k n := by
    have : (1 : ℝ) ≤ aOf k n := by linarith
    exact_mod_cast this
  -- bounds on `q`
  have hnx : (n : ℝ) / x = (n : ℝ) ^ β := by
    rw [hx, hβγ, Real.rpow_sub hn0, Real.rpow_one]
  have hden : ((2 * aOf k n + dOf n + 1 : ℕ) : ℝ) ≤ 3 * x := by push_cast; linarith
  have hden0 : (0 : ℝ) < ((2 * aOf k n + dOf n + 1 : ℕ) : ℝ) := by positivity
  have hq : (n : ℝ) ^ β / 6 ≤ qOf k n := by
    have h1 := Nat.lt_div_mul_add (a := n) (b := 2 * aOf k n + dOf n + 1) (by omega)
    have h1' : (n : ℝ) < ((qOf k n : ℕ) + 1) * ((2 * aOf k n + dOf n + 1 : ℕ) : ℝ) := by
      have : (n : ℝ) < ((n / (2 * aOf k n + dOf n + 1) * (2 * aOf k n + dOf n + 1) +
          (2 * aOf k n + dOf n + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      simp only [qOf]; push_cast at this ⊢; linarith
    have h2 : (n : ℝ) ≤ ((qOf k n : ℝ) + 1) * (3 * x) :=
      h1'.le.trans (mul_le_mul_of_nonneg_left hden (by positivity))
    have h3 : (n : ℝ) ^ β ≤ ((qOf k n : ℝ) + 1) * 3 := by
      rw [← hnx, div_le_iff₀ hx0]; linarith
    linarith
  have hq2 : 2 ≤ qOf k n := by
    have : (2 : ℝ) ≤ qOf k n := by linarith
    exact_mod_cast this
  refine ⟨ha, hq2, fun T B m hm hcase => ?_⟩
  have hD : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ Nat.log 2 n := by positivity
    linarith
  have hB : (1 : ℝ) ≤ (B : ℝ) + 1 := by
    have : (0 : ℝ) ≤ B := by positivity
    linarith
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have hprod : (T : ℝ) + 1 ≤ (T + 1) * (B + 1) * (Nat.log 2 n + 2) := by
    have : (1 : ℝ) ≤ ((B : ℝ) + 1) * (Nat.log 2 n + 2) := by nlinarith
    nlinarith
  have hnβ0 : 0 ≤ (n : ℝ) ^ β := by positivity
  rcases hcase with hcase | hcase
  · have hT : (qOf k n : ℝ) ≤ 2 * T + 1 := by exact_mod_cast hcase
    calc min (1 / 12) (κ * c / 16) * (n : ℝ) ^ β ≤ 1 / 12 * (n : ℝ) ^ β :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hnβ0
      _ ≤ T + 1 := by linarith
      _ ≤ _ := hprod
  · -- the edge count
    have hm' : c * ((n : ℝ) ^ β / 4) ≤ m := by
      refine le_trans ?_ hm
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      have e1 : (x / 2) ^ ε ≤ (aOf k n : ℝ) ^ ε :=
        Real.rpow_le_rpow (by positivity) ha2 hε0
      have e2 : (x / 2) ^ ε = (n : ℝ) ^ β * (1 / 2) ^ ε := by
        rw [div_eq_mul_one_div, Real.mul_rpow hx0.le (by norm_num), hx, ← Real.rpow_mul hn0.le,
          hγε]
      have e3 : (1 / 4 : ℝ) ≤ (1 / 2) ^ ε := by
        have := Real.rpow_le_rpow_of_exponent_ge (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
          hε2
        have h22 : (1 / 2 : ℝ) ^ (2 : ℝ) = 1 / 4 := by norm_num
        linarith
      calc (n : ℝ) ^ β / 4 = (n : ℝ) ^ β * (1 / 4) := by ring
        _ ≤ (n : ℝ) ^ β * (1 / 2) ^ ε := mul_le_mul_of_nonneg_left e3 hnβ0
        _ = (x / 2) ^ ε := e2.symm
        _ ≤ _ := e1
    have hcase' : κ * m ≤ (T : ℝ) * (2 * (((dOf n : ℝ) + 1) * B)) + 2 := by exact_mod_cast hcase
    have hbig : 16 / (κ * c) ≤ (n : ℝ) ^ β := hβn'
    have hkc : 0 < κ * c := by positivity
    have h16 : 16 ≤ κ * c * (n : ℝ) ^ β := by
      rw [div_le_iff₀ hkc] at hbig; linarith
    have hlin : κ * c * (n : ℝ) ^ β / 8 ≤ (T : ℝ) * (2 * (((dOf n : ℝ) + 1) * B)) := by
      have : κ * (c * ((n : ℝ) ^ β / 4)) ≤ κ * m := mul_le_mul_of_nonneg_left hm' hκ.le
      nlinarith
    have hdOf : (dOf n : ℝ) + 1 = (Nat.log 2 n : ℝ) + 2 := by simp only [dOf]; push_cast; ring
    rw [hdOf] at hlin
    have hfin : (T : ℝ) * (2 * (((Nat.log 2 n : ℝ) + 2) * B)) ≤
        2 * ((T + 1) * (B + 1) * (Nat.log 2 n + 2)) := by
      have hl0 : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) + 2 := by positivity
      have hB0 : (0 : ℝ) ≤ B := by positivity
      have hTB : (T : ℝ) * B ≤ (T + 1) * (B + 1) := by nlinarith
      calc (T : ℝ) * (2 * (((Nat.log 2 n : ℝ) + 2) * B))
          = 2 * ((T * B) * ((Nat.log 2 n : ℝ) + 2)) := by ring
        _ ≤ 2 * (((T + 1) * (B + 1)) * ((Nat.log 2 n : ℝ) + 2)) := by gcongr
        _ = _ := by ring
    calc min (1 / 12) (κ * c / 16) * (n : ℝ) ^ β ≤ κ * c / 16 * (n : ℝ) ^ β :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hnβ0
      _ ≤ _ := by linarith [hlin, hfin]

/-! ### Number of vertices -/

/-- `Vtx L R q d p` as a sum type. -/
def Vtx.equivSum (L R : Type*) (q d p : ℕ) :
    Vtx L R q d p ≃ ((L × Fin q) ⊕ (R × Fin q)) ⊕ (TNode q d ⊕ Fin p) where
  toFun
    | .l u c => .inl (.inl (u, c))
    | .r w c => .inl (.inr (w, c))
    | .t z => .inr (.inl z)
    | .pad i => .inr (.inr i)
  invFun
    | .inl (.inl (u, c)) => .l u c
    | .inl (.inr (w, c)) => .r w c
    | .inr (.inl z) => .t z
    | .inr (.inr i) => .pad i
  left_inv v := by cases v <;> rfl
  right_inv s := by rcases s with ((⟨_, _⟩ | ⟨_, _⟩) | (_ | _)) <;> rfl

lemma Vtx.card (L R : Type*) [Fintype L] [Fintype R] (q d p : ℕ) :
    Fintype.card (Vtx L R q d p) =
      Fintype.card L * q + Fintype.card R * q + Fintype.card (TNode q d) + p := by
  rw [Fintype.card_congr (Vtx.equivSum L R q d p)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

lemma TNode.card_le (q d : ℕ) : Fintype.card (TNode q d) ≤ (d + 1) * q := by
  refine (Fintype.card_subtype_le _).trans ?_
  simp

/-- For `n` nodes, the lower-bound graph with parameters `aOf k n`, `qOf k n`, `dOf n` padded to
exactly `n` vertices. -/
lemma exists_equiv_vtx (k : ℕ) (V : Type*) [Fintype V] :
    ∃ p, Nonempty (V ≃ Vtx (Fin (aOf k (Fintype.card V))) (Fin (aOf k (Fintype.card V)))
      (qOf k (Fintype.card V)) (dOf (Fintype.card V)) p) := by
  set n := Fintype.card V
  set a := aOf k n
  set q := qOf k n
  set d := dOf n
  have h1 := TNode.card_le q d
  have h2 := qOf_mul_le k n
  have hle : 2 * a * q + Fintype.card (TNode q d) ≤ n := by
    have : (d + 1) * q + 2 * a * q = q * (2 * a + d + 1) := by ring
    simp only [q, a, d] at *
    nlinarith
  refine ⟨n - (2 * a * q + Fintype.card (TNode q d)), ⟨Fintype.equivOfCardEq ?_⟩⟩
  rw [Vtx.card]
  simp only [Fintype.card_fin]
  have : 2 * a * q = a * q + a * q := by ring
  omega

/-! ### The gaps -/

open scoped ENNReal

/-- The directed gap: `α · 2q < 2kq` for `α < k`. -/
lemma gap_dir {k q : ℕ} {α : ℝ≥0∞} (hα : α < k) (hq : 0 < q) :
    α * (2 * (q : ℝ≥0∞)) < ((2 * k * q : ℕ) : ℝ≥0∞) := by
  have h : ((2 * k * q : ℕ) : ℝ≥0∞) = (k : ℝ≥0∞) * (2 * q) := by push_cast; ring
  rw [h, mul_comm α, mul_comm (k : ℝ≥0∞)]
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hq.ne'
  exact ENNReal.mul_lt_mul_right (mul_ne_zero two_ne_zero hq0)
    (ENNReal.mul_ne_top (by simp) (by simp)) hα

/-- The undirected gap: for `α < k` there is `M` with `α · (2(q-1) + 2Mq) < 2kMq`. -/
lemma gap_undir {k : ℕ} {α : ℝ≥0∞} (hα : α < k) : ∃ M : ℕ, 1 ≤ M ∧ ∀ q : ℕ, 0 < q →
    α * ((2 * (q - 1) + 2 * (M * q) : ℕ) : ℝ≥0∞) < ((2 * k * (M * q) : ℕ) : ℝ≥0∞) := by
  have hαt : α ≠ ⊤ := ne_top_of_lt hα
  set a := α.toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hak : a < k := by
    have := (ENNReal.toReal_lt_toReal hαt (by simp)).2 hα
    simpa using this
  refine ⟨⌈a / (k - a)⌉₊ + 1, by omega, fun q hq => ?_⟩
  set M := ⌈a / (k - a)⌉₊ + 1
  have hka : 0 < (k : ℝ) - a := by linarith
  have hM : a < M * ((k : ℝ) - a) := by
    have h1 : a / (k - a) ≤ ⌈a / (k - a)⌉₊ := Nat.le_ceil _
    have h2 : a / (k - a) < M := by simp only [M]; push_cast; linarith
    rwa [div_lt_iff₀ hka] at h2
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [← ENNReal.ofReal_toReal hαt, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul ha0, ENNReal.ofReal_lt_ofReal_iff (by
      have hk0 : (0 : ℝ) < k := by linarith
      have hM0 : (0 : ℝ) < M := by positivity
      push_cast; positivity)]
  have hsub : ((q - 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q 1
  push_cast
  have : a * (2 * ((q - 1 : ℕ) : ℝ) + 2 * (M * q)) ≤ a * (2 * q + 2 * (M * q)) := by
    gcongr
  nlinarith

end Podc.GirthApproxCongest
