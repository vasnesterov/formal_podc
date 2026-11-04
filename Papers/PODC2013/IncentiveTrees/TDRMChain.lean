import Mathlib

/-!
# Chain functions of TDRM and their inequalities

A participant with contribution `c` is represented by TDRM as a chain of `N = n + 1` nodes
(`n = ⌈c/μ⌉ - 1`): a head of contribution `ε = c - n μ ∈ (0, μ]` followed by `n` nodes of
contribution `μ`.  For such a chain (with discount `a`):

* `Gc c = ε aⁿ + μ g(n)`: the depth-weighted sum of the chain seen from its tail;
* `Hc c = ε + a μ g(n)`: the depth-weighted sum of the chain seen from its head;
* `Qc c = ε² + a μ ε g(n) + μ² s(n)`: the "inner" quadratic form `Σ_{w ≥ x} a^{d(w,x)} C(w) C(x)`;

where `g(n) = Σ_{i<n} aⁱ` and `s(n) = Σ_{k<n} g(k+1)`.  The inequalities below (`Qc_add`,
`Qc_superadd`, `Hc_add_le`, `Gc_add_le`, `Gc_subadd`) are the whole content of the
"optimal Sybil partition is an ε-chain" Lemmas 1–5 of the paper.
-/

namespace Podc.IncentiveTrees.Chain

open Finset

/-- `g(n) = Σ_{i<n} aⁱ`. -/
def g (a : ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, a ^ i

/-- `s(n) = Σ_{k<n} g(k+1)`; `μ² s(n)` is the inner form of a chain of `n` full nodes. -/
def s (a : ℝ) (n : ℕ) : ℝ := ∑ k ∈ range n, g a (k + 1)

section Geom

variable {a : ℝ}

theorem g_zero : g a 0 = 0 := by simp [g]

theorem g_add (n k : ℕ) : g a (n + k) = g a n + a ^ n * g a k := by
  simp [g, Finset.sum_range_add, pow_add, Finset.mul_sum]

theorem g_succ (n : ℕ) : g a (n + 1) = g a n + a ^ n := by
  simp [g, Finset.sum_range_succ]

theorem g_succ' (n : ℕ) : g a (n + 1) = 1 + a * g a n := by
  rw [add_comm n 1, g_add]; simp [g]

theorem one_sub_mul_g (n : ℕ) : (1 - a) * g a n = 1 - a ^ n := by
  induction n with
  | zero => simp [g]
  | succ n ih => rw [g_succ, mul_add, ih, pow_succ]; ring

theorem g_nonneg (ha : 0 ≤ a) (n : ℕ) : 0 ≤ g a n :=
  Finset.sum_nonneg fun i _ => pow_nonneg ha i

theorem s_succ (n : ℕ) : s a (n + 1) = s a n + g a (n + 1) := by
  simp [s, Finset.sum_range_succ]

theorem g_one : g a 1 = 1 := by simp [g]

theorem s_one : s a 1 = 1 := by simp [s, g]

theorem g_comm (n k : ℕ) : g a n + a ^ n * g a k = g a k + a ^ k * g a n := by
  rw [← g_add, ← g_add, add_comm]

theorem s_add (n k : ℕ) : s a (n + k) = s a n + s a k + a * g a n * g a k := by
  induction k with
  | zero => simp [s, g]
  | succ k ih =>
    rw [← add_assoc, s_succ, ih, s_succ, g_succ (n + k), g_add n k, g_succ k, pow_add]
    linear_combination (g_comm (a := a) n k) + a ^ k * one_sub_mul_g (a := a) n

theorem s_nonneg (ha : 0 ≤ a) (n : ℕ) : 0 ≤ s a n :=
  Finset.sum_nonneg fun k _ => g_nonneg ha (k + 1)

end Geom

/-! ## Closed forms in terms of a decomposition `c = n μ + ε` -/

section Forms

variable (a μ : ℝ)

/-- Tail-seen weighted sum of the chain `[ε, μ, …, μ]` (`n` full nodes). -/
def Gf (n : ℕ) (ε : ℝ) : ℝ := ε * a ^ n + μ * g a n

/-- Head-seen weighted sum of the chain `[ε, μ, …, μ]`. -/
def Hf (n : ℕ) (ε : ℝ) : ℝ := ε + a * μ * g a n

/-- Inner quadratic form of the chain `[ε, μ, …, μ]`. -/
def Qf (n : ℕ) (ε : ℝ) : ℝ := ε ^ 2 + a * μ * ε * g a n + μ ^ 2 * s a n

/-- Number of full nodes below the head: `N_u - 1 = ⌈c/μ⌉ - 1`. -/
noncomputable def nOf (c : ℝ) : ℕ := ⌈c / μ⌉₊ - 1

/-- Contribution of the head node, `c - (N_u - 1) μ`. -/
noncomputable def headOf (c : ℝ) : ℝ := c - nOf μ c * μ

noncomputable def Gc (c : ℝ) : ℝ := Gf a μ (nOf μ c) (headOf μ c)
noncomputable def Hc (c : ℝ) : ℝ := Hf a μ (nOf μ c) (headOf μ c)
noncomputable def Qc (c : ℝ) : ℝ := Qf a μ (nOf μ c) (headOf μ c)

end Forms

section Decomp

variable {a μ : ℝ}

theorem decomp (μ c : ℝ) : c = nOf μ c * μ + headOf μ c := by simp [headOf]

theorem headOf_le (hμ : 0 < μ) (c : ℝ) (_hc : 0 ≤ c) : headOf μ c ≤ μ := by
  unfold headOf nOf
  rcases Nat.eq_zero_or_pos ⌈c / μ⌉₊ with h | h
  · rw [h]
    have : c / μ ≤ 0 := Nat.ceil_eq_zero.mp h
    have : c ≤ 0 := by rwa [div_le_iff₀ hμ, zero_mul] at this
    simp; linarith
  · have h1 : c / μ ≤ ⌈c / μ⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ hμ] at h1
    rw [Nat.cast_sub (by omega)]
    push_cast
    nlinarith

theorem headOf_nonneg (hμ : 0 < μ) (c : ℝ) (hc : 0 ≤ c) : 0 ≤ headOf μ c := by
  unfold headOf nOf
  rcases Nat.eq_zero_or_pos ⌈c / μ⌉₊ with h | h
  · rw [h]; simpa using hc
  · have h1 : (⌈c / μ⌉₊ : ℝ) < c / μ + 1 := Nat.ceil_lt_add_one (by positivity)
    rw [Nat.cast_sub (by omega)]
    push_cast
    have : ((⌈c / μ⌉₊ : ℝ) - 1) * μ < c / μ * μ := by nlinarith
    rw [div_mul_cancel₀ _ hμ.ne'] at this
    linarith

theorem headOf_pos (hμ : 0 < μ) (c : ℝ) (hc : 0 < c) : 0 < headOf μ c := by
  unfold headOf nOf
  have hpos : 0 < ⌈c / μ⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have h1 : ((⌈c / μ⌉₊ - 1 : ℕ) : ℝ) < c / μ := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ c / μ by positivity)
    linarith
  rw [lt_div_iff₀ hμ] at h1
  linarith

/-- Representation independence: any decomposition `c = n μ + ε` with `0 ≤ ε ≤ μ` can be used
to compute `Gc` and `Qc`. -/
theorem nOf_headOf_of (hμ : 0 < μ) (n : ℕ) (ε : ℝ) (hε : 0 < ε) (hεμ : ε ≤ μ) :
    nOf μ (n * μ + ε) = n ∧ headOf μ (n * μ + ε) = ε := by
  have hn : nOf μ (n * μ + ε) = n := by
    unfold nOf
    have : ⌈(n * μ + ε) / μ⌉₊ = n + 1 := by
      rw [Nat.ceil_eq_iff (by omega)]
      push_cast
      constructor
      · rw [lt_div_iff₀ hμ]; simp; linarith
      · rw [div_le_iff₀ hμ]; linarith
    omega
  refine ⟨hn, ?_⟩
  simp [headOf, hn]

theorem Gc_eq (hμ : 0 < μ) (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hεμ : ε ≤ μ) :
    Gc a μ (n * μ + ε) = Gf a μ n ε := by
  rcases hε.lt_or_eq with hε | rfl
  · obtain ⟨h1, h2⟩ := nOf_headOf_of hμ n ε hε hεμ
    simp [Gc, h1, h2]
  · rcases n with _ | m
    · simp [Gc, Gf, nOf, headOf, g]
    · have : ((m + 1 : ℕ) : ℝ) * μ + 0 = m * μ + μ := by push_cast; ring
      rw [this]
      obtain ⟨h1, h2⟩ := nOf_headOf_of hμ m μ hμ le_rfl
      simp only [Gc, h1, h2, Gf, g_succ]
      ring

theorem Qc_eq (hμ : 0 < μ) (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hεμ : ε ≤ μ) :
    Qc a μ (n * μ + ε) = Qf a μ n ε := by
  rcases hε.lt_or_eq with hε | rfl
  · obtain ⟨h1, h2⟩ := nOf_headOf_of hμ n ε hε hεμ
    simp [Qc, h1, h2]
  · rcases n with _ | m
    · simp [Qc, Qf, nOf, headOf, g, s]
    · have : ((m + 1 : ℕ) : ℝ) * μ + 0 = m * μ + μ := by push_cast; ring
      rw [this]
      obtain ⟨h1, h2⟩ := nOf_headOf_of hμ m μ hμ le_rfl
      simp only [Qc, h1, h2, Qf, s_succ, g_succ']
      ring

end Decomp

/-! ## The inequalities -/

section Ineq

variable {a μ : ℝ}

/-- Common case split: both decompositions and their sum. -/
private theorem two_cases (hμ : 0 < μ) (c m : ℝ) (hc : 0 ≤ c) (hm : 0 ≤ m) (P : Prop)
    (h₁ : ∀ (n k : ℕ) (ε δ : ℝ), 0 ≤ ε → ε ≤ μ → 0 ≤ δ → δ ≤ μ → ε + δ ≤ μ →
      m = k * μ + δ → c + m = ((n + k : ℕ) : ℝ) * μ + (ε + δ) →
      nOf μ c = n → headOf μ c = ε → P)
    (h₂ : ∀ (n k : ℕ) (ε δ : ℝ), 0 ≤ ε → ε ≤ μ → 0 ≤ δ → δ ≤ μ → μ < ε + δ →
      m = k * μ + δ → c + m = ((n + k + 1 : ℕ) : ℝ) * μ + (ε + δ - μ) →
      nOf μ c = n → headOf μ c = ε → P) : P := by
  have hc' := decomp μ c
  have hm' := decomp μ m
  have e0 := headOf_nonneg hμ c hc
  have e1 := headOf_le hμ c hc
  have d0 := headOf_nonneg hμ m hm
  have d1 := headOf_le hμ m hm
  rcases le_or_gt (headOf μ c + headOf μ m) μ with h | h
  · exact h₁ _ _ _ _ e0 e1 d0 d1 h hm' (by push_cast; linarith) rfl rfl
  · exact h₂ _ _ _ _ e0 e1 d0 d1 h hm' (by push_cast; linarith) rfl rfl

variable (ha : 0 ≤ a) (ha1 : a < 1) (hμ : 0 < μ)
include ha hμ

theorem Gc_nonneg (c : ℝ) (hc : 0 ≤ c) : 0 ≤ Gc a μ c := by
  have := headOf_nonneg hμ c hc
  have := g_nonneg ha (nOf μ c)
  unfold Gc Gf; positivity

theorem Hc_nonneg (c : ℝ) (hc : 0 ≤ c) : 0 ≤ Hc a μ c := by
  have := headOf_nonneg hμ c hc
  have := g_nonneg ha (nOf μ c)
  unfold Hc Hf; positivity

theorem Qc_nonneg (c : ℝ) (hc : 0 ≤ c) : 0 ≤ Qc a μ c := by
  have := headOf_nonneg hμ c hc
  have := g_nonneg ha (nOf μ c)
  have := s_nonneg ha (nOf μ c)
  unfold Qc Qf; positivity

theorem Gc_pos (ha0 : 0 < a) (c : ℝ) (hc : 0 < c) : 0 < Gc a μ c := by
  have := headOf_pos hμ c hc
  have := g_nonneg ha (nOf μ c)
  unfold Gc Gf; positivity

theorem Hc_pos (c : ℝ) (hc : 0 < c) : 0 < Hc a μ c := by
  have := headOf_pos hμ c hc
  have := g_nonneg ha (nOf μ c)
  unfold Hc Hf; positivity

theorem Qc_pos (c : ℝ) (hc : 0 < c) : 0 < Qc a μ c := by
  have := headOf_pos hμ c hc
  have := g_nonneg ha (nOf μ c)
  have := s_nonneg ha (nOf μ c)
  unfold Qc Qf; positivity

include ha1

/-- `(1 - a) G(c) ≤ μ (1 - a^{N(c)})`. -/
theorem Gc_le (c : ℝ) (hc : 0 ≤ c) : (1 - a) * Gc a μ c ≤ μ * (1 - a ^ (nOf μ c + 1)) := by
  have e1 := headOf_le hμ c hc
  have hg := one_sub_mul_g (a := a) (nOf μ c)
  have hp := pow_nonneg ha (nOf μ c)
  unfold Gc Gf
  rw [pow_succ]
  nlinarith [mul_le_mul_of_nonneg_left e1 (mul_nonneg hp (sub_nonneg.2 ha1.le))]

theorem Gc_le' (c : ℝ) (hc : 0 ≤ c) : (1 - a) * Gc a μ c ≤ μ := by
  have := Gc_le ha ha1 hμ c hc
  have := pow_nonneg ha (nOf μ c + 1)
  nlinarith

/-- Budget of one chain: `(1 - a) Q(c) + a μ H(c) ≤ μ c`. -/
theorem chain_budget (c : ℝ) (hc : 0 ≤ c) : (1 - a) * Qc a μ c + a * μ * Hc a μ c ≤ μ * c := by
  have e0 := headOf_nonneg hμ c hc
  have e1 := headOf_le hμ c hc
  have hcd : c = nOf μ c * μ + headOf μ c := decomp μ c
  unfold Qc Hc Qf Hf
  generalize nOf μ c = n at *
  generalize headOf μ c = ε at *
  subst hcd
  have hs : (1 - a) * s a n = n - a * g a n := by
    clear hc
    induction n with
    | zero => simp [s, g]
    | succ n ih =>
      rw [s_succ, mul_add, ih, g_succ']
      push_cast
      ring
  have hgn := g_nonneg ha n
  have key : μ * (n * μ + ε) - ((1 - a) * (ε ^ 2 + a * μ * ε * g a n + μ ^ 2 * s a n) +
      a * μ * (ε + a * μ * g a n)) = (1 - a) * (μ - ε) * (ε + a * μ * g a n) := by
    linear_combination (-μ ^ 2) * hs
  have : 0 ≤ (1 - a) * (μ - ε) * (ε + a * μ * g a n) := by
    have := sub_nonneg.2 ha1.le
    have := sub_nonneg.2 e1
    positivity
  linarith

/-- F6: `G(c) + a^{N(c)} G(m) ≤ G(c + m)` (concatenating a chain above another). -/
theorem Gc_add_le (c m : ℝ) (hc : 0 ≤ c) (hm : 0 ≤ m) :
    Gc a μ c + a ^ (nOf μ c + 1) * Gc a μ m ≤ Gc a μ (c + m) := by
  apply two_cases hμ c m hc hm
  · intro n k ε δ e0 e1 d0 d1 hs hmd hsum hn he
    rw [hsum, Gc_eq hμ _ _ (by linarith) hs, hmd, Gc_eq hμ _ _ d0 d1]
    unfold Gc Gf; rw [hn, he]
    simp only [g_add, pow_add, pow_one]
    have Rk := one_sub_mul_g (a := a) k
    have hA := pow_nonneg ha n
    have hB := pow_nonneg ha k
    have hB1 : a ^ k ≤ 1 := pow_le_one₀ ha ha1.le
    have h1 : 0 ≤ a ^ n * (1 - a ^ k) * (μ - ε) := by
      have := sub_nonneg.2 hB1; have := sub_nonneg.2 e1; positivity
    have h2 : 0 ≤ δ * a ^ n * a ^ k * (1 - a) := by have := sub_nonneg.2 ha1.le; positivity
    linear_combination h1 + h2 - (μ * a ^ n) * Rk
  · intro n k ε δ e0 e1 d0 d1 hs hmd hsum hn he
    rw [hsum, Gc_eq hμ _ _ (by linarith) (by linarith), hmd, Gc_eq hμ _ _ d0 d1]
    unfold Gc Gf; rw [hn, he]
    simp only [g_add, pow_add, pow_one, g_one]
    have Rk := one_sub_mul_g (a := a) k
    have hA := pow_nonneg ha n
    have hB := pow_nonneg ha k
    have hB1 : a * a ^ k ≤ 1 := by
      rw [← pow_succ']; exact pow_le_one₀ ha ha1.le
    have h1 : 0 ≤ a ^ n * (1 - a * a ^ k) * (μ - ε) := by
      have := sub_nonneg.2 hB1; have := sub_nonneg.2 e1; positivity
    linear_combination h1 - (μ * a ^ n) * Rk

/-- F3: `H(c) + a^{N(c)} G(m) ≤ G(c + m)`. -/
theorem Hc_add_le (c m : ℝ) (hc : 0 ≤ c) (hm : 0 ≤ m) :
    Hc a μ c + a ^ (nOf μ c + 1) * Gc a μ m ≤ Gc a μ (c + m) := by
  apply two_cases hμ c m hc hm
  · intro n k ε δ e0 e1 d0 d1 hs hmd hsum hn he
    rw [hsum, Gc_eq hμ _ _ (by linarith) hs, hmd, Gc_eq hμ _ _ d0 d1]
    unfold Hc Hf Gf; rw [hn, he]
    simp only [g_add, pow_add, pow_one]
    have Rn := one_sub_mul_g (a := a) n
    have Rk := one_sub_mul_g (a := a) k
    have hA := pow_nonneg ha n
    have hB := pow_nonneg ha k
    have hAB1 : a ^ n * a ^ k ≤ 1 := by rw [← pow_add]; exact pow_le_one₀ ha ha1.le
    have h1 : 0 ≤ (μ - ε) * (1 - a ^ n * a ^ k) := by
      have := sub_nonneg.2 hAB1; have := sub_nonneg.2 e1; positivity
    have h2 : 0 ≤ δ * a ^ n * a ^ k * (1 - a) := by have := sub_nonneg.2 ha1.le; positivity
    linear_combination h1 + h2 - μ * Rn - (μ * a ^ n) * Rk
  · intro n k ε δ e0 e1 d0 d1 hs hmd hsum hn he
    rw [hsum, Gc_eq hμ _ _ (by linarith) (by linarith), hmd, Gc_eq hμ _ _ d0 d1]
    unfold Hc Hf Gf; rw [hn, he]
    simp only [g_add, pow_add, pow_one, g_one]
    have Rn := one_sub_mul_g (a := a) n
    have Rk := one_sub_mul_g (a := a) k
    have hA := pow_nonneg ha n
    have hB := pow_nonneg ha k
    have hAB1 : a ^ n * a ^ k * a ≤ 1 := by
      rw [← pow_add, ← pow_succ]; exact pow_le_one₀ ha ha1.le
    have h1 : 0 ≤ (μ - ε) * (1 - a ^ n * a ^ k * a) := by
      have := sub_nonneg.2 hAB1; have := sub_nonneg.2 e1; positivity
    linear_combination h1 - μ * Rn - (μ * a ^ n) * Rk

theorem Gc_mono (c m : ℝ) (hc : 0 ≤ c) (hcm : c ≤ m) : Gc a μ c ≤ Gc a μ m := by
  have h1 := Gc_add_le ha ha1 hμ c (m - c) hc (by linarith)
  have h2 := Gc_nonneg ha hμ (m - c) (by linarith)
  have h3 := pow_nonneg ha (nOf μ c + 1)
  rw [add_sub_cancel] at h1
  nlinarith [mul_nonneg h3 h2]

/-- F5: `Q(c) + Q(m) + a G(c) G(m) ≤ Q(c + m)` (concatenating two chains). -/
theorem Qc_add (c m : ℝ) (hc : 0 ≤ c) (hm : 0 ≤ m) :
    Qc a μ c + Qc a μ m + a * Gc a μ c * Gc a μ m ≤ Qc a μ (c + m) := by
  apply two_cases hμ c m hc hm
  · intro n k ε δ e0 e1 d0 d1 hs hmd hsum hn he
    rw [hsum, Qc_eq hμ _ _ (by linarith) hs, hmd, Qc_eq hμ _ _ d0 d1, Gc_eq hμ _ _ d0 d1]
    unfold Qc Gc Qf Gf; rw [hn, he]
    have Rnk := g_comm (a := a) n k
    simp only [s_add, g_add]
    have hA := pow_nonneg ha n
    have hB := pow_nonneg ha k
    have hAB1 : a * (a ^ n * a ^ k) ≤ 1 := by
      rw [← pow_add, ← pow_succ']; exact pow_le_one₀ ha ha1.le
    have h1 : 0 ≤ ε * δ * (2 - a * (a ^ n * a ^ k)) := by
      have : 0 ≤ 2 - a * (a ^ n * a ^ k) := by linarith
      positivity
    linear_combination h1 - (a * μ * δ) * Rnk
  · intro n k ε δ e0 e1 d0 d1 hs hmd hsum hn he
    rw [hsum, Qc_eq hμ _ _ (by linarith) (by linarith), hmd, Qc_eq hμ _ _ d0 d1,
      Gc_eq hμ _ _ d0 d1]
    unfold Qc Gc Qf Gf; rw [hn, he]
    have Rnk := g_comm (a := a) n k
    simp only [s_add, g_add, pow_add, g_one, s_one]
    have hA := pow_nonneg ha n
    have hB := pow_nonneg ha k
    have hAB1 : a * (a ^ n * a ^ k) ≤ 1 := by
      rw [← pow_add, ← pow_succ']; exact pow_le_one₀ ha ha1.le
    have h1 : 0 ≤ (2 - a * (a ^ n * a ^ k)) * (μ - ε) * (μ - δ) := by
      have : 0 ≤ 2 - a * (a ^ n * a ^ k) := by linarith
      have := sub_nonneg.2 e1; have := sub_nonneg.2 d1
      positivity
    linear_combination h1 - (a * μ * δ) * Rnk

/-- `G` is subadditive, and the subadditivity gap is controlled by `G(c) G(m)`:
`μ (G(c) + G(m) - G(c + m)) ≤ (1 - a) G(c) G(m)`. -/
theorem Gc_subadd (c m : ℝ) (hc : 0 ≤ c) (hm : 0 ≤ m) :
    0 ≤ Gc a μ c + Gc a μ m - Gc a μ (c + m) ∧
      μ * (Gc a μ c + Gc a μ m - Gc a μ (c + m)) ≤ (1 - a) * (Gc a μ c * Gc a μ m) := by
  apply two_cases hμ c m hc hm
  · intro n k ε δ e0 e1 d0 d1 hs hmd hsum hn he
    rw [hsum, Gc_eq hμ _ _ (by linarith) hs, hmd, Gc_eq hμ _ _ d0 d1]
    unfold Gc Gf; rw [hn, he]
    have Rnk := g_comm (a := a) n k
    have Rn := one_sub_mul_g (a := a) n
    have Rk := one_sub_mul_g (a := a) k
    simp only [g_add, pow_add]
    have hA := pow_nonneg ha n
    have hB := pow_nonneg ha k
    have hA1 := sub_nonneg.2 (pow_le_one₀ (n := n) ha ha1.le)
    have hB1 := sub_nonneg.2 (pow_le_one₀ (n := k) ha ha1.le)
    have hgk0 := g_nonneg ha k
    have ha' := sub_nonneg.2 ha1.le
    constructor
    · have h1 : 0 ≤ ε * a ^ n * (1 - a ^ k) := by positivity
      have h2 : 0 ≤ δ * a ^ k * (1 - a ^ n) := by positivity
      have h3 : 0 ≤ μ * g a k * (1 - a ^ n) := by positivity
      linear_combination h1 + h2 + h3
    · have h1 : 0 ≤ (1 - a) * ε * δ * a ^ n * a ^ k := by positivity
      linear_combination h1 - (ε * a ^ n * μ) * Rk - (μ * δ * a ^ k) * Rn -
        (μ ^ 2 * g a n) * Rk - μ ^ 2 * Rnk
  · intro n k ε δ e0 e1 d0 d1 hs hmd hsum hn he
    rw [hsum, Gc_eq hμ _ _ (by linarith) (by linarith), hmd, Gc_eq hμ _ _ d0 d1]
    unfold Gc Gf; rw [hn, he]
    have Rnk := g_comm (a := a) n k
    have Rn := one_sub_mul_g (a := a) n
    have Rk := one_sub_mul_g (a := a) k
    simp only [g_add, pow_add, pow_one, g_one]
    have hA := pow_nonneg ha n
    have hB := pow_nonneg ha k
    have hA1 := sub_nonneg.2 (pow_le_one₀ (n := n) ha ha1.le)
    have hB1 := sub_nonneg.2 (pow_le_one₀ (n := k) ha ha1.le)
    have hgk0 := g_nonneg ha k
    have ha' := sub_nonneg.2 ha1.le
    have hs' : 0 ≤ ε + δ - μ := by linarith
    constructor
    · have h1 : 0 ≤ ε * a ^ n * (1 - a ^ k) := by positivity
      have h2 : 0 ≤ δ * a ^ k * (1 - a ^ n) := by positivity
      have h3 : 0 ≤ μ * g a k * (1 - a ^ n) := by positivity
      have h4 : 0 ≤ a ^ n * a ^ k * (1 - a) * (ε + δ - μ) := by positivity
      linear_combination h1 + h2 + h3 + h4
    · have h1 : 0 ≤ (1 - a) * a ^ n * a ^ k * (μ - ε) * (μ - δ) := by
        have := sub_nonneg.2 e1; have := sub_nonneg.2 d1; positivity
      linear_combination h1 - (ε * a ^ n * μ) * Rk - (μ * δ * a ^ k) * Rn -
        (μ ^ 2 * g a n) * Rk - μ ^ 2 * Rnk

/-- F7: for `0 ≤ α ≤ μ / (1 - a)`, `x ↦ Q(x) + a α G(x)` is superadditive. -/
theorem Qc_superadd (α : ℝ) (hαμ : (1 - a) * α ≤ μ) (c m : ℝ) (hc : 0 ≤ c)
    (hm : 0 ≤ m) :
    Qc a μ c + a * α * Gc a μ c + (Qc a μ m + a * α * Gc a μ m) ≤
      Qc a μ (c + m) + a * α * Gc a μ (c + m) := by
  have h1 := Qc_add ha ha1 hμ c m hc hm
  obtain ⟨h2, h3⟩ := Gc_subadd ha ha1 hμ c m hc hm
  set K := Gc a μ c + Gc a μ m - Gc a μ (c + m)
  have h4 : (1 - a) * (α * K) ≤ (1 - a) * (Gc a μ c * Gc a μ m) := by
    have : (1 - a) * α * K ≤ μ * K := mul_le_mul_of_nonneg_right hαμ h2
    linarith
  have h5 : α * K ≤ Gc a μ c * Gc a μ m := le_of_mul_le_mul_left h4 (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h5 ha]

end Ineq

end Podc.IncentiveTrees.Chain
