import Papers.PODC2015.SynchronousCounting.Theorem1

/-!
# Theorem 1 of Lenzen–Rybicki–Suomela (PODC 2015), packaged as a statement about `Achievable`

The state of `B` is the state of `A` plus `a ∈ [C] ∪ {∞}` and one bit `d`, so
`S(B) ≤ S(A) + ⌈log₂ (C + 1)⌉ + 1` (the paper writes `=`, which holds for this bit-field encoding).
-/

namespace SynchronousCounting

open Podc.SyncCounting

/-- Theorem 1 (repaired: with the extra hypotheses `2f < n` and `3F < kn`). -/
theorem boost {n f c T S k F C : ℕ} (h : Achievable n f c T S) (hk : 3 ≤ k)
    (hF : F < (f + 1) * half k) (hC : 1 < C) (hc : boostTime k F ∣ c) (hn : 2 * f < n)
    (hN : 3 * F < k * n) :
    Achievable (k * n) F C (T + boostTime k F) (S + Nat.clog 2 (C + 1) + 1) := by
  obtain ⟨X, _, _, A, hX, hA⟩ := h
  have : NeZero C := ⟨by omega⟩
  have hB := theorem1 (C := C) A hA hk hF hc hn hN
  have hcard : Fintype.card (BState X C) ≤ 2 ^ (S + Nat.clog 2 (C + 1) + 1) := by
    have h1 : C + 1 ≤ 2 ^ Nat.clog 2 (C + 1) := Nat.le_pow_clog (by norm_num) _
    simp only [BState, Fintype.card_prod, Fintype.card_option, Fintype.card_fin,
      Fintype.card_bool, pow_add, pow_one]
    have := Nat.mul_le_mul hX h1
    nlinarith
  have := achievable_of_equiv _ hcard hB
  simpa using this

/-- With the paper's implicit assumption `f < n/3`, the hypothesis `3F < kn` of `boost` follows
from `F < (f+1)⌈k/2⌉` as soon as `n ≥ 2` (the paper claims it always follows; it fails for
`n = 1`, see `theorem1_as_stated_false`). -/
lemma three_mul_lt_of_paper {n f k F : ℕ} (hn : 3 * f < n) (hn2 : 2 ≤ n) (hk : 3 ≤ k)
    (hF : F < (f + 1) * half k) : 3 * F < k * n := by
  have hh : half k = (k + 1) / 2 := rfl
  have hm1 : 2 * half k ≤ k + 1 := by omega
  have hm2 : k ≤ 2 * half k := by omega
  have hmk : half k ≤ k := by omega
  have h1 : 3 * F + 3 ≤ 3 * ((f + 1) * half k) := by omega
  have h2 : 3 * ((f + 1) * half k) ≤ (n + 2) * half k := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
  have h3 : k * n = half k * n + (k - half k) * n := by
    rw [← add_mul, Nat.add_sub_cancel' hmk]
  have h4 : 2 * (k - half k) ≤ (k - half k) * n := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ hn2
  have h5 : (n + 2) * half k = half k * n + 2 * half k := by ring
  omega

/-- **Theorem 1** with the paper's hypotheses, plus `f < n/3` (implicit in the paper) and
`n ≥ 2` (needed: `theorem1_as_stated_false`). -/
theorem theorem1_paper {n f c T S k F C : ℕ} (h : Achievable n f c T S) (hn : 3 * f < n)
    (hn2 : 2 ≤ n) (hk : 3 ≤ k) (hF : F < (f + 1) * half k) (hC : 1 < C)
    (hc : boostTime k F ∣ c) :
    Achievable (k * n) F C (T + boostTime k F) (S + Nat.clog 2 (C + 1) + 1) :=
  boost h hk hF hC hc (by omega) (three_mul_lt_of_paper hn hn2 hk hF)

end SynchronousCounting
