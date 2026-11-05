import Mathlib

/-!
# The counting recursion of Section 5.2 and Claim 5.5

`f N 0 = N`, `f N (k+1) = f N k - ⌊f N k / (N - k)⌋ + 1` (the paper's `f`, for `n = N`
processes). Lemma 5.4(e) gives `m_k ≥ f N k` for the number `m_k` of groups after round `k`;
Claim 5.5 gives a closed form of `f` when `N = 2^t`, in particular `f (2^t) (2^t - 4) = 4 (t - 1)`.
-/

namespace Podc.LeaderElectionSpaceLB

/-- The paper's function `f` (Section 5.2) for `N` processes. -/
def f (N : ℕ) : ℕ → ℕ
  | 0 => N
  | k + 1 => f N k - f N k / (N - k) + 1

@[simp] lemma f_zero (N : ℕ) : f N 0 = N := rfl

lemma f_succ (N k : ℕ) : f N (k + 1) = f N k - f N k / (N - k) + 1 := rfl

lemma succ_div_le (a M : ℕ) : (a + 1) / M ≤ a / M + 1 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · calc (a + 1) / M ≤ (a + M) / M := Nat.div_le_div_right (by omega)
      _ = a / M + 1 := Nat.add_div_right a hM

lemma add_div_le (x d M : ℕ) : (x + d) / M ≤ x / M + d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have := succ_div_le (x + d) M
    rw [← add_assoc]; omega

/-- `x ↦ x - ⌊x / M⌋` is monotone. -/
lemma sub_div_mono {x y : ℕ} (M : ℕ) (h : x ≤ y) : x - x / M ≤ y - y / M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 := add_div_le x d M
  have h2 := Nat.div_le_self x M
  have h3 := Nat.div_le_self (x + d) M
  omega

/-- The update rule of Lemma 5.4(e) is monotone in the number of groups. -/
lemma step_mono {x y : ℕ} (M : ℕ) (h : x ≤ y) : x - x / M + 1 ≤ y - y / M + 1 := by
  have := sub_div_mono M h; omega

lemma sub_le_f {N : ℕ} : ∀ k, k ≤ N → N - k ≤ f N k
  | 0, _ => by simp
  | k + 1, hk => by
    have ih := sub_le_f (N := N) k (by omega)
    rw [f_succ]
    have := step_mono (N - k) ih
    have h2 : (N - k) / (N - k) = 1 := Nat.div_self (by omega)
    omega

/-- `f` is nonincreasing on `0, …, N`. -/
lemma f_succ_le {N k : ℕ} (hk : k + 1 ≤ N) : f N (k + 1) ≤ f N k := by
  rw [f_succ]
  have h := sub_le_f k (by omega : k ≤ N)
  have : 1 ≤ f N k / (N - k) := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  omega

/-- The division step in Claim 5.5(b): `⌊((s+1) a - s d) / (a - d)⌋ = s + 1` for `2 d < a`. -/
lemma div_step {s a d : ℕ} (hd : 2 * d < a) : ((s + 1) * a - s * d) / (a - d) = s + 1 := by
  apply Nat.div_eq_of_lt_le
  · -- (s+1)(a-d) ≤ (s+1)a - sd
    have : (s + 1) * (a - d) + d = (s + 1) * a - s * d := by
      obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (by omega : d ≤ a)
      simp only [Nat.add_sub_cancel_left]
      have : (s + 1) * (d + e) - s * d = d + (s + 1) * e := by
        rw [Nat.sub_eq_iff_eq_add (by nlinarith)]; ring
      rw [this]; ring
    omega
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (by omega : d ≤ a)
    simp only [Nat.add_sub_cancel_left]
    have : (s + 1) * (d + e) - s * d = d + (s + 1) * e := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]; ring
    rw [this]
    nlinarith

/-- One step of Claim 5.5: inside an interval `I(s)` the value of `f` drops by exactly `s`. -/
lemma claim55_step {N s a d : ℕ} (ha : a ≤ N) (hd : 2 * d < a)
    (h : f N (N - a + d) = (s + 1) * a - s * d) :
    f N (N - a + d) / (N - (N - a + d)) = s + 1 ∧
      f N (N - a + (d + 1)) = (s + 1) * a - s * (d + 1) := by
  have hNk : N - (N - a + d) = a - d := by omega
  have hdiv : f N (N - a + d) / (N - (N - a + d)) = s + 1 := by rw [h, hNk]; exact div_step hd
  refine ⟨hdiv, ?_⟩
  rw [show N - a + (d + 1) = (N - a + d) + 1 by omega, f_succ, hdiv, h]
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (by omega : d ≤ a)
  have h1 : (s + 1) * (d + e) - s * d = d + (s + 1) * e := by
    rw [Nat.sub_eq_iff_eq_add (by nlinarith)]; ring
  have h2 : (s + 1) * (d + e) - s * (d + 1) = d + (s + 1) * e - s := by
    rw [mul_add s d 1, mul_one, ← Nat.sub_sub, h1]
  rw [h1, h2]
  have : 1 ≤ e := by omega
  have : s + 1 ≤ (s + 1) * e := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- **Claim 5.5 (a)**, closed form of `f` for `N = 2^t`: for `s < t` and
`k = N - N/2^s + d` with `0 ≤ d ≤ N/2^(s+1)` (i.e. `k ∈ I(s)`, plus the first point of
`I(s+1)`), `f(k) = N (s+1)/2^s - s (k - N + N/2^s)`. -/
theorem claim_5_5_a (t : ℕ) : ∀ s, s < t → ∀ d, d ≤ 2 ^ (t - s - 1) →
    f (2 ^ t) (2 ^ t - 2 ^ (t - s) + d) = (s + 1) * 2 ^ (t - s) - s * d := by
  intro s
  induction s with
  | zero =>
    intro ht d hd
    induction d with
    | zero => simp
    | succ d ih =>
      have h2 : 2 ^ t = 2 * 2 ^ (t - 0 - 1) := by
        rw [← pow_succ']; congr 1; omega
      have := (claim55_step (N := 2 ^ t) (s := 0) (a := 2 ^ (t - 0)) (d := d) le_rfl
        (by simp only [Nat.sub_zero] at h2 hd ⊢; omega) (ih (by omega))).2
      exact this
  | succ s ih =>
    intro ht d hd
    have hpow : 2 ^ (t - s) = 2 * 2 ^ (t - (s + 1)) := by
      rw [← pow_succ']; congr 1; omega
    have hpow' : 2 ^ (t - s - 1) = 2 ^ (t - (s + 1)) := by congr 1
    have hle : 2 ^ (t - s) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    induction d with
    | zero =>
      have := ih (by omega) (2 ^ (t - s - 1)) le_rfl
      rw [hpow', hpow] at this
      rw [hpow] at hle
      have hk : 2 ^ t - 2 * 2 ^ (t - (s + 1)) + 2 ^ (t - (s + 1)) =
          2 ^ t - 2 ^ (t - (s + 1)) + 0 := by omega
      rw [hk] at this
      rw [this]
      simp only [mul_zero, Nat.sub_zero]
      have : (s + 1) * (2 * 2 ^ (t - (s + 1))) = (s + 1) * 2 ^ (t - (s + 1)) +
          (s + 1) * 2 ^ (t - (s + 1)) := by ring
      rw [this, show (s + 1 + 1) * 2 ^ (t - (s + 1)) = (s + 1) * 2 ^ (t - (s + 1)) +
          2 ^ (t - (s + 1)) by ring]
      have : s * 2 ^ (t - (s + 1)) ≤ (s + 1) * 2 ^ (t - (s + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      have : (s + 1) * 2 ^ (t - (s + 1)) = s * 2 ^ (t - (s + 1)) + 2 ^ (t - (s + 1)) := by ring
      omega
    | succ d ihd =>
      have hpow2 : 2 ^ (t - (s + 1)) = 2 * 2 ^ (t - (s + 1) - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hle' : 2 ^ (t - (s + 1)) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact (claim55_step hle' (by omega) (ihd (by omega))).2

/-- **Claim 5.5 (b)**: for `k ∈ I(s)`, `δ(k+1) = ⌊f(k)/(n-k)⌋ - 1 = s`. -/
theorem claim_5_5_b (t s d : ℕ) (hs : s < t) (hd : d < 2 ^ (t - s - 1)) :
    f (2 ^ t) (2 ^ t - 2 ^ (t - s) + d) / (2 ^ t - (2 ^ t - 2 ^ (t - s) + d)) - 1 = s := by
  have hpow : 2 ^ (t - s) = 2 * 2 ^ (t - s - 1) := by rw [← pow_succ']; congr 1; omega
  have hle : 2 ^ (t - s) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [(claim55_step hle (by omega) (claim_5_5_a t s hs d hd.le)).1]
  simp

/-- The value used in the proof of Theorem 5.1: `f(n - 4) = 4 (log n - 1)` for `n = 2^t ≥ 4`. -/
theorem f_pow_sub_four (t : ℕ) (ht : 2 ≤ t) : f (2 ^ t) (2 ^ t - 4) = 4 * (t - 1) := by
  have := claim_5_5_a t (t - 2) (by omega) 0 (Nat.zero_le _)
  rw [show t - (t - 2) = 2 by omega] at this
  simp only [mul_zero, Nat.sub_zero, add_zero] at this
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at this
  rw [this, show t - 2 + 1 = t - 1 by omega, mul_comm]

end Podc.LeaderElectionSpaceLB
