import Papers.PODC2017.DeltaEdgeColoring.CliqueDecomposition

/-!
# The colour count of the star-partition scheme (Theorem 4.1, arithmetic part)

Section 4 colours the edge-connector (max degree `t`) with `2t - 1` colours and recurses `x` times on
the colour classes, whose max degree drops from `Δ` to `⌈Δ/t⌉`, …, `⌈Δ/t^x⌉`; the last classes are
coloured with `2⌈Δ/t^x⌉ - 1` colours. Theorem 4.1 claims `2^{x+1} Δ` colours for `t = Δ^{1/(x+1)}`.
We check the arithmetic for the integer choice `t = ⌊Δ^{1/(x+1)}⌋` (any `t ≥ 1` with
`t^{x+1} ≤ Δ`): `(2t-1)^x · (2⌈Δ/t^x⌉ - 1) ≤ 2^{x+1} Δ`, without the extra colour-reduction round
the paper uses for `x = 1`. The distributed algorithm of Section 4 itself is not formalized.
-/

namespace Podc.DeltaEdgeColoring

/-- Theorem 4.1, colour count: for `t ≥ 1` with `t^{x+1} ≤ Δ`,
`(2t-1)^x · (2⌈Δ/t^x⌉ - 1) ≤ 2^{x+1} Δ`. -/
theorem theorem_4_1_count {t Δ : ℕ} (x : ℕ) (ht : 1 ≤ t) (hΔ : t ^ (x + 1) ≤ Δ) :
    (2 * t - 1) ^ x * (2 * (Δ ⌈/⌉ t ^ x) - 1) ≤ 2 ^ (x + 1) * Δ := by
  rcases x with _ | y
  · simp only [pow_zero, ceilDiv_one, one_mul, zero_add, pow_one]
    omega
  set x := y + 1 with hx
  set T := t ^ x with hT
  have hT0 : 0 < T := pow_pos ht x
  set k := Δ ⌈/⌉ T
  -- `k T ≤ Δ + T - 1` and `T t ≤ Δ`
  have hk : k * T ≤ Δ + T - 1 := by
    rw [show k = (Δ + T - 1) / T from Nat.ceilDiv_eq_add_pred_div Δ T]
    exact Nat.div_mul_le_self _ _
  have hTt : T * t ≤ Δ := by rw [hT, ← pow_succ]; exact hΔ
  -- `(2k - 1) · T · t ≤ (2t + 1) Δ`
  have h1 : (2 * k - 1) * T * t ≤ (2 * t + 1) * Δ := by
    have : (2 * k - 1) * T ≤ 2 * Δ + T := by
      have : (2 * k - 1) * T = 2 * k * T - T := by rw [Nat.sub_mul, one_mul]
      have : 2 * k * T = 2 * (k * T) := by ring
      omega
    calc (2 * k - 1) * T * t ≤ (2 * Δ + T) * t := Nat.mul_le_mul_right _ this
      _ = 2 * t * Δ + T * t := by ring
      _ ≤ 2 * t * Δ + Δ := Nat.add_le_add_left hTt _
      _ = (2 * t + 1) * Δ := by ring
  -- `(2t - 1)^{y+1} (2t + 1) ≤ (2t)^{y+2}`
  have h2 : (2 * t - 1) ^ (y + 1) * (2 * t + 1) ≤ (2 * t) ^ (y + 1 + 1) := by
    have hA : (2 * t - 1) ^ y ≤ (2 * t) ^ y := Nat.pow_le_pow_left (Nat.sub_le _ _) y
    have hB : (2 * t - 1) * (2 * t + 1) ≤ 2 * t * (2 * t) := by
      have : 1 ≤ 2 * t := by omega
      zify [this]; nlinarith
    calc (2 * t - 1) ^ (y + 1) * (2 * t + 1)
        = (2 * t - 1) ^ y * ((2 * t - 1) * (2 * t + 1)) := by ring
      _ ≤ (2 * t) ^ y * (2 * t * (2 * t)) := Nat.mul_le_mul hA hB
      _ = (2 * t) ^ (y + 1 + 1) := by ring
  have hTt0 : 0 < T * t := Nat.mul_pos hT0 ht
  refine Nat.le_of_mul_le_mul_right ?_ hTt0
  calc (2 * t - 1) ^ (y + 1) * (2 * k - 1) * (T * t)
      = (2 * t - 1) ^ (y + 1) * ((2 * k - 1) * T * t) := by ring
    _ ≤ (2 * t - 1) ^ (y + 1) * ((2 * t + 1) * Δ) := Nat.mul_le_mul_left _ h1
    _ = (2 * t - 1) ^ (y + 1) * (2 * t + 1) * Δ := by ring
    _ ≤ (2 * t) ^ (y + 1 + 1) * Δ := Nat.mul_le_mul_right _ h2
    _ = 2 ^ (y + 1 + 1) * Δ * (T * t) := by rw [hT]; ring

/-- Theorem 4.1 for `x = 1` and `t = ⌊√Δ⌋`: `(2t-1)(2⌈Δ/t⌉-1) ≤ 4Δ` (the paper bounds it by
`4Δ + 1` and then reduces one colour). -/
theorem theorem_4_1_count_one {Δ : ℕ} (hΔ : 1 ≤ Δ) :
    (2 * Nat.sqrt Δ - 1) * (2 * (Δ ⌈/⌉ Nat.sqrt Δ) - 1) ≤ 4 * Δ := by
  have h := theorem_4_1_count (t := Nat.sqrt Δ) (Δ := Δ) 1 (Nat.sqrt_pos.2 hΔ)
    (by rw [pow_two]; exact Nat.sqrt_le Δ)
  simpa using h

end Podc.DeltaEdgeColoring
