import Papers.PODC2017.NoisyRadioBroadcast.Lemma15
import Papers.PODC2017.NoisyRadioBroadcast.StarCoding
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Theorem 17: a `Θ(log n)` coding gap on the star with receiver faults
-/

namespace Podc.NoisyRadioBroadcast

open Filter
open scoped ENNReal

/-- **Theorem 17** of the paper: with receiver faults of constant probability `p ∈ (0, 1)`, the
coding gap `τ^NC(star n) / τ^R(star n)` of the star with `n` leaves (adaptive routing; messages and
packets from finite fields `F k` with `|F k| ≥ k²`) is `Θ(log n)`. In particular the shared topology
gap (Definition 2) is `Ω(log n)`, witnessed by the star. -/
theorem theorem17 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (F : ℕ → Type) [∀ k, Field (F k)] [∀ k, Fintype (F k)] [∀ k, DecidableEq (F k)]
    (hF : ∀ k, k ^ 2 ≤ Fintype.card (F k)) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ENNReal.ofReal (c₁ * Real.log n) ≤
          codingThroughput (star n) none .receiver p F /
            routingThroughput (star n) none .receiver p ∧
        codingThroughput (star n) none .receiver p F /
            routingThroughput (star n) none .receiver p ≤ ENNReal.ofReal (c₂ * Real.log n) := by
  obtain ⟨d₁, hd₁, d₂, hd₂, n₀, h15⟩ := lemma15 hp0 hp1
  have hq : 0 < 1 - p := by linarith
  refine ⟨(1 - p) / 8 / d₂, by positivity, 2 / d₁, by positivity, max n₀ 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_of_max_le_right hn
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  obtain ⟨hR1, hR2⟩ := h15 n (le_of_max_le_left hn)
  obtain ⟨hC1, hC2⟩ := lemma16 hp0.le hp1 (n := n) (by omega) F hF
  constructor
  · calc ENNReal.ofReal ((1 - p) / 8 / d₂ * Real.log n)
        = ENNReal.ofReal ((1 - p) / 8) / ENNReal.ofReal (d₂ / Real.log n) := by
          rw [← ENNReal.ofReal_div_of_pos (by positivity)]
          congr 1
          field_simp
      _ ≤ _ := ENNReal.div_le_div hC1 hR2
  · calc _ ≤ 2 / ENNReal.ofReal (d₁ / Real.log n) := ENNReal.div_le_div hC2 hR1
      _ = ENNReal.ofReal (2 / d₁ * Real.log n) := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_div_of_pos (by positivity)]
          congr 1
          field_simp

/-! ### Non-vacuity: an admissible alphabet family -/

/-- Messages and packets for `k` messages: the field with `2^(2 ⌊log₂ k⌋ + 2)` elements, i.e.
`O(log k)` bits, within the paper's `O(log (n k))`-bit message and packet size. -/
def galoisAlphabet (k : ℕ) : Type := GaloisField 2 (2 * Nat.log 2 k + 2)

noncomputable instance (k : ℕ) : Field (galoisAlphabet k) :=
  inferInstanceAs (Field (GaloisField 2 (2 * Nat.log 2 k + 2)))

noncomputable instance (k : ℕ) : Fintype (galoisAlphabet k) :=
  @Fintype.ofFinite _ (inferInstanceAs (Finite (GaloisField 2 (2 * Nat.log 2 k + 2))))

noncomputable instance (k : ℕ) : DecidableEq (galoisAlphabet k) := Classical.decEq _

theorem card_galoisAlphabet (k : ℕ) : k ^ 2 ≤ Fintype.card (galoisAlphabet k) := by
  rw [Fintype.card_eq_nat_card]
  change k ^ 2 ≤ Nat.card (GaloisField 2 (2 * Nat.log 2 k + 2))
  rw [GaloisField.card 2 (2 * Nat.log 2 k + 2) (by omega)]
  have : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  calc k ^ 2 ≤ (2 ^ (Nat.log 2 k + 1)) ^ 2 := Nat.pow_le_pow_left this.le 2
    _ = 2 ^ (2 * Nat.log 2 k + 2) := by rw [← pow_mul]; ring_nf

/-- Theorem 17 for the concrete alphabets `galoisAlphabet` (the hypotheses are satisfiable). -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ENNReal.ofReal (c₁ * Real.log n) ≤
          codingThroughput (star n) none .receiver p galoisAlphabet /
            routingThroughput (star n) none .receiver p ∧
        codingThroughput (star n) none .receiver p galoisAlphabet /
            routingThroughput (star n) none .receiver p ≤ ENNReal.ofReal (c₂ * Real.log n) :=
  theorem17 hp0 hp1 galoisAlphabet card_galoisAlphabet

end Podc.NoisyRadioBroadcast
