import Papers.PODC2018.LocallyIterativeColoring.Main
import Papers.PODC2018.LocallyIterativeColoring.Halving

/-!
# Corollary 3.9 of [BEG18] (second assertion): `O(Δ²)` to `Δ + 1` colours with one-bit rounds

AG (Corollary 3.5, one bit per edge per round) followed by `s` one-bit halving phases (Lemma 3.8).
-/

namespace BEG18

open Cslib.LocallyIterative

/-- AG for `q = agPrime Δ k` rounds, then `s` halving phases. -/
noncomputable def oneBitColoring (Δ k s : ℕ) : Algorithm ℕ :=
  (agNat (agPrime Δ k)).seq (agPrime Δ k) (Halving.iterHalving Δ s (agPrime Δ k))

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **Corollary 3.9 of [BEG18], second assertion.** From a proper `k`-colouring of a graph of maximum
degree `≤ Δ`, if `q = agPrime Δ k ≤ 2^s (Δ + 1)` (e.g. `s = 6` for `k ≤ max (16Δ²) 256`), then after
`q + (Δ + 1) s` rounds — each of which needs one bit per edge — the colouring is a proper
`(Δ + 1)`-colouring. -/
theorem oneBitColoring_run {Δ k s : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
    (hs : agPrime Δ k ≤ 2 ^ s * (Δ + 1)) {φ : V → ℕ} (hφ : ∀ v, φ v < k) (hp : IsProper G φ) :
    IsProper G ((oneBitColoring Δ k s).run G φ (agPrime Δ k + (Δ + 1) * s)) ∧
      ∀ v, (oneBitColoring Δ k s).run G φ (agPrime Δ k + (Δ + 1) * s) v < Δ + 1 := by
  have hφq : ∀ v, φ v < agPrime Δ k * agPrime Δ k := fun v => (hφ v).trans (lt_agPrime_sq Δ k)
  rw [oneBitColoring, Algorithm.run_seq_add]
  exact Halving.iterHalving_run hΔ s hs (agNat_isProper hφq hp _)
    (agNat_lt hΔ (two_mul_lt_agPrime Δ k) hφq hp)

/-- With Linial's palette `k = max (16Δ²) 256`, six halving phases suffice: `O(Δ)` one-bit rounds. -/
theorem agPrime_linial_le (Δ : ℕ) : agPrime Δ (max (16 * Δ ^ 2) 256) ≤ 2 ^ 6 * (Δ + 1) := by
  have h1 := agPrime_le Δ (max (16 * Δ ^ 2) 256)
  have hK : max (16 * Δ ^ 2) 256 ≤ (4 * Δ + 16) * (4 * Δ + 16) := by
    apply max_le <;> nlinarith
  have hs : Nat.sqrt (max (16 * Δ ^ 2) 256) ≤ 4 * Δ + 16 :=
    (Nat.sqrt_le_sqrt hK).trans (Nat.sqrt_eq _).le
  have : max (2 * Δ + 1) (Nat.sqrt (max (16 * Δ ^ 2) 256) + 1) ≤ 4 * Δ + 17 := by omega
  omega

end BEG18
