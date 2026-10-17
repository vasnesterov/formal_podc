import Mathlib.Order.OrderIsoNat

-- CSLib candidate: Mathlib/Order/OrderIsoNat.lean (next to `WellFoundedLT.antitone_chain_condition`)

/-!
# Eventually non-increasing sequences of natural numbers

A sequence `f : ℕ → ℕ` that is non-increasing from some index `N` on is eventually constant
(`Nat.eventually_const_of_succ_le`); consequently it can decrease only finitely often
(`Nat.eventually_not_of_succ_le`, `Nat.not_frequently_lt_of_succ_le`). These are the termination
arguments ("potential functions") behind wait-freedom and lock-freedom proofs. Dually, a bounded
sequence that is non-decreasing from some index on is eventually constant
(`Nat.eventually_const_of_le_succ`).

Both follow from Mathlib's antitone chain condition (`WellFoundedLT.antitone_chain_condition`).
-/

namespace Nat

variable {f : ℕ → ℕ} {N : ℕ}

/-- A sequence of natural numbers that is non-increasing from `N` on is eventually constant. -/
theorem eventually_const_of_succ_le (h : ∀ m ≥ N, f (m + 1) ≤ f m) :
    ∃ T ≥ N, ∀ m ≥ T, f m = f T := by
  obtain ⟨n, hn⟩ := WellFoundedLT.antitone_chain_condition (f := fun k => f (N + k))
    (antitone_nat_of_succ_le fun k => h (N + k) (by omega))
  refine ⟨N + n, by omega, fun m hm => ?_⟩
  have := hn (m - N) (by omega)
  rw [show N + (m - N) = m by omega] at this
  exact this.symm

/-- A sequence of natural numbers that is non-increasing from `N` on and strictly decreases at
every index `m ≥ N` satisfying `p m` satisfies `p` only finitely often. -/
theorem eventually_not_of_succ_le (h : ∀ m ≥ N, f (m + 1) ≤ f m) {p : ℕ → Prop}
    (hp : ∀ m ≥ N, p m → f (m + 1) < f m) : ∃ T ≥ N, ∀ m ≥ T, ¬ p m := by
  obtain ⟨T, hT, hc⟩ := eventually_const_of_succ_le h
  refine ⟨T, hT, fun m hm hpm => ?_⟩
  have := hp m (by omega) hpm
  rw [hc m hm, hc (m + 1) (by omega)] at this
  exact lt_irrefl _ this

/-- A sequence of natural numbers that is non-increasing from `N` on cannot decrease infinitely
often. -/
theorem not_frequently_lt_of_succ_le (h : ∀ m ≥ N, f (m + 1) ≤ f m) :
    ¬ ∀ M, ∃ m ≥ M, f (m + 1) < f m := by
  intro hs
  obtain ⟨T, hT, hc⟩ := eventually_not_of_succ_le h (p := fun m => f (m + 1) < f m)
    fun _ _ hm => hm
  obtain ⟨m, hm, hlt⟩ := hs T
  exact hc m hm hlt

/-- A bounded sequence of natural numbers that is non-decreasing from `N` on is eventually
constant. -/
theorem eventually_const_of_le_succ {B : ℕ} (hB : ∀ m ≥ N, f m ≤ B)
    (h : ∀ m ≥ N, f m ≤ f (m + 1)) : ∃ T ≥ N, ∀ m ≥ T, f m = f T := by
  obtain ⟨T, hT, hc⟩ := eventually_const_of_succ_le (f := fun m => B - f m) (N := N)
    fun m hm => by have := h m hm; have := hB m hm; have := hB (m + 1) (by omega); omega
  refine ⟨T, hT, fun m hm => ?_⟩
  have := hc m hm; have := hB m (by omega); have := hB T hT
  omega

end Nat
