import Mathlib.Data.Fintype.Fin
import Papers.PODC2024.BoundedRegisterPower.NonUniversality
import Papers.PODC2024.BoundedRegisterPower.ApproxAgreement
import Podc.Computability.Distributed.SWMR.FLP

/-!
# Theorem 1.1: bounded registers are not universal when `n/2 < t < n`

`n` processes `Fin n`; the early processes `G = {p₁, …, p_{n-t+1}}` are the first `n - t + 1`
indices. Lemma 2.1 (impossibility of `1`-resilient binary consensus) is
`Cslib.SWMR.Alg.not_solves_binConsensus`; Lemma 2.2 (wait-free `ε`-agreement with unbounded
registers) is `approxAgreement_solvable`.
-/

namespace Podc.BoundedRegisterPower

open Cslib.SWMR

/-- The early processes `p₁, …, p_m` (`m = n - t + 1` in the paper). -/
def early (n m : ℕ) : Finset (Fin n) := Finset.univ.filter (fun p => p.1 < m)

lemma card_early {n m : ℕ} (h : m ≤ n) : (early n m).card = m := by
  simp [early, Fin.card_filter_val_lt, h]

lemma card_compl_early {n m : ℕ} (h : m ≤ n) : (early n m)ᶜ.card = n - m := by
  rw [Finset.card_compl, Fintype.card_fin, card_early h]

/-- **Proposition 4.1** (full version) for `n` processes with register banks of at most
`2 ^ f(n)` values (`f(n)` bits): `1/k`-agreement with `k = 2 (2^{f(n)})^{n-t+1} + 1` cannot be
solved `t`-resiliently when `n > 2` and `n/2 < t < n`. -/
theorem proposition_4_1 (f : ℕ → ℕ) {n t : ℕ} (hn : 2 < n) (ht : n < 2 * t) (htn : t < n)
    {K : Type} [DecidableEq K] {V : K → Type} [Finite (∀ i, V i)]
    (hV : Nat.card (∀ i, V i) ≤ 2 ^ f n) (A : Alg (Fin n) K V Bool ℕ) :
    ¬ A.Solves t (epsAgreement (2 * (2 ^ f n) ^ (n - t + 1) + 1)) := by
  have hm : n - t + 1 ≤ n := by omega
  have hG := card_early (n := n) hm
  have hGc := card_compl_early (n := n) hm
  refine not_solves_epsAgreement A (G := early n (n - t + 1)) (by omega) (by omega) ?_ ?_ ?_
  · rw [← Finset.card_pos, hGc]; omega
  · intro B
    exact Alg.not_solves_binConsensus (by rw [Fintype.card_coe, hG]; omega) B
  · rw [hG]
    have := Nat.pow_le_pow_left hV (n - t + 1)
    omega

/-- **Theorem 1.1.** For every `f : ℕ → ℕ`, `n > 2` and `n/2 < t < n` there is a task with binary
inputs (`1/k`-agreement for a suitable `k`) that `n` processes solve `t`-resiliently (even
wait-free) with unbounded registers (one register per process holding a list of rationals), but
that no algorithm solves `t`-resiliently when every process owns registers of at most `f(n)` bits
in total (any bank `∀ i, V i` of at most `2 ^ f(n)` values). -/
theorem theorem_1_1 (f : ℕ → ℕ) {n t : ℕ} (hn : 2 < n) (ht : n < 2 * t) (htn : t < n) :
    ∃ T : Task (Fin n) Bool ℕ,
      (∃ A : Alg (Fin n) Unit (fun _ => List ℚ) Bool ℕ, A.Solves t T) ∧
      ∀ (K : Type) [DecidableEq K] (V : K → Type) [Finite (∀ i, V i)],
        Nat.card (∀ i, V i) ≤ 2 ^ f n → ∀ A : Alg (Fin n) K V Bool ℕ, ¬ A.Solves t T := by
  refine ⟨epsAgreement (2 * (2 ^ f n) ^ (n - t + 1) + 1), ?_, fun K _ V _ hV A =>
    proposition_4_1 f hn ht htn hV A⟩
  obtain ⟨A, hA⟩ := approxAgreement_solvable (P := Fin n) (2 * (2 ^ f n) ^ (n - t + 1) + 1)
    (by omega)
  exact ⟨A, hA.mono (by rw [Fintype.card_fin]; omega)⟩

/-- Theorem 1.1 for the paper's model with a single register of at most `f(n)` bits per process. -/
theorem theorem_1_1_single (f : ℕ → ℕ) {n t : ℕ} (hn : 2 < n) (ht : n < 2 * t) (htn : t < n) :
    ∃ T : Task (Fin n) Bool ℕ,
      (∃ A : Alg (Fin n) Unit (fun _ => List ℚ) Bool ℕ, A.Solves t T) ∧
      ∀ (W : Type) [Fintype W], Fintype.card W ≤ 2 ^ f n →
        ∀ A : Alg (Fin n) Unit (fun _ => W) Bool ℕ, ¬ A.Solves t T := by
  obtain ⟨T, hpos, hneg⟩ := theorem_1_1 f hn ht htn
  refine ⟨T, hpos, fun W _ hW A => hneg Unit (fun _ => W) ?_ A⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  simpa using hW

end Podc.BoundedRegisterPower
