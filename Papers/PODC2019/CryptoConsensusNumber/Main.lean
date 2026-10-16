import Papers.PODC2019.CryptoConsensusNumber.Lemma1
import Papers.PODC2019.CryptoConsensusNumber.Impossibility

/-!
# Theorem 2 and Corollary 1: the consensus number of `k`-shared asset transfer

`ATSolvable n k` (see `System.lean`): wait-free binary consensus for `n` processes is solvable with
read/write objects and asset-transfer objects in which every account has at most `k` owners.

* `theorem_2`: for `k ≥ 1`, `ATSolvable k k` and `¬ ATSolvable n k` for every `n > k`, i.e. the
  consensus number of `k`-shared asset transfer is exactly `k`. The algorithm (Lemma 1) uses a
  single asset-transfer object whose shared account has exactly `k` owners (so it is `k`-shared in
  the paper's exact sense, `max_a |μ(a)| = k`).
* `corollary_1`: `k = 1` (single-owner asset transfer has consensus number 1).
* `atSolvable_one`: the degenerate case `k = 0` — one process always solves consensus, so a
  "`0`-shared" object (no owners) has consensus number `1`, not `0`.
-/

namespace CryptoCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable TwoShotCons

/-- Lemma 1 as an `ATSolvable` statement: `k` processes can solve consensus. -/
theorem atSolvable_self {k : ℕ} (hk : 0 < k) : ATSolvable k k :=
  ⟨Fin k, Unit, Fin 2, inferInstance, inferInstance, inferInstance, Lemma1.Reg k,
    fun _ => isRW_register _ _, Lemma1.μ₁ k, fun _ => Lemma1.μ₁_card.2, Lemma1.alg k,
    Lemma1.lemma_1 hk⟩

/-- The "at most `k`" direction as an `ATSolvable` statement. -/
theorem not_atSolvable {n k : ℕ} (hn : 2 ≤ n) (hkn : k < n) : ¬ ATSolvable n k := by
  rintro ⟨ιR, ιS, Acct, _, _, _, R, hR, μ, hμ, A, hA, hH⟩
  exact no_consensus hn hkn hR hμ A hH hA

/-- **Theorem 2.** For `k ≥ 1`, `k`-shared asset transfer has consensus number exactly `k`:
`k` processes can solve wait-free consensus with registers and `k`-shared asset-transfer objects
(Lemma 1, one object suffices), and no larger number of processes can. -/
theorem theorem_2 {k : ℕ} (hk : 1 ≤ k) : ATSolvable k k ∧ ∀ n, k < n → ¬ ATSolvable n k :=
  ⟨atSolvable_self hk, fun _ hkn => not_atSolvable (by omega) hkn⟩

/-- **Corollary 1.** Single-owner (`1`-shared) asset transfer has consensus number `1`. -/
theorem corollary_1 : ATSolvable 1 1 ∧ ∀ n, 1 < n → ¬ ATSolvable n 1 := theorem_2 le_rfl

namespace Trivial

/-- The trivial one-process algorithm: decide your own input (no objects at all). -/
def alg : Alg 1 (atSys (n := 1) (ιR := Empty) (ιS := Empty) (Acct := Empty) Empty.elim
    (fun j => j.elim)) where
  L := Bool
  init _ x := x
  act v := .out v
  mem₀ i := match i with | .inl j => j.elim | .inr j => j.elim

end Trivial

/-- **Degenerate case `k = 0`.** One process always solves consensus (here without any object), so
the consensus number of a `0`-shared asset-transfer object (no account has an owner) is `1`, not
`0` as Theorem 2 would say for `k = 0`; for `n ≥ 2` it is impossible (`not_atSolvable`). -/
theorem atSolvable_one (k : ℕ) : ATSolvable 1 k := by
  refine ⟨Empty, Empty, Empty, inferInstance, inferInstance, inferInstance, Empty.elim,
    fun j => j.elim, fun j => j.elim, fun j => j.elim, Trivial.alg, ?_, ?_⟩
  · refine wfConsensus_of_inv' (fun x C => ∀ p, C.loc p = x p) (fun x p => rfl)
      (fun x C p hC => ?_) (fun x C hC => ⟨0, fun p w hp => ?_⟩) (fun _ => 0)
      (fun l i o κ r h => by cases h)
    · rw [stepP_of_out C (v := C.loc p) rfl]; exact hC
    · have : C.loc p = w := by
        change Act.out (C.loc p) = Act.out w at hp
        cases hp; rfl
      rw [← this, hC p, Subsingleton.elim p 0]
  · intro x α _ p j
    exact j.elim

end CryptoCons
