import Papers.PODC2026.ReachingUnivalency.Recursive
import Papers.PODC2026.ReachingUnivalency.Sampler

/-!
# Reaching Univalency — Theorem 1 (for the corrected protocol)

**Theorem 1.** For every `ε ∈ (0, 1/3)`, ε-BA can be solved deterministically in the synchronous
unauthenticated setting with `O(n log n)` communication when `f < n(1/3 - ε)`.

We prove it for the recursive ε-RPK of Fig. 3 with the step-1 threshold raised from
`k(2/3 - ε/2)` to `k(2/3 - ε/4)` (the paper's protocol is not correct for every admissible sampling
choice, see `Counterexample.lean`): there is a sample size `k = k(ε)` and a sampling choice for
every size such that every execution with `f < n(1/3 - ε)` solves ε-BA, and the protocol sends at
most `6kn⌈log₂ n⌉ + n` messages of `O(1)` bits.
-/

namespace ReachingUnivalency.RPK

open Finset

/-- **Theorem 1 (corrected protocol).** -/
theorem theorem1_corrected {ε : ℚ} (hε : 0 < ε) (hε3 : ε < 1/3) :
    ∃ k : ℕ, 0 < k ∧ ∃ smp : (m : ℕ) → Sampling m k,
      (∀ (n : ℕ) (F : Finset (Fin n)) (out : (Fin n → Bool) → Fin n → Bool),
        Outcome (T1c ε) smp n F out → 0 < n → ((F.card : ℕ) : ℚ) < n * (1/3 - ε) →
        ∀ inp, EpsBA ε F inp (out inp)) ∧
      (∀ n, msgs k n ≤ 6 * k * n * Nat.clog 2 n + n) := by
  obtain ⟨k, hk, hs⟩ := exists_sampler (δ := ε/8) (γ := ε/80) (by positivity) (by positivity)
  choose g hgR hg using hs
  have hne : ∀ m, 2 < m → (univ : Finset (Fin m)).Nonempty :=
    fun m hm => ⟨⟨0, by omega⟩, mem_univ _⟩
  have hcne : ∀ m, 2 < m → ∀ r, (comms m r).Nonempty := by
    intro m hm r
    rw [← card_pos, card_comms]
    split_ifs <;> omega
  let smp : (m : ℕ) → Sampling m k := fun m =>
    if h : 2 < m then
      { val := fun _ => g m univ (hne m h), resp := fun _ => g m univ (hne m h),
        comm := fun r => g m (comms m r) (hcne m h r) }
    else { val := fun _ p _ => p, resp := fun _ p _ => p, comm := fun _ p _ => p }
  have hgood : ∀ m : ℕ, 2 < m → SamplingGood (ε/8) (ε/80 * m) (smp m) (comms m) := by
    intro m hm r
    simp only [smp, hm, ↓reduceDIte]
    exact ⟨hg m univ (hne m hm), hg m univ (hne m hm), hg m (comms m r) (hcne m hm r)⟩
  refine ⟨k, hk, smp, fun n F out h hn hF inp => ?_, fun n => msgs_le k n⟩
  exact outcome_epsBA smp hε hε3 hk (by positivity) le_rfl (by linarith) hgood h hn hF inp

end ReachingUnivalency.RPK
