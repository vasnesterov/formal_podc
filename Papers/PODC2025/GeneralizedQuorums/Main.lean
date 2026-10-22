import Papers.PODC2025.GeneralizedQuorums.Objects
import Podc.Computability.Distributed.MessagePassing.ChannelFailures.PartialSync

/-!
# Main results: the lower bounds of Theorem 2, Lemma 2 and Theorem 6

[NCGR25] A. Naser-Pastoriza, G. Chockler, A. Gotsman, F. Ryabinin. *Tight Bounds on Channel
Reliability via Generalized Quorum Systems.* PODC 2025 (arXiv:2505.02646v1).

All statements are about an arbitrary deterministic algorithm `Alg` in the asynchronous
message-passing model with process crashes and channel disconnections
(`Cslib.ChannelFailures`), whose finite executions all satisfy the safety specification of the
object (`Alg.Satisfies ...`). The value domain must be non-trivial (see `Counterexamples.lean`
for why this hypothesis is needed).
-/

namespace Podc.GeneralizedQuorums

open Cslib.ChannelFailures Cslib.SharedMemory

variable {P : Type} [DecidableEq P] [Fintype P] {M L : Type}

/-- **Theorem 2 for lattice agreement.** Let `τ(f)` be a non-empty set of processes correct
under `f`, for every `f ∈ F`. If `Alg` is an `(F, τ)`-obstruction-free implementation of lattice
agreement over a partial order with two incomparable elements, then there are `R`, `W` such that
`(F, R, W)` is a generalized quorum system, and `τ(f) ⊆ U_f` for every `f ∈ F`. -/
theorem theorem_2_lattice_agreement {V : Type} [PartialOrder V]
    (hV : ∃ x₁ x₂ : V, ¬ x₁ ≤ x₂ ∧ ¬ x₂ ≤ x₁) (Alg : Algorithm P (laObj V) M L)
    (hsafe : Alg.Satisfies (laSafe V)) {F : Set (FailurePattern P)}
    {τ : FailurePattern P → Set P} (hne : ∀ f ∈ F, (τ f).Nonempty)
    (hτ : ∀ f ∈ F, τ f ⊆ (f.procs)ᶜ) (hOF : Alg.ObstructionFreeOn F τ) :
    ∃ R W : Set (Set P), IsGQS F R W ∧ ∀ f ∈ F, τ f ⊆ Uf R W f := by
  obtain ⟨x₁, x₂, h₁, h₂⟩ := hV
  exact theorem_2_generic Alg hsafe (fun _ _ hne => conflict_la h₁ h₂ hne) hne hτ hOF

/-- **Theorem 2 for MWMR atomic registers** (with at least two values). -/
theorem theorem_2_register {V : Type} {v₀ : V} (hV : ∃ x : V, x ≠ v₀)
    (Alg : Algorithm P (register V v₀) M L) (hsafe : Alg.Satisfies (regSafe V v₀))
    {F : Set (FailurePattern P)} {τ : FailurePattern P → Set P}
    (hne : ∀ f ∈ F, (τ f).Nonempty) (hτ : ∀ f ∈ F, τ f ⊆ (f.procs)ᶜ)
    (hOF : Alg.ObstructionFreeOn F τ) :
    ∃ R W : Set (Set P), IsGQS F R W ∧ ∀ f ∈ F, τ f ⊆ Uf R W f := by
  obtain ⟨x, hx⟩ := hV
  exact theorem_2_generic Alg hsafe (fun _ _ hne => conflict_reg hx hne) hne hτ hOF

/-- **Theorem 2 for SWMR atomic snapshots** (with at least two values). -/
theorem theorem_2_snapshot {V : Type} {v₀ : V} (hV : ∃ x : V, x ≠ v₀)
    (Alg : Algorithm P (snapObj P V v₀) M L) (hsafe : Alg.Satisfies (snapSafe V v₀))
    {F : Set (FailurePattern P)} {τ : FailurePattern P → Set P}
    (hne : ∀ f ∈ F, (τ f).Nonempty) (hτ : ∀ f ∈ F, τ f ⊆ (f.procs)ᶜ)
    (hOF : Alg.ObstructionFreeOn F τ) :
    ∃ R W : Set (Set P), IsGQS F R W ∧ ∀ f ∈ F, τ f ⊆ Uf R W f := by
  obtain ⟨x, hx⟩ := hV
  exact theorem_2_generic Alg hsafe (fun _ _ hne => conflict_snap hx hne) hne hτ hOF

/-- **Lemma 2.** If `Alg` is an `(f, T)`-obstruction-free implementation of lattice agreement
(over a partial order with two incomparable elements) and `T` consists of processes correct
under `f`, then `T` is strongly connected in `G \ f`. -/
theorem lemma_2_lattice_agreement {V : Type} [PartialOrder V]
    (hV : ∃ x₁ x₂ : V, ¬ x₁ ≤ x₂ ∧ ¬ x₂ ≤ x₁) (Alg : Algorithm P (laObj V) M L)
    (hsafe : Alg.Satisfies (laSafe V)) {f : FailurePattern P} {T : Set P}
    (hT : T ⊆ (f.procs)ᶜ) (hOF : Alg.ObstructionFree f T) :
    ∀ u ∈ T, ∀ v ∈ T, f.Reach u v := by
  obtain ⟨x₁, x₂, h₁, h₂⟩ := hV
  exact lemma_2 Alg hsafe (fun _ _ hne => conflict_la h₁ h₂ hne) hT hOF

/-- **Theorem 6.** Under partial synchrony, an `(F, τ)`-obstruction-free implementation of
consensus (over at least two values), with `τ(f)` non-empty, yields a generalized quorum system
`(F, R, W)` with `τ(f) ⊆ U_f`. -/
theorem theorem_6 {V : Type} (hV : ∃ x₁ x₂ : V, x₁ ≠ x₂) (Alg : Algorithm P (consObj V) M L)
    (hsafe : Alg.Satisfies (consSafe V)) {F : Set (FailurePattern P)}
    {τ : FailurePattern P → Set P} (hne : ∀ f ∈ F, (τ f).Nonempty)
    (hτ : ∀ f ∈ F, τ f ⊆ (f.procs)ᶜ) (hOF : Alg.ObstructionFreePSOn F τ) :
    ∃ R W : Set (Set P), IsGQS F R W ∧ ∀ f ∈ F, τ f ⊆ Uf R W f := by
  obtain ⟨x₁, x₂, hx⟩ := hV
  exact theorem_2_of_soloTerm Alg hsafe (fun _ _ hne => conflict_cons hx hne) hne hτ
    fun f hf p hp o => soloTerm_of_obstructionFreePS (hOF f hf) hp (hτ f hf hp) o

/-- The lower bound of Theorem 6 also holds for lattice agreement, registers and snapshots under
partial synchrony (§7); stated here for lattice agreement. -/
theorem theorem_6_lattice_agreement {V : Type} [PartialOrder V]
    (hV : ∃ x₁ x₂ : V, ¬ x₁ ≤ x₂ ∧ ¬ x₂ ≤ x₁) (Alg : Algorithm P (laObj V) M L)
    (hsafe : Alg.Satisfies (laSafe V)) {F : Set (FailurePattern P)}
    {τ : FailurePattern P → Set P} (hne : ∀ f ∈ F, (τ f).Nonempty)
    (hτ : ∀ f ∈ F, τ f ⊆ (f.procs)ᶜ) (hOF : Alg.ObstructionFreePSOn F τ) :
    ∃ R W : Set (Set P), IsGQS F R W ∧ ∀ f ∈ F, τ f ⊆ Uf R W f := by
  obtain ⟨x₁, x₂, h₁, h₂⟩ := hV
  exact theorem_2_of_soloTerm Alg hsafe (fun _ _ hne => conflict_la h₁ h₂ hne) hne hτ
    fun f hf p hp o => soloTerm_of_obstructionFreePS (hOF f hf) hp (hτ f hf hp) o

/-- Consensus is also covered by the asynchronous lower bound (Theorem 2's argument). -/
theorem theorem_2_consensus {V : Type} (hV : ∃ x₁ x₂ : V, x₁ ≠ x₂)
    (Alg : Algorithm P (consObj V) M L) (hsafe : Alg.Satisfies (consSafe V))
    {F : Set (FailurePattern P)} {τ : FailurePattern P → Set P}
    (hne : ∀ f ∈ F, (τ f).Nonempty) (hτ : ∀ f ∈ F, τ f ⊆ (f.procs)ᶜ)
    (hOF : Alg.ObstructionFreeOn F τ) :
    ∃ R W : Set (Set P), IsGQS F R W ∧ ∀ f ∈ F, τ f ⊆ Uf R W f := by
  obtain ⟨x₁, x₂, hx⟩ := hV
  exact theorem_2_generic Alg hsafe (fun _ _ hne => conflict_cons hx hne) hne hτ hOF

end Podc.GeneralizedQuorums
