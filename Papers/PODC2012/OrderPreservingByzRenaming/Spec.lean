import Mathlib
import Cslib.Computability.Distributed.Byzantine.LockStep.GroupSim

/-!
# Order-preserving renaming: the problem

Denysyuk, Rodrigues, *Order-Preserving Renaming in Synchronous Message Passing Systems with
Byzantine Faults*, PODC 2012 (brief announcement); full version: Chapter 6 of O. Denysyuk's PhD
thesis *Fault-Tolerant Renaming in Synchronous Message-Passing Systems* (IST Lisbon, 2014).
Section numbers refer to the thesis.

We use CSLib's synchronous lock-step Byzantine model (`Cslib.Byzantine.LockStep`): deterministic
history-based protocols, a static Byzantine set, an adversary choosing arbitrary messages (per round,
sender and receiver), reliable links. Inputs are the original identifiers (`ℕ`), outputs the new
names (`ℕ`).

`OPRenamingOn S M` (§3.4): whenever the correct processes have pairwise distinct original ids in the
original namespace `S`, every correct process decides (termination), on a name in `{1, …, M}`
(validity), names of correct processes are distinct (uniqueness) and preserve the order of the
original ids (order preservation). Byzantine processes have no requirements and their inputs are
irrelevant.
-/

namespace Podc.OrderPreservingByzRenaming

open Cslib.Byzantine.LockStep

/-- **Order-preserving renaming** (§3.4.1–3.4.2 of the thesis) from the original namespace `S` into
the target namespace `{1, …, M}`, as a `LockStep` specification. -/
def OPRenamingOn {P : Type*} (S : Set ℕ) (M : ℕ) : Spec P ℕ ℕ := fun x H dec =>
  (Set.InjOn x H ∧ ∀ p ∈ H, x p ∈ S) →
    -- termination
    (∀ p ∈ H, ∃ o, dec p o) ∧
    -- validity
    (∀ p ∈ H, ∀ o, dec p o → 1 ≤ o ∧ o ≤ M) ∧
    -- uniqueness
    (∀ p ∈ H, ∀ q ∈ H, ∀ o o', dec p o → dec q o' → p ≠ q → o ≠ o') ∧
    -- order preservation
    (∀ p ∈ H, ∀ q ∈ H, ∀ o o', dec p o → dec q o' → x p < x q → o < o')

/-- Order-preserving renaming with arbitrary original ids (in `ℕ`) into `{1, …, M}`. -/
abbrev OPRenaming {P : Type*} (M : ℕ) : Spec P ℕ ℕ := OPRenamingOn Set.univ M

/-- A smaller original namespace makes the problem easier. -/
lemma OPRenamingOn.mono {P : Type*} {S S' : Set ℕ} {M : ℕ} (hS : S ⊆ S') {x : P → ℕ} {H : Set P}
    {dec : P → ℕ → Prop} (h : OPRenamingOn S' M x H dec) : OPRenamingOn S M x H dec :=
  fun ⟨hinj, hx⟩ => h ⟨hinj, fun p hp => hS (hx p hp)⟩

/-- Solvability is monotone in the original namespace. -/
lemma solvable_mono {P : Type*} {G : SimpleGraph P} {Z : AdvStructure P} {S S' : Set ℕ} {M : ℕ}
    (hS : S ⊆ S') (h : Solvable G Z (OPRenamingOn (P := P) S' M)) :
    Solvable G Z (OPRenamingOn (P := P) S M) := by
  obtain ⟨Msg, alg, halg⟩ := h
  exact ⟨Msg, alg, fun s hs hr => (halg s hs hr).mono hS⟩

end Podc.OrderPreservingByzRenaming
