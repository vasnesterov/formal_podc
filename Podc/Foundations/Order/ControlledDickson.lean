/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Foundations/Order/ControlledDickson.lean
import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.WellFoundedSet
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Discrete
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Controlled Dickson's lemma (qualitative form)

Dickson's lemma says that every infinite sequence in `ℕ^d` has an infinite monotone (for the
product order) subsequence. For *controlled* sequences — sequences `v` with `‖v i‖₁ ≤ i + δ` —
a compactness argument (König's lemma) yields a uniform bound: for every `δ m d` there is `N`
such that every such sequence has a monotone subsequence of length `m + 1` within the first
`N + 1` terms. This is the qualitative content of the length-function theorems of Figueira,
Figueira, Schmitz and Schnoebelen (*Ackermannian and primitive-recursive bounds with Dickson's
lemma*, LICS 2011), which give explicit (Ackermannian) bounds.

## Main results

* `Cslib.exists_controlled_chain_bound`: existence of the uniform bound.
* `Cslib.ctrlChainBound δ m d`: the least such bound, with `Cslib.ctrlChainBound_spec`.
-/

namespace Cslib

open Set Topology

/-- `v` has a *chain* of length `m + 1` within the first `N + 1` terms: a strictly increasing
family of indices `idx 0 < ⋯ < idx m ≤ N` along which `v` is monotone. -/
def HasChainWithin (m N : ℕ) {d : ℕ} (v : ℕ → Fin d → ℕ) : Prop :=
  ∃ idx : Fin (m + 1) → ℕ, StrictMono idx ∧ (∀ k, idx k ≤ N) ∧ Monotone (v ∘ idx)

/-- Dickson's lemma: every sequence in `ℕ^d` has chains of every length. -/
theorem exists_hasChainWithin {d : ℕ} (m : ℕ) (v : ℕ → Fin d → ℕ) :
    ∃ N, HasChainWithin m N v := by
  obtain ⟨g, hg⟩ := (Set.isPWO_of_wellQuasiOrderedLE (univ : Set (Fin d → ℕ))).exists_monotone_subseq
    (f := v) (fun _ => mem_univ _)
  refine ⟨g m, fun k => g k, fun a b hab => g.strictMono hab, fun k => ?_, fun a b hab => hg hab⟩
  exact g.monotone (Fin.is_le k)

/-- The compact space of coordinatewise-bounded sequences used in the compactness argument. -/
private abbrev BoundedSeq (δ d : ℕ) := ∀ i : ℕ, Fin d → Fin (i + δ + 1)

/-- The sequence in `ℕ^d` underlying a bounded sequence. -/
private def boundedSeqToNat {δ d : ℕ} (w : BoundedSeq δ d) : ℕ → Fin d → ℕ :=
  fun i k => w i k

/-- A set of sequences in a product of discrete spaces that depends only on finitely many
coordinates is closed. -/
private theorem isClosed_of_depends {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, DiscreteTopology (X i)] (s : Set (∀ i, X i)) (F : Set ι) (hF : F.Finite)
    (hs : ∀ w w', (∀ i ∈ F, w i = w' i) → (w ∈ s ↔ w' ∈ s)) : IsClosed s := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro w hw
  refine ⟨F.pi fun i => {w i}, fun w' hw' => ?_, isOpen_set_pi hF fun _ _ => isOpen_discrete _,
    by simp⟩
  have : ∀ i ∈ F, w i = w' i := fun i hi => (hw' i hi).symm
  exact fun h => hw ((hs w w' this).2 h)

/-- Qualitative controlled Dickson lemma: for every `δ m d` there is `N` such that every
sequence `v` in `ℕ^d` with `‖v i‖₁ ≤ i + δ` has a monotone subsequence of length `m + 1` among its
first `N + 1` terms. -/
theorem exists_controlled_chain_bound (δ m d : ℕ) : ∃ N, ∀ v : ℕ → Fin d → ℕ,
    (∀ i, ∑ k, v i k ≤ i + δ) →
    ∃ idx : Fin (m + 1) → ℕ, StrictMono idx ∧ (∀ k, idx k ≤ N) ∧ Monotone (v ∘ idx) := by
  by_contra hcon
  push Not at hcon
  -- `Bad N`: bounded sequences without a chain within `[0, N]`.
  let Bad : ℕ → Set (BoundedSeq δ d) := fun N => {w | ¬ HasChainWithin m N (boundedSeqToNat w)}
  have hne : ∀ N, (Bad N).Nonempty := by
    intro N
    obtain ⟨v, hv, hbad⟩ := hcon N
    have hle : ∀ i k, v i k < i + δ + 1 := fun i k =>
      Nat.lt_succ_of_le ((Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)).trans (hv i))
    refine ⟨fun i k => ⟨v i k, hle i k⟩, fun ⟨idx, h1, h2, h3⟩ => ?_⟩
    exact hbad idx h1 h2 h3
  have hmono : ∀ N, Bad (N + 1) ⊆ Bad N := by
    intro N w hw ⟨idx, h1, h2, h3⟩
    exact hw ⟨idx, h1, fun k => (h2 k).trans (Nat.le_succ N), h3⟩
  have hclosed : ∀ N, IsClosed (Bad N) := by
    intro N
    refine isClosed_of_depends _ (Iic N) (finite_Iic N) fun w w' hww' => ?_
    have key : ∀ idx : Fin (m + 1) → ℕ, (∀ k, idx k ≤ N) →
        (boundedSeqToNat w) ∘ idx = (boundedSeqToNat w') ∘ idx := by
      intro idx h
      funext k
      show (fun c => ((w (idx k) c : ℕ))) = fun c => (w' (idx k) c : ℕ)
      rw [hww' (idx k) (h k)]
    simp only [Bad, HasChainWithin]
    refine not_congr ⟨fun ⟨idx, h1, h2, h3⟩ => ⟨idx, h1, h2, ?_⟩,
      fun ⟨idx, h1, h2, h3⟩ => ⟨idx, h1, h2, ?_⟩⟩
    · rwa [← key idx h2]
    · rwa [key idx h2]
  obtain ⟨w, hw⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Bad hmono
    hne (hclosed 0).isCompact hclosed
  obtain ⟨N, hN⟩ := exists_hasChainWithin m (boundedSeqToNat w)
  exact (mem_iInter.1 hw N) hN

open Classical in
/-- The least `N` of `exists_controlled_chain_bound`: every sequence `v` in `ℕ^d` with
`‖v i‖₁ ≤ i + δ` has a monotone subsequence of length `m + 1` among `v 0, …, v N`. -/
noncomputable def ctrlChainBound (δ m d : ℕ) : ℕ :=
  Nat.find (exists_controlled_chain_bound δ m d)

/-- Specification of `ctrlChainBound`. -/
theorem ctrlChainBound_spec (δ m d : ℕ) (v : ℕ → Fin d → ℕ) (hv : ∀ i, ∑ k, v i k ≤ i + δ) :
    ∃ idx : Fin (m + 1) → ℕ, StrictMono idx ∧ (∀ k, idx k ≤ ctrlChainBound δ m d) ∧
      Monotone (v ∘ idx) := by
  classical
  exact Nat.find_spec (exists_controlled_chain_bound δ m d) v hv

/-- `ctrlChainBound δ m d` is the least bound with the property of
`exists_controlled_chain_bound`. -/
theorem ctrlChainBound_le {δ m d N : ℕ} (hN : ∀ v : ℕ → Fin d → ℕ,
    (∀ i, ∑ k, v i k ≤ i + δ) →
    ∃ idx : Fin (m + 1) → ℕ, StrictMono idx ∧ (∀ k, idx k ≤ N) ∧ Monotone (v ∘ idx)) :
    ctrlChainBound δ m d ≤ N := by
  classical
  exact Nat.find_min' (exists_controlled_chain_bound δ m d) hN

end Cslib
