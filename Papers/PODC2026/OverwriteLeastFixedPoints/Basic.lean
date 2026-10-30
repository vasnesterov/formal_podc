import Mathlib

/-!
# Basic notions for "Computing Least Fixed Points with Overwrite Semantics"

Garg & Garg, PODC 2026 (brief announcement; full version arXiv:2602.10486).

* `Inflationary f` (Definition 1), monotonicity is Mathlib's `Monotone` (Definition 2);
* `IsCommonFixed f x`: `x` is a fixed point of every `f i`;
* `FairSeq σ` / `FairSets S`: every index is scheduled infinitely often;
* `StronglyFair τ S` (Definition 6): every index is scheduled in every window of `τ` rounds;
* `TerminatesAt G x`: the execution `G : ℕ → L` is eventually constant equal to `x`;
* `exists_terminatesAt_of_monotone`: an ascending chain in a poset without infinite ascending chains
  stabilizes.
-/

namespace Podc.OverwriteLeastFixedPoints

variable {L ι : Type*}

/-- Definition 1 of [Garg–Garg]: `f` is inflationary if `G ≤ f G` for all `G`. -/
def Inflationary [LE L] (f : L → L) : Prop := ∀ x, x ≤ f x

/-- Dual of Definition 1 (used in Section 5): `f` is deflationary if `f G ≤ G` for all `G`. -/
def Deflationary [LE L] (f : L → L) : Prop := ∀ x, f x ≤ x

/-- `x` is a common fixed point of the family `f`. -/
def IsCommonFixed (f : ι → L → L) (x : L) : Prop := ∀ i, f i x = x

/-- A schedule picking one index per step is fair if every index is picked infinitely often. -/
def FairSeq (σ : ℕ → ι) : Prop := ∀ i N, ∃ t, N ≤ t ∧ σ t = i

/-- A schedule picking a set of indices per round is fair if every index is in infinitely many of
the sets. -/
def FairSets (S : ℕ → Set ι) : Prop := ∀ i N, ∃ t, N ≤ t ∧ i ∈ S t

/-- Definition 6 of [Garg–Garg]: strong fairness with window `τ`: every index is selected at least
once in any window of `τ` consecutive rounds. -/
def StronglyFair (τ : ℕ) (S : ℕ → Set ι) : Prop := ∀ i t, ∃ s, t ≤ s ∧ s < t + τ ∧ i ∈ S s

/-- Strong fairness implies fairness. -/
theorem StronglyFair.fairSets {τ : ℕ} {S : ℕ → Set ι} (h : StronglyFair τ S) : FairSets S := by
  intro i N
  obtain ⟨s, hs, -, hi⟩ := h i N
  exact ⟨s, hs, hi⟩

/-- The execution `G` terminates at `x`: from some time on, the state is constantly `x`. -/
def TerminatesAt (G : ℕ → L) (x : L) : Prop := ∃ T, ∀ t, T ≤ t → G t = x

theorem TerminatesAt.unique {G : ℕ → L} {x y : L} (hx : TerminatesAt G x)
    (hy : TerminatesAt G y) : x = y := by
  obtain ⟨T, hT⟩ := hx
  obtain ⟨U, hU⟩ := hy
  rw [← hT (max T U) (le_max_left _ _), hU (max T U) (le_max_right _ _)]

/-- An ascending chain in a poset without infinite strictly ascending chains stabilizes. -/
theorem exists_terminatesAt_of_monotone [PartialOrder L] [WellFoundedGT L] {G : ℕ → L}
    (hG : Monotone G) : ∃ T, ∀ t, T ≤ t → G t = G T := by
  obtain ⟨T, hT⟩ := WellFoundedGT.monotone_chain_condition ⟨G, hG⟩
  exact ⟨T, fun t ht => (hT t ht).symm⟩

/-- For an inflationary function, `f x = x ↔ f x ≤ x`. -/
theorem Inflationary.eq_iff_le [PartialOrder L] {f : L → L} (hf : Inflationary f) {x : L} :
    f x = x ↔ f x ≤ x :=
  ⟨fun h => h.le, fun h => le_antisymm h (hf x)⟩

/-- The common fixed points of monotone inflationary functions are closed under binary meets
(the correct version of the paper's remark that they form a sublattice; see
`Interleaving.fixedPoints_not_supClosed`). -/
theorem isCommonFixed_inf [SemilatticeInf L] {f : ι → L → L} (hm : ∀ i, Monotone (f i))
    (hinf : ∀ i, Inflationary (f i)) {x y : L} (hx : IsCommonFixed f x) (hy : IsCommonFixed f y) :
    IsCommonFixed f (x ⊓ y) := by
  intro i
  refine le_antisymm ?_ (hinf i _)
  refine le_inf ?_ ?_
  · calc f i (x ⊓ y) ≤ f i x := hm i inf_le_left
      _ = x := hx i
  · calc f i (x ⊓ y) ≤ f i y := hm i inf_le_right
      _ = y := hy i

end Podc.OverwriteLeastFixedPoints
