import Mathlib

/-!
# Weighted independent sets

Basic notions for vertex-weighted maximum independent set (MaxIS): independence of a finset,
its weight, and the optimum `opt G w`.
-/

namespace Podc.MISInapproxCongest

open Finset

variable {V : Type*}

/-- `I` is an independent set of `G`. -/
def IsIndep (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v

/-- The weight `w(I) = ∑_{v ∈ I} w v`. -/
def wsum (w : V → ℕ) (I : Finset V) : ℕ := ∑ v ∈ I, w v

theorem IsIndep.subset {G : SimpleGraph V} {I J : Finset V} (h : IsIndep G I) (hJ : J ⊆ I) :
    IsIndep G J := fun u hu v hv => h u (hJ hu) v (hJ hv)

variable [Fintype V]

/-- The weight of a maximum-weight independent set. -/
noncomputable def opt (G : SimpleGraph V) (w : V → ℕ) : ℕ := by
  classical
  exact ((univ : Finset V).powerset.filter (IsIndep G)).sup (wsum w)

theorem le_opt {G : SimpleGraph V} {w : V → ℕ} {I : Finset V} (h : IsIndep G I) :
    wsum w I ≤ opt G w := by
  classical
  unfold opt
  convert Finset.le_sup (f := wsum w) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (subset_univ I), h⟩)

theorem opt_le {G : SimpleGraph V} {w : V → ℕ} {b : ℕ} (h : ∀ I, IsIndep G I → wsum w I ≤ b) :
    opt G w ≤ b := by
  classical
  unfold opt
  convert Finset.sup_le (f := wsum w) (s := (univ : Finset V).powerset.filter (IsIndep G))
    fun I hI => h I (Finset.mem_filter.1 hI).2

theorem exists_opt (G : SimpleGraph V) (w : V → ℕ) : ∃ I, IsIndep G I ∧ wsum w I = opt G w := by
  classical
  obtain ⟨I, hI, he⟩ := Finset.exists_mem_eq_sup ((univ : Finset V).powerset.filter (IsIndep G))
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, fun _ h => absurd h (Finset.notMem_empty _)⟩⟩
    (wsum w)
  refine ⟨I, (Finset.mem_filter.1 hI).2, ?_⟩
  unfold opt
  convert he.symm

end Podc.MISInapproxCongest
