import Mathlib

-- CSLib candidate: `IsMIS`, `IsMISOn`, `restrict`, `isMIS_union_of_extendable` (SimpleGraph MIS API)

/-!
# Maximal independent sets and extendable partial solutions

Basic notions for Boyar–Ellen–Larsen, *Distributed Graph Algorithms with Predictions*
(PODC 2025, Brief Announcement; full version arXiv:2501.05267).

* `IsMIS G s`: `s` is a maximal independent set of `G` (independent and dominating); equivalent to
  Mathlib's `Maximal G.IsIndepSet s` (`isMIS_iff_maximal`).
* `restrict G R`: the subgraph induced by `R`, on the same vertex type.
* `isMIS_union_of_extendable` (Section 3 of the paper): if `I` is independent, the partial solution
  "`I` outputs 1, the neighbours of `I` output 0" is *extendable*: together with any MIS of the
  subgraph induced by the remaining nodes it is an MIS of the whole graph.
-/

namespace Podc.GraphAlgorithmsPredictions

open SimpleGraph

variable {V : Type*}

/-- `s` is a maximal independent set of `G`: no two members are adjacent and every non-member has
a neighbour in `s`. -/
def IsMIS (G : SimpleGraph V) (s : Set V) : Prop :=
  G.IsIndepSet s ∧ ∀ v ∉ s, ∃ u ∈ s, G.Adj v u

/-- `IsMIS` is maximality among independent sets. -/
theorem isMIS_iff_maximal (G : SimpleGraph V) (s : Set V) :
    IsMIS G s ↔ Maximal G.IsIndepSet s := by
  constructor
  · rintro ⟨hI, hD⟩
    refine ⟨hI, fun t ht hst v hv => ?_⟩
    by_contra hvs
    obtain ⟨u, hu, huv⟩ := hD v hvs
    exact ht hv (hst hu) (fun h => hvs (h ▸ hu)) huv
  · rintro ⟨hI, hmax⟩
    refine ⟨hI, fun v hv => ?_⟩
    by_contra hcon
    push Not at hcon
    have hI' : G.IsIndepSet (insert v s) := by
      rw [isIndepSet_iff, Set.pairwise_insert]
      refine ⟨hI, fun u hu _ => ⟨hcon u hu, fun h => hcon u hu h.symm⟩⟩
    exact hv (hmax hI' (Set.subset_insert v s) (Set.mem_insert v s))

/-- The subgraph of `G` induced by `R`, as a graph on the same vertex type (vertices outside `R`
are isolated). -/
def restrict (G : SimpleGraph V) (R : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ R ∧ v ∈ R
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

@[simp] lemma restrict_adj {G : SimpleGraph V} {R : Set V} {u v : V} :
    (restrict G R).Adj u v ↔ G.Adj u v ∧ u ∈ R ∧ v ∈ R := Iff.rfl

/-- `M` is a maximal independent set of the subgraph of `G` induced by `R`. -/
def IsMISOn (G : SimpleGraph V) (R M : Set V) : Prop :=
  M ⊆ R ∧ G.IsIndepSet M ∧ ∀ v ∈ R, v ∉ M → ∃ u ∈ M, G.Adj v u

/-- `IsMISOn G R` is `IsMIS` of the induced subgraph `G.induce R` (on the subtype). -/
theorem isMISOn_iff_isMIS_induce (G : SimpleGraph V) (R M : Set V) (hMR : M ⊆ R) :
    IsMISOn G R M ↔ IsMIS (G.induce R) {v : R | (v : V) ∈ M} := by
  constructor
  · rintro ⟨-, hI, hD⟩
    refine ⟨fun u hu w hw huw h => hI hu hw (fun e => huw (Subtype.ext e)) h, fun v hv => ?_⟩
    obtain ⟨u, hu, huv⟩ := hD v v.2 hv
    exact ⟨⟨u, hMR hu⟩, hu, huv⟩
  · rintro ⟨hI, hD⟩
    refine ⟨hMR, fun u hu w hw huw h => ?_, fun v hv hvM => ?_⟩
    · have := @hI ⟨u, hMR hu⟩ hu ⟨w, hMR hw⟩ hw (fun e => huw (congrArg Subtype.val e))
      exact this h
    · obtain ⟨u, hu, huv⟩ := hD ⟨v, hv⟩ hvM
      exact ⟨u, hu, huv⟩

/-- The nodes that are neither in `I` nor adjacent to `I`: the remainder of the graph after the
partial solution "`I` outputs 1, `N(I)` outputs 0". -/
def remainder (G : SimpleGraph V) (I : Set V) : Set V :=
  {v | v ∉ I ∧ ∀ u ∈ I, ¬ G.Adj v u}

/-- **Extendability** (Section 3): if `I` is independent, then `I` together with any MIS `M` of the
subgraph induced by the remainder `V \ (I ∪ N(I))` is an MIS of `G`. -/
theorem isMIS_union_of_extendable {G : SimpleGraph V} {I M : Set V} (hI : G.IsIndepSet I)
    (hM : IsMISOn G (remainder G I) M) : IsMIS G (I ∪ M) := by
  obtain ⟨hMR, hMI, hMD⟩ := hM
  refine ⟨?_, fun v hv => ?_⟩
  · rintro u (hu | hu) w (hw | hw) huw hadj
    · exact hI hu hw huw hadj
    · exact (hMR hw).2 u hu hadj.symm
    · exact (hMR hu).2 w hw hadj
    · exact hMI hu hw huw hadj
  · simp only [Set.mem_union, not_or] at hv
    by_cases hR : v ∈ remainder G I
    · obtain ⟨u, hu, huv⟩ := hMD v hR hv.2
      exact ⟨u, Or.inr hu, huv⟩
    · simp only [remainder, Set.mem_ofPred_eq, not_and, not_forall, not_not] at hR
      obtain ⟨u, hu, huv⟩ := hR hv.1
      exact ⟨u, Or.inl hu, huv⟩

/-- If the remainder is empty, the independent set `I` itself is an MIS. -/
theorem isMIS_of_remainder_eq_empty {G : SimpleGraph V} {I : Set V} (hI : G.IsIndepSet I)
    (h : remainder G I = ∅) : IsMIS G I := by
  have := isMIS_union_of_extendable (M := ∅) hI ⟨by simp, by simp, fun v hv => by simp_all⟩
  simpa using this

end Podc.GraphAlgorithmsPredictions
