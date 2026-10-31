import Papers.PODC2014.LinearInDeltaLB.Defs

/-!
# Non-vacuity of `IDAlg.Solves`

The hypothesis `A.Solves Δ` of Theorem 1 is satisfiable: the (global, non-local) algorithm that
outputs the indicator of a maximum-cardinality matching finds a maximal fractional matching on
every finite graph (`exists_solves`).
-/

namespace Podc.LinearInDeltaLB

/-- `M` is a matching: distinct edges of `M` share no node. -/
def IsMatchingSet (M : Finset (Sym2 ℕ)) : Prop :=
  ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → ∀ x, x ∈ e → x ∉ e'

theorem exists_maximal_matching (G : SimpleGraph ℕ) (hG : G.edgeSet.Finite) :
    ∃ M : Finset (Sym2 ℕ), (↑M ⊆ G.edgeSet) ∧ IsMatchingSet M ∧
      ∀ u v, G.Adj u v → (∃ w, s(u, w) ∈ M) ∨ (∃ w, s(v, w) ∈ M) := by
  classical
  let E := hG.toFinset
  let C := E.powerset.filter IsMatchingSet
  have hne : C.Nonempty := ⟨∅, by simp [C, IsMatchingSet]⟩
  obtain ⟨M, hMC, hmax⟩ := C.exists_max_image Finset.card hne
  simp only [C, Finset.mem_filter, Finset.mem_powerset] at hMC
  refine ⟨M, fun e he => by simpa [E] using hMC.1 he, hMC.2, fun u v huv => ?_⟩
  by_contra h
  push Not at h
  obtain ⟨hu, hv⟩ := h
  have hnot : s(u, v) ∉ M := hu v
  have hmem : insert s(u, v) M ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset (by simpa [E] using huv) hMC.1, ?_⟩
    intro e he e' he' hee' x hxe hxe'
    rw [Finset.mem_insert] at he he'
    have key : ∀ f ∈ M, x ∈ f → x ∉ s(u, v) := by
      intro f hf hxf hx
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      · obtain ⟨y, rfl⟩ : ∃ y, f = s(x, y) := by
          induction f using Sym2.ind with
          | _ a b =>
            rcases Sym2.mem_iff.1 hxf with rfl | rfl
            · exact ⟨b, rfl⟩
            · exact ⟨a, Sym2.eq_swap⟩
        exact hu y hf
      · obtain ⟨y, rfl⟩ : ∃ y, f = s(x, y) := by
          induction f using Sym2.ind with
          | _ a b =>
            rcases Sym2.mem_iff.1 hxf with rfl | rfl
            · exact ⟨b, rfl⟩
            · exact ⟨a, Sym2.eq_swap⟩
        exact hv y hf
    rcases he with rfl | he <;> rcases he' with rfl | he'
    · exact hee' rfl
    · exact key e' he' hxe' hxe
    · exact key e he hxe hxe'
    · exact hMC.2 e he e' he' hee' x hxe hxe'
  have := hmax _ hmem
  rw [Finset.card_insert_of_notMem hnot] at this
  omega

/-- On every finite graph there is a maximal fractional matching (even an integral one). -/
theorem exists_isMaxFMGraph (G : SimpleGraph ℕ) (hG : G.edgeSet.Finite) :
    ∃ y, IsMaxFMGraph G y := by
  classical
  obtain ⟨M, hME, hM, hmax⟩ := exists_maximal_matching G hG
  let y : ℕ → ℕ → ℝ := fun u v => if s(u, v) ∈ M then 1 else 0
  -- at most one matching edge per node
  have uniq : ∀ u v w, s(u, v) ∈ M → s(u, w) ∈ M → v = w := by
    intro u v w hv hw
    by_contra h
    have hne : s(u, v) ≠ s(u, w) := by
      intro e; rcases Sym2.eq_iff.1 e with ⟨-, h'⟩ | ⟨rfl, rfl⟩ <;> [exact h h'; exact h rfl]
    exact hM _ hv _ hw hne u (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _)
  have load : ∀ u, ∑ᶠ v ∈ G.neighborSet u, y u v = if ∃ w, s(u, w) ∈ M then 1 else 0 := by
    intro u
    split_ifs with h
    · obtain ⟨w, hw⟩ := h
      have hadj : w ∈ G.neighborSet u := by
        have := hME hw; simpa using this
      rw [finsum_mem_def, finsum_eq_single _ w, Set.indicator_of_mem hadj]
      · simp [y, hw]
      · intro v hvw
        by_cases hv : v ∈ G.neighborSet u
        · rw [Set.indicator_of_mem hv]
          simp only [y, ite_eq_right_iff, one_ne_zero, imp_false]
          intro hv'; exact hvw (uniq u v w hv' hw)
        · exact Set.indicator_of_notMem hv _
    · push Not at h
      rw [finsum_mem_eq_zero_of_forall_eq_zero]
      intro v _; simp [y, h v]
  refine ⟨y, ⟨fun u v _ => by simp [y, Sym2.eq_swap], fun u v _ => by simp only [y]; split_ifs <;>
    norm_num, fun u => by rw [load]; split_ifs <;> norm_num, fun u v huv => ?_⟩⟩
  rw [load, load]
  rcases hmax u v huv with h | h
  · left; simp [h]
  · right; simp [h]

/-- Non-vacuity: some ID-algorithm (a global one) solves the maximal FM problem for every `Δ`. -/
theorem exists_solves : ∃ A : IDAlg, ∀ Δ, A.Solves Δ := by
  classical
  refine ⟨fun G => if h : G.edgeSet.Finite then (exists_isMaxFMGraph G h).choose else 0,
    fun Δ G hG _ => ?_⟩
  simp only [hG, ↓reduceDIte]
  exact (exists_isMaxFMGraph G hG).choose_spec

end Podc.LinearInDeltaLB
