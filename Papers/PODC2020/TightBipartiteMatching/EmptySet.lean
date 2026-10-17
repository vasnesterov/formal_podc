import Papers.PODC2020.TightBipartiteMatching.Relaxations

/-!
# The empty set in `R_B` (gap in the proof of Lemma 4.1)

The paper's `R_B(Π)` uses all subsets of `Σ_Π`, including `∅`. With `∅` allowed, the configuration
`(∅, MZPOX, …, MZPOX)` satisfies the universal condition of `R_B(Ψ^W_Δ(a, b, c))` vacuously, it is
maximal (adding any label to `∅` creates a choice with `Δ − 1 > a` labels `M`), and for
`a ≤ Δ − 2` it cannot be extended to any configuration of the relaxation `Ψ^B_Δ(a, d', b)` (these
contain at most `a` sets `MZPOX`). So the first claim of the proof of Lemma 4.1 fails for it. This is
harmless (`∅` never occurs in a correct solution); we use nonempty sets (`univC`).
-/

namespace TightBipartiteMatching

open Lab

variable {d : ℕ}

/-- The paper's universal quantifier, allowing empty sets. -/
def univC₀ {L : Type*} (C : Set (Multiset L)) : Set (Multiset (Set L)) :=
  {m | ∀ m', Multiset.Rel (· ∈ ·) m' m → m' ∈ C}

/-- `(∅, MZPOX, …, MZPOX)`. -/
def emptyConf (d : ℕ) : Fin (d + 1) → Set Lab := Fin.cons ∅ fun _ => Set.univ

theorem psi_W_count_X {a b c : ℕ} {m : Multiset Lab} (h : m ∈ (Psi d a b c).W) :
    m.count X ≤ a := by
  simp only [Psi, Cond.mem_gens, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨c', hc', hm⟩ := h
  rcases hc' with rfl | rfl | rfl
  all_goals
    obtain ⟨m₁, m₂, m₃, rfl, h1, h2, h3⟩ := gen3_counts hm
    simp [-Multiset.count_eq_zero] at h1 h2 h3
    simp only [Multiset.count_add]
    omega

/-- The configuration `(∅, MZPOX, …, MZPOX)` is in the paper's black constraint of
`R_B(Ψ^W_Δ(a, b, c))` (vacuously), it is maximal, and for `a ≤ Δ − 2` no port-wise enlargement of it is
a configuration of `Ψ^B_Δ(a, d', b)`, for any `d'`. -/
theorem emptyConf_counterexample {a b c d' : ℕ} (ha : 1 ≤ a) (ha' : a + 1 ≤ d) :
    mset (emptyConf d) ∈ univC₀ (Psi d a b c).B ∧
    (∀ ℓ : Lab, mset (Fin.cons {ℓ} fun _ => Set.univ : Fin (d + 1) → Set Lab) ∉
      univC₀ (Psi d a b c).B) ∧
    ¬ ∃ g' : Fin (d + 1) → Lab, mset g' ∈ (Psi d a d' b).W ∧ ∀ k, emptyConf d k ⊆ phiPsi (g' k) := by
  refine ⟨fun m' hm' => ?_, fun ℓ h => ?_, ?_⟩
  · obtain ⟨f, hf, -⟩ := rel_mset_iff.1 hm'
    simpa [emptyConf] using hf 0
  · have := h _ (rel_mset_of (f := Fin.cons ℓ fun _ => M) fun k => by
      refine Fin.cases ?_ (fun i => ?_) k <;> simp)
    have hc := (psi_B_counts ha this).1
    have hM := card_le_count (Fin.cons ℓ fun _ => M : Fin (d + 1) → Lab)
      (Finset.univ.map (Fin.succEmb d)) M (by
        simp only [Finset.mem_map, Finset.mem_univ, true_and, Fin.coe_succEmb, forall_exists_index]
        rintro k i rfl; simp)
    simp at hM
    omega
  · rintro ⟨g', hW, hsub⟩
    have hX : ∀ i : Fin d, g' i.succ = X := fun i => by
      have := hsub i.succ
      simp only [emptyConf, Fin.cons_succ] at this
      cases h : g' i.succ <;> simp_all [phiPsi, Set.univ_subset_iff, Set.ext_iff] <;>
        exact absurd (this Z) (by simp)
    have := psi_W_count_X hW
    have hc := card_le_count g' (Finset.univ.map (Fin.succEmb d)) X (by
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Fin.coe_succEmb, forall_exists_index]
      rintro k i rfl; exact hX i)
    simp at hc
    omega

end TightBipartiteMatching
