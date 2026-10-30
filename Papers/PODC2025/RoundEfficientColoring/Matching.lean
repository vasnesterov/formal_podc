import Papers.PODC2025.RoundEfficientColoring.Model

/-!
# Lemma 5.3: a matching covering all vertices of maximum degree

Chang–Mishra–Nguyen–Salim, PODC 2025, Lemma 5.3: in a graph with maximum degree `Δ` in which the
vertices of degree `Δ` form an independent set, there is a matching covering every vertex of
degree `Δ` (a "`Δ`-perfect matching"). The paper argues via the integrality of the bipartite
fractional matching polytope; we use Hall's theorem directly (double counting: `Δ |S|` edges leave
a set `S` of degree-`Δ` vertices and every vertex receives at most `Δ` of them).

The lemma needs `Δ ≥ 1` (or no vertex of degree `Δ`): for `Δ = 0` a graph with one isolated
vertex is a counterexample (`lemma_5_3_false_of_zero`).

The matching is described by an injective map `f` from the vertices of degree `k` to their
neighbours; its edges are `s(u, f u)`. Since `f u` has a neighbour of degree `k`, `f u` has degree
`< k`, so the edges are pairwise disjoint.
-/

namespace Podc.RoundEfficientColoring

open SimpleGraph Finset

variable {V : Type*} [Finite V]

/-- **Lemma 5.3** of [CMNS25] (for `k ≥ 1`): if `G` has maximum degree `≤ k` and no two vertices
of degree `k` are adjacent, there is an injective choice `f u` of a neighbour of every vertex `u`
of degree `k`. -/
theorem lemma_5_3 (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k) :
    ∃ f : V → V, (∀ u, (G.neighborSet u).ncard = k → G.Adj u (f u)) ∧
      ∀ u u', (G.neighborSet u).ncard = k → (G.neighborSet u').ncard = k → f u = f u' → u = u' := by
  classical
  let ι := {u : V // (G.neighborSet u).ncard = k}
  let t : ι → Finset V := fun u => (Set.toFinite (G.neighborSet u.1)).toFinset
  have hcard : ∀ u : ι, #(t u) = k := fun u => by
    rw [← u.2, Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  have hall : ∀ s : Finset ι, #s ≤ #(s.biUnion t) := by
    intro s
    have h := Finset.card_mul_le_card_mul (r := fun (u : ι) (w : V) => G.Adj u.1 w)
      (s := s) (t := s.biUnion t) (m := k) (n := k) (fun u hu => ?_) (fun w hw => ?_)
    · exact Nat.le_of_mul_le_mul_right h hk
    · refine (hcard u).symm.le.trans (Finset.card_le_card fun w hw => ?_)
      simp only [t, Set.Finite.mem_toFinset, mem_neighborSet] at hw
      simp only [bipartiteAbove, Finset.mem_filter, Finset.mem_biUnion]
      exact ⟨⟨u, hu, by simpa [t] using hw⟩, hw⟩
    · calc #(s.bipartiteBelow (fun (u : ι) (w : V) => G.Adj u.1 w) w)
          ≤ #((s.bipartiteBelow (fun (u : ι) (w : V) => G.Adj u.1 w) w).map
            (Function.Embedding.subtype _)) := by rw [Finset.card_map]
        _ ≤ #((Set.toFinite (G.neighborSet w)).toFinset) := by
          refine Finset.card_le_card fun x hx => ?_
          simp only [Finset.mem_map, bipartiteBelow, Finset.mem_filter,
            Function.Embedding.coe_subtype] at hx
          obtain ⟨u, ⟨-, hu⟩, rfl⟩ := hx
          simpa using hu.symm
        _ = (G.neighborSet w).ncard := (Set.ncard_eq_toFinset_card _ _).symm
        _ ≤ k := hdeg w
  obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  refine ⟨fun u => if h : (G.neighborSet u).ncard = k then f ⟨u, h⟩ else u,
    fun u hu => ?_, fun u u' hu hu' he => ?_⟩
  · simp only [dite_eq_left hu]
    simpa [t] using hf ⟨u, hu⟩
  · simp only [dite_eq_left hu, dite_eq_left hu'] at he
    exact congrArg Subtype.val (hfinj he)

/-- **Lemma 5.3** of [CMNS25] in the paper's form (for `k ≥ 1`): if `G` has maximum degree `≤ k`
and the vertices of degree `k` form an independent set, then there is a matching `M ≤ G` (every
vertex has at most one `M`-neighbour) covering every vertex of degree `k` (a "`k`-perfect
matching"). -/
theorem lemma_5_3_matching (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k)
    (hind : ∀ ⦃u v⦄, G.Adj u v → (G.neighborSet u).ncard = k → (G.neighborSet v).ncard ≠ k) :
    ∃ M ≤ G, (∀ v, (M.neighborSet v).ncard ≤ 1) ∧
      ∀ u, (G.neighborSet u).ncard = k → ∃ w, M.Adj u w := by
  obtain ⟨f, hf, hfinj⟩ := lemma_5_3 G hk hdeg
  let M := SimpleGraph.fromRel fun u v => (G.neighborSet u).ncard = k ∧ v = f u
  refine ⟨M, fun a b h => ?_, fun v => ?_, fun u hu => ⟨f u, ?_⟩⟩
  · obtain ⟨-, ⟨ha, rfl⟩ | ⟨hb, rfl⟩⟩ := (fromRel_adj _ _ _).mp h
    · exact hf a ha
    · exact (hf b hb).symm
  · refine (Set.ncard_le_one (Set.toFinite _)).mpr fun a ha b hb => ?_
    have key : ∀ w, M.Adj v w → ((G.neighborSet v).ncard = k ∧ w = f v) ∨
        ((G.neighborSet w).ncard = k ∧ v = f w) := fun w h => ((fromRel_adj _ _ _).mp h).2
    by_cases hv : (G.neighborSet v).ncard = k
    · have hfv : ∀ w, M.Adj v w → w = f v := fun w h => by
        rcases key w h with ⟨-, h1⟩ | ⟨hw, rfl⟩
        · exact h1
        · exact absurd hv (hind (hf w hw) hw)
      rw [hfv a ha, hfv b hb]
    · rcases key a ha with ⟨h1, -⟩ | ⟨ha', hva⟩
      · exact absurd h1 hv
      rcases key b hb with ⟨h1, -⟩ | ⟨hb', hvb⟩
      · exact absurd h1 hv
      exact hfinj a b ha' hb' (hva.symm.trans hvb)
  · exact (fromRel_adj _ _ _).mpr ⟨(hf u hu).ne, Or.inl ⟨hu, rfl⟩⟩

/-- Lemma 5.3 is false for `Δ = 0`: a single vertex has maximum degree `0`, the (only) vertex of
degree `0` forms an independent set, but no matching covers it. -/
theorem lemma_5_3_false_of_zero :
    ¬ ∃ f : Unit → Unit, ∀ u, ((⊥ : SimpleGraph Unit).neighborSet u).ncard = 0 →
      (⊥ : SimpleGraph Unit).Adj u (f u) := by
  rintro ⟨f, hf⟩
  exact hf () (by simp) |>.elim

end Podc.RoundEfficientColoring
