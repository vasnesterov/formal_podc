import Papers.PODC2010.EdgeDominatingSets.Theorem5Alg
import Papers.PODC2010.EdgeDominatingSets.Analysis5
import Papers.PODC2010.EdgeDominatingSets.Theorem3

/-!
# Theorem 5: `(4 - 1/k)`-approximation in graphs of maximum degree `2k` or `2k + 1`

We combine the simulation of the algorithm `alg5` (`Theorem5Alg.lean`), the properties of the
phases (`Phase5.lean`) and the combinatorial analysis (`Analysis5.lean`):

* `theorem_5_odd`: `alg5 (2k+1)` finds a `(4 - 1/k)`-approximation in every simple
  port-numbered graph of maximum degree `≤ 2k + 1`, in `T5 (2k+1) = O(k²)` rounds;
* `theorem_5_even`: the same algorithm works for maximum degree `≤ 2k` (`A(2k) = A(2k+1)`);
* `theorem_5_one`: for maximum degree `1`, the one-round algorithm `alg3` is optimal.
-/

namespace Podc.EdgeDominatingSets

open Podc.PortNumbering Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The 2-matching `P` produced by phase III. -/
noncomputable def P5 (G : PNGraph V) (Δ : ℕ) : Finset (Sym2 V) := by
  classical
  exact univ.filter fun e => ∃ u p, (phase3 G (Unm G Δ) Δ).1 u = some p ∧ G.edge u p = e

theorem mem_P5 {G : PNGraph V} {Δ : ℕ} {e : Sym2 V} :
    e ∈ P5 G Δ ↔ ∃ u p, (phase3 G (Unm G Δ) Δ).1 u = some p ∧ G.edge u p = e := by
  classical
  simp [P5]

theorem T5_eq (Δ : ℕ) : T5 Δ = Δ * Δ + 2 * ((Δ + 1) * Δ) + 2 * Δ + 2 := by
  unfold T5; ring

section

variable {G : PNGraph V} (hG : G.IsSimple) {Δ : ℕ} (hΔ : ∀ v, G.deg v ≤ Δ)
include hG hΔ

omit hΔ in
/-- The output of `alg5` selects exactly `Mfin ∪ P5`, and is consistent. -/
theorem alg5_out :
    (∀ v, (alg5 Δ).eval G (T5 Δ) (fun _ => ()) v =
      {r | r < G.deg v ∧ (G.edge v r ∈ Mfin G Δ ∨ (phase3 G (Unm G Δ) Δ).1 v = some r ∨
        (phase3 G (Unm G Δ) Δ).2 v = some r)}) := by
  intro v
  obtain ⟨hR, hp⟩ := run5_phase3 hG Δ (le_refl Δ)
  rw [alg5_eval, T5_eq, (run5_static G Δ _ v).1, (hp v).1, (hp v).2]
  ext r
  simp only [Set.mem_ofPred_eq]
  exact and_congr_right fun hr => or_congr_left (hR v r hr)

omit hΔ in
theorem outEdges_alg5 :
    outEdges G ((alg5 Δ).eval G (T5 Δ) (fun _ => ())) = Mfin G Δ ∪ P5 G Δ := by
  have hX := alg5_out (Δ := Δ) hG
  have hinv := phase3_inv G (Unm G Δ) Δ
  ext e
  rw [mem_outEdges, mem_union, mem_P5]
  constructor
  · rintro ⟨v, r, hr, hX', rfl⟩
    rw [hX] at hX'
    rcases hX'.2 with h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨v, r, h, rfl⟩
    · obtain ⟨-, h'⟩ := hinv.pout_spec v r h
      exact Or.inr ⟨_, _, h', G.edge_nbr hr⟩
  · rintro (h | ⟨u, p, hp, rfl⟩)
    · obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨e.out.1, Sym2.out_fst_mem e⟩
      obtain ⟨r, hr, rfl⟩ := exists_port_of_mem (mphase2_sub hG Δ _) h hv
      exact ⟨v, r, hr, by rw [hX]; exact ⟨hr, Or.inl h⟩, rfl⟩
    · have hpu := (hinv.pin_spec u p hp).1
      exact ⟨u, p, hpu, by rw [hX]; exact ⟨hpu, Or.inr (Or.inl hp)⟩, rfl⟩

omit hΔ in
theorem consistent_alg5 : Consistent G ((alg5 Δ).eval G (T5 Δ) (fun _ => ())) := by
  have hX := alg5_out (Δ := Δ) hG
  have hinv := phase3_inv G (Unm G Δ) Δ
  obtain ⟨hR, -⟩ := run5_phase3 hG Δ (le_refl Δ)
  intro v r hr hrX
  rw [hX] at hrX ⊢
  refine ⟨G.rport_lt hr, ?_⟩
  rcases hrX.2 with h | h | h
  · exact Or.inl (by rw [G.edge_nbr hr]; exact h)
  · exact Or.inr (Or.inr (hinv.pin_spec v r h).2.2.2)
  · exact Or.inr (Or.inl (hinv.pout_spec v r h).2)

omit hΔ in
/-- The nodes covered by `P5` are unmatched, and `P5` lies in the graph. -/
theorem P5_spec {e : Sym2 V} (he : e ∈ P5 G Δ) :
    e ∈ G.toSimpleGraph.edgeSet ∧ ∀ x ∈ e, Unm G Δ x := by
  obtain ⟨u, p, hp, rfl⟩ := mem_P5.1 he
  obtain ⟨hpd, hu, hn, -⟩ := (phase3_inv G (Unm G Δ) Δ).pin_spec u p hp
  refine ⟨G.edge_mem_edgeSet hG hpd, fun x hx => ?_⟩
  simp only [PNGraph.edge, Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · exact hu
  · exact hn

omit hG hΔ in
/-- Edges of `P5` at `v` come from `pin v` or `pout v`. -/
theorem P5_at {v : V} {e : Sym2 V} (he : e ∈ P5 G Δ) (hv : v ∈ e) :
    ∃ r, ((phase3 G (Unm G Δ) Δ).1 v = some r ∨ (phase3 G (Unm G Δ) Δ).2 v = some r) ∧
      G.edge v r = e := by
  obtain ⟨u, p, hp, rfl⟩ := mem_P5.1 he
  obtain ⟨hpd, -, -, hout⟩ := (phase3_inv G (Unm G Δ) Δ).pin_spec u p hp
  simp only [PNGraph.edge, Sym2.mem_iff] at hv
  rcases hv with rfl | rfl
  · exact ⟨p, Or.inl hp, rfl⟩
  · exact ⟨_, Or.inr hout, G.edge_nbr hpd⟩

theorem props_alg5 [DecidableRel G.toSimpleGraph.Adj] :
    Props G.toSimpleGraph (Mfin G Δ) (P5 G Δ) := by
  classical
  have hMm : IsMatching (Mfin G Δ) :=
    isMatching_mphase2 G Δ (isMatching_mphase1 G Δ _) _
  refine ⟨mphase2_sub hG Δ _, fun e he => (P5_spec (Δ := Δ) hG he).1, hMm.card_le_one, ?_, ?_, ?_, ?_⟩
  · -- (a) `P` is a 2-matching
    intro v
    set pin := (phase3 G (Unm G Δ) Δ).1
    set pout := (phase3 G (Unm G Δ) Δ).2
    have hsub : (P5 G Δ).filter (v ∈ ·) ⊆
        ((pin v).toFinset.image (G.edge v)) ∪ ((pout v).toFinset.image (G.edge v)) := by
      intro e he
      obtain ⟨he, hve⟩ := mem_filter.1 he
      obtain ⟨r, h | h, rfl⟩ := P5_at he hve
      · exact mem_union_left _ (mem_image.2 ⟨r, by simpa using h, rfl⟩)
      · exact mem_union_right _ (mem_image.2 ⟨r, by simpa using h, rfl⟩)
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    have h1 : ((pin v).toFinset.image (G.edge v)).card ≤ 1 :=
      card_image_le.trans (by cases pin v <;> simp)
    have h2 : ((pout v).toFinset.image (G.edge v)).card ≤ 1 :=
      card_image_le.trans (by cases pout v <;> simp)
    omega
  · -- (a) node-disjointness
    intro v e he hve e' he' hve'
    exact (P5_spec (Δ := Δ) hG he').2 v hve' ⟨e, he, hve⟩
  · -- (b)
    intro v hodd
    rw [G.degree_eq hG] at hodd
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 (G.dn_isSome_of_odd hodd)
    have hsub : M1 G Δ ⊆ Mfin G Δ := iterPairs_mono (subset_propStep G) Δ _ (Nat.zero_le _)
    rcases odd_cover_mphase1 hΔ hi with ⟨e, he, hve⟩ | ⟨e, he, hve⟩
    · exact Or.inl ⟨e, hsub he, hve⟩
    · exact Or.inr ⟨_, G.adj_nbr hG (G.dn_spec hi).1, e, hsub he, hve⟩
  · -- (c)
    intro u v huv
    obtain ⟨-, hU⟩ := P5_spec (Δ := Δ) hG huv
    have hu := hU u (Sym2.mem_mk_left _ _)
    have hv := hU v (Sym2.mem_mk_right _ _)
    have hadj : G.toSimpleGraph.Adj u v := (P5_spec (Δ := Δ) hG huv).1
    rw [G.degree_eq hG, G.degree_eq hG]
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨q, hq, rfl⟩ := G.exists_port_of_adj hadj.symm
      rcases maximal_mphase2 hΔ (M1 G Δ) hq hlt with h | h
      · exact hv h
      · exact hu h
    · obtain ⟨q, hq, rfl⟩ := G.exists_port_of_adj hadj
      rcases maximal_mphase2 hΔ (M1 G Δ) hq hlt with h | h
      · exact hu h
      · exact hv h

theorem isEDS_alg5 : IsEDS G.toSimpleGraph (Mfin G Δ ∪ P5 G Δ) := by
  classical
  have hinv := phase3_inv G (Unm G Δ) Δ
  refine isEDS_of_cover (fun e he => ?_) {v | Covered (Mfin G Δ ∪ P5 G Δ) v} (fun v hv => hv) ?_
  · rcases mem_union.1 he with h | h
    · exact mphase2_sub hG Δ _ e h
    · exact (P5_spec (Δ := Δ) hG h).1
  · intro u v huv
    by_cases hu : Covered (Mfin G Δ) u
    · exact Or.inl (Covered.mono subset_union_left hu)
    by_cases hv : Covered (Mfin G Δ) v
    · exact Or.inr (Covered.mono subset_union_left hv)
    obtain ⟨q, hq, rfl⟩ := G.exists_port_of_adj huv
    rcases phase3_dominates G (Unm G Δ) hΔ hq hu hv with h | h
    · left
      obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 h
      obtain ⟨hrd, hpin⟩ := hinv.pout_spec u r hr
      exact ⟨G.edge u r, mem_union_right _ (mem_P5.2 ⟨_, _, hpin, G.edge_nbr hrd⟩),
        Sym2.mem_mk_left _ _⟩
    · right
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 h
      exact ⟨_, mem_union_right _ (mem_P5.2 ⟨_, _, hp, rfl⟩), Sym2.mem_mk_left _ _⟩

end

/-- **Theorem 5** (odd maximum degree `Δ = 2k + 1`, `k ≥ 1`): the algorithm `alg5 (2k+1)` finds
a factor-`(4 - 1/k)` approximation of a minimum edge dominating set in every simple
port-numbered graph of maximum degree `≤ 2k + 1`, in `T5 (2k+1) = O(k²)` rounds. -/
theorem theorem_5_odd {k : ℕ} (hk : 1 ≤ k) (G : PNGraph V) (hG : G.IsSimple)
    (hΔ : ∀ v, G.deg v ≤ 2 * k + 1) :
    Approximates (alg5 (2 * k + 1)) (T5 (2 * k + 1)) G (4 - 1 / k) := by
  classical
  refine ⟨consistent_alg5 (Δ := 2 * k + 1) hG, ?_, ?_⟩
  · rw [outEdges_alg5 (Δ := 2 * k + 1) hG]; exact isEDS_alg5 hG hΔ
  · rw [outEdges_alg5 (Δ := 2 * k + 1) hG]
    exact card_le_edgeDomNum_of_props G.toSimpleGraph hk
      (fun v => by rw [G.degree_eq hG]; exact hΔ v) (props_alg5 hG hΔ)

/-- **Theorem 5** (even maximum degree `Δ = 2k`, `k ≥ 1`): `A(2k) = A(2k+1)` finds a
factor-`(4 - 1/k)` approximation in every simple port-numbered graph of maximum degree `≤ 2k`. -/
theorem theorem_5_even {k : ℕ} (hk : 1 ≤ k) (G : PNGraph V) (hG : G.IsSimple)
    (hΔ : ∀ v, G.deg v ≤ 2 * k) :
    Approximates (alg5 (2 * k + 1)) (T5 (2 * k + 1)) G (4 - 1 / k) :=
  theorem_5_odd hk G hG fun v => (hΔ v).trans (Nat.le_succ _)

/-- **Theorem 5** (`Δ = 1`): in graphs of maximum degree `1` the one-round algorithm `alg3` is
optimal (`α(1) = 1`). -/
theorem theorem_5_one (G : PNGraph V) (hG : G.IsSimple) (hΔ : ∀ v, G.deg v ≤ 1) :
    Approximates alg3 1 G 1 := by
  classical
  have hX := alg3_eval G
  unfold Approximates
  generalize alg3.eval G 1 (fun _ => ()) = X at hX ⊢
  have hcov : ∀ v, 0 < G.deg v → 0 ∈ X v := fun v h => by rw [hX]; exact ⟨h, Or.inl rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v i hi hiX
    rw [hX] at hiX ⊢
    refine ⟨G.rport_lt hi, Or.inl ?_⟩
    have := G.rport_lt hi
    have := hΔ (G.nbr v i)
    omega
  · refine isEDS_of_cover (outEdges_subset_edgeSet hG X) {v | 0 < G.deg v} (fun v hv => ?_)
      (fun u v huv => Or.inl ?_)
    · exact ⟨G.edge v 0, edge_mem_outEdges hv (hcov v hv), Sym2.mem_mk_left _ _⟩
    · obtain ⟨i, hi, -⟩ := G.exists_port_of_adj huv
      exact lt_of_le_of_lt (Nat.zero_le _) hi
  · obtain ⟨D, hD, hcard⟩ := exists_isEDS_card_eq G.toSimpleGraph
    have h1 := card_edgeFinset_add_le G.toSimpleGraph (Δ := 1)
      (fun v => by rw [G.degree_eq hG]; exact hΔ v) hD
    have h2 : (outEdges G X).card ≤ G.toSimpleGraph.edgeFinset.card :=
      card_le_card fun e he => by
        rw [SimpleGraph.mem_edgeFinset]; exact outEdges_subset_edgeSet hG X e he
    rw [one_mul]
    exact_mod_cast (show (outEdges G X).card ≤ edgeDomNum G.toSimpleGraph by omega)

end Podc.EdgeDominatingSets
