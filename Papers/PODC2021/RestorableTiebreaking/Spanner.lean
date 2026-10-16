import Papers.PODC2021.RestorableTiebreaking.Applications

/-!
# Lemma 32 and Theorem 33: fault-tolerant `+4` additive spanners

Bodwin–Parter, PODC 2021, Section 4.4.

* `lemma32_correct` — the deterministic correctness part of Lemma 32: if every vertex either has
  `f + 1` spanner edges to cluster centers or keeps all its edges, and the spanner contains an
  `f`-FT `C × C` preserver on the cluster centers `C`, then it is an `f`-FT `+4` additive spanner
  (for all pairs of vertices). The paper's proof forgets the case where the replacement path has
  no clustered vertex (then it lies entirely in `H`); we handle it.
* `theorem33_exponent` — the parameter balancing of Theorem 33.

The edge bound of Lemma 32 (an expectation bound for a random choice of `C`, via Chernoff bounds)
is not formalized.
-/

open Finset SimpleGraph SimpleGraph.Walk

set_option linter.unusedSectionVars false

namespace RestorableTiebreaking

variable {V : Type*} [DecidableEq V]

/-- `v` is *clustered*: it has `f + 1` neighbours in `C` via edges of `H`. -/
def Clustered (H : SimpleGraph V) (C : Set V) (f : ℕ) (v : V) : Prop :=
  ∃ T : Finset V, #T = f + 1 ∧ (T : Set V) ⊆ C ∧ ∀ c ∈ T, H.Adj v c

lemma Clustered.exists_center {H : SimpleGraph V} {C : Set V} {f : ℕ} {v : V}
    (h : Clustered H C f v) {F : Finset (Sym2 V)} (hF : #F ≤ f) :
    ∃ c ∈ C, H.Adj v c ∧ s(v, c) ∉ F := by
  obtain ⟨T, hT, hTC, hadj⟩ := h
  by_contra hcon
  push Not at hcon
  have hsub : T.image (fun c => s(v, c)) ⊆ F := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := mem_image.mp he
    exact hcon c (hTC hc) (hadj c hc)
  have hinj : Set.InjOn (fun c => s(v, c)) T := fun a _ b _ hab => Sym2.congr_right.mp hab
  have := card_le_card hsub
  rw [card_image_of_injOn hinj] at this
  omega

lemma tri3 {a b c d : V} (G : SimpleGraph V) :
    G.edist a d ≤ G.edist a b + G.edist b c + G.edist c d :=
  G.edist_triangle.trans (by rw [add_assoc]; exact add_le_add_right G.edist_triangle _)

/-- Split a walk at its first vertex satisfying `K` (if any). -/
lemma split_first (K : V → Prop) {G : SimpleGraph V} {u v : V} (q : G.Walk u v) :
    (∀ z ∈ q.support, ¬ K z) ∨ ∃ (x : V) (q₁ : G.Walk u x) (q₂ : G.Walk x v),
      q = q₁.append q₂ ∧ K x ∧ ∀ d ∈ q₁.darts, ¬ K d.fst := by
  induction q with
  | @nil a =>
    by_cases ha : K a
    · exact .inr ⟨a, nil, nil, rfl, ha, by simp⟩
    · exact .inl (by simpa using ha)
  | @cons a b c hab q ih =>
    by_cases ha : K a
    · exact .inr ⟨a, nil, cons hab q, rfl, ha, by simp⟩
    · rcases ih with h | ⟨x, q₁, q₂, rfl, hx, hq₁⟩
      · exact .inl (by simpa [ha] using h)
      · refine .inr ⟨x, cons hab q₁, q₂, rfl, hx, ?_⟩
        simp only [darts_cons, List.mem_cons, forall_eq_or_imp]
        exact ⟨ha, hq₁⟩

/-- **Lemma 32 of [Bodwin–Parter] (correctness).** Let `C` be a set of cluster centers and
`H ≤ G` a subgraph such that every vertex either is clustered (has `f + 1` `H`-edges to `C`) or
keeps all its `G`-edges in `H`, and such that `H` contains an `f`-FT `C × C` preserver `P`. Then
`H` is an `f`-FT `+4` additive spanner of `G`. -/
theorem lemma32_correct {G H P : SimpleGraph V} {C : Set V} {f : ℕ} (hHG : H ≤ G) (hPH : P ≤ H)
    (hP : IsFTPreserver G P C C f) (hcl : ∀ v, Clustered H C f v ∨ ∀ w, G.Adj v w → H.Adj v w) :
    IsFTAdditiveSpanner G H Set.univ f 4 := by
  classical
  refine ⟨hHG, fun F hF s _ t _ => ?_⟩
  by_cases hst : (G.deleteEdges F).Reachable s t
  swap
  · rw [edist_eq_top_of_not_reachable hst]; simp
  obtain ⟨q, hq⟩ := exists_isShortestIn hst
  rw [← hq.2]
  set K : V → Prop := fun v => Clustered H C f v
  -- an unclustered vertex keeps its edges, so darts leaving / entering unclustered vertices are
  -- edges of `H \ F`
  have hfst : ∀ {a b : V} (p : G.Walk a b), p.Avoids F → (∀ d ∈ p.darts, ¬ K d.fst) →
      (H.deleteEdges F).edist a b ≤ p.length := by
    intro a b p hav hK
    refine edist_le_of_darts p fun d hd => ?_
    rw [deleteEdges_adj]
    refine ⟨(hcl d.fst).resolve_left (hK d hd) _ d.adj, hav _ (List.mem_map_of_mem hd)⟩
  rcases split_first K q with hnone | ⟨x, q₁, q₂, rfl, hx, hq₁⟩
  · -- no clustered vertex: the whole path is in `H`
    refine (hfst q hq.1 fun d hd => hnone _ (q.dart_fst_mem_support_of_mem_darts hd)).trans ?_
    exact le_self_add
  · -- the last clustered vertex `y`
    rcases split_first K q₂.reverse with hnone | ⟨y, r₁, r₂, hr, hy, hr₁⟩
    · exact absurd hx (hnone x (by simp))
    have hq₂ : q₂ = r₂.reverse.append r₁.reverse := by
      rw [← reverse_append, ← hr, reverse_reverse]
    have hav := hq.1
    rw [avoids_append, hq₂, avoids_append, avoids_reverse, avoids_reverse] at hav
    obtain ⟨hav₁, hav₂, hav₃⟩ := hav
    -- the cluster centers of `x` and `y` surviving the faults
    obtain ⟨cx, hcxC, hcx, hcxF⟩ := Clustered.exists_center hx hF
    obtain ⟨cy, hcyC, hcy, hcyF⟩ := Clustered.exists_center hy hF
    have hHx : (H.deleteEdges F).Adj x cx := by rw [deleteEdges_adj]; exact ⟨hcx, hcxF⟩
    have hHy : (H.deleteEdges F).Adj cy y := by
      rw [deleteEdges_adj]; exact ⟨hcy.symm, by rwa [Sym2.eq_swap]⟩
    have hGx : (G.deleteEdges F).Adj cx x := by
      rw [deleteEdges_adj]; exact ⟨hHG hcx.symm, by rwa [Sym2.eq_swap]⟩
    have hGy : (G.deleteEdges F).Adj y cy := by rw [deleteEdges_adj]; exact ⟨hHG hcy, hcyF⟩
    -- the three pieces
    have h₁ := hfst q₁ hav₁ hq₁
    have h₃ : (H.deleteEdges F).edist y t ≤ r₁.reverse.length := by
      rw [edist_comm, length_reverse]
      exact hfst r₁ hav₃ hr₁
    have h₂ : (G.deleteEdges F).edist x y ≤ r₂.reverse.length := by
      rw [length_reverse, edist_comm]; exact hav₂.edist_le
    have hmid : (H.deleteEdges F).edist x y ≤ (G.deleteEdges F).edist x y + 4 := by
      calc (H.deleteEdges F).edist x y
          ≤ (H.deleteEdges F).edist x cx + (H.deleteEdges F).edist cx cy +
              (H.deleteEdges F).edist cy y :=
            tri3 _
        _ ≤ 1 + (P.deleteEdges F).edist cx cy + 1 :=
            add_le_add (add_le_add (edist_eq_one_iff_adj.mpr hHx).le
              (edist_anti (deleteEdges_mono hPH))) (edist_eq_one_iff_adj.mpr hHy).le
        _ = 1 + (G.deleteEdges F).edist cx cy + 1 := by rw [hP.2 F hF cx hcxC cy hcyC]
        _ ≤ 1 + ((G.deleteEdges F).edist cx x + (G.deleteEdges F).edist x y +
              (G.deleteEdges F).edist y cy) + 1 := by
            gcongr
            exact tri3 _
        _ ≤ 1 + (1 + (G.deleteEdges F).edist x y + 1) + 1 := by
            gcongr
            · exact (edist_eq_one_iff_adj.mpr hGx).le
            · exact (edist_eq_one_iff_adj.mpr hGy).le
        _ = (G.deleteEdges F).edist x y + 4 := by ring
    calc (H.deleteEdges F).edist s t
        ≤ (H.deleteEdges F).edist s x + (H.deleteEdges F).edist x y +
            (H.deleteEdges F).edist y t :=
          tri3 _
      _ ≤ q₁.length + ((G.deleteEdges F).edist x y + 4) + r₁.reverse.length := by
          gcongr
      _ ≤ q₁.length + (r₂.reverse.length + 4) + r₁.reverse.length := by gcongr
      _ = ((q₁.append (r₂.reverse.append r₁.reverse)).length : ℕ∞) + 4 := by
          simp only [length_append]; push_cast; ring
      _ = ((q₁.append q₂).length : ℕ∞) + 4 := by rw [hq₂]

/-- Exponent arithmetic of Theorem 33: with `σ = n^{1/(2^f+1)}`, both the preserver term
`n^{2 - 1/2^f} σ^{1/2^f}` and the clustering term `n² / σ` equal `n^{1 + 2^f/(2^f+1)}`. -/
theorem theorem33_exponent (n : ℝ) (hn : 0 < n) (f : ℕ) :
    let σ := n ^ (1 / ((2 : ℝ) ^ f + 1))
    n ^ (2 - 1 / (2 : ℝ) ^ f) * σ ^ (1 / (2 : ℝ) ^ f) = n ^ (1 + (2 : ℝ) ^ f / (2 ^ f + 1)) ∧
      n ^ (2 : ℝ) / σ = n ^ (1 + (2 : ℝ) ^ f / (2 ^ f + 1)) := by
  intro σ
  have h2 : (0 : ℝ) < 2 ^ f := by positivity
  constructor
  · rw [← Real.rpow_mul hn.le, ← Real.rpow_add hn]
    congr 1
    field_simp
    ring
  · rw [← Real.rpow_sub hn]
    congr 1
    field_simp
    ring

end RestorableTiebreaking
