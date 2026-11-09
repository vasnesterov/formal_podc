import Papers.PODC2017.FenceInsertionChain.Basic

/-!
# Multi-cut and the reduction of fence insertion to chain multi-cut (Definition 2.3, Lemma 2.4)

* `IsMultiCut G T C` — **Definition 2.3**: `C ⊆ E` and no terminal pair `(s, t) ∈ T` is connected
  in `⟨V, E \ C⟩`; `IsMinMultiCut` — a minimum-size multi-cut.
* `chainEdge k = {v_k, v_{k+1}}` — the edges of the chain `pathGraph n` (Mathlib's path graph on
  `Fin n`).
* `reachable_deleteEdges_iff` — on a chain, `v_a` and `v_b` (`a ≤ b`) stay connected after deleting
  `C` iff no edge `{v_k, v_{k+1}}` with `a ≤ k < b` is in `C`.

## Lemma 2.4

The instance of `MultiCut` built from a fence insertion instance `⟨p, →⟩` is the chain on the `|p|`
operations with terminal pairs `T = →`. The two solution maps of the paper:

* `edgesOf F = {{v_k, v_{k+1}} | k ∈ F}` (dropping `k = |p|-1`, whose edge does not exist):
  `isMultiCut_edgesOf`, `card_edgesOf_le`;
* `cutIdx C = {k | {v_k, v_{k+1}} ∈ C}`: `isIns1_cutIdx`, `card_cutIdx`.

`lemma_2_4` — both maps send optimal solutions to optimal solutions, and the optima have equal size.
-/

namespace Podc.FenceInsertionChain

open Finset SimpleGraph

section MultiCut

variable {V : Type*}

/-- **Definition 2.3** (multi-cut): a set `C ⊆ E` of edges such that for every terminal pair
`(s, t) ∈ T` there is no path between `s` and `t` in `⟨V, E \ C⟩`. -/
def IsMultiCut (G : SimpleGraph V) (T : Finset (V × V)) (C : Finset (Sym2 V)) : Prop :=
  (C : Set (Sym2 V)) ⊆ G.edgeSet ∧ ∀ p ∈ T, ¬ (G.deleteEdges C).Reachable p.1 p.2

/-- A minimum-size multi-cut (a solution of `MultiCut`). -/
def IsMinMultiCut (G : SimpleGraph V) (T : Finset (V × V)) (C : Finset (Sym2 V)) : Prop :=
  IsMultiCut G T C ∧ ∀ C', IsMultiCut G T C' → C.card ≤ C'.card

/-- A terminal pair `(v, v)` cannot be cut: no multi-cut exists. -/
theorem not_isMultiCut_of_diag {G : SimpleGraph V} {T : Finset (V × V)} {v : V}
    (hv : (v, v) ∈ T) (C : Finset (Sym2 V)) : ¬ IsMultiCut G T C :=
  fun h => h.2 _ hv (Reachable.refl _)

end MultiCut

variable {n : ℕ}

/-- The successor of `k` on the chain, or `k` itself for the last vertex. -/
def succV (k : Fin n) : Fin n := ⟨min (k.val + 1) (n - 1), by have := k.isLt; omega⟩

theorem succV_val {k : Fin n} (hk : k.val + 1 < n) : (succV k).val = k.val + 1 := by
  simp [succV]; omega

/-- The edge `{v_k, v_{k+1}}` of the chain (a loop `s(k, k)` for the last vertex, which is not an
edge). -/
def chainEdge (k : Fin n) : Sym2 (Fin n) := s(k, succV k)

theorem chainEdge_mem_edgeSet {k : Fin n} (hk : k.val + 1 < n) :
    chainEdge k ∈ (pathGraph n).edgeSet := by
  simp [chainEdge, pathGraph_adj, succV_val hk]

theorem chainEdge_injOn :
    Set.InjOn (chainEdge (n := n)) {k | k.val + 1 < n} := by
  intro a ha b hb h
  simp only [Set.mem_ofPred_eq] at ha hb
  simp only [chainEdge, Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · have := congrArg Fin.val h1; have := congrArg Fin.val h2
    rw [succV_val hb] at *; rw [succV_val ha] at *; omega

/-- Every edge of the chain is a `chainEdge`. -/
theorem exists_chainEdge {e : Sym2 (Fin n)} (he : e ∈ (pathGraph n).edgeSet) :
    ∃ k : Fin n, k.val + 1 < n ∧ chainEdge k = e := by
  induction e using Sym2.ind with
  | _ u v =>
  rw [mem_edgeSet, pathGraph_adj] at he
  rcases he with h | h
  · refine ⟨u, by omega, ?_⟩
    simp only [chainEdge]
    congr 1
    ext; rw [succV_val (by omega)]; omega
  · refine ⟨v, by omega, ?_⟩
    simp only [chainEdge, Sym2.eq_swap (a := u)]
    congr 1
    ext; rw [succV_val (by omega)]; omega

-- CSLib candidate
/-- On a chain, `v_a` and `v_b` with `a ≤ b` remain connected after deleting the edges `C` iff no
edge `{v_k, v_{k+1}}` with `a ≤ k < b` is deleted. -/
theorem reachable_deleteEdges_iff (C : Set (Sym2 (Fin n))) {a b : Fin n} (hab : a ≤ b) :
    ((pathGraph n).deleteEdges C).Reachable a b ↔ ∀ k : Fin n, a ≤ k → k < b → chainEdge k ∉ C := by
  constructor
  · intro hr k hak hkb hk
    rw [reachable_iff_reflTransGen] at hr
    have key : ∀ v, Relation.ReflTransGen ((pathGraph n).deleteEdges C).Adj a v → v ≤ k := by
      intro v hv
      induction hv with
      | refl => exact hak
      | @tail x y _ hxy ih =>
        rw [deleteEdges_adj, pathGraph_adj] at hxy
        obtain ⟨hxy | hxy, hnot⟩ := hxy
        · rcases (Fin.le_iff_val_le_val.1 ih).lt_or_eq with h | h
          · exact Fin.le_iff_val_le_val.2 (by omega)
          · exfalso; apply hnot
            have hk1 : k.val + 1 < n := by have := y.isLt; omega
            have hx : x = k := Fin.ext h
            subst hx
            have : y = succV x := Fin.ext (by rw [succV_val hk1]; omega)
            subst this
            exact hk
        · exact Fin.le_iff_val_le_val.2 (by have := Fin.le_iff_val_le_val.1 ih; omega)
    exact absurd (key b hr) (not_le.2 hkb)
  · intro h
    have : ∀ t, a.val + t ≤ b.val → ∀ hlt : a.val + t < n,
        ((pathGraph n).deleteEdges C).Reachable a ⟨a.val + t, hlt⟩ := by
      intro t
      induction t with
      | zero => intro _ _; exact Reachable.refl _
      | succ t ih =>
        intro ht hlt
        refine (ih (by omega) (by omega)).trans (Adj.reachable ?_)
        rw [deleteEdges_adj, pathGraph_adj]
        refine ⟨Or.inl rfl, ?_⟩
        have hk := h ⟨a.val + t, by omega⟩ (Fin.le_iff_val_le_val.2 (by simp))
          (Fin.lt_def.2 (by simp; omega))
        convert hk using 2
        simp only [chainEdge]
        congr 1
        ext; rw [succV_val (by simp; omega)]; simp; omega
    have := this (b.val - a.val) (by have := Fin.le_iff_val_le_val.1 hab; omega) (by omega)
    convert this
    have := Fin.le_iff_val_le_val.1 hab; omega

/-- A terminal pair `(s, t)` is separated by deleting `C` iff `C` contains an edge between them. -/
theorem not_reachable_iff (C : Set (Sym2 (Fin n))) (s t : Fin n) :
    ¬ ((pathGraph n).deleteEdges C).Reachable s t ↔
      ∃ k : Fin n, min s t ≤ k ∧ k < max s t ∧ chainEdge k ∈ C := by
  rcases le_total s t with h | h
  · rw [reachable_deleteEdges_iff C h, min_eq_left h, max_eq_right h]
    push Not; rfl
  · rw [reachable_comm, reachable_deleteEdges_iff C h, min_eq_right h, max_eq_left h]
    push Not; rfl

/-! ### Lemma 2.4 -/

/-- The paper's map from fence insertions to edge sets, `F ↦ {{v_k, v_{k+1}} | k ∈ F}`; a fence
after the last operation has no edge and is dropped. -/
def edgesOf (F : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  (F.filter fun k => k.val + 1 < n).image chainEdge

/-- The paper's map from edge sets to fence insertions, `{{v_k, v_{k+1}} | …} ↦ {k | …}`. -/
def cutIdx (C : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  univ.filter fun k => k.val + 1 < n ∧ chainEdge k ∈ C

/-- `edgesOf` does not increase the size. -/
theorem card_edgesOf_le (F : Finset (Fin n)) : (edgesOf F).card ≤ F.card :=
  card_image_le.trans (card_filter_le _ _)

-- CSLib candidate
/-- An edge set of the chain has as many edges as `cutIdx` has indices. -/
theorem card_cutIdx {C : Finset (Sym2 (Fin n))}
    (hC : (C : Set (Sym2 (Fin n))) ⊆ (pathGraph n).edgeSet) :
    (cutIdx C).card = C.card := by
  refine card_nbij chainEdge (fun k hk => (mem_filter.1 hk).2.2) ?_ ?_
  · intro a ha b hb h
    exact chainEdge_injOn (mem_filter.1 ha).2.1 (mem_filter.1 hb).2.1 h
  · intro e he
    obtain ⟨k, hk, rfl⟩ := exists_chainEdge (hC he)
    exact ⟨k, by simpa [cutIdx] using ⟨hk, he⟩, rfl⟩

variable {ord : Finset (Fin n × Fin n)}

/-- A fence insertion gives a multi-cut of the chain with terminal pairs `→`. -/
theorem isMultiCut_edgesOf (hlt : ∀ x ∈ ord, x.1 < x.2) {F : Finset (Fin n)} (hF : IsIns1 ord F) :
    IsMultiCut (pathGraph n) ord (edgesOf F) := by
  refine ⟨fun e he => ?_, fun x hx => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := mem_image.1 (mem_coe.1 he)
    exact chainEdge_mem_edgeSet (mem_filter.1 hk).2
  · obtain ⟨k, hk, h1, h2⟩ := hF x hx
    have hle := (hlt x hx).le
    rw [not_reachable_iff, min_eq_left hle, max_eq_right hle]
    refine ⟨k, h1, h2, mem_coe.2 (mem_image_of_mem _ (mem_filter.2 ⟨hk, ?_⟩))⟩
    have := x.2.isLt; have := Fin.lt_def.1 h2; omega

/-- A multi-cut of the chain gives a fence insertion of the same size. -/
theorem isIns1_cutIdx (hlt : ∀ x ∈ ord, x.1 < x.2) {C : Finset (Sym2 (Fin n))}
    (hC : IsMultiCut (pathGraph n) ord C) : IsIns1 ord (cutIdx C) := by
  intro x hx
  have hle := (hlt x hx).le
  obtain ⟨k, h1, h2, h3⟩ := (not_reachable_iff _ _ _).1 (hC.2 x hx)
  rw [min_eq_left hle] at h1
  rw [max_eq_right hle] at h2
  refine ⟨k, mem_filter.2 ⟨mem_univ _, ?_, h3⟩, h1, h2⟩
  have := x.2.isLt; have := Fin.lt_def.1 h2; omega

/-- **Lemma 2.4** (`FenceIns ≤ MultiCut`): with `G` the chain on the `|p|` operations and `T = →`,
the paper's two solution maps send minimum fence insertions to minimum multi-cuts and back, and
the two optima have the same size. -/
theorem lemma_2_4 (hlt : ∀ x ∈ ord, x.1 < x.2) :
    (∀ F, IsOptIns1 ord F → IsMinMultiCut (pathGraph n) ord (edgesOf F)) ∧
    (∀ C, IsMinMultiCut (pathGraph n) ord C → IsOptIns1 ord (cutIdx C)) ∧
    (∀ F C, IsOptIns1 ord F → IsMinMultiCut (pathGraph n) ord C → F.card = C.card) := by
  refine ⟨fun F hF => ⟨isMultiCut_edgesOf hlt hF.1, fun C' hC' => ?_⟩,
    fun C hC => ⟨isIns1_cutIdx hlt hC.1, fun G hG => ?_⟩, fun F C hF hC => ?_⟩
  · calc (edgesOf F).card ≤ F.card := card_edgesOf_le F
      _ ≤ (cutIdx C').card := hF.2 _ (isIns1_cutIdx hlt hC')
      _ = C'.card := card_cutIdx hC'.1
  · calc (cutIdx C).card = C.card := card_cutIdx hC.1.1
      _ ≤ (edgesOf G).card := hC.2 _ (isMultiCut_edgesOf hlt hG)
      _ ≤ G.card := card_edgesOf_le G
  · refine le_antisymm ?_ ?_
    · exact (hF.2 _ (isIns1_cutIdx hlt hC.1)).trans (card_cutIdx hC.1.1).le
    · exact (hC.2 _ (isMultiCut_edgesOf hlt hF.1)).trans (card_edgesOf_le F)

end Podc.FenceInsertionChain
