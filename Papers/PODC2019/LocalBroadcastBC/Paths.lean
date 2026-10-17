import Papers.PODC2019.LocalBroadcastBC.Phase
import Cslib.Foundations.Combinatorics.SimpleGraph.Menger
import Cslib.Foundations.Combinatorics.SimpleGraph.Spanner

/-!
# Existence of the paths used by Algorithm 1: Lemmas 5.4 and 5.5 of [KNV19]

* `exists_selSpec` (Lemma 5.4): a path selection for step (b) exists. Only
  `(f + 1)`-connectivity *after removing at most `f` vertices* is needed; Menger's theorem is not.
* `pathsExist` (Lemma 5.5): for every `Z` and `w ∈ B_w` there are `f + 1` node-disjoint
  `A_w w`-paths that exclude `F`. Cases 1 and 3 use the fan lemma (`SimpleGraph.fan`, proved in
  `Cslib/Foundations/Combinatorics/SimpleGraph/Menger.lean`) in `G` with the vertices
  `B'_w = (B_w ∩ F) \ {w}` removed (CSLib's `SimpleGraph.deleteVerts`); cases 2 and 4 use the
  minimum degree.
-/

open Finset

namespace LocalBroadcastBC

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : ℕ}

/-! ### Lists of vertices of walks -/

omit [Fintype V] [DecidableEq V] in
lemma walk_support_spec {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    IsPathList G p.support ∧ p.support.head? = some a ∧ p.support.getLast? = some b := by
  refine ⟨⟨p.isChain_adj_support, hp.support_nodup⟩, ?_, ?_⟩
  · rw [List.head?_eq_some_head p.support_ne_nil, p.head_support]
  · rw [List.getLast?_eq_some_getLast p.support_ne_nil, p.getLast_support]

omit [Fintype V] [DecidableEq V] in
lemma ne_head_of_mem_internal {l : List V} {a x : V} (hl : l.Nodup) (ha : l.head? = some a)
    (hx : x ∈ internal l) : x ≠ a := by
  rcases l with _ | ⟨b, t⟩
  · simp at ha
  · simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    rintro rfl
    simp only [internal, List.tail_cons] at hx
    exact (List.nodup_cons.1 hl).1 (List.dropLast_subset _ hx)

omit [Fintype V] [DecidableEq V] in
lemma ne_last_of_mem_internal {l : List V} {b x : V} (hl : l.Nodup) (hb : l.getLast? = some b)
    (hx : x ∈ internal l) : x ≠ b := by
  rintro rfl
  have h1 : x ∈ l.dropLast := by
    simp only [internal] at hx
    rw [← List.tail_dropLast] at hx
    exact List.mem_of_mem_tail hx
  have hl' := List.dropLast_append_getLast? x hb
  rw [← hl', List.nodup_append] at hl
  exact hl.2.2 x h1 x (by simp) rfl

/-! ### Lemma 5.4 -/

/-- One path for Lemma 5.4. -/
lemma exists_path_excluding (hconn : G.IsVertexConnected (3 * f / 2 + 1)) {F : Finset V}
    (hF : F.card ≤ f) {u v : V} :
    ∃ P : List V, IsPathList G P ∧ P.head? = some u ∧ P.getLast? = some v ∧
      ∀ x ∈ internal P, x ∉ F := by
  classical
  have hX : ((F.erase u).erase v).card < 3 * f / 2 + 1 := by
    have h1 := card_erase_le (s := F.erase u) (a := v)
    have h2 := card_erase_le (s := F) (a := u)
    omega
  obtain ⟨p, hp⟩ := hconn.2 _ hX u v (by simp) (by simp)
  obtain ⟨hP, hh, hl⟩ := walk_support_spec p.bypass p.bypass_isPath
  refine ⟨p.bypass.support, hP, hh, hl, fun x hx hxF => ?_⟩
  have hxu := ne_head_of_mem_internal hP.2 hh hx
  have hxv := ne_last_of_mem_internal hP.2 hl hx
  exact hp x (p.support_bypass_subset_support (mem_of_mem_internal hx))
    (by simp [hxu, hxv, hxF])

/-- **Lemma 5.4** of [KNV19]: in a `(⌊3f/2⌋ + 1)`-connected graph, a path selection for step (b)
exists. -/
theorem exists_selSpec (hconn : G.IsVertexConnected (3 * f / 2 + 1)) :
    ∃ sel : Finset V → V → V → List V, SelSpec G f sel := by
  classical
  refine ⟨fun F u v => if h : F.card ≤ f then (exists_path_excluding hconn h (u := u) (v := v)).choose
    else [], fun F hF u v _ => ?_⟩
  simp only [hF, dite_true]
  exact (exists_path_excluding hconn hF).choose_spec

/-! ### Lemma 5.5 -/

/-- Cases 1 and 3 of the proof of Lemma 5.5 (via the fan lemma). -/
lemma disjointPaths_fan (hconn : G.IsVertexConnected (3 * f / 2 + 1)) {F A B : Finset V}
    (hF : F.card ≤ f) (hAB : B = univ \ A) {w : V} (hw : w ∈ B) (hA : f < A.card)
    (hBF : (B ∩ F).card ≤ f / 2) : DisjointPaths G f F A w := by
  classical
  have hwA : w ∉ A := by simp [hAB] at hw; exact hw
  -- `A'`: `f + 1` nodes of `A`, including all of `A ∩ F`
  obtain ⟨A', hA'F, hA'A, hA'card⟩ := exists_subsuperset_card_eq (s := A ∩ F) (t := A)
    (n := f + 1) inter_subset_left
    (by have := card_le_card (inter_subset_right (s₁ := A) (s₂ := F)); omega) hA
  set B' := (B ∩ F).erase w with hB'
  have hB'card : B'.card ≤ f / 2 := (card_erase_le).trans hBF
  have hwB' : w ∉ B' := by simp [hB']
  have hA'B' : ∀ x ∈ A', x ∉ B' := fun x hx hxB => by
    have : x ∈ B := (mem_inter.1 (mem_of_mem_erase hxB)).1
    simp [hAB, hA'A hx] at this
  set G' := G.deleteVerts (B' : Set V)
  have hwA' : w ∉ A' := fun h => hwA (hA'A h)
  obtain ⟨P, hPU, hPdisj⟩ := SimpleGraph.fan G' w A' hwA' (f + 1) (by
    intro X hwX hXcard
    obtain ⟨u, hu⟩ : (A' \ X).Nonempty := by
      rw [← card_pos]
      have := le_card_sdiff X A'
      omega
    rw [mem_sdiff] at hu
    have hY : (X ∪ B').card < 3 * f / 2 + 1 := by
      have := card_union_le X B'
      omega
    obtain ⟨p, hp⟩ := hconn.2 (X ∪ B') hY w u (by simp [hwX, hwB']) (by simp [hu.2, hA'B' u hu.1])
    have hpB : ∀ x ∈ p.support, x ∉ (B' : Set V) := fun x hx hxB => hp x hx (by simp [mem_coe.1 hxB])
    exact ⟨u, hu.1, p.toDeleteVerts hpB, fun x hx hxX =>
      hp x (by simpa using hx) (by simp [mem_coe.1 hxX])⟩)
  -- the lists `u_i … w`
  let W : ∀ i : Fin (f + 1), G.Walk (P i).1 w := fun i => ((P i).2.mapLe (G.deleteVerts_le _)).reverse
  have hWsupp : ∀ i, (W i).support = (P i).2.support.reverse := fun i => by
    simp [W]
  have hWpath : ∀ i, (W i).IsPath := fun i => ((hPU i).2.mapLe _).reverse
  let L : Fin (f + 1) → List V := fun i => (W i).support
  have hLspec := fun i => walk_support_spec (W i) (hWpath i)
  have hmemL : ∀ i x, x ∈ L i ↔ x ∈ (P i).2.support := fun i x => by
    simp [L, hWsupp]
  -- endpoints are injective, hence hit all of `A'`
  have hend_inj : Function.Injective (fun i => (P i).1) := by
    intro i j hij
    by_contra hne
    have := hPdisj i j hne (P i).1 (P i).2.end_mem_support (by simp only at hij; rw [hij]; exact (P j).2.end_mem_support)
    exact hwA' (this ▸ (hPU i).1)
  have himage : univ.image (fun i => (P i).1) = A' := by
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, -, rfl⟩ := mem_image.1 hx
      exact (hPU i).1
    · rw [card_image_of_injective _ hend_inj, card_univ, Fintype.card_fin, hA'card]
  have hL_inj : Function.Injective L := by
    intro i j hij
    have h1 := (hLspec i).2.1
    have h2 := (hLspec j).2.1
    simp only [L] at hij
    rw [hij, h2, Option.some.injEq] at h1
    exact hend_inj h1.symm
  refine ⟨univ.image L, by rw [card_image_of_injective _ hL_inj, card_univ, Fintype.card_fin],
    ?_, ?_⟩
  · intro Q hQ
    obtain ⟨i, -, rfl⟩ := mem_image.1 hQ
    obtain ⟨hpath, hh, hl⟩ := hLspec i
    refine ⟨hpath, ⟨(P i).1, hA'A (hPU i).1, hh⟩, hl, fun x hx hxF => ?_⟩
    have hx1 := ne_head_of_mem_internal hpath.2 hh hx
    have hx2 := ne_last_of_mem_internal hpath.2 hl hx
    have hxP : x ∈ (P i).2.support := (hmemL i x).1 (mem_of_mem_internal hx)
    by_cases hxA : x ∈ A
    · -- `x ∈ A ∩ F ⊆ A'` is the endpoint of another path
      have : x ∈ univ.image (fun i => (P i).1) := himage ▸ hA'F (mem_inter.2 ⟨hxA, hxF⟩)
      obtain ⟨j, -, hj⟩ := mem_image.1 this
      by_cases hij : i = j
      · subst hij; exact hx1 hj.symm
      · exact hx2 (hPdisj i j hij x hxP (hj ▸ (P j).2.end_mem_support))
    · have hxB' : x ∈ B' := by
        simp [hB', hAB, hxA, hxF, hx2]
      exact (P i).2.not_mem_of_mem_support_deleteVerts (by simpa using hwB') x hxP (by simpa using hxB')
  · intro Q hQ Q' hQ' hne x hx hx'
    obtain ⟨i, -, rfl⟩ := mem_image.1 hQ
    obtain ⟨j, -, rfl⟩ := mem_image.1 hQ'
    have hij : i ≠ j := fun h => hne (h ▸ rfl)
    exact hPdisj i j hij x ((hmemL i x).1 hx) ((hmemL j x).1 hx')

/-- Cases 2 and 4 of the proof of Lemma 5.5 (via the minimum degree). -/
lemma disjointPaths_degree [DecidableRel G.Adj] (hdeg : 2 * f ≤ G.minDegree) {F A B : Finset V}
    (hAB : B = univ \ A) {w : V} (hw : w ∈ B) (hB : B.card ≤ f) : DisjointPaths G f F A w := by
  classical
  have hwA : w ∉ A := by simp [hAB] at hw; exact hw
  set N := G.neighborFinset w
  have hdw : 2 * f ≤ N.card := by
    rw [G.card_neighborFinset_eq_degree]; exact hdeg.trans (G.minDegree_le_degree w)
  have hsd : N \ A ⊆ B.erase w := by
    intro x hx
    rw [mem_sdiff] at hx
    have hxw : x ≠ w := fun h => by subst h; simp [N] at hx
    simp [hAB, hx.2, hxw]
  have h1 := card_le_card hsd
  have h2 := card_erase_of_mem hw
  have h3 := card_inter_add_card_sdiff N A
  have hpos : 0 < B.card := card_pos.2 ⟨w, hw⟩
  obtain ⟨T, hTN, hTcard⟩ := exists_subset_card_eq (s := N ∩ A) (n := f + 1) (by omega)
  have hinj : Function.Injective (fun a : V => [a, w]) := fun a b h => by simpa using h
  refine ⟨T.image (fun a => [a, w]), by rw [card_image_of_injective _ hinj, hTcard], ?_, ?_⟩
  · intro Q hQ
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hQ
    have haN := mem_inter.1 (hTN ha)
    have hadj : G.Adj a w := ((G.mem_neighborFinset w a).1 haN.1).symm
    refine ⟨⟨by simp [hadj], by simp [hadj.ne]⟩, ⟨a, haN.2, rfl⟩, by simp, by simp [internal]⟩
  · intro Q hQ Q' hQ' hne x hx hx'
    obtain ⟨a, -, rfl⟩ := mem_image.1 hQ
    obtain ⟨b, -, rfl⟩ := mem_image.1 hQ'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hx'
    rcases hx with rfl | rfl
    · rcases hx' with rfl | rfl
      · exact absurd rfl hne
      · rfl
    · rfl

/-- **Lemma 5.5** of [KNV19]: if `G` has minimum degree `≥ 2f` and is `(⌊3f/2⌋ + 1)`-connected,
then in every phase every `w ∈ B_w` has `f + 1` node-disjoint `A_w w`-paths excluding `F`. -/
theorem pathsExist [DecidableRel G.Adj] (hdeg : 2 * f ≤ G.minDegree)
    (hconn : G.IsVertexConnected (3 * f / 2 + 1)) : PathsExist G f := by
  classical
  intro F hF Z w hw
  unfold sets at hw ⊢
  have hZF : (Z ∩ F).card + ((univ \ Z) ∩ F).card = F.card := by
    rw [← card_union_of_disjoint (disjoint_left.2 fun x h1 h2 => by simp_all)]
    congr 1
    ext x; by_cases x ∈ Z <;> simp_all
  have hZZ : Z.card + (univ \ Z).card = Fintype.card V := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
    have := card_le_univ Z
    omega
  split_ifs at hw ⊢ with h1 h2 h3 <;> simp only at hw ⊢
  · -- Case 1
    exact disjointPaths_fan hconn hF (by simp) hw h2 h1
  · -- Case 2
    exact disjointPaths_degree hdeg rfl hw (by omega)
  · -- Case 3
    exact disjointPaths_fan hconn hF rfl hw h3 (by omega)
  · -- Case 4
    exact disjointPaths_degree hdeg (by simp) hw (by omega)

end LocalBroadcastBC
