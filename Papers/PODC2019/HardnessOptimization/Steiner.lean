import Papers.PODC2019.HardnessOptimization.MDSTheorem

/-!
# Section 2.3: minimum Steiner tree (Claim 2.8, Theorem 2.7)

From the MDS graph `G_{x,y}` on `V = V_A ∪ V_B` build `G'_{x,y}` on `V ∪ Ṽ` (`Ṽ` a copy of `V`):
1. identity edges `ṽ – v`; 2. original edges `ũ – v` for every edge `{u, v}` of `G_{x,y}`;
3. clique edges inside `Ṽ_A` and inside `Ṽ_B`; 4. two crossing edges `f̃⁰_{A₁} – f̃⁰_{B₁}` and
`t̃⁰_{A₁} – t̃⁰_{B₁}`. Terminals: `Term = V`. Claim 2.8: there is a Steiner tree with
`4k + 16 log k + 1` edges iff `DISJ(x, y) = FALSE`.

We need `log k ≥ 1` (`[NeZero L]`): for `k = 1` there are no crossing edges and `G'` is
disconnected.
-/

namespace HardnessOptimization

open Finset Podc.CongestLB

/-- A Steiner tree for the terminals `Term` with at most `M` edges: a tree `T` on a vertex set
`W ⊇ Term`, all of whose edges are edges of `G`. -/
def HasSteinerTreeLE {V : Type*} (G : SimpleGraph V) (Term : Set V) (M : ℕ) : Prop :=
  ∃ W : Set V, Term ⊆ W ∧ ∃ T : SimpleGraph W, T ≤ G.induce W ∧ T.IsTree ∧ Nat.card T.edgeSet ≤ M

variable {L : ℕ} [NeZero L]

/-- Vertices of `G'`: `inl v` is the original (terminal) `v`, `inr v` its copy `ṽ`. -/
abbrev SV (L : ℕ) := MV L ⊕ MV L

/-- The crossing edges `f̃⁰_{A₁} – f̃⁰_{B₁}`, `t̃⁰_{A₁} – t̃⁰_{B₁}`. -/
def IsCross (u v : MV L) : Prop :=
  ∃ κ : Fin 3, κ ≠ 2 ∧ u = .gad false false 0 κ ∧ v = .gad true false 0 κ

instance (u v : MV L) : Decidable (IsCross u v) := by unfold IsCross; infer_instance

/-- One-directional edge relation of `G'` (symmetrized by `fromRel`). -/
def stRel (x y : Idx L → Idx L → Bool) : SV L → SV L → Prop
  | .inr u, .inl v => u = v ∨ (mdsGraph x y).Adj u v
  | .inr u, .inr v => u.side = v.side ∨ IsCross u v
  | _, _ => False

instance (x y : Idx L → Idx L → Bool) : DecidableRel (stRel x y) := fun a b => by
  cases a <;> cases b <;> simp only [stRel] <;> infer_instance

/-- The graph `G'_{x,y}` of Section 2.3.2. -/
def stGraph (x y : Idx L → Idx L → Bool) : SimpleGraph (SV L) := SimpleGraph.fromRel (stRel x y)

instance (x y : Idx L → Idx L → Bool) : DecidableRel (stGraph x y).Adj := fun a b => by
  unfold stGraph; rw [SimpleGraph.fromRel_adj]; infer_instance

section Adj

variable (x y : Idx L → Idx L → Bool)

@[simp] lemma st_adj_inl_inl {v w : MV L} : ¬(stGraph x y).Adj (.inl v) (.inl w) := by
  simp [stGraph, stRel]

@[simp] lemma st_adj_inr_inl {u v : MV L} :
    (stGraph x y).Adj (.inr u) (.inl v) ↔ u = v ∨ (mdsGraph x y).Adj u v := by
  simp [stGraph, stRel]

@[simp] lemma st_adj_inl_inr {u v : MV L} :
    (stGraph x y).Adj (.inl v) (.inr u) ↔ u = v ∨ (mdsGraph x y).Adj u v := by
  rw [SimpleGraph.adj_comm, st_adj_inr_inl]

@[simp] lemma st_adj_inr_inr {u v : MV L} :
    (stGraph x y).Adj (.inr u) (.inr v) ↔ u ≠ v ∧ (u.side = v.side ∨ IsCross u v ∨ IsCross v u) := by
  simp only [stGraph, SimpleGraph.fromRel_adj, stRel, ne_eq, Sum.inr.injEq]
  constructor
  · rintro ⟨h1, (h2 | h2) | (h2 | h2)⟩
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1, Or.inr (Or.inl h2)⟩
    · exact ⟨h1, Or.inl h2.symm⟩
    · exact ⟨h1, Or.inr (Or.inr h2)⟩
  · rintro ⟨h1, h2 | h2 | h2⟩
    · exact ⟨h1, Or.inl (Or.inl h2)⟩
    · exact ⟨h1, Or.inl (Or.inr h2)⟩
    · exact ⟨h1, Or.inr (Or.inr h2)⟩

end Adj

/-- Number of terminals `|V| = 4k + 12 log k`; the Steiner tree size bound is `|V| + 4 log k + 1`. -/
def stBound (L : ℕ) : ℕ := 4 * 2 ^ L + 16 * L + 1

lemma exists_adj_of_connected {α : Type*} {G : SimpleGraph α} (hG : G.Connected) {a b : α}
    (hab : a ≠ b) : ∃ c, G.Adj a c := by
  obtain ⟨p⟩ := hG.preconnected a b
  cases p with
  | nil => exact absurd rfl hab
  | cons h _ => exact ⟨_, h⟩

variable {x y : Idx L → Idx L → Bool}

/-- `⇒` of Claim 2.8: the copies used by a small Steiner tree form a small dominating set. -/
lemma dominating_of_steiner (h : HasSteinerTreeLE (stGraph x y) (Set.range Sum.inl) (stBound L)) :
    ∃ D : Finset (MV L), IsDominating (mdsGraph x y) D ∧ D.card ≤ 4 * L + 2 := by
  classical
  obtain ⟨W, hTerm, T, hle, htree, hcard⟩ := h
  have hW : Nat.card T.edgeSet + 1 = Nat.card W := (SimpleGraph.isTree_iff_connected_and_card.1 htree).2
  let C : Finset (MV L) := univ.filter fun u => (Sum.inr u : SV L) ∈ W
  refine ⟨C, ?_, ?_⟩
  · -- every terminal has a tree neighbour, which is a copy `ũ` with `u = v` or `u ~ v`
    intro v
    have hv : (Sum.inl v : SV L) ∈ W := hTerm ⟨v, rfl⟩
    -- a second terminal
    obtain ⟨v', hv'⟩ : ∃ v' : MV L, v' ≠ v := by
      by_cases hr : v = .row false false (fun _ => false)
      · exact ⟨.row true false (fun _ => false), by rw [hr]; simp⟩
      · exact ⟨.row false false (fun _ => false), fun h => hr h.symm⟩
    obtain ⟨c, hc⟩ := exists_adj_of_connected htree.connected (a := ⟨Sum.inl v, hv⟩)
      (b := ⟨Sum.inl v', hTerm ⟨v', rfl⟩⟩) (by simp [hv'.symm])
    have hG := hle hc
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype] at hG
    obtain ⟨c, hcW⟩ := c
    cases c with
    | inl w => exact absurd hG (st_adj_inl_inl x y)
    | inr u =>
      rw [st_adj_inl_inr] at hG
      have huC : u ∈ C := by simp [C, hcW]
      rcases hG with rfl | hG
      · exact Or.inl huC
      · exact Or.inr ⟨u, huC, hG.symm⟩
  · -- counting: `|W| ≥ |V| + |C|`
    have hsub : Set.range (Sum.inl : MV L → SV L) ∪ Sum.inr '' (C : Set (MV L)) ⊆ W := by
      rintro _ (⟨v, rfl⟩ | ⟨u, hu, rfl⟩)
      · exact hTerm ⟨v, rfl⟩
      · simpa [C] using hu
    have hdisj : Disjoint (Set.range (Sum.inl : MV L → SV L)) (Sum.inr '' (C : Set (MV L))) := by
      rw [Set.disjoint_left]
      rintro _ ⟨v, rfl⟩ ⟨u, -, hu⟩
      exact Sum.inr_ne_inl hu
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite W)
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      Set.ncard_range_of_injective Sum.inl_injective,
      Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_coe_finset,
      Nat.card_eq_fintype_card, card_MV] at h1
    rw [← Nat.card_coe_set_eq] at h1
    simp only [stBound] at hcard
    omega

/-- `⇐` of Claim 2.8: from an intersecting index, the canonical dominating set and one crossing
edge give a Steiner tree with exactly `4k + 16 log k + 1` edges. -/
lemma steiner_of_not_disj {i j : Idx L} (hx : x i j = true) (hy : y i j = true) :
    HasSteinerTreeLE (stGraph x y) (Set.range Sum.inl) (stBound L) := by
  classical
  set C := canonDS i j
  have hC := isDominating_canonDS x y hx hy
  set W : Set (SV L) := Set.range Sum.inl ∪ Sum.inr '' (C : Set (MV L))
  have hrow : MV.row false false i ∈ C := by simp [C, canonDS]
  have hmem : ∀ s, MV.gad s false 0 (dsKind (i 0)) ∈ C := fun s =>
    mem_union_right _ (mem_image.2 ⟨(s, false, 0), mem_univ _, rfl⟩)
  have hk : dsKind (i 0) ≠ 2 := by unfold dsKind; split_ifs <;> decide
  -- connectivity of `G'[W]`
  have inW_inr : ∀ {u}, u ∈ C → (Sum.inr u : SV L) ∈ W := fun hu => Or.inr ⟨_, hu, rfl⟩
  have inW_inl : ∀ v, (Sum.inl v : SV L) ∈ W := fun v => Or.inl ⟨v, rfl⟩
  let r : W := ⟨Sum.inr (MV.row false false i), inW_inr hrow⟩
  have adjW : ∀ {a b : SV L} (ha : a ∈ W) (hb : b ∈ W), (stGraph x y).Adj a b →
      ((stGraph x y).induce W).Adj ⟨a, ha⟩ ⟨b, hb⟩ := fun _ _ h => by simpa using h
  have reach_same : ∀ {u v : MV L} (hu : u ∈ C) (hv : v ∈ C), u.side = v.side →
      ((stGraph x y).induce W).Reachable ⟨_, inW_inr hu⟩ ⟨_, inW_inr hv⟩ := by
    intro u v hu hv hs
    by_cases huv : u = v
    · subst huv; rfl
    · exact (adjW _ _ ((st_adj_inr_inr x y).2 ⟨huv, Or.inl hs⟩)).reachable
  have reach_copy : ∀ {u : MV L} (hu : u ∈ C), ((stGraph x y).induce W).Reachable r ⟨_, inW_inr hu⟩ := by
    intro u hu
    cases hs : u.side
    · exact reach_same hrow hu hs.symm
    · have h1 := reach_same hrow (hmem false) (by simp [MV.side])
      have h2 : ((stGraph x y).induce W).Reachable ⟨_, inW_inr (hmem false)⟩
          ⟨_, inW_inr (hmem true)⟩ :=
        (adjW _ _ ((st_adj_inr_inr x y).2 ⟨by simp, Or.inr (Or.inl ⟨_, hk, rfl, rfl⟩)⟩)).reachable
      have h3 := reach_same (hmem true) hu hs.symm
      exact h1.trans (h2.trans h3)
  have hconn : ((stGraph x y).induce W).Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨r, ?_⟩
    rintro ⟨w, hw⟩
    rcases hw with ⟨v, rfl⟩ | ⟨u, hu, rfl⟩
    · rcases hC v with hv | ⟨u, hu, hvu⟩
      · exact (reach_copy hv).trans
          (adjW _ _ ((st_adj_inr_inl x y).2 (Or.inl rfl))).reachable
      · exact (reach_copy hu).trans
          (adjW _ _ ((st_adj_inr_inl x y).2 (Or.inr hvu.symm))).reachable
    · exact reach_copy hu
  obtain ⟨T, hTle, hT⟩ := hconn.exists_isTree_le
  refine ⟨W, Set.subset_union_left, T, hTle, hT, ?_⟩
  have hW := (SimpleGraph.isTree_iff_connected_and_card.1 hT).2
  have hdisj : Disjoint (Set.range (Sum.inl : MV L → SV L)) (Sum.inr '' (C : Set (MV L))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, rfl⟩ ⟨u, -, hu⟩
    exact Sum.inr_ne_inl hu
  have hWc : Nat.card W = 4 * 2 ^ L + 12 * L + (4 * L + 2) := by
    rw [Nat.card_coe_set_eq W, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      Set.ncard_range_of_injective Sum.inl_injective,
      Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_coe_finset,
      Nat.card_eq_fintype_card, card_MV, card_canonDS]
  simp only [stBound]
  omega

/-- **Claim 2.8** (combinatorial part). For `k = 2^L ≥ 2`, `G'_{x,y}` has a Steiner tree for
`Term = V` with at most `4k + 16 log k + 1` edges iff `DISJ(x, y) = FALSE`. -/
theorem claim_2_8 :
    HasSteinerTreeLE (stGraph x y) (Set.range Sum.inl) (stBound L) ↔
      ∃ i j, x i j = true ∧ y i j = true := by
  constructor
  · intro h
    obtain ⟨D, hD, hcard⟩ := dominating_of_steiner h
    exact (lemma_2_1_le x y).1 ⟨D, hD, hcard⟩
  · rintro ⟨i, j, hx, hy⟩
    exact steiner_of_not_disj hx hy

/-! ### The Steiner family and Theorem 2.7 -/

omit [NeZero L] in
lemma mdsCut_sides {p : MV L × MV L} (hp : p ∈ mdsCut L) : p.1.side = false ∧ p.2.side = true := by
  obtain ⟨q, -, rfl⟩ := mem_image.1 hp
  simp [MV.side]

/-- The side of a vertex of `G'` (`false` = Alice: `V_A ∪ Ṽ_A`). -/
def stSide : SV L → Bool := Sum.elim MV.side MV.side

/-- Cut edges of `G'`: `(ũ, v)` and `(u, ṽ)` for every cut edge `(u, v)` of `G`, and the two
crossing edges. -/
def stCut (L : ℕ) [NeZero L] : Finset (SV L × SV L) :=
  (mdsCut L).image (fun p => (Sum.inr p.1, Sum.inl p.2)) ∪
    (mdsCut L).image (fun p => (Sum.inl p.1, Sum.inr p.2)) ∪
    ({0, 1} : Finset (Fin 3)).image fun κ => (Sum.inr (.gad false false 0 κ), Sum.inr (.gad true false 0 κ))

lemma card_stCut : (stCut L).card ≤ 8 * L + 2 := by
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add (card_union_le _ _) card_image_le).trans ?_
  have h1 := card_image_le (s := mdsCut L) (f := fun p => ((Sum.inr p.1, Sum.inl p.2) : SV L × SV L))
  have h2 := card_image_le (s := mdsCut L) (f := fun p => ((Sum.inl p.1, Sum.inr p.2) : SV L × SV L))
  rw [card_mdsCut] at h1 h2
  have h3 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  omega

/-- `G'_{x,y}` with inputs indexed by pairs. -/
def stG (x y : Idx L × Idx L → Bool) : SimpleGraph (SV L) :=
  stGraph (fun i j => x (i, j)) (fun i j => y (i, j))

instance (x y : Idx L × Idx L → Bool) : DecidableRel (stG x y).Adj :=
  inferInstanceAs (DecidableRel (stGraph _ _).Adj)

/-- The Steiner graphs form a family of lower bound graphs (Theorem 2.6 applied to the MDS
family). -/
def stFamily (L : ℕ) [NeZero L] :
    LBFamily (Idx L × Idx L → Bool) (Idx L × Idx L → Bool) (SV L) (SV L → Bool) :=
  LBFamily.ofAdj stG (fun v => !stSide v) (stCut L)
    (by
      intro p hp
      simp only [stCut, mem_union, mem_image] at hp
      rcases hp with (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨κ, -, rfl⟩
      · have := mdsCut_sides hq; simp [stSide, this]
      · have := mdsCut_sides hq; simp [stSide, this]
      · simp [stSide, MV.side])
    (by
      intro x y a b ha hb hab
      simp only [Bool.not_eq_true', Bool.not_eq_false'] at ha hb
      simp only [stCut, mem_union, mem_image]
      cases a with
      | inl v =>
        cases b with
        | inl w => exact absurd hab (st_adj_inl_inl _ _)
        | inr u =>
          rw [stG, st_adj_inl_inr] at hab
          simp only [stSide, Sum.elim_inl, Sum.elim_inr] at ha hb
          rcases hab with rfl | hab
          · rw [ha] at hb; exact absurd hb (by simp)
          · exact Or.inl (Or.inr ⟨(v, u), mds_adj_cut ha hb hab.symm, rfl⟩)
      | inr u =>
        cases b with
        | inl v =>
          rw [stG, st_adj_inr_inl] at hab
          simp only [stSide, Sum.elim_inl, Sum.elim_inr] at ha hb
          rcases hab with rfl | hab
          · rw [ha] at hb; exact absurd hb (by simp)
          · exact Or.inl (Or.inl ⟨(u, v), mds_adj_cut ha hb hab, rfl⟩)
        | inr v =>
          rw [stG, st_adj_inr_inr] at hab
          simp only [stSide, Sum.elim_inr] at ha hb
          obtain ⟨-, hs | ⟨κ, hκ, rfl, rfl⟩ | ⟨κ, hκ, rfl, rfl⟩⟩ := hab
          · rw [ha, hb] at hs; exact absurd hs (by simp)
          · refine Or.inr ⟨κ, ?_, rfl⟩
            revert hκ; fin_cases κ <;> simp
          · simp [MV.side] at ha)
    (by
      intro x y y' a b ha hb
      simp only [Bool.not_eq_true'] at ha hb
      cases a <;> cases b <;> simp only [stG, st_adj_inl_inl, st_adj_inl_inr, st_adj_inr_inl,
        st_adj_inr_inr] <;> simp only [stSide, Sum.elim_inl, Sum.elim_inr] at ha hb
      · rw [mds_adj_A _ _ (fun i j => y' (i, j)) hb ha]
      · rw [mds_adj_A _ _ (fun i j => y' (i, j)) ha hb])
    (by
      intro x x' y a b ha hb
      simp only [Bool.not_eq_false'] at ha hb
      cases a <;> cases b <;> simp only [stG, st_adj_inl_inl, st_adj_inl_inr, st_adj_inr_inl,
        st_adj_inr_inr] <;> simp only [stSide, Sum.elim_inl, Sum.elim_inr] at ha hb
      · rw [mds_adj_B _ _ (fun i j => x' (i, j)) hb ha]
      · rw [mds_adj_B _ _ (fun i j => x' (i, j)) ha hb])
    (by
      intro x x' y y' a b ha hb
      simp only [Bool.not_eq_true', Bool.not_eq_false'] at ha hb
      cases a <;> cases b <;> simp only [stG, st_adj_inl_inl, st_adj_inl_inr, st_adj_inr_inl,
        st_adj_inr_inr] <;> simp only [stSide, Sum.elim_inl, Sum.elim_inr] at ha hb
      · rw [(mdsGraph _ _).adj_comm, (mdsGraph (fun i j => x' (i, j)) _).adj_comm,
          mds_adj_fixed _ _ (fun i j => x' (i, j)) (fun i j => y' (i, j)) ha hb]
      · rw [mds_adj_fixed _ _ (fun i j => x' (i, j)) (fun i j => y' (i, j)) ha hb])

instance (x y : Idx L × Idx L → Bool) : DecidableRel ((stFamily L).G x y).Adj :=
  inferInstanceAs (DecidableRel (stG x y).Adj)

/-- **Theorem 2.7** (deterministic, decision version). If a deterministic CONGEST algorithm with
`B`-bit messages decides in `T` rounds, on every `G'_{x,y}` (`n = 8k + 24 log k` vertices,
terminals `V`), whether there is a Steiner tree with at most `4k + 16 log k + 1` edges, then
`k² ≤ 2 T (8 log k + 2) B + 2`. -/
theorem theorem_2_7 {σ : Type*} {B : ℕ} (A : Algorithm (SV L) (SV L → Bool) σ B) (T : ℕ)
    (hA : ∀ x y : Idx L × Idx L → Bool,
      A.Accepts (stG x y) (fun v w => decide ((stG x y).Adj v w)) T ↔
        HasSteinerTreeLE (stG x y) (Set.range Sum.inl) (stBound L)) :
    4 ^ L ≤ T * (2 * ((8 * L + 2) * B)) + 2 := by
  have h := (stFamily L).not_disj_lowerBound A T fun x y => by
    change A.Accepts (stG x y) (fun v w => decide ((stG x y).Adj v w)) T ↔ _
    rw [hA x y, stG, claim_2_8]
    simp [Protocol.disj]
  have hc : Fintype.card (Idx L × Idx L) = 4 ^ L := by
    simp [Fintype.card_prod, ← mul_pow]
  rw [hc] at h
  refine h.trans ?_
  have := card_stCut (L := L)
  change T * (2 * ((stCut L).card * B)) + 2 ≤ _
  gcongr

end HardnessOptimization
