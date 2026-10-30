import Papers.PODC2021.BFTInBlockDAG.Graph

/-!
# Blocks and block DAGs (Section 3, Definitions 3.1, 3.3, 3.4; Lemmas 3.2, A.2, A.3, A.7)

**Blocks are content-addressed.** The paper identifies a block `B` with its hash `ref(B)`
("justified by collision resistance") and uses preimage resistance to rule out cyclic references
(Lemma 3.2). We idealize the hash function in the standard symbolic way: a block *contains* its
predecessor blocks (`Block` is a nested inductive type), so two blocks are equal iff their contents
are equal, and the predecessor relation is well founded by construction. The signature `σ` is not
a field: unforgeability is modelled in the execution (`Gossip.lean`), where only server `s` can
create blocks with `n = s`.

* `Block.Edge C B` (`C ⇀ B`): `C ∈ B.preds`. Well founded (`Block.wellFounded_edge`).
* Lemma 3.2: `Block.edge_asymm`.
* `Block.IsParent`, genesis blocks (`k = 0`), `Block.LocallyValid` (Definition 3.3 (ii)) and
  `Block.Valid` (Definition 3.3 (ii)–(iii), i.e. `LocallyValid` for the block and all its ancestors).
* Block DAGs (Definition 3.4): `IsBlockDAG V` for a vertex set `V`; the graph is `toGraph V`
  (edges `(B, B')` with `B ∈ B'.preds`). `isBlockDAG_iff_paper` relates it to the graph version
  `PaperBlockDAG` of Definition 3.4.
* Lemma A.2 `insertBlock_eq_self`, Lemma A.3 `paperBlockDAG_insertBlock`, Lemma A.7
  `isBlockDAG_union`.
* `Block.fold`: structural recursion over the DAG below a block (used to define the
  interpretation of Section 4); it reduces in the kernel, so concrete examples go through `decide`.
-/

set_option linter.unusedSectionVars false

namespace Podc.BFTInBlockDAG

/-- Definition 3.1: a block has the identifier `n` of the server that built it, a sequence
number `k`, a finite list of predecessor blocks `preds` (idealized hashes `ref(Bᵢ)`) and a list of
labelled requests `rs`. -/
inductive Block (S L R : Type) where
  | mk (n : S) (k : ℕ) (preds : List (Block S L R)) (rs : List (L × R))

namespace Block

variable {S L R : Type}

/-- The server that built the block. -/
def n : Block S L R → S | mk n _ _ _ => n
/-- The sequence number. -/
def k : Block S L R → ℕ | mk _ k _ _ => k
/-- The predecessor blocks. -/
def preds : Block S L R → List (Block S L R) | mk _ _ p _ => p
/-- The labelled requests. -/
def rs : Block S L R → List (L × R) | mk _ _ _ r => r

@[simp] theorem n_mk (n : S) (k p r) : (mk n k p r : Block S L R).n = n := rfl
@[simp] theorem k_mk (n : S) (k p r) : (mk n k p r : Block S L R).k = k := rfl
@[simp] theorem preds_mk (n : S) (k p r) : (mk n k p r : Block S L R).preds = p := rfl
@[simp] theorem rs_mk (n : S) (k p r) : (mk n k p r : Block S L R).rs = r := rfl

theorem eta (B : Block S L R) : mk B.n B.k B.preds B.rs = B := by cases B; rfl

/-! ### Decidable equality (by mutual structural recursion, so that it reduces in the kernel) -/

section DecEq
variable [DecidableEq S] [DecidableEq L] [DecidableEq R]

mutual
/-- Decidable equality of blocks. -/
def decEq : (a b : Block S L R) → Decidable (a = b)
  | mk n k p r, mk n' k' p' r' =>
    if h1 : n = n' then if h2 : k = k' then if h4 : r = r' then
      match decEqList p p' with
      | isTrue h3 => isTrue (by subst h1 h2 h3 h4; rfl)
      | isFalse h3 => isFalse (by intro h; cases h; exact h3 rfl)
    else isFalse (by intro h; cases h; exact h4 rfl)
    else isFalse (by intro h; cases h; exact h2 rfl)
    else isFalse (by intro h; cases h; exact h1 rfl)
/-- Decidable equality of lists of blocks. -/
def decEqList : (a b : List (Block S L R)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | a :: as, b :: bs =>
    match decEq a b, decEqList as bs with
    | isTrue h, isTrue h' => isTrue (by rw [h, h'])
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
end

instance : DecidableEq (Block S L R) := decEq

end DecEq

/-! ### The predecessor relation -/

/-- `C ⇀ B`: `C` is a predecessor of `B` (the edge `(C, B)` of a block DAG). -/
def Edge (C B : Block S L R) : Prop := C ∈ B.preds

theorem sizeOf_lt_of_edge {C B : Block S L R} (h : Edge C B) : sizeOf C < sizeOf B := by
  cases B with
  | mk n k p r =>
    have := List.sizeOf_lt_of_mem (show C ∈ p from h)
    simp only [mk.sizeOf_spec]
    omega

theorem sizeOf_lt_of_transGen {C B : Block S L R} (h : Relation.TransGen Edge C B) :
    sizeOf C < sizeOf B := by
  induction h with
  | single h => exact sizeOf_lt_of_edge h
  | tail _ h ih => exact ih.trans (sizeOf_lt_of_edge h)

/-- The predecessor relation is well founded (idealized preimage resistance). -/
theorem wellFounded_edge : WellFounded (Edge : Block S L R → Block S L R → Prop) :=
  Subrelation.wf (fun h => sizeOf_lt_of_edge h) (measure (sizeOf : Block S L R → ℕ)).wf

/-- No block is its own strict ancestor. -/
theorem not_transGen_self (B : Block S L R) : ¬ Relation.TransGen Edge B B :=
  fun h => lt_irrefl _ (sizeOf_lt_of_transGen h)

/-- Lemma 3.2: if `B₁ ∈ B₂.preds` then `B₂ ∉ B₁.preds`. -/
theorem edge_asymm {B₁ B₂ : Block S L R} (h : Edge B₁ B₂) : ¬ Edge B₂ B₁ :=
  fun h' => not_transGen_self B₁ ((Relation.TransGen.single h).tail h')

theorem ne_of_transGen {C B : Block S L R} (h : Relation.TransGen Edge C B) : C ≠ B := by
  rintro rfl; exact not_transGen_self C h

/-! ### Structural folds over the DAG below a block -/

section Fold
variable {α : Type*}

mutual
/-- `fold f B = f B [fold f C | C ∈ B.preds]`, by structural recursion. -/
def fold (f : Block S L R → List α → α) : Block S L R → α
  | mk n k p r => f (mk n k p r) (foldList f p)
/-- `foldList f l = l.map (fold f)`. -/
def foldList (f : Block S L R → List α → α) : List (Block S L R) → List α
  | [] => []
  | b :: bs => fold f b :: foldList f bs
end

theorem foldList_eq_map (f : Block S L R → List α → α) (l : List (Block S L R)) :
    foldList f l = l.map (fold f) := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [foldList, ih]

theorem fold_eq (f : Block S L R → List α → α) (B : Block S L R) :
    fold f B = f B (B.preds.map (fold f)) := by
  cases B with
  | mk n k p r => simp [fold, foldList_eq_map]

end Fold

/-! ### Ancestors -/

mutual
/-- The strict ancestors of a block (with repetitions). -/
def anc : Block S L R → List (Block S L R)
  | mk _ _ p _ => ancList p
/-- `ancList l = l.flatMap (fun C => C :: anc C)`. -/
def ancList : List (Block S L R) → List (Block S L R)
  | [] => []
  | b :: bs => b :: anc b ++ ancList bs
end

theorem ancList_eq (l : List (Block S L R)) : ancList l = l.flatMap (fun C => C :: anc C) := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [ancList, ih]

theorem anc_eq (B : Block S L R) : anc B = B.preds.flatMap (fun C => C :: anc C) := by
  cases B; simp [anc, ancList_eq]

/-- `anc B` lists exactly the strict ancestors `C ⇀⁺ B`. -/
theorem mem_anc {C B : Block S L R} : C ∈ anc B ↔ Relation.TransGen Edge C B := by
  induction B using wellFounded_edge.induction generalizing C with
  | _ B ih =>
    rw [anc_eq, List.mem_flatMap]
    constructor
    · rintro ⟨D, hD, hC⟩
      rcases List.mem_cons.1 hC with rfl | hC
      · exact Relation.TransGen.single hD
      · exact ((ih D hD).1 hC).tail hD
    · intro h
      obtain ⟨D, hCD, hD⟩ := Relation.TransGen.tail'_iff.1 h
      refine ⟨D, hD, ?_⟩
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 hCD with rfl | hCD
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ ((ih D hD).2 hCD)

/-! ### Parents and validity (Definition 3.3) -/

/-- `C` is a parent of `B`: `C ∈ B.preds`, `C.n = B.n` and `B.k = C.k + 1`. -/
def IsParent (C B : Block S L R) : Prop := C ∈ B.preds ∧ C.n = B.n ∧ C.k + 1 = B.k

/-- Definition 3.3 (ii): `B` is a genesis block (`B.k = 0`) or has exactly one parent. (A genesis
block never has a parent.) Condition (i), the signature check, is part of the execution model;
condition (iii) is in `Valid`. -/
def LocallyValid (B : Block S L R) : Prop := B.k = 0 ∨ ∃! C, IsParent C B

/-- Definition 3.3, server-independent part: `B` and all its ancestors are locally valid.
(A correct server `s` considers `B` valid once it has received `B` and all its ancestors.) -/
def Valid (B : Block S L R) : Prop := ∀ C, Relation.ReflTransGen Edge C B → LocallyValid C

theorem Valid.locallyValid {B : Block S L R} (h : B.Valid) : B.LocallyValid :=
  h B Relation.ReflTransGen.refl

theorem Valid.of_edge {C B : Block S L R} (h : B.Valid) (hC : Edge C B) : C.Valid :=
  fun D hD => h D (hD.tail hC)

theorem valid_iff {B : Block S L R} : B.Valid ↔ B.LocallyValid ∧ ∀ C ∈ B.preds, C.Valid := by
  refine ⟨fun h => ⟨h.locallyValid, fun C hC => h.of_edge hC⟩, fun ⟨h1, h2⟩ D hD => ?_⟩
  rcases Relation.ReflTransGen.cases_tail hD with rfl | ⟨C, hDC, hC⟩
  · exact h1
  · exact h2 C hC D hDC

theorem not_isParent_of_k_eq_zero {C B : Block S L R} (h : B.k = 0) : ¬ IsParent C B := by
  rintro ⟨-, -, h'⟩; omega

section Decidable
variable [DecidableEq S] [DecidableEq L] [DecidableEq R]

instance (C B : Block S L R) : Decidable (IsParent C B) := by
  unfold IsParent; infer_instance

/-- `B.parent?`: the first parent in `B.preds` (the parent of a locally valid non-genesis block). -/
def parent? (B : Block S L R) : Option (Block S L R) :=
  B.preds.find? fun C => decide (C.n = B.n ∧ C.k + 1 = B.k)

omit [DecidableEq S] [DecidableEq L] [DecidableEq R] in
theorem locallyValid_iff_list {B : Block S L R} :
    B.LocallyValid ↔ B.k = 0 ∨
      ∃ C ∈ B.preds, IsParent C B ∧ ∀ D ∈ B.preds, IsParent D B → D = C := by
  unfold LocallyValid
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨C, hC, hu⟩
    exact ⟨C, hC.1, hC, fun D _ hD => hu D hD⟩
  · rintro ⟨C, -, hC, hu⟩
    exact ⟨C, hC, fun D hD => hu D hD.1 hD⟩

instance (B : Block S L R) : Decidable B.LocallyValid :=
  decidable_of_iff _ locallyValid_iff_list.symm

omit [DecidableEq L] [DecidableEq R] in
theorem parent?_eq_some {B C : Block S L R} (h : B.parent? = some C) : IsParent C B := by
  unfold parent? at h
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [decide_eq_true_eq] at h2
  exact ⟨h1, h2⟩

theorem parent?_eq_some_of_isParent {B C : Block S L R} (hB : B.LocallyValid)
    (hC : IsParent C B) : B.parent? = some C := by
  rcases hB with h | ⟨D, hD, hu⟩
  · exact absurd hC (not_isParent_of_k_eq_zero h)
  · have hCD : C = D := hu C hC
    subst hCD
    unfold parent?
    cases h : B.preds.find? (fun C => decide (C.n = B.n ∧ C.k + 1 = B.k)) with
    | none =>
      exfalso
      rw [List.find?_eq_none] at h
      exact h C hC.1 (by simp [hC.2.1, hC.2.2])
    | some E =>
      have hE : IsParent E B := parent?_eq_some (by unfold parent?; exact h)
      rw [hu E hE]

theorem exists_parent?_of_locallyValid {B : Block S L R} (hB : B.LocallyValid) (hk : B.k ≠ 0) :
    ∃ C, B.parent? = some C ∧ IsParent C B := by
  have hB' := hB
  rcases hB with h | ⟨C, hC, -⟩
  · exact absurd h hk
  · exact ⟨C, parent?_eq_some_of_isParent hB' hC, hC⟩

end Decidable

end Block

/-! ### Block DAGs (Definition 3.4) -/

open Block

variable {S L R : Type}

/-- Definition 3.4, as a set of vertices: every block is valid and every predecessor of a block
of `V` is in `V`. The edges are then determined: `toGraph V`. -/
def IsBlockDAG (V : Set (Block S L R)) : Prop :=
  (∀ B ∈ V, B.Valid) ∧ ∀ B ∈ V, ∀ C ∈ B.preds, C ∈ V

/-- The graph of a set of blocks: edges `(B, B')` for `B ∈ B'.preds`, `B' ∈ V`. -/
def toGraph (V : Set (Block S L R)) : DGraph (Block S L R) :=
  ⟨V, {e | e.2 ∈ V ∧ e.1 ∈ e.2.preds}⟩

/-- Definition 3.4 for a general directed graph `G` (with `E ⊆ V × V`): `G` is acyclic, all its
blocks are valid and if `B ∈ B'.preds` for `B' ∈ G` then `B ∈ G` and `(B, B') ∈ E_G`. -/
def PaperBlockDAG (G : DGraph (Block S L R)) : Prop :=
  G.WellFormed ∧ G.Acyclic ∧ (∀ B ∈ G.V, B.Valid) ∧
    ∀ B' ∈ G.V, ∀ B ∈ B'.preds, B ∈ G.V ∧ (B, B') ∈ G.E

/-- `G.insert(B')` of Definition 3.4: `insert(G, B', {(B, B') | B ∈ B'.preds})`. -/
def insertBlock (G : DGraph (Block S L R)) (B' : Block S L R) : DGraph (Block S L R) :=
  G.insert B' {e | e.2 = B' ∧ e.1 ∈ B'.preds}

theorem toGraph_acyclic (V : Set (Block S L R)) : (toGraph V).Acyclic := by
  intro a b h
  apply ne_of_transGen
  induction h with
  | single h => exact Relation.TransGen.single h.2
  | tail _ h ih => exact ih.tail h.2

/-- A vertex-set block DAG gives a block DAG in the sense of Definition 3.4. -/
theorem IsBlockDAG.paper {V : Set (Block S L R)} (h : IsBlockDAG V) :
    PaperBlockDAG (toGraph V) :=
  ⟨fun _ he => ⟨h.2 _ he.1 _ he.2, he.1⟩, toGraph_acyclic V, h.1,
    fun B' hB' B hB => ⟨h.2 B' hB' B hB, hB', hB⟩⟩

theorem isBlockDAG_of_paper {G : DGraph (Block S L R)} (h : PaperBlockDAG G) :
    IsBlockDAG G.V :=
  ⟨h.2.2.1, fun B' hB' B hB => (h.2.2.2 B' hB' B hB).1⟩

/-- For closed vertex sets, the paper's `⩽` is inclusion of vertex sets. -/
theorem toGraph_le_toGraph_iff {V W : Set (Block S L R)} (hV : ∀ B ∈ V, ∀ C ∈ B.preds, C ∈ V) :
    toGraph V ≤ toGraph W ↔ V ⊆ W := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  ext ⟨a, b⟩
  simp only [toGraph, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod]
  constructor
  · rintro ⟨hb, ha⟩
    exact ⟨⟨h hb, ha⟩, hV b hb a ha, hb⟩
  · rintro ⟨⟨-, ha⟩, -, hb⟩
    exact ⟨hb, ha⟩

theorem insertBlock_toGraph (V : Set (Block S L R)) (B : Block S L R) :
    insertBlock (toGraph V) B = toGraph (V ∪ {B}) := by
  simp only [insertBlock, DGraph.insert, toGraph, DGraph.mk.injEq, true_and]
  ext ⟨a, b⟩
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro (⟨hb, ha⟩ | ⟨rfl, ha⟩)
    · exact ⟨Or.inl hb, ha⟩
    · exact ⟨Or.inr rfl, ha⟩
  · rintro ⟨hb | rfl, ha⟩
    · exact Or.inl ⟨hb, ha⟩
    · exact Or.inr ⟨rfl, ha⟩

/-- Lemma A.2: inserting a block that is already in a block DAG does nothing. -/
theorem insertBlock_eq_self {G : DGraph (Block S L R)} (hG : PaperBlockDAG G) {B : Block S L R}
    (hB : B ∈ G.V) : insertBlock G B = G := by
  apply DGraph.insert_eq_self G hB
  rintro ⟨a, b⟩ ⟨rfl, ha⟩
  exact (hG.2.2.2 _ hB a ha).2

/-- Lemma A.3: if `B'` is (locally) valid and all its predecessors are in the block DAG `G`, then
`G.insert(B')` is a block DAG. -/
theorem paperBlockDAG_insertBlock {G : DGraph (Block S L R)} (hG : PaperBlockDAG G)
    {B' : Block S L R} (hB' : B'.LocallyValid) (hpreds : ∀ B ∈ B'.preds, B ∈ G.V) :
    PaperBlockDAG (insertBlock G B') := by
  obtain ⟨hwf, hac, hval, hcl⟩ := hG
  by_cases hmem : B' ∈ G.V
  · rw [insertBlock_eq_self ⟨hwf, hac, hval, hcl⟩ hmem]; exact ⟨hwf, hac, hval, hcl⟩
  have hE : G.InsertEdges B' {e | e.2 = B' ∧ e.1 ∈ B'.preds} := fun e he => ⟨hpreds _ he.2, he.1⟩
  refine ⟨?_, DGraph.acyclic_insert G hwf hE hmem hac, ?_, ?_⟩
  · rintro e (he | ⟨he1, he2⟩)
    · exact ⟨Or.inl (hwf e he).1, Or.inl (hwf e he).2⟩
    · exact ⟨Or.inl (hpreds _ he2), Or.inr he1⟩
  · rintro B (hB | rfl)
    · exact hval B hB
    · exact valid_iff.2 ⟨hB', fun C hC => hval C (hpreds C hC)⟩
  · rintro B (hB | rfl) C hC
    · exact ⟨Or.inl (hcl B hB C hC).1, Or.inl (hcl B hB C hC).2⟩
    · exact ⟨Or.inl (hpreds C hC), Or.inr ⟨rfl, hC⟩⟩

/-- Lemma A.7: the joint block DAG of two block DAGs is a block DAG containing both
(in the sense of `⩽`). -/
theorem isBlockDAG_union {V W : Set (Block S L R)} (hV : IsBlockDAG V) (hW : IsBlockDAG W) :
    IsBlockDAG (V ∪ W) ∧ toGraph V ≤ toGraph (V ∪ W) ∧ toGraph W ≤ toGraph (V ∪ W) := by
  refine ⟨⟨?_, ?_⟩, (toGraph_le_toGraph_iff hV.2).2 Set.subset_union_left,
    (toGraph_le_toGraph_iff hW.2).2 Set.subset_union_right⟩
  · rintro B (hB | hB)
    · exact hV.1 B hB
    · exact hW.1 B hB
  · rintro B (hB | hB) C hC
    · exact Or.inl (hV.2 B hB C hC)
    · exact Or.inr (hW.2 B hB C hC)

/-- Inserting a locally valid block whose predecessors are present keeps a block DAG. -/
theorem IsBlockDAG.insert {V : Set (Block S L R)} (hV : IsBlockDAG V) {B : Block S L R}
    (hB : B.LocallyValid) (hp : ∀ C ∈ B.preds, C ∈ V) : IsBlockDAG (insert B V) := by
  refine ⟨?_, ?_⟩
  · rintro D (rfl | hD)
    · exact valid_iff.2 ⟨hB, fun C hC => hV.1 C (hp C hC)⟩
    · exact hV.1 D hD
  · rintro D (rfl | hD) C hC
    · exact Or.inr (hp C hC)
    · exact Or.inr (hV.2 D hD C hC)

theorem isBlockDAG_empty : IsBlockDAG (∅ : Set (Block S L R)) := by
  simp [IsBlockDAG]

/-- In a block DAG, all ancestors of a member are members. -/
theorem IsBlockDAG.mem_of_reflTransGen {V : Set (Block S L R)} (hV : IsBlockDAG V)
    {B C : Block S L R} (hB : B ∈ V) (h : Relation.ReflTransGen Edge C B) : C ∈ V := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hB
  | head hCD _ ih => exact hV.2 _ ih _ hCD

end Podc.BFTInBlockDAG
