import Papers.PODC2011.LocallyCheckableProofs.Lifts

/-!
# Trees: every graph property admits `O(n)`-bit proofs (Section 6.2 of Göös–Suomela)

"In this section, we fix `F` to be the family of connected trees. Here, any graph property
`P ⊆ F` admits a locally checkable proof of size `O(n)`: for each node `v` of the tree `G ∈ P`, we
encode the structure of `G` and an index that identifies which node of `G` is `v`."

* `IsCovering.injOn_of_isAcyclic`: a covering map from a connected graph onto an acyclic graph is
  injective, hence an isomorphism (`IsIsoMap`). Consequently, on trees, closure under isomorphism
  implies closure under lifts (`closedUnderLifts_of_closedUnderIso`).
* Tree codes: a nondecreasing parent sequence `ps` (node `k + 2` has parent `ps[k] + 1`,
  `ps[k] ≤ k`; `treeOf ps`), written in "stars and bars" form (`sbEnc`: `ps[k] - ps[k-1]` zeros and
  a one per entry; `≤ 2n` bits).
* `exists_treeCode`: every finite tree `H` is isomorphic to `treeOf ps` for a nondecreasing parent
  sequence `ps` (number the nodes in BFS order: by the shortlex order of their root paths).
* `tree_upper` (**Section 6.2**): every property of trees closed under isomorphism admits locally
  checkable proofs of size `8n`, verifiable even by a (one-round) port-numbering verifier.
-/

namespace Podc.LocallyCheckableProofs.Trees

open SimpleGraph Finset Cslib.BitEncoding Universal Lifts

/-! ### Isomorphisms; coverings of trees are isomorphisms -/

/-- `ϕ` is an isomorphism from `H` onto `G`. -/
structure IsIsoMap (ϕ : ℕ → ℕ) (H G : Inst Unit) : Prop where
  bijOn : Set.BijOn ϕ H.V G.V
  adj_iff : ∀ u ∈ H.V, ∀ v ∈ H.V, H.G.Adj u v ↔ G.G.Adj (ϕ u) (ϕ v)

/-- `P` is closed under isomorphism within `F` (a *graph property*). -/
def ClosedUnderIso (F P : Set (Inst Unit)) : Prop :=
  ∀ G ∈ F, G ∈ P → ∀ H ∈ F, (∃ ϕ, IsIsoMap ϕ H G) → H ∈ P

/-- The family of trees: connected, unlabelled, acyclic. -/
def TreeFam : Set (Inst Unit) := {I | I.Conn ∧ I.Plain ∧ I.G.IsAcyclic}

variable {ϕ : ℕ → ℕ} {H G : Inst Unit}

/-- A covering map that is injective on the nodes is an isomorphism. -/
lemma _root_.Podc.LocallyCheckableProofs.Lifts.IsCovering.isIsoMap (h : IsCovering ϕ H G) (hinj : Set.InjOn ϕ H.V) : IsIsoMap ϕ H G := by
  refine ⟨⟨h.mapsTo, hinj, h.surjOn⟩, fun u hu v hv => ⟨h.adj, fun hadj => ?_⟩⟩
  obtain ⟨w, hw, hwv⟩ := (h.bijOn_nbrs u hu).surjOn hadj
  rwa [hinj (H.sub' hw) hv hwv] at hw

/-- A homomorphism into an acyclic graph that is injective on neighbourhoods maps paths to
paths. -/
-- CSLib candidate
lemma isPath_map_of_locInj {A B : SimpleGraph ℕ} (f : A →g B) (hB : B.IsAcyclic)
    (hinj : ∀ a b d, A.Adj b a → A.Adj b d → f a = f d → a = d) :
    ∀ {u v : ℕ} (p : A.Walk u v), p.IsPath → (p.map f).IsPath := by
  classical
  intro u v p hp
  induction p with
  | nil => simp
  | @cons a b c h q ih =>
    rw [Walk.cons_isPath_iff] at hp
    have ihq := ih hp.1
    rw [Walk.map_cons, Walk.cons_isPath_iff]
    refine ⟨ihq, fun hmem => ?_⟩
    cases q with
    | nil =>
      simp only [Walk.map_nil, Walk.support_nil, List.mem_singleton] at hmem
      exact (f.map_adj h).ne hmem
    | @cons _ d _ h' q'' =>
      simp only [Walk.map_cons, Walk.support_cons, List.mem_cons] at hmem
      rcases hmem with hab | hmem
      · exact (f.map_adj h).ne hab
      rw [Walk.map_cons, Walk.cons_isPath_iff] at ihq
      have had : a ≠ d := fun had => hp.2 (by simp [had])
      have hfad : f a ≠ f d := fun he => had (hinj a b d h.symm h' he)
      set W := q''.map f
      let r := W.takeUntil (f a) hmem
      have hr : r.IsPath := ihq.1.takeUntil hmem
      have hbr : f b ∉ r.support := fun hb => ihq.2 (W.support_takeUntil_subset_support hmem hb)
      have hcyc : (Walk.cons (f.map_adj h) (Walk.cons (f.map_adj h') r)).IsCycle := by
        rw [Walk.cons_isCycle_iff]
        refine ⟨Walk.cons_isPath_iff _ _ |>.2 ⟨hr, hbr⟩, ?_⟩
        rw [Walk.edges_cons, List.mem_cons, not_or]
        refine ⟨fun he => ?_, fun he => hbr (r.snd_mem_support_of_mem_edges he)⟩
        rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact (f.map_adj h).ne h1
        · exact hfad h1
      exact hB _ hcyc

/-- A covering map from a connected graph onto an acyclic graph is injective: connected lifts of
trees are trivial. -/
lemma _root_.Podc.LocallyCheckableProofs.Lifts.IsCovering.injOn_of_isAcyclic (h : IsCovering ϕ H G) (hH : H.Conn) (hG : G.G.IsAcyclic) :
    Set.InjOn ϕ H.V := by
  intro u hu w hw huw
  obtain ⟨p, hp⟩ := (hH.2 u hu w hw).exists_isPath
  have hmp := isPath_map_of_locInj h.hom hG (fun a b d hba hbd he =>
    (h.bijOn_nbrs b (H.sub hba)).injOn hba hbd he) p hp
  have hc : ((p.map h.hom).copy (rfl : h.hom u = h.hom u)
      (show h.hom w = h.hom u from huw.symm)).IsPath := by rw [Walk.isPath_copy]; exact hmp
  have hlen := (Walk.isPath_iff_nil.1 hc).length_eq_zero
  simp only [Walk.length_copy, Walk.length_map] at hlen
  exact Walk.eq_of_length_eq_zero hlen

/-- On trees, closure under isomorphism implies closure under lifts. -/
lemma closedUnderLifts_of_closedUnderIso {F P : Set (Inst Unit)} (hF : ∀ I ∈ F, I ∈ TreeFam)
    (hP : ClosedUnderIso F P) : ClosedUnderLifts F P := by
  intro G hG hGP H hH ⟨ϕ, hϕ⟩
  exact hP G hG hGP H hH ⟨ϕ, hϕ.isIsoMap (hϕ.injOn_of_isAcyclic (hF H hH).1 (hF G hG).2.2)⟩

/-- The vertices of a nonempty walk are nodes. -/
lemma mem_V_of_mem_support {I : Inst Unit} {u v : ℕ} (p : I.G.Walk u v) (hp : ¬ p.Nil) {y : ℕ}
    (hy : y ∈ p.support) : y ∈ I.V := by
  induction p with
  | nil => simp at hp
  | @cons a b c h q ih =>
    rw [Walk.support_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact I.sub h
    · by_cases hq : q.Nil
      · cases q with
        | nil => simp only [Walk.support_nil, List.mem_singleton] at hy; exact hy ▸ I.sub' h
        | cons _ _ => simp at hq
      · exact ih hq hy

/-- Acyclicity is reflected by homomorphisms injective on the nodes. -/
-- CSLib candidate
lemma isAcyclic_of_hom_injOn {A B : Inst Unit} (f : A.G →g B.G) (hinj : Set.InjOn f A.V)
    (hB : B.G.IsAcyclic) : A.G.IsAcyclic := by
  intro x c hc
  rw [Walk.isCycle_iff_isPath_tail_and_le_length] at hc
  refine hB (c.map f) ?_
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  have hnil : ¬ c.Nil := fun hn => by have := hn.length_eq_zero; omega
  have hnil' : ¬ (c.map f).Nil := by simpa using hnil
  refine ⟨?_, by simpa using hc.2⟩
  have h1 := hc.1
  rw [Walk.isPath_def, Walk.support_tail_of_not_nil _ hnil] at h1
  rw [Walk.isPath_def, Walk.support_tail_of_not_nil _ hnil', Walk.support_map, ← List.map_tail]
  refine h1.map_on fun a ha b hb hab => hinj ?_ ?_ hab
  · exact mem_V_of_mem_support c hnil (List.mem_of_mem_tail ha)
  · exact mem_V_of_mem_support c hnil (List.mem_of_mem_tail hb)


/-! ### Tree codes: nondecreasing parent sequences in stars-and-bars form -/

/-- Stars-and-bars code of a nondecreasing sequence (starting above `b`): for each entry `x`
after the previous entry `b`, write `x - b` zeros and a one. -/
def sbEnc : ℕ → List ℕ → List Bool
  | _, [] => []
  | b, x :: xs => List.replicate (x - b) false ++ true :: sbEnc x xs

/-- Decoder of `sbEnc`: every one outputs the number of zeros read so far. -/
def sbDec : ℕ → List Bool → List ℕ
  | _, [] => []
  | z, false :: w => sbDec (z + 1) w
  | z, true :: w => z :: sbDec z w

lemma sbDec_replicate (z k : ℕ) (w : List Bool) :
    sbDec z (List.replicate k false ++ w) = sbDec (z + k) w := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, sbDec, ih]
    congr 1; omega

lemma sbDec_sbEnc : ∀ (b : ℕ) (xs : List ℕ), List.Pairwise (· ≤ ·) (b :: xs) →
    sbDec b (sbEnc b xs) = xs
  | _, [], _ => rfl
  | b, x :: xs, h => by
    have hbx : b ≤ x := (List.pairwise_cons.1 h).1 x (by simp)
    have h' := (List.pairwise_cons.1 h).2
    rw [sbEnc, sbDec_replicate, Nat.add_sub_cancel' hbx, sbDec, sbDec_sbEnc x xs h']

lemma length_sbEnc_le : ∀ (b : ℕ) (xs : List ℕ) (M : ℕ), List.Pairwise (· ≤ ·) (b :: xs) →
    (∀ x ∈ xs, x ≤ M) → b ≤ M → (sbEnc b xs).length ≤ xs.length + (M - b)
  | _, [], _, _, _, _ => by simp [sbEnc]
  | b, x :: xs, M, h, hM, hb => by
    have hbx : b ≤ x := (List.pairwise_cons.1 h).1 x (by simp)
    have ih := length_sbEnc_le x xs M (List.pairwise_cons.1 h).2
      (fun y hy => hM y (by simp [hy])) (hM x (by simp))
    have hxM : x ≤ M := hM x (by simp)
    simp only [sbEnc, List.length_append, List.length_replicate, List.length_cons]
    omega

/-- Adjacency in the tree with parent sequence `ps`: node `k + 2` is a child of node
`ps[k] + 1` (entries with `ps[k] > k` are ignored). -/
def TreeAdj (ps : List ℕ) (x y : ℕ) : Prop :=
  ∃ k < ps.length, ps.getD k 0 ≤ k ∧
    ((x = k + 2 ∧ y = ps.getD k 0 + 1) ∨ (y = k + 2 ∧ x = ps.getD k 0 + 1))

/-- The graph with parent sequence `ps`. -/
def treeGraph (ps : List ℕ) : SimpleGraph ℕ where
  Adj := TreeAdj ps
  symm := ⟨fun _ _ ⟨k, hk, hle, h⟩ => ⟨k, hk, hle, h.symm⟩⟩
  loopless := ⟨fun _ ⟨_, _, hle, h⟩ => by omega⟩

/-- The tree with parent sequence `ps`, on the nodes `1, …, |ps| + 1`. -/
def treeOf (ps : List ℕ) : Inst Unit where
  V := (List.range' 1 (ps.length + 1)).toFinset
  G := treeGraph ps
  sub := by
    rintro x y ⟨k, hk, hle, h⟩
    simp only [List.mem_toFinset, List.mem_range'_1]
    omega
  S := ⊥
  S_le := bot_le
  lab := fun _ => ()

lemma mem_treeOf_V {ps : List ℕ} {x : ℕ} : x ∈ (treeOf ps).V ↔ 1 ≤ x ∧ x ≤ ps.length + 1 := by
  simp only [treeOf, List.mem_toFinset, List.mem_range'_1]
  omega

lemma treeOf_n (ps : List ℕ) : (treeOf ps).n = ps.length + 1 := by
  simp [Inst.n, treeOf, List.toFinset_card_of_nodup List.nodup_range']

/-! ### Every tree has a code (BFS numbering) -/

/-- `idxOf` is injective on the members of a list. -/
lemma idxOf_injOn {l : List ℕ} {x y : ℕ} (hx : x ∈ l) (hy : y ∈ l) (h : l.idxOf x = l.idxOf y) :
    x = y := by
  calc x = l[l.idxOf x]'(List.idxOf_lt_length_iff.2 hx) := (List.getElem_idxOf _).symm
    _ = l[l.idxOf y]'(List.idxOf_lt_length_iff.2 hy) := by simp only [h]
    _ = y := List.getElem_idxOf _

/-- For lists of equal length, `l ++ x < m ++ y` implies `l ≤ m`. -/
lemma le_of_append_lt {l m x y : List ℕ} (hlen : l.length = m.length) (h : l ++ x < m ++ y) :
    l ≤ m := by
  have key : ∀ (l m : List ℕ), m < l → m.length = l.length → m ++ y < l ++ x := by
    intro l m h h'
    induction m generalizing l with
    | nil => cases l <;> simp_all
    | cons a m ih =>
      cases l with
      | nil => simp at h'
      | cons b l =>
        simp only [List.cons_append, List.cons_lt_cons_iff] at h ⊢
        simp only [List.length_cons, add_left_inj] at h'
        rcases h with h | ⟨rfl, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨rfl, ih l h h'⟩
  by_contra hlm
  exact lt_asymm h (key l m (lt_of_not_ge hlm) hlen.symm)

section BFS

variable (H : Inst Unit) (r : ℕ)

open Classical in
/-- The BFS key of `v`: length and vertex list of the path from the root `r` (compared
lexicographically, i.e. shortlex on root paths). -/
noncomputable def key (v : ℕ) : ℕ ×ₗ List ℕ :=
  if h : H.G.Reachable r v then
    toLex (h.exists_isPath.choose.length, h.exists_isPath.choose.support)
  else toLex (0, [])

open Classical in
/-- The parent of `v`: the penultimate node of the path from the root. -/
noncomputable def parent (v : ℕ) : ℕ :=
  if h : H.G.Reachable r v then h.exists_isPath.choose.penultimate else 0

/-- The nodes in BFS order (sorted by `key`). -/
noncomputable def bfsList : List ℕ :=
  H.V.toList.mergeSort (fun a b => decide (key H r a ≤ key H r b))

/-- The BFS number of a node (`0` for the root). -/
noncomputable def bfsIdx (v : ℕ) : ℕ := (bfsList H r).idxOf v

/-- The parent sequence of the BFS numbering: entry `k` is the BFS number of the parent of the
node with BFS number `k + 1`. -/
noncomputable def bfsSeq : List ℕ :=
  (List.range (H.n - 1)).map fun k => bfsIdx H r (parent H r ((bfsList H r).getD (k + 1) 0))

variable {H r}

lemma chosen_eq (hac : H.G.IsAcyclic) {v : ℕ} (h : H.G.Reachable r v) (p : H.G.Walk r v)
    (hp : p.IsPath) : h.exists_isPath.choose = p :=
  congrArg Subtype.val ((hac.subsingleton_path r v).elim ⟨_, h.exists_isPath.choose_spec⟩ ⟨p, hp⟩)

lemma key_eq (hac : H.G.IsAcyclic) {v : ℕ} (p : H.G.Walk r v) (hp : p.IsPath) :
    key H r v = toLex (p.length, p.support) := by
  unfold key
  split_ifs with h
  · rw [chosen_eq hac h p hp]
  · exact absurd ⟨p⟩ h

lemma parent_eq (hac : H.G.IsAcyclic) {v : ℕ} (p : H.G.Walk r v) (hp : p.IsPath) :
    parent H r v = p.penultimate := by
  unfold parent
  split_ifs with h
  · rw [chosen_eq hac h p hp]
  · exact absurd ⟨p⟩ h

variable (hac : H.G.IsAcyclic) (hcon : H.Conn) (hr : r ∈ H.V)
include hac hcon hr

omit hac in
lemma exists_path {v : ℕ} (hv : v ∈ H.V) : ∃ p : H.G.Walk r v, p.IsPath :=
  (hcon.2 r hr v hv).exists_isPath

lemma key_injOn : Set.InjOn (key H r) H.V := by
  intro u hu w hw h
  obtain ⟨p, hp⟩ := exists_path hcon hr hu
  obtain ⟨q, hq⟩ := exists_path hcon hr hw
  rw [key_eq hac p hp, key_eq hac q hq] at h
  have hs : p.support = q.support := congrArg Prod.snd (toLex.injective h)
  have h1 := p.getLast_support
  have h2 := q.getLast_support
  simp only [hs] at h1
  exact h1.symm.trans h2

omit hcon hr in
lemma key_root : key H r r = toLex (0, [r]) := by
  rw [key_eq hac Walk.nil Walk.IsPath.nil]; rfl

lemma parent_spec {v : ℕ} (hv : v ∈ H.V) (hvr : v ≠ r) :
    parent H r v ∈ H.V ∧ H.G.Adj (parent H r v) v ∧ ∃ p : H.G.Walk r (parent H r v), p.IsPath ∧
      key H r (parent H r v) = toLex (p.length, p.support) ∧
      key H r v = toLex (p.length + 1, p.support ++ [v]) := by
  obtain ⟨q, hq⟩ := exists_path hcon hr hv
  have hnil : ¬ q.Nil := fun h => hvr h.eq.symm
  rw [parent_eq hac q hq]
  have hadj := q.adj_penultimate hnil
  refine ⟨H.sub hadj, hadj, q.dropLast, hq.dropLast, key_eq hac _ hq.dropLast, ?_⟩
  rw [key_eq hac q hq, Walk.length_dropLast_add_one hnil, Walk.support_dropLast_concat hnil]

lemma key_parent_lt {v : ℕ} (hv : v ∈ H.V) (hvr : v ≠ r) :
    key H r (parent H r v) < key H r v := by
  obtain ⟨-, -, p, -, h1, h2⟩ := parent_spec hac hcon hr hv hvr
  rw [h1, h2, Prod.Lex.toLex_lt_toLex]
  exact Or.inl (Nat.lt_succ_self _)

lemma key_root_lt {v : ℕ} (hv : v ∈ H.V) (hvr : v ≠ r) : key H r r < key H r v := by
  obtain ⟨-, -, p, -, -, h2⟩ := parent_spec hac hcon hr hv hvr
  rw [key_root hac, h2, Prod.Lex.toLex_lt_toLex]
  exact Or.inl (Nat.succ_pos _)

/-- Every edge of a tree joins a node and its parent. -/
lemma adj_cases {u w : ℕ} (h : H.G.Adj u w) :
    (w ≠ r ∧ parent H r w = u) ∨ (u ≠ r ∧ parent H r u = w) := by
  classical
  obtain ⟨p, hp⟩ := exists_path hcon hr (H.sub h)
  obtain ⟨q, hq⟩ := exists_path hcon hr (H.sub' h)
  by_cases hu : u ∈ q.support
  · have hqe := hac.path_concat hp hq h hu
    left
    refine ⟨fun hwr => ?_, ?_⟩
    · subst hwr
      have h1 := congrArg Walk.length hqe
      have h0 := (Walk.isPath_iff_nil.1 hq).length_eq_zero
      simp only [Walk.length_concat] at h1
      omega
    · rw [parent_eq hac q hq, hqe, Walk.penultimate_concat]
  · have hw := hac.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq h hu
    have hpe := hac.path_concat hq hp h.symm hw
    right
    refine ⟨fun hur => ?_, ?_⟩
    · subst hur
      have h1 := congrArg Walk.length hpe
      have h0 := (Walk.isPath_iff_nil.1 hp).length_eq_zero
      simp only [Walk.length_concat] at h1
      omega
    · rw [parent_eq hac p hp, hpe, Walk.penultimate_concat]

/-- BFS monotonicity: the parents of nodes are in the same order as the nodes. -/
lemma key_parent_mono {u w : ℕ} (hu : u ∈ H.V) (hur : u ≠ r) (hw : w ∈ H.V) (hwr : w ≠ r)
    (h : key H r u < key H r w) : key H r (parent H r u) ≤ key H r (parent H r w) := by
  obtain ⟨-, -, p, -, hkp, hku⟩ := parent_spec hac hcon hr hu hur
  obtain ⟨-, -, q, -, hkq, hkw⟩ := parent_spec hac hcon hr hw hwr
  rw [hkp, hkq]
  rw [hku, hkw, Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨h1, h2⟩
  · exact le_of_lt (Prod.Lex.toLex_lt_toLex.2 (Or.inl (by simp only at h ⊢; omega)))
  · simp only [add_left_inj] at h1 h2
    have hlen : p.support.length = q.support.length := by simp [Walk.length_support, h1]
    exact Prod.Lex.toLex_le_toLex.2 (Or.inr ⟨h1, le_of_append_lt hlen h2⟩)

/-! #### The BFS numbering -/

omit hac hcon hr in
lemma bfsList_perm : (bfsList H r).Perm H.V.toList := List.mergeSort_perm _ _

omit hac hcon hr in
lemma bfsList_nodup : (bfsList H r).Nodup := bfsList_perm.nodup_iff.2 H.V.nodup_toList

omit hac hcon hr in
lemma mem_bfsList {v : ℕ} : v ∈ bfsList H r ↔ v ∈ H.V := by
  rw [bfsList_perm.mem_iff, Finset.mem_toList]

omit hac hcon hr in
lemma length_bfsList : (bfsList H r).length = H.n := by
  rw [bfsList_perm.length_eq, Finset.length_toList]; rfl

lemma key_bfsList_lt {i j : ℕ} (hi : i < (bfsList H r).length) (hj : j < (bfsList H r).length)
    (hij : i < j) : key H r (bfsList H r)[i] < key H r (bfsList H r)[j] := by
  have hs := List.pairwise_mergeSort (le := fun a b => decide (key H r a ≤ key H r b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact hab.trans hbc)
    (fun a b => by simpa using le_total _ _) H.V.toList
  have hle := List.pairwise_iff_getElem.1 hs i j hi hj hij
  simp only [decide_eq_true_eq] at hle
  refine lt_of_le_of_ne hle fun heq => ?_
  have hne : (bfsList H r)[i] ≠ (bfsList H r)[j] := fun h =>
    (Nat.ne_of_lt hij) ((bfsList_nodup.getElem_inj_iff).1 h)
  exact hne (key_injOn hac hcon hr (mem_bfsList.1 (List.getElem_mem _))
    (mem_bfsList.1 (List.getElem_mem _)) heq)

omit hac hcon hr in
lemma bfsIdx_lt {v : ℕ} (hv : v ∈ H.V) : bfsIdx H r v < H.n := by
  rw [← length_bfsList (r := r)]
  exact List.idxOf_lt_length_iff.2 (mem_bfsList.2 hv)

omit hac hcon hr in
lemma getElem_bfsIdx {v : ℕ} (hv : v ∈ H.V) :
    (bfsList H r)[bfsIdx H r v]'(List.idxOf_lt_length_iff.2 (mem_bfsList.2 hv)) = v :=
  List.getElem_idxOf _

omit hac hcon hr in
lemma bfsIdx_getElem {i : ℕ} (hi : i < (bfsList H r).length) :
    bfsIdx H r (bfsList H r)[i] = i :=
  bfsList_nodup.idxOf_getElem i hi

lemma bfsIdx_lt_iff {u w : ℕ} (hu : u ∈ H.V) (hw : w ∈ H.V) :
    bfsIdx H r u < bfsIdx H r w ↔ key H r u < key H r w := by
  have hu' := List.idxOf_lt_length_iff.2 (mem_bfsList (r := r) |>.2 hu)
  have hw' := List.idxOf_lt_length_iff.2 (mem_bfsList (r := r) |>.2 hw)
  constructor
  · intro h
    have := key_bfsList_lt hac hcon hr hu' hw' h
    rwa [List.getElem_idxOf, List.getElem_idxOf] at this
  · intro h
    by_contra hle
    rcases (not_lt.1 hle).lt_or_eq with hlt | heq
    · have := key_bfsList_lt hac hcon hr hw' hu' hlt
      rw [List.getElem_idxOf, List.getElem_idxOf] at this
      exact lt_asymm h this
    · have : w = u := by
        have h1 := getElem_bfsIdx (r := r) hu
        have h2 := getElem_bfsIdx (r := r) hw
        simp only [bfsIdx] at h1 h2 heq
        simp only [heq] at h2
        exact h2.symm.trans h1
      subst this
      exact lt_irrefl _ h

lemma bfsIdx_le_of_key_le {u w : ℕ} (hu : u ∈ H.V) (hw : w ∈ H.V)
    (h : key H r u ≤ key H r w) : bfsIdx H r u ≤ bfsIdx H r w := by
  by_contra hlt
  exact absurd h (not_le.2 ((bfsIdx_lt_iff hac hcon hr hw hu).1 (not_le.1 hlt)))

lemma bfsIdx_root : bfsIdx H r r = 0 := by
  by_contra h0
  have hlen : 0 < (bfsList H r).length := by
    rw [length_bfsList]; exact Finset.card_pos.2 ⟨r, hr⟩
  set v := (bfsList H r)[0]
  have hv : v ∈ H.V := mem_bfsList.1 (List.getElem_mem _)
  have hv0 : bfsIdx H r v = 0 := bfsIdx_getElem hlen
  have hvr : v ≠ r := fun h => h0 (h ▸ hv0)
  have := (bfsIdx_lt_iff hac hcon hr hr hv).2 (key_root_lt hac hcon hr hv hvr)
  omega

lemma bfsIdx_ne_zero {v : ℕ} (hv : v ∈ H.V) (hvr : v ≠ r) : bfsIdx H r v ≠ 0 := by
  intro h
  rw [← bfsIdx_root hac hcon hr] at h
  exact hvr (idxOf_injOn (mem_bfsList.2 hv) (mem_bfsList.2 hr) h)

omit hac hcon hr in
lemma getD_bfsList_mem {i : ℕ} (hi : i < H.n) : (bfsList H r).getD i 0 ∈ H.V := by
  rw [← length_bfsList (r := r)] at hi
  rw [List.getD_eq_getElem _ _ hi]
  exact mem_bfsList.1 (List.getElem_mem _)

omit hac hcon hr in
lemma bfsIdx_getD {i : ℕ} (hi : i < H.n) : bfsIdx H r ((bfsList H r).getD i 0) = i := by
  rw [← length_bfsList (r := r)] at hi
  rw [List.getD_eq_getElem _ _ hi]
  exact bfsIdx_getElem hi

omit hac hcon hr in
lemma getD_bfsIdx {v : ℕ} (hv : v ∈ H.V) : (bfsList H r).getD (bfsIdx H r v) 0 = v := by
  unfold bfsIdx
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.2 (mem_bfsList.2 hv))]
  exact getElem_bfsIdx hv

omit hac hcon hr in
lemma length_bfsSeq : (bfsSeq H r).length = H.n - 1 := by simp [bfsSeq]

omit hac hcon hr in
lemma bfsSeq_getD {k : ℕ} (hk : k < H.n - 1) :
    (bfsSeq H r).getD k 0 = bfsIdx H r (parent H r ((bfsList H r).getD (k + 1) 0)) := by
  simp [bfsSeq, List.getD_eq_getElem?_getD, hk]

lemma bfsSeq_getD_lt {k : ℕ} (hk : k < H.n - 1) : (bfsSeq H r).getD k 0 < k + 1 := by
  rw [bfsSeq_getD hk]
  have hw := getD_bfsList_mem (r := r) (show k + 1 < H.n by omega)
  have hwi := bfsIdx_getD (r := r) (show k + 1 < H.n by omega)
  have hwr : (bfsList H r).getD (k + 1) 0 ≠ r := fun h => by
    rw [h, bfsIdx_root hac hcon hr] at hwi; omega
  have := (bfsIdx_lt_iff hac hcon hr (parent_spec hac hcon hr hw hwr).1 hw).2
    (key_parent_lt hac hcon hr hw hwr)
  omega

lemma bfsSeq_pairwise : List.Pairwise (· ≤ ·) (0 :: bfsSeq H r) := by
  refine List.pairwise_cons.2 ⟨fun _ _ => Nat.zero_le _, ?_⟩
  unfold bfsSeq
  refine List.pairwise_map.2 (List.pairwise_lt_range.imp_of_mem fun {a b} ha hb hab => ?_)
  rw [List.mem_range] at ha hb
  have hu := getD_bfsList_mem (r := r) (show a + 1 < H.n by omega)
  have hw := getD_bfsList_mem (r := r) (show b + 1 < H.n by omega)
  have hui := bfsIdx_getD (r := r) (show a + 1 < H.n by omega)
  have hwi := bfsIdx_getD (r := r) (show b + 1 < H.n by omega)
  have hur : (bfsList H r).getD (a + 1) 0 ≠ r := fun h => by
    rw [h, bfsIdx_root hac hcon hr] at hui; omega
  have hwr : (bfsList H r).getD (b + 1) 0 ≠ r := fun h => by
    rw [h, bfsIdx_root hac hcon hr] at hwi; omega
  have hkey := (bfsIdx_lt_iff hac hcon hr hu hw).1 (by omega)
  exact bfsIdx_le_of_key_le hac hcon hr (parent_spec hac hcon hr hu hur).1
    (parent_spec hac hcon hr hw hwr).1 (key_parent_mono hac hcon hr hu hur hw hwr hkey)

/-- The BFS numbering `v ↦ bfsIdx v + 1` is an isomorphism onto `treeOf (bfsSeq H r)`, with
inverse `x ↦ bfsList[x - 1]`; both are covering maps. -/
lemma bfs_isCovering :
    IsCovering (fun v => bfsIdx H r v + 1) H (treeOf (bfsSeq H r)) ∧
    IsCovering (fun x => (bfsList H r).getD (x - 1) 0) (treeOf (bfsSeq H r)) H := by
  have hn : 1 ≤ H.n := Finset.card_pos.2 ⟨r, hr⟩
  have hmemT : ∀ x, x ∈ (treeOf (bfsSeq H r)).V ↔ 1 ≤ x ∧ x ≤ H.n := fun x => by
    rw [mem_treeOf_V, length_bfsSeq]; omega
  have hne : ∀ v ∈ H.V, v ≠ r → 1 ≤ bfsIdx H r v := fun v hv hvr =>
    Nat.one_le_iff_ne_zero.2 (bfsIdx_ne_zero hac hcon hr hv hvr)
  -- forward homomorphism
  have hfw : ∀ u w, H.G.Adj u w → (treeOf (bfsSeq H r)).G.Adj (bfsIdx H r u + 1)
      (bfsIdx H r w + 1) := by
    -- the edge from a child `w` to its parent `u`
    have key : ∀ u w, H.G.Adj u w → w ≠ r → parent H r w = u →
        ∃ k < (bfsSeq H r).length, (bfsSeq H r).getD k 0 ≤ k ∧ bfsIdx H r w + 1 = k + 2 ∧
          bfsIdx H r u + 1 = (bfsSeq H r).getD k 0 + 1 := by
      intro u w h hwr hpar
      have hw := H.sub' h
      have h1 := hne w hw hwr
      have h2 := bfsIdx_lt (r := r) hw
      refine ⟨bfsIdx H r w - 1, by rw [length_bfsSeq]; omega, ?_, by omega, ?_⟩
      · have := bfsSeq_getD_lt hac hcon hr (show bfsIdx H r w - 1 < H.n - 1 by omega)
        omega
      · rw [bfsSeq_getD (show bfsIdx H r w - 1 < H.n - 1 by omega),
          show bfsIdx H r w - 1 + 1 = bfsIdx H r w by omega, getD_bfsIdx hw, hpar]
    intro u w h
    rcases adj_cases hac hcon hr h with ⟨hwr, hpar⟩ | ⟨hur, hpar⟩
    · obtain ⟨k, hk, hle, h1, h2⟩ := key u w h hwr hpar
      exact ⟨k, hk, hle, Or.inr ⟨h1, h2⟩⟩
    · obtain ⟨k, hk, hle, h1, h2⟩ := key w u h.symm hur hpar
      exact ⟨k, hk, hle, Or.inl ⟨h1, h2⟩⟩
  -- backward homomorphism
  have hbw : ∀ x y, (treeOf (bfsSeq H r)).G.Adj x y →
      H.G.Adj ((bfsList H r).getD (x - 1) 0) ((bfsList H r).getD (y - 1) 0) := by
    rintro x y ⟨k, hk, hle, h⟩
    rw [length_bfsSeq] at hk
    have hw := getD_bfsList_mem (r := r) (show k + 1 < H.n by omega)
    have hwi := bfsIdx_getD (r := r) (show k + 1 < H.n by omega)
    have hwr : (bfsList H r).getD (k + 1) 0 ≠ r := fun h => by
      rw [h, bfsIdx_root hac hcon hr] at hwi; omega
    obtain ⟨hpV, hpadj, -⟩ := parent_spec hac hcon hr hw hwr
    have hp : (bfsList H r).getD ((bfsSeq H r).getD k 0 + 1 - 1) 0 =
        parent H r ((bfsList H r).getD (k + 1) 0) := by
      rw [Nat.add_sub_cancel, bfsSeq_getD hk, getD_bfsIdx hpV]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hp, show k + 2 - 1 = k + 1 by omega]; exact hpadj.symm
    · rw [hp, show k + 2 - 1 = k + 1 by omega]; exact hpadj
  have hfV : Set.MapsTo (fun v => bfsIdx H r v + 1) H.V (treeOf (bfsSeq H r)).V :=
    fun v hv => (hmemT _).2 (by have := bfsIdx_lt (r := r) hv; dsimp only; omega)
  have hbV : Set.MapsTo (fun x => (bfsList H r).getD (x - 1) 0) (treeOf (bfsSeq H r)).V H.V :=
    fun x hx => getD_bfsList_mem (by have := (hmemT x).1 hx; omega)
  have hbf : ∀ v ∈ H.V, (bfsList H r).getD (bfsIdx H r v + 1 - 1) 0 = v := fun v hv => by
    rw [Nat.add_sub_cancel]; exact getD_bfsIdx hv
  have hfb : ∀ x ∈ (treeOf (bfsSeq H r)).V,
      bfsIdx H r ((bfsList H r).getD (x - 1) 0) + 1 = x := fun x hx => by
    have := (hmemT x).1 hx
    rw [bfsIdx_getD (by omega)]; omega
  exact ⟨IsCovering.of_inverse hfw hbw hfV hbV hbf hfb,
    IsCovering.of_inverse hbw hfw hbV hfV hfb hbf⟩

end BFS

/-! ### The `O(n)` scheme for trees -/

/-- Decoding of a tree code. -/
def decTree (w : List Bool) : Inst Unit := treeOf (sbDec 0 w)

/-- Every tree `H` is isomorphic to a decoded tree code of at most `2n` bits: there is a covering
map (in fact an isomorphism) `e : H → decTree w` with `e v ≤ n`, and `H` is a lift of
`decTree w`. -/
theorem exists_treeCode {H : Inst Unit} (hH : H ∈ TreeFam) :
    ∃ (w : List Bool) (e : ℕ → ℕ), w.length ≤ 2 * H.n ∧ decTree w ∈ TreeFam ∧
      IsLift (decTree w) H ∧ IsCovering e H (decTree w) ∧ (∀ v ∈ H.V, e v ≤ H.n) ∧
      (decTree w).n = H.n := by
  obtain ⟨r, hr⟩ := hH.1.1
  have hac := hH.2.2
  have hcon := hH.1
  have hn : 1 ≤ H.n := Finset.card_pos.2 ⟨r, hr⟩
  obtain ⟨hf, hb⟩ := bfs_isCovering hac hcon hr
  have hps := bfsSeq_pairwise hac hcon hr
  have hdec : decTree (sbEnc 0 (bfsSeq H r)) = treeOf (bfsSeq H r) := by
    rw [decTree, sbDec_sbEnc 0 _ hps]
  refine ⟨sbEnc 0 (bfsSeq H r), _, ?_, ?_, ⟨_, hdec ▸ hb⟩, hdec ▸ hf, fun v hv => ?_, ?_⟩
  · have := length_sbEnc_le 0 (bfsSeq H r) H.n hps (fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
      rw [← List.getD_eq_getElem _ 0 hk]
      rw [length_bfsSeq] at hk
      have := bfsSeq_getD_lt hac hcon hr hk
      omega) (Nat.zero_le _)
    rw [length_bfsSeq] at this
    omega
  · rw [hdec]
    exact ⟨hf.conn hcon, rfl, isAcyclic_of_hom_injOn hb.hom
      (hb.injOn_of_isAcyclic (hf.conn hcon) hac) hac⟩
  · have := mem_treeOf_V.1 (hf.mapsTo hv)
    rw [length_bfsSeq] at this
    omega
  · rw [hdec, treeOf_n, length_bfsSeq]; omega

/-- The scheme for trees, on any family `F` of trees containing the decoded tree codes of the
right size. -/
theorem tree_upper_of {F P : Set (Inst Unit)} (hF : ∀ I ∈ F, I ∈ TreeFam)
    (hcl : ∀ I ∈ F, ∀ w, decTree w ∈ TreeFam → (decTree w).n = I.n → decTree w ∈ F)
    (hP : ClosedUnderIso F P) : AdmitsPNLCP F P (fun n => 8 * n) :=
  admitsPNLCP_of_codes decTree (encK := id) Function.injective_id (fun I hI => (hF I hI).1)
    (closedUnderLifts_of_closedUnderIso hF hP) _ fun H hH => by
      obtain ⟨w, e, hw, hT, hlift, hcov, he, hTn⟩ := exists_treeCode (hF H hH)
      refine ⟨w, e, hcl H hH w hT hTn, hlift, hcov, fun v hv => ?_⟩
      have h2 : (Nat.bits (e v)).length ≤ H.n := by
        rw [Nat.size_eq_bits_len]; exact (size_le_self _).trans (he v hv)
      have hn : 1 ≤ H.n := Finset.card_pos.2 (hF H hH).1.1
      simp only [encLabel, id, length_encList, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega

/-- **Section 6.2** of [GS16]: on trees, every graph property (i.e. closed under isomorphism)
admits locally checkable proofs of size `O(n)`, explicitly `8n`; the verifier is even a
(one-round) port-numbering verifier. -/
theorem tree_upper (P : Set (Inst Unit)) (hP : ClosedUnderIso TreeFam P) :
    AdmitsPNLCP TreeFam P (fun n => 8 * n) :=
  tree_upper_of (fun _ h => h) (fun _ _ _ h _ => h) hP

/-- **Section 6.2** of [GS16], with the paper's identifier range `[1, n^c]` (`c ≥ 1`) and the usual
(identifier-aware) verifiers. -/
theorem tree_upper_idBound (c : ℕ) (hc : 1 ≤ c) (P : Set (Inst Unit))
    (hP : ClosedUnderIso {I | I ∈ TreeFam ∧ I.IdBound c} P) :
    AdmitsLCP {I | I ∈ TreeFam ∧ I.IdBound c} P (fun n => 8 * n) := by
  refine (tree_upper_of (F := {I | I ∈ TreeFam ∧ I.IdBound c}) (fun _ h => h.1)
    (fun I hI w hT hTn => ?_) hP).admitsLCP
  refine ⟨hT, fun x hx => ?_⟩
  have hx' := mem_treeOf_V.1 hx
  have hn : 1 ≤ I.n := Finset.card_pos.2 hI.1.1.1
  have : (decTree w).n = (sbDec 0 w).length + 1 := treeOf_n _
  refine ⟨hx'.1, ?_⟩
  calc x ≤ (decTree w).n := by omega
    _ = (decTree w).n ^ 1 := (pow_one _).symm
    _ ≤ (decTree w).n ^ c := Nat.pow_le_pow_right (by omega) hc

end Podc.LocallyCheckableProofs.Trees
