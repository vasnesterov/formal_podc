import Papers.PODC2026.TreeAA.Protocol

/-!
# Block graphs (Section 5): `BlockGraphAA` and Theorem 8

* `IsMaxClique`, `IsBlockGraph` (distinct maximal cliques share at most one vertex),
  `IsCliqueTree G T bag` (a tree `T` whose nodes are exactly the maximal cliques `bag c` of `G`,
  adjacent cliques intersect, running intersection property).
* `subdiv T` — the subdivided clique tree `T_S` (one intermediate vertex `inr e` per edge `e`).
* `blockOut` — the output map of `BlockGraphAA` (lines 4–5).
* `sep_mem_support` / `sep_btw` — **Lemma 12** (clique-tree edge separator).
* `blockOut_spec` — **Lemmas 13 and 14** at spec level (model independent: also covers the
  asynchronous Corollary 6 at the level of the reduction).
* `blockGraphAA_solves` — **Theorem 8** (round complexity: that of the tree protocol on `T_S`).
* `subdiv_isTree`, `diam_subdiv_le` — `T_S` is a tree and `D(T_S) ≤ 2·D(T)`.
* `blockGraphAA_of_gc_realAA` — Theorem 8 instantiated with `TreeAA` (Theorem 5).

Auxiliary material: the lift `liftW` of `T`-walks to `T_S` and the description `btw_subdiv` of
paths of `T_S` between clique vertices; sides of a tree edge (`side_or`, `btw_cross`); and
`eq_of_mem_cross` (a vertex in cliques on both sides of `{c, c'}` is the separator `u`).

Proof notes. Lemma 12 is proved by induction along the walk with the invariant "the current vertex
is not `u` and all cliques containing it are on `c`'s side" (the appendix proof's step "`T_P`
meets both components, so some `v_i` lies in `bag c ∩ bag c'`" is made precise this way). In
Case 3 of Lemma 13 (`cout = c` a clique with `v_in ∉ bag c`) the paper claims the output is the
separator towards the honest clique `c_b`; in fact it is the separator `u''` towards the party's
*own* clique `cin p` (the vertex of `bag c` closest to `v_in`). The output is still valid: `c` lies
between `cin p` and one of the honest cliques `c_a, c_b` (tripod), and by Lemma 12 `u''` lies on
a shortest path from `v_in` to that party's input.
-/

namespace TreeAA

open Cslib.Byzantine.LockStep SimpleGraph

section Defs

variable {V C : Type*} (G : SimpleGraph V)

/-- A maximal clique of `G`. -/
def IsMaxClique (K : Finset V) : Prop :=
  G.IsClique (K : Set V) ∧ ∀ K' : Finset V, G.IsClique (K' : Set V) → K ⊆ K' → K' = K

/-- A *block graph*: any two distinct maximal cliques share at most one vertex. (The paper's
definition is "chordal, and maximal cliques pairwise share at most one vertex"; chordality is
provided by the clique tree `IsCliqueTree`.) -/
def IsBlockGraph [DecidableEq V] : Prop :=
  ∀ K K', IsMaxClique G K → IsMaxClique G K' → K ≠ K' → (K ∩ K').card ≤ 1

/-- `(T, bag)` is a *clique tree* of `G`: `T` is a tree whose nodes `c` are labelled injectively
by the maximal cliques `bag c` of `G` (all of them), adjacent nodes have intersecting cliques,
and the running intersection property holds: `bag c ∩ bag c'` is contained in every clique on
the path between `c` and `c'`. -/
structure IsCliqueTree [DecidableEq V] (T : SimpleGraph C) (bag : C → Finset V) : Prop where
  isTree : T.IsTree
  isMaxClique : ∀ c, IsMaxClique G (bag c)
  injective : Function.Injective bag
  surjective : ∀ K, IsMaxClique G K → ∃ c, bag c = K
  adj_nonempty : ∀ c c', T.Adj c c' → (bag c ∩ bag c').Nonempty
  rip : ∀ c c' d, Btw T c d c' → bag c ∩ bag c' ⊆ bag d

/-- The *subdivided clique tree* `T_S`: every edge `e = {c, c'}` of `T` is replaced by a path
`c — inr e — c'`. -/
def subdiv (T : SimpleGraph C) : SimpleGraph (C ⊕ T.edgeSet) :=
  SimpleGraph.fromRel fun a b => ∃ c e, a = Sum.inl c ∧ b = Sum.inr e ∧ c ∈ (e : Sym2 C)

variable [DecidableEq V] {T : SimpleGraph C} (bag : C → Finset V)

open Classical in
/-- The output map of `BlockGraphAA` (lines 4–5): for a clique vertex, the vertex of the clique
closest to the own input `v`; for an intermediate vertex of the edge `{c, c'}`, the vertex in
`bag c ∩ bag c'`. (The fallback `v` is never used for honest parties.) -/
noncomputable def blockOut (v : V) : C ⊕ T.edgeSet → V
  | .inl c => if h : (bag c).Nonempty then ((bag c).exists_min_image (G.dist v) h).choose else v
  | .inr e => if h : ∃ u, ∀ c ∈ (e : Sym2 C), u ∈ bag c then h.choose else v

/-- **`BlockGraphAA`**: run a tree-AA protocol `treeAlg` on `T_S` with input a clique `cl p v`
containing the own input `v`, and map the output back with `blockOut`. -/
noncomputable def blockGraphAA {P M : Type*} (cl : P → V → C)
    (treeAlg : Protocol P (C ⊕ T.edgeSet) M (C ⊕ T.edgeSet)) : Protocol P V M V :=
  treeAlg.wrap (fun p v => Sum.inl (cl p v)) (fun _ v c => blockOut G bag v c)

end Defs

/-! ### The subdivided tree -/

section Subdiv

variable {C : Type*} {T : SimpleGraph C}

@[simp] lemma subdiv_adj_inl_inr {c : C} {e : T.edgeSet} :
    (subdiv T).Adj (Sum.inl c) (Sum.inr e) ↔ c ∈ (e : Sym2 C) := by
  simp [subdiv, SimpleGraph.fromRel_adj]

@[simp] lemma subdiv_adj_inr_inl {c : C} {e : T.edgeSet} :
    (subdiv T).Adj (Sum.inr e) (Sum.inl c) ↔ c ∈ (e : Sym2 C) := by
  rw [adj_comm]; exact subdiv_adj_inl_inr

@[simp] lemma subdiv_not_adj_inl_inl {c c' : C} : ¬ (subdiv T).Adj (Sum.inl c) (Sum.inl c') := by
  simp [subdiv]

@[simp] lemma subdiv_not_adj_inr_inr {e e' : T.edgeSet} :
    ¬ (subdiv T).Adj (Sum.inr e) (Sum.inr e') := by
  simp [subdiv]

lemma exists_eq_edge (e : T.edgeSet) : ∃ c c', T.Adj c c' ∧ (e : Sym2 C) = s(c, c') := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h c c' => exact ⟨c, c', he, rfl⟩

/-- The edge `s(a, b)` of `T` as an element of `T.edgeSet`. -/
def edgeOf {a b : C} (h : T.Adj a b) : T.edgeSet := ⟨s(a, b), h⟩

/-- The lift of a walk of `T` to the subdivided tree `T_S`. -/
def liftW : ∀ {a b : C}, T.Walk a b → (subdiv T).Walk (Sum.inl a) (Sum.inl b)
  | _, _, .nil => .nil
  | a, _, .cons (v := b) h p =>
    .cons (subdiv_adj_inl_inr.2 (Sym2.mem_mk_left a b) :
        (subdiv T).Adj (Sum.inl a) (Sum.inr (edgeOf h)))
      (.cons (subdiv_adj_inr_inl.2 (Sym2.mem_mk_right a b)) (liftW p))

lemma length_liftW {a b : C} (p : T.Walk a b) : (liftW p).length = 2 * p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [liftW, Walk.length_cons, ih]; ring

lemma mem_support_liftW {a b : C} (p : T.Walk a b) (z : C ⊕ T.edgeSet) :
    z ∈ (liftW p).support ↔
      (∃ c ∈ p.support, z = Sum.inl c) ∨
        (∃ e : T.edgeSet, (e : Sym2 C) ∈ p.edges ∧ z = Sum.inr e) := by
  induction p with
  | nil => simp [liftW]
  | cons h p ih =>
    simp only [liftW, Walk.support_cons, List.mem_cons, ih, Walk.edges_cons]
    constructor
    · rintro (rfl | rfl | (⟨c, hc, rfl⟩ | ⟨e, he, rfl⟩))
      · exact Or.inl ⟨_, Or.inl rfl, rfl⟩
      · exact Or.inr ⟨_, Or.inl rfl, rfl⟩
      · exact Or.inl ⟨c, Or.inr hc, rfl⟩
      · exact Or.inr ⟨e, Or.inr he, rfl⟩
    · rintro (⟨c, hc, rfl⟩ | ⟨e, he, rfl⟩)
      · rcases hc with rfl | hc
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))
      · rcases he with he | he
        · exact Or.inr (Or.inl (by rw [show e = edgeOf h from Subtype.ext he]))
        · exact Or.inr (Or.inr (Or.inr ⟨e, he, rfl⟩))

lemma liftW_isPath {a b : C} {p : T.Walk a b} (hp : p.IsPath) : (liftW p).IsPath := by
  induction p with
  | nil => simp [liftW]
  | cons h p ih =>
    rw [Walk.cons_isPath_iff] at hp
    simp only [liftW, Walk.cons_isPath_iff, Walk.support_cons, List.mem_cons, mem_support_liftW]
    refine ⟨⟨ih hp.1, ?_⟩, ?_⟩
    · rintro (⟨c, -, hc⟩ | ⟨e, he, hee⟩)
      · exact Sum.inr_ne_inl hc
      · cases hee
        exact hp.2 (p.fst_mem_support_of_mem_edges he)
    · rintro (hc | ⟨c, hc', hc⟩ | ⟨e, -, hc⟩)
      · exact Sum.inl_ne_inr hc
      · obtain rfl := Sum.inl.inj hc; exact hp.2 hc'
      · exact Sum.inl_ne_inr hc

lemma subdiv_connected (hT : T.Connected) : (subdiv T).Connected := by
  have hne := hT.nonempty
  have hinl : ∀ a b : C, (subdiv T).Reachable (Sum.inl a) (Sum.inl b) := fun a b =>
    ⟨liftW (hT.preconnected a b).some⟩
  have hto : ∀ z : C ⊕ T.edgeSet, ∃ c, (subdiv T).Reachable z (Sum.inl c) := by
    rintro (c | e)
    · exact ⟨c, Reachable.refl _⟩
    · obtain ⟨c, c', -, he⟩ := exists_eq_edge e
      exact ⟨c, (subdiv_adj_inr_inl.2 (by rw [he]; exact Sym2.mem_mk_left c c')).reachable⟩
  have : Nonempty (C ⊕ T.edgeSet) := ⟨Sum.inl hne.some⟩
  refine ⟨fun z z' => ?_⟩
  obtain ⟨c, hc⟩ := hto z
  obtain ⟨c', hc'⟩ := hto z'
  exact hc.trans ((hinl c c').trans hc'.symm)

/-- Edges of `T_S` correspond to darts of `T`, hence `|E(T_S)| = 2 |E(T)|`. -/
lemma card_edgeSet_subdiv [Finite C] : Nat.card (subdiv T).edgeSet = 2 * Nat.card T.edgeSet := by
  classical
  have := Fintype.ofFinite C
  let f : T.Dart → (subdiv T).edgeSet := fun d =>
    ⟨s(Sum.inl d.fst, Sum.inr (edgeOf d.adj)), subdiv_adj_inl_inr.2 (Sym2.mem_mk_left _ _)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
      simp only [f, edgeOf, Subtype.mk.injEq, Sym2.eq_iff, Sum.inl.injEq, reduceCtorEq,
        false_and, or_false] at h
      obtain ⟨rfl, h⟩ := h
      obtain rfl := Sym2.congr_right.1 (congrArg Subtype.val (Sum.inr.inj h))
      rfl
    · rintro ⟨z, hz⟩
      revert hz
      induction z using Sym2.ind with
      | h x y =>
        intro hz
        rw [mem_edgeSet] at hz
        rcases x with c | e <;> rcases y with c' | e'
        · simp at hz
        · have hc : c ∈ (e' : Sym2 C) := subdiv_adj_inl_inr.1 hz
          refine ⟨⟨(c, Sym2.Mem.other hc), by
            rw [← mem_edgeSet, Sym2.other_spec]; exact e'.2⟩, ?_⟩
          simp only [f, edgeOf, Subtype.mk.injEq]
          congr 2
          exact Subtype.ext (Sym2.other_spec hc)
        · have hc : c' ∈ (e : Sym2 C) := subdiv_adj_inr_inl.1 hz
          refine ⟨⟨(c', Sym2.Mem.other hc), by
            rw [← mem_edgeSet, Sym2.other_spec]; exact e.2⟩, ?_⟩
          simp only [f, edgeOf, Subtype.mk.injEq]
          rw [Sym2.eq_swap]
          congr 2
          exact Subtype.ext (Sym2.other_spec hc)
        · simp at hz
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, dart_card_eq_twice_card_edges,
    edgeFinset_card, Nat.card_eq_fintype_card]

end Subdiv

section Proofs

variable {V C : Type*} [DecidableEq V] {G : SimpleGraph V} {T : SimpleGraph C}
  {bag : C → Finset V}

/-- The subdivided tree of a tree is a tree. -/
theorem subdiv_isTree [Finite C] (hT : T.IsTree) : (subdiv T).IsTree := by
  rw [isTree_iff_connected_and_card] at hT ⊢
  refine ⟨subdiv_connected hT.1, ?_⟩
  rw [card_edgeSet_subdiv, Nat.card_sum, ← hT.2]
  ring

/-- The path of `T_S` between two clique vertices `inl a`, `inl b` is the lift of the path of `T`
between `a` and `b`: its vertices are the `inl c` with `c` between `a` and `b`, and the `inr e`
for the edges `e = {c, c'}` of that path, where `c` is on `a`'s side and `c'` on `b`'s side. -/
lemma btw_subdiv [Finite C] (hT : T.IsTree) {a b : C} {z : C ⊕ T.edgeSet}
    (h : Btw (subdiv T) (Sum.inl a) z (Sum.inl b)) :
    (∃ c, z = Sum.inl c ∧ Btw T a c b) ∨
      (∃ e c c', z = Sum.inr e ∧ (e : Sym2 C) = s(c, c') ∧ T.Adj c c' ∧ Btw T a c c' ∧
        Btw T b c' c) := by
  classical
  have hTS := subdiv_isTree hT
  rw [← mem_tpath_iff hTS, ← eq_tpath hTS _ (liftW_isPath (tpath_isPath hT a b)),
    mem_support_liftW] at h
  rcases h with ⟨c, hc, rfl⟩ | ⟨e, he, rfl⟩
  · exact Or.inl ⟨c, rfl, (mem_tpath_iff hT).1 hc⟩
  · right
    obtain ⟨c, c', hcc', hee⟩ := exists_eq_edge e
    rw [hee] at he
    have h1 := (mem_tpath_iff hT).1 ((tpath hT a b).fst_mem_support_of_mem_edges he)
    have h2 := (mem_tpath_iff hT).1 ((tpath hT a b).snd_mem_support_of_mem_edges he)
    have d1 : T.dist c c' = 1 := dist_eq_one_iff_adj.2 hcc'
    have d2 : T.dist c' c = 1 := dist_eq_one_iff_adj.2 hcc'.symm
    have d3 : T.dist b c = T.dist c b := dist_comm
    have d4 : T.dist b c' = T.dist c' b := dist_comm
    unfold Btw at h1 h2
    rcases hT.dist_eq_dist_add_one_of_adj a hcc' with hd | hd
    · refine ⟨e, c', c, rfl, by rw [hee, Sym2.eq_swap], hcc'.symm, ?_, ?_⟩ <;> unfold Btw <;> omega
    · refine ⟨e, c, c', rfl, hee, hcc', ?_, ?_⟩ <;> unfold Btw <;> omega

/-- `D(T_S) ≤ 2 · D(T)`. -/
theorem diam_subdiv_le [Finite C] (hT : T.IsTree) : (subdiv T).diam ≤ 2 * T.diam := by
  have hTS := subdiv_isTree hT
  have : Nonempty C := hT.connected.nonempty
  have hD : ∀ a b : C, T.dist a b ≤ T.diam := fun a b =>
    dist_le_diam (connected_iff_ediam_ne_top.1 hT.connected)
  have hll : ∀ a b : C, (subdiv T).dist (Sum.inl a) (Sum.inl b) ≤ 2 * T.dist a b := by
    intro a b
    obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist a b
    calc _ ≤ (liftW p).length := dist_le _
      _ = _ := by rw [length_liftW, hp]
  have hrl : ∀ (e : T.edgeSet) (b : C),
      (subdiv T).dist (Sum.inr e) (Sum.inl b) + 1 ≤ 2 * T.diam := by
    intro e b
    obtain ⟨c, c', hcc', hee⟩ := exists_eq_edge e
    have key : ∀ x y : C, x ∈ (e : Sym2 C) → T.dist b x < T.dist b y →
        (subdiv T).dist (Sum.inr e) (Sum.inl b) + 1 ≤ 2 * T.diam := by
      intro x y hx hxy
      have h1 := hTS.connected.dist_triangle (u := Sum.inr e) (v := Sum.inl x) (w := Sum.inl b)
      have h2 : (subdiv T).dist (Sum.inr e) (Sum.inl x) = 1 :=
        dist_eq_one_iff_adj.2 (subdiv_adj_inr_inl.2 hx)
      have h3 := hll x b
      have h4 := hD b y
      have h5 : T.dist x b = T.dist b x := dist_comm
      omega
    rcases lt_or_gt_of_ne (hT.dist_ne_of_adj b hcc') with h | h
    · exact key c c' (by rw [hee]; exact Sym2.mem_mk_left _ _) h
    · exact key c' c (by rw [hee]; exact Sym2.mem_mk_right _ _) h
  obtain ⟨u, v, huv⟩ := (subdiv T).exists_dist_eq_diam
  rw [← huv]
  rcases u with a | e <;> rcases v with b | e'
  · exact (hll a b).trans (Nat.mul_le_mul_left 2 (hD a b))
  · rw [dist_comm]; have := hrl e' a; omega
  · have := hrl e b; omega
  · obtain ⟨c, c', -, hee⟩ := exists_eq_edge e'
    have h1 := hTS.connected.dist_triangle (u := Sum.inr e) (v := Sum.inl c) (w := Sum.inr e')
    have h2 : (subdiv T).dist (Sum.inl c) (Sum.inr e') = 1 :=
      dist_eq_one_iff_adj.2 (subdiv_adj_inl_inr.2 (by rw [hee]; exact Sym2.mem_mk_left _ _))
    have := hrl e c
    omega

/-! #### Sides of a tree edge -/

/-- In a tree, every vertex `d` is on one side of an edge `{c, c'}`. -/
lemma side_or (hT : T.IsTree) {c c' : C} (h : T.Adj c c') (d : C) :
    Btw T d c c' ∨ Btw T d c' c := by
  have h1 : T.dist c c' = 1 := dist_eq_one_iff_adj.2 h
  have h2 : T.dist c' c = 1 := dist_eq_one_iff_adj.2 h.symm
  unfold Btw
  rcases hT.dist_eq_dist_add_one_of_adj d h with hd | hd <;> omega

lemma not_side_and {c c' : C} (h : T.Adj c c') {d : C} (h1 : Btw T d c c') (h2 : Btw T d c' c) :
    False := by
  have := dist_eq_one_iff_adj.2 h
  have := dist_eq_one_iff_adj.2 h.symm
  unfold Btw at *
  omega

/-- **Crossing lemma**: if `f` is on `c`'s side and `e` on `c'`'s side of the edge `{c, c'}`,
then both `c` and `c'` lie on the path between `f` and `e`. -/
lemma btw_cross (hT : T.IsTree) {c c' f e : C} (h : T.Adj c c') (hf : Btw T f c c')
    (he : Btw T e c' c) : Btw T f c e ∧ Btw T f c' e := by
  classical
  have := dist_eq_one_iff_adj.2 h
  have := dist_eq_one_iff_adj.2 h.symm
  constructor
  · rcases btw_or hT hf e with h' | h'
    · exact h'
    · exfalso; unfold Btw at *; omega
  · rcases btw_or hT he f with h' | h'
    · exact h'.symm
    · exfalso; unfold Btw at *; omega

/-! #### Bags -/

/-- A vertex lying in a clique on each side of the clique-tree edge `{c, c'}` is the unique
vertex `u` of `bag c ∩ bag c'` (running intersection property + block property). -/
lemma eq_of_mem_cross (hB : IsBlockGraph G) (hCT : IsCliqueTree G T bag) {c c' : C}
    (h : T.Adj c c') {u : V} (hu : u ∈ bag c) (hu' : u ∈ bag c') {f e : C} (hf : Btw T f c c')
    (he : Btw T e c' c) {y : V} (hyf : y ∈ bag f) (hye : y ∈ bag e) : y = u := by
  obtain ⟨h1, h2⟩ := btw_cross hCT.isTree h hf he
  have hy : y ∈ bag c ∩ bag c' := Finset.mem_inter.2
    ⟨hCT.rip f e c h1 (Finset.mem_inter.2 ⟨hyf, hye⟩),
      hCT.rip f e c' h2 (Finset.mem_inter.2 ⟨hyf, hye⟩)⟩
  have hcard := hB _ _ (hCT.isMaxClique c) (hCT.isMaxClique c') (hCT.injective.ne h.ne)
  exact Finset.card_le_one.1 hcard _ hy _ (Finset.mem_inter.2 ⟨hu, hu'⟩)

/-- Every edge of `G` lies in some bag (it extends to a maximal clique). -/
lemma exists_bag_of_adj [Finite V] (hCT : IsCliqueTree G T bag) {a b : V} (h : G.Adj a b) :
    ∃ c, a ∈ bag c ∧ b ∈ bag c := by
  classical
  have := Fintype.ofFinite V
  let S := Finset.univ.filter (fun K : Finset V => G.IsClique (K : Set V) ∧ {a, b} ⊆ K)
  have hS : ({a, b} : Finset V) ∈ S := by
    rw [Finset.mem_filter, Finset.coe_pair, isClique_pair]
    exact ⟨Finset.mem_univ _, fun _ => h, subset_rfl⟩
  obtain ⟨K, hK, hmax⟩ := S.exists_max_image Finset.card ⟨_, hS⟩
  rw [Finset.mem_filter] at hK
  have hKmax : IsMaxClique G K := ⟨hK.2.1, fun K' hK' hsub =>
    (Finset.eq_of_subset_of_card_le hsub (hmax K' (Finset.mem_filter.2
      ⟨Finset.mem_univ _, hK', hK.2.2.trans hsub⟩))).symm⟩
  obtain ⟨c, hc⟩ := hCT.surjective K hKmax
  refine ⟨c, ?_, ?_⟩ <;> rw [hc] <;> apply hK.2.2 <;> simp

omit [DecidableEq V] in
/-- Maximal cliques are nonempty (when there is a vertex). -/
lemma IsMaxClique.nonempty [Nonempty V] {K : Finset V} (hK : IsMaxClique G K) : K.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  obtain ⟨v⟩ := ‹Nonempty V›
  have := hK.2 {v} (by rw [Finset.coe_singleton]; exact isClique_singleton v)
    (Finset.empty_subset _)
  simp at this

/-- **Lemma 12** (clique-tree edge separator). Let `{c, c'}` be an edge of the clique tree and
`u ∈ bag c ∩ bag c'`. If `d` is on `c`'s side (the path from `d` to `c'` passes `c`), `d'` on
`c'`'s side, `v ∈ bag d`, `w ∈ bag d'` and `v, w ≠ u`, then every walk from `v` to `w` passes
through `u`. (The hypothesis `w ≠ u` is not needed.) -/
theorem sep_mem_support [Finite V] (hB : IsBlockGraph G) (hCT : IsCliqueTree G T bag)
    {c c' : C} (hcc' : T.Adj c c') {u : V} (hu : u ∈ bag c) (hu' : u ∈ bag c')
    {d d' : C} (hd : Btw T d c c') (hd' : Btw T d' c' c) {v w : V} (hv : v ∈ bag d)
    (hw : w ∈ bag d') (hvu : v ≠ u) (_hwu : w ≠ u) (q : G.Walk v w) : u ∈ q.support := by
  have hT := hCT.isTree
  -- the invariant: all cliques containing the current vertex are on `c`'s side
  have side : ∀ {y : V} {f : C}, y ≠ u → Btw T f c c' → y ∈ bag f → ∀ e, y ∈ bag e →
      Btw T e c c' := by
    intro y f hyu hf hyf e hye
    rcases side_or hT hcc' e with h | h
    · exact h
    · exact absurd (eq_of_mem_cross hB hCT hcc' hu hu' hf h hyf hye) hyu
  have main : ∀ {y w' : V} (q : G.Walk y w'), w' ∈ bag d' → y ≠ u →
      (∀ e, y ∈ bag e → Btw T e c c') → u ∈ q.support := by
    intro y w' q
    induction q with
    | nil => intro hw' _ hy; exact (not_side_and hcc' (hy d' hw') hd').elim
    | @cons y z _ h q ih =>
      intro hw' hyu hy
      rw [Walk.support_cons, List.mem_cons]
      by_cases hzu : z = u
      · exact Or.inr (hzu ▸ q.start_mem_support)
      · obtain ⟨f, hyf, hzf⟩ := exists_bag_of_adj hCT h
        exact Or.inr (ih hw' hzu (side hzu (hy f hyf) hzf))
  exact main q hw hvu (side hvu hd hv)

/-- **Lemma 12**, metric form: `u` lies on a shortest path between `v` and `w`. -/
theorem sep_btw [Finite V] (hG : G.Connected) (hB : IsBlockGraph G) (hCT : IsCliqueTree G T bag)
    {c c' : C} (hcc' : T.Adj c c') {u : V} (hu : u ∈ bag c) (hu' : u ∈ bag c')
    {d d' : C} (hd : Btw T d c c') (hd' : Btw T d' c' c) {v w : V} (hv : v ∈ bag d)
    (hw : w ∈ bag d') : Btw G v u w := by
  classical
  unfold Btw
  apply le_antisymm _ hG.dist_triangle
  by_cases hvu : v = u
  · subst hvu; simp
  by_cases hwu : w = u
  · subst hwu; simp
  obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist v w
  have hmem := sep_mem_support hB hCT hcc' hu hu' hd hd' hv hw hvu hwu q
  have := congrArg Walk.length (q.take_spec hmem)
  rw [Walk.length_append] at this
  have h1 := dist_le (q.takeUntil u hmem)
  have h2 := dist_le (q.dropUntil u hmem)
  omega

/-- `blockOut` at a clique vertex `inl c`: a vertex of `bag c` closest to the input. -/
lemma blockOut_inl [Nonempty V] (hCT : IsCliqueTree G T bag) (v : V) (c : C) :
    blockOut G bag v (Sum.inl c : C ⊕ T.edgeSet) ∈ bag c ∧
      ∀ w ∈ bag c, G.dist v (blockOut G bag v (Sum.inl c : C ⊕ T.edgeSet)) ≤ G.dist v w := by
  have hne := (hCT.isMaxClique c).nonempty
  simp only [blockOut, hne, ↓reduceDIte]
  exact ((bag c).exists_min_image (G.dist v) hne).choose_spec

/-- `blockOut` at an intermediate vertex `inr e`: the vertex of `bag c ∩ bag c'`, `e = {c, c'}`. -/
lemma blockOut_inr (hCT : IsCliqueTree G T bag) (v : V) (e : T.edgeSet) :
    ∀ c ∈ (e : Sym2 C), blockOut G bag v (Sum.inr e) ∈ bag c := by
  obtain ⟨c, c', hcc', hee⟩ := exists_eq_edge e
  obtain ⟨u, hu⟩ := hCT.adj_nonempty c c' hcc'
  rw [Finset.mem_inter] at hu
  have h : ∃ u, ∀ c ∈ (e : Sym2 C), u ∈ bag c := ⟨u, fun d hd => by
    rw [hee, Sym2.mem_iff] at hd
    rcases hd with rfl | rfl
    · exact hu.1
    · exact hu.2⟩
  simp only [blockOut, h, ↓reduceDIte]
  exact h.choose_spec

/-- Two vertices of a clique are at distance at most one. -/
lemma dist_le_one_of_mem (hCT : IsCliqueTree G T bag) {c : C} {v w : V} (hv : v ∈ bag c)
    (hw : w ∈ bag c) : G.dist v w ≤ 1 := by
  by_cases hvw : v = w
  · simp [hvw]
  · rw [dist_eq_one_iff_adj.2 ((hCT.isMaxClique c).1 hv hw hvw)]

/-- **Lemmas 13 and 14** (spec level; Case 3 of Lemma 13 with the corrected argument, see the
module docstring). If the honest outputs `cout` of the tree protocol on `T_S`
(run with clique inputs `cin p ∋ x p`) are in the hull of the honest clique inputs and pairwise
at distance `≤ 1` in `T_S`, then the mapped outputs `blockOut` are in the hull of the honest
inputs in `G` and pairwise at distance `≤ 1` in `G`. -/
theorem blockOut_spec [Finite V] [Finite C] (hG : G.Connected) (hB : IsBlockGraph G)
    (hCT : IsCliqueTree G T bag) {P : Type*} {H : Set P} (x : P → V) (cin : P → C)
    (hcin : ∀ p ∈ H, x p ∈ bag (cin p)) (cout : P → C ⊕ T.edgeSet)
    (hval : ∀ p ∈ H, cout p ∈ hull (subdiv T) ((fun p => Sum.inl (cin p)) '' H))
    (hagr : ∀ p ∈ H, ∀ q ∈ H, (subdiv T).dist (cout p) (cout q) ≤ 1) :
    (∀ p ∈ H, blockOut G bag (x p) (cout p) ∈ hull G (x '' H)) ∧
    (∀ p ∈ H, ∀ q ∈ H,
      G.dist (blockOut G bag (x p) (cout p)) (blockOut G bag (x q) (cout q)) ≤ 1) := by
  have hT := hCT.isTree
  have hTS := subdiv_isTree hT
  constructor
  · -- **Lemma 13** (validity)
    intro p hp
    have : Nonempty V := ⟨x p⟩
    obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩ := hval p hp
    rcases btw_subdiv hT hab with ⟨c, hc, hacb⟩ | ⟨e, c, c', he, hee, hcc', hac, hbc⟩
    · rw [hc]
      obtain ⟨hgc, hmin⟩ := blockOut_inl hCT (x p) c
      set g := blockOut G bag (x p) (Sum.inl c)
      by_cases hxp : x p ∈ bag c
      · -- the own input is in the clique: it is the output
        have h0 := hmin _ hxp
        rw [dist_self] at h0
        have : x p = g := hG.dist_eq_zero_iff.1 (by omega)
        rw [← this]
        exact subset_hull _ ⟨p, hp, rfl⟩
      · -- Case 3 (corrected): the output is the separator `u` towards the own clique `cin p`
        classical
        have hpc : cin p ≠ c := fun h => hxp (h ▸ hcin p hp)
        obtain ⟨q, hq, hqc⟩ : ∃ q ∈ H, Btw T (cin q) c (cin p) := by
          rcases btw_or hT hacb (cin p) with h | h
          · exact ⟨a, ha, h⟩
          · exact ⟨b, hb, h.symm⟩
        -- the neighbour `c''` of `c` towards `cin p`
        have hnil : ¬ (tpath hT c (cin p)).Nil := Walk.not_nil_of_ne hpc.symm
        set c'' := (tpath hT c (cin p)).snd
        have hcc'' : T.Adj c c'' := Walk.adj_snd hnil
        have hc'' : Btw T c c'' (cin p) :=
          (mem_tpath_iff hT).1 ((tpath hT c (cin p)).getVert_mem_support 1)
        have hpside : Btw T (cin p) c'' c := by
          have := dist_eq_one_iff_adj.2 hcc''
          have := dist_eq_one_iff_adj.2 hcc''.symm
          have e1 : T.dist (cin p) c'' = T.dist c'' (cin p) := dist_comm
          have e2 : T.dist (cin p) c = T.dist c (cin p) := dist_comm
          unfold Btw at hc'' ⊢
          omega
        have hqside : Btw T (cin q) c c'' := hqc.left_of_trans' hT.connected hc''
        obtain ⟨u, hu⟩ := hCT.adj_nonempty c c'' hcc''
        rw [Finset.mem_inter] at hu
        -- every other vertex of `bag c` is farther from `x p` than `u`
        have hfar : ∀ w ∈ bag c, w ≠ u → G.dist (x p) w = G.dist (x p) u + 1 := by
          intro w hw hwu
          have h1 := sep_btw hG hB hCT hcc''.symm hu.2 hu.1 hpside (btw_left c c'') (hcin p hp) hw
          have h2 : G.dist u w = 1 :=
            dist_eq_one_iff_adj.2 ((hCT.isMaxClique c).1 hu.1 hw (Ne.symm hwu))
          unfold Btw at h1
          omega
        have hgu : g = u := by
          by_contra hne
          have := hfar g hgc hne
          have := hmin u hu.1
          omega
        rw [hgu]
        exact ⟨x p, ⟨p, hp, rfl⟩, x q, ⟨q, hq, rfl⟩,
          sep_btw hG hB hCT hcc''.symm hu.2 hu.1 hpside hqside (hcin p hp) (hcin q hq)⟩
    · -- intermediate vertex of an edge `{c, c'}` of the path: the separator `u`
      rw [he]
      have hmem := blockOut_inr hCT (x p) e
      have hu : blockOut G bag (x p) (Sum.inr e) ∈ bag c :=
        hmem c (by rw [hee]; exact Sym2.mem_mk_left _ _)
      have hu' : blockOut G bag (x p) (Sum.inr e) ∈ bag c' :=
        hmem c' (by rw [hee]; exact Sym2.mem_mk_right _ _)
      exact ⟨x a, ⟨a, ha, rfl⟩, x b, ⟨b, hb, rfl⟩,
        sep_btw hG hB hCT hcc' hu hu' hac hbc (hcin a ha) (hcin b hb)⟩
  · -- **Lemma 14** (agreement): both outputs lie in a common clique
    intro p hp q hq
    have : Nonempty V := ⟨x p⟩
    have hmemb : ∀ (v : V) (z : C ⊕ T.edgeSet) (c : C),
        (z = Sum.inl c ∨ ∃ e : T.edgeSet, z = Sum.inr e ∧ c ∈ (e : Sym2 C)) →
          blockOut G bag v z ∈ bag c := by
      rintro v z c (rfl | ⟨e, rfl, hc⟩)
      · exact (blockOut_inl hCT v c).1
      · exact blockOut_inr hCT v e c hc
    obtain ⟨c, hpc, hqc⟩ : ∃ c : C,
        (cout p = Sum.inl c ∨ ∃ e : T.edgeSet, cout p = Sum.inr e ∧ c ∈ (e : Sym2 C)) ∧
        (cout q = Sum.inl c ∨ ∃ e : T.edgeSet, cout q = Sum.inr e ∧ c ∈ (e : Sym2 C)) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hagr p hp q hq) with h0 | h1
      · rw [← hTS.connected.dist_eq_zero_iff.1 h0]
        rcases cout p with c | e
        · exact ⟨c, Or.inl rfl, Or.inl rfl⟩
        · obtain ⟨c, c', -, hee⟩ := exists_eq_edge e
          have hc : c ∈ (e : Sym2 C) := by rw [hee]; exact Sym2.mem_mk_left _ _
          exact ⟨c, Or.inr ⟨e, rfl, hc⟩, Or.inr ⟨e, rfl, hc⟩⟩
      · have hadj := dist_eq_one_iff_adj.1 h1
        rcases hz : cout p with c | e <;> rcases hz' : cout q with c' | e' <;>
          rw [hz, hz'] at hadj
        · simp at hadj
        · exact ⟨c, Or.inl rfl, Or.inr ⟨e', rfl, subdiv_adj_inl_inr.1 hadj⟩⟩
        · exact ⟨c', Or.inr ⟨e, rfl, subdiv_adj_inr_inl.1 hadj⟩, Or.inl rfl⟩
        · simp at hadj
    exact dist_le_one_of_mem hCT (hmemb _ _ c hpc) (hmemb _ _ c hqc)

/-- **Theorem 8.** If `treeAlg` achieves AA on the subdivided clique tree `T_S` within `R` rounds
(against an adversary structure `Z`), then `BlockGraphAA` achieves AA on the connected block
graph `G` within `R` rounds. -/
theorem blockGraphAA_solves [Finite V] [Finite C] {P M S : Type*} (hG : G.Connected)
    (hB : IsBlockGraph G) (hCT : IsCliqueTree G T bag) (cl : P → V → C)
    (hcl : ∀ p v, v ∈ bag (cl p v)) (A : Auth P M S)
    (treeAlg : Protocol P (C ⊕ T.edgeSet) M (C ⊕ T.edgeSet)) (Z : AdvStructure P) (R : ℕ)
    (hU : treeAlg.Unforging A)
    (htree : SolvesAuthWithin ⊤ treeAlg A Z noPre (GraphAA (subdiv T)) R) :
    (blockGraphAA G bag cl treeAlg).Unforging A ∧
      SolvesAuthWithin ⊤ (blockGraphAA G bag cl treeAlg) A Z noPre (GraphAA G) R := by
  refine ⟨Protocol.Unforging.wrap _ _ _ hU, ?_⟩
  intro s hZ hrel hV _
  set fi : P → V → C ⊕ T.edgeSet := fun p v => Sum.inl (cl p v)
  have hV' : (s.wrapIn fi).AuthValid ⊤ treeAlg A :=
    (Scenario.authValid_wrap _ _ _ _ _ _).1 hV
  obtain ⟨⟨hTerm, hVal, hAgr⟩, hTermBy⟩ := htree (s.wrapIn fi) hZ (hrel.wrapIn fi) hV' trivial
  have hex : ∀ p, ∃ o, p ∈ s.honest → Decides ⊤ treeAlg (s.wrapIn fi) p o := by
    intro p
    by_cases hp : p ∈ s.honest
    · obtain ⟨o, ho⟩ := hTerm p hp; exact ⟨o, fun _ => ho⟩
    · exact ⟨fi p (s.input p), fun h => absurd h hp⟩
  choose cout hcout using hex
  have hdec : ∀ p ∈ s.honest, ∀ o, Decides ⊤ (blockGraphAA G bag cl treeAlg) s p o ↔
      o = blockOut G bag (s.input p) (cout p) := by
    intro p hp o
    rw [blockGraphAA, decides_wrap_iff]
    constructor
    · rintro ⟨o', ho', rfl⟩
      rw [Decides.unique _ _ ho' (hcout p hp)]
    · rintro rfl
      exact ⟨cout p, hcout p hp, rfl⟩
  obtain ⟨hvalid, hagree⟩ := blockOut_spec hG hB hCT (H := s.honest) s.input
    (fun p => cl p (s.input p)) (fun p _ => hcl p (s.input p)) cout
    (fun p hp => hVal p hp _ (hcout p hp))
    (fun p hp q hq => hAgr p hp q hq _ _ (hcout p hp) (hcout q hq))
  refine ⟨⟨fun p hp => ⟨_, (hdec p hp _).2 rfl⟩, fun p hp o ho => ?_,
    fun p hp q hq o o' ho ho' => ?_⟩, terminatesBy_wrap _ _ _ _ _ _ hTermBy⟩
  · rw [(hdec p hp o).1 ho]; exact hvalid p hp
  · rw [(hdec p hp o).1 ho, (hdec q hq o').1 ho']; exact hagree p hp q hq

/-- **Theorem 8 with Theorem 5** (Corollaries 4/5 modulo the instantiation of the black boxes):
`BlockGraphAA` on top of `TreeAA(T_S)` (rooted at a clique vertex), with gradecast and RealAA as
black boxes, achieves AA on the block graph `G` within `R_GC + R_RealAA` rounds, where RealAA
only needs to handle `2·D(T)`-close inputs. -/
theorem blockGraphAA_of_gc_realAA {P : Type} [Fintype P] [DecidableEq P] {V C : Type}
    [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] {G : SimpleGraph V}
    {T : SimpleGraph C} [DecidableRel T.Adj] {bag : C → Finset V}
    (hG : G.Connected) (hB : IsBlockGraph G) (hCT : IsCliqueTree G T bag)
    (cl : P → V → C) (hcl : ∀ p v, v ∈ bag (cl p v)) (c₀ : C)
    {M₁ S₁ M₂ S₂ : Type} {t Rgc Rreal : ℕ} (ht : 2 * t < Fintype.card P)
    (A₁ : Auth P M₁ S₁)
    (gc : P → Protocol P (List (C ⊕ T.edgeSet)) M₁ (List (C ⊕ T.edgeSet) × Fin 3))
    (hgcU : ∀ s, (gc s).Unforging A₁)
    (hgc : ∀ s, SolvesAuthWithin ⊤ (gc s) A₁ (atMost t) noPre (Gradecast s) Rgc)
    (A₂ : Auth P M₂ S₂) (realAA : Protocol P ℝ M₂ ℝ) (hrU : realAA.Unforging A₂)
    (hreal : SolvesAuthWithin ⊤ realAA A₂ (atMost t) (Close (2 * T.diam : ℝ)) (RealAA 1) Rreal) :
    (blockGraphAA G bag cl (treeAA (subdiv_isTree hCT.isTree) (Sum.inl c₀) t Rgc gc realAA)).Unforging
        (treeAuth A₁ A₂) ∧
      SolvesAuthWithin ⊤
        (blockGraphAA G bag cl (treeAA (subdiv_isTree hCT.isTree) (Sum.inl c₀) t Rgc gc realAA))
        (treeAuth A₁ A₂) (atMost t) noPre (GraphAA G) (Rgc + Rreal) := by
  have hT := hCT.isTree
  have hD : ((subdiv T).diam : ℝ) ≤ 2 * T.diam := by exact_mod_cast diam_subdiv_le hT
  obtain ⟨hU, hsol⟩ := treeAA_solves (subdiv_isTree hT) (Sum.inl c₀) ht A₁ gc hgcU hgc A₂ realAA
    hrU fun s hZ hrel hV hpre =>
      hreal s hZ hrel hV fun p hp q hq => (hpre p hp q hq).trans hD
  exact blockGraphAA_solves hG hB hCT cl hcl _ _ _ _ hU hsol

end Proofs

end TreeAA
