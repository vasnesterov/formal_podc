import Papers.PODC2026.LCLDefinitions.PNView

/-!
# From PN-checkable problems to the RE formalism (Section 6)

Formalization of Section 6 of *"It does not matter how you define locally checkable labelings"*
(Cruciani, Das, Raevskaya, Suomela; PODC 2026, arXiv 2602.18188): a PN-checkable problem `D`
of radius `r + 1` on 3-regular graphs is encoded as a problem `E` in the RE formalism
(Definition 6.1), and solutions are lifted in both directions (Lemmas 6.2–6.4).

## Model

* Graphs: simple graphs `G : SimpleGraph V` (locally finite); problem `E` is only considered on
  3-regular graphs (`∀ v, G.degree v = 3`). The instances of `D` and `E` are the same graph
  (the paper's `G_E ≅ G_D`).
* RE formalism (Section 2.2): a half-edge labelling is `λ : V → V → Λ`, where `λ v u` is the label
  of the half-edge at `v` on the edge `{v, u}` (values at non-edges are irrelevant). It is valid if
  the multiset of the half-edge labels around every node is in `C_V`, and the multiset of the two
  half-edge labels of every edge is in `C_E`.
* PN-views are canonical labelled rooted trees (`View`, see `PNView.lean`), so `≅` is `=`.

## Modelling choices (differences from the paper)

* The checking radius is written `r + 1` (`r_D ≥ 1`; the construction needs the depth-`r`
  subtrees `(T, v → w)`).
* `Σ_E = View Σ (r+1) × Fin 3` instead of `C_D × [3]`; the node constraint only admits
  `a ∈ C_D`, so labels outside `C_D × [3]` never occur in a valid solution.
* The node constraint additionally requires that the root of `a` has exactly 3 children
  (an implicit assumption of the paper: on 3-regular graphs, PN-views in `C_D` whose root does not
  have 3 children are never used, and the `I_fit` definition via `ζ : [3] → N(v)` presupposes it).
* The enumeration `ζ` of the children of the root is fixed as `Multiset.toList` (`child`);
  `γ` is the induced index map `N(v) → Fin 3` chosen in Lemma 6.4 (`enumIdx`).
* `I_fit` (`Fit`) is formulated via the canonical trees: `(T_{v→u}) ≅ (T'_{v' \ u'})` becomes
  `child a x = prune b (child b y)`.
-/

namespace Podc.LCLDefinitions

open View

universe u w

/-! ### The RE formalism -/

/-- A problem in the RE formalism (Section 2.2): node constraint `CV` (multisets of the three
half-edge labels around a node) and edge constraint `CE` (multisets of the two half-edge labels of
an edge). -/
structure REProblem (Λ : Type*) where
  /-- Node constraint. -/
  CV : Set (Multiset Λ)
  /-- Edge constraint. -/
  CE : Set (Multiset Λ)

section RE

variable {V : Type w} (G : SimpleGraph V) [G.LocallyFinite] {Λ : Type*}

/-- A half-edge labelling `lam` (`lam v u` = label of the half-edge at `v` on the edge `{v, u}`)
is valid for the RE problem `P` (Section 2.2). -/
def REProblem.Valid (P : REProblem Λ) (lam : V → V → Λ) : Prop :=
  (∀ v, (G.neighborFinset v).val.map (lam v) ∈ P.CV) ∧
    ∀ v u, G.Adj v u → ({lam v u, lam u v} : Multiset Λ) ∈ P.CE

end RE

/-! ### Enumeration of children -/

section Enum

variable {Sig : Type u} {r : ℕ}

/-- The `x`-th child subtree of the root of `a` (the paper's `ζ`), using the fixed enumeration
`Multiset.toList` of the children; a dummy leaf if there are fewer than `x + 1` children. -/
noncomputable def child (a : View Sig (r + 1)) (x : Fin 3) : View Sig r :=
  (children a).toList.getD x (leaf (label a) r)

/-- If the root of `a` has exactly 3 children, they are `child a 0`, `child a 1`, `child a 2`. -/
theorem children_eq_child {a : View Sig (r + 1)} (h : Multiset.card (children a) = 3) :
    children a = {child a 0, child a 1, child a 2} := by
  have hl : (children a).toList.length = 3 := by rw [Multiset.length_toList, h]
  conv_lhs => rw [← Multiset.coe_toList (children a)]
  generalize hL : (children a).toList = l at hl ⊢
  match l, hl with
  | [x, y, z], _ => simp [child, hL]; rfl

/-- **Enumeration lemma** (existence of the paper's `γ`, list version): if `↑l = S.map f`, the
elements of `S` can be injectively indexed by positions of `l` holding their `f`-values. -/
theorem exists_index_of_coe_eq {V β : Type*} [DecidableEq V] (f : V → β) (d : β) :
    ∀ (l : List β) (S : Finset V), (l : Multiset β) = S.val.map f →
      ∃ e : V → ℕ, (∀ u ∈ S, e u < l.length ∧ l.getD (e u) d = f u) ∧ Set.InjOn e S
  | [], S, h => by
    have : S = ∅ := by
      rw [Multiset.coe_nil, eq_comm, Multiset.map_eq_zero, Finset.val_eq_zero] at h
      exact h
    subst this
    exact ⟨fun _ => 0, by simp, by simp⟩
  | b :: l, S, h => by
    classical
    have hb : b ∈ S.val.map f := h ▸ by simp
    obtain ⟨u₀, hu₀, rfl⟩ := Multiset.mem_map.1 hb
    have h' : (l : Multiset β) = (S.erase u₀).val.map f := by
      rw [← map_erase_of_mem S f hu₀, ← h]
      simp
    obtain ⟨e, he, hinj⟩ := exists_index_of_coe_eq f d l (S.erase u₀) h'
    refine ⟨fun u => if u = u₀ then 0 else e u + 1, fun u hu => ?_, ?_⟩
    · by_cases hu' : u = u₀
      · subst hu'; simp
      · have := he u (Finset.mem_erase.2 ⟨hu', hu⟩)
        refine ⟨by simp [hu', this.1], ?_⟩
        simp only [hu', ite_false, List.getD_cons_succ]
        exact this.2
    · intro u hu u' hu' huu
      simp only at huu
      by_cases h1 : u = u₀ <;> by_cases h2 : u' = u₀
      · rw [h1, h2]
      · simp [h1, h2] at huu
      · simp [h1, h2] at huu
      · simp only [h1, h2, ite_false, add_left_inj] at huu
        exact hinj (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨h1, hu⟩))
          (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨h2, hu'⟩)) huu

/-- **Enumeration lemma** (the paper's `γ`): for a 3-element set `S` and `f : V → β`, there is a
bijective indexing `e : S → Fin 3` such that the `e u`-th element of the fixed enumeration of the
multiset `S.map f` is `f u`. -/
theorem exists_enum {V β : Type*} [DecidableEq V] (S : Finset V) (hS : S.card = 3)
    (f : V → β) (d : β) :
    ∃ e : V → Fin 3, (∀ u ∈ S, (S.val.map f).toList.getD (e u) d = f u) ∧
      S.val.map e = (Finset.univ : Finset (Fin 3)).val := by
  classical
  obtain ⟨e, he, hinj⟩ :=
    exists_index_of_coe_eq f d (S.val.map f).toList S (Multiset.coe_toList _)
  have hlen : (S.val.map f).toList.length = 3 := by simp [hS]
  let e' : V → Fin 3 := fun u => if h : e u < 3 then ⟨e u, h⟩ else 0
  have he' : ∀ u ∈ S, (e' u : ℕ) = e u := fun u hu => by
    have := (he u hu).1; rw [hlen] at this; simp [e', this]
  refine ⟨e', fun u hu => by rw [he' u hu]; exact (he u hu).2, ?_⟩
  have hinj' : Set.InjOn e' S := fun u hu u' hu' h =>
    hinj hu hu' (by rw [← he' u hu, ← he' u' hu', h])
  rw [← Finset.image_val_of_injOn hinj']
  congr 1
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn hinj', hS, Fintype.card_fin]

end Enum

/-! ### Definition 6.1: the problem `E` -/

section ProblemE

variable {Sig : Type u} {r : ℕ}

/-- The multiset `[(a, 0), (a, 1), (a, 2)]` of half-edge labels around a node with view `a`. -/
def nodeLabels (a : View Sig (r + 1)) : Multiset (View Sig (r + 1) × Fin 3) :=
  {(a, 0), (a, 1), (a, 2)}

theorem nodeLabels_eq_map (a : View Sig (r + 1)) :
    nodeLabels a = (Finset.univ : Finset (Fin 3)).val.map (fun x => (a, x)) := rfl

theorem fst_of_mem_nodeLabels {a : View Sig (r + 1)} {p : View Sig (r + 1) × Fin 3}
    (h : p ∈ nodeLabels a) : p.1 = a := by
  simp only [nodeLabels, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] at h
  rcases h with rfl | rfl | rfl <;> rfl

theorem nodeLabels_injective : Function.Injective (nodeLabels (Sig := Sig) (r := r)) := by
  intro a b h
  have : (a, (0 : Fin 3)) ∈ nodeLabels b := h ▸ by simp [nodeLabels]
  exact fst_of_mem_nodeLabels this

/-- The compatibility indicator `I_fit` of Section 6: the branch of `a` towards its `x`-th
neighbour is the view `b` with its `y`-th branch pruned, and vice versa
(`(T_{v→u}) ≅ (T'_{v'\u'})` and `(T_{v\u}) ≅ (T'_{v'→u'})`). -/
def Fit (p q : View Sig (r + 1) × Fin 3) : Prop :=
  child p.1 p.2 = prune q.1 (child q.1 q.2) ∧ prune p.1 (child p.1 p.2) = child q.1 q.2

theorem Fit.symm {p q : View Sig (r + 1) × Fin 3} (h : Fit p q) : Fit q p :=
  ⟨h.2.symm, h.1.symm⟩

/-- **Definition 6.1** (problem `E`). Given the set `C` of accepted radius-`(r+1)` PN-views of the
PN-checkable problem `D`, the RE problem `E` has labels `View Σ (r+1) × Fin 3`,
`C_V = {[(a,0),(a,1),(a,2)] | a ∈ C_D}` (with the root of `a` having exactly 3 children, see the
module docstring) and `C_E = {[p, q] | I_fit(p, q)}`. -/
def problemE (C : Set (View Sig (r + 1))) : REProblem (View Sig (r + 1) × Fin 3) where
  CV := {m | ∃ a ∈ C, Multiset.card (children a) = 3 ∧ m = nodeLabels a}
  CE := {m | ∃ p q, Fit p q ∧ m = {p, q}}

theorem fit_of_mem_CE {C : Set (View Sig (r + 1))} {p q : View Sig (r + 1) × Fin 3}
    (h : ({p, q} : Multiset _) ∈ (problemE C).CE) : Fit p q := by
  obtain ⟨p', q', hfit, he⟩ := h
  simp only [Multiset.insert_eq_cons, Multiset.cons_eq_cons, Multiset.singleton_inj] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨_, cs, h1, h2⟩
  · exact hfit
  · obtain ⟨rfl, -⟩ := (Multiset.singleton_eq_cons_iff _).1 h1
    obtain ⟨rfl, -⟩ := (Multiset.singleton_eq_cons_iff _).1 h2
    exact hfit.symm

end ProblemE

/-! ### Lemmas 6.2–6.4 -/

section Lift

variable {V : Type w} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]
  {Sig : Type u} {r : ℕ} {C : Set (View Sig (r + 1))}

open Classical in
/-- The view `t(v)` associated with `v` by the node constraint of `E` (Definition 6.1): the `a`
with `[(a,0),(a,1),(a,2)]` equal to the half-edge labels around `v` (a junk value if no such `a`
exists). -/
noncomputable def rootView (G : SimpleGraph V) [G.LocallyFinite]
    (lam : V → V → View Sig (r + 1) × Fin 3) (v : V) : View Sig (r + 1) :=
  if h : ∃ a, (G.neighborFinset v).val.map (lam v) = nodeLabels a then h.choose else (lam v v).1

/-- The lift `E → D` (Definition 6.1): `l(v)` is the root label of `t(v)`. -/
noncomputable def liftED (G : SimpleGraph V) [G.LocallyFinite]
    (lam : V → V → View Sig (r + 1) × Fin 3) : V → Sig :=
  fun v => label (rootView G lam v)

omit [DecidableEq V] in
theorem rootView_spec {lam : V → V → View Sig (r + 1) × Fin 3} (h : (problemE C).Valid G lam)
    (v : V) : (G.neighborFinset v).val.map (lam v) = nodeLabels (rootView G lam v) := by
  have hex : ∃ a, (G.neighborFinset v).val.map (lam v) = nodeLabels a := by
    obtain ⟨a, -, -, ha⟩ := h.1 v
    exact ⟨a, ha⟩
  unfold rootView
  split
  · next h' => exact h'.choose_spec
  · exact absurd hex ‹_›

/-- **Lemma 6.2.** If `λ` satisfies `C_V` at every node and `C_E` at every edge, and `t(v)` is the
view associated with `v` by the node constraint, then the PN-view of `v` under `l(v) = label(t(v))`
is `t(v)`: `(T^{r+1}_G(v), l) ≅ t(v)`. -/
theorem pnView_eq_of_valid {lam : V → V → View Sig (r + 1) × Fin 3}
    (h : (problemE C).Valid G lam) {t : V → View Sig (r + 1)}
    (ht : ∀ v, (G.neighborFinset v).val.map (lam v) = nodeLabels (t v)) (v : V) :
    pnView G (fun v => label (t v)) (r + 1) v = t v := by
  set l : V → Sig := fun v => label (t v)
  -- `t v ∈ C` with exactly three children at the root
  have htC : ∀ v, t v ∈ C ∧ Multiset.card (children (t v)) = 3 := fun v => by
    obtain ⟨a, haC, hcard, ha⟩ := h.1 v
    rw [ht v] at ha
    rw [nodeLabels_injective ha]
    exact ⟨haC, hcard⟩
  -- the half-edge labels at `v` all carry `t v`
  have hfst : ∀ v u, G.Adj v u → (lam v u).1 = t v := fun v u hvu => by
    apply fst_of_mem_nodeLabels
    rw [← ht v]
    exact Multiset.mem_map_of_mem _ ((G.mem_neighborFinset v u).2 hvu)
  -- `c v u` is the subtree of `t v` towards `u` designated by the half-edge label
  let c : V → V → View Sig r := fun v u => child (lam v u).1 (lam v u).2
  have hchildren : ∀ v, children (t v) = (G.neighborFinset v).val.map (c v) := fun v => by
    have : (G.neighborFinset v).val.map (c v) =
        ((G.neighborFinset v).val.map (lam v)).map (fun p => child p.1 p.2) := by
      rw [Multiset.map_map]; rfl
    rw [this, ht v, children_eq_child (htC v).2]
    simp [nodeLabels]
  -- the edge constraint gives the recursion of `branch`
  have hrec : ∀ v u, G.Adj v u →
      c v u = trunc (node (l u) (((G.neighborFinset u).erase v).val.map (c u))) := by
    intro v u hvu
    classical
    have hfit := fit_of_mem_CE (h.2 v u hvu)
    have h1 := hfit.1
    change c v u = prune (lam u v).1 (c u v) at h1
    rw [hfst u v hvu.symm] at h1
    rw [h1, prune, hchildren u,
      map_erase_of_mem _ _ ((G.mem_neighborFinset u v).2 hvu.symm)]
  have hbranch : ∀ v u, G.Adj v u → c v u = branch G l r v u :=
    fun v u hvu => branch_unique l c hrec hvu
  rw [pnView_succ, ← eta (t v), hchildren v]
  congr 1
  exact Multiset.map_congr rfl fun u hu =>
    (hbranch v u ((G.mem_neighborFinset v u).1 hu)).symm

/-- **Lemma 6.3** (lift `E → D`). If the half-edge labelling `λ` is valid for `E`, then the node
labelling `l = liftED G λ` (root labels of the views `t(v)`) is a valid solution of `D`. -/
theorem liftED_valid {lam : V → V → View Sig (r + 1) × Fin 3}
    (h : (problemE C).Valid G lam) : PNValid G C (liftED G lam) := by
  intro v
  have := pnView_eq_of_valid h (rootView_spec h) v
  change pnView G (fun v => label (rootView G lam v)) (r + 1) v ∈ C
  rw [this]
  obtain ⟨a, haC, -, ha⟩ := h.1 v
  rw [rootView_spec h v] at ha
  rw [nodeLabels_injective ha]
  exact haC

open Classical in
/-- The index map `γ(T^{r+1}_G(v), ·) : N(v) → [3]` used in Lemma 6.4: an indexing of the
neighbours of `v` such that `child (T^{r+1}_G(v)) (γ u)` is the branch towards `u` and `γ` is a
bijection `N(v) → Fin 3` (junk if `deg v ≠ 3`). -/
noncomputable def enumIdx (G : SimpleGraph V) [G.LocallyFinite] (σ : V → Sig) (r : ℕ)
    (v : V) : V → Fin 3 :=
  if h : ∃ e : V → Fin 3, (∀ u ∈ G.neighborFinset v,
      child (pnView G σ (r + 1) v) (e u) = branch G σ r v u) ∧
      (G.neighborFinset v).val.map e = (Finset.univ : Finset (Fin 3)).val
  then h.choose else fun _ => 0

/-- The lift `D → E` (Lemma 6.4): `σ_E(v, {v,u}) = (T^{r+1}_G(v), γ(T^{r+1}_G(v), u))`. -/
noncomputable def liftDE (G : SimpleGraph V) [G.LocallyFinite] (σ : V → Sig) (r : ℕ) :
    V → V → View Sig (r + 1) × Fin 3 :=
  fun v u => (pnView G σ (r + 1) v, enumIdx G σ r v u)

theorem enumIdx_spec (hG : ∀ v, G.degree v = 3) (σ : V → Sig) (v : V) :
    (∀ u ∈ G.neighborFinset v, child (pnView G σ (r + 1) v) (enumIdx G σ r v u) =
      branch G σ r v u) ∧
    (G.neighborFinset v).val.map (enumIdx G σ r v) = (Finset.univ : Finset (Fin 3)).val := by
  have hex : ∃ e : V → Fin 3, (∀ u ∈ G.neighborFinset v,
      child (pnView G σ (r + 1) v) (e u) = branch G σ r v u) ∧
      (G.neighborFinset v).val.map e = (Finset.univ : Finset (Fin 3)).val := by
    obtain ⟨e, he, hbij⟩ := exists_enum (G.neighborFinset v)
      (by rw [G.card_neighborFinset_eq_degree, hG v]) (branch G σ r v)
      (leaf (σ v) r)
    exact ⟨e, fun u hu => he u hu, hbij⟩
  unfold enumIdx
  split
  · next h' => exact h'.choose_spec
  · exact absurd hex ‹_›

/-- **Lemma 6.4** (lift `D → E`). On a 3-regular graph, if `σ` is a valid solution of `D`, then
the half-edge labelling `σ_E(v, {v,u}) = (T^{r+1}_G(v), γ(T^{r+1}_G(v), u))` is valid for `E`. -/
theorem liftDE_valid (hG : ∀ v, G.degree v = 3) {σ : V → Sig} (hσ : PNValid G C σ) :
    (problemE C).Valid G (liftDE G σ r) := by
  have hcard : ∀ v, Multiset.card (children (pnView G σ (r + 1) v)) = 3 := fun v => by
    rw [pnView_succ, children_node, Multiset.card_map, Finset.card_val,
      G.card_neighborFinset_eq_degree, hG v]
  have hchild : ∀ v u, G.Adj v u →
      child (liftDE G σ r v u).1 (liftDE G σ r v u).2 = branch G σ r v u := fun v u hvu =>
    (enumIdx_spec hG σ v).1 u ((G.mem_neighborFinset v u).2 hvu)
  refine ⟨fun v => ⟨pnView G σ (r + 1) v, hσ v, hcard v, ?_⟩, fun v u hvu => ?_⟩
  · change (G.neighborFinset v).val.map (fun u => (pnView G σ (r + 1) v, enumIdx G σ r v u)) = _
    rw [nodeLabels_eq_map, ← (enumIdx_spec hG σ v).2, Multiset.map_map]
    rfl
  · refine ⟨liftDE G σ r v u, liftDE G σ r u v, ⟨?_, ?_⟩, rfl⟩
    · rw [hchild v u hvu, hchild u v hvu.symm]
      exact branch_eq_prune_pnView σ r hvu
    · rw [hchild v u hvu, hchild u v hvu.symm]
      exact (branch_eq_prune_pnView σ r hvu.symm).symm

end Lift

end Podc.LCLDefinitions
