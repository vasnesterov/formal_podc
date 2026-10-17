import Papers.PODC2020.SSLERegular.EulerLiteral

/-!
# Coherent configurations of SS-EulerCycle: the virtual-ring permutation

For a configuration whose colours are *injective on neighbourhoods* (`InjCol`) and in which
every edge carries a virtual edge in some direction (`EdgeOK`), on a `2k`-regular graph the
`2k` predecessor/successor slots of each node are in bijection with its `2k` neighbours.
Consequently the virtual edges form a **permutation** `σ` of the virtual nodes `V × Fin k`
(`vperm`): `σ (u, i) = (x, j)` iff `u.node[i].successorColor = x.color` and
`x.node[j].predecessorColor = u.color` (`edge_iff_vperm`), every edge of `G` carries exactly one
virtual edge, in exactly one direction (`edge_not_rev`).

Everything here only depends on the *skeleton* (colours and slot colours) of a configuration.
-/

open Finset

namespace SSLERegular

variable {RS : Type*} {k : ℕ} {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Skeletons: the colour and the (predecessor, successor) slot colours of each virtual node. -/
abbrev Skel (k : ℕ) := Fin (4 * k ^ 2) × (Fin k → Fin (4 * k ^ 2) × Fin (4 * k ^ 2))

variable (G)

/-- Colours are injective on every neighbourhood. -/
def InjCol (S : V → Skel k) : Prop :=
  ∀ x u v, G.Adj x u → G.Adj x v → (S u).1 = (S v).1 → u = v

/-- `(u, i) → (x, j)` is a virtual edge. -/
def VEdge (S : V → Skel k) (u : V) (i : Fin k) (x : V) (j : Fin k) : Prop :=
  G.Adj u x ∧ ((S u).2 i).2 = (S x).1 ∧ ((S x).2 j).1 = (S u).1

/-- Every edge carries a virtual edge in some direction. -/
def EdgeOK (S : V → Skel k) : Prop :=
  ∀ u x, G.Adj u x → (∃ i j, VEdge G S u i x j) ∨ ∃ i j, VEdge G S x i u j

variable {G}

/-- Slot values: `inl i` is the successor slot `i`, `inr j` the predecessor slot `j`. -/
def slotVal (s : Skel k) : Fin k ⊕ Fin k → Fin (4 * k ^ 2)
  | .inl i => (s.2 i).2
  | .inr j => (s.2 j).1

section Slots

variable [Fintype V] [DecidableRel G.Adj] {S : V → Skel k}
  (hdeg : ∀ v, G.degree v = 2 * k) (hinj : InjCol G S) (hok : EdgeOK G S)
include hdeg hinj hok

open Classical in
/-- The slot of `u` used by the neighbour `x`. -/
noncomputable def slotOf (u : V) (x : G.neighborSet u) : Fin k ⊕ Fin k :=
  if h : ∃ i j, VEdge G S u i x j then .inl h.choose
  else .inr (((hok u x x.2).resolve_left h).choose_spec.choose)

omit hdeg hinj in
lemma slotVal_slotOf (u : V) (x : G.neighborSet u) :
    slotVal (S u) (slotOf hok u x) = (S x).1 := by
  unfold slotOf
  split_ifs with h
  · exact h.choose_spec.choose_spec.2.1
  · exact ((hok u x x.2).resolve_left h).choose_spec.choose_spec.2.2

omit hdeg in
lemma slotOf_injective (u : V) : Function.Injective (slotOf hok u) := by
  intro x y hxy
  have := congrArg (slotVal (S u)) hxy
  rw [slotVal_slotOf, slotVal_slotOf] at this
  exact Subtype.ext (hinj u x y x.2 y.2 this)

lemma slotOf_bijective (u : V) : Function.Bijective (slotOf hok u) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨slotOf_injective hinj hok u, ?_⟩
  rw [SimpleGraph.card_neighborSet_eq_degree, hdeg, Fintype.card_sum, Fintype.card_fin]; ring

/-- A slot whose value is the colour of a neighbour `x` is the slot of `x`. -/
lemma slot_unique {u x : V} (hx : G.Adj u x) {s : Fin k ⊕ Fin k}
    (hs : slotVal (S u) s = (S x).1) : s = slotOf hok u ⟨x, hx⟩ := by
  obtain ⟨y, rfl⟩ := (slotOf_bijective hdeg hinj hok u).2 s
  rw [slotVal_slotOf] at hs
  have : (y : V) = x := hinj u y x y.2 hx hs
  congr 1; exact Subtype.ext this

lemma vedge_succ_unique {u x : V} {i i' j j' : Fin k} (h : VEdge G S u i x j)
    (h' : VEdge G S u i' x j') : i = i' := by
  have a := slot_unique hdeg hinj hok h.1 (s := .inl i) h.2.1
  have b := slot_unique hdeg hinj hok h.1 (s := .inl i') h'.2.1
  rw [← b] at a; exact Sum.inl_injective a

lemma vedge_pred_unique {u x : V} {i i' j j' : Fin k} (h : VEdge G S u i x j)
    (h' : VEdge G S u i' x j') : j = j' := by
  have a := slot_unique hdeg hinj hok h.1.symm (s := .inr j) h.2.2
  have b := slot_unique hdeg hinj hok h.1.symm (s := .inr j') h'.2.2
  rw [← b] at a; exact Sum.inr_injective a

/-- No virtual edge in the reverse direction. -/
lemma edge_not_rev {u x : V} {i j : Fin k} (h : VEdge G S u i x j) (i' j' : Fin k) :
    ¬ VEdge G S x i' u j' := by
  intro h'
  have a := slot_unique hdeg hinj hok h.1 (s := .inl i) h.2.1
  have b := slot_unique hdeg hinj hok h.1 (s := .inr j') h'.2.2
  rw [← b] at a; exact Sum.inl_ne_inr a

lemma vedge_total (u : V) (i : Fin k) : ∃ x j, VEdge G S u i x j := by
  obtain ⟨x, hx⟩ := (slotOf_bijective hdeg hinj hok u).2 (.inl i)
  unfold slotOf at hx
  split_ifs at hx with h
  · obtain ⟨j, hj⟩ := h.choose_spec
    rw [← Sum.inl_injective hx]; exact ⟨x, j, hj⟩

lemma vedge_func {u x x' : V} {i j j' : Fin k} (h : VEdge G S u i x j)
    (h' : VEdge G S u i x' j') : x = x' ∧ j = j' := by
  have hx : x = x' := hinj u x x' h.1 h'.1 (h.2.1.symm.trans h'.2.1)
  subst hx
  exact ⟨rfl, vedge_pred_unique hdeg hinj hok h h'⟩

lemma vedge_inj {u u' x : V} {i i' j : Fin k} (h : VEdge G S u i x j)
    (h' : VEdge G S u' i' x j) : u = u' ∧ i = i' := by
  have hu : u = u' := hinj x u u' h.1.symm h'.1.symm (h.2.2.symm.trans h'.2.2)
  subst hu
  exact ⟨rfl, vedge_succ_unique hdeg hinj hok h h'⟩

/-- The successor of a virtual node. -/
noncomputable def vnext (w : V × Fin k) : V × Fin k :=
  ((vedge_total hdeg hinj hok w.1 w.2).choose, (vedge_total hdeg hinj hok w.1 w.2).choose_spec.choose)

lemma vedge_vnext (w : V × Fin k) :
    VEdge G S w.1 w.2 (vnext hdeg hinj hok w).1 (vnext hdeg hinj hok w).2 :=
  (vedge_total hdeg hinj hok w.1 w.2).choose_spec.choose_spec

lemma vnext_injective : Function.Injective (vnext hdeg hinj hok) := by
  intro w w' h
  have a := vedge_vnext hdeg hinj hok w
  have b := vedge_vnext hdeg hinj hok w'
  rw [h] at a
  obtain ⟨h1, h2⟩ := vedge_inj hdeg hinj hok a b
  exact Prod.ext h1 h2

/-- **The virtual-ring permutation.** -/
noncomputable def vperm : Equiv.Perm (V × Fin k) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (vnext_injective hdeg hinj hok))

lemma vperm_apply (w : V × Fin k) : vperm hdeg hinj hok w = vnext hdeg hinj hok w := rfl

lemma vedge_vperm (w : V × Fin k) :
    VEdge G S w.1 w.2 (vperm hdeg hinj hok w).1 (vperm hdeg hinj hok w).2 :=
  vedge_vnext hdeg hinj hok w

lemma edge_iff_vperm {u x : V} {i j : Fin k} :
    VEdge G S u i x j ↔ vperm hdeg hinj hok (u, i) = (x, j) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := vedge_func hdeg hinj hok (vedge_vperm hdeg hinj hok (u, i)) h
    exact Prod.ext h1 h2
  · intro h
    have := vedge_vperm hdeg hinj hok (u, i)
    rw [h] at this; exact this

/-- The node of the successor is a neighbour. -/
lemma adj_vperm (w : V × Fin k) : G.Adj w.1 (vperm hdeg hinj hok w).1 :=
  (vedge_vperm hdeg hinj hok w).1

/-- Every edge is the image of exactly one virtual edge (in one of the two directions). -/
lemma exists_vperm_of_adj {u x : V} (h : G.Adj u x) :
    (∃ i, (vperm hdeg hinj hok (u, i)).1 = x) ∨ ∃ j, (vperm hdeg hinj hok (x, j)).1 = u := by
  rcases hok u x h with ⟨i, j, hij⟩ | ⟨i, j, hij⟩
  · left; exact ⟨i, by rw [(edge_iff_vperm hdeg hinj hok).1 hij]⟩
  · right; exact ⟨i, by rw [(edge_iff_vperm hdeg hinj hok).1 hij]⟩

end Slots

end SSLERegular
