import Cslib.Foundations.Combinatorics.Digraph.Walk
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max

-- CSLib candidate: Cslib/Foundations/Combinatorics/Digraph/Walk.lean (append to the existing
-- file)

/-!
# Ancestors, roots and vertices of source components of digraphs

Additions to `Cslib/Foundations/Combinatorics/Digraph/Walk.lean`.

* `Digraph.ancestors G v`: the (finite) set of ancestors of `v` (vertices with a walk to `v`).
* `Digraph.IsRoot G r`: `r` reaches every vertex. A digraph with a root has a unique source
  component, the set of its roots (`isSourceComponent_setOf_isRoot`,
  `IsSourceComponent.eq_setOf_isRoot`). `Cslib.DynNet.IsRoot E r` is `(Digraph.mk E).IsRoot r`
  (`Cslib.DynNet.isRoot_iff`, in `DynamicNetworks/Journey.lean`).
* `Digraph.InSourceComponent G v`: `v` is reachable from each of its ancestors, i.e. `v` lies in a
  source component, namely the set of its ancestors (`InSourceComponent.isSourceComponent`,
  `IsSourceComponent.inSourceComponent`); every vertex of a finite digraph has such an ancestor
  (`exists_inSourceComponent`).
* `Digraph.IsRootAvoiding G X r`: `r ∉ X` reaches every vertex outside `X` in `G - X`.
  **Pairwise common ancestors give a root** (`exists_isRootAvoiding`, `exists_isRoot`): in a finite
  digraph, if any two vertices outside `X` have a common ancestor in `G - X`, then some vertex is
  a root of `G - X`.
* `reachable_iff_of_closed`: two digraphs with the same arcs into a predecessor-closed set `S`
  have the same walks into `S`.
-/

open Relation

namespace Digraph

variable {V : Type*} {G H : Digraph V} {X S : Set V} {u v w r : V}

/-! ### Ancestors -/

section Ancestors

variable [Fintype V]

open Classical in
/-- The ancestors of `v`: the vertices with a walk to `v` (including `v`). -/
noncomputable def ancestors (G : Digraph V) (v : V) : Finset V :=
  Finset.univ.filter fun u => G.Reachable u v

/-- The ancestors of `v` are the vertices with a walk to `v`. -/
@[simp] theorem mem_ancestors : u ∈ G.ancestors v ↔ G.Reachable u v := by
  classical
  simp [ancestors]

/-- The ancestors of `v`, as a set. -/
theorem coe_ancestors (G : Digraph V) (v : V) :
    (G.ancestors v : Set V) = {u | G.Reachable u v} :=
  Set.ext fun _ => mem_ancestors

/-- Every vertex is its own ancestor. -/
theorem self_mem_ancestors (G : Digraph V) (v : V) : v ∈ G.ancestors v :=
  mem_ancestors.2 .rfl

/-- The ancestors of an ancestor are ancestors. -/
theorem ancestors_subset_of_reachable (h : G.Reachable u v) : G.ancestors u ⊆ G.ancestors v :=
  fun _ hw => mem_ancestors.2 ((mem_ancestors.1 hw).trans h)

/-- A source component is the set of ancestors of any of its vertices. -/
theorem IsSourceComponent.eq_coe_ancestors (hS : G.IsSourceComponent S) (hv : v ∈ S) :
    S = G.ancestors v :=
  (hS.eq_setOf_reachable hv).trans (coe_ancestors G v).symm

end Ancestors

/-! ### Roots -/

/-- `r` is a *root* of `G`: every vertex is reachable from `r`. -/
def IsRoot (G : Digraph V) (r : V) : Prop := ∀ v, G.Reachable r v

/-- Ancestors of a root are roots. -/
theorem IsRoot.of_reachable (hr : G.IsRoot r) (h : G.Reachable u r) : G.IsRoot u :=
  fun v => h.trans (hr v)

/-- In-neighbours of a root are roots. -/
theorem IsRoot.of_adj (hr : G.IsRoot r) (h : G.Adj u r) : G.IsRoot u :=
  hr.of_reachable h.reachable

/-- A root of a subgraph is a root. -/
theorem IsRoot.mono (hGH : G ≤ H) (hr : G.IsRoot r) : H.IsRoot r :=
  fun v => (hr v).mono hGH

/-- If `G` has a root, the set of its roots is a source component. -/
theorem isSourceComponent_setOf_isRoot (hr : G.IsRoot r) :
    G.IsSourceComponent {u | G.IsRoot u} := by
  have hS : {u | G.IsRoot u} = {u | G.Reachable u r} :=
    Set.ext fun u => ⟨fun hu => hu r, fun hu => hr.of_reachable hu⟩
  rw [hS]
  exact isSourceComponent_iff.2 ⟨r, rfl, fun x _ => hr x⟩

/-- If `G` has a root, its unique source component is the set of its roots. -/
theorem IsSourceComponent.eq_setOf_isRoot (hS : G.IsSourceComponent S) (hr : G.IsRoot r) :
    S = {u | G.IsRoot u} := by
  obtain ⟨v, hv⟩ := hS.nonempty
  have hrS : r ∈ S := mem_of_reachable_of_closed hS.closed (hr v) hv
  exact hS.eq_of_mem (isSourceComponent_setOf_isRoot hr) hrS hr

/-! ### Vertices of source components -/

/-- `v` lies in a source component: `v` is reachable from each of its ancestors. The source
component is then the set of ancestors of `v` (`InSourceComponent.isSourceComponent`). -/
def InSourceComponent (G : Digraph V) (v : V) : Prop := ∀ u, G.Reachable u v → G.Reachable v u

/-- Ancestors of a vertex of a source component lie in the same source component. -/
theorem InSourceComponent.of_reachable (hv : G.InSourceComponent v) (h : G.Reachable u v) :
    G.InSourceComponent u :=
  fun w hw => h.trans (hv w (hw.trans h))

/-- The ancestors of a vertex of a source component form a source component. -/
theorem InSourceComponent.isSourceComponent (hv : G.InSourceComponent v) :
    G.IsSourceComponent {u | G.Reachable u v} :=
  isSourceComponent_iff.2 ⟨v, rfl, hv⟩

/-- The ancestors of a vertex of a source component form a source component. -/
theorem InSourceComponent.isSourceComponent_ancestors [Fintype V] (hv : G.InSourceComponent v) :
    G.IsSourceComponent (G.ancestors v) := by
  rw [coe_ancestors]
  exact hv.isSourceComponent

/-- Every vertex of a source component lies in a source component. -/
theorem IsSourceComponent.inSourceComponent (hS : G.IsSourceComponent S) (hv : v ∈ S) :
    G.InSourceComponent v :=
  fun _ hu => hS.reachable hv (mem_of_reachable_of_closed hS.closed hu hv)

/-- A root lies in a source component. -/
theorem IsRoot.inSourceComponent (hr : G.IsRoot r) : G.InSourceComponent r :=
  fun u _ => hr u

/-- In a finite digraph, every vertex has an ancestor in a source component. -/
theorem exists_inSourceComponent [Finite V] (v : V) :
    ∃ r, G.Reachable r v ∧ G.InSourceComponent r := by
  obtain ⟨S, hS, hSv⟩ := G.exists_isSourceComponent_subset v
  obtain ⟨r, hr⟩ := hS.nonempty
  exact ⟨r, hSv hr, hS.inSourceComponent hr⟩

/-! ### Roots avoiding a set of vertices -/

/-- `r` is a root of `G - X`: `r ∉ X`, and `r` reaches every vertex outside `X` by a walk
avoiding `X`. -/
def IsRootAvoiding (G : Digraph V) (X : Set V) (r : V) : Prop :=
  r ∉ X ∧ ∀ v, v ∉ X → G.ReachableAvoiding X r v

/-- Roots avoiding `∅` are roots. -/
@[simp] theorem isRootAvoiding_empty : G.IsRootAvoiding ∅ r ↔ G.IsRoot r := by
  simp [IsRootAvoiding, IsRoot]

/-- Ancestors of a root of `G - X` in `G - X` are roots of `G - X`. -/
theorem IsRootAvoiding.of_reachableAvoiding (hr : G.IsRootAvoiding X r)
    (h : G.ReachableAvoiding X u r) : G.IsRootAvoiding X u :=
  ⟨h.notMem_left, fun v hv => h.trans (hr.2 v hv)⟩

/-- In-neighbours of a root of `G - X` outside `X` are roots of `G - X`. -/
theorem IsRootAvoiding.of_adj (hr : G.IsRootAvoiding X r) (e : G.Adj u r) (hu : u ∉ X) :
    G.IsRootAvoiding X u :=
  hr.of_reachableAvoiding ((ReachableAvoiding.refl hr.1).head e hu)

/-- **Pairwise common ancestors give a root.** In a finite digraph, if some vertex lies outside
`X` and any two vertices outside `X` have a common ancestor in `G - X`, then `G - X` has a
root. -/
theorem exists_isRootAvoiding [Finite V] (hne : ∃ v, v ∉ X)
    (h : ∀ u v, u ∉ X → v ∉ X → ∃ w, G.ReachableAvoiding X w u ∧ G.ReachableAvoiding X w v) :
    ∃ r, G.IsRootAvoiding X r := by
  classical
  have := Fintype.ofFinite V
  -- a vertex outside `X` with the fewest ancestors in `G - X`
  let A : V → Finset V := fun w => Finset.univ.filter fun a => G.ReachableAvoiding X a w
  obtain ⟨s, hsX, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun x => x ∉ X)
    (fun w => (A w).card) (by obtain ⟨v, hv⟩ := hne; exact ⟨v, by simp [hv]⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hsX hmin
  refine ⟨s, hsX, fun v hv => ?_⟩
  obtain ⟨z, hzs, hzv⟩ := h s v hsX hv
  have hsub : A z ⊆ A s := fun a ha => by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.trans hzs
  have heq := Finset.eq_of_subset_of_card_le hsub (hmin z hzs.notMem_left)
  have hsz : s ∈ A z := by
    rw [heq]; simpa [A] using ReachableAvoiding.refl hsX
  simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hsz
  exact hsz.trans hzv

/-- **Pairwise common ancestors give a root.** A finite nonempty digraph in which any two vertices
have a common ancestor has a root. -/
theorem exists_isRoot [Finite V] [Nonempty V]
    (h : ∀ u v, ∃ w, G.Reachable w u ∧ G.Reachable w v) : ∃ r, G.IsRoot r := by
  obtain ⟨r, hr⟩ := exists_isRootAvoiding (G := G) (X := ∅) ⟨Classical.arbitrary V, id⟩
    fun u v _ _ => by simpa using h u v
  exact ⟨r, isRootAvoiding_empty.1 hr⟩

/-! ### Predecessor-closed sets -/

/-- Two digraphs with the same arcs into a predecessor-closed set `S` (of `G`) have the same walks
into `S`. -/
theorem reachable_iff_of_closed (hE : ∀ r ∈ S, ∀ u, H.Adj u r ↔ G.Adj u r)
    (hS : ∀ r ∈ S, ∀ u, G.Adj u r → u ∈ S) (hr : r ∈ S) :
    H.Reachable u r ↔ G.Reachable u r := by
  have hS' : ∀ r ∈ S, ∀ u, H.Adj u r → u ∈ S := fun r hr u h => hS r hr u ((hE r hr u).1 h)
  constructor
  · intro h
    induction h using ReflTransGen.head_induction_on with
    | refl => exact .rfl
    | head huw hw ih =>
      exact Reachable.head ((hE _ (mem_of_reachable_of_closed hS' hw hr) _).1 huw) ih
  · intro h
    induction h using ReflTransGen.head_induction_on with
    | refl => exact .rfl
    | head huw hw ih =>
      exact Reachable.head ((hE _ (mem_of_reachable_of_closed hS hw hr) _).2 huw) ih

end Digraph
