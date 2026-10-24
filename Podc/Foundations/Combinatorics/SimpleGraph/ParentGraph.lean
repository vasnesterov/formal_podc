import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Cslib.Foundations.Combinatorics.SimpleGraph.Ball

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/ParentGraph.lean

/-!
# Graphs of parent maps

A *rooted map* is a function `P : V → V` with `P r = r` and a rank `rk : V → ℕ` that strictly
decreases along `P` away from the root `r` (`IsRootedMap P r rk`). Its graph
`parentGraph P` joins every vertex to its parent. Rooted maps are the parent-pointer
representation of rooted trees used by pointer-jumping algorithms: the graph is a spanning tree
(`IsRootedMap.isTree`) with one edge per non-root vertex (`IsRootedMap.ncard_edgeSet`), and
`IsRootedMap.jump` shows that letting any set of non-root vertices jump to their grandparent gives
again a rooted map with the same rank.

## Main definitions

* `parentGraph P`: `u ~ v` iff `u ≠ v` and `P u = v ∨ P v = u`.
* `IsRootedMap P r rk`.
* `jump P S`: vertices in `S` move to their grandparent, the others keep their parent.

## Main results

* `IsRootedMap.iterate_ne_self`: no cycles besides the root loop.
* `IsRootedMap.connected`, `IsRootedMap.ncard_edgeSet`, `IsRootedMap.isTree`.
* `IsRootedMap.exists_child_root`: with two vertices the root has a child.
* `IsRootedMap.parentGraph_jump`: the graph after a jump is the old graph plus the edges to the
  grandparents minus the edges to the old parents of the jumping vertices.
-/

namespace SimpleGraph

variable {V : Type*}

/-- The graph of a parent map: every vertex is joined to its parent. -/
def parentGraph (P : V → V) : SimpleGraph V := SimpleGraph.fromRel fun u v => P u = v

theorem parentGraph_adj {P : V → V} {u v : V} :
    (parentGraph P).Adj u v ↔ u ≠ v ∧ (P u = v ∨ P v = u) := fromRel_adj _ _ _

/-- `P` is a parent map with root `r` (`P r = r`) whose rank `rk` drops along every non-root
parent pointer. -/
structure IsRootedMap (P : V → V) (r : V) (rk : V → ℕ) : Prop where
  map_root : P r = r
  rk_lt : ∀ v, v ≠ r → rk (P v) < rk v

/-- Vertices in `S` jump to their grandparent, the others keep their parent. -/
def jump (P : V → V) (S : V → Prop) [DecidablePred S] : V → V :=
  fun u => if S u then P (P u) else P u

namespace IsRootedMap

variable {P : V → V} {r : V} {rk : V → ℕ}

theorem iterate_root (h : IsRootedMap P r rk) (k : ℕ) : P^[k] r = r :=
  Function.iterate_fixed h.map_root k

theorem iterate_eq_root_or_lt (h : IsRootedMap P r rk) {v : V} (hv : v ≠ r) {k : ℕ}
    (hk : 0 < k) : P^[k] v = r ∨ rk (P^[k] v) < rk v := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · show P v = r ∨ rk (P v) < rk v
      by_cases h1 : P v = r
      · exact Or.inl h1
      · exact Or.inr (h.rk_lt v hv)
    · rw [Function.iterate_succ_apply']
      rcases ih hk' with h1 | h1
      · left; rw [h1, h.map_root]
      · by_cases h2 : P^[k] v = r
        · left; rw [h2, h.map_root]
        · exact Or.inr ((h.rk_lt _ h2).trans h1)

theorem iterate_ne_self (h : IsRootedMap P r rk) {v : V} (hv : v ≠ r) {k : ℕ} (hk : 0 < k) :
    P^[k] v ≠ v := by
  intro he
  rcases h.iterate_eq_root_or_lt hv hk with h1 | h1
  · exact hv (he ▸ h1)
  · rw [he] at h1; exact lt_irrefl _ h1

theorem map_ne_self (h : IsRootedMap P r rk) {v : V} (hv : v ≠ r) : P v ≠ v :=
  h.iterate_ne_self hv (k := 1) one_pos

theorem map_map_ne_self (h : IsRootedMap P r rk) {v : V} (hv : v ≠ r) : P (P v) ≠ v :=
  h.iterate_ne_self hv (k := 2) two_pos

theorem map_map_map_ne_self (h : IsRootedMap P r rk) {v : V} (hv : v ≠ r) : P (P (P v)) ≠ v :=
  h.iterate_ne_self hv (k := 3) (by omega)

theorem map_eq_self_iff (h : IsRootedMap P r rk) {v : V} : P v = v ↔ v = r :=
  ⟨fun he => by_contra fun hv => h.map_ne_self hv he, fun he => he ▸ h.map_root⟩

theorem adj_root_iff (h : IsRootedMap P r rk) {v : V} :
    (parentGraph P).Adj v r ↔ v ≠ r ∧ P v = r := by
  rw [parentGraph_adj]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨h1, h2⟩
    · exact absurd (h2 ▸ h.map_root) h1
  · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inl h2⟩

theorem reachable (h : IsRootedMap P r rk) (v : V) : (parentGraph P).Reachable v r := by
  induction hn : rk v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hv : v = r
    · rw [hv]
    · have hadj : (parentGraph P).Adj v (P v) :=
        parentGraph_adj.2 ⟨(h.map_ne_self hv).symm, Or.inl rfl⟩
      exact hadj.reachable.trans (ih _ (hn ▸ h.rk_lt v hv) _ rfl)

theorem connected (h : IsRootedMap P r rk) : (parentGraph P).Connected :=
  have : Nonempty V := ⟨r⟩
  ⟨fun u v => (h.reachable u).trans (h.reachable v).symm⟩

/-- The edges of `parentGraph P` correspond to the non-root vertices. -/
theorem ncard_edgeSet (h : IsRootedMap P r rk) [Finite V] :
    (parentGraph P).edgeSet.ncard + 1 = Nat.card V := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hbij : Set.BijOn (fun v => s(v, P v)) {v | v ≠ r} (parentGraph P).edgeSet := by
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      exact parentGraph_adj.2 ⟨(h.map_ne_self hv).symm, Or.inl rfl⟩
    · intro v hv w hw hvw
      simp only [Sym2.eq_iff] at hvw
      rcases hvw with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact h1
      · exfalso
        have := h.map_map_ne_self (v := v) hv
        rw [h2, ← h1] at this
        exact this rfl
    · intro e he
      induction e using Sym2.ind with
      | _ u v =>
        rw [mem_edgeSet, parentGraph_adj] at he
        rcases he with ⟨hne, h1 | h1⟩
        · refine ⟨u, ?_, by simp [h1]⟩
          intro hu; rw [hu, h.map_root] at h1; exact hne (hu.trans h1)
        · refine ⟨v, ?_, by simp [h1, Sym2.eq_swap]⟩
          intro hv; rw [hv, h.map_root] at h1; exact hne (h1.symm.trans hv.symm)
  rw [← hbij.image_eq, hbij.injOn.ncard_image]
  have : {v | v ≠ r} = (Set.univ : Set V) \ {r} := by ext; simp
  rw [this, Set.ncard_sdiff (by simp) (Set.toFinite _), Set.ncard_univ, Set.ncard_singleton,
    Nat.card_eq_fintype_card]
  have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨r⟩
  omega

theorem isTree (h : IsRootedMap P r rk) [Finite V] : (parentGraph P).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨h.connected, ?_⟩
  rw [← h.ncard_edgeSet, Nat.card_coe_set_eq]

/-- If there is a vertex besides the root, the root has a child. -/
theorem exists_child_root (h : IsRootedMap P r rk) {v : V} (hv : v ≠ r) :
    ∃ c, c ≠ r ∧ P c = r := by
  induction hn : rk v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases h1 : P v = r
    · exact ⟨v, hv, h1⟩
    · exact ih _ (hn ▸ h.rk_lt v hv) h1 rfl

/-- With an exact depth function (`rk r = 0`, `rk (P v) + 1 = rk v`), the distance from the root
in `parentGraph P` is the depth. -/
theorem edist_root_eq (h : IsRootedMap P r rk) (h0 : rk r = 0)
    (hs : ∀ v, v ≠ r → rk (P v) + 1 = rk v) (v : V) : (parentGraph P).edist r v = rk v := by
  apply le_antisymm
  · induction hn : rk v using Nat.strong_induction_on generalizing v with
    | _ n ih =>
      by_cases hv : v = r
      · subst hv; simp [← hn, h0]
      · have hadj : (parentGraph P).Adj (P v) v :=
          parentGraph_adj.2 ⟨h.map_ne_self hv, Or.inr rfl⟩
        have h1 := ih (rk (P v)) (by have := hs v hv; omega) (P v) rfl
        calc (parentGraph P).edist r v ≤ (parentGraph P).edist r (P v) +
              (parentGraph P).edist (P v) v := (parentGraph P).edist_triangle
          _ ≤ rk (P v) + 1 := by
              gcongr; exact (edist_eq_one_iff_adj.2 hadj).le
          _ = n := by rw [← hn, ← hs v hv]; push_cast; rfl
  · have := le_add_edist_of_lipschitz (G := parentGraph P) (f := rk) ?_ r v
    · rw [h0] at this; simpa using this
    · intro x y hxy
      rw [parentGraph_adj] at hxy
      rcases hxy with ⟨hne, h1 | h1⟩
      · have hx : x ≠ r := by rintro rfl; rw [h.map_root] at h1; exact hne h1
        have := hs x hx; rw [h1] at this; omega
      · have hy : y ≠ r := by rintro rfl; rw [h.map_root] at h1; exact hne h1.symm
        have := hs y hy; rw [h1] at this; omega

/-- The neighbours of `v` are its parent and its children. -/
theorem neighborSet_subset (v : V) :
    (parentGraph P).neighborSet v ⊆ insert (P v) {j | j ≠ v ∧ P j = v} := by
  intro w hw
  rw [mem_neighborSet, parentGraph_adj] at hw
  rcases hw with ⟨hne, h1 | h1⟩
  · exact Or.inl h1.symm
  · exact Or.inr ⟨hne.symm, h1⟩

/-! ### Jumping to the grandparent -/

variable {S : V → Prop} [DecidablePred S]

/-- Jumping preserves rootedness (with the same rank) when only non-root children jump. -/
theorem jump (h : IsRootedMap P r rk) (hS : ∀ u, S u → P u ≠ r) :
    IsRootedMap (SimpleGraph.jump P S) r rk where
  map_root := by
    have : ¬ S r := fun hr => hS r hr h.map_root
    simp [SimpleGraph.jump, this, h.map_root]
  rk_lt v hv := by
    unfold SimpleGraph.jump
    split_ifs with h1
    · exact (h.rk_lt _ (hS v h1)).trans (h.rk_lt v hv)
    · exact h.rk_lt v hv

theorem ne_root_of_map_ne_root (h : IsRootedMap P r rk) {u : V} (hu : P u ≠ r) : u ≠ r := by
  rintro rfl; exact hu h.map_root

end IsRootedMap

end SimpleGraph
