import Mathlib

/-!
# PN-views (Section 2.1 of the paper)

Formalization support for *"It does not matter how you define locally checkable labelings"*
(Cruciani, Das, Raevskaya, Suomela; PODC 2026, arXiv 2602.18188).

The radius-`r` PN-view `T^r_G(v)` of a node `v` is the tree of non-backtracking walks of length
`≤ r` starting at `v`, labelled by the label of the last node of the walk; the paper considers it
up to isomorphism of labelled rooted trees.

## Modelling choice

We represent a PN-view directly by its **canonical isomorphism type**: a labelled rooted tree of
depth `≤ k` with unordered children is
* a label, if `k = 0`;
* a root label together with the *multiset* of the (depth `≤ k - 1`) subtrees of its children,
  if `k > 0`.

This is the type `View L k`. Two labelled rooted trees (of depth `≤ k`) are isomorphic iff their
canonical forms are equal, so the paper's `≅` between PN-views becomes `=` here. Shallow leaves
are represented by empty child multisets.

## Main definitions

* `View L k`, `View.label`, `View.trunc` (drop the deepest level), `View.prune a c`
  (the paper's `(T, v \ w)`: remove one child branch `c` of the root and truncate).
* `branch σ k p u`: the PN-view of depth `k` of the non-backtracking walks that enter `u` from `p`
  (the paper's `T^r_G(p → u)` for `k = r - 1`).
* `pnView σ r v`: the radius-`r` PN-view `T^r_G(v)`.
* `PNValid C σ`: validity of a solution of the PN-checkable problem given by `C`.

## Main results

* `trunc_branch`, `trunc_pnView`: truncation commutes with taking views.
* `branch_eq_prune_pnView`: the Remark of Section 6, `T(v → u) ≅ T(u \ v)`.
* `branch_unique`: views of branches are the unique solution of their defining recursion
  (the core of the induction in the proof of Lemma 6.2).
-/

namespace Podc.LCLDefinitions

-- CSLib candidate (PN-views / outcome transfer are reusable beyond this paper)

universe u w

/-- Canonical forms of labelled rooted trees of depth `≤ k` with unordered children:
a depth-`0` tree is its root label, a depth-`(k+1)` tree is a root label together with the
multiset of its children's depth-`k` subtrees. Isomorphism of labelled rooted trees is equality
of these canonical forms. -/
def View (L : Type u) : ℕ → Type u
  | 0 => L
  | k + 1 => L × Multiset (View L k)

namespace View

variable {L : Type u}

/-- The tree with root label `l` and children subtrees `s`. -/
def node {k : ℕ} (l : L) (s : Multiset (View L k)) : View L (k + 1) := (l, s)

/-- The multiset of the children subtrees of the root. -/
def children {k : ℕ} (a : View L (k + 1)) : Multiset (View L k) := a.2

/-- The label of the root. -/
def label : {k : ℕ} → View L k → L
  | 0, a => a
  | _ + 1, a => a.1

/-- The tree consisting of a single (root) node with label `l`. -/
def leaf (l : L) : (k : ℕ) → View L k
  | 0 => l
  | _ + 1 => (l, 0)

/-- Truncation: forget the deepest level of a depth-`(k+1)` tree. -/
def trunc : {k : ℕ} → View L (k + 1) → View L k
  | 0, a => a.1
  | _ + 1, a => (a.1, a.2.map trunc)

@[simp] theorem label_zero (a : View L 0) : label a = a := rfl

@[simp] theorem label_node {k : ℕ} (l : L) (s : Multiset (View L k)) : label (node l s) = l := rfl

@[simp] theorem children_node {k : ℕ} (l : L) (s : Multiset (View L k)) :
    children (node l s) = s := rfl

theorem eta {k : ℕ} (a : View L (k + 1)) : node (label a) (children a) = a := rfl

theorem ext_iff' {k : ℕ} {a b : View L (k + 1)} :
    a = b ↔ label a = label b ∧ children a = children b :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => Prod.ext h.1 h.2⟩

theorem node_inj {k : ℕ} {l l' : L} {s s' : Multiset (View L k)} :
    node l s = node l' s' ↔ l = l' ∧ s = s' := Prod.ext_iff

@[simp] theorem trunc_node_zero (l : L) (s : Multiset (View L 0)) : trunc (node l s) = l := rfl

@[simp] theorem trunc_node_succ {k : ℕ} (l : L) (s : Multiset (View L (k + 1))) :
    trunc (node l s) = node l (s.map trunc) := rfl

@[simp] theorem label_trunc {k : ℕ} (a : View L (k + 1)) : label (trunc a) = label a := by
  cases k <;> rfl

open Classical in
/-- `prune a c` is the paper's `(T, v \ w)`: remove (one copy of) the child branch `c` from the
root of `a` and truncate the result to depth `k`. -/
noncomputable def prune {k : ℕ} (a : View L (k + 1)) (c : View L k) : View L k :=
  trunc (node (label a) ((children a).erase c))

end View

open View

section Graph

variable {V : Type w} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite] {L : Type u}

/-- `branch G σ k p u` is the depth-`k` view of the tree of non-backtracking walks that enter `u`
coming from `p`: its root is labelled `σ u`, and its children are the branches entering the
neighbours of `u` other than `p`. For adjacent `p, u` this is the subtree `T^{k+1}_G(p → u)` of
the PN-view of `p`. -/
def branch (σ : V → L) : (k : ℕ) → V → V → View L k
  | 0, _, u => σ u
  | k + 1, p, u => node (σ u) (((G.neighborFinset u).erase p).val.map (branch σ k u))

/-- The radius-`r` PN-view `T^r_G(v)` of `v` (Section 2.1), as a canonical labelled rooted tree:
the root is labelled `σ v` and its children are the branches entering all neighbours of `v`. -/
def pnView (σ : V → L) : (r : ℕ) → V → View L r
  | 0, v => σ v
  | k + 1, v => node (σ v) ((G.neighborFinset v).val.map (branch G σ k v))

/-- A solution `σ` of the PN-checkable problem with radius `r` given by the set `C` of accepted
PN-views is valid iff the PN-view of every node is accepted (Section 2.2). -/
def PNValid {r : ℕ} (C : Set (View L r)) (σ : V → L) : Prop :=
  ∀ v, pnView G σ r v ∈ C

variable {G}

@[simp] theorem branch_zero (σ : V → L) (p u : V) : branch G σ 0 p u = σ u := rfl

theorem branch_succ (σ : V → L) (k : ℕ) (p u : V) :
    branch G σ (k + 1) p u = node (σ u) (((G.neighborFinset u).erase p).val.map (branch G σ k u)) :=
  rfl

@[simp] theorem label_branch (σ : V → L) (k : ℕ) (p u : V) :
    label (branch G σ k p u) = σ u := by
  cases k <;> rfl

theorem pnView_succ (σ : V → L) (k : ℕ) (v : V) :
    pnView G σ (k + 1) v = node (σ v) ((G.neighborFinset v).val.map (branch G σ k v)) := rfl

@[simp] theorem label_pnView (σ : V → L) (r : ℕ) (v : V) : label (pnView G σ r v) = σ v := by
  cases r <;> rfl

/-- Truncating a branch view of depth `k + 1` gives the branch view of depth `k`. -/
theorem trunc_branch (σ : V → L) (k : ℕ) (p u : V) :
    trunc (branch G σ (k + 1) p u) = branch G σ k p u := by
  induction k generalizing p u with
  | zero => rfl
  | succ k ih =>
    rw [branch_succ, trunc_node_succ, Multiset.map_map, branch_succ]
    congr 1
    exact Multiset.map_congr rfl fun w _ => ih u w

/-- Truncating the radius-`(r+1)` PN-view gives the radius-`r` PN-view. -/
theorem trunc_pnView (σ : V → L) (r : ℕ) (v : V) :
    trunc (pnView G σ (r + 1) v) = pnView G σ r v := by
  cases r with
  | zero => rfl
  | succ r =>
    rw [pnView_succ, trunc_node_succ, Multiset.map_map, pnView_succ]
    congr 1
    exact Multiset.map_congr rfl fun w _ => trunc_branch σ r v w

/-- Erasing the value at a member from a mapped finset multiset. -/
theorem map_erase_of_mem {β : Type*} [DecidableEq β] (s : Finset V) (f : V → β) {v : V}
    (hv : v ∈ s) : (s.val.map f).erase (f v) = (s.erase v).val.map f := by
  conv_lhs => rw [← Finset.insert_erase hv, Finset.insert_val_of_notMem (Finset.notMem_erase v s)]
  rw [Multiset.map_cons, Multiset.erase_cons_head]

/-- **Remark of Section 6** (`T^r_G(v → u) ≅ T^r_G(u \ v)`): for adjacent `u, v`, the branch of
the PN-view of `v` towards `u` equals the PN-view of `u` with the branch towards `v` pruned. -/
theorem branch_eq_prune_pnView (σ : V → L) (k : ℕ) {u v : V} (h : G.Adj v u) :
    branch G σ k v u = prune (pnView G σ (k + 1) u) (branch G σ k u v) := by
  classical
  unfold prune
  rw [pnView_succ, label_node, children_node, map_erase_of_mem _ _ ((G.mem_neighborFinset u v).2 h.symm)]
  rw [← branch_succ, trunc_branch]

/-- Uniqueness of branch views: any family `c v u` of depth-`k` views satisfying the defining
recursion of `branch` on all directed edges (`c v u` is the truncation of the tree with root label
`l u` and children `c u w` for the neighbours `w ≠ v` of `u`) equals `branch G l k`. This is the
induction in the proof of Lemma 6.2, organised over the depth `k`. -/
theorem branch_unique (l : V → L) {k : ℕ} (c : V → V → View L k)
    (hc : ∀ v u, G.Adj v u →
      c v u = trunc (node (l u) (((G.neighborFinset u).erase v).val.map (c u))))
    {v u : V} (h : G.Adj v u) : c v u = branch G l k v u := by
  induction k generalizing v u with
  | zero => exact hc v u h
  | succ k ih =>
    have key : ∀ v u, G.Adj v u → trunc (c v u) = branch G l k v u := by
      refine fun v u h => ih (fun v u => trunc (c v u)) (fun v u h => ?_) h
      conv_lhs => rw [hc v u h]
      rw [trunc_node_succ, Multiset.map_map]
      rfl
    rw [hc v u h, trunc_node_succ, branch_succ, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun w hw => ?_
    simp only [Finset.mem_val, Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hw
    exact key u w hw.2

end Graph

end Podc.LCLDefinitions
