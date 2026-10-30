import Mathlib
import Cslib.Computability.Distributed.Local.Locality

/-!
# The pointer problem `P*` and its `Ω(log n)` lower bound

Section 3.2 and Section 8.2 (Lemma 18) of *Hardness of Minimal Symmetry Breaking in Distributed
Computing* (A. Balliu, J. Hirvonen, D. Olivetti, J. Suomela, PODC 2019).

## Model

Deterministic or randomized LOCAL model with unique identifiers: the nodes of every graph are the
elements of a fixed type `V` (the identifiers), an algorithm is a function
`f : SimpleGraph V → (V → α) → V → ℕ × Option V` (input labels `x : V → α`, e.g. random bits),
and `Cslib.Local.IsLocal R f` says that it runs in `R` rounds. The output of a node is the pair
`(d v, p v)`: the number `d v` and the pointer `p v` (the identifier of a neighbour, equivalent to a
port number).

## Main definitions

* `deg G v`: the (instance-free) degree `(G.neighborSet v).ncard`.
* `PHappy Δ G d p v`: node `v` is `P*`-happy (conditions (1)–(5) of Section 3.2, plus `d v < Δ`).
* `Solves Δ G out`: every node is `P*`-happy.
* `TNode Δ m`, `tree Δ m`: the balanced tree of radius `m` (root degree `Δ`, inner degree `Δ`,
  leaves at depth `m`); `tree' Δ r`: the tree `T'` of the proof of Lemma 18 (radius `r + 1`; below
  every node at depth `r` one leaf is moved under a sibling leaf).

## Main results

* `chain_eq`: in a tree-like region, a non-backtracking pointer chain from the root goes down and
  carries the degree of the first non-`Δ`-degree level.
* `tree_root_d`, `tree'_root_d`: every `P*`-labelling has `d(root) = 1` on `T` and `d(root) = Δ - 1`
  on `T'`.
* `gAgree_tree_tree'`: `T` and `T'` look the same from the root for `r` rounds.
* `lemma18`, `lemma18_class`, `lemma18_randomized`: **Lemma 18** (no `r`-round algorithm solves
  `P*` on both `T` and `T'`; with `n = |T| ≤ Δ^(2r+2)` this is `Ω(log_Δ n)`).
-/

namespace Podc.MinimalSymmetryBreaking

open SimpleGraph Cslib.Local

section Problem

variable {V : Type*}

/-- The degree of `v` in `G` (instance-free version of `SimpleGraph.degree`). -/
noncomputable def deg (G : SimpleGraph V) (v : V) : ℕ := (G.neighborSet v).ncard

/-- Node `v` is **`P*`-happy** (Section 3.2 of [BHOS19]) for the labelling `d : V → ℕ` and the
pointers `p : V → Option V` (`none` = `⊥`):
`0 ≤ d(v) < Δ` and
(1) if `deg v = Δ`, then `p v` points to a neighbour of `v`;
(2) if `deg v < Δ`, then `p v = ⊥` and `d v = deg v`;
(3) if `p v = u`, then `d v = d u`;
(4) if `p v = u`, then `p u ≠ v`;
(5) if `p v = u`, then `p u ≠ ⊥` or `deg u = d v`. -/
structure PHappy (Δ : ℕ) (G : SimpleGraph V) (d : V → ℕ) (p : V → Option V) (v : V) : Prop where
  d_lt : d v < Δ
  full : deg G v = Δ → ∃ u, p v = some u ∧ G.Adj v u
  low : deg G v < Δ → p v = none ∧ d v = deg G v
  consistent : ∀ u, p v = some u → d u = d v
  noBacktrack : ∀ u, p v = some u → p u ≠ some v
  terminate : ∀ u, p v = some u → p u ≠ none ∨ deg G u = d v

/-- The output `out v = (d v, p v)` is a feasible solution of `P*` on `G`: all nodes are happy. -/
def Solves (Δ : ℕ) (G : SimpleGraph V) (out : V → ℕ × Option V) : Prop :=
  ∀ v, PHappy Δ G (fun v => (out v).1) (fun v => (out v).2) v

/-- **Chain lemma.** Let `dep` be a depth function and `IsPar w u` ("`u` is the parent of `w`")
a parent relation with unique parents, such that up to depth `L` the graph is a tree going down:
nodes of depth `< L` have degree `Δ` and their neighbours are their parent or a child one level
deeper, and nodes of depth `L` have degree `c < Δ`. Then in every `P*`-labelling every node of
depth `≤ L` that is a root (no parent) or is pointed at by its parent has `d = c`: the pointer
chain cannot backtrack, so it goes down to depth `L`. -/
theorem chain_eq {G : SimpleGraph V} {Δ L c : ℕ} (dep : V → ℕ) (IsPar : V → V → Prop)
    (huniq : ∀ u w w', IsPar u w → IsPar u w' → w = w')
    (hint : ∀ u, dep u < L → deg G u = Δ) (hbd : ∀ u, dep u = L → deg G u = c) (hc : c < Δ)
    (hadj : ∀ u w, dep u < L → G.Adj u w → IsPar u w ∨ (IsPar w u ∧ dep w = dep u + 1))
    {d : V → ℕ} {p : V → Option V} (hP : ∀ v, PHappy Δ G d p v) :
    ∀ u, dep u ≤ L → ((∀ w, ¬ IsPar u w) ∨ ∃ w, IsPar u w ∧ p w = some u) → d u = c := by
  intro u hu hpar
  induction h : L - dep u generalizing u with
  | zero =>
    have hd := hbd u (by omega)
    exact ((hP u).low (by omega)).2.trans hd
  | succ k ih =>
    have hlt : dep u < L := by omega
    obtain ⟨w, hpw, hadjw⟩ := (hP u).full (hint u hlt)
    rcases hadj u w hlt hadjw with h1 | ⟨h1, h2⟩
    · exfalso
      rcases hpar with h0 | ⟨w', hw', hpw'⟩
      · exact h0 w h1
      · rw [huniq u w w' h1 hw'] at hpw
        exact (hP u).noBacktrack w' hpw hpw'
    · have := ih w (by omega) (Or.inr ⟨u, h1, hpw⟩) (by omega)
      rw [← (hP u).consistent w hpw, this]

end Problem

/-! ### The balanced trees `T` and `T'` -/

section Trees

variable {Δ m : ℕ}

-- CSLib candidate: balanced `Δ`-regular trees (`TNode`, `tree`, degree computations) and
-- `chain_eq` are reusable for other indistinguishability lower bounds on trees.
/-- Nodes of the balanced tree of radius `m` with root degree `Δ` and inner degree `Δ`: a depth
`k ≤ m` and a path `f` of child indices (`f i` is the index of the `(i+1)`-st step; the first step
has `Δ` choices, later ones `Δ - 1`), padded with `0` from position `k` on. -/
abbrev TNode (Δ m : ℕ) : Type :=
  {q : Fin (m + 1) × (Fin m → Fin Δ) //
    (∀ i : Fin m, q.1.val ≤ i.val → (q.2 i).val = 0) ∧
    (∀ i : Fin m, 0 < i.val → i.val < q.1.val → (q.2 i).val < Δ - 1)}

namespace TNode

/-- The depth of a node. -/
def dep (u : TNode Δ m) : ℕ := u.1.1.val

/-- The (padded) path of child indices of a node. -/
def pth (u : TNode Δ m) : Fin m → Fin Δ := u.1.2

lemma dep_le (u : TNode Δ m) : u.dep ≤ m := Nat.lt_succ_iff.1 u.1.1.isLt

lemma pth_of_le (u : TNode Δ m) {i : Fin m} (h : u.dep ≤ i.val) : (u.pth i).val = 0 := u.2.1 i h

lemma pth_lt (u : TNode Δ m) {i : Fin m} (h0 : 0 < i.val) (h : i.val < u.dep) :
    (u.pth i).val < Δ - 1 := u.2.2 i h0 h

@[ext] lemma ext {u w : TNode Δ m} (h1 : u.dep = w.dep) (h2 : ∀ i, u.pth i = w.pth i) : u = w := by
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext h1
  · funext i; exact h2 i

/-- The root. -/
def root [NeZero Δ] : TNode Δ m :=
  ⟨(0, fun _ => ⟨0, Nat.pos_of_neZero Δ⟩), fun _ _ => rfl, fun _ _ h => by simp at h⟩

@[simp] lemma dep_root [NeZero Δ] : (root : TNode Δ m).dep = 0 := by simp [root, dep]

/-- `u` is the parent of `w`. -/
def IsPar (w u : TNode Δ m) : Prop :=
  w.dep = u.dep + 1 ∧ ∀ i : Fin m, i.val ≠ u.dep → w.pth i = u.pth i

lemma IsPar.dep_eq {w u : TNode Δ m} (h : IsPar w u) : w.dep = u.dep + 1 := h.1

lemma isPar_unique {u w w' : TNode Δ m} (h : IsPar u w) (h' : IsPar u w') : w = w' := by
  have hd : w.dep = w'.dep := by have := h.1; have := h'.1; omega
  refine ext hd fun i => ?_
  by_cases hi : i.val = w.dep
  · exact Fin.ext (by rw [w.pth_of_le hi.ge, w'.pth_of_le (hd ▸ hi.ge)])
  · rw [← h.2 i hi, h'.2 i (hd ▸ hi)]

/-- Build a node from a depth and a padded path. -/
def mk (k : ℕ) (hk : k ≤ m) (f : Fin m → Fin Δ) (h1 : ∀ i : Fin m, k ≤ i.val → (f i).val = 0)
    (h2 : ∀ i : Fin m, 0 < i.val → i.val < k → (f i).val < Δ - 1) : TNode Δ m :=
  ⟨(⟨k, by omega⟩, f), h1, h2⟩

@[simp] lemma mk_dep (k : ℕ) (hk : k ≤ m) (f : Fin m → Fin Δ) (h1 h2) :
    (mk k hk f h1 h2).dep = k := rfl

@[simp] lemma mk_pth (k : ℕ) (hk : k ≤ m) (f : Fin m → Fin Δ) (h1 h2) :
    (mk k hk f h1 h2).pth = f := rfl

/-- The child of `u` with index `a` at position `dep u`. -/
def child (u : TNode Δ m) (hu : u.dep < m) (a : Fin Δ) (ha : u.dep = 0 ∨ a.val < Δ - 1) :
    TNode Δ m := by
  refine mk (u.dep + 1) hu (Function.update u.pth ⟨u.dep, hu⟩ a) (fun i hi => ?_)
    (fun i h0 hi => ?_)
  · have hne : i ≠ ⟨u.dep, hu⟩ := by intro h; subst h; simp at hi
    have hi' : u.dep ≤ i.val := by omega
    rw [Function.update_of_ne hne]; exact u.pth_of_le hi'
  · by_cases h : i = ⟨u.dep, hu⟩
    · subst h; simp only [Function.update_self]
      rcases ha with ha | ha
      · simp [ha] at h0
      · exact ha
    · rw [Function.update_of_ne h]
      have : i.val ≠ u.dep := fun h' => h (Fin.ext h')
      exact u.pth_lt h0 (by omega)

@[simp] lemma child_dep (u : TNode Δ m) (hu : u.dep < m) (a : Fin Δ) (ha) :
    (u.child hu a ha).dep = u.dep + 1 := rfl

lemma child_pth_apply (u : TNode Δ m) (hu : u.dep < m) (a : Fin Δ) (ha) (i : Fin m) :
    (u.child hu a ha).pth i = Function.update u.pth ⟨u.dep, hu⟩ a i := rfl

lemma isPar_child (u : TNode Δ m) (hu : u.dep < m) (a : Fin Δ) (ha) : IsPar (u.child hu a ha) u :=
  ⟨rfl, fun i hi => by
    rw [child_pth_apply, Function.update_of_ne (fun h => hi (by rw [h]))]⟩

lemma child_pth (u : TNode Δ m) (hu : u.dep < m) (a : Fin Δ) (ha) :
    (u.child hu a ha).pth ⟨u.dep, hu⟩ = a := by rw [child_pth_apply, Function.update_self]

/-- The children of `u` whose index satisfies `Q` are counted by the admissible indices. -/
lemma ncard_children (u : TNode Δ m) (hu : u.dep < m) (Q : Fin Δ → Prop) :
    {w | IsPar w u ∧ Q (w.pth ⟨u.dep, hu⟩)}.ncard =
      {a : Fin Δ | (u.dep = 0 ∨ a.val < Δ - 1) ∧ Q a}.ncard := by
  have hinj : Set.InjOn (fun w : TNode Δ m => w.pth ⟨u.dep, hu⟩)
      {w | IsPar w u ∧ Q (w.pth ⟨u.dep, hu⟩)} := by
    intro w hw w' hw' he
    refine ext (by rw [hw.1.1, hw'.1.1]) fun i => ?_
    by_cases hi : i = ⟨u.dep, hu⟩
    · subst hi; exact he
    · have : i.val ≠ u.dep := fun h => hi (Fin.ext h)
      rw [hw.1.2 i this, hw'.1.2 i this]
  rw [← hinj.ncard_image]
  congr 1
  ext a
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, ⟨hw, hq⟩, rfl⟩
    refine ⟨?_, hq⟩
    by_cases h0 : u.dep = 0
    · exact Or.inl h0
    · exact Or.inr (w.pth_lt (by simp; omega) (by simp [hw.1]))
  · rintro ⟨ha, hq⟩
    exact ⟨u.child hu a ha, ⟨isPar_child u hu a ha, by rwa [child_pth]⟩, child_pth u hu a ha⟩

lemma ncard_admissible (u : TNode Δ m) :
    {a : Fin Δ | (u.dep = 0 ∨ a.val < Δ - 1) ∧ True}.ncard = if u.dep = 0 then Δ else Δ - 1 := by
  split_ifs with h
  · simp [h]
  · simp only [h, false_or, and_true]
    rw [Set.ncard_eq_toFinset_card']
    simp [Fin.card_filter_val_lt]

/-- The number of children of `u`. -/
lemma ncard_children_all (u : TNode Δ m) :
    {w | IsPar w u}.ncard = if u.dep < m then (if u.dep = 0 then Δ else Δ - 1) else 0 := by
  split_ifs with hu h0
  · have := ncard_children u hu (fun _ => True)
    simp only [and_true] at this
    rw [this]; simp [h0]
  · have := ncard_children u hu (fun _ => True)
    simp only [and_true] at this
    rw [this]
    have := ncard_admissible u
    simpa only [h0, ite_false, and_true] using this
  · rw [Set.ncard_eq_zero]
    ext w; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hw; have := hw.1; have := w.dep_le; have := u.dep_le; omega

/-- The parent of `u`, if any: at most one, and exactly one iff `dep u ≠ 0`. -/
lemma ncard_parents [NeZero Δ] (u : TNode Δ m) :
    {w | IsPar u w}.ncard = if u.dep = 0 then 0 else 1 := by
  split_ifs with h0
  · rw [Set.ncard_eq_zero]
    ext w; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hw; have := hw.1; omega
  · rw [Set.ncard_eq_one]
    have hlt : u.dep - 1 < m := by have := u.dep_le; omega
    have h1 : ∀ i : Fin m, u.dep - 1 ≤ i.val →
        (Function.update u.pth ⟨u.dep - 1, hlt⟩ ⟨0, Nat.pos_of_neZero Δ⟩ i).val = 0 := by
      intro i hi
      by_cases h : i = ⟨u.dep - 1, hlt⟩
      · subst h; simp
      · rw [Function.update_of_ne h]
        have : i.val ≠ u.dep - 1 := fun h' => h (Fin.ext h')
        exact u.pth_of_le (by omega)
    have h2 : ∀ i : Fin m, 0 < i.val → i.val < u.dep - 1 →
        (Function.update u.pth ⟨u.dep - 1, hlt⟩ ⟨0, Nat.pos_of_neZero Δ⟩ i).val < Δ - 1 := by
      intro i h0 hi
      have : i ≠ ⟨u.dep - 1, hlt⟩ := by intro h; subst h; simp at hi
      rw [Function.update_of_ne this]
      exact u.pth_lt h0 (by omega)
    let w : TNode Δ m := mk (u.dep - 1) (by omega) _ h1 h2
    have hw : IsPar u w := ⟨by simp [w]; omega, fun i hi => by
      have : i ≠ ⟨u.dep - 1, hlt⟩ := fun h => hi (by rw [h]; simp [w])
      simp only [w, mk_pth]; rw [Function.update_of_ne this]⟩
    exact ⟨w, Set.ext fun w' => ⟨fun h => isPar_unique h hw, fun h => h ▸ hw⟩⟩

end TNode

open TNode

/-- The balanced tree `T` of radius `m`: every node is joined to its parent. -/
def tree (Δ m : ℕ) : SimpleGraph (TNode Δ m) := SimpleGraph.fromRel IsPar

lemma tree_adj {u w : TNode Δ m} : (tree Δ m).Adj u w ↔ IsPar u w ∨ IsPar w u := by
  rw [tree, fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun he => ?_, h⟩
    subst he
    rcases h with h | h <;> (have := h.1; omega)

lemma tree_neighborSet (u : TNode Δ m) :
    (tree Δ m).neighborSet u = {w | IsPar u w} ∪ {w | IsPar w u} := by
  ext w; simp [tree_adj]

lemma deg_tree [NeZero Δ] (u : TNode Δ m) :
    deg (tree Δ m) u = (if u.dep = 0 then 0 else 1) +
      (if u.dep < m then (if u.dep = 0 then Δ else Δ - 1) else 0) := by
  rw [deg, tree_neighborSet, Set.ncard_union_eq, ncard_parents, ncard_children_all]
  rw [Set.disjoint_left]
  intro w h1 h2
  have := h1.1; have := h2.1; simp only [Set.mem_ofPred_eq] at *; omega

lemma deg_tree_inner [NeZero Δ] (hΔ : 1 ≤ Δ) {u : TNode Δ m} (hu : u.dep < m) :
    deg (tree Δ m) u = Δ := by
  rw [deg_tree]; split_ifs <;> omega

lemma deg_tree_leaf [NeZero Δ] {u : TNode Δ m} (hu : u.dep = m) (hm : 0 < m) :
    deg (tree Δ m) u = 1 := by
  rw [deg_tree]; split_ifs <;> omega

lemma deg_tree_le [NeZero Δ] (u : TNode Δ m) : deg (tree Δ m) u ≤ Δ := by
  have := Nat.pos_of_neZero Δ
  rw [deg_tree]; split_ifs <;> omega

/-- Along an edge of `T` the depth changes by one. -/
lemma tree_adj_dep {u w : TNode Δ m} (h : (tree Δ m).Adj u w) :
    w.dep ≤ u.dep + 1 ∧ u.dep ≤ w.dep + 1 := by
  rcases tree_adj.1 h with h | h <;> (have := h.1; omega)

/-- The depth is at most the distance from the root. -/
lemma dep_le_edist [NeZero Δ] (u : TNode Δ m) : (u.dep : ℕ∞) ≤ (tree Δ m).edist root u := by
  have key : ∀ {a b : TNode Δ m} (w : (tree Δ m).Walk a b), b.dep ≤ a.dep + w.length := by
    intro a b w
    induction w with
    | nil => simp
    | cons h w ih => have := tree_adj_dep h; simp only [Walk.length_cons]; omega
  by_cases hr : (tree Δ m).edist root u = ⊤
  · rw [hr]; exact le_top
  · obtain ⟨w, hw⟩ := exists_walk_of_edist_ne_top hr
    rw [← hw]; have := key w; simp at this; exact_mod_cast this

/-! #### `T'` -/

/-- The leaves (depth `r + 1`) with last index `0` are moved. -/
def Moved {r : ℕ} (w : TNode Δ (r + 1)) : Prop := w.dep = r + 1 ∧ (w.pth (Fin.last r)).val = 0

/-- `u` is the sibling leaf with last index `1` of the moved leaf `w`: its new parent in `T'`. -/
def IsSib {r : ℕ} (w u : TNode Δ (r + 1)) : Prop :=
  u.dep = r + 1 ∧ (u.pth (Fin.last r)).val = 1 ∧ ∀ i, i ≠ Fin.last r → u.pth i = w.pth i

/-- The parent relation of `T'`. -/
def IsPar' {r : ℕ} (w u : TNode Δ (r + 1)) : Prop :=
  (¬ Moved w ∧ IsPar w u) ∨ (Moved w ∧ IsSib w u)

/-- The tree `T'` of the proof of Lemma 18: `T` (radius `r + 1`) where, below every node at depth
`r`, the leaf child with index `0` is detached and re-attached below its sibling with index `1`.
Same vertex set as `T`. -/
def tree' (Δ r : ℕ) : SimpleGraph (TNode Δ (r + 1)) := SimpleGraph.fromRel IsPar'

variable {r : ℕ}

lemma tree'_adj {u w : TNode Δ (r + 1)} : (tree' Δ r).Adj u w ↔ u ≠ w ∧ (IsPar' u w ∨ IsPar' w u) :=
  fromRel_adj _ _ _

/-- Nodes of depth `< r` have the same neighbours in `T` and `T'`. -/
lemma tree'_adj_iff {u : TNode Δ (r + 1)} (hu : u.dep < r) (w : TNode Δ (r + 1)) :
    (tree Δ (r + 1)).Adj u w ↔ (tree' Δ r).Adj u w := by
  have hnm : ¬ Moved u := fun h => by have := h.1; omega
  have e1 : IsPar' u w ↔ IsPar u w := by simp [IsPar', hnm]
  have e2 : IsPar' w u ↔ IsPar w u := by
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact h
      · have := h.1; omega
    · intro h
      left; refine ⟨fun hm => ?_, h⟩
      have := hm.1; have := h.1; omega
  rw [tree', fromRel_adj, tree_adj, e1, e2]
  constructor
  · intro h; refine ⟨fun he => ?_, h⟩; subst he; rcases h with h | h <;> (have := h.1; omega)
  · exact fun h => h.2

lemma deg_tree'_eq_of_lt {u : TNode Δ (r + 1)} (hu : u.dep < r) :
    deg (tree' Δ r) u = deg (tree Δ (r + 1)) u := by
  unfold deg; congr 1; ext w; exact (tree'_adj_iff hu w).symm

/-- In `T'`, nodes at depth `r` have degree `Δ - 1`. -/
lemma deg_tree'_mid [NeZero Δ] (hΔ : 3 ≤ Δ) {u : TNode Δ (r + 1)} (hu : u.dep = r) :
    deg (tree' Δ r) u = Δ - 1 := by
  have hnm : ¬ Moved u := fun h => by have := h.1; omega
  have hlt : u.dep < r + 1 := by omega
  have hidx : (⟨u.dep, hlt⟩ : Fin (r + 1)) = Fin.last r := Fin.ext (by simp [hu])
  have hN : (tree' Δ r).neighborSet u =
      {w | IsPar u w} ∪ {w | IsPar w u ∧ (fun a : Fin Δ => a.val ≠ 0) (w.pth ⟨u.dep, hlt⟩)} := by
    ext w
    simp only [mem_neighborSet, tree'_adj, Set.mem_union, Set.mem_ofPred_eq, IsPar', hnm,
      not_false_eq_true, true_and, false_and, or_false, hidx]
    constructor
    · rintro ⟨-, h | h⟩
      · exact Or.inl h
      · rcases h with ⟨hm, hp⟩ | ⟨-, hs⟩
        · refine Or.inr ⟨hp, fun h0 => hm ⟨?_, h0⟩⟩
          rw [hp.1, hu]
        · have := hs.1; omega
    · intro h
      refine ⟨fun he => ?_, ?_⟩
      · subst he; rcases h with h | ⟨h, -⟩ <;> (have := h.1; omega)
      rcases h with h | ⟨hp, h0⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨fun hm => h0 hm.2, hp⟩)
  rw [deg, hN, Set.ncard_union_eq, ncard_parents, ncard_children u hlt (fun a : Fin Δ => a.val ≠ 0)]
  · have hadm : {a : Fin Δ | (u.dep = 0 ∨ a.val < Δ - 1) ∧ a.val ≠ 0} =
        {a : Fin Δ | (u.dep = 0 ∨ a.val < Δ - 1)} \ {⟨0, by omega⟩} := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, Fin.ext_iff]
    rw [hadm, Set.ncard_sdiff_singleton_of_mem (by simp; omega)]
    have := ncard_admissible (Δ := Δ) u
    simp only [and_true] at this
    rw [this]
    split_ifs <;> omega
  · rw [Set.disjoint_left]
    intro w h1 h2
    have := h1.1; have := h2.1.1; simp only [Set.mem_ofPred_eq] at *; omega

/-- In `T'`, the leaves have degree at most `2`. -/
lemma deg_tree'_leaf_le {u : TNode Δ (r + 1)} (hu : u.dep = r + 1) : deg (tree' Δ r) u ≤ 2 := by
  have hN : (tree' Δ r).neighborSet u ⊆ {w | IsPar' u w} ∪ {w | IsPar' w u} := by
    intro w hw; exact (tree'_adj.1 hw).2
  have h1 : {w | IsPar' u w}.ncard ≤ 1 := by
    rw [Set.ncard_le_one_iff]
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, IsPar'] at ha hb
    rcases ha with ⟨hm, ha⟩ | ⟨hm, ha⟩ <;> rcases hb with ⟨hm', hb⟩ | ⟨hm', hb⟩
    · exact isPar_unique ha hb
    · exact absurd hm' hm
    · exact absurd hm hm'
    · refine ext (by rw [ha.1, hb.1]) fun i => ?_
      by_cases hi : i = Fin.last r
      · subst hi; exact Fin.ext (by rw [ha.2.1, hb.2.1])
      · rw [ha.2.2 i hi, hb.2.2 i hi]
  have h2 : {w | IsPar' w u}.ncard ≤ 1 := by
    rw [Set.ncard_le_one_iff]
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, IsPar'] at ha hb
    have : ∀ c : TNode Δ (r + 1), (¬ Moved c ∧ IsPar c u) ∨ (Moved c ∧ IsSib c u) →
        Moved c ∧ IsSib c u := by
      rintro c (⟨-, hc⟩ | hc)
      · have := hc.1; have := c.dep_le; omega
      · exact hc
    obtain ⟨hma, hsa⟩ := this a ha
    obtain ⟨hmb, hsb⟩ := this b hb
    refine ext (by rw [hma.1, hmb.1]) fun i => ?_
    by_cases hi : i = Fin.last r
    · subst hi; exact Fin.ext (by rw [hma.2, hmb.2])
    · rw [← hsa.2.2 i hi, ← hsb.2.2 i hi]
  calc deg (tree' Δ r) u ≤ ({w | IsPar' u w} ∪ {w | IsPar' w u}).ncard :=
        Set.ncard_le_ncard hN (Set.toFinite _)
    _ ≤ {w | IsPar' u w}.ncard + {w | IsPar' w u}.ncard := Set.ncard_union_le _ _
    _ ≤ 2 := by omega

/-- `T'` has maximum degree `≤ Δ`. -/
lemma deg_tree'_le [NeZero Δ] (hΔ : 3 ≤ Δ) (u : TNode Δ (r + 1)) : deg (tree' Δ r) u ≤ Δ := by
  rcases lt_trichotomy u.dep r with h | h | h
  · rw [deg_tree'_eq_of_lt h]; exact deg_tree_le u
  · rw [deg_tree'_mid hΔ h]; omega
  · have := deg_tree'_leaf_le (Δ := Δ) (show u.dep = r + 1 by have := u.dep_le; omega); omega

/-- `T` and `T'` cannot be distinguished at the root in `r` rounds: they agree on all edges at
nodes of distance `< r` from the root. -/
theorem gAgree_tree_tree' [NeZero Δ] : GAgree (tree Δ (r + 1)) (tree' Δ r) root r := by
  intro x hx y
  have h1 := dep_le_edist (Δ := Δ) (m := r + 1) x
  have hlt : x.dep < r := by
    have := lt_of_le_of_lt h1 hx
    exact_mod_cast this
  exact tree'_adj_iff hlt y

/-! #### The value of `d` at the root -/

/-- In every `P*`-labelling of `T` (radius `m ≥ 1`), the root has `d = 1`: its pointer chain goes
down to a leaf of degree `1`. -/
theorem tree_root_d [NeZero Δ] (hΔ : 3 ≤ Δ) (hm : 0 < m) {p : TNode Δ m → Option (TNode Δ m)}
    {d : TNode Δ m → ℕ} (hP : ∀ v, PHappy Δ (tree Δ m) d p v) : d root = 1 := by
  refine chain_eq (G := tree Δ m) (Δ := Δ) (L := m) (c := 1) TNode.dep IsPar
    (fun _ _ _ h h' => isPar_unique h h') (fun u hu => deg_tree_inner (by omega) hu)
    (fun u hu => deg_tree_leaf hu hm) (by omega) ?_ hP root (by simp) (Or.inl ?_)
  · intro u w _ h
    rcases tree_adj.1 h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, h.1⟩
  · intro w h; have := h.1; simp at this

/-- In every `P*`-labelling of `T'`, the root has `d = Δ - 1`: its pointer chain stops at depth `r`,
where all nodes have degree `Δ - 1`. -/
theorem tree'_root_d [NeZero Δ] (hΔ : 3 ≤ Δ) {p : TNode Δ (r + 1) → Option (TNode Δ (r + 1))}
    {d : TNode Δ (r + 1) → ℕ} (hP : ∀ v, PHappy Δ (tree' Δ r) d p v) : d root = Δ - 1 := by
  refine chain_eq (G := tree' Δ r) (Δ := Δ) (L := r) (c := Δ - 1) TNode.dep IsPar
    (fun _ _ _ h h' => isPar_unique h h')
    (fun u hu => by rw [deg_tree'_eq_of_lt hu]; exact deg_tree_inner (by omega) (by omega))
    (fun u hu => deg_tree'_mid hΔ hu) (by omega) ?_ hP root (by simp) (Or.inl ?_)
  · intro u w hu h
    rcases tree_adj.1 ((tree'_adj_iff hu w).2 h) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, h.1⟩
  · intro w h; have := h.1; simp at this

/-! #### Lemma 18 -/

/-- The number of nodes of `T` (and `T'`) is `n ≤ Δ^(2r+2)`, so radius `r ≥ log_Δ n / 2 - 1`.
(The exact value is `1 + Δ((Δ-1)^(r+1) - 1)/(Δ-2)`; the crude bound suffices for `Ω(log_Δ n)`.) -/
theorem card_tnode_le (hΔ : 3 ≤ Δ) (r : ℕ) : Fintype.card (TNode Δ (r + 1)) ≤ Δ ^ (2 * r + 2) := by
  calc Fintype.card (TNode Δ (r + 1)) ≤ Fintype.card (Fin (r + 2) × (Fin (r + 1) → Fin Δ)) :=
        Fintype.card_subtype_le _
    _ = (r + 2) * Δ ^ (r + 1) := by simp
    _ ≤ Δ ^ (r + 1) * Δ ^ (r + 1) := by
        gcongr
        exact Nat.lt_pow_self (by omega)
    _ = Δ ^ (2 * r + 2) := by rw [← pow_add]; ring_nf

/-- **Lemma 18** of [BHOS19] (indistinguishability core): for `Δ ≥ 3`, no `r`-round LOCAL
algorithm `f` (with arbitrary input labels `x`, e.g. random bits) solves `P*` on both `T` and `T'`
(radius `r + 1`, same node set): the root sees the same view in both, but must output `d = 1` in
`T` and `d = Δ - 1` in `T'`. -/
theorem lemma18 (hΔ : 3 ≤ Δ) (r : ℕ) {α : Type*}
    {f : SimpleGraph (TNode Δ (r + 1)) → (TNode Δ (r + 1) → α) → TNode Δ (r + 1) →
      ℕ × Option (TNode Δ (r + 1))} (hf : IsLocal r f) (x : TNode Δ (r + 1) → α) :
    ¬ (Solves Δ (tree Δ (r + 1)) (f (tree Δ (r + 1)) x) ∧
      Solves Δ (tree' Δ r) (f (tree' Δ r) x)) := by
  have : NeZero Δ := ⟨by omega⟩
  rintro ⟨h1, h2⟩
  have e : f (tree Δ (r + 1)) x root = f (tree' Δ r) x root :=
    hf _ _ _ _ root ⟨gAgree_tree_tree', fun _ _ => rfl⟩
  have d1 := tree_root_d hΔ (by omega) h1
  have d2 := tree'_root_d hΔ h2
  simp only [e] at d1
  omega

/-- **Lemma 18** of [BHOS19], deterministic form: for every `Δ ≥ 3` and `r`, there is a node set
(identifier set) with `n ≤ Δ^(2r+2)` elements on which no `r`-round LOCAL algorithm solves `P*` on
all graphs of maximum degree `≤ Δ`. Hence the complexity of `P*` is `Ω(log_Δ n)`. -/
theorem lemma18_lowerBound (hΔ : 3 ≤ Δ) (r : ℕ) :
    Fintype.card (TNode Δ (r + 1)) ≤ Δ ^ (2 * r + 2) ∧
    ∀ {α : Type*} [Nonempty α]
      (f : SimpleGraph (TNode Δ (r + 1)) → (TNode Δ (r + 1) → α) → TNode Δ (r + 1) →
        ℕ × Option (TNode Δ (r + 1))), IsLocal r f →
      ¬ ∀ (G : SimpleGraph (TNode Δ (r + 1))) (x : TNode Δ (r + 1) → α),
        (∀ v, deg G v ≤ Δ) → Solves Δ G (f G x) := by
  have : NeZero Δ := ⟨by omega⟩
  refine ⟨card_tnode_le hΔ r, fun {α} _ f hf hall => ?_⟩
  let x : TNode Δ (r + 1) → α := fun _ => Classical.arbitrary α
  exact lemma18 hΔ r hf x ⟨hall _ x deg_tree_le, hall _ x (deg_tree'_le hΔ)⟩

/-- **Lemma 18** of [BHOS19], randomized form: for any distribution `μ` of the random input
labels `x` (any discrete joint distribution of the nodes' random bits), an `r`-round algorithm
succeeds on `T` and on `T'` with probabilities summing to at most `1`; so it fails with probability
at least `1/2` on one of them. -/
theorem lemma18_randomized (hΔ : 3 ≤ Δ) (r : ℕ) {α : Type*}
    {f : SimpleGraph (TNode Δ (r + 1)) → (TNode Δ (r + 1) → α) → TNode Δ (r + 1) →
      ℕ × Option (TNode Δ (r + 1))} (hf : IsLocal r f) (μ : PMF (TNode Δ (r + 1) → α)) :
    μ.toOuterMeasure {x | Solves Δ (tree Δ (r + 1)) (f (tree Δ (r + 1)) x)} +
      μ.toOuterMeasure {x | Solves Δ (tree' Δ r) (f (tree' Δ r) x)} ≤ 1 := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add, ← μ.tsum_coe]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases h1 : Solves Δ (tree Δ (r + 1)) (f (tree Δ (r + 1)) x)
  · have h2 : ¬ Solves Δ (tree' Δ r) (f (tree' Δ r) x) := fun h2 => lemma18 hΔ r hf x ⟨h1, h2⟩
    simp [Set.indicator, h1, h2]
  · by_cases h2 : Solves Δ (tree' Δ r) (f (tree' Δ r) x) <;> simp [Set.indicator, h1, h2]

end Trees

end Podc.MinimalSymmetryBreaking
