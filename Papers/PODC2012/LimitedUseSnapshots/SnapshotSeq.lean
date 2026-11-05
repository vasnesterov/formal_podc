import Papers.PODC2012.LimitedUseSnapshots.SnapshotDefs

/-!
# Algorithm 3: trees and the auxiliary `seq` arrays

Combinatorics of the tree addresses, and the relation `SeqR R c t a k s` that plays the role of
the paper's auxiliary array `u.seq` (proof of Theorem 4.2): `s : P → ℕ` is the vector of leaf
pointers represented by index `k` of the node at address `a` (subtree `t`), given the sets
`R a` of all states ever taken by the max arrays and the leaf counters `c`.

The paper's invariants on `seq` are `SeqR.sum` (`ptr` is the sum of `u.seq[ptr]`) and `SeqR.le`
(`ptr ≤ ptr'` implies `u.seq[ptr] ≤ u.seq[ptr']`, from the max arrays' states forming a chain).
-/

namespace Podc.LimitedUseSnapshots.Snapshot

open Cslib.SharedMemory

namespace BTree

variable {P : Type}

@[simp] lemma sub_nil (t : BTree P) : t.sub [] = some t := rfl

@[simp] lemma sub_cons (t : BTree P) (b : Bool) (a : List Bool) :
    t.sub (b :: a) = (t.sub a).bind (fun u => u.child b) := rfl

lemma sub_append (t : BTree P) (c a : List Bool) :
    t.sub (c ++ a) = (t.sub a).bind (fun u => u.sub c) := by
  induction c with
  | nil => simp
  | cons b c ih => simp [ih, Option.bind_assoc]

@[simp] lemma node_sub_false (l r : BTree P) : (node l r).sub [false] = some l := rfl
@[simp] lemma node_sub_true (l r : BTree P) : (node l r).sub [true] = some r := rfl

lemma node_sub_concat (l r : BTree P) (c : List Bool) (b : Bool) :
    (node l r).sub (c ++ [b]) = (if b then r else l).sub c := by
  rw [sub_append]; cases b <;> rfl

lemma leaf_sub_cons (p : P) (b : Bool) (c : List Bool) : (leaf p).sub (b :: c) = none := by
  induction c generalizing b with
  | nil => rfl
  | cons b' c ih => simp only [sub_cons] at ih ⊢; rw [ih b']; rfl

lemma eq_nil_of_leaf_sub {p : P} {c : List Bool} {u : BTree P} (h : (leaf p).sub c = some u) :
    c = [] ∧ u = leaf p := by
  cases c with
  | nil => simp at h; exact ⟨rfl, h.symm⟩
  | cons b c => rw [leaf_sub_cons] at h; cases h

lemma child_leaves_sublist {u w : BTree P} {b : Bool} (h : u.child b = some w) :
    w.leaves.Sublist u.leaves := by
  cases u with
  | leaf p => cases h
  | node l r =>
    cases b
    · cases h; exact List.sublist_append_left _ _
    · cases h; exact List.sublist_append_right _ _

lemma sub_leaves_sublist {t u : BTree P} {a : List Bool} (h : t.sub a = some u) :
    u.leaves.Sublist t.leaves := by
  induction a generalizing u with
  | nil => simp at h; subst h; exact List.Sublist.refl _
  | cons b a ih =>
    simp only [sub_cons] at h
    cases hw : t.sub a with
    | none => simp [hw] at h
    | some w =>
      simp only [hw, Option.bind_some] at h
      exact (child_leaves_sublist h).trans (ih hw)

lemma mem_leaves_of_sub {t u : BTree P} {a : List Bool} (h : t.sub a = some u) {j : P}
    (hj : j ∈ u.leaves) : j ∈ t.leaves := (sub_leaves_sublist h).subset hj

lemma nodup_of_sub {t u : BTree P} {a : List Bool} (h : t.sub a = some u)
    (hnd : t.leaves.Nodup) : u.leaves.Nodup := hnd.sublist (sub_leaves_sublist h)

variable [DecidableEq P]

lemma suffix_concat {c d : List Bool} (b : Bool) (h : c <:+ d) : c ++ [b] <:+ d ++ [b] := by
  obtain ⟨e, he⟩ := h; exact ⟨e, by simp [← he]⟩

lemma suffix_path_of_sub {t u : BTree P} (hnd : t.leaves.Nodup) {a : List Bool}
    (h : t.sub a = some u) {j : P} (hj : j ∈ u.leaves) : a <:+ t.path j := by
  induction t generalizing a with
  | leaf p =>
    obtain ⟨rfl, -⟩ := eq_nil_of_leaf_sub h; exact List.nil_suffix
  | node l r ihl ihr =>
    rcases List.eq_nil_or_concat' a with rfl | ⟨c, b, rfl⟩
    · exact List.nil_suffix
    · simp only [leaves] at hnd
      rw [node_sub_concat] at h
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        have hjl : j ∈ l.leaves := mem_leaves_of_sub h hj
        simp only [path, hjl, ↓reduceIte]
        exact suffix_concat _ (ihl (List.nodup_append.1 hnd).1 h)
      · simp only [↓reduceIte] at h
        have hjr : j ∈ r.leaves := mem_leaves_of_sub h hj
        have hjl : j ∉ l.leaves := fun hjl =>
          (List.nodup_append.1 hnd).2.2 j hjl j hjr rfl
        simp only [path, hjl, ↓reduceIte]
        exact suffix_concat _ (ihr (List.nodup_append.1 hnd).2.1 h)

lemma sub_path {t : BTree P} {j : P} (hj : j ∈ t.leaves) : t.sub (t.path j) = some (leaf j) := by
  induction t with
  | leaf p => simp [leaves] at hj; subst hj; rfl
  | node l r ihl ihr =>
    simp only [leaves, List.mem_append] at hj
    by_cases hjl : j ∈ l.leaves
    · simp only [path, hjl, ↓reduceIte, node_sub_concat, Bool.false_eq_true]; exact ihl hjl
    · simp only [path, hjl, ↓reduceIte, node_sub_concat]
      exact ihr (hj.resolve_left hjl)

lemma sub_of_suffix_path {t : BTree P} {j : P} (hj : j ∈ t.leaves) {a : List Bool}
    (h : a <:+ t.path j) : ∃ u, t.sub a = some u ∧ j ∈ u.leaves := by
  obtain ⟨d, hd⟩ := h
  have := sub_path hj
  rw [← hd, sub_append] at this
  cases hu : t.sub a with
  | none => simp [hu] at this
  | some u =>
    refine ⟨u, rfl, ?_⟩
    simp only [hu, Option.bind_some] at this
    exact (sub_leaves_sublist this).subset (by simp [leaves])

lemma path_eq_of_sub_leaf {t : BTree P} (hnd : t.leaves.Nodup) {a : List Bool} {j : P}
    (h : t.sub a = some (leaf j)) : a = t.path j := by
  have hs := suffix_path_of_sub hnd h (j := j) (by simp [leaves])
  obtain ⟨d, hd⟩ := hs
  have hp := sub_path (mem_leaves_of_sub h (by simp [leaves] : j ∈ (leaf j).leaves))
  rw [← hd, sub_append, h, Option.bind_some] at hp
  rw [← hd, (eq_nil_of_leaf_sub hp).1, List.nil_append]

lemma ne_path_of_sub_node {t : BTree P} {a : List Bool} {l r : BTree P}
    (h : t.sub a = some (node l r)) (j : P) (hj : j ∈ t.leaves) : a ≠ t.path j := by
  rintro rfl; rw [sub_path hj] at h; cases h

omit [DecidableEq P] in
lemma leavesAt_of_sub {t u : BTree P} {a : List Bool} (h : t.sub a = some u) :
    t.leavesAt a = u.leaves := by simp [leavesAt, h]

/-- Going up from a non-root ancestor-or-self `a` of a leaf. -/
lemma exists_parent {t : BTree P} {i : P} (hi : i ∈ t.leaves) {b : Bool} {p : List Bool}
    (h : b :: p <:+ t.path i) :
    p <:+ t.path i ∧ ∃ l r, t.sub p = some (node l r) ∧ (node l r).child b = t.sub (b :: p) := by
  have hp : p <:+ t.path i := (List.suffix_cons b p).trans h
  refine ⟨hp, ?_⟩
  obtain ⟨u, hu, -⟩ := sub_of_suffix_path hi h
  simp only [sub_cons] at hu
  cases hw : t.sub p with
  | none => simp [hw] at hu
  | some w =>
    simp only [hw, Option.bind_some] at hu
    cases w with
    | leaf q => cases hu
    | node l r => exact ⟨l, r, rfl, by simp [hw, hu]⟩

lemma child_suffix {t : BTree P} (hnd : t.leaves.Nodup) {a : List Bool} {l r : BTree P}
    (h : t.sub a = some (node l r)) {j : P} (hj : j ∈ (node l r).leaves) :
    (j ∈ l.leaves ∧ false :: a <:+ t.path j) ∨ (j ∈ r.leaves ∧ true :: a <:+ t.path j) := by
  simp only [leaves, List.mem_append] at hj
  rcases hj with hj | hj
  · exact Or.inl ⟨hj, suffix_path_of_sub hnd (by simp [h, child]) hj⟩
  · exact Or.inr ⟨hj, suffix_path_of_sub hnd (by simp [h, child]) hj⟩

omit [DecidableEq P] in
lemma disjoint_of_node {l r : BTree P} (hnd : (node l r).leaves.Nodup) {j : P}
    (hl : j ∈ l.leaves) (hr : j ∈ r.leaves) : False :=
  (List.nodup_append.1 hnd).2.2 j hl j hr rfl

end BTree

/-! ### The auxiliary `seq` arrays -/

variable {P : Type} [DecidableEq P]

/-- `SeqR R c t a k s`: the index `k` of the node at address `a` (subtree `t`) represents the
vector of leaf pointers `s` (the paper's `u.seq[k] = s`), given that the max array of every node
`a'` has taken exactly the states in `R a'` so far and the leaf counters are `c`. -/
def SeqR (R : List Bool → Set (ℕ × ℕ)) (c : P → ℕ) :
    BTree P → List Bool → ℕ → (P → ℕ) → Prop
  | .leaf j, _, k, s => k ≤ c j ∧ s = Pi.single j k
  | .node l r, a, k, s => ∃ x y, (x, y) ∈ R a ∧ x + y = k ∧
      ∃ s₁ s₂, SeqR R c l (false :: a) x s₁ ∧ SeqR R c r (true :: a) y s₂ ∧ s = s₁ + s₂

/-- The states taken by each max array form a chain. -/
def Chain (R : List Bool → Set (ℕ × ℕ)) : Prop := ∀ a, ∀ p ∈ R a, ∀ q ∈ R a, p ≤ q ∨ q ≤ p

namespace SeqR

variable {R R' : List Bool → Set (ℕ × ℕ)} {c c' : P → ℕ}

lemma mono (hR : ∀ a, R a ⊆ R' a) (hc : c ≤ c') :
    ∀ {t : BTree P} {a k s}, SeqR R c t a k s → SeqR R' c' t a k s
  | .leaf j, _, _, _, h => ⟨h.1.trans (hc j), h.2⟩
  | .node _ _, _, _, _, ⟨x, y, hxy, hk, s₁, s₂, h₁, h₂, hs⟩ =>
    ⟨x, y, hR _ hxy, hk, s₁, s₂, mono hR hc h₁, mono hR hc h₂, hs⟩

/-- Two pairs of a chain with comparable sums are comparable in the same direction. -/
lemma chain_le {p q : ℕ × ℕ} (hpq : p ≤ q ∨ q ≤ p) (h : p.1 + p.2 ≤ q.1 + q.2) : p ≤ q := by
  rcases hpq with h' | h'
  · exact h'
  · obtain ⟨h1, h2⟩ := Prod.mk_le_mk.1 h'
    exact Prod.mk_le_mk.2 ⟨by omega, by omega⟩

/-- The paper's second invariant: `seq` is monotone in the index. -/
lemma le (hch : Chain R) :
    ∀ {t : BTree P} {a k k' s s'}, SeqR R c t a k s → SeqR R c t a k' s' → k ≤ k' → s ≤ s'
  | .leaf j, _, _, _, _, _, h, h', hk => by
    rw [h.2, h'.2]; exact Pi.single_mono (f := fun _ : P => ℕ) j hk
  | .node _ _, a, _, _, _, _, ⟨x, y, hxy, hk, s₁, s₂, h₁, h₂, hs⟩,
      ⟨x', y', hxy', hk', s₁', s₂', h₁', h₂', hs'⟩, hkk => by
    have := chain_le (p := (x, y)) (q := (x', y')) (hch a _ hxy _ hxy') (by simp; omega)
    obtain ⟨hx, hy⟩ := Prod.mk_le_mk.1 this
    rw [hs, hs']
    exact fun j => Nat.add_le_add (le hch h₁ h₁' hx j) (le hch h₂ h₂' hy j)

lemma unique (hch : Chain R) {t : BTree P} {a k s s'} (h : SeqR R c t a k s)
    (h' : SeqR R c t a k s') : s = s' :=
  le_antisymm (le hch h h' le_rfl) (le hch h' h le_rfl)

lemma zero_of_not_mem :
    ∀ {t : BTree P} {a k s}, SeqR R c t a k s → ∀ j, j ∉ t.leaves → s j = 0
  | .leaf p, _, _, _, h, j, hj => by
    rw [h.2]; simp only [BTree.leaves, List.mem_singleton] at hj; simp [hj]
  | .node _ _, _, _, _, ⟨_, _, _, _, s₁, s₂, h₁, h₂, hs⟩, j, hj => by
    simp only [BTree.leaves, List.mem_append, not_or] at hj
    rw [hs, Pi.add_apply, zero_of_not_mem h₁ j hj.1, zero_of_not_mem h₂ j hj.2]

lemma le_cnt :
    ∀ {t : BTree P} {a k s}, t.leaves.Nodup → SeqR R c t a k s → s ≤ c
  | .leaf p, _, _, _, _, h, j => by
    rw [h.2]
    by_cases hj : j = p
    · subst hj; simpa using h.1
    · simp [hj]
  | .node l r, _, _, _, hnd, ⟨_, _, _, _, s₁, s₂, h₁, h₂, hs⟩, j => by
    have hnl := BTree.nodup_of_sub (a := [false]) rfl hnd
    have hnr := BTree.nodup_of_sub (a := [true]) rfl hnd
    rw [hs, Pi.add_apply]
    by_cases hj : j ∈ l.leaves
    · have : s₂ j = 0 := zero_of_not_mem h₂ j fun hr => BTree.disjoint_of_node hnd hj hr
      rw [this, add_zero]; exact le_cnt hnl h₁ j
    · rw [zero_of_not_mem h₁ j hj, zero_add]; exact le_cnt hnr h₂ j

/-- The paper's first invariant: `ptr` is the sum of the elements of `u.seq[ptr]`. -/
lemma sum :
    ∀ {t : BTree P} {a k s}, t.leaves.Nodup → SeqR R c t a k s → (t.leaves.map s).sum = k
  | .leaf p, _, _, _, _, h => by simp [BTree.leaves, h.2]
  | .node l r, _, _, s, hnd, ⟨x, y, _, hk, s₁, s₂, h₁, h₂, hs⟩ => by
    have hnl := BTree.nodup_of_sub (a := [false]) rfl hnd
    have hnr := BTree.nodup_of_sub (a := [true]) rfl hnd
    have e1 : l.leaves.map s = l.leaves.map s₁ := List.map_congr_left fun j hj => by
      rw [hs, Pi.add_apply,
        zero_of_not_mem h₂ j fun hr => BTree.disjoint_of_node hnd hj hr, add_zero]
    have e2 : r.leaves.map s = r.leaves.map s₂ := List.map_congr_left fun j hj => by
      rw [hs, Pi.add_apply,
        zero_of_not_mem h₁ j fun hl => BTree.disjoint_of_node hnd hl hj, zero_add]
    simp only [BTree.leaves, List.map_append, List.sum_append, e1, e2, sum hnl h₁, sum hnr h₂, hk]

/-- Decomposing the `seq` of a node at a known state `(x, y)` of its max array. -/
lemma node_decomp (hch : Chain R) {l r : BTree P} {a : List Bool} {x y : ℕ} {s : P → ℕ}
    (h : SeqR R c (.node l r) a (x + y) s) (hxy : (x, y) ∈ R a) :
    ∃ s₁ s₂, SeqR R c l (false :: a) x s₁ ∧ SeqR R c r (true :: a) y s₂ ∧ s = s₁ + s₂ := by
  obtain ⟨x', y', hxy', hk, s₁, s₂, h₁, h₂, hs⟩ := h
  have := chain_le (p := (x', y')) (q := (x, y)) (hch a _ hxy' _ hxy) (by simp; omega)
  obtain ⟨h1, h2⟩ := Prod.mk_le_mk.1 this
  obtain rfl : x' = x := by omega
  obtain rfl : y' = y := by omega
  exact ⟨s₁, s₂, h₁, h₂, hs⟩

end SeqR

end Podc.LimitedUseSnapshots.Snapshot
