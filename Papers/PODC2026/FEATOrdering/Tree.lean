import Papers.PODC2026.FEATOrdering.Fairness

/-!
# Comparator-guided BST insertion and two-pointer merge (Lemmas 6.1, 6.2)

FEAT builds, in each round, a balanced binary search tree whose branching is guided by a
(possibly non-transitive) comparator, and takes its in-order traversal; it then stitches the
result with the tail list by a two-pointer merge.

* `BTree.insert c x t` — Algorithm 2 (TryInsert) without the `⊥` case: walk down from the root,
  going left at `u` iff `c x u = True`, and attach `x` as a leaf.
* `buildTree c bal xs` — insert the transactions `xs` in this order; after every insertion apply
  `bal` (AVL rebalancing; we only assume that it preserves the in-order traversal, which holds for
  rotations).
* `lemma_6_1` — the in-order traversal satisfies Adjacent-Comparator Consistency for every
  tournament comparator, every insertion order and every in-order-preserving rebalancing.
* `lemma_6_2` — the two-pointer merge (`List.merge`, which is exactly the paper's stitching loop
  once `cmp` is known) of two consistent lists is consistent.
-/

namespace Podc.FEATOrdering

variable {α : Type*}

/-- Binary trees with keys at internal nodes. -/
inductive BTree (α : Type*) where
  | nil : BTree α
  | node (l : BTree α) (x : α) (r : BTree α) : BTree α

namespace BTree

/-- In-order traversal. -/
def inorder : BTree α → List α
  | nil => []
  | node l x r => inorder l ++ x :: inorder r

/-- Comparator-guided BST insertion (Algorithm 2 with a total comparator): go left at `y` iff
`c x y = True`, attach `x` as a new leaf. -/
def insert (c : α → α → Bool) (x : α) : BTree α → BTree α
  | nil => node nil x nil
  | node l y r => if c x y then node (insert c x l) y r else node l y (insert c x r)

/-- Inserting `x` puts it at exactly one position of the in-order traversal, between its in-order
predecessor `p` (with `c x p = False`: the search went right at `p`) and its successor `s` (with
`c x s = True`: the search went left at `s`). -/
theorem inorder_insert (c : α → α → Bool) (x : α) (t : BTree α) :
    ∃ L₁ L₂, t.inorder = L₁ ++ L₂ ∧ (t.insert c x).inorder = L₁ ++ x :: L₂ ∧
      (∀ p ∈ L₁.getLast?, c x p = false) ∧ (∀ s ∈ L₂.head?, c x s = true) := by
  induction t with
  | nil => exact ⟨[], [], rfl, rfl, by simp, by simp⟩
  | node l y r ihl ihr =>
    by_cases hxy : c x y = true
    · obtain ⟨A₁, A₂, h1, h2, h3, h4⟩ := ihl
      refine ⟨A₁, A₂ ++ y :: r.inorder, by simp [inorder, h1], ?_, h3, ?_⟩
      · simp [insert, hxy, inorder, h2]
      · intro s hs
        cases A₂ with
        | nil => simp at hs; exact hs ▸ hxy
        | cons a A₂ => exact h4 s (by simpa using hs)
    · obtain ⟨B₁, B₂, h1, h2, h3, h4⟩ := ihr
      refine ⟨l.inorder ++ y :: B₁, B₂, by simp [inorder, h1], ?_, ?_, h4⟩
      · simp [insert, hxy, inorder, h2]
      · intro p hp
        rcases List.eq_nil_or_concat B₁ with h | ⟨B, b, h⟩
        · subst h; simp at hp; exact hp ▸ (by simpa using hxy)
        · subst h
          rw [show l.inorder ++ y :: B.concat b = (l.inorder ++ y :: B) ++ [b] by simp,
            List.getLast?_concat] at hp
          have : p = b := by simpa using hp.symm
          exact h3 p (by simp [this, List.concat_eq_append])

theorem inorder_insert_perm (c : α → α → Bool) (x : α) (t : BTree α) :
    (t.insert c x).inorder.Perm (x :: t.inorder) := by
  obtain ⟨L₁, L₂, h1, h2, -, -⟩ := inorder_insert c x t
  rw [h1, h2]
  exact List.perm_middle

end BTree

/-- Build the round tree: insert the transactions of `xs` in order, rebalancing with `bal` after
each insertion. -/
def buildTree (c : α → α → Bool) (bal : BTree α → BTree α) (xs : List α) : BTree α :=
  xs.foldl (fun t x => bal (t.insert c x)) .nil

/-- A comparator is *total* if for all `a, b` one of `c a b`, `c b a` holds (a tournament with
`c a a = True`). -/
def TotalCmp (c : α → α → Bool) : Prop := ∀ a b, c a b = true ∨ c b a = true

theorem AdjConsistent.insert {c : α → α → Bool} (htot : TotalCmp c) {t : BTree α} (x : α)
    (h : AdjConsistent c t.inorder) : AdjConsistent c (t.insert c x).inorder := by
  obtain ⟨L₁, L₂, h1, h2, h3, h4⟩ := BTree.inorder_insert c x t
  unfold AdjConsistent at h ⊢
  rw [h1] at h
  rw [h2]
  obtain ⟨hL₁, hL₂, -⟩ := List.isChain_append.1 h
  refine List.isChain_append.2 ⟨hL₁, List.isChain_cons.2 ⟨h4, hL₂⟩, ?_⟩
  intro p hp y hy
  simp at hy; subst hy
  rcases htot x p with h | h
  · rw [h3 p hp] at h; exact absurd h (by simp)
  · exact h

/-- **Lemma 6.1 (ACC of the round ordering).** For a total (tournament) comparator, any insertion
order and any rebalancing that preserves in-order traversals (AVL rotations), the in-order
traversal of the round tree satisfies Adjacent-Comparator Consistency. -/
theorem lemma_6_1 {c : α → α → Bool} (htot : TotalCmp c) (bal : BTree α → BTree α)
    (hbal : ∀ t, (bal t).inorder = t.inorder) (xs : List α) :
    AdjConsistent c (buildTree c bal xs).inorder := by
  unfold buildTree
  suffices ∀ t : BTree α, AdjConsistent c t.inorder →
      AdjConsistent c (xs.foldl (fun t x => bal (t.insert c x)) t).inorder from
    this _ (by simp [AdjConsistent, BTree.inorder])
  induction xs with
  | nil => intro t h; exact h
  | cons x xs ih =>
    intro t h
    exact ih _ (by rw [AdjConsistent, hbal]; exact AdjConsistent.insert htot x h)

/-- The round ordering is a permutation of the inserted transactions. -/
theorem buildTree_perm (c : α → α → Bool) (bal : BTree α → BTree α)
    (hbal : ∀ t, (bal t).inorder = t.inorder) (xs : List α) :
    (buildTree c bal xs).inorder.Perm xs := by
  unfold buildTree
  suffices ∀ t : BTree α,
      (xs.foldl (fun t x => bal (t.insert c x)) t).inorder.Perm (t.inorder ++ xs) from
    by simpa [BTree.inorder] using this .nil
  induction xs with
  | nil => intro t; simp
  | cons x xs ih =>
    intro t
    refine (ih _).trans ?_
    rw [hbal]
    refine ((BTree.inorder_insert_perm c x t).append_right xs).trans ?_
    simp [List.perm_middle.symm]

/-- The merge invariant of Lemma 6.2: if the last appended element `z` precedes both current
heads, then `z` followed by the merge of the rests is consistent. -/
theorem isChain_cons_merge {c : α → α → Bool} (htot : TotalCmp c) :
    ∀ (xs ys : List α) (z : α), AdjConsistent c xs → AdjConsistent c ys →
      (∀ a ∈ xs.head?, c z a = true) → (∀ b ∈ ys.head?, c z b = true) →
      AdjConsistent c (z :: List.merge xs ys c)
  | [], ys, z, _, hy, _, hzy => by
    simpa [AdjConsistent, List.nil_merge] using List.isChain_cons.2 ⟨hzy, hy⟩
  | x :: xs, [], z, hx, _, hzx, _ => by
    simpa [AdjConsistent] using List.isChain_cons.2 ⟨hzx, hx⟩
  | x :: xs, y :: ys, z, hx, hy, hzx, hzy => by
    rw [List.cons_merge_cons]
    by_cases hxy : c x y = true
    · rw [if_pos hxy]
      refine List.isChain_cons.2 ⟨fun a ha => by simp at ha; exact ha ▸ hzx x (by simp), ?_⟩
      exact isChain_cons_merge htot xs (y :: ys) x (List.isChain_cons.1 hx).2 hy
        (List.isChain_cons.1 hx).1 (by simpa using hxy)
    · rw [if_neg hxy]
      have hyx : c y x = true := (htot x y).resolve_left hxy
      refine List.isChain_cons.2 ⟨fun a ha => by simp at ha; exact ha ▸ hzy y (by simp), ?_⟩
      exact isChain_cons_merge htot (x :: xs) ys y hx (List.isChain_cons.1 hy).2
        (by simpa using hyx) (List.isChain_cons.1 hy).1
  termination_by xs ys => xs.length + ys.length

/-- **Lemma 6.2 (stitching preserves ACC).** The two-pointer merge of two lists satisfying
Adjacent-Comparator Consistency satisfies it too. -/
theorem lemma_6_2 {c : α → α → Bool} (htot : TotalCmp c) {xs ys : List α}
    (hx : AdjConsistent c xs) (hy : AdjConsistent c ys) :
    AdjConsistent c (List.merge xs ys c) := by
  rcases xs with _ | ⟨x, xs⟩
  · simpa [List.nil_merge] using hy
  rcases ys with _ | ⟨y, ys⟩
  · simpa using hx
  rw [List.cons_merge_cons]
  split_ifs with hxy
  · exact isChain_cons_merge htot xs (y :: ys) x (List.isChain_cons.1 hx).2 hy
      (List.isChain_cons.1 hx).1 (by simpa using hxy)
  · exact isChain_cons_merge htot (x :: xs) ys y hx (List.isChain_cons.1 hy).2
      (by simpa using (htot x y).resolve_left hxy) (List.isChain_cons.1 hy).1

end Podc.FEATOrdering
