import Papers.PODC2011.LocallyCheckableProofs.Star

/-!
# Theorem 6.3: fixed-point-free symmetry of trees requires proofs of size `Ω(n)`

A graph has a *fixed-point-free symmetry* if some automorphism moves every node (`HasFPFSym`).
The paper glues two rooted trees by a path, as in Theorem 6.1, and uses that there are `2^Θ(k)`
rooted trees on `k` nodes. We use an explicit family instead: for a word `w ∈ {0,1}^m`, the
caterpillar `cat m w` on `Fin (5m)` has the spine `0 — 1 — ⋯ — (2m-1)` (rooted at `0`) and three
leaves `2m+3i, 2m+3i+1, 2m+3i+2` for every `i < m`, attached to `2i`, to `2i` or `2i+1` (according
to `w i`), and to `2i+1`. So the spine node `2i` has two leaves iff `w i`.

In `cat w ⊛ cat w'` (path of even length `p ≥ 2`) the non-leaf nodes form one long path (spine of
the first copy, the connecting path, spine of the second copy). An automorphism without fixed
points must reverse this path (`StarCons.PathEnum`), so it maps the spine node `2i` of the first
copy to the spine node `2i` of the second copy, and `w i = w' i`. Conversely, the swap of
`cat w ⊛ cat w`
has no fixed point when `p` is even.

Note: a tree with a fixed-point-free automorphism has an even number of nodes (the automorphism
flips the central edge), so only even `n` matter; we prove the lower bound for all large even `n`
(and do not formalise the remark about odd `n`).
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset StarCons

/-- Some automorphism of the graph (induced on the nodes) moves every node. -/
def HasFPFSym {L : Type*} (I : Inst L) : Prop :=
  ∃ φ : I.G.induce (I.V : Set ℕ) ≃g I.G.induce (I.V : Set ℕ), ∀ v, φ v ≠ v

-- CSLib candidate
/-- A graph on `ℕ` in which every vertex has at most one smaller neighbour is acyclic. -/
lemma isAcyclic_of_unique_lt_adj (G : SimpleGraph ℕ)
    (h : ∀ x y z, G.Adj x y → G.Adj x z → y < x → z < x → y = z) : G.IsAcyclic := by
  classical
  intro v c hc
  set u := c.support.toFinset.max' ⟨v, by simp⟩ with hu
  have humem : u ∈ c.support := by
    have := c.support.toFinset.max'_mem ⟨v, by simp⟩
    simpa using this
  have hle : ∀ w ∈ c.support, w ≤ u := fun w hw =>
    c.support.toFinset.le_max' w (by simpa using hw)
  have hc' := hc.rotate humem
  set c' := c.rotate u humem
  have hle' : ∀ i, c'.getVert i ≤ u := fun i =>
    hle _ ((Walk.mem_support_rotate_iff c u humem).1 (c'.getVert_mem_support i))
  have a1 := Walk.adj_snd hc'.not_nil
  have a2 := (Walk.adj_penultimate hc'.not_nil).symm
  have l1 : c'.snd < u := lt_of_le_of_ne (hle' 1) a1.ne.symm
  have l2 : c'.penultimate < u := lt_of_le_of_ne (hle' _) a2.ne.symm
  exact hc'.snd_ne_penultimate (h _ _ _ a1 a2 l1 l2)

namespace FPF

variable {m : ℕ}

/-- The word as a function on `ℕ`. -/
def wd (w : Fin m → Bool) (i : ℕ) : Bool := if h : i < m then w ⟨i, h⟩ else false

/-- The parent of a non-root vertex `x` of the caterpillar `cat m w`. -/
def par (m : ℕ) (w : Fin m → Bool) (x : ℕ) : ℕ :=
  if x < 2 * m then x - 1
  else if (x - 2 * m) % 3 = 0 then 2 * ((x - 2 * m) / 3)
  else if (x - 2 * m) % 3 = 2 then 2 * ((x - 2 * m) / 3) + 1
  else if wd w ((x - 2 * m) / 3) then 2 * ((x - 2 * m) / 3) else 2 * ((x - 2 * m) / 3) + 1

lemma par_spine {w : Fin m → Bool} {x : ℕ} (hx : x < 2 * m) : par m w x = x - 1 := by
  unfold par; simp only [hx, ↓reduceIte]

/-- The three leaves of block `i`. -/
lemma par_leaf {w : Fin m → Bool} {x : ℕ} (hx : 2 * m ≤ x) :
    let i := (x - 2 * m) / 3
    (x = 2 * m + 3 * i ∧ par m w x = 2 * i) ∨ (x = 2 * m + 3 * i + 2 ∧ par m w x = 2 * i + 1) ∨
      (x = 2 * m + 3 * i + 1 ∧ (wd w i = true ∧ par m w x = 2 * i ∨
        wd w i = false ∧ par m w x = 2 * i + 1)) := by
  intro i
  unfold par
  have hx' : ¬ x < 2 * m := by omega
  simp only [hx', ↓reduceIte]
  cases h : wd w i <;> simp only [i] at h ⊢ <;> split_ifs <;> simp_all <;> omega

lemma par_lt {w : Fin m → Bool} {x : ℕ} (hx0 : 0 < x) (hm : 1 ≤ m) : par m w x < x := by
  rcases lt_or_ge x (2 * m) with h | h
  · rw [par_spine h]; omega
  · rcases par_leaf (w := w) h with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, ⟨-, e⟩ | ⟨-, e⟩⟩ <;> omega

lemma par_lt_spine {w : Fin m → Bool} {x : ℕ} (hx : x < 5 * m) : par m w x < 2 * m := by
  rcases lt_or_ge x (2 * m) with h | h
  · rw [par_spine h]; omega
  · rcases par_leaf (w := w) h with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, ⟨-, e⟩ | ⟨-, e⟩⟩ <;> omega

/-- The caterpillar of the word `w`: spine `0, …, 2m-1`, leaves `2m, …, 5m-1`. -/
def cat (m : ℕ) (w : Fin m → Bool) : SimpleGraph (Fin (5 * m)) :=
  SimpleGraph.fromRel fun a b => 0 < (b : ℕ) ∧ (a : ℕ) = par m w b

lemma cat_adj {w : Fin m → Bool} {a b : Fin (5 * m)} :
    (cat m w).Adj a b ↔ (0 < (b : ℕ) ∧ (a : ℕ) = par m w b) ∨
      (0 < (a : ℕ) ∧ (b : ℕ) = par m w a) := by
  have hm : 1 ≤ m := by have := a.isLt; omega
  simp only [cat, fromRel_adj, ne_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun e => ?_, h⟩
    subst e
    rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> have := par_lt (w := w) h0 hm <;> omega

lemma cat_connected (w : Fin m → Bool) (hm : 1 ≤ m) : (cat m w).Connected := by
  have : Nonempty (Fin (5 * m)) := ⟨⟨0, by omega⟩⟩
  have key : ∀ x (hx : x < 5 * m), (cat m w).Reachable ⟨0, by omega⟩ ⟨x, hx⟩ := by
    intro x
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      intro hx
      rcases Nat.eq_zero_or_pos x with rfl | hx0
      · rfl
      have hlt := par_lt (w := w) hx0 hm
      refine (ih _ hlt (by omega)).trans (Adj.reachable ?_)
      rw [cat_adj]; exact Or.inl ⟨hx0, rfl⟩
  exact ⟨fun a b => (key a a.isLt).symm.trans (key b b.isLt)⟩

/-! ### The tree `cat w ⊛ cat w'` -/

section Tree

variable {p : ℕ} {w w' : Fin m → Bool}

/-- The graph `cat w ⊛ cat w'`. -/
abbrev TG (p m : ℕ) (w w' : Fin m → Bool) : SimpleGraph ℕ := graph p (5 * m) (cat m w) (cat m w')

/-- The parent of a node `x ≠ 1` of `cat w ⊛ cat w'` (rooted at the path node `1`). -/
def P (p m : ℕ) (w w' : Fin m → Bool) (x : ℕ) : ℕ :=
  if 2 ≤ x ∧ x ≤ p then x - 1
  else if x = p + 1 then 1
  else if x = p + 5 * m + 1 then p
  else if p + 1 < x ∧ x ≤ p + 5 * m then p + 1 + par m w (x - p - 1)
  else p + 5 * m + 1 + par m w' (x - p - 5 * m - 1)

/-- The non-root nodes. -/
def NR (p m x : ℕ) : Prop := 2 ≤ x ∧ x ≤ p + 2 * (5 * m)

lemma P_path {x : ℕ} (h1 : 2 ≤ x) (h2 : x ≤ p) : P p m w w' x = x - 1 := by
  unfold P; simp only [h1, h2, and_self, ↓reduceIte]

lemma P_root₁ : P p m w w' (p + 1) = 1 := by
  unfold P; have : ¬ (2 ≤ p + 1 ∧ p + 1 ≤ p) := by omega
  simp only [this, ↓reduceIte]

lemma P_root₂ (hm : 1 ≤ m) : P p m w w' (p + 5 * m + 1) = p := by
  unfold P
  have h1 : ¬ (2 ≤ p + 5 * m + 1 ∧ p + 5 * m + 1 ≤ p) := by omega
  have h2 : ¬ (p + 5 * m + 1 = p + 1) := by omega
  simp only [h1, h2, ↓reduceIte]

lemma P_c₁ {x : ℕ} (h1 : p + 1 < x) (h2 : x ≤ p + 5 * m) :
    P p m w w' x = p + 1 + par m w (x - p - 1) := by
  unfold P
  have e1 : ¬ (2 ≤ x ∧ x ≤ p) := by omega
  have e2 : ¬ (x = p + 1) := by omega
  have e3 : ¬ (x = p + 5 * m + 1) := by omega
  simp only [e1, e2, e3, h1, h2, and_self, ↓reduceIte]

lemma P_c₂ {x : ℕ} (h1 : p + 5 * m + 1 < x) :
    P p m w w' x = p + 5 * m + 1 + par m w' (x - p - 5 * m - 1) := by
  unfold P
  have e1 : ¬ (2 ≤ x ∧ x ≤ p) := by omega
  have e2 : ¬ (x = p + 1) := by omega
  have e3 : ¬ (x = p + 5 * m + 1) := by omega
  have e4 : ¬ (p + 1 < x ∧ x ≤ p + 5 * m) := by omega
  simp only [e1, e2, e3, e4, ↓reduceIte]

/-- `P` on the nodes of `cat w ⊛ cat w'`, in one statement. -/
lemma P_spec (hm : 1 ≤ m) {x : ℕ} (hx : NR p m x) :
    (x ≤ p ∧ P p m w w' x = x - 1) ∨ (x = p + 1 ∧ P p m w w' x = 1) ∨
    (x = p + 5 * m + 1 ∧ P p m w w' x = p) ∨
    (p + 1 < x ∧ x ≤ p + 5 * m ∧ P p m w w' x = p + 1 + par m w (x - p - 1)) ∨
    (p + 5 * m + 1 < x ∧ P p m w w' x = p + 5 * m + 1 + par m w' (x - p - 5 * m - 1)) := by
  unfold NR at hx
  by_cases h1 : x ≤ p
  · exact Or.inl ⟨h1, P_path hx.1 h1⟩
  by_cases h2 : x = p + 1
  · subst h2; exact Or.inr (Or.inl ⟨rfl, P_root₁⟩)
  by_cases h3 : x = p + 5 * m + 1
  · subst h3; exact Or.inr (Or.inr (Or.inl ⟨rfl, P_root₂ hm⟩))
  by_cases h4 : x ≤ p + 5 * m
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, h4, P_c₁ (by omega) h4⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, P_c₂ (by omega)⟩)))

lemma P_lt (hp : 1 ≤ p) (hm : 1 ≤ m) {x : ℕ} (hx : NR p m x) : P p m w w' x < x := by
  have := P_spec (w := w) (w' := w') hm hx
  unfold NR at hx
  rcases this with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, e⟩
  · omega
  · omega
  · omega
  · have := par_lt (w := w) (x := x - p - 1) (by omega) hm; omega
  · have := par_lt (w := w') (x := x - p - 5 * m - 1) (by omega) hm; omega

/-- **Adjacency in `cat w ⊛ cat w'`** is the parent relation. -/
lemma adj_iff (hp : 2 ≤ p) (hm : 1 ≤ m) {x y : ℕ} :
    (TG p m w w').Adj x y ↔ (NR p m y ∧ x = P p m w w' y) ∨ (NR p m x ∧ y = P p m w w' x) := by
  have hp1 : 1 ≤ p := by omega
  -- one direction for an "upward" edge, used twice
  have up : ∀ x y, (TG p m w w').Adj x y → (NR p m y ∧ x = P p m w w' y) ∨
      (NR p m x ∧ y = P p m w w' x) := by
    intro x y h
    rw [graph_adj] at h
    unfold pathRel at h
    rcases h with h | h | h
    · rcases h with ⟨h1, h2, rfl⟩ | ⟨rfl, -, -, rfl⟩ | ⟨rfl, -, -, rfl⟩
      · left; exact ⟨⟨by omega, by omega⟩, by rw [P_path (by omega) (by omega)]; omega⟩
      · left; exact ⟨⟨by omega, by omega⟩, (P_root₁).symm⟩
      · left; exact ⟨⟨by omega, by omega⟩, (P_root₂ hm).symm⟩
    · rcases h with ⟨h1, h2, rfl⟩ | ⟨rfl, -, -, rfl⟩ | ⟨rfl, -, -, rfl⟩
      · right; exact ⟨⟨by omega, by omega⟩, by rw [P_path (by omega) (by omega)]; omega⟩
      · right; exact ⟨⟨by omega, by omega⟩, (P_root₁).symm⟩
      · right; exact ⟨⟨by omega, by omega⟩, (P_root₂ hm).symm⟩
    · rcases h with ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
      · have := a.isLt; have := b.isLt
        rw [cat_adj] at hab
        rcases hab with ⟨h0, e⟩ | ⟨h0, e⟩
        · left; refine ⟨⟨by omega, by omega⟩, ?_⟩
          rw [P_c₁ (by omega) (by omega), show p + 1 + (b : ℕ) - p - 1 = b by omega]; omega
        · right; refine ⟨⟨by omega, by omega⟩, ?_⟩
          rw [P_c₁ (by omega) (by omega), show p + 1 + (a : ℕ) - p - 1 = a by omega]; omega
      · have := a.isLt; have := b.isLt
        rw [cat_adj] at hab
        rcases hab with ⟨h0, e⟩ | ⟨h0, e⟩
        · left; refine ⟨⟨by omega, by omega⟩, ?_⟩
          rw [P_c₂ (by omega), show p + 5 * m + 1 + (b : ℕ) - p - 5 * m - 1 = b by omega]; omega
        · right; refine ⟨⟨by omega, by omega⟩, ?_⟩
          rw [P_c₂ (by omega), show p + 5 * m + 1 + (a : ℕ) - p - 5 * m - 1 = a by omega]; omega
  -- converse: a node is adjacent to its parent
  have down : ∀ y, NR p m y → (TG p m w w').Adj (P p m w w' y) y := by
    intro y hy
    have hy' := hy
    unfold NR at hy'
    rcases P_spec (w := w) (w' := w') hm hy with ⟨h1, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ |
      ⟨h1, h2, e⟩ | ⟨h1, e⟩ <;> rw [e, graph_adj]
    · left; left; refine ⟨by omega, by omega, by omega⟩
    · left; right; left; exact ⟨rfl, hp1, by omega, rfl⟩
    · left; right; right; exact ⟨rfl, hp1, by omega, rfl⟩
    · right; right; left
      have := par_lt_spine (w := w) (x := y - p - 1) (by omega)
      refine ⟨⟨par m w (y - p - 1), by omega⟩, ⟨y - p - 1, by omega⟩, ?_, rfl, by simp; omega⟩
      rw [cat_adj]; left; exact ⟨by simp; omega, rfl⟩
    · right; right; right
      have := par_lt_spine (w := w') (x := y - p - 5 * m - 1) (by omega)
      refine ⟨⟨par m w' (y - p - 5 * m - 1), by omega⟩, ⟨y - p - 5 * m - 1, by omega⟩, ?_, rfl,
        by simp; omega⟩
      rw [cat_adj]; left; exact ⟨by simp; omega, rfl⟩
  constructor
  · exact up x y
  · rintro (⟨hy, rfl⟩ | ⟨hx, rfl⟩)
    · exact down y hy
    · exact (down x hx).symm

lemma tree_acyclic (hp : 2 ≤ p) (hm : 1 ≤ m) : (TG p m w w').IsAcyclic := by
  refine isAcyclic_of_unique_lt_adj _ fun x y z hy hz hyx hzx => ?_
  have key : ∀ y, (TG p m w w').Adj x y → y < x → y = P p m w w' x := by
    intro y h hyx
    rcases (adj_iff hp hm).1 h with ⟨hy', rfl⟩ | ⟨_, rfl⟩
    · have := P_lt (w := w) (w' := w') (by omega) hm hy'; omega
    · rfl
  rw [key y hy hyx, key z hz hzx]

/-- `cat w ⊛ cat w'` is a tree on `{1, …, p + 10m}`. -/
lemma star_tree (hp : 2 ≤ p) (hm : 1 ≤ m) :
    (star p (5 * m) (cat m w) (cat m w')).Conn ∧
      (star p (5 * m) (cat m w) (cat m w')).G.IsAcyclic :=
  ⟨star_conn (by omega) (by omega) (cat_connected w hm) (cat_connected w' hm),
    tree_acyclic hp hm⟩

/-- `x` is a leaf: a node with exactly one neighbour. -/
def IsLeaf {L : Type*} (I : Inst L) (x : ℕ) : Prop := x ∈ I.V ∧ ∃ y, ∀ z, I.G.Adj x z ↔ z = y

lemma isLeaf_of_isAut {L : Type*} {I : Inst L} {ψ : Equiv.Perm ℕ} (h : IsAut I ψ) {x : ℕ}
    (hx : IsLeaf I x) : IsLeaf I (ψ x) := by
  obtain ⟨hxV, y, hy⟩ := hx
  refine ⟨(h.mem x).2 hxV, ψ y, fun z => ?_⟩
  rw [← Equiv.apply_symm_apply ψ z, h.adj, hy]
  exact ψ.injective.eq_iff.symm

lemma isLeaf_isAut_iff {L : Type*} {I : Inst L} {ψ : Equiv.Perm ℕ} (h : IsAut I ψ) {x : ℕ} :
    IsLeaf I (ψ x) ↔ IsLeaf I x :=
  ⟨fun hx => by simpa using isLeaf_of_isAut h.symm hx, isLeaf_of_isAut h⟩

/-- The leaves of the two caterpillars. -/
def LeafNode (p m x : ℕ) : Prop :=
  (p + 1 + 2 * m ≤ x ∧ x ≤ p + 5 * m) ∨ (p + 5 * m + 1 + 2 * m ≤ x ∧ x ≤ p + 2 * (5 * m))

lemma not_leafNode_P (hm : 1 ≤ m) {y : ℕ} (hy : NR p m y) : ¬ LeafNode p m (P p m w w' y) := by
  have hy' := hy
  unfold NR at hy'
  unfold LeafNode
  rcases P_spec (w := w) (w' := w') hm hy with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, e⟩
  · omega
  · omega
  · omega
  · have := par_lt_spine (w := w) (x := y - p - 1) (by omega); omega
  · have := par_lt_spine (w := w') (x := y - p - 5 * m - 1) (by omega); omega

/-- A child of a non-leaf node. -/
def ch (p m x : ℕ) : ℕ :=
  if x < p then x + 1 else if x = p then p + 5 * m + 1
  else if x ≤ p + 5 * m then p + 1 + (2 * m + 3 * ((x - p - 1) / 2) + 2 * ((x - p - 1) % 2))
  else p + 5 * m + 1 + (2 * m + 3 * ((x - p - 5 * m - 1) / 2) + 2 * ((x - p - 5 * m - 1) % 2))

/-- The leaf `2m + 3 (j/2) + 2 (j % 2)` is a child of the spine node `j`. -/
lemma par_ch {w : Fin m → Bool} {j : ℕ} :
    par m w (2 * m + 3 * (j / 2) + 2 * (j % 2)) = j := by
  rcases par_leaf (w := w) (x := 2 * m + 3 * (j / 2) + 2 * (j % 2)) (by omega) with
    ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨h1, -⟩ <;> omega

lemma adj_ch (hp : 2 ≤ p) (hm : 1 ≤ m) {x : ℕ} (hx1 : 1 ≤ x) (hx : x ≤ p + 2 * (5 * m))
    (hl : ¬ LeafNode p m x) : (TG p m w w').Adj x (ch p m x) := by
  unfold LeafNode at hl
  rw [adj_iff hp hm]
  left
  unfold ch
  split_ifs with h1 h2 h3
  · exact ⟨⟨by omega, by omega⟩, by rw [P_path (by omega) (by omega)]; omega⟩
  · subst h2; exact ⟨⟨by omega, by omega⟩, (P_root₂ hm).symm⟩
  · refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [P_c₁ (by omega) (by omega)]
    rw [show p + 1 + (2 * m + 3 * ((x - p - 1) / 2) + 2 * ((x - p - 1) % 2)) - p - 1 =
      2 * m + 3 * ((x - p - 1) / 2) + 2 * ((x - p - 1) % 2) by omega, par_ch]
    omega
  · refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [P_c₂ (by omega)]
    rw [show p + 5 * m + 1 + (2 * m + 3 * ((x - p - 5 * m - 1) / 2) + 2 * ((x - p - 5 * m - 1) % 2))
      - p - 5 * m - 1 = 2 * m + 3 * ((x - p - 5 * m - 1) / 2) + 2 * ((x - p - 5 * m - 1) % 2) by
      omega, par_ch]
    omega

/-- **Leaves of `cat w ⊛ cat w'`** are exactly the leaves of the two caterpillars. -/
lemma isLeaf_iff (hp : 2 ≤ p) (hm : 1 ≤ m) {x : ℕ}
    (hx : x ∈ (star p (5 * m) (cat m w) (cat m w')).V) :
    IsLeaf (star p (5 * m) (cat m w) (cat m w')) x ↔ LeafNode p m x := by
  simp only [star_V, mem_Icc] at hx
  constructor
  · rintro ⟨-, y, hy⟩
    by_contra hl
    have a1 := (hy _).1 (adj_ch hp hm hx.1 hx.2 hl)
    have a2 : (TG p m w w').Adj x (if x = 1 then p + 1 else P p m w w' x) := by
      rw [adj_iff hp hm]
      split_ifs with h
      · subst h; left; exact ⟨⟨by omega, by omega⟩, P_root₁.symm⟩
      · right; exact ⟨⟨by omega, hx.2⟩, rfl⟩
    have a2 := (hy _).1 a2
    have hlt : x < ch p m x := by
      unfold LeafNode at hl; unfold ch; split_ifs <;> omega
    rw [← a2] at a1
    split_ifs at a1 with h
    · subst h; unfold ch at a1; split_ifs at a1 <;> omega
    · have : P p m w w' x < x := P_lt (by omega) hm ⟨by omega, hx.2⟩
      omega
  · intro hl
    refine ⟨by simp; omega, P p m w w' x, fun z => ?_⟩
    have hNR : NR p m x := by unfold LeafNode at hl; unfold NR; omega
    show (TG p m w w').Adj x z ↔ _
    rw [adj_iff hp hm]
    constructor
    · rintro (⟨hz, rfl⟩ | ⟨-, rfl⟩)
      · exact absurd hl (not_leafNode_P hm hz)
      · rfl
    · rintro rfl; exact Or.inr ⟨hNR, rfl⟩

/-- `x` has two distinct leaf neighbours. -/
def TwoLeaves {L : Type*} (I : Inst L) (x : ℕ) : Prop :=
  ∃ y₁ y₂, y₁ ≠ y₂ ∧ IsLeaf I y₁ ∧ IsLeaf I y₂ ∧ I.G.Adj x y₁ ∧ I.G.Adj x y₂

lemma twoLeaves_of_isAut {L : Type*} {I : Inst L} {ψ : Equiv.Perm ℕ} (h : IsAut I ψ) {x : ℕ}
    (hx : TwoLeaves I x) : TwoLeaves I (ψ x) := by
  obtain ⟨y₁, y₂, hne, l1, l2, a1, a2⟩ := hx
  exact ⟨ψ y₁, ψ y₂, ψ.injective.ne hne, isLeaf_of_isAut h l1, isLeaf_of_isAut h l2,
    (h.adj _ _).2 a1, (h.adj _ _).2 a2⟩

/-! ### Spine nodes with two leaves -/

/-- The offset of copy `b`. -/
def offB (p m : ℕ) (b : Bool) : ℕ := if b then p + 5 * m + 1 else p + 1

/-- The word of copy `b`. -/
def wB (w w' : Fin m → Bool) (b : Bool) : Fin m → Bool := if b then w' else w

lemma P_copy (b : Bool) {y : ℕ} (h1 : offB p m b < y) (h2 : y < offB p m b + 5 * m) :
    P p m w w' y = offB p m b + par m (wB w w' b) (y - offB p m b) := by
  cases b <;> simp only [offB, wB, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
  · rw [P_c₁ h1 (by omega)]; congr 2
  · rw [P_c₂ h1]; congr 2; omega

lemma leaf_parent {y : ℕ} (hy : LeafNode p m y) :
    ∃ b, offB p m b + 2 * m ≤ y ∧ y < offB p m b + 5 * m ∧
      P p m w w' y = offB p m b + par m (wB w w' b) (y - offB p m b) := by
  unfold LeafNode at hy
  rcases hy with hy | hy
  · exact ⟨false, by simp [offB]; omega, by simp [offB]; omega,
      P_copy false (by simp [offB]; omega) (by simp [offB]; omega)⟩
  · exact ⟨true, by simp [offB]; omega, by simp [offB]; omega,
      P_copy true (by simp [offB]; omega) (by simp [offB]; omega)⟩

lemma par_eq_even {u : Fin m → Bool} {t i : ℕ} (ht : 2 * m ≤ t) (h : par m u t = 2 * i) :
    t = 2 * m + 3 * i ∨ (t = 2 * m + 3 * i + 1 ∧ wd u i = true) := by
  rcases par_leaf (w := u) ht with ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨h1, ⟨hw, e⟩ | ⟨hw, e⟩⟩
  · left; omega
  · omega
  · have : (t - 2 * m) / 3 = i := by omega
    rw [this] at hw
    right; exact ⟨by omega, hw⟩
  · omega

lemma par_at₀ {u : Fin m → Bool} (i : ℕ) : par m u (2 * m + 3 * i) = 2 * i := by
  rcases par_leaf (w := u) (x := 2 * m + 3 * i) (by omega) with
    ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨h1, -⟩ <;> omega

lemma par_at₁ {u : Fin m → Bool} {i : ℕ} (hw : wd u i = true) :
    par m u (2 * m + 3 * i + 1) = 2 * i := by
  rcases par_leaf (w := u) (x := 2 * m + 3 * i + 1) (by omega) with
    ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨h1, ⟨-, e⟩ | ⟨hw', e⟩⟩
  · omega
  · omega
  · omega
  · have : (2 * m + 3 * i + 1 - 2 * m) / 3 = i := by omega
    rw [this, hw] at hw'; exact absurd hw' (by simp)

/-- The spine node `2i` of copy `b` has two leaves iff the `i`-th letter of its word is `1`. -/
lemma twoLeaves_iff (hp : 2 ≤ p) (hm : 1 ≤ m) (b : Bool) {i : ℕ} (hi : i < m) :
    TwoLeaves (star p (5 * m) (cat m w) (cat m w')) (offB p m b + 2 * i) ↔
      wd (wB w w' b) i = true := by
  have hoff : offB p m b = p + 1 ∨ offB p m b = p + 5 * m + 1 := by
    cases b <;> simp [offB]
  constructor
  · rintro ⟨y₁, y₂, hne, l1, l2, a1, a2⟩
    -- every leaf neighbour `y` has offset `2m + 3i` or (if the letter is 1) `2m + 3i + 1`
    have key : ∀ y, IsLeaf (star p (5 * m) (cat m w) (cat m w')) y →
        (star p (5 * m) (cat m w) (cat m w')).G.Adj (offB p m b + 2 * i) y →
        y = offB p m b + (2 * m + 3 * i) ∨
          (y = offB p m b + (2 * m + 3 * i + 1) ∧ wd (wB w w' b) i = true) := by
      intro y ly ay
      have hy := (isLeaf_iff hp hm ly.1).1 ly
      change (TG p m w w').Adj _ y at ay
      rw [adj_iff hp hm] at ay
      rcases ay with ⟨hNR, e⟩ | ⟨hNR, e⟩
      · obtain ⟨b', h1, h2, e'⟩ := leaf_parent (w := w) (w' := w') hy
        rw [e'] at e
        have hpar := par_lt_spine (w := wB w w' b') (x := y - offB p m b') (by omega)
        have hb : b' = b := by
          cases b <;> cases b' <;>
            simp only [offB, Bool.false_eq_true, ↓reduceIte] at e h1 h2 hpar ⊢ <;> omega
        subst hb
        rcases par_eq_even (u := wB w w' b') (t := y - offB p m b') (i := i) (by omega)
          (by omega) with h | ⟨h, hw⟩
        · left; omega
        · right; exact ⟨by omega, hw⟩
      · exact absurd hy (e ▸ not_leafNode_P hm hNR)
    rcases key y₁ l1 a1 with h1 | h1 <;> rcases key y₂ l2 a2 with h2 | h2
    · omega
    · exact h2.2
    · exact h1.2
    · exact h1.2
  · intro hw
    have hleaf : ∀ t, 2 * m ≤ t → t < 5 * m →
        IsLeaf (star p (5 * m) (cat m w) (cat m w')) (offB p m b + t) := by
      intro t h1 h2
      have hV : offB p m b + t ∈ (star p (5 * m) (cat m w) (cat m w')).V := by
        simp only [star_V, mem_Icc]; omega
      rw [isLeaf_iff hp hm hV]
      unfold LeafNode; omega
    have hadj : ∀ t, 2 * m ≤ t → t < 5 * m → par m (wB w w' b) t = 2 * i →
        (star p (5 * m) (cat m w) (cat m w')).G.Adj (offB p m b + 2 * i) (offB p m b + t) := by
      intro t h1 h2 e
      change (TG p m w w').Adj _ _
      rw [adj_iff hp hm]
      left
      refine ⟨by unfold NR; omega, ?_⟩
      rw [P_copy b (by omega) (by omega), Nat.add_sub_cancel_left, e]
    refine ⟨_, _, ?_, hleaf (2 * m + 3 * i) (by omega) (by omega),
      hleaf (2 * m + 3 * i + 1) (by omega) (by omega),
      hadj _ (by omega) (by omega) (par_at₀ i), hadj _ (by omega) (by omega) (par_at₁ hw)⟩
    omega

/-! ### The long path of non-leaf nodes -/

/-- The non-leaf nodes in path order: the spine of the first copy (from its far end), the path
`1, …, p`, the spine of the second copy. -/
def e (p m i : ℕ) : ℕ :=
  if i < 2 * m then p + 1 + (2 * m - 1 - i) else if i < 2 * m + p then i - 2 * m + 1
  else p + 5 * m + 1 + (i - 2 * m - p)

lemma e_NR (hp : 2 ≤ p) (hm : 1 ≤ m) {i : ℕ} (hi : i ≤ 4 * m + p - 1) (h2 : i ≠ 2 * m) :
    NR p m (e p m i) := by
  unfold NR e; split_ifs <;> omega

lemma P_e (hp : 2 ≤ p) (hm : 1 ≤ m) {i : ℕ} (hi : i ≤ 4 * m + p - 1) (h2 : i ≠ 2 * m) :
    P p m w w' (e p m i) = e p m (if i < 2 * m then i + 1 else i - 1) := by
  by_cases h1 : i + 1 < 2 * m
  · have : e p m i = p + 1 + (2 * m - 1 - i) := by unfold e; split_ifs <;> omega
    rw [this, P_c₁ (by omega) (by omega), show p + 1 + (2 * m - 1 - i) - p - 1 = 2 * m - 1 - i by
      omega, par_spine (by omega), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    unfold e; split_ifs; omega
  by_cases h1' : i + 1 = 2 * m
  · have : e p m i = p + 1 := by unfold e; split_ifs <;> omega
    rw [this, P_root₁, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    unfold e; split_ifs <;> omega
  by_cases h3 : i < 2 * m + p
  · have : e p m i = i - 2 * m + 1 := by unfold e; split_ifs <;> omega
    rw [this, P_path (by omega) (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    unfold e; split_ifs <;> omega
  by_cases h4 : i = 2 * m + p
  · have : e p m i = p + 5 * m + 1 := by unfold e; split_ifs <;> omega
    rw [this, P_root₂ hm, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    unfold e; split_ifs <;> omega
  · have : e p m i = p + 5 * m + 1 + (i - 2 * m - p) := by unfold e; split_ifs <;> omega
    rw [this, P_c₂ (by omega), show p + 5 * m + 1 + (i - 2 * m - p) - p - 5 * m - 1 =
      i - 2 * m - p by omega, par_spine (by omega),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    unfold e; split_ifs <;> omega

lemma e_inj {i j : ℕ} (h : e p m i = e p m j) :
    i = j := by
  unfold e at h; split_ifs at h <;> omega

lemma pathEnum (hp : 2 ≤ p) (hm : 1 ≤ m) :
    PathEnum (star p (5 * m) (cat m w) (cat m w')).G
      (fun x => x ∈ (star p (5 * m) (cat m w) (cat m w')).V ∧
        ¬ IsLeaf (star p (5 * m) (cat m w) (cat m w')) x) (4 * m + p - 1) (e p m) where
  mem v := by
    constructor
    · rintro ⟨hv, hl⟩
      rw [isLeaf_iff hp hm hv] at hl
      simp only [star_V, mem_Icc] at hv
      unfold LeafNode at hl
      refine ⟨if v ≤ p then v + 2 * m - 1 else if v ≤ p + 5 * m then 2 * m - 1 - (v - p - 1)
        else v - 3 * m - 1, ?_, ?_⟩
      · split_ifs <;> omega
      · unfold e; split_ifs <;> omega
    · rintro ⟨i, hi, rfl⟩
      have hV : e p m i ∈ (star p (5 * m) (cat m w) (cat m w')).V := by
        simp only [star_V, mem_Icc]; unfold e; split_ifs <;> omega
      refine ⟨hV, fun hl => ?_⟩
      rw [isLeaf_iff hp hm hV] at hl
      unfold LeafNode e at hl; split_ifs at hl <;> omega
  inj i hi j hj h := e_inj h
  adj i hi j hj := by
    change (TG p m w w').Adj _ _ ↔ _
    rw [adj_iff hp hm]
    have hNR : ∀ l ≤ 4 * m + p - 1, NR p m (e p m l) ↔ l ≠ 2 * m := by
      intro l hl
      refine ⟨fun h e2 => ?_, e_NR hp hm hl⟩
      subst e2; unfold NR e at h; split_ifs at h <;> omega
    rw [hNR i hi, hNR j hj]
    constructor
    · rintro (⟨h2, h⟩ | ⟨h2, h⟩)
      · rw [P_e hp hm hj h2] at h
        have := e_inj h
        split_ifs at this <;> omega
      · rw [P_e hp hm hi h2] at h
        have := e_inj h
        split_ifs at this <;> omega
    · rintro (h | h)
      · by_cases hij : i < 2 * m
        · right
          refine ⟨by omega, ?_⟩
          rw [P_e hp hm hi (by omega), ite_eq_left_of_eq_true _ _ (eq_true hij), h]
        · left
          refine ⟨by omega, ?_⟩
          rw [P_e hp hm hj (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          congr 1; omega
      · by_cases hj2 : j < 2 * m
        · left
          refine ⟨by omega, ?_⟩
          rw [P_e hp hm hj (by omega), ite_eq_left_of_eq_true _ _ (eq_true hj2), h]
        · right
          refine ⟨by omega, ?_⟩
          rw [P_e hp hm hi (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          congr 1; omega

/-! ### Fixed-point-free automorphisms of `cat w ⊛ cat w'` -/

/-- An automorphism of `cat w ⊛ cat w'` without fixed points forces `w = w'`. -/
theorem eq_of_fpf (hp : 2 ≤ p) (hm : 1 ≤ m) {ψ : Equiv.Perm ℕ}
    (hψ : IsAut (star p (5 * m) (cat m w) (cat m w')) ψ)
    (hfpf : ∀ v ∈ (star p (5 * m) (cat m w) (cat m w')).V, ψ v ≠ v) : w = w' := by
  set I := star p (5 * m) (cat m w) (cat m w')
  have hPE := pathEnum (w := w) (w' := w') hp hm
  have hQ : ∀ x, (ψ x ∈ I.V ∧ ¬ IsLeaf I (ψ x)) ↔ (x ∈ I.V ∧ ¬ IsLeaf I x) := by
    intro x; rw [hψ.mem, isLeaf_isAut_iff hψ]
  have he0 : e p m 0 ∈ I.V := ((hPE.mem _).2 ⟨0, by omega, rfl⟩).1
  rcases hPE.end_cases hψ.adj hQ with h0 | h0
  · exact absurd h0 (hfpf _ he0)
  have hrev := hPE.rigid hPE.rev hψ.adj hQ (by simpa using h0)
  -- the spine node `2i` of the first copy is mapped to the spine node `2i` of the second copy
  have hmap : ∀ i < m, ψ (offB p m false + 2 * i) = offB p m true + 2 * i := by
    intro i hi
    have := hrev (2 * m - 1 - 2 * i) (by omega)
    have e1 : e p m (2 * m - 1 - 2 * i) = offB p m false + 2 * i := by
      simp only [e, offB, Bool.false_eq_true, ↓reduceIte]; split_ifs <;> omega
    have e2 : e p m (4 * m + p - 1 - (2 * m - 1 - 2 * i)) = offB p m true + 2 * i := by
      simp only [e, offB, ↓reduceIte]; split_ifs <;> omega
    rw [e1, e2] at this
    exact this
  funext ⟨i, hi⟩
  have h1 := twoLeaves_iff (w := w) (w' := w') hp hm false hi
  have h2 := twoLeaves_iff (w := w) (w' := w') hp hm true hi
  simp only [wB, Bool.false_eq_true, ↓reduceIte, wd, hi, dite_true] at h1 h2
  have key : TwoLeaves I (offB p m false + 2 * i) ↔ TwoLeaves I (offB p m true + 2 * i) := by
    rw [← hmap i hi]
    refine ⟨twoLeaves_of_isAut hψ, fun h => ?_⟩
    simpa using twoLeaves_of_isAut hψ.symm h
  rw [h1, h2] at key
  cases hw : w ⟨i, hi⟩ <;> cases hw' : w' ⟨i, hi⟩ <;> simp_all

/-- For even `p`, the swap of `H ⊛ H` has no fixed point. -/
lemma swap_fpf {k : ℕ} (hk : 0 < k) (hp : Even p) (H : SimpleGraph (Fin k)) :
    ∀ v ∈ (star p k H H).V, swap p k v ≠ v := by
  intro v hv
  obtain ⟨t, rfl⟩ := hp
  simp only [star_V, mem_Icc] at hv
  rw [swap_apply]
  rcases swapFun_spec (p := t + t) (k := k) v with h | h | h | h <;> omega

end Tree

end FPF

open FPF

/-- **Theorem 6.3** of [GS16] (lower bound): trees with a fixed-point-free symmetry require locally
checkable proofs of size `Ω(n)`. Here `F` is any family containing all unlabelled trees
(connected and acyclic) with identifiers in `{1, …, n}`, and the bound holds for all large even `n`
(trees with an odd number of nodes never have a fixed-point-free automorphism, so no proofs are
needed for them). The constant depends on the local horizon `r` (`c = 1/(32 (2r+1))`). -/
theorem fpf_tree_lcp_lower_bound (F : Set (Inst Unit))
    (hF : ∀ I : Inst Unit, I.Plain → I.Conn → I.G.IsAcyclic → I.IdBound 1 → I ∈ F) {s : ℕ → ℕ}
    (h : AdmitsLCP F {I | HasFPFSym I} s) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → c * n ≤ s n := by
  classical
  obtain ⟨r, A, hA, hc, hs⟩ := h
  refine ⟨1 / (32 * (2 * r + 1)), by positivity, 15 * (2 * r + 20), fun n hn hev => ?_⟩
  set m := n / 15 with hmdef
  set p := n - 10 * m with hpdef
  have hm : 2 * r + 20 ≤ m := by omega
  have hp5 : 5 * m ≤ p := by omega
  have hn' : p + 2 * (5 * m) = n := by omega
  have hpev : Even p := by
    obtain ⟨t, ht⟩ := hev; exact ⟨t - 5 * m, by omega⟩
  have hmem : ∀ v v' : Fin m → Bool, star p (5 * m) (cat m v) (cat m v') ∈ F := fun v v' =>
    hF _ star_plain (star_tree (by omega) (by omega)).1 (star_tree (by omega) (by omega)).2
      star_idBound
  have key := card_le_of_glue (p := p) (univ : Finset (Fin m → Bool)) (cat m) (· ≠ ·) 1 ?_ hA
    (by omega) (s n) ?_ ?_
  rotate_left
  · intro i _
    refine (card_le_card (fun j hj => ?_)).trans (card_singleton i).le
    simp only [mem_filter, ne_eq, not_not] at hj
    simp [hj.2]
  · intro i _
    have hsym : HasFPFSym (star p (5 * m) (cat m i) (cat m i)) := by
      obtain ⟨φ, hφ⟩ := exists_iso_of_perm (swap_isAut (p := p) (cat m i))
      exact ⟨φ, fun v e => swap_fpf (by omega) hpev _ v v.2 (by rw [← hφ, e])⟩
    obtain ⟨P, hP, hacc⟩ := hc _ (hmem i i) hsym
    rw [star_n, hn'] at hP
    exact ⟨P, hP, hacc⟩
  · intro i _ j _ hij P
    refine hs _ (hmem i j) (fun hsym => hij ?_) P
    obtain ⟨φ, hφ⟩ := hsym
    obtain ⟨ψ, hψ, hψφ⟩ := exists_perm_of_iso _ φ
    exact eq_of_fpf (by omega) (by omega) hψ fun v hv e => hφ ⟨v, hv⟩ (Subtype.ext (by
      rw [← hψφ]; exact e))
  -- arithmetic
  simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, one_mul] at key
  have h1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 key
  have hs1 : 1 ≤ s n := by
    by_contra h0
    have : s n = 0 := by omega
    rw [this] at h1
    omega
  have hn16 : n ≤ 16 * m := by omega
  have h3 : (s n + 1) * (2 * r + 1) ≤ 2 * s n * (2 * r + 1) := by nlinarith
  have h2 : n ≤ 32 * (2 * r + 1) * s n := by nlinarith
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  have : ((n : ℕ) : ℝ) ≤ ((32 * (2 * r + 1) * s n : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at this
  linarith

end Podc.LocallyCheckableProofs
