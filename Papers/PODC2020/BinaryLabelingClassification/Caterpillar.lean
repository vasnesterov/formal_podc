import Papers.PODC2020.BinaryLabelingClassification.Transport
import Podc.Foundations.Combinatorics.SimpleGraph.ParentGraph

/-!
# The caterpillar instances of §8 and their mirrored versions

The lower bounds of Theorems 8.1 and 8.2 use a long "caterpillar" tree: a spine
`w₀ – b₀ – w₁ – b₁ – ⋯ – w_M – b_M` of alternating white (`w_k`) and black (`b_k`) nodes, where
every white spine node has `a` black leaves ("hairs") and every black spine node has `b` white
hairs, so that the inner spine nodes have degrees `d = a + 2` and `δ = b + 2`. The remaining
`r` nodes are white leaves attached to `b_M` (padding, so that every number of nodes can be
realised).

The *mirror* `mirror p q` reverses the part `w_p – b_p – ⋯ – w_q` of the spine (with the hairs).
Relabelling the caterpillar along the mirror gives another tree (an isomorphic copy) which agrees
with the caterpillar at every node except the four boundary nodes `b_{p-1}, w_p, w_q, b_q`
(`adj_mirror`). Nodes far from the boundary therefore see the same view in both trees, while the
spine order is reversed inside the mirrored part.
-/

namespace Podc.BinaryLabeling.Caterpillar

open SimpleGraph

/-- The nodes: `(k, none)` / `(k, some j)` in the first summand are the white spine node `w_k` and
its black hairs, the second summand holds the black spine nodes `b_k` and their white hairs, the
third the `r` extra white leaves. -/
abbrev Node (M a b r : ℕ) := (Fin (M + 1) × Option (Fin a)) ⊕ (Fin (M + 1) × Option (Fin b)) ⊕ Fin r

variable {M a b r : ℕ}

/-- The white spine node `w_k`. -/
def wS (k : Fin (M + 1)) : Node M a b r := .inl (k, none)

/-- The black spine node `b_k`. -/
def bS (k : Fin (M + 1)) : Node M a b r := .inr (.inl (k, none))

/-- Parent pointers (root `w₀`). -/
def par : Node M a b r → Node M a b r
  | .inl (k, none) =>
    if h : k.val = 0 then .inl (k, none) else .inr (.inl (⟨k.val - 1, by omega⟩, none))
  | .inl (k, some _) => .inl (k, none)
  | .inr (.inl (k, none)) => .inl (k, none)
  | .inr (.inl (k, some _)) => .inr (.inl (k, none))
  | .inr (.inr _) => .inr (.inl (Fin.last M, none))

/-- A rank decreasing along parent pointers. -/
def rank : Node M a b r → ℕ
  | .inl (k, none) => 2 * k.val
  | .inl (k, some _) => 2 * k.val + 1
  | .inr (.inl (k, none)) => 2 * k.val + 1
  | .inr (.inl (k, some _)) => 2 * k.val + 2
  | .inr (.inr _) => 2 * M + 3

/-- The caterpillar. -/
def graph : SimpleGraph (Node M a b r) := parentGraph par

lemma isRootedMap : IsRootedMap (par (M := M) (a := a) (b := b) (r := r)) (.inl (0, none)) rank where
  map_root := by simp [par]
  rk_lt := by
    rintro (⟨k, _ | j⟩ | ⟨k, _ | j⟩ | i) hv
    · have : k.val ≠ 0 := fun h => hv (by simp [Fin.ext_iff, h])
      simp [par, this, rank]; omega
    · simp [par, rank]
    · simp [par, rank]
    · simp [par, rank]
    · simp [par, rank]

/-- The caterpillar is a tree. -/
theorem isTree : (graph : SimpleGraph (Node M a b r)).IsTree := isRootedMap.isTree

/-- Adjacency in arithmetic form. -/
def adjP : Node M a b r → Node M a b r → Prop
  | .inl (k, none), .inl (k', some _) => k = k'
  | .inl (k, some _), .inl (k', none) => k = k'
  | .inl (k, none), .inr (.inl (k', none)) => k'.val = k.val ∨ k'.val + 1 = k.val
  | .inr (.inl (k', none)), .inl (k, none) => k'.val = k.val ∨ k'.val + 1 = k.val
  | .inr (.inl (k, none)), .inr (.inl (k', some _)) => k = k'
  | .inr (.inl (k, some _)), .inr (.inl (k', none)) => k = k'
  | .inr (.inl (k, none)), .inr (.inr _) => k = Fin.last M
  | .inr (.inr _), .inr (.inl (k, none)) => k = Fin.last M
  | _, _ => False

lemma adj_iff {x y : Node M a b r} : graph.Adj x y ↔ adjP x y := by
  rw [graph, parentGraph_adj]
  rcases x with ⟨k, _ | j⟩ | ⟨k, _ | j⟩ | i <;> rcases y with ⟨k', _ | j'⟩ | ⟨k', _ | j'⟩ | i' <;>
    simp only [par, adjP] <;> (try split_ifs) <;> simp [Fin.ext_iff] <;> omega

/-- The 2-colouring (`true` = white). -/
def col : Node M a b r → Bool
  | .inl (_, none) => true
  | .inl (_, some _) => false
  | .inr (.inl (_, none)) => false
  | .inr (.inl (_, some _)) => true
  | .inr (.inr _) => true

lemma isProper : IsProper (graph : SimpleGraph (Node M a b r)) col := by
  intro x y h
  rw [adj_iff] at h
  rcases x with ⟨k, _ | j⟩ | ⟨k, _ | j⟩ | i <;> rcases y with ⟨k', _ | j'⟩ | ⟨k', _ | j'⟩ | i' <;>
    simp_all [adjP, col]

/-- The caterpillar with its colouring is an instance. -/
lemma isInstance : IsInstance (graph : SimpleGraph (Node M a b r)) col := ⟨isTree, isProper⟩

/-- The spine position (hairs get the position of their spine node). -/
def pos : Node M a b r → ℤ
  | .inl (k, _) => 2 * k.val
  | .inr (.inl (k, _)) => 2 * k.val + 1
  | .inr (.inr _) => 2 * M + 1

lemma pos_lipschitz {x y : Node M a b r} (h : graph.Adj x y) : |pos x - pos y| ≤ 1 := by
  rw [adj_iff] at h
  rcases x with ⟨k, _ | j⟩ | ⟨k, _ | j⟩ | i <;> rcases y with ⟨k', _ | j'⟩ | ⟨k', _ | j'⟩ | i' <;>
    simp_all [adjP, pos, abs_le, Fin.ext_iff] <;> omega

lemma natAbs_pos_le_edist (x y : Node M a b r) :
    ((pos x - pos y).natAbs : ℕ∞) ≤ graph.edist x y :=
  natAbs_le_edist pos (fun _ _ h => pos_lipschitz h) x y

/-! ### The mirror -/

/-- Reflection of the white indices `p ≤ k ≤ q`. -/
def rW (p q : ℕ) (k : Fin (M + 1)) : Fin (M + 1) :=
  if h : p ≤ k.val ∧ k.val ≤ q ∧ q ≤ M then ⟨p + q - k.val, by omega⟩ else k

/-- Reflection of the black indices `p ≤ k < q`. -/
def rB (p q : ℕ) (k : Fin (M + 1)) : Fin (M + 1) :=
  if h : p ≤ k.val ∧ k.val < q ∧ q ≤ M then ⟨p + q - 1 - k.val, by omega⟩ else k

lemma rW_spec (p q : ℕ) (k : Fin (M + 1)) :
    (p ≤ k.val ∧ k.val ≤ q ∧ q ≤ M ∧ (rW p q k).val = p + q - k.val) ∨
      (¬ (p ≤ k.val ∧ k.val ≤ q ∧ q ≤ M) ∧ (rW p q k).val = k.val) := by
  unfold rW; split_ifs with h
  · exact Or.inl ⟨h.1, h.2.1, h.2.2, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

lemma rB_spec (p q : ℕ) (k : Fin (M + 1)) :
    (p ≤ k.val ∧ k.val < q ∧ q ≤ M ∧ (rB p q k).val = p + q - 1 - k.val) ∨
      (¬ (p ≤ k.val ∧ k.val < q ∧ q ≤ M) ∧ (rB p q k).val = k.val) := by
  unfold rB; split_ifs with h
  · exact Or.inl ⟨h.1, h.2.1, h.2.2, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

/-- The mirror reversing the spine segment `w_p – ⋯ – w_q` (with its hairs). -/
def mirror (p q : ℕ) : Node M a b r → Node M a b r
  | .inl (k, o) => .inl (rW p q k, o)
  | .inr (.inl (k, o)) => .inr (.inl (rB p q k, o))
  | .inr (.inr i) => .inr (.inr i)

lemma mirror_mirror (p q : ℕ) (x : Node M a b r) : mirror p q (mirror p q x) = x := by
  rcases x with ⟨k, o⟩ | ⟨k, o⟩ | i
  · have h1 := rW_spec p q k
    have h2 := rW_spec p q (rW p q k)
    simp only [mirror, Sum.inl.injEq, Prod.mk.injEq, and_true, Fin.ext_iff]; omega
  · have h1 := rB_spec p q k
    have h2 := rB_spec p q (rB p q k)
    simp only [mirror, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true, Fin.ext_iff]; omega
  · rfl

/-- The mirror as a permutation. -/
def mirrorPerm (p q : ℕ) : Equiv.Perm (Node M a b r) :=
  Function.Involutive.toPerm _ (mirror_mirror p q)

@[simp] lemma mirrorPerm_apply (p q : ℕ) (x : Node M a b r) : mirrorPerm p q x = mirror p q x := rfl

lemma col_mirror (p q : ℕ) (x : Node M a b r) : col (mirror p q x) = col x := by
  rcases x with ⟨k, _ | j⟩ | ⟨k, _ | j⟩ | i <;> rfl

lemma pos_mirror_of_not (p q : ℕ) (x : Node M a b r) (h : pos x < 2 * p - 1 ∨ 2 * q + 1 < pos x) :
    mirror p q x = x := by
  rcases x with ⟨k, o⟩ | ⟨k, o⟩ | i
  · have h1 := rW_spec p q k
    simp only [pos] at h
    simp only [mirror, Sum.inl.injEq, Prod.mk.injEq, and_true, Fin.ext_iff]; omega
  · have h1 := rB_spec p q k
    simp only [pos] at h
    simp only [mirror, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true, Fin.ext_iff]; omega
  · rfl

/-- The four boundary nodes `b_{p-1}, w_p, w_q, b_q` of the mirrored segment. -/
def IsBoundary (p q : ℕ) : Node M a b r → Prop
  | .inl (k, none) => k.val = p ∨ k.val = q
  | .inr (.inl (k, none)) => k.val + 1 = p ∨ k.val = q
  | _ => False

lemma pos_of_isBoundary {p q : ℕ} {x : Node M a b r} (h : IsBoundary p q x) :
    pos x = 2 * p - 1 ∨ pos x = 2 * p ∨ pos x = 2 * q ∨ pos x = 2 * q + 1 := by
  rcases x with ⟨k, _ | j⟩ | ⟨k, _ | j⟩ | i <;> simp_all [IsBoundary, pos] <;> omega

/-- The mirror is an automorphism of the caterpillar at every non-boundary node. -/
lemma adj_mirror {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q ≤ M) {y : Node M a b r}
    (hy : ¬ IsBoundary p q y) (z : Node M a b r) :
    graph.Adj (mirror p q y) (mirror p q z) ↔ graph.Adj y z := by
  rw [adj_iff, adj_iff]
  rcases y with ⟨k, _ | j⟩ | ⟨k, _ | j⟩ | i <;> rcases z with ⟨k', _ | j'⟩ | ⟨k', _ | j'⟩ | i' <;>
    simp only [mirror, adjP, IsBoundary, Fin.ext_iff, Fin.val_last] at hy ⊢ <;>
    first
    | (have h1 := rW_spec p q k; have h2 := rW_spec p q k'; omega)
    | (have h1 := rW_spec p q k; have h2 := rB_spec p q k'; omega)
    | (have h1 := rB_spec p q k; have h2 := rW_spec p q k'; omega)
    | (have h1 := rB_spec p q k; have h2 := rB_spec p q k'; omega)
    | (have h1 := rB_spec p q k; omega)
    | (have h1 := rB_spec p q k'; omega)
    | skip

/-! ### Degrees of the spine nodes -/

lemma deg_wS {k : Fin (M + 1)} (hk : 1 ≤ k.val) : deg graph (wS k : Node M a b r) = a + 2 := by
  let g : Fin a ⊕ Fin 2 → Node M a b r := fun
    | .inl j => .inl (k, some j)
    | .inr i => .inr (.inl (⟨k.val - 1 + i.val, by omega⟩, none))
  have hg : Function.Injective g := by
    rintro (j | i) (j' | i') h <;> simp_all [g, Fin.ext_iff] <;> omega
  have : graph.neighborSet (wS k : Node M a b r) = Set.range g := by
    ext z
    simp only [mem_neighborSet, adj_iff, wS, Set.mem_range]
    rcases z with ⟨k', _ | j'⟩ | ⟨k', _ | j'⟩ | i'
    · simp [adjP, g]
    · simp only [adjP]
      constructor
      · rintro rfl; exact ⟨.inl j', rfl⟩
      · rintro ⟨_ | i, h⟩ <;> simp_all [g]
    · simp only [adjP]
      constructor
      · rintro (h | h)
        · exact ⟨.inr 1, by simp [g, Fin.ext_iff]; omega⟩
        · exact ⟨.inr 0, by simp [g, Fin.ext_iff]; omega⟩
      · rintro ⟨_ | i, h⟩
        · simp [g] at h
        · simp only [g, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true, Fin.ext_iff] at h
          have := i.isLt; omega
    · simp [adjP, g]
    · simp [adjP, g]
  rw [deg, this, Set.ncard_range_of_injective hg]
  simp

lemma deg_bS {k : Fin (M + 1)} (hk : k.val < M) : deg graph (bS k : Node M a b r) = b + 2 := by
  let g : Fin b ⊕ Fin 2 → Node M a b r := fun
    | .inl j => .inr (.inl (k, some j))
    | .inr i => .inl (⟨k.val + i.val, by omega⟩, none)
  have hg : Function.Injective g := by
    rintro (j | i) (j' | i') h <;> simp_all [g, Fin.ext_iff] <;> omega
  have : graph.neighborSet (bS k : Node M a b r) = Set.range g := by
    ext z
    simp only [mem_neighborSet, adj_iff, bS, Set.mem_range]
    rcases z with ⟨k', _ | j'⟩ | ⟨k', _ | j'⟩ | i'
    · simp only [adjP]
      constructor
      · rintro (h | h)
        · exact ⟨.inr 0, by simp [g, Fin.ext_iff]; omega⟩
        · exact ⟨.inr 1, by simp [g, Fin.ext_iff]; omega⟩
      · rintro ⟨_ | i, h⟩
        · simp [g] at h
        · simp only [g, Sum.inl.injEq, Prod.mk.injEq, and_true, Fin.ext_iff] at h
          have := i.isLt; omega
    · simp [adjP, g]
    · simp [adjP, g]
    · simp only [adjP]
      constructor
      · rintro rfl; exact ⟨.inl j', rfl⟩
      · rintro ⟨_ | i, h⟩ <;> simp_all [g]
    · simp only [adjP, g, Fin.ext_iff, Fin.val_last]
      constructor
      · intro h; omega
      · rintro ⟨_ | i, h⟩ <;> simp_all
  rw [deg, this, Set.ncard_range_of_injective hg]
  simp

lemma adj_wS_bS (k : Fin (M + 1)) : graph.Adj (wS k : Node M a b r) (bS k) := by
  rw [adj_iff]; simp [adjP, wS, bS]

lemma adj_bS_wS {k k' : Fin (M + 1)} (h : k'.val = k.val + 1) :
    graph.Adj (bS k : Node M a b r) (wS k') := by
  rw [adj_iff]; simp [adjP, wS, bS]; omega

end Podc.BinaryLabeling.Caterpillar
