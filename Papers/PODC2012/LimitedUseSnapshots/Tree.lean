import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Binary tree shapes for recursive max registers / max arrays

The `MaxReg_k` of Aspnes–Attiya–Censor-Hillel and the `MaxArray_{k×h}` of Algorithm 2 split the
range `{0, …, k-1}` of the first component recursively into `{0, …, m-1}` (left) and
`{m, …, k-1}` (right). We record the recursion as a binary tree `Shape` whose leaves are the values
(`m` = number of leaves of the left subtree). Nodes are addressed by paths `List Bool` from the root
(`false` = left, `true` = right).

* `Shape.size` — number of leaves (`k`), `Shape.subD t a` — the subtree at address `a`
  (`leaf` if `a` leaves the tree), `Shape.lo t a` — the offset of the subtree at `a` (the smallest
  value of its range), `Shape.addr t v` — the address of the leaf of value `v`.
* `Shape.balanced k` — the paper's balanced tree (`m = ⌈k/2⌉`).
* `LeftDom c σ` — every left step of the path `c` is at a node whose switch is off ("a traversal of
  `c` is consistent with switch states `≥ σ`"); `RightDom c σ` — every right step of `c` is at a node
  whose switch is on ("a traversal reading switches no later than `σ`"). The key comparison lemma
  `lo_le_lo_of_rightDom_leftDom`: a leaf reachable under `RightDom σ` is at most a leaf reachable
  under `LeftDom σ`.
-/

namespace Podc.LimitedUseSnapshots

/-- Binary tree shapes; the leaves stand for the values of a bounded max register. -/
inductive Shape where
  | leaf
  | node (l r : Shape)
  deriving DecidableEq

namespace Shape

/-- Number of leaves (the range `k`). -/
def size : Shape → ℕ
  | leaf => 1
  | node l r => l.size + r.size

lemma size_pos : ∀ t : Shape, 0 < t.size
  | leaf => Nat.one_pos
  | node l _ => Nat.add_pos_left (size_pos l) _

/-- The subtree at address `a` (`leaf` if `a` leaves the tree). -/
def subD : Shape → List Bool → Shape
  | t, [] => t
  | leaf, _ :: _ => leaf
  | node l _, false :: a => l.subD a
  | node _ r, true :: a => r.subD a

/-- Offset of the subtree at address `a`. -/
def lo : Shape → List Bool → ℕ
  | _, [] => 0
  | leaf, _ :: _ => 0
  | node l _, false :: a => l.lo a
  | node l r, true :: a => l.size + r.lo a

/-- `a` is the address of a node of the tree. -/
def IsAddr : Shape → List Bool → Prop
  | _, [] => True
  | leaf, _ :: _ => False
  | node l _, false :: a => l.IsAddr a
  | node _ r, true :: a => r.IsAddr a

/-- The address of the leaf with value `v`. -/
def addr : Shape → ℕ → List Bool
  | leaf, _ => []
  | node l r, v => if v < l.size then false :: l.addr v else true :: r.addr (v - l.size)

/-- The balanced tree with `k` leaves: `m = ⌈k/2⌉` (paper, Section 3). -/
def balanced : ℕ → Shape
  | 0 => leaf
  | 1 => leaf
  | k + 2 => node (balanced ((k + 3) / 2)) (balanced ((k + 2) / 2))
termination_by k => k
decreasing_by all_goals omega

/-- Depth (height) of the tree. -/
def depth : Shape → ℕ
  | leaf => 0
  | node l r => max l.depth r.depth + 1

@[simp] lemma subD_nil (t : Shape) : t.subD [] = t := by cases t <;> rfl
@[simp] lemma lo_nil (t : Shape) : t.lo [] = 0 := by cases t <;> rfl
@[simp] lemma isAddr_nil (t : Shape) : t.IsAddr [] := by cases t <;> trivial
@[simp] lemma subD_leaf (a : List Bool) : leaf.subD a = leaf := by cases a <;> rfl
@[simp] lemma lo_leaf (a : List Bool) : leaf.lo a = 0 := by cases a <;> rfl
@[simp] lemma subD_node_false (l r : Shape) (a : List Bool) :
    (node l r).subD (false :: a) = l.subD a := rfl
@[simp] lemma subD_node_true (l r : Shape) (a : List Bool) :
    (node l r).subD (true :: a) = r.subD a := rfl
@[simp] lemma lo_node_false (l r : Shape) (a : List Bool) :
    (node l r).lo (false :: a) = l.lo a := rfl
@[simp] lemma lo_node_true (l r : Shape) (a : List Bool) :
    (node l r).lo (true :: a) = l.size + r.lo a := rfl
@[simp] lemma isAddr_node_false (l r : Shape) (a : List Bool) :
    (node l r).IsAddr (false :: a) ↔ l.IsAddr a := Iff.rfl
@[simp] lemma isAddr_node_true (l r : Shape) (a : List Bool) :
    (node l r).IsAddr (true :: a) ↔ r.IsAddr a := Iff.rfl
@[simp] lemma isAddr_leaf_cons (b : Bool) (a : List Bool) : ¬ leaf.IsAddr (b :: a) := id

lemma subD_append : ∀ (t : Shape) (a b : List Bool), t.subD (a ++ b) = (t.subD a).subD b
  | t, [], b => by simp
  | leaf, _ :: a, b => by simp [subD]
  | node l _, false :: a, b => by simp [subD_append l a b]
  | node _ r, true :: a, b => by simp [subD_append r a b]

lemma lo_append : ∀ (t : Shape) (a b : List Bool), t.lo (a ++ b) = t.lo a + (t.subD a).lo b
  | t, [], b => by simp
  | leaf, _ :: a, b => by simp [lo]
  | node l _, false :: a, b => by simp [lo_append l a b]
  | node l r, true :: a, b => by simp [lo_append r a b]; omega

lemma isAddr_append : ∀ (t : Shape) (a b : List Bool),
    t.IsAddr (a ++ b) ↔ t.IsAddr a ∧ (t.subD a).IsAddr b
  | t, [], b => by simp
  | leaf, _ :: a, b => by simp
  | node l _, false :: a, b => by simp [isAddr_append l a b]
  | node _ r, true :: a, b => by simp [isAddr_append r a b]

lemma isAddr_of_append {t : Shape} {a b : List Bool} (h : t.IsAddr (a ++ b)) : t.IsAddr a :=
  ((isAddr_append t a b).1 h).1

/-- Children of an internal node. -/
lemma subD_append_false {t : Shape} {a : List Bool} {l r : Shape} (h : t.subD a = node l r) :
    t.subD (a ++ [false]) = l := by rw [subD_append, h]; simp [subD]

lemma subD_append_true {t : Shape} {a : List Bool} {l r : Shape} (h : t.subD a = node l r) :
    t.subD (a ++ [true]) = r := by rw [subD_append, h]; simp [subD]

lemma lo_append_false {t : Shape} {a : List Bool} {l r : Shape} (h : t.subD a = node l r) :
    t.lo (a ++ [false]) = t.lo a := by rw [lo_append, h]; simp

lemma lo_append_true {t : Shape} {a : List Bool} {l r : Shape} (h : t.subD a = node l r) :
    t.lo (a ++ [true]) = t.lo a + l.size := by rw [lo_append, h]; simp

lemma isAddr_append_bool {t : Shape} {a : List Bool} {l r : Shape} (ha : t.IsAddr a)
    (h : t.subD a = node l r) (b : Bool) : t.IsAddr (a ++ [b]) := by
  rw [isAddr_append, h]; cases b <;> simp [ha]

/-- The range of a node: `lo a + size (subD a) ≤ size`. -/
lemma lo_add_size_le : ∀ (t : Shape) (a : List Bool), t.IsAddr a →
    t.lo a + (t.subD a).size ≤ t.size
  | t, [], _ => by simp
  | leaf, _ :: _, h => absurd h (isAddr_leaf_cons _ _)
  | node l r, false :: a, h => by
    have := lo_add_size_le l a h; simp [size] at *; omega
  | node l r, true :: a, h => by
    have := lo_add_size_le r a h; simp [size] at *; omega

/-! ### Leaf addresses -/

lemma subD_addr : ∀ (t : Shape) (v : ℕ), t.subD (t.addr v) = leaf
  | leaf, v => rfl
  | node l r, v => by
    unfold addr; split_ifs
    · simp [subD_addr l v]
    · simp [subD_addr r]

lemma isAddr_addr : ∀ (t : Shape) (v : ℕ), t.IsAddr (t.addr v)
  | leaf, v => trivial
  | node l r, v => by
    unfold addr; split_ifs
    · simpa using isAddr_addr l v
    · simpa using isAddr_addr r _

lemma lo_addr : ∀ (t : Shape) (v : ℕ), v < t.size → t.lo (t.addr v) = v
  | leaf, v, h => by simp [size] at h; simp [addr, h]
  | node l r, v, h => by
    unfold addr; split_ifs with h1
    · simp [lo_addr l v h1]
    · simp only [lo_node_true]; rw [lo_addr r]; · omega
      simp [size] at h; omega

/-- A leaf address is the address of its value. -/
lemma addr_lo : ∀ (t : Shape) (a : List Bool), t.IsAddr a → t.subD a = leaf →
    t.addr (t.lo a) = a
  | leaf, [], _, _ => rfl
  | leaf, _ :: _, h, _ => absurd h (isAddr_leaf_cons _ _)
  | node l r, [], _, h => by simp at h
  | node l r, false :: a, h1, h2 => by
    have hlt : l.lo a < l.size := by
      have := lo_add_size_le l a h1; have := size_pos (l.subD a); omega
    simp only [lo_node_false, addr, hlt, ↓reduceIte]
    rw [addr_lo l a h1 h2]
  | node l r, true :: a, h1, h2 => by
    simp only [lo_node_true, addr, Nat.add_sub_cancel_left]
    rw [ite_eq_right_iff.2 (fun h => absurd h (by omega)), addr_lo r a h1 h2]

/-! ### Divergence of two addresses -/

/-- Two different leaf addresses diverge at some node, the first going left. -/
lemma lo_lt_of_diverge {t : Shape} {u x y : List Bool} (hx : t.IsAddr (u ++ false :: x))
    (_hy : t.IsAddr (u ++ true :: y)) : t.lo (u ++ false :: x) < t.lo (u ++ true :: y) := by
  have hu := isAddr_of_append hx
  rw [isAddr_append] at hx
  rw [lo_append, lo_append]
  cases h : t.subD u with
  | leaf => rw [h] at hx; exact absurd hx.2 (isAddr_leaf_cons _ _)
  | node l r =>
    rw [h] at hx
    simp only [lo_node_false, lo_node_true]
    have := lo_add_size_le l x hx.2; have := size_pos (l.subD x); omega

/-- Any two lists are comparable as paths: equal, one a proper prefix of the other, or they
diverge. -/
lemma path_trichotomy : ∀ (a b : List Bool),
    a = b ∨ (∃ c, c ≠ [] ∧ b = a ++ c) ∨ (∃ c, c ≠ [] ∧ a = b ++ c) ∨
    (∃ u x y, a = u ++ false :: x ∧ b = u ++ true :: y) ∨
    (∃ u x y, a = u ++ true :: x ∧ b = u ++ false :: y)
  | [], [] => Or.inl rfl
  | [], c :: cs => Or.inr (Or.inl ⟨c :: cs, by simp, rfl⟩)
  | c :: cs, [] => Or.inr (Or.inr (Or.inl ⟨c :: cs, by simp, rfl⟩))
  | x :: a, y :: b => by
    rcases path_trichotomy a b with h | ⟨c, hc, h⟩ | ⟨c, hc, h⟩ | ⟨u, p, q, h1, h2⟩ |
        ⟨u, p, q, h1, h2⟩
    · subst h
      cases x <;> cases y
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨[], a, a, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨[], a, a, rfl, rfl⟩)))
      · exact Or.inl rfl
    · cases x <;> cases y
      · exact Or.inr (Or.inl ⟨c, hc, by simp [h]⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨[], a, b, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨[], a, b, rfl, rfl⟩)))
      · exact Or.inr (Or.inl ⟨c, hc, by simp [h]⟩)
    · cases x <;> cases y
      · exact Or.inr (Or.inr (Or.inl ⟨c, hc, by simp [h]⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨[], a, b, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨[], a, b, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨c, hc, by simp [h]⟩))
    · cases x <;> cases y
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨false :: u, p, q, by simp [h1], by simp [h2]⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨[], a, b, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨[], a, b, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨true :: u, p, q, by simp [h1], by simp [h2]⟩)))
    · cases x <;> cases y
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨false :: u, p, q, by simp [h1], by simp [h2]⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨[], a, b, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨[], a, b, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨true :: u, p, q, by simp [h1], by simp [h2]⟩)))

/-- A leaf has no proper extension inside the tree. -/
lemma not_isAddr_of_leaf {t : Shape} {a c : List Bool} (h : t.subD a = leaf) (hc : c ≠ []) :
    ¬ t.IsAddr (a ++ c) := by
  rw [isAddr_append, h]; obtain ⟨b, c, rfl⟩ := List.exists_cons_of_ne_nil hc; simp

/-! ### Prefixes of leaf addresses -/

/-- `a` is on the path to the leaf `v` iff `v` is in the range of `a`. -/
lemma prefix_addr_iff : ∀ (t : Shape) (a : List Bool) (v : ℕ), t.IsAddr a → v < t.size →
    (a <+: t.addr v ↔ t.lo a ≤ v ∧ v < t.lo a + (t.subD a).size)
  | t, [], v, _, hv => by simp [hv]
  | leaf, _ :: _, _, h, _ => absurd h (isAddr_leaf_cons _ _)
  | node l r, false :: a, v, h, hv => by
    simp only [addr, lo_node_false, subD_node_false]
    have ih := prefix_addr_iff l a v h
    have := lo_add_size_le l a h
    split_ifs with h1
    · simp [ih h1]
    · simp only [List.cons_prefix_cons, Bool.false_eq_true, false_and, false_iff, not_and,
        not_lt]
      intro _; omega
  | node l r, true :: a, v, h, hv => by
    simp only [addr, lo_node_true, subD_node_true]
    have := lo_add_size_le r a h
    split_ifs with h1
    · simp only [List.cons_prefix_cons, Bool.true_eq_false, false_and, false_iff, not_and,
        not_lt]
      omega
    · simp only [size] at hv
      have ih := prefix_addr_iff r a (v - l.size) h (by omega)
      simp only [List.cons_prefix_cons, true_and, ih]
      omega

lemma isAddr_of_prefix_addr {t : Shape} {a : List Bool} {v : ℕ} (h : a <+: t.addr v) :
    t.IsAddr a := by
  obtain ⟨c, hc⟩ := h; exact isAddr_of_append (hc ▸ isAddr_addr t v)

/-- Following the path to `v` at an internal node of it. -/
lemma prefix_addr_child {t : Shape} {a : List Bool} {v : ℕ} {l r : Shape} (hv : v < t.size)
    (ha : a <+: t.addr v) (hn : t.subD a = node l r) :
    (v - t.lo a < l.size → a ++ [false] <+: t.addr v) ∧
    (¬ v - t.lo a < l.size → a ++ [true] <+: t.addr v) := by
  have hA := isAddr_of_prefix_addr ha
  have hr := (prefix_addr_iff t a v hA hv).1 ha
  rw [hn] at hr; simp only [size] at hr
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [prefix_addr_iff t _ v (isAddr_append_bool hA hn false) hv, lo_append_false hn,
      subD_append_false hn]; omega
  · rw [prefix_addr_iff t _ v (isAddr_append_bool hA hn true) hv, lo_append_true hn,
      subD_append_true hn]; omega

/-- A leaf is the end of every address extending it. -/
lemma eq_of_prefix_of_leaf {t : Shape} {a e : List Bool} (h : t.subD a = leaf) (he : t.IsAddr e)
    (hae : a <+: e) : e = a := by
  obtain ⟨c, rfl⟩ := hae
  rcases c with _ | ⟨b, c⟩
  · simp
  · exact absurd he (not_isAddr_of_leaf h (by simp))

lemma eq_addr_of_leaf {t : Shape} {e : List Bool} {v : ℕ} (h : t.subD e = leaf)
    (he : e <+: t.addr v) : t.addr v = e :=
  eq_of_prefix_of_leaf h (isAddr_addr t v) he

/-- Paths without right steps have offset `0`. -/
lemma lo_eq_zero_of_noTrue : ∀ (t : Shape) (a : List Bool), (∀ u x, a ≠ u ++ true :: x) →
    t.lo a = 0
  | _, [], _ => by simp
  | leaf, _ :: _, _ => by simp
  | node l r, false :: a, h => by
    simp only [lo_node_false]
    exact lo_eq_zero_of_noTrue l a (fun u x hux => h (false :: u) x (by simp [hux]))
  | node l r, true :: a, h => absurd (rfl : true :: a = [] ++ true :: a) (h [] a)

lemma addr_zero_noTrue : ∀ (t : Shape) (u x : List Bool), t.addr 0 ≠ u ++ true :: x
  | leaf, u, x => by simp [addr]
  | node l r, u, x => by
    have := size_pos l
    simp only [addr, this, ↓reduceIte]
    rcases u with _ | ⟨b, u⟩
    · simp
    · intro h
      simp only [List.cons_append, List.cons.injEq] at h
      exact addr_zero_noTrue l u x h.2

lemma lo_le_lo_append (t : Shape) (a c : List Bool) : t.lo a ≤ t.lo (a ++ c) := by
  rw [lo_append]; omega

end Shape

/-! ### Paths and switch states -/

/-- Every left step of the path `c` is at a node whose switch is off in `σ`. -/
def LeftDom (c : List Bool) (σ : List Bool → Bool) : Prop :=
  ∀ u x, c = u ++ false :: x → σ u = false

/-- Every right step of the path `c` is at a node whose switch is on in `σ`. -/
def RightDom (c : List Bool) (σ : List Bool → Bool) : Prop :=
  ∀ u x, c = u ++ true :: x → σ u = true

lemma LeftDom.mono {c : List Bool} {σ σ' : List Bool → Bool} (h : LeftDom c σ')
    (hσ : ∀ u, σ u = true → σ' u = true) : LeftDom c σ := by
  intro u x hc; have := h u x hc; cases hu : σ u; · rfl
  · simp [hσ u hu] at this

lemma RightDom.mono {c : List Bool} {σ σ' : List Bool → Bool} (h : RightDom c σ)
    (hσ : ∀ u, σ u = true → σ' u = true) : RightDom c σ' :=
  fun u x hc => hσ u (h u x hc)

@[simp] lemma leftDom_nil (σ : List Bool → Bool) : LeftDom [] σ := by
  intro u x h; cases u <;> simp at h

@[simp] lemma rightDom_nil (σ : List Bool → Bool) : RightDom [] σ := by
  intro u x h; cases u <;> simp at h

lemma LeftDom.of_append {c d : List Bool} {σ : List Bool → Bool} (h : LeftDom (c ++ d) σ) :
    LeftDom c σ := fun u x hc => h u (x ++ d) (by simp [hc])

lemma RightDom.of_append {c d : List Bool} {σ : List Bool → Bool} (h : RightDom (c ++ d) σ) :
    RightDom c σ := fun u x hc => h u (x ++ d) (by simp [hc])

lemma eq_append_singleton_cases {u x c : List Bool} {b b' : Bool}
    (h : u ++ b :: x = c ++ [b']) :
    (u = c ∧ b = b' ∧ x = []) ∨ ∃ x', x = x' ++ [b'] ∧ c = u ++ b :: x' := by
  rcases List.eq_nil_or_concat x with rfl | ⟨x', y, rfl⟩
  · simp at h; exact Or.inl ⟨h.1, h.2, rfl⟩
  · have h' : (u ++ b :: x') ++ [y] = c ++ [b'] := by simpa using h
    have := List.append_inj' h' rfl
    simp at this
    exact Or.inr ⟨x', by simp [this.2], by simp [this.1]⟩

lemma leftDom_append_false {c : List Bool} {σ : List Bool → Bool} (h : LeftDom c σ)
    (hc : σ c = false) : LeftDom (c ++ [false]) σ := by
  intro u x hux
  rcases eq_append_singleton_cases hux.symm with ⟨rfl, -, -⟩ | ⟨x', -, rfl⟩
  · exact hc
  · exact h u x' rfl

lemma leftDom_append_true {c : List Bool} {σ : List Bool → Bool} (h : LeftDom c σ) :
    LeftDom (c ++ [true]) σ := by
  intro u x hux
  rcases eq_append_singleton_cases hux.symm with ⟨-, h2, -⟩ | ⟨x', -, rfl⟩
  · simp at h2
  · exact h u x' rfl

lemma rightDom_append_true {c : List Bool} {σ : List Bool → Bool} (h : RightDom c σ)
    (hc : σ c = true) : RightDom (c ++ [true]) σ := by
  intro u x hux
  rcases eq_append_singleton_cases hux.symm with ⟨rfl, -, -⟩ | ⟨x', -, rfl⟩
  · exact hc
  · exact h u x' rfl

lemma rightDom_append_false {c : List Bool} {σ : List Bool → Bool} (h : RightDom c σ) :
    RightDom (c ++ [false]) σ := by
  intro u x hux
  rcases eq_append_singleton_cases hux.symm with ⟨-, h2, -⟩ | ⟨x', -, rfl⟩
  · simp at h2
  · exact h u x' rfl

namespace Shape

/-- **Key comparison.** If the leaf `a` is reached by a traversal that read every switch no later
than `σ` (`RightDom a σ`) and the leaf `b` by one that read every switch no earlier than `σ`
(`LeftDom b σ`), then `a ≤ b`. -/
lemma lo_le_lo_of_rightDom_leftDom {t : Shape} {a b : List Bool} {σ : List Bool → Bool}
    (ha : t.IsAddr a) (hb : t.IsAddr b) (hal : t.subD a = leaf) (hbl : t.subD b = leaf)
    (hra : RightDom a σ) (hlb : LeftDom b σ) : t.lo a ≤ t.lo b := by
  rcases path_trichotomy a b with rfl | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨u, x, y, rfl, rfl⟩ |
      ⟨u, x, y, rfl, rfl⟩
  · exact le_rfl
  · exact absurd hb (not_isAddr_of_leaf hal hc)
  · exact absurd ha (not_isAddr_of_leaf hbl hc)
  · exact (lo_lt_of_diverge ha hb).le
  · have h1 := hra u x rfl; have h2 := hlb u y rfl; simp [h1] at h2

end Shape

end Podc.LimitedUseSnapshots
