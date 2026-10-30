import Papers.PODC2026.TreesNetworkSizeKnowledge.Trees

/-!
# The `k`-hierarchical lower bound graph (Definition 16)

`comp ℓ j top` is a level-`j` component of the `k`-hierarchical lower bound graph with path lengths
`ℓ 1, …, ℓ j`: a path `P_j` of `ℓ j` nodes, where every node has one attached level-`(j-1)`
component and the free endpoint(s) have two. A non-top component (`top = false`) hangs from its first
path node; the top component (`top = true`, `j = k`) has two attached components at both ends, so
`comp ℓ k true` is the whole lower bound graph of Definition 16.

Node codes (identifiers): path node `t` is `Nat.pair 0 t`; node `y` of the `b`-th component
attached to path node `t` is `Nat.pair (2t+b+1) y`. The root (first path node) is `0`.
Along with the vertex set we define parent pointers `par`, a rank, the designed level `lev` and the
position `pos` (index of the path node the node hangs from), used as a distance potential.
-/

namespace Podc.TreesNetworkSizeKnowledge

/-- Data of a component. -/
structure CData where
  V : Finset ℕ
  par : ℕ → ℕ
  rank : ℕ → ℕ
  lev : ℕ → ℕ
  pos : ℕ → ℕ

/-- Path node `t` of a path of `m` nodes has an attached component number `b`. -/
def HasBr (m : ℕ) (top : Bool) (t b : ℕ) : Prop :=
  b = 0 ∨ (b = 1 ∧ (t + 1 = m ∨ (top = true ∧ t = 0)))

instance (m : ℕ) (top : Bool) (t b : ℕ) : Decidable (HasBr m top t b) := by
  unfold HasBr; infer_instance

/-- A level-`j` component of the lower bound graph with path lengths `ℓ`. -/
def comp (ℓ : ℕ → ℕ) : ℕ → Bool → CData
  | 0, _ => ⟨∅, id, fun _ => 0, fun _ => 0, fun _ => 0⟩
  | j + 1, top =>
    let C := comp ℓ j false
    let m := ℓ (j + 1)
    { V := (Finset.range m).image (Nat.pair 0) ∪
        ((Finset.range m ×ˢ Finset.range 2).filter (fun p => HasBr m top p.1 p.2)).biUnion
          (fun p => C.V.image (Nat.pair (2 * p.1 + p.2 + 1)))
      par := fun x => if x.unpair.1 = 0 then Nat.pair 0 (x.unpair.2 - 1)
        else if x.unpair.2 = 0 then Nat.pair 0 ((x.unpair.1 - 1) / 2)
        else Nat.pair x.unpair.1 (C.par x.unpair.2)
      rank := fun x => if x.unpair.1 = 0 then x.unpair.2
        else (x.unpair.1 - 1) / 2 + 1 + C.rank x.unpair.2
      lev := fun x => if x.unpair.1 = 0 then j + 1 else C.lev x.unpair.2
      pos := fun x => if x.unpair.1 = 0 then x.unpair.2 else (x.unpair.1 - 1) / 2 }

lemma pair_eq_zero_iff {a b : ℕ} : Nat.pair a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h; exact Nat.pair_eq_pair.1 (h.trans (show 0 = Nat.pair 0 0 by decide))
  · rintro ⟨rfl, rfl⟩; decide

lemma child_div {t b : ℕ} (hb : b < 2) : (2 * t + b + 1 - 1) / 2 = t := by omega

variable (ℓ : ℕ → ℕ) (j : ℕ) (top : Bool)

section Simp

@[simp] lemma comp_zero_V (top : Bool) : (comp ℓ 0 top).V = ∅ := rfl

lemma par_path (t : ℕ) : (comp ℓ (j + 1) top).par (Nat.pair 0 t) = Nat.pair 0 (t - 1) := by
  simp [comp, Nat.unpair_pair]

lemma par_childRoot {t b : ℕ} (hb : b < 2) :
    (comp ℓ (j + 1) top).par (Nat.pair (2 * t + b + 1) 0) = Nat.pair 0 t := by
  simp only [comp, Nat.unpair_pair]
  simp; omega

lemma par_child (a : ℕ) {y : ℕ} (ha : a ≠ 0) (hy : y ≠ 0) :
    (comp ℓ (j + 1) top).par (Nat.pair a y) = Nat.pair a ((comp ℓ j false).par y) := by
  simp [comp, Nat.unpair_pair, ha, hy]

lemma rank_path (t : ℕ) : (comp ℓ (j + 1) top).rank (Nat.pair 0 t) = t := by
  simp [comp, Nat.unpair_pair]

lemma rank_child {t b : ℕ} (hb : b < 2) (y : ℕ) :
    (comp ℓ (j + 1) top).rank (Nat.pair (2 * t + b + 1) y) = t + 1 + (comp ℓ j false).rank y := by
  simp only [comp, Nat.unpair_pair]
  simp; omega

lemma lev_path (t : ℕ) : (comp ℓ (j + 1) top).lev (Nat.pair 0 t) = j + 1 := by
  simp [comp, Nat.unpair_pair]

lemma lev_child (a : ℕ) (ha : a ≠ 0) (y : ℕ) :
    (comp ℓ (j + 1) top).lev (Nat.pair a y) = (comp ℓ j false).lev y := by
  simp [comp, Nat.unpair_pair, ha]

lemma pos_path (t : ℕ) : (comp ℓ (j + 1) top).pos (Nat.pair 0 t) = t := by
  simp [comp, Nat.unpair_pair]

lemma pos_child {t b : ℕ} (hb : b < 2) (y : ℕ) :
    (comp ℓ (j + 1) top).pos (Nat.pair (2 * t + b + 1) y) = t := by
  simp only [comp, Nat.unpair_pair]
  simp; omega

lemma mem_V {x : ℕ} : x ∈ (comp ℓ (j + 1) top).V ↔
    (∃ t < ℓ (j + 1), x = Nat.pair 0 t) ∨
    (∃ t < ℓ (j + 1), ∃ b < 2, HasBr (ℓ (j + 1)) top t b ∧ ∃ y ∈ (comp ℓ j false).V,
      x = Nat.pair (2 * t + b + 1) y) := by
  simp only [comp, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨t, b, ⟨⟨ht, hb⟩, hbr⟩, y, hy, rfl⟩)
    · exact Or.inl ⟨t, ht, rfl⟩
    · exact Or.inr ⟨t, ht, b, hb, hbr, y, hy, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, b, hb, hbr, y, hy, rfl⟩)
    · exact Or.inl ⟨t, ht, rfl⟩
    · exact Or.inr ⟨t, b, ⟨⟨ht, hb⟩, hbr⟩, y, hy, rfl⟩

lemma path_mem {t : ℕ} (ht : t < ℓ (j + 1)) : Nat.pair 0 t ∈ (comp ℓ (j + 1) top).V :=
  (mem_V ℓ j top).2 (Or.inl ⟨t, ht, rfl⟩)

lemma child_mem {t b y : ℕ} (ht : t < ℓ (j + 1)) (hb : b < 2) (hbr : HasBr (ℓ (j + 1)) top t b)
    (hy : y ∈ (comp ℓ j false).V) : Nat.pair (2 * t + b + 1) y ∈ (comp ℓ (j + 1) top).V :=
  (mem_V ℓ j top).2 (Or.inr ⟨t, ht, b, hb, hbr, y, hy, rfl⟩)

end Simp

/-! ### Basic properties -/

lemma zero_mem (hℓ : ∀ i, 1 ≤ ℓ i) : 0 ∈ (comp ℓ (j + 1) top).V :=
  path_mem ℓ j top (t := 0) (hℓ _)

/-- Well-foundedness of parent pointers. -/
lemma par_wf : ∀ (j : ℕ) (top : Bool), ∀ x ∈ (comp ℓ j top).V, x ≠ 0 →
    (comp ℓ j top).par x ∈ (comp ℓ j top).V ∧
    (comp ℓ j top).rank ((comp ℓ j top).par x) < (comp ℓ j top).rank x
  | 0, _ => by simp
  | j + 1, top => by
    intro x hx h0
    rcases (mem_V ℓ j top).1 hx with ⟨t, ht, rfl⟩ | ⟨t, ht, b, hb, hbr, y, hy, rfl⟩
    · have : t ≠ 0 := by rintro rfl; exact h0 (by decide)
      rw [par_path, rank_path, rank_path]
      exact ⟨path_mem ℓ j top (by omega), by omega⟩
    · by_cases hy0 : y = 0
      · subst hy0
        rw [par_childRoot ℓ j top hb, rank_path, rank_child ℓ j top hb]
        exact ⟨path_mem ℓ j top ht, by omega⟩
      · rw [par_child ℓ j top _ (by omega) hy0, rank_child ℓ j top hb, rank_child ℓ j top hb]
        obtain ⟨h1, h2⟩ := par_wf j false y hy hy0
        exact ⟨child_mem ℓ j top ht hb hbr h1, by omega⟩

/-- Levels are between `1` and `j`. -/
lemma lev_bounds : ∀ (j : ℕ) (top : Bool), ∀ x ∈ (comp ℓ j top).V,
    1 ≤ (comp ℓ j top).lev x ∧ (comp ℓ j top).lev x ≤ j
  | 0, _ => by simp
  | j + 1, top => by
    intro x hx
    rcases (mem_V ℓ j top).1 hx with ⟨t, ht, rfl⟩ | ⟨t, ht, b, hb, hbr, y, hy, rfl⟩
    · rw [lev_path]; omega
    · rw [lev_child ℓ j top _ (by omega)]
      have := lev_bounds j false y hy
      omega

lemma lev_zero (j : ℕ) (top : Bool) : (comp ℓ (j + 1) top).lev 0 = j + 1 :=
  lev_path ℓ j top 0

/-- The children of a path node. -/
lemma par_eq_path {x t : ℕ} (hx : x ∈ (comp ℓ (j + 1) top).V) (hx0 : x ≠ 0)
    (h : (comp ℓ (j + 1) top).par x = Nat.pair 0 t) :
    x = Nat.pair 0 (t + 1) ∨ ∃ b < 2, HasBr (ℓ (j + 1)) top t b ∧ x = Nat.pair (2 * t + b + 1) 0 := by
  rcases (mem_V ℓ j top).1 hx with ⟨t', ht', rfl⟩ | ⟨t', ht', b, hb, hbr, y, hy, rfl⟩
  · rw [par_path, Nat.pair_eq_pair] at h
    have : t' ≠ 0 := by rintro rfl; exact hx0 (by decide)
    left; congr 1; omega
  · by_cases hy0 : y = 0
    · subst hy0
      rw [par_childRoot ℓ j top hb, Nat.pair_eq_pair] at h
      obtain ⟨-, rfl⟩ := h
      exact Or.inr ⟨b, hb, hbr, rfl⟩
    · rw [par_child ℓ j top _ (by omega) hy0, Nat.pair_eq_pair] at h
      omega

/-- The children of a node of an attached component. -/
lemma par_eq_child {x a y : ℕ} (ha : a ≠ 0) (hx : x ∈ (comp ℓ (j + 1) top).V) (hx0 : x ≠ 0)
    (h : (comp ℓ (j + 1) top).par x = Nat.pair a y) :
    ∃ y' ∈ (comp ℓ j false).V, y' ≠ 0 ∧ (comp ℓ j false).par y' = y ∧ x = Nat.pair a y' := by
  rcases (mem_V ℓ j top).1 hx with ⟨t', ht', rfl⟩ | ⟨t', ht', b, hb, hbr, y', hy', rfl⟩
  · rw [par_path, Nat.pair_eq_pair] at h
    omega
  · by_cases hy0 : y' = 0
    · subst hy0
      rw [par_childRoot ℓ j top hb, Nat.pair_eq_pair] at h
      omega
    · rw [par_child ℓ j top _ (by omega) hy0, Nat.pair_eq_pair] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨y', hy', hy0, rfl, rfl⟩

/-- Positions change by at most one along tree edges. -/
lemma pos_par : ∀ x ∈ (comp ℓ (j + 1) top).V, x ≠ 0 →
    (comp ℓ (j + 1) top).pos x ≤ (comp ℓ (j + 1) top).pos ((comp ℓ (j + 1) top).par x) + 1 ∧
    (comp ℓ (j + 1) top).pos ((comp ℓ (j + 1) top).par x) ≤ (comp ℓ (j + 1) top).pos x := by
  intro x hx h0
  rcases (mem_V ℓ j top).1 hx with ⟨t, ht, rfl⟩ | ⟨t, ht, b, hb, hbr, y, hy, rfl⟩
  · rw [par_path, pos_path, pos_path]; omega
  · by_cases hy0 : y = 0
    · subst hy0
      rw [par_childRoot ℓ j top hb, pos_path, pos_child ℓ j top hb]; omega
    · rw [par_child ℓ j top _ (by omega) hy0, pos_child ℓ j top hb, pos_child ℓ j top hb]; omega

lemma pos_lt : ∀ x ∈ (comp ℓ (j + 1) top).V, (comp ℓ (j + 1) top).pos x < ℓ (j + 1) := by
  intro x hx
  rcases (mem_V ℓ j top).1 hx with ⟨t, ht, rfl⟩ | ⟨t, ht, b, hb, hbr, y, hy, rfl⟩
  · rw [pos_path]; exact ht
  · rw [pos_child ℓ j top hb]; exact ht

/-! ### A level-1 node at position 0 (where padding is attached) -/

/-- The code of a level-1 node at position `0` of `comp ℓ j _`. -/
def leafCode : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | j + 2 => Nat.pair 1 (leafCode (j + 1))

lemma leafCode_spec (hℓ : ∀ i, 1 ≤ ℓ i) : ∀ (j : ℕ) (top : Bool),
    leafCode (j + 1) ∈ (comp ℓ (j + 1) top).V ∧ (comp ℓ (j + 1) top).lev (leafCode (j + 1)) = 1 ∧
    (comp ℓ (j + 1) top).pos (leafCode (j + 1)) = 0
  | 0, top => ⟨zero_mem ℓ 0 top hℓ, lev_zero ℓ 0 top, pos_path ℓ 0 top 0⟩
  | j + 1, top => by
    obtain ⟨h1, h2, -⟩ := leafCode_spec hℓ j false
    refine ⟨?_, ?_, ?_⟩
    · exact child_mem ℓ (j + 1) top (t := 0) (b := 0) (hℓ _) (by omega) (Or.inl rfl) h1
    · simp only [leafCode]; rw [lev_child ℓ (j + 1) top 1 (by omega)]; exact h2
    · simp only [leafCode]; exact pos_child ℓ (j + 1) top (t := 0) (b := 0) (by omega) _

/-! ### Size (Observation 17, upper bound) -/

/-- `L j = ℓ 1 ⋯ ℓ j`. -/
def Lprod (ℓ : ℕ → ℕ) (j : ℕ) : ℕ := ∏ i ∈ Finset.range j, ℓ (i + 1)

lemma Lprod_succ (j : ℕ) : Lprod ℓ (j + 1) = Lprod ℓ j * ℓ (j + 1) := by
  simp [Lprod, Finset.prod_range_succ]

lemma Lprod_pos (hℓ : ∀ i, 1 ≤ ℓ i) (j : ℕ) : 1 ≤ Lprod ℓ j :=
  Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => by have := hℓ (i + 1); omega)

lemma card_comp_succ_le (j : ℕ) (top : Bool) :
    (comp ℓ (j + 1) top).V.card ≤ ℓ (j + 1) + 2 * ℓ (j + 1) * (comp ℓ j false).V.card := by
  simp only [comp]
  refine (Finset.card_union_le _ _).trans (add_le_add (Finset.card_image_le.trans (by simp)) ?_)
  refine (Finset.card_biUnion_le_card_mul _ _ _ fun _ _ => Finset.card_image_le).trans ?_
  refine Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans ?_)
  simp [mul_comm]

/-- Observation 17 (upper bound, with `c₂ = 3^j`): a level-`j` component has at most
`3^j ℓ₁⋯ℓ_j` nodes. -/
lemma card_comp_le (hℓ : ∀ i, 1 ≤ ℓ i) : ∀ (j : ℕ) (top : Bool),
    (comp ℓ j top).V.card ≤ 3 ^ j * Lprod ℓ j
  | 0, _ => by simp
  | j + 1, top => by
    have h1 := card_comp_succ_le ℓ j top
    have h2 := card_comp_le hℓ j false
    have h3 := Lprod_pos ℓ hℓ j
    rw [Lprod_succ, pow_succ]
    have h4 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    have h5 : 1 ≤ 3 ^ j * Lprod ℓ j := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc (comp ℓ (j + 1) top).V.card ≤ ℓ (j + 1) + 2 * ℓ (j + 1) * (3 ^ j * Lprod ℓ j) :=
          h1.trans (by gcongr)
      _ ≤ 3 ^ j * 3 * (Lprod ℓ j * ℓ (j + 1)) := by nlinarith

end Podc.TreesNetworkSizeKnowledge
