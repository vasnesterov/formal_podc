import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# The infinite binary tree of Algorithm 1 (Afek–Morrison–Wertheim, PODC 2011, Section 4)

Nodes of the infinite binary tree are pairs `(d, k)` with `k < 2^d` (depth `d`, the root has depth
`0`, `k` counts the nodes of depth `d` from the left). The **in-order** of the tree is the order
of the dyadic rationals `key (d, k) = (2k+1) / 2^(d+1) ∈ (0, 1)`: the root is `1/2`, its left
subtree is `(0, 1/2)`, its right subtree is `(1/2, 1)`, and so on. The right subtree of `v` is
`rightSub v` (nodes strictly deeper than `v` whose key lies in `(key v, key v + 2^-(d+1))`).

## Main definitions

* `Node`, `Node.key`, the linear order on nodes (in-order), `rightSub`
* `next d S` (`NextUnaccessedNodeAtDepth`): the smallest node of depth `d` larger than every node
  of the snapshot `S`, if any;
* `prev r m` (`GetPrevNodeMaxDepth`): the largest node of depth `≤ m` smaller than `r`, if any.

## Main statements

* `Node.gap`: two keys of depth `≤ R` differ by at least `2^-(R+1)`;
* `Node.between_left`: the nodes strictly between `leftNb v i` (the largest node of depth `i`
  smaller than `v`) and a node `w` of `v`'s right subtree are `v`, nodes of `v`'s right subtree,
  and nodes of `leftNb v i`'s right subtree (the tree fact behind Lemma 1);
* `Node.rightSub_rm`: every node larger than the rightmost node of depth `d` is in its right subtree.
-/

namespace Podc.UnboundedConcurrency.Swap

/-- A node of the infinite binary tree: depth `d` (the root has depth `0`) and index `k < 2^d`
among the nodes of depth `d`, counted from the left. -/
@[ext] structure Node where
  /-- Depth (distance from the root). -/
  d : ℕ
  /-- Index among the nodes of depth `d`, from the left. -/
  k : ℕ
  /-- There are `2^d` nodes of depth `d`. -/
  hk : k < 2 ^ d
  deriving DecidableEq

namespace Node

/-- The in-order key of a node: the dyadic rational `(2k+1)/2^(d+1)`. -/
def key (v : Node) : ℚ := (2 * v.k + 1) / 2 ^ (v.d + 1)

/-- The key of `v` scaled to resolution `R ≥ v.d`: `key v * 2^(R+1)`, a natural number. -/
def scaled (v : Node) (R : ℕ) : ℕ := (2 * v.k + 1) * 2 ^ (R - v.d)

lemma key_mul {v : Node} {R : ℕ} (h : v.d ≤ R) :
    v.key * 2 ^ (R + 1) = (v.scaled R : ℚ) := by
  unfold key scaled
  have : (2 : ℚ) ^ (R + 1) = 2 ^ (v.d + 1) * 2 ^ (R - v.d) := by
    rw [← pow_add]; congr 1; omega
  rw [this]; push_cast; field_simp

lemma key_pos (v : Node) : 0 < v.key := by unfold key; positivity

lemma key_lt_one (v : Node) : v.key < 1 := by
  unfold key
  rw [div_lt_one (by positivity)]
  have h := v.hk
  have : (2 * v.k + 1 : ℕ) < 2 ^ (v.d + 1) := by rw [pow_succ]; omega
  exact_mod_cast this

lemma key_lt_iff {v w : Node} {R : ℕ} (hv : v.d ≤ R) (hw : w.d ≤ R) :
    v.key < w.key ↔ v.scaled R < w.scaled R := by
  have hp : (0 : ℚ) < 2 ^ (R + 1) := by positivity
  rw [← mul_lt_mul_iff_left₀ hp, key_mul hv, key_mul hw]
  exact_mod_cast Iff.rfl

/-- Gap lemma: keys of nodes of depth `≤ R` are multiples of `2^-(R+1)`. -/
lemma gap {v w : Node} {R : ℕ} (hv : v.d ≤ R) (hw : w.d ≤ R) (h : v.key < w.key) :
    v.key + 1 / 2 ^ (R + 1) ≤ w.key := by
  have hs := (key_lt_iff hv hw).1 h
  have hp : (0 : ℚ) < 2 ^ (R + 1) := by positivity
  rw [← mul_le_mul_iff_left₀ hp, add_mul, key_mul hv, key_mul hw, div_mul_cancel₀ _ hp.ne']
  exact_mod_cast hs

lemma key_injective : Function.Injective key := by
  intro v w h
  -- compare at resolution `max v.d w.d`
  set R := max v.d w.d
  have hv : v.d ≤ R := le_max_left _ _
  have hw : w.d ≤ R := le_max_right _ _
  have hs : v.scaled R = w.scaled R := by
    have := congrArg (· * (2 : ℚ) ^ (R + 1)) h
    simp only [key_mul hv, key_mul hw] at this
    exact_mod_cast this
  unfold scaled at hs
  have hd : v.d = w.d := by
    rcases Nat.lt_trichotomy v.d w.d with hlt | heq | hgt
    · exfalso
      have h1 : R - w.d = 0 := by omega
      obtain ⟨e, he⟩ : ∃ e, R - v.d = e + 1 := ⟨R - v.d - 1, by omega⟩
      rw [h1, he, pow_zero, mul_one] at hs
      have : 2 ∣ 2 * w.k + 1 := ⟨(2 * v.k + 1) * 2 ^ e, by rw [← hs, pow_succ]; ring⟩
      omega
    · exact heq
    · exfalso
      have h1 : R - v.d = 0 := by omega
      obtain ⟨e, he⟩ : ∃ e, R - w.d = e + 1 := ⟨R - w.d - 1, by omega⟩
      rw [h1, he, pow_zero, mul_one] at hs
      have : 2 ∣ 2 * v.k + 1 := ⟨(2 * w.k + 1) * 2 ^ e, by rw [hs, pow_succ]; ring⟩
      omega
  rw [hd] at hs
  have hpos : 0 < 2 ^ (R - w.d) := by positivity
  have hk : v.k = w.k := by
    have := Nat.eq_of_mul_eq_mul_right hpos hs
    omega
  exact Node.ext hd hk

/-- The in-order of the tree. -/
instance : LinearOrder Node := LinearOrder.lift' key key_injective

lemma lt_iff_key {v w : Node} : v < w ↔ v.key < w.key := Iff.rfl

lemma le_iff_key {v w : Node} : v ≤ w ↔ v.key ≤ w.key := Iff.rfl

/-- Nodes of the same depth are ordered by their index. -/
lemma lt_iff_k_of_d_eq {v w : Node} (h : v.d = w.d) : v < w ↔ v.k < w.k := by
  rw [lt_iff_key, key_lt_iff (le_refl v.d) (h ▸ le_refl w.d)]
  unfold scaled
  rw [h, Nat.sub_self, pow_zero]
  omega

/-- `w` is in the right subtree of `v`. -/
def rightSub (v w : Node) : Prop :=
  v.d < w.d ∧ v.key < w.key ∧ w.key < v.key + 1 / 2 ^ (v.d + 1)

lemma rightSub.lt {v w : Node} (h : rightSub v w) : v < w := h.2.1

/-- The rightmost node of depth `d`. -/
def rm (d : ℕ) : Node := ⟨d, 2 ^ d - 1, by have := Nat.one_le_two_pow (n := d); omega⟩

@[simp] lemma rm_d (d : ℕ) : (rm d).d = d := rfl

lemma key_rm (d : ℕ) : (rm d).key = 1 - 1 / 2 ^ (d + 1) := by
  unfold key rm
  have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  simp only
  rw [Nat.cast_sub h1]
  push_cast
  field_simp
  ring

/-- Every node of depth `d` is at most the rightmost one. -/
lemma le_rm {y : Node} {d : ℕ} (h : y.d = d) : y ≤ rm d := by
  rcases lt_or_eq_of_le (show y.k ≤ (rm d).k by have := y.hk; simp only [rm]; rw [h] at this; omega) with hk | hk
  · exact le_of_lt ((lt_iff_k_of_d_eq (by simp [h])).2 hk)
  · exact le_of_eq (Node.ext (by simp [h]) hk)

/-- Every node larger than the rightmost node of depth `d` is in its right subtree. -/
lemma rightSub_rm {d : ℕ} {y : Node} (h : rm d < y) : rightSub (rm d) y := by
  have hy1 := key_lt_one y
  have hk := key_rm d
  refine ⟨?_, h, ?_⟩
  · by_contra hd
    push Not at hd
    have := gap (R := d) (by simp) hd h
    rw [hk] at this
    linarith
  · rw [hk]; simp only [rm_d]; linarith

/-- The largest node of depth `i` smaller than `v`, for `i > v.d`; its key is
`key v - 2^-(i+1)`. -/
def leftNb (v : Node) (i : ℕ) (h : v.d < i) : Node :=
  ⟨i, (2 * v.k + 1) * 2 ^ (i - v.d - 1) - 1, by
    have hk := v.hk
    have h1 : 2 ^ (i - v.d - 1) * 2 ^ (v.d + 1) = 2 ^ i := by rw [← pow_add]; congr 1; omega
    have h2 : (2 * v.k + 1) * 2 ^ (i - v.d - 1) ≤ (2 ^ (v.d + 1) - 1) * 2 ^ (i - v.d - 1) :=
      Nat.mul_le_mul_right _ (by rw [pow_succ]; omega)
    have h3 : 1 ≤ 2 ^ (i - v.d - 1) := Nat.one_le_two_pow
    rw [Nat.sub_mul, one_mul, mul_comm (2 ^ (v.d + 1)), h1] at h2
    generalize (2 * v.k + 1) * 2 ^ (i - v.d - 1) = A at h2 ⊢
    generalize 2 ^ (i - v.d - 1) = B at h2 h3
    have : 0 < 2 ^ i := by positivity
    omega⟩

@[simp] lemma leftNb_d (v : Node) (i : ℕ) (h : v.d < i) : (leftNb v i h).d = i := rfl

lemma key_leftNb (v : Node) (i : ℕ) (h : v.d < i) :
    (leftNb v i h).key = v.key - 1 / 2 ^ (i + 1) := by
  have hp : (0 : ℚ) < 2 ^ (i + 1) := by positivity
  have e1 := key_mul (v := leftNb v i h) (R := i) (le_refl _)
  have e2 := key_mul (v := v) (R := i) h.le
  have hs : (leftNb v i h).scaled i + 1 = v.scaled i := by
    unfold scaled leftNb
    simp only [Nat.sub_self, pow_zero, mul_one]
    have h3 : 1 ≤ 2 ^ (i - v.d - 1) := Nat.one_le_two_pow
    have h4 : 2 ^ (i - v.d) = 2 * 2 ^ (i - v.d - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h4]
    have h5 : 1 ≤ (2 * v.k + 1) * 2 ^ (i - v.d - 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    rw [Nat.mul_sub, mul_one]
    have : 2 * ((2 * v.k + 1) * 2 ^ (i - v.d - 1)) = (2 * v.k + 1) * (2 * 2 ^ (i - v.d - 1)) := by
      ring
    omega
  have : (leftNb v i h).key * 2 ^ (i + 1) + 1 = v.key * 2 ^ (i + 1) := by
    rw [e1, e2]; exact_mod_cast hs
  field_simp
  linarith

lemma leftNb_lt (v : Node) (i : ℕ) (h : v.d < i) : leftNb v i h < v := by
  rw [lt_iff_key, key_leftNb]
  have : (0 : ℚ) < 1 / 2 ^ (i + 1) := by positivity
  linarith

/-- The tree fact behind Lemma 1: a node strictly between `leftNb v i` and a node `w` of depth
`i` of `v`'s right subtree is `v`, or in `v`'s right subtree, or in `leftNb v i`'s right subtree. -/
lemma between_left {v w y : Node} (hw : rightSub v w) (h1 : leftNb v w.d hw.1 < y) (h2 : y < w) :
    y = v ∨ rightSub v y ∨ rightSub (leftNb v w.d hw.1) y := by
  have hl := key_leftNb v w.d hw.1
  rw [lt_iff_key] at h1 h2
  rcases lt_trichotomy y.key v.key with hlt | heq | hgt
  · right; right
    refine ⟨?_, h1, ?_⟩
    · by_contra hd
      push Not at hd
      have := gap (R := w.d) (v := y) (w := v) (by simpa using hd) hw.1.le hlt
      simp only [leftNb_d] at hd
      rw [hl] at h1
      linarith
    · simp only [leftNb_d]; rw [hl]; linarith
  · left; exact key_injective heq
  · right; left
    refine ⟨?_, hgt, ?_⟩
    · by_contra hd
      push Not at hd
      have := gap (R := v.d) (v := v) (w := y) le_rfl hd hgt
      have := hw.2.2
      linarith
    · linarith [hw.2.2]

/-! ### Finite sets of nodes -/

lemma finite_le (m : ℕ) : {v : Node | v.d ≤ m}.Finite := by
  let f : Node → ℕ × ℕ := fun v => (v.d, v.k)
  have hf : Function.Injective f := by
    intro a b h; simp only [f, Prod.mk.injEq] at h; exact Node.ext h.1 h.2
  have hsub : {v : Node | v.d ≤ m} ⊆
      f ⁻¹' ((Finset.range (m + 1) ×ˢ Finset.range (2 ^ m) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv
    simp only [Set.mem_preimage, Finset.coe_product, Finset.coe_range, Set.mem_prod,
      Set.mem_Iio, f]
    refine ⟨by omega, lt_of_lt_of_le v.hk (Nat.pow_le_pow_right (by norm_num) hv)⟩
  exact ((Finset.finite_toSet _).preimage hf.injOn).subset hsub

/-- The (finite) set of nodes of depth `≤ m`. -/
noncomputable def upTo (m : ℕ) : Finset Node := (finite_le m).toFinset

@[simp] lemma mem_upTo {m : ℕ} {v : Node} : v ∈ upTo m ↔ v.d ≤ m := by
  simp [upTo]

end Node

open Node

/-! ### `NextUnaccessedNodeAtDepth` and `GetPrevNodeMaxDepth` -/

/-- `c` is larger than every node of the snapshot `S`. -/
def Above (S : ℕ → Option Node) (c : Node) : Prop := ∀ e a, S e = some a → a < c

open Classical in
/-- `NextUnaccessedNodeAtDepth(d)` applied to the result `S` of `scan(accessed)`: the smallest
node of depth `d` larger than every node of `S`, or `none` if there is no such node. -/
noncomputable def next (d : ℕ) (S : ℕ → Option Node) : Option Node :=
  if h : ∃ k, ∃ hk : k < 2 ^ d, Above S ⟨d, k, hk⟩ then
    some ⟨d, Nat.find h, (Nat.find_spec h).1⟩
  else none

lemma next_some {d : ℕ} {S : ℕ → Option Node} {c : Node} (h : next d S = some c) :
    c.d = d ∧ Above S c ∧ ∀ c' : Node, c'.d = d → Above S c' → c ≤ c' := by
  classical
  unfold next at h
  split_ifs at h with hex
  cases h
  refine ⟨rfl, (Nat.find_spec hex).2, fun c' hd hc' => ?_⟩
  have hmin : Nat.find hex ≤ c'.k := Nat.find_min' hex ⟨c'.hk.trans_eq (by rw [hd]), by
    have : c' = ⟨d, c'.k, c'.hk.trans_eq (by rw [hd])⟩ := Node.ext hd rfl
    rw [← this]; exact hc'⟩
  rcases lt_or_eq_of_le hmin with hlt | heq
  · exact le_of_lt ((lt_iff_k_of_d_eq hd.symm).2 hlt)
  · exact le_of_eq (Node.ext hd.symm heq)

lemma next_none {d : ℕ} {S : ℕ → Option Node} (h : next d S = none) :
    ∀ c : Node, c.d = d → ∃ e a, S e = some a ∧ c ≤ a := by
  classical
  unfold next at h
  split_ifs at h with hex
  intro c hd
  by_contra hno
  push Not at hno
  apply hex
  refine ⟨c.k, c.hk.trans_eq (by rw [hd]), fun e a ha => ?_⟩
  have : (⟨d, c.k, c.hk.trans_eq (by rw [hd])⟩ : Node) = c := Node.ext hd.symm rfl
  rw [this]; exact hno e a ha

/-- The nodes of depth `≤ m` smaller than `r`. -/
noncomputable def below (r : Node) (m : ℕ) : Finset Node := (upTo m).filter (· < r)

/-- `GetPrevNodeMaxDepth(r, m)`: the largest node of depth `≤ m` smaller than `r`, or `none`
(`⊥`) if there is none. -/
noncomputable def prev (r : Node) (m : ℕ) : Option Node :=
  if h : (below r m).Nonempty then some ((below r m).max' h) else none

lemma prev_some {r r' : Node} {m : ℕ} (h : prev r m = some r') :
    r' < r ∧ r'.d ≤ m ∧ ∀ y : Node, y.d ≤ m → y < r → y ≤ r' := by
  unfold prev at h
  split_ifs at h with hne
  cases h
  have hmem := Finset.max'_mem _ hne
  simp only [below, Finset.mem_filter, mem_upTo] at hmem
  refine ⟨hmem.2, hmem.1, fun y hy hyr => ?_⟩
  exact Finset.le_max' _ y (by simp [below, hy, hyr])

lemma prev_none {r : Node} {m : ℕ} (h : prev r m = none) : ∀ y : Node, y.d ≤ m → ¬ y < r := by
  unfold prev at h
  split_ifs at h with hne
  intro y hy hyr
  exact hne ⟨y, by simp [below, hy, hyr]⟩

lemma card_below_lt {r r' : Node} {m : ℕ} (h : prev r m = some r') :
    (below r' m).card < (below r m).card := by
  obtain ⟨h1, h2, -⟩ := prev_some h
  apply Finset.card_lt_card
  refine ⟨fun y hy => ?_, fun hsub => ?_⟩
  · simp only [below, Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, hy.2.trans h1⟩
  · have : r' ∈ below r m := by simp [below, h1, h2]
    have := hsub this
    simp [below] at this

end Podc.UnboundedConcurrency.Swap
