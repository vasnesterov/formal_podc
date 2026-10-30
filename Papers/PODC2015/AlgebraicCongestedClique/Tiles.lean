import Mathlib

/-!
# Lemma 12: disjoint tiles (Censor-Hillel et al., PODC 2015)

Lemma 12 of [Censor-Hillel, Kaski, Korhonen, Lenzen, Paz, Suomela, *Algebraic Methods in the
Congested Clique*, PODC 2015] (combinatorial part): if `∑_y deg(y)² < 2n²` then one can choose
for every node `y` sets `A(y), B(y) ⊆ V` with `|A(y)| = |B(y)| ≥ deg(y)/8` such that the tiles
`A(y) × B(y)` are pairwise disjoint.

## Construction

* `tileSize d` is the side `f(y)` of the tile of a node of degree `d`: `d/4` rounded down to a
  power of two (as in the paper), but `1` for `1 ≤ d ≤ 3` (the paper's rule gives no positive
  integer there) and `0` for `d = 0`. We have `d ≤ 8 * tileSize d`.
* Area: `16 f² ≤ d² + 15` for every `d`, so `∑ f² ≤ k²` where `k = 2 ^ Nat.log 2 n` is `n`
  rounded down to a power of two (for `n ≥ 3` from `∑ d² < 2n²` and `2k ≥ n + 1`; for `n ≤ 2`
  directly).
* Packing (instead of the paper's iterative quadtree procedure we use the equivalent Z-order /
  Morton order): sort the nodes by decreasing tile size (ties by identifier); the offset of `y`
  is the total area of the tiles before it. As all sizes are powers of two and the earlier ones
  are at least as large, `f(y)²` divides the offset, so the Morton-order interval
  `[off(y), off(y) + f(y)²)` is exactly an aligned `f(y) × f(y)` square.

The Morton-order machinery (`morton`, `unmorton`, `alignedBlock`, `packA`, `packB`) is generic.
-/

namespace Podc.AlgebraicCongestedClique

open Finset

/-! ### Morton (Z-order) bit interleaving -/

-- CSLib candidate
/-- Morton (Z-order) code: interleaves the bits of `a` (odd positions) and `b` (even positions). -/
def morton (a b : ℕ) : ℕ :=
  if a = 0 ∧ b = 0 then 0 else 4 * morton (a / 2) (b / 2) + 2 * (a % 2) + b % 2
termination_by a + b
decreasing_by omega

theorem morton_eq (a b : ℕ) : morton a b = 4 * morton (a / 2) (b / 2) + 2 * (a % 2) + b % 2 := by
  rw [morton]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [morton]; simp
  · rfl

theorem morton_div_four (a b : ℕ) : morton a b / 4 = morton (a / 2) (b / 2) := by
  rw [morton_eq a b]; omega

theorem morton_div_pow (a b j : ℕ) : morton a b / 4 ^ j = morton (a / 2 ^ j) (b / 2 ^ j) := by
  induction j generalizing a b with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ih, morton_div_four,
      Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_succ]

theorem le_morton_left (a b : ℕ) : a ≤ morton a b := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    rw [morton_eq]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · omega
    · have := ih (a / 2) (by omega) (b / 2); omega

theorem le_morton_right (a b : ℕ) : b ≤ morton a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rw [morton_eq]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · omega
    · have := ih (b / 2) (by omega) (a / 2); omega

/-- If the Morton code is below `4 ^ r`, both coordinates are below `2 ^ r`. -/
theorem lt_pow_of_morton_lt {a b r : ℕ} (h : morton a b < 4 ^ r) : a < 2 ^ r ∧ b < 2 ^ r := by
  have h0 : morton (a / 2 ^ r) (b / 2 ^ r) = 0 := by
    rw [← morton_div_pow]; exact Nat.div_eq_of_lt h
  have h1 := le_morton_left (a / 2 ^ r) (b / 2 ^ r)
  have h2 := le_morton_right (a / 2 ^ r) (b / 2 ^ r)
  have hp : 0 < 2 ^ r := by positivity
  constructor
  · by_contra hc; have := Nat.div_pos (not_lt.1 hc) hp; omega
  · by_contra hc; have := Nat.div_pos (not_lt.1 hc) hp; omega

-- CSLib candidate
/-- Inverse of `morton`: de-interleaves the bits of `c`. -/
def unmorton (c : ℕ) : ℕ × ℕ :=
  if c = 0 then (0, 0) else
    (2 * (unmorton (c / 4)).1 + c % 4 / 2, 2 * (unmorton (c / 4)).2 + c % 2)
termination_by c
decreasing_by omega

theorem morton_unmorton (c : ℕ) : morton (unmorton c).1 (unmorton c).2 = c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rw [unmorton]
    split_ifs with hc
    · subst hc; rw [morton]; simp
    · rw [morton_eq]
      have h := ih (c / 4) (by omega)
      have e1 : (2 * (unmorton (c / 4)).1 + c % 4 / 2) / 2 = (unmorton (c / 4)).1 := by omega
      have e2 : (2 * (unmorton (c / 4)).2 + c % 2) / 2 = (unmorton (c / 4)).2 := by omega
      simp only [e1, e2, h]
      omega

/-! ### Aligned blocks and packing of power-of-two squares in Morton order -/

-- CSLib candidate
/-- The aligned block `{a : Fin n | a / K = p}` (the `p`-th block of `K` consecutive indices). -/
def alignedBlock (n K p : ℕ) : Finset (Fin n) := univ.filter fun a => a.val / K = p

theorem card_alignedBlock {n K p : ℕ} (hK : 0 < K) (h : (p + 1) * K ≤ n) :
    (alignedBlock n K p).card = K := by
  have e : (alignedBlock n K p).map Fin.valEmbedding = Ico (p * K) (p * K + K) := by
    ext a
    simp only [alignedBlock, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
      mem_Ico]
    constructor
    · rintro ⟨b, hb, rfl⟩
      subst hb
      exact ⟨Nat.div_mul_le_self _ _, Nat.lt_div_mul_add hK⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨a, by nlinarith⟩, ?_, rfl⟩
      exact Nat.div_eq_of_lt_le h1 (by nlinarith)
  rw [← card_map, e]; simp

section Packing

variable {n : ℕ} (f : Fin n → ℕ)

/-- The offset of `y` in the Morton-order packing: the total area of the squares placed before
`y`, where the squares are placed by decreasing side, ties broken by identifier. -/
def offset (y : Fin n) : ℕ :=
  ∑ y' ∈ univ.filter (fun y' => f y < f y' ∨ (f y = f y' ∧ y' < y)), f y' ^ 2

-- CSLib candidate
/-- Row set of the square of `y` in the Morton-order packing of the squares of sides `f`. -/
def packA (y : Fin n) : Finset (Fin n) :=
  if f y = 0 then ∅ else alignedBlock n (f y) (unmorton (offset f y / f y ^ 2)).1

-- CSLib candidate
/-- Column set of the square of `y` in the Morton-order packing of the squares of sides `f`. -/
def packB (y : Fin n) : Finset (Fin n) :=
  if f y = 0 then ∅ else alignedBlock n (f y) (unmorton (offset f y / f y ^ 2)).2

variable {f}

theorem two_pow_sq (j : ℕ) : (2 ^ j) ^ 2 = 4 ^ j := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

theorem dvd_offset (hf : ∀ y, f y = 0 ∨ ∃ j, f y = 2 ^ j) {y : Fin n} {j : ℕ} (hy : f y = 2 ^ j) :
    4 ^ j ∣ offset f y := by
  apply Finset.dvd_sum
  intro y' hy'
  simp only [mem_filter, mem_univ, true_and] at hy'
  have hle : f y ≤ f y' := by omega
  rcases hf y' with h0 | ⟨i, hi⟩
  · rw [hy] at hle; have := Nat.one_le_two_pow (n := j); omega
  · rw [hy, hi] at hle
    rw [hi, two_pow_sq]
    exact pow_dvd_pow 4 ((Nat.pow_le_pow_iff_right (by norm_num)).1 hle)

theorem offset_add_le {y y' : Fin n} (h : f y < f y' ∨ (f y = f y' ∧ y' < y)) :
    offset f y' + f y' ^ 2 ≤ offset f y := by
  unfold offset
  rw [add_comm, ← Finset.sum_insert (f := fun z => f z ^ 2)
    (s := univ.filter fun z => f y' < f z ∨ (f y' = f z ∧ z < y')) (by simp)]
  apply Finset.sum_le_sum_of_subset
  intro z hz
  simp only [mem_insert, mem_filter, mem_univ, true_and] at hz ⊢
  rcases hz with rfl | hz
  · exact h
  · rw [Fin.lt_def] at h hz ⊢; omega

theorem offset_add_le_sum (y : Fin n) : offset f y + f y ^ 2 ≤ ∑ y', f y' ^ 2 := by
  unfold offset
  rw [add_comm, ← Finset.sum_insert (f := fun z => f z ^ 2)
    (s := univ.filter fun z => f y < f z ∨ (f y = f z ∧ z < y)) (by simp)]
  exact Finset.sum_le_sum_of_subset (subset_univ _)

/-- A point of the square of `y` has Morton code in `[offset y, offset y + f(y)²)`. -/
theorem morton_mem_of_mem_pack (hf : ∀ y, f y = 0 ∨ ∃ j, f y = 2 ^ j) {y : Fin n} {a b : Fin n}
    (ha : a ∈ packA f y) (hb : b ∈ packB f y) :
    offset f y ≤ morton a b ∧ morton a b < offset f y + f y ^ 2 := by
  unfold packA at ha; unfold packB at hb
  split_ifs at ha hb with h0
  · simp at ha
  rcases hf y with h | ⟨j, hj⟩
  · exact absurd h h0
  simp only [alignedBlock, mem_filter, mem_univ, true_and] at ha hb
  obtain ⟨c, hc⟩ := dvd_offset hf hj
  rw [hj, two_pow_sq] at ha hb ⊢
  rw [hc, Nat.mul_div_cancel_left _ (by positivity)] at ha hb
  have hm : morton a b / 4 ^ j = c := by
    rw [morton_div_pow, ha, hb, morton_unmorton]
  have hQ : 0 < 4 ^ j := by positivity
  have h1 := Nat.div_mul_le_self (morton a b) (4 ^ j)
  have h2 := Nat.lt_div_mul_add (a := morton a b) hQ
  rw [hm] at h1 h2
  rw [hc]
  constructor <;> nlinarith

-- CSLib candidate
/-- The squares of the Morton-order packing are pairwise disjoint (sides powers of two or `0`). -/
theorem pack_disjoint (hf : ∀ y, f y = 0 ∨ ∃ j, f y = 2 ^ j) :
    Pairwise fun y y' => Disjoint (packA f y ×ˢ packB f y) (packA f y' ×ˢ packB f y') := by
  intro y y' hne
  rw [Finset.disjoint_left]
  rintro ⟨a, b⟩ h1 h2
  rw [mem_product] at h1 h2
  have i1 := morton_mem_of_mem_pack hf h1.1 h1.2
  have i2 := morton_mem_of_mem_pack hf h2.1 h2.2
  rcases lt_trichotomy (f y) (f y') with hlt | heq | hgt
  · have := offset_add_le (Or.inl hlt); omega
  · rcases lt_trichotomy y y' with hlt | rfl | hgt
    · have := offset_add_le (f := f) (y := y') (y' := y) (Or.inr ⟨heq.symm, hlt⟩); omega
    · exact hne rfl
    · have := offset_add_le (f := f) (y := y) (y' := y') (Or.inr ⟨heq, hgt⟩); omega
  · have := offset_add_le (Or.inl hgt); omega

-- CSLib candidate
/-- If the total area fits into a `2^m × 2^m` square and `2^m ≤ n`, each square of the
Morton-order packing has full side `f y`. -/
theorem card_packA (hf : ∀ y, f y = 0 ∨ ∃ j, f y = 2 ^ j) {m : ℕ}
    (hsum : ∑ y, f y ^ 2 ≤ 4 ^ m) (hm : 2 ^ m ≤ n) (y : Fin n) :
    (packA f y).card = f y ∧ (packB f y).card = f y := by
  unfold packA packB
  split_ifs with h0
  · simp [h0]
  rcases hf y with h | ⟨j, hj⟩
  · exact absurd h h0
  have hle := (offset_add_le_sum (f := f) y).trans hsum
  obtain ⟨c, hc⟩ := dvd_offset hf hj
  rw [hj, two_pow_sq] at hle ⊢
  rw [hc] at hle
  rw [hc, Nat.mul_div_cancel_left _ (by positivity)]
  have hjm : j ≤ m := by
    rw [← Nat.pow_le_pow_iff_right (show 1 < 4 by norm_num)]; omega
  have hc' : c < 4 ^ (m - j) := by
    have e : 4 ^ m = 4 ^ j * 4 ^ (m - j) := by rw [← pow_add]; congr 1; omega
    rw [e] at hle
    have : 4 ^ j * (c + 1) ≤ 4 ^ j * 4 ^ (m - j) := by linarith
    have := Nat.le_of_mul_le_mul_left this (by positivity)
    omega
  rw [← morton_unmorton c] at hc'
  obtain ⟨hp, hq⟩ := lt_pow_of_morton_lt hc'
  have e2 : 2 ^ m = 2 ^ (m - j) * 2 ^ j := by rw [← pow_add]; congr 1; omega
  constructor
  · apply card_alignedBlock (by positivity)
    have : ((unmorton c).1 + 1) * 2 ^ j ≤ 2 ^ (m - j) * 2 ^ j :=
      Nat.mul_le_mul_right _ hp
    omega
  · apply card_alignedBlock (by positivity)
    have : ((unmorton c).2 + 1) * 2 ^ j ≤ 2 ^ (m - j) * 2 ^ j :=
      Nat.mul_le_mul_right _ hq
    omega

end Packing

/-! ### The tiles of Lemma 12 -/

/-- `f(y)` of the proof of Lemma 12: `deg(y)/4` rounded down to a power of two, and `1` for
`1 ≤ deg(y) ≤ 3` (where the paper's rule gives no positive integer), `0` for `deg(y) = 0`. -/
def tileSize (d : ℕ) : ℕ := if d = 0 then 0 else 2 ^ Nat.log 2 (max 1 (d / 4))

theorem tileSize_eq_zero_or_pow (d : ℕ) : tileSize d = 0 ∨ ∃ j, tileSize d = 2 ^ j := by
  unfold tileSize; split_ifs
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

/-- `|A(y)| ≥ deg(y)/8`. -/
theorem le_eight_mul_tileSize (d : ℕ) : d ≤ 8 * tileSize d := by
  unfold tileSize
  split_ifs with h
  · omega
  · have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (max 1 (d / 4))
    rw [pow_succ] at this
    have : d / 4 ≤ max 1 (d / 4) := le_max_right _ _
    omega

theorem tileSize_le_one {d : ℕ} (hd : d < 4) : tileSize d ≤ 1 := by
  unfold tileSize
  split_ifs
  · omega
  · have : max 1 (d / 4) = 1 := by omega
    simp [this]

/-- Per-node area bound: `16 f(y)² ≤ deg(y)² + 15` (the `+ 15` is needed for `1 ≤ deg(y) ≤ 3`,
where the paper's `16 f(y)² ≤ deg(y)²` fails). -/
theorem sixteen_mul_tileSize_sq_le (d : ℕ) : 16 * tileSize d ^ 2 ≤ d ^ 2 + 15 := by
  rcases Nat.lt_or_ge d 4 with h | h
  · rcases Nat.eq_zero_or_pos d with rfl | hpos
    · simp [tileSize]
    have h1 := tileSize_le_one h
    have : tileSize d ^ 2 ≤ 1 := by nlinarith
    nlinarith
  · have hne : d ≠ 0 := by omega
    have hmax : max 1 (d / 4) = d / 4 := by omega
    have hle := Nat.pow_log_le_self 2 (show d / 4 ≠ 0 by omega)
    have h4 : 4 * tileSize d ≤ d := by
      unfold tileSize; simp only [hne, ↓reduceIte, hmax]; omega
    nlinarith

/-- Total area: `∑ f(y)² ≤ k²` with `k = 2 ^ Nat.log 2 n` (`n` rounded down to a power of two). -/
theorem sum_tileSize_sq_le {n : ℕ} {d : Fin n → ℕ} (hd : ∀ y, d y < n)
    (h : ∑ y, d y ^ 2 < 2 * n ^ 2) : ∑ y, tileSize (d y) ^ 2 ≤ 4 ^ Nat.log 2 n := by
  rw [← two_pow_sq]
  set k := 2 ^ Nat.log 2 n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hk : n < 2 * k := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n; rw [pow_succ] at this; omega
  have hk' : k ≤ n := Nat.pow_log_le_self 2 (by omega)
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · -- `n ≤ 2`: all degrees are `< 4`, so every tile has side `≤ 1`.
    calc ∑ y, tileSize (d y) ^ 2 ≤ ∑ _y : Fin n, 1 := by
          apply Finset.sum_le_sum; intro y _
          have := tileSize_le_one (show d y < 4 by have := hd y; omega)
          nlinarith
      _ = n := by simp
      _ ≤ k ^ 2 := by nlinarith
  · have h16 : 16 * ∑ y, tileSize (d y) ^ 2 ≤ ∑ y, d y ^ 2 + 15 * n := by
      rw [Finset.mul_sum]
      calc ∑ y, 16 * tileSize (d y) ^ 2 ≤ ∑ y, (d y ^ 2 + 15) :=
            Finset.sum_le_sum fun y _ => sixteen_mul_tileSize_sq_le (d y)
        _ = ∑ y, d y ^ 2 + 15 * n := by simp [Finset.sum_add_distrib, mul_comm]
    nlinarith

/-- The row set `A(y)` of the tile of `y`: Morton-order packing of the squares of sides
`tileSize (d y)`. -/
def tileA (n : ℕ) (d : Fin n → ℕ) (y : Fin n) : Finset (Fin n) :=
  packA (fun y => tileSize (d y)) y

/-- The column set `B(y)` of the tile of `y`. -/
def tileB (n : ℕ) (d : Fin n → ℕ) (y : Fin n) : Finset (Fin n) :=
  packB (fun y => tileSize (d y)) y

theorem card_tileA_tileB {n : ℕ} {d : Fin n → ℕ} (hd : ∀ y, d y < n)
    (h : ∑ y, d y ^ 2 < 2 * n ^ 2) (y : Fin n) :
    (tileA n d y).card = tileSize (d y) ∧ (tileB n d y).card = tileSize (d y) :=
  card_packA (f := fun y => tileSize (d y)) (fun y => tileSize_eq_zero_or_pow (d y))
    (sum_tileSize_sq_le hd h) (Nat.pow_log_le_self 2 (by have := y.pos; omega)) y

theorem card_tileA {n : ℕ} {d : Fin n → ℕ} (hd : ∀ y, d y < n) (h : ∑ y, d y ^ 2 < 2 * n ^ 2)
    (y : Fin n) : (tileA n d y).card = tileSize (d y) := (card_tileA_tileB hd h y).1

theorem card_tileB {n : ℕ} {d : Fin n → ℕ} (hd : ∀ y, d y < n) (h : ∑ y, d y ^ 2 < 2 * n ^ 2)
    (y : Fin n) : (tileB n d y).card = tileSize (d y) := (card_tileA_tileB hd h y).2

set_option linter.unusedVariables false in
/-- The tiles `A(y) × B(y)` are pairwise disjoint. (Holds without the hypotheses `hd`, `h`, which
are only needed for the cardinalities.) -/
theorem tiles_disjoint {n : ℕ} {d : Fin n → ℕ} (hd : ∀ y, d y < n)
    (h : ∑ y, d y ^ 2 < 2 * n ^ 2) :
    Pairwise fun y y' => Disjoint (tileA n d y ×ˢ tileB n d y) (tileA n d y' ×ˢ tileB n d y') :=
  pack_disjoint fun y => tileSize_eq_zero_or_pow (d y)

/-- Lemma 12 of [Censor-Hillel et al., PODC 2015] (combinatorial part): if the degrees satisfy
`deg(y) < n` and `∑_y deg(y)² < 2n²`, there are sets `A(y), B(y) ⊆ V` with
`|A(y)| = |B(y)| ≥ deg(y)/8` such that the tiles `A(y) × B(y)` are pairwise disjoint subsets of
`V × V`. (The sets are `tileA n d`, `tileB n d`, computed locally from the broadcast degrees.) -/
theorem lemma_12 {n : ℕ} (d : Fin n → ℕ) (hd : ∀ y, d y < n) (h : ∑ y, d y ^ 2 < 2 * n ^ 2) :
    ∃ A B : Fin n → Finset (Fin n), (∀ y, (A y).card = (B y).card ∧ d y ≤ 8 * (A y).card) ∧
      Pairwise fun y y' => Disjoint (A y ×ˢ B y) (A y' ×ˢ B y') := by
  refine ⟨tileA n d, tileB n d, fun y => ?_, tiles_disjoint hd h⟩
  rw [card_tileA hd h, card_tileB hd h]
  exact ⟨rfl, le_eight_mul_tileSize (d y)⟩

end Podc.AlgebraicCongestedClique
