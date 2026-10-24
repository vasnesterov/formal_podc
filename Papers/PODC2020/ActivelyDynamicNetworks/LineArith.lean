import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Arithmetic of LineToCompleteBinaryTree

Closed form of the execution of LineToCompleteBinaryTree on the line `0 - 1 - ⋯ - n` rooted at `0`
(Michail–Skretas–Spirakis, PODC 2020, Proposition 2.2). Node `i` moves in rounds `0, …, kk i - 1`
(jumping from `i - 2^s` to `i - 2^(s+1)` in round `s`) and then stays, where
`kk i = #{s ≥ 0 : 3·2^s ≤ i + 1}` (`le_kk_iff`). So after `r` rounds its parent is
`Q r i = i - 2^min(r, kk i)`, and its final parent is `F i = i - 2^(kk i)`.

The final tree is the complete binary tree in level order: node `i` has depth
`lev i = ⌊log₂ (i+1)⌋` (`lev_F`), and `g` has the children `g + 2^(lev g)` and `g + 2^(lev g + 1)`
(`F_c1`, `F_c2`).

The lemmas used for the step of the algorithm:
* `active_step`: if `r < kk i` then `i`'s grandparent `Q r (Q r i)` has `Q r i` as its only child,
  and `Q (r+1) i` is that grandparent.
* `frozen_two_children`: if `kk i ≤ r` and `i` is not a child of the root, its grandparent has two
  children (both below `i`).
* `child_cases`: every child of `g` after `r` rounds is either `g + 2^r` (then the only child) or one
  of the two final children (binary tree in every snapshot).
-/

namespace Podc.ActivelyDynamicNetworks.LineArith

/-- Number of rounds in which node `i` moves. -/
def kk (i : ℕ) : ℕ := if i + 1 < 3 then 0 else Nat.log 2 ((i + 1) / 3) + 1

/-- Level of node `i` in the final tree, `⌊log₂ (i+1)⌋`. -/
def lev (i : ℕ) : ℕ := Nat.log 2 (i + 1)

/-- Parent of node `i` after `r` rounds. -/
def Q (r i : ℕ) : ℕ := i - 2 ^ min r (kk i)

/-- Final parent of node `i`. -/
def F (i : ℕ) : ℕ := i - 2 ^ kk i

theorem le_kk_iff (s i : ℕ) : s + 1 ≤ kk i ↔ 3 * 2 ^ s ≤ i + 1 := by
  unfold kk
  split_ifs with h
  · have : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    constructor <;> intro h' <;> omega
  · rw [Nat.add_le_add_iff_right, Nat.le_log_iff_pow_le (by norm_num) (by omega),
      Nat.le_div_iff_mul_le (by norm_num), mul_comm]

theorem kk_lt (i : ℕ) : i + 1 < 3 * 2 ^ kk i := by
  have := (le_kk_iff (kk i) i).not.1 (by omega)
  omega

theorem kk_ge {i : ℕ} (h : 1 ≤ kk i) : 3 * 2 ^ (kk i - 1) ≤ i + 1 :=
  (le_kk_iff _ i).1 (by omega)

theorem pow_kk_le {i : ℕ} (hi : 1 ≤ i) : 2 ^ kk i ≤ i := by
  rcases Nat.eq_zero_or_pos (kk i) with h | h
  · rw [h]; simpa using hi
  · have h1 := kk_ge h
    have : 2 ^ kk i = 2 * 2 ^ (kk i - 1) := by rw [← pow_succ']; congr 1; omega
    omega

theorem kk_mono {i j : ℕ} (hij : i ≤ j) : kk i ≤ kk j := by
  rcases Nat.eq_zero_or_pos (kk i) with h | h
  · omega
  · have := kk_ge h
    have := (le_kk_iff (kk i - 1) j).2 (by omega)
    omega

theorem pow_lev_le (i : ℕ) : 2 ^ lev i ≤ i + 1 := Nat.pow_log_le_self 2 (by omega)

theorem lt_pow_lev (i : ℕ) : i + 1 < 2 ^ (lev i + 1) := Nat.lt_pow_succ_log_self (by norm_num) _

theorem lev_eq {i ℓ : ℕ} (h1 : 2 ^ ℓ ≤ i + 1) (h2 : i + 1 < 2 ^ (ℓ + 1)) : lev i = ℓ :=
  Nat.log_eq_of_pow_le_of_lt_pow h1 h2

theorem kk_le_lev (i : ℕ) : kk i ≤ lev i := by
  by_contra h
  have := (le_kk_iff (lev i) i).1 (by omega)
  have := lt_pow_lev i
  rw [pow_succ] at this
  omega

theorem lev_le_kk_succ (i : ℕ) : lev i ≤ kk i + 1 := by
  rcases Nat.lt_or_ge (lev i) 2 with h | h
  · omega
  · have h1 := pow_lev_le i
    have : 2 ^ lev i = 4 * 2 ^ (lev i - 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    have := (le_kk_iff (lev i - 2) i).2 (by omega)
    omega

/-- `kk i = lev i` iff `i` lies in the second half of its level. -/
theorem kk_eq_lev_iff {i : ℕ} (hl : 1 ≤ lev i) : kk i = lev i ↔ 3 * 2 ^ (lev i - 1) ≤ i + 1 := by
  rw [← le_kk_iff]
  have := kk_le_lev i
  omega

/-- `2^(ℓ-1)` bookkeeping. -/
theorem two_pow_pred {ℓ : ℕ} (h : 1 ≤ ℓ) : 2 ^ ℓ = 2 * 2 ^ (ℓ - 1) := by
  rw [← pow_succ']; congr 1; omega

theorem lev_F {x : ℕ} (hx : 1 ≤ x) : lev (F x) + 1 = lev x := by
  have hl : 1 ≤ lev x := by
    rw [lev, Nat.le_log_iff_pow_le (by norm_num) (by omega)]; omega
  have h1 := pow_lev_le x
  have h2 := lt_pow_lev x
  have ha := two_pow_pred hl
  rw [pow_succ] at h2
  have hk1 := kk_le_lev x
  have hk2 := lev_le_kk_succ x
  have hiff := kk_eq_lev_iff hl
  set a := 2 ^ (lev x - 1)
  have hapos : 1 ≤ a := Nat.one_le_two_pow
  unfold F
  rcases Nat.lt_or_ge (kk x) (lev x) with hk | hk
  · have hk' : kk x = lev x - 1 := by omega
    have : ¬ 3 * a ≤ x + 1 := fun h => by have := hiff.2 h; omega
    rw [hk']
    have := lev_eq (i := x - 2 ^ (lev x - 1)) (ℓ := lev x - 1) (by omega)
      (by rw [show lev x - 1 + 1 = lev x by omega]; omega)
    omega
  · have hk' : kk x = lev x := by omega
    have : 3 * a ≤ x + 1 := hiff.1 hk'
    rw [hk']
    have := lev_eq (i := x - 2 ^ lev x) (ℓ := lev x - 1) (by omega)
      (by rw [show lev x - 1 + 1 = lev x by omega]; omega)
    omega

theorem F_lt {x : ℕ} (hx : 1 ≤ x) : F x < x := by
  unfold F; have : 1 ≤ 2 ^ kk x := Nat.one_le_two_pow; omega

/-- First final child of `g`. -/
def c1 (g : ℕ) : ℕ := g + 2 ^ lev g
/-- Second final child of `g`. -/
def c2 (g : ℕ) : ℕ := g + 2 ^ (lev g + 1)

theorem kk_c1 (g : ℕ) : kk (c1 g) = lev g := by
  have h1 := pow_lev_le g
  have h2 := lt_pow_lev g
  rw [pow_succ] at h2
  unfold c1
  apply le_antisymm
  · by_contra h
    have := (le_kk_iff (lev g) (g + 2 ^ lev g)).1 (by omega)
    omega
  · rcases Nat.eq_zero_or_pos (lev g) with h | h
    · omega
    · have := two_pow_pred h
      have := (le_kk_iff (lev g - 1) (g + 2 ^ lev g)).2 (by omega)
      omega

theorem kk_c2 (g : ℕ) : kk (c2 g) = lev g + 1 := by
  have h1 := pow_lev_le g
  have h2 := lt_pow_lev g
  rw [pow_succ] at h2
  unfold c2
  rw [pow_succ]
  apply le_antisymm
  · by_contra h
    have := (le_kk_iff (lev g + 1) (g + 2 ^ lev g * 2)).1 (by omega)
    rw [pow_succ] at this
    omega
  · exact (le_kk_iff (lev g) _).2 (by omega)

theorem F_c1 (g : ℕ) : F (c1 g) = g := by
  unfold F; rw [kk_c1]; unfold c1; omega

theorem F_c2 (g : ℕ) : F (c2 g) = g := by
  unfold F; rw [kk_c2]; unfold c2; omega

theorem c1_lt_c2 (g : ℕ) : c1 g < c2 g := by
  unfold c1 c2; rw [pow_succ]; have : 1 ≤ 2 ^ lev g := Nat.one_le_two_pow; omega

theorem g_lt_c1 (g : ℕ) : g < c1 g := by
  unfold c1; have : 1 ≤ 2 ^ lev g := Nat.one_le_two_pow; omega

/-- The final children of `g` are exactly `c1 g` and `c2 g`. -/
theorem eq_c_of_F_eq {g j : ℕ} (hj : 1 ≤ j) (h : F j = g) : j = c1 g ∨ j = c2 g := by
  have hl := lev_F hj
  rw [h] at hl
  have hp := pow_kk_le hj
  have hk1 := kk_le_lev j
  have hk2 := lev_le_kk_succ j
  unfold F at h
  rcases Nat.lt_or_ge (kk j) (lev j) with hk | hk
  · left; unfold c1
    have : kk j = lev g := by omega
    rw [← this]; omega
  · right; unfold c2
    have : kk j = lev g + 1 := by omega
    rw [← this]; omega

theorem Q_zero_right (r : ℕ) : Q r 0 = 0 := by simp [Q]

theorem Q_lt {r i : ℕ} (hi : 1 ≤ i) : Q r i < i := by
  unfold Q; have : 1 ≤ 2 ^ min r (kk i) := Nat.one_le_two_pow; omega

theorem Q_zero_left (i : ℕ) : Q 0 i = i - 1 := by simp [Q]

theorem Q_of_le {r i : ℕ} (h : kk i ≤ r) : Q r i = F i := by
  unfold Q F; rw [min_eq_right h]

theorem Q_of_lt {r i : ℕ} (h : r < kk i) : Q r i = i - 2 ^ r := by
  unfold Q; rw [min_eq_left h.le]

/-- **Uniqueness of children.** If `2^r ≤ g + 1`, the only possible child of `g` after `r` rounds
is `g + 2^r`. -/
theorem child_unique {r g j : ℕ} (hg : 2 ^ r ≤ g + 1) (hj : Q r j = g) (hne : j ≠ g) :
    j = g + 2 ^ r := by
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; rw [Q_zero_right] at hj; exact absurd hj hne
    · exact h
  have hp := pow_kk_le hj1
  rcases Nat.lt_or_ge (kk j) r with h | h
  · rw [Q_of_le h.le, F] at hj
    have h1 := kk_lt j
    have h2 : 2 ^ (kk j + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h
    rw [pow_succ] at h2
    omega
  · have : 2 ^ r ≤ 2 ^ kk j := Nat.pow_le_pow_right (by norm_num) h
    unfold Q at hj; rw [min_eq_left h] at hj
    omega

/-- **Active nodes** (`r < kk i`): the parent `p = Q r i` is not the root, the grandparent is
`Q r p = i - 2^(r+1) = Q (r+1) i`, and `p` is its only child. -/
theorem active_step {r i : ℕ} (h : r < kk i) :
    Q r i ≠ 0 ∧ Q r (Q r i) = Q (r + 1) i ∧
      ∀ j, j ≠ Q r (Q r i) → Q r j = Q r (Q r i) → j = Q r i := by
  have h3 := (le_kk_iff r i).1 h
  have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hp : Q r i = i - 2 ^ r := Q_of_lt h
  have hQ1 : Q (r + 1) i = i - 2 ^ (r + 1) := by
    unfold Q; rw [min_eq_left (by omega)]
  have hkp : r ≤ kk (Q r i) := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · omega
    · have := two_pow_pred h0
      have := (le_kk_iff (r - 1) (Q r i)).2 (by rw [hp]; omega)
      omega
  have hgp : Q r (Q r i) = Q r i - 2 ^ r := by
    show Q r i - 2 ^ min r (kk (Q r i)) = _; rw [min_eq_left hkp]
  refine ⟨by omega, by rw [hgp, hQ1, hp, pow_succ]; omega, ?_⟩
  intro j hne hj
  have := child_unique (r := r) (g := Q r (Q r i)) (by rw [hgp, hp]; omega) hj hne
  rw [this, hgp]
  omega

/-- **Frozen nodes** (`kk i ≤ r`) that are not children of the root: their grandparent has two
distinct children, both smaller than `i`. -/
theorem frozen_two_children {r i : ℕ} (h : kk i ≤ r) (hp : Q r i ≠ 0) :
    ∃ a b, a ≠ b ∧ a ≠ Q r (Q r i) ∧ b ≠ Q r (Q r i) ∧ a < i ∧ b < i ∧
      Q r a = Q r (Q r i) ∧ Q r b = Q r (Q r i) := by
  rw [Q_of_le h] at hp ⊢
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; simp [F] at hp
    · exact h0
  have hp1 : 1 ≤ F i := Nat.one_le_iff_ne_zero.2 hp
  have l1 := lev_F hi1
  have l2 := lev_F hp1
  have hkp : kk (F i) ≤ r := by
    have := kk_le_lev (F i); have := lev_le_kk_succ i; omega
  rw [Q_of_le hkp]
  set g := F (F i)
  refine ⟨c1 g, c2 g, (c1_lt_c2 g).ne, (g_lt_c1 g).ne', ((g_lt_c1 g).trans (c1_lt_c2 g)).ne', ?_,
    ?_, ?_, ?_⟩
  · have : c2 g < i := ?_
    · exact (c1_lt_c2 g).trans this
    · unfold c2
      have := lt_pow_lev g; have := pow_lev_le i
      have e : 2 ^ lev i = 2 * 2 ^ (lev g + 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
  · unfold c2
    have := lt_pow_lev g; have := pow_lev_le i
    have e : 2 ^ lev i = 2 * 2 ^ (lev g + 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  · rw [Q_of_le, F_c1]
    rw [kk_c1]; have := kk_le_lev (F i); have := lev_le_kk_succ i; omega
  · rw [Q_of_le, F_c2]
    rw [kk_c2]; have := lev_le_kk_succ i; omega

/-- Frozen nodes stay: `Q (r+1) i = Q r i` when `kk i ≤ r`. -/
theorem Q_succ_of_le {r i : ℕ} (h : kk i ≤ r) : Q (r + 1) i = Q r i := by
  rw [Q_of_le h, Q_of_le (by omega)]

/-- Children of the root stay. -/
theorem Q_succ_of_eq_zero {r i : ℕ} (h : Q r i = 0) : Q (r + 1) i = 0 := by
  rcases Nat.lt_or_ge r (kk i) with h' | h'
  · exact absurd h (active_step h').1
  · rw [Q_succ_of_le h', h]

/-- **Children after `r` rounds.** Every child of `g` after `r` rounds is `g + 2^r` (and then it is
the only child), or one of the two final children `c1 g`, `c2 g`. -/
theorem child_cases {r g j : ℕ} (hne : j ≠ g) (hj : Q r j = g) :
    (∀ j', j' ≠ g → Q r j' = g → j' = j) ∨ j = c1 g ∨ j = c2 g := by
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; rw [Q_zero_right] at hj; exact absurd hj hne
    · exact h
  rcases Nat.lt_or_ge r (kk j) with h | h
  · left
    have h3 := (le_kk_iff r j).1 h
    have hq := Q_of_lt h
    have hg : 2 ^ r ≤ g + 1 := by rw [← hj, hq]; omega
    intro j' hne' hj'
    rw [child_unique hg hj' hne', child_unique hg hj hne]
  · right
    rw [Q_of_le h] at hj
    exact eq_c_of_F_eq hj1 hj

end Podc.ActivelyDynamicNetworks.LineArith
