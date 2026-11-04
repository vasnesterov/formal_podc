import Papers.PODC2014.ReadUpdateTradeoffs.AlgA.Defs

/-!
# Algorithm A of Hendler–Khait (PODC 2014): a concrete leaf layout

The tree of Algorithm A has two subtrees under the root `1` (heap indexing: children of `n` are
`2n`, `2n+1`):

* `T_L` under node `2`, a `B₁`-like tree (Bentley–Yao unbounded search): the leaf of value `v`
  has the binary code `10 1^b 0 t`, where `b = ⌊log₂(v+1)⌋` and `t` is the `b` low bits of
  `v + 1`; it lies at depth `2b + 2`.
* `T_R` under node `3`, a complete binary tree with `2 ^ ⌈log₂ N⌉ ≥ N` leaves, at depth
  `⌈log₂ N⌉ + 1`.

At every depth `d ≥ 1`, positions of `T_L` lie in `[2^d, 3·2^(d-1))` (top bits `10`) and positions
of `T_R` in `[3·2^(d-1), 2^(d+1))` (top bits `11`); `x / 2^k` keeps the top bits of `x`. This
gives `stdLayout N : Layout N` and the depth bound `log_leafOf_le`: the leaf written by
`WriteMax(v)` has depth at most `2 log₂(min(N, v+1)) + 2`.
-/

namespace Podc.ReadUpdateTradeoffs.AlgA

/-- Position of the leaf of `T_L` for value `v`: under node `2`, path `1^b 0 t` where
`b = ⌊log₂(v+1)⌋` and `t` = the `b` low bits of `v + 1` (a `B₁`-like tree, Bentley–Yao). -/
def tlPos (v : ℕ) : ℕ :=
  (3 * 2 ^ (Nat.log 2 (v + 1) + 1) - 2) * 2 ^ Nat.log 2 (v + 1) + (v + 1 - 2 ^ Nat.log 2 (v + 1))

/-- Position of the `i`-th leaf of `T_R` (a complete tree with `2^⌈log₂ N⌉ ≥ N` leaves under
node `3`). -/
def trPos (N i : ℕ) : ℕ := 3 * 2 ^ Nat.clog 2 N + i

/-- Arithmetic characterisation of `tlPos v` in terms of `u = 2 ^ ⌊log₂(v+1)⌋`. -/
lemma tlPos_spec (v : ℕ) :
    2 ^ Nat.log 2 (v + 1) ≤ v + 1 ∧ v + 1 < 2 * 2 ^ Nat.log 2 (v + 1) ∧
      tlPos v + 3 * 2 ^ Nat.log 2 (v + 1) = 6 * (2 ^ Nat.log 2 (v + 1)) ^ 2 + v + 1 := by
  have h1 : 2 ^ Nat.log 2 (v + 1) ≤ v + 1 := Nat.pow_log_le_self 2 (by omega)
  have h2 : v + 1 < 2 * 2 ^ Nat.log 2 (v + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (v + 1)
    rw [pow_succ] at this; linarith
  refine ⟨h1, h2, ?_⟩
  unfold tlPos
  rw [pow_succ]
  generalize 2 ^ Nat.log 2 (v + 1) = u at *
  obtain ⟨c, rfl⟩ : ∃ c, u = c + 1 := ⟨u - 1, by omega⟩
  have : 3 * ((c + 1) * 2) - 2 = 6 * c + 4 := by omega
  rw [this]
  have : v + 1 - (c + 1) = v - c := by omega
  rw [this]
  have : (6 * c + 4) * (c + 1) + (v - c) + 3 * (c + 1) = 6 * (c + 1) ^ 2 + (v - c) + c + 1 := by
    ring
  omega

/-- `T_L` leaf `v` lies at depth `2 ⌊log₂(v+1)⌋ + 2`. -/
theorem log_tlPos (v : ℕ) : Nat.log 2 (tlPos v) = 2 * Nat.log 2 (v + 1) + 2 := by
  obtain ⟨h1, h2, h3⟩ := tlPos_spec v
  rw [Nat.log_eq_iff (Or.inl (by omega))]
  rw [show 2 ^ (2 * Nat.log 2 (v + 1) + 2) = 4 * (2 ^ Nat.log 2 (v + 1)) ^ 2 by ring,
    show 2 ^ (2 * Nat.log 2 (v + 1) + 2 + 1) = 8 * (2 ^ Nat.log 2 (v + 1)) ^ 2 by ring]
  generalize 2 ^ Nat.log 2 (v + 1) = u at *
  constructor <;> nlinarith

/-- `T_R` leaf `i < N` lies at depth `⌈log₂ N⌉ + 1`. -/
theorem log_trPos {N i : ℕ} (hi : i < N) : Nat.log 2 (trPos N i) = Nat.clog 2 N + 1 := by
  have hw : N ≤ 2 ^ Nat.clog 2 N := Nat.le_pow_clog (by norm_num) N
  unfold trPos
  rw [Nat.log_eq_iff (Or.inl (by omega)),
    show 2 ^ (Nat.clog 2 N + 1) = 2 * 2 ^ Nat.clog 2 N by ring,
    show 2 ^ (Nat.clog 2 N + 1 + 1) = 4 * 2 ^ Nat.clog 2 N by ring]
  generalize 2 ^ Nat.clog 2 N = w at *
  omega

/-- `T_L` positions have top bits `10`. -/
lemma tlPos_top (v : ℕ) : 2 * (tlPos v + 1) ≤ 3 * 2 ^ Nat.log 2 (tlPos v) := by
  obtain ⟨h1, h2, h3⟩ := tlPos_spec v
  rw [log_tlPos, show 2 ^ (2 * Nat.log 2 (v + 1) + 2) = 4 * (2 ^ Nat.log 2 (v + 1)) ^ 2 by ring]
  generalize 2 ^ Nat.log 2 (v + 1) = u at *
  nlinarith

/-- `T_R` positions have top bits `11`. -/
lemma trPos_top {N i : ℕ} (hi : i < N) : 3 * 2 ^ Nat.log 2 (trPos N i) ≤ 2 * trPos N i := by
  rw [log_trPos hi, pow_succ]
  unfold trPos
  omega

/-- `T_L` leaves are at depth `≥ 2`. -/
lemma tlPos_ge (v : ℕ) : 4 ≤ tlPos v := by
  obtain ⟨h1, h2, h3⟩ := tlPos_spec v
  generalize 2 ^ Nat.log 2 (v + 1) = u at *
  nlinarith

/-- If `x / 2^k = y ≠ 0` then `x` is `k` levels deeper than `y`. -/
lemma log_of_div {x y k : ℕ} (h : x / 2 ^ k = y) (hy : y ≠ 0) :
    Nat.log 2 x = Nat.log 2 y + k := by
  have hK : 0 < 2 ^ k := by positivity
  have h1 : y * 2 ^ k ≤ x := h ▸ Nat.div_mul_le_self x (2 ^ k)
  have h2 : x < (y + 1) * 2 ^ k := by
    have := Nat.lt_mul_div_succ x hK
    rw [h] at this; linarith
  have h3 : 2 ^ Nat.log 2 y ≤ y := Nat.pow_log_le_self 2 hy
  have h4 : y < 2 ^ (Nat.log 2 y + 1) := Nat.lt_pow_succ_log_self (by norm_num) y
  have hx : x ≠ 0 := by
    intro hx; subst hx; simp at h; exact hy h.symm
  rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, hx⟩), pow_add,
    show Nat.log 2 y + k + 1 = (Nat.log 2 y + 1) + k by ring, pow_add]
  constructor
  · calc 2 ^ Nat.log 2 y * 2 ^ k ≤ y * 2 ^ k := Nat.mul_le_mul_right _ h3
      _ ≤ x := h1
  · calc x < (y + 1) * 2 ^ k := h2
      _ ≤ 2 ^ (Nat.log 2 y + 1) * 2 ^ k := Nat.mul_le_mul_right _ h4

/-- A position with top bits `10` and one with top bits `11` are never related by
`· / 2 ^ k`. -/
lemma no_cross {x y k : ℕ} (hx : 2 * (x + 1) ≤ 3 * 2 ^ Nat.log 2 x)
    (hy : 3 * 2 ^ Nat.log 2 y ≤ 2 * y) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    x / 2 ^ k ≠ y ∧ y / 2 ^ k ≠ x := by
  constructor
  · intro h
    have hl := log_of_div h hy0
    have h1 : y * 2 ^ k ≤ x := h ▸ Nat.div_mul_le_self x (2 ^ k)
    rw [hl, pow_add] at hx
    have := Nat.mul_le_mul_right (2 ^ k) hy
    nlinarith
  · intro h
    have hl := log_of_div h hx0
    have h2 : y < (x + 1) * 2 ^ k := by
      have := Nat.lt_mul_div_succ y (show 0 < 2 ^ k by positivity)
      rw [h] at this; linarith
    rw [hl, pow_add] at hy
    have := Nat.mul_le_mul_right (2 ^ k) hx
    nlinarith

/-- No `T_L` leaf is a proper ancestor of another `T_L` leaf. -/
lemma tl_not_anc {v v' k : ℕ} (hk : 0 < k) : tlPos v / 2 ^ k ≠ tlPos v' := by
  intro h
  have hl := log_of_div h (by have := tlPos_ge v'; omega)
  rw [log_tlPos, log_tlPos] at hl
  set b := Nat.log 2 (v + 1)
  set b' := Nat.log 2 (v' + 1)
  obtain ⟨m, hm, hkm⟩ : ∃ m, b = b' + m ∧ k = 2 * m := ⟨b - b', by omega, by omega⟩
  have hm1 : 1 ≤ m := by omega
  obtain ⟨h1, h2, h3⟩ := tlPos_spec v
  obtain ⟨h1', h2', h3'⟩ := tlPos_spec v'
  have hT : tlPos v < (tlPos v' + 1) * 2 ^ k := by
    have := Nat.lt_mul_div_succ (tlPos v) (show 0 < 2 ^ k by positivity)
    rw [h] at this; linarith
  change 2 ^ b ≤ v + 1 at h1
  change v + 1 < 2 * 2 ^ b at h2
  change tlPos v + 3 * 2 ^ b = 6 * (2 ^ b) ^ 2 + v + 1 at h3
  change 2 ^ b' ≤ v' + 1 at h1'
  change v' + 1 < 2 * 2 ^ b' at h2'
  change tlPos v' + 3 * 2 ^ b' = 6 * (2 ^ b') ^ 2 + v' + 1 at h3'
  have hp : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  have hu' : 1 ≤ 2 ^ b' := Nat.one_le_two_pow
  rw [hm, pow_add] at h1 h2 h3
  rw [hkm, show 2 * m = m + m by ring, pow_add] at hT
  generalize 2 ^ b' = u at *
  generalize 2 ^ m = p at *
  generalize tlPos v = T at *
  generalize tlPos v' = T' at *
  -- `T + 2 u p ≥ 6 (u p)^2` and `T' + u + 1 ≤ 6 u^2`
  have hA : 6 * (u * p) ^ 2 ≤ T + 2 * (u * p) := by nlinarith
  have hB : T' + u + 1 ≤ 6 * u ^ 2 := by nlinarith
  have hC := Nat.mul_le_mul_right (p * p) hB
  have hD : u * p * 2 ≤ u * p * p := Nat.mul_le_mul_left _ hp
  nlinarith

/-- The standard layout: `T_L` a `B₁`-like tree under node `2`, `T_R` a complete tree under
node `3`. -/
def stdLayout (N : ℕ) : Layout N where
  leaf
    | .inl v => tlPos v
    | .inr i => trPos N i
  two_le a := by
    rcases a with v | i
    · have := tlPos_ge v; simp only; omega
    · simp only [trPos]; have : 1 ≤ 2 ^ Nat.clog 2 N := Nat.one_le_two_pow; omega
  inj a b h := by
    rcases a with v | i <;> rcases b with v' | i' <;> simp only at h
    · congr 1
      apply Fin.ext
      have hl := congrArg (Nat.log 2) h
      rw [log_tlPos, log_tlPos] at hl
      have hb : Nat.log 2 (v.1 + 1) = Nat.log 2 (v'.1 + 1) := by omega
      have h3 := (tlPos_spec v).2.2
      have h3' := (tlPos_spec v').2.2
      rw [hb, h] at h3
      omega
    · exfalso
      have := (no_cross (k := 0) (tlPos_top v) (trPos_top i'.2)
        (by have := tlPos_ge v; omega) (by unfold trPos; positivity)).1
      simp at this; exact this h
    · exfalso
      have := (no_cross (k := 0) (tlPos_top v') (trPos_top i.2)
        (by have := tlPos_ge v'; omega) (by unfold trPos; positivity)).1
      simp at this; exact this h.symm
    · congr 1; apply Fin.ext; unfold trPos at h; omega
  not_anc a b k hk := by
    rcases a with v | i <;> rcases b with v' | i' <;> simp only
    · exact tl_not_anc hk
    · exact (no_cross (tlPos_top v) (trPos_top i'.2)
        (by have := tlPos_ge v; omega) (by unfold trPos; positivity)).1
    · exact (no_cross (tlPos_top v') (trPos_top i.2)
        (by have := tlPos_ge v'; omega) (by unfold trPos; positivity)).2
    · intro h
      have hl := log_of_div h (by unfold trPos; positivity)
      rw [log_trPos i.2, log_trPos i'.2] at hl
      omega

@[simp] lemma stdLayout_leaf_inl (N : ℕ) (v : Fin N) : (stdLayout N).leaf (.inl v) = tlPos v :=
  rfl

@[simp] lemma stdLayout_leaf_inr (N : ℕ) (i : Fin N) : (stdLayout N).leaf (.inr i) = trPos N i :=
  rfl

/-- The leaf written by `WriteMax(v)` in the standard layout has depth at most
`2 ⌊log₂ (min N (v+1))⌋ + 2`. -/
theorem log_leafOf_le (N : ℕ) (p : Fin N) (v : ℕ) :
    Nat.log 2 ((stdLayout N).leafOf p v) ≤ 2 * Nat.log 2 (min N (v + 1)) + 2 := by
  unfold Layout.leafOf
  split_ifs with h
  · rw [stdLayout_leaf_inl, log_tlPos, min_eq_right (by omega)]
  · rw [stdLayout_leaf_inr, log_trPos p.2, min_eq_left (by omega)]
    have : Nat.clog 2 N ≤ Nat.log 2 N + 1 :=
      Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by norm_num) N).le
    omega

end Podc.ReadUpdateTradeoffs.AlgA
