import Papers.PODC2017.LCLGrids.Basic

/-!
# The row invariant `s` of a proper 3-colouring (Lemmas 12 and 14)

For a colouring `c` of the toroidal `n × n` grid, `rowSum c r = ∑_x ℓ(x, r)` is the sum of the
labels of Lemma 14 along row `r`. The paper writes `s(G) = ∑_{C ∈ 𝒞} i_r(C)` for a decomposition
`𝒞` of `H` into directed cycles and observes `s(G) = ∑_v ℓ(v)` ("directly by definitions").

* `rowSum_eq_flux`, `rowSum_succ`, `rowSum_eq`: for a proper colouring, `rowSum c r` is the net
  number of `H`-edges crossing from row `r - 1` to row `r`, hence independent of `r` (the
  corollary of Lemma 12; `H` is Eulerian by `indeg_eq_outdeg`);
* `rowSum_cast_two`, `odd_rowSum` (Lemma 14, parity): `rowSum c r ≡ n (mod 2)`, so it is odd for
  odd `n`;
* `two_mul_abs_rowSum_le` (Lemma 14, bound): `|rowSum c r| ≤ n / 2`.

None of these needs the colouring to be greedy (the paper first makes it greedy by a
constant-round post-processing step); properness suffices.
-/

namespace Podc.LCLGrids

open Finset

variable {n : ℕ}

/-- The sum of the labels `ℓ(v)` along row `r`. -/
def rowSum [NeZero n] (c : Pos n → Col) (r : ZMod n) : ℤ := ∑ x : ZMod n, ell c (x, r)

section flux

variable (c : Pos n → Col)

/-- Indicator of an `H`-edge, as an integer. -/
def he (u : Pos n) (d : Diag) : ℤ := if HEdge c u d then 1 else 0

lemma step_ne' (x y : ZMod n) : step (x, y) .ne = (x + 1, y + 1) := by
  simp [step, sh, Diag.dx, Diag.dy]
lemma step_nw' (x y : ZMod n) : step (x, y) .nw = (x - 1, y + 1) := by
  simp [step, sh, Diag.dx, Diag.dy, sub_eq_add_neg]
lemma step_sw' (x y : ZMod n) : step (x, y) .sw = (x - 1, y - 1) := by
  simp [step, sh, Diag.dx, Diag.dy, sub_eq_add_neg]
lemma step_se' (x y : ZMod n) : step (x, y) .se = (x + 1, y - 1) := by
  simp [step, sh, Diag.dx, Diag.dy, sub_eq_add_neg]

lemma inBelow_eq' (v : Pos n) :
    (inBelow c v : ℤ) = he c (step v .sw) .ne + he c (step v .se) .nw := by
  rw [inBelow, Diag.card_filter]
  simp [List.countP_cons, Diag.IsDown, Diag.dy, Diag.neg, he]
  split_ifs <;> simp

lemma outBelow_eq' (v : Pos n) :
    (outBelow c v : ℤ) = he c v .sw + he c v .se := by
  rw [outBelow, Diag.card_filter]
  simp [List.countP_cons, Diag.IsDown, Diag.dy, he]
  split_ifs <;> simp

lemma inAbove_eq' (v : Pos n) :
    (inAbove c v : ℤ) = he c (step v .ne) .sw + he c (step v .nw) .se := by
  rw [inAbove, Diag.card_filter]
  simp [List.countP_cons, Diag.IsDown, Diag.dy, Diag.neg, he]
  split_ifs <;> simp

lemma outAbove_eq' (v : Pos n) :
    (outAbove c v : ℤ) = he c v .ne + he c v .nw := by
  rw [outAbove, Diag.card_filter]
  simp [List.countP_cons, Diag.IsDown, Diag.dy, he]
  split_ifs <;> simp

lemma indeg_split (v : Pos n) : (indeg c v : ℤ) = inBelow c v + inAbove c v := by
  have : (indeg c v : ℤ) = he c (step v .sw) .ne + he c (step v .se) .nw +
      (he c (step v .ne) .sw + he c (step v .nw) .se) := by
    rw [indeg, Diag.card_filter]
    simp [List.countP_cons, he, Diag.neg]
    split_ifs <;> first | rfl | (exfalso; simp_all)
  rw [this, inBelow_eq', inAbove_eq']

lemma outdeg_split (v : Pos n) : (outdeg c v : ℤ) = outBelow c v + outAbove c v := by
  have : (outdeg c v : ℤ) = he c v .sw + he c v .se + (he c v .ne + he c v .nw) := by
    rw [outdeg, Diag.card_filter]
    simp [List.countP_cons, he]
    split_ifs <;> rfl
  rw [this, outBelow_eq', outAbove_eq']

variable [NeZero n]

/-- Reindexing a sum over a row by a translation. -/
lemma sum_shift (f : ZMod n → ℤ) (a : ZMod n) : ∑ x, f (x + a) = ∑ x, f x :=
  Equiv.sum_comp (Equiv.addRight a) f

/-- The edges entering row `r + 1` from below are the edges leaving row `r` upwards. -/
lemma sum_inBelow_succ (r : ZMod n) :
    ∑ x, (inBelow c (x, r + 1) : ℤ) = ∑ x, (outAbove c (x, r) : ℤ) := by
  simp only [inBelow_eq', outAbove_eq', sum_add_distrib, step_sw', step_se', add_sub_cancel_right]
  congr 1
  · exact sum_shift (fun x => he c (x, r) .ne) (-1) |>.symm.trans (by simp [sub_eq_add_neg]) |>.symm
  · exact sum_shift (fun x => he c (x, r) .nw) 1

/-- The edges leaving row `r + 1` downwards are the edges entering row `r` from above. -/
lemma sum_outBelow_succ (r : ZMod n) :
    ∑ x, (outBelow c (x, r + 1) : ℤ) = ∑ x, (inAbove c (x, r) : ℤ) := by
  simp only [inAbove_eq', outBelow_eq', sum_add_distrib, step_ne', step_nw']
  congr 1
  · exact (sum_shift (fun x => he c (x, r + 1) .sw) 1).symm
  · exact (sum_shift (fun x => he c (x, r + 1) .se) (-1)).symm.trans (by simp [sub_eq_add_neg])

variable {c}

/-- For a proper colouring, the row sum is the net number of `H`-edges from row `r - 1` to row
`r` (edges entering row `r` from below minus edges leaving it downwards). -/
lemma rowSum_eq_flux (hc : IsProper c) (r : ZMod n) :
    rowSum c r = ∑ x, ((inBelow c (x, r) : ℤ) - outBelow c (x, r)) := by
  simp only [rowSum, ell_eq _ hc]

/-- Corollary of Lemma 12: the row sum does not depend on the row. -/
theorem rowSum_succ (hc : IsProper c) (r : ZMod n) : rowSum c (r + 1) = rowSum c r := by
  rw [rowSum_eq_flux hc, rowSum_eq_flux hc, sum_sub_distrib, sum_inBelow_succ,
    sum_outBelow_succ, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  have h := congrArg (fun k : ℕ => (k : ℤ)) (indeg_eq_outdeg (x, r) hc)
  simp only [indeg_split, outdeg_split] at h
  linarith

/-- Corollary of Lemma 12: `∑_{C ∈ 𝒞} i_{r₁}(C) = ∑_{C ∈ 𝒞} i_{r₂}(C)`, in the form
`rowSum c r₁ = rowSum c r₂`. -/
theorem rowSum_eq (hc : IsProper c) (r₁ r₂ : ZMod n) : rowSum c r₁ = rowSum c r₂ := by
  have key : ∀ k : ℕ, rowSum c (r₁ + k) = rowSum c r₁ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, ← add_assoc, rowSum_succ hc, ih]
  have := key (r₂ - r₁).val
  rw [ZMod.natCast_zmod_val, add_sub_cancel] at this
  exact this.symm

end flux

/-! ### Lemma 14 -/

section lemma14

variable {c : Pos n → Col}

/-- `0` for colour `1`, `1` otherwise. -/
def bit (k : Col) : ZMod 2 := if k = .one then 0 else 1

/-- Indicator of colour `3`, in `ZMod 2`. -/
def is3 (k : Col) : ZMod 2 := if k = .three then 1 else 0

lemma ell_cast_two (v : Pos n) : (ell c v : ZMod 2) = if ell c v = 0 then 0 else 1 := by
  rcases ell_mem (c := c) v with h | h | h <;> rw [h] <;> decide

/-- The pointwise identity behind the parity part of Lemma 14. Let `g x` be the colour of
`(x, r)` if it is not `3`, and the colour of its western neighbour otherwise; then
`ℓ(x) = [g(x+1) ≠ g(x)] + 1 + [c(x) = 3] + [c(x+1) = 3]` modulo `2`. -/
lemma ell_two_pointwise (hc : IsProper c) (x r : ZMod n) :
    let g : ZMod n → Col := fun x => if c (x, r) = .three then c (x - 1, r) else c (x, r)
    (ell c (x, r) : ZMod 2) =
      (bit (g (x + 1)) + bit (g x)) + 1 + is3 (c (x, r)) + is3 (c (x + 1, r)) := by
  intro g
  have hE := (hc (x, r)).1
  have hW := (hc (x - 1, r)).1
  simp only [sh, Int.cast_one, Int.cast_zero, add_zero, sub_add_cancel] at hE hW
  rw [ell_cast_two]
  by_cases h3 : c (x, r) = .three
  · have hne := ell_ne_zero_iff (x, r) hc h3
    simp only [sh, Int.cast_neg, Int.cast_one, Int.cast_zero, add_zero, ← sub_eq_add_neg] at hne
    have h3' : c (x + 1, r) ≠ .three := fun h => hE (h3.trans h.symm)
    have hW3 : c (x - 1, r) ≠ .three := fun h => hW (h.trans h3.symm)
    simp only [g, h3, h3', ite_true, ite_false, add_sub_cancel_right, is3]
    by_cases h0 : ell c (x, r) = 0
    · have : c (x - 1, r) = c (x + 1, r) := by
        by_contra hh; exact (hne.2 hh) h0
      rw [ite_eq_left_of_eq_true _ _ (eq_true h0), this]
      generalize c (x + 1, r) = k at *
      cases k <;> simp [bit] at * <;> decide
    · have : c (x - 1, r) ≠ c (x + 1, r) := hne.1 h0
      rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
      revert this hW3 h3'
      generalize c (x + 1, r) = k
      generalize c (x - 1, r) = k'
      cases k <;> cases k' <;> simp [bit] <;> decide
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (ell_eq_zero_of_ne_three _ h3))]
    by_cases h3' : c (x + 1, r) = .three
    · simp only [g, h3, h3', ite_true, ite_false, add_sub_cancel_right, is3]
      generalize c (x, r) = k at *
      cases k <;> simp [bit] at * <;> decide
    · simp only [g, h3, h3', ite_false, is3]
      revert hE h3 h3'
      generalize c (x + 1, r) = k
      generalize c (x, r) = k'
      cases k <;> cases k' <;> simp [bit] <;> decide

variable [NeZero n]

/-- Lemma 14 (parity), general form: `s ≡ n (mod 2)`. -/
theorem rowSum_cast_two (hc : IsProper c) (r : ZMod n) : (rowSum c r : ZMod 2) = n := by
  set g : ZMod n → Col := fun x => if c (x, r) = .three then c (x - 1, r) else c (x, r)
  have hsum : (rowSum c r : ZMod 2) =
      ∑ x : ZMod n, ((bit (g (x + 1)) + bit (g x)) + 1 + is3 (c (x, r)) + is3 (c (x + 1, r))) := by
    rw [rowSum, Int.cast_sum]
    exact sum_congr rfl fun x _ => ell_two_pointwise hc x r
  have shift : ∀ f : ZMod n → ZMod 2, ∑ x, f (x + 1) = ∑ x, f x :=
    fun f => Equiv.sum_comp (Equiv.addRight 1) f
  rw [hsum, sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib,
    shift (fun x => bit (g x)), shift (fun x => is3 (c (x, r)))]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  rw [h2, zero_add, add_assoc, h2, add_zero]

/-- Lemma 14 (parity): if `n` is odd, then `s(n)` is odd. -/
theorem odd_rowSum (hc : IsProper c) (hn : Odd n) (r : ZMod n) : Odd (rowSum c r) := by
  rw [← ZMod.intCast_eq_one_iff_odd, rowSum_cast_two hc r]
  exact (ZMod.natCast_eq_one_iff_odd).2 hn

/-- Lemma 14 (bound): `|s(n)| ≤ n / 2`, in the form `2 |s| ≤ n`. Only colour-3 nodes have a
nonzero label, and colour-3 nodes are not adjacent along the row. -/
theorem two_mul_abs_rowSum_le (hc : IsProper c) (r : ZMod n) : 2 * |rowSum c r| ≤ n := by
  let t : ZMod n → ℤ := fun x => if c (x, r) = .three then 1 else 0
  have h1 : |rowSum c r| ≤ ∑ x, t x := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
    by_cases h : c (x, r) = .three
    · simp only [t, h, ite_true]; rcases ell_mem (c := c) (x, r) with e | e | e <;> rw [e] <;> simp
    · simp [t, h, ell_eq_zero_of_ne_three _ h]
  have h2 : ∀ x, t x + t (x + 1) ≤ 1 := by
    intro x
    have hE := (hc (x, r)).1
    simp only [sh, Int.cast_one, Int.cast_zero, add_zero] at hE
    simp only [t]; split_ifs with a b <;> simp_all
  have h3 : ∑ x, (t x + t (x + 1)) ≤ ∑ _x : ZMod n, (1 : ℤ) := sum_le_sum fun x _ => h2 x
  rw [sum_add_distrib, sum_shift t 1] at h3
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one] at h3
  linarith

end lemma14

end Podc.LCLGrids
