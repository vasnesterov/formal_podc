import Papers.PODC2017.LCLGrids.Basic

/-!
# Lemma 12: the intersection number of a cycle of `H` is the same for all rows

Section 9 of Brandt et al., *LCL problems on grids* (PODC 2017).

A directed cycle of `H` is modelled as a closed walk `γ : ZMod m → Pos n`: position `i` has
predecessor `γ (i - 1)` and successor `γ (i + 1)`. Position `i` is a *northbound intersection* on
row `r` if `γ (i - 1)`, `γ i`, `γ (i + 1)` lie on rows `r - 1`, `r`, `r + 1`, and *southbound* if
they lie on rows `r + 1`, `r`, `r - 1`. The intersection number is
`crossing γ r = northCount γ r - southCount γ r`.

## Main results

* `crossing_eq_of_rows`: for any closed walk that moves one row up or down at every step,
  `crossing γ r` does not depend on `r`;
* `lemma12`: in particular this holds for closed walks along edges of `H` (Lemma 12).

## Proof

`crossing γ r` equals the net number of steps from row `r - 1` up to row `r` (pointwise: a visit of
row `r` that arrives from below and leaves downwards contributes `1 - 1`), and the difference of
the net numbers for consecutive rows `r - 1 → r` and `r → r + 1` telescopes to
`∑ i, ([γ (i + 1) on row r] - [γ i on row r]) = 0`.

No assumption on the grid size is needed: if `2 = 0` in `ZMod n` (i.e. `n ≤ 2`), then
`r - 1 = r + 1` and both counts coincide, so `crossing γ r = 0`.
-/

namespace Podc.LCLGrids

section pointwise

variable {R : Type*} [CommRing R] [DecidableEq R]

omit [DecidableEq R] in
private lemma ne_of_two (h2 : (2 : R) ≠ 0) (r : R) : r + 1 ≠ r - 1 := fun h =>
  h2 (by linear_combination h)

private lemma pt1 (h2 : (2 : R) ≠ 0) (a x b r : R) (ha : x = a + 1 ∨ x = a - 1)
    (hb : b = x + 1 ∨ b = x - 1) :
    ((if a = r - 1 ∧ x = r ∧ b = r + 1 then 1 else 0 : ℤ) -
      if a = r + 1 ∧ x = r ∧ b = r - 1 then 1 else 0) =
      (if a = r - 1 ∧ x = r then 1 else 0 : ℤ) - if x = r ∧ b = r - 1 then 1 else 0 := by
  have hne := ne_of_two h2 r
  have hne' := hne.symm
  by_cases hx : x = r
  · subst hx
    have ha' : a = x - 1 ∨ a = x + 1 := by
      rcases ha with h | h
      · left; linear_combination -h
      · right; linear_combination -h
    rcases ha' with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hne, hne']
  · simp [hx]

private lemma pt2 (h2 : (2 : R) ≠ 0) (x y r : R) (hy : y = x + 1 ∨ y = x - 1) :
    ((if x = r - 1 ∧ y = r then 1 else 0 : ℤ) - (if x = r ∧ y = r - 1 then 1 else 0)) -
      ((if x = r ∧ y = r + 1 then 1 else 0 : ℤ) - (if x = r + 1 ∧ y = r then 1 else 0)) =
      (if y = r then 1 else 0 : ℤ) - if x = r then 1 else 0 := by
  have h1 : (1 : R) ≠ 0 := fun h => h2 (by linear_combination 2 * h)
  have e1 : r - 1 ≠ r := fun h => h1 (by linear_combination -h)
  have e2 : r + 1 ≠ r := fun h => h1 (by linear_combination h)
  have e3 : r + 1 + 1 ≠ r := fun h => h2 (by linear_combination h)
  have e4 : r - 1 - 1 ≠ r := fun h => h2 (by linear_combination -h)
  have e5 := ne_of_two h2 r
  have e1' := e1.symm; have e2' := e2.symm; have e3' := e3.symm; have e4' := e4.symm
  have e5' := e5.symm
  by_cases hx1 : x = r - 1
  · subst hx1; rcases hy with rfl | rfl <;> simp [*]
  by_cases hx2 : x = r
  · subst hx2; rcases hy with rfl | rfl <;> simp [*]
  by_cases hx3 : x = r + 1
  · subst hx3; rcases hy with rfl | rfl <;> simp [*]
  have hyr : y ≠ r := by
    rcases hy with rfl | rfl
    · exact fun h => hx1 (by linear_combination h)
    · exact fun h => hx3 (by linear_combination h)
  simp [hx1, hx2, hx3, hyr]

end pointwise

variable {n m : ℕ} [NeZero m]

/-- Number of northbound intersections of the closed walk `γ` on row `r`: positions `i` with the
predecessor on row `r - 1`, `γ i` on row `r` and the successor on row `r + 1`. -/
def northCount (γ : ZMod m → Pos n) (r : ZMod n) : ℕ :=
  (Finset.univ.filter fun i =>
    (γ (i - 1)).2 = r - 1 ∧ (γ i).2 = r ∧ (γ (i + 1)).2 = r + 1).card

/-- Number of southbound intersections of the closed walk `γ` on row `r`: positions `i` with the
predecessor on row `r + 1`, `γ i` on row `r` and the successor on row `r - 1`. -/
def southCount (γ : ZMod m → Pos n) (r : ZMod n) : ℕ :=
  (Finset.univ.filter fun i =>
    (γ (i - 1)).2 = r + 1 ∧ (γ i).2 = r ∧ (γ (i + 1)).2 = r - 1).card

/-- The intersection number `i_r(γ) = north_r(γ) - south_r(γ)` of the closed walk `γ` with
row `r`. -/
def crossing (γ : ZMod m → Pos n) (r : ZMod n) : ℤ :=
  northCount γ r - southCount γ r

/-- Net number of steps of `γ` from row `r - 1` up to row `r` (upward minus downward steps). -/
private def net (γ : ZMod m → Pos n) (r : ZMod n) : ℤ :=
  ∑ i, ((if (γ i).2 = r - 1 ∧ (γ (i + 1)).2 = r then 1 else 0) -
    if (γ i).2 = r ∧ (γ (i + 1)).2 = r - 1 then 1 else 0)

section walk

variable {γ : ZMod m → Pos n}
  (hγ : ∀ i, (γ (i + 1)).2 = (γ i).2 + 1 ∨ (γ (i + 1)).2 = (γ i).2 - 1)
include hγ

private lemma crossing_eq_net (h2 : (2 : ZMod n) ≠ 0) (r : ZMod n) :
    crossing γ r = net γ r := by
  have hc : crossing γ r = ∑ i, ((if (γ (i - 1)).2 = r - 1 ∧ (γ i).2 = r then 1 else 0) -
      if (γ i).2 = r ∧ (γ (i + 1)).2 = r - 1 then 1 else 0) := by
    rw [crossing, northCount, southCount, Finset.natCast_card_filter,
      Finset.natCast_card_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => pt1 h2 _ _ _ r ?_ (hγ i)
    have := hγ (i - 1)
    rwa [sub_add_cancel] at this
  rw [hc, net, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  refine (Equiv.sum_comp (Equiv.addRight (1 : ZMod m)) _).symm.trans ?_
  simp

private lemma net_add_one (h2 : (2 : ZMod n) ≠ 0) (r : ZMod n) : net γ r = net γ (r + 1) := by
  rw [← sub_eq_zero, net, net, ← Finset.sum_sub_distrib]
  have key : ∀ i, (((if (γ i).2 = r - 1 ∧ (γ (i + 1)).2 = r then 1 else 0 : ℤ) -
      if (γ i).2 = r ∧ (γ (i + 1)).2 = r - 1 then 1 else 0) -
      ((if (γ i).2 = r + 1 - 1 ∧ (γ (i + 1)).2 = r + 1 then 1 else 0) -
      if (γ i).2 = r + 1 ∧ (γ (i + 1)).2 = r + 1 - 1 then 1 else 0)) =
      (if (γ (i + 1)).2 = r then 1 else 0) - if (γ i).2 = r then 1 else 0 := fun i => by
    simpa only [add_sub_cancel_right] using pt2 h2 _ _ r (hγ i)
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib, sub_eq_zero]
  exact Equiv.sum_comp (Equiv.addRight (1 : ZMod m)) (fun i => if (γ i).2 = r then 1 else 0)

/-- The intersection number of a closed walk that moves one row up or down at every step is the
same for all rows (Lemma 12 for walks). -/
theorem crossing_eq_of_rows (r₁ r₂ : ZMod n) : crossing γ r₁ = crossing γ r₂ := by
  by_cases h2 : (2 : ZMod n) = 0
  · have e : ∀ r : ZMod n, r + 1 = r - 1 := fun r => by linear_combination h2
    simp only [crossing, northCount, southCount, e, sub_self]
  have hk : ∀ k : ℤ, net γ r₁ = net γ (r₁ + k) := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih => rw [ih, net_add_one hγ h2]; push_cast; rw [add_assoc]
    | pred k ih =>
      rw [ih, net_add_one hγ h2 (r₁ + ((-(k : ℤ) - 1 : ℤ) : ZMod n))]; push_cast; ring_nf
  rw [crossing_eq_net hγ h2, crossing_eq_net hγ h2, hk ((r₂ - r₁ : ZMod n).cast),
    ZMod.intCast_zmod_cast, add_sub_cancel]

end walk

/-- Lemma 12 of [Brandt et al., *LCL problems on grids*, PODC 2017]: for a directed cycle `C` of
`H` (here: a closed walk `γ : ℤ/m → Pos n` along edges of `H`), the intersection number
`i_r(C) = north_r(C) - south_r(C)` does not depend on the row `r`. (The paper works on tori with
`n ≥ 5`; no lower bound on `n` is needed here.) -/
theorem lemma12 (c : Pos n → Col) (γ : ZMod m → Pos n)
    (hγ : ∀ i, ∃ d, HEdge c (γ i) d ∧ γ (i + 1) = step (γ i) d) (r₁ r₂ : ZMod n) :
    crossing γ r₁ = crossing γ r₂ := by
  refine crossing_eq_of_rows (fun i => ?_) r₁ r₂
  obtain ⟨d, -, hd⟩ := hγ i
  rw [hd]
  cases d <;> simp [step, sh, Diag.dy, sub_eq_add_neg]

end Podc.LCLGrids
