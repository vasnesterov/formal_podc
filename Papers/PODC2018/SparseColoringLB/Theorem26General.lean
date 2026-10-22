import Papers.PODC2018.SparseColoringLB.Theorem26Counterexample

/-!
# Theorem 2.6 is false for every odd `k = 2t + 1 ≥ 3`

`Theorem26Counterexample` reduces the counterexample to Theorem 2.6 of the paper to a purely
combinatorial fact about the `(2t+1) × (2t+1)` grid and checks it for `k ≤ 11` by computation.
Here we prove that fact for every `t`: the number `σ` of grid points at `ℓ₁`-distance exactly `t`
from `p = (x, y)` determines the parity of `x + y`.

Explicitly, with `a = min x (2t - x)`, `b = min y (2t - y)` (both in `[0, t]`, `a + b ≡ x + y`):
* `a, b < t`, `a + b < t`: `σ = t + 1 + (a + b)` (range `[t+1, 2t]`);
* `a, b < t`, `a + b ≥ t`: `σ = 2 (a + b) + 2` (even, range `[2t+2, 4t-2]`);
* exactly one of `a, b` (say `a`) equals `t`: `σ = 2t + 1 + 2b` (odd, `≥ 2t+1`), `a + b = t + b`;
* `a = b = t`: `σ = 4t`.
So `σ` determines `a + b`. The count is obtained by summing, row by row, the number of columns at
the right distance (`sum_row`), and then counting the rows whose distance to `x` lies in an interval
(`sum_interval`).
-/

namespace Podc.SparseColoringLB

open Finset Cslib.Local

private lemma sum_interval_aux (x lo hi n : ℕ) :
    ∑ i ∈ range n, (if lo ≤ max x i - min x i ∧ max x i - min x i ≤ hi then 1 else 0) =
      (min n (x + hi + 1) - (x + lo)) +
      (if max lo 1 ≤ x then min n (x + 1 - max lo 1) - (x - hi) else 0) := by
  induction n with
  | zero => rw [sum_range_zero]; split_ifs <;> omega
  | succ n ih =>
    rw [sum_range_succ, ih]
    generalize hL : max lo 1 = L
    have hL1 : L = max lo 1 := hL.symm
    generalize hD : max x n - min x n = D
    have hD1 : D = max x n - min x n := hD.symm
    rw [Nat.max_def] at hL1
    rw [Nat.max_def, Nat.min_def] at hD1
    split_ifs at * <;> omega

/-- Number of `i < n` whose distance to `x` lies in `[lo, hi]`: the right part `i ≥ x` and the
left part `i < x` (the `max lo 1` avoids counting `i = x` twice). -/
private lemma sum_interval (x lo hi n : ℕ) :
    ∑ i ∈ range n, (if lo ≤ max x i - min x i ∧ max x i - min x i ≤ hi then 1 else 0) =
      (min n (x + hi + 1) - (x + lo)) + (min n (x + 1 - max lo 1) - (x - hi)) := by
  rw [sum_interval_aux]
  split_ifs <;> omega

/-- Number of `j < n` with `δ + |j - y| = t`. -/
private lemma sum_row (δ y t n : ℕ) :
    ∑ j ∈ range n, (if δ + (max y j - min y j) = t then 1 else 0) =
      (if δ ≤ t ∧ y + t < n + δ then 1 else 0) +
      (if δ < t ∧ t ≤ y + δ ∧ y + δ < n + t then 1 else 0) := by
  induction n with
  | zero => rw [sum_range_zero]; split_ifs <;> omega
  | succ n ih =>
    rw [sum_range_succ, ih]
    generalize hD : max y n - min y n = D
    have hD1 : D = max y n - min y n := hD.symm
    rw [Nat.max_def, Nat.min_def] at hD1
    split_ifs at * <;> omega

private lemma gridSphere_eq_sum {N : ℕ} (p : Fin N × Fin N) (d : ℕ) :
    gridSphere p d = ∑ i ∈ range N, ∑ j ∈ range N,
      (if (max (p.1 : ℕ) i - min (p.1 : ℕ) i) + (max (p.2 : ℕ) j - min (p.2 : ℕ) j) = d
        then 1 else 0) := by
  unfold gridSphere
  rw [card_filter, Fintype.sum_prod_type]
  simp only [Finset.sum_range, l1]
  rfl

/-- Closed form of the number of grid points at distance exactly `t` in the `(2t+1)`-grid. -/
private lemma gridSphere_closed (t : ℕ) (ht : 0 < t) (p : Fin (2 * t + 1) × Fin (2 * t + 1)) :
    gridSphere p t =
      ((min (2 * t + 1) (p.1 + t + 1) - (p.1 + (p.2 - t))) +
          (min (2 * t + 1) (p.1 + 1 - max (p.2 - t) 1) - (p.1 - t))) +
      ((min (2 * t + 1) (p.1 + (t - 1) + 1) - (p.1 + (t - p.2))) +
          (min (2 * t + 1) (p.1 + 1 - max (t - p.2) 1) - (p.1 - (t - 1)))) := by
  rw [gridSphere_eq_sum, ← sum_interval, ← sum_interval, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_row]
  have hy := p.2.isLt
  congr 1 <;> congr 1 <;> apply propext <;> omega

/-- The closed form in terms of `a = min x (2t - x)`, `b = min y (2t - y)`:
`σ + [a = t] + [b = t] = t + 1 + (a + b) + (a + b + 1 - t)`. -/
private lemma cases_of_closed (t x y σ : ℕ) (ht : 0 < t) (hx : x < 2 * t + 1)
    (hy : y < 2 * t + 1)
    (h : σ = ((min (2 * t + 1) (x + t + 1) - (x + (y - t))) +
          (min (2 * t + 1) (x + 1 - max (y - t) 1) - (x - t))) +
      ((min (2 * t + 1) (x + (t - 1) + 1) - (x + (t - y))) +
          (min (2 * t + 1) (x + 1 - max (t - y) 1) - (x - (t - 1))))) :
    ∃ a b : ℕ, a ≤ t ∧ b ≤ t ∧ (a + b) % 2 = (x + y) % 2 ∧
      σ + (if a = t then 1 else 0) + (if b = t then 1 else 0) =
        t + 1 + a + b + (a + b + 1 - t) := by
  have hmin : ∀ a b : ℕ, min a b = a - (a - b) := by intros; omega
  have hmax : ∀ a b : ℕ, max a b = a + (b - a) := by intros; omega
  simp only [hmin, hmax] at h
  generalize hP1 : 2 * t + 1 - (2 * t + 1 - (x + t + 1)) - (x + (y - t)) = P1 at h
  generalize hP2 :
    2 * t + 1 - (2 * t + 1 - (x + 1 - (y - t + (1 - (y - t))))) - (x - t) = P2 at h
  generalize hP3 : 2 * t + 1 - (2 * t + 1 - (x + (t - 1) + 1)) - (x + (t - y)) = P3 at h
  generalize hP4 :
    2 * t + 1 - (2 * t + 1 - (x + 1 - (t - y + (1 - (t - y))))) - (x - (t - 1)) = P4 at h
  clear hmin hmax
  rcases le_or_gt x t with hxt | hxt <;> rcases le_or_gt y t with hyt | hyt
  · refine ⟨x, y, hxt, hyt, rfl, ?_⟩
    have e1 : P1 = t + 1 := by clear hP2 hP3 hP4 h; omega
    have e2 : P2 = x := by clear hP1 hP3 hP4 h; omega
    have e3 : P3 = y := by clear hP2 hP1 hP4 h; omega
    have e4 : P4 = x + 1 - (t - y + (1 - (t - y))) - (x - (t - 1)) := by
      clear hP2 hP3 hP1 h; omega
    clear hP1 hP2 hP3 hP4
    split_ifs <;> omega
  · refine ⟨x, 2 * t - y, hxt, by omega, by omega, ?_⟩
    have e1 : P1 = 2 * t + 1 - y := by clear hP2 hP3 hP4 h; omega
    have e2 : P2 = x + 1 + t - y := by clear hP1 hP3 hP4 h; omega
    have e3 : P3 = t := by clear hP2 hP1 hP4 h; omega
    have e4 : P4 = x - (x - (t - 1)) := by clear hP2 hP3 hP1 h; omega
    clear hP1 hP2 hP3 hP4
    split_ifs <;> omega
  · refine ⟨2 * t - x, y, by omega, hyt, by omega, ?_⟩
    have e1 : P1 = 2 * t + 1 - x := by clear hP2 hP3 hP4 h; omega
    have e2 : P2 = t := by clear hP1 hP3 hP4 h; omega
    have e3 : P3 = t + 1 + y - x := by clear hP2 hP1 hP4 h; omega
    have e4 : P4 = t - (t - y + (1 - (t - y))) := by clear hP2 hP3 hP1 h; omega
    clear hP1 hP2 hP3 hP4
    split_ifs <;> omega
  · refine ⟨2 * t - x, 2 * t - y, by omega, by omega, by omega, ?_⟩
    have e1 : P1 = 3 * t + 1 - (x + y) := by clear hP2 hP3 hP4 h; omega
    have e2 : P2 = 2 * t + 1 - y := by clear hP1 hP3 hP4 h; omega
    have e3 : P3 = 2 * t + 1 - x := by clear hP2 hP1 hP4 h; omega
    have e4 : P4 = t - 1 := by clear hP2 hP3 hP1 h; omega
    clear hP1 hP2 hP3 hP4
    split_ifs <;> omega

/-- In the `(2t+1) × (2t+1)` grid, the number of nodes at distance exactly `t` from a node `p`
determines the colour class `(row + column) mod 2` of `p`. This is the combinatorial fact behind
the counterexample to Theorem 2.6 (checked by computation for `t ≤ 5` in
`Theorem26Counterexample`). -/
theorem gridSphere_top_determines_parity (t : ℕ) (p p' : Fin (2 * t + 1) × Fin (2 * t + 1))
    (h : gridSphere p t = gridSphere p' t) : gridParity p = gridParity p' := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have h1 := p.1.isLt; have h2 := p.2.isLt; have h3 := p'.1.isLt; have h4 := p'.2.isLt
    have : p = p' := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    rw [this]
  · obtain ⟨a, b, ha, hb, hab, hσ⟩ :=
      cases_of_closed t p.1 p.2 _ ht p.1.isLt p.2.isLt (gridSphere_closed t ht p)
    obtain ⟨a', b', ha', hb', hab', hσ'⟩ :=
      cases_of_closed t p'.1 p'.2 _ ht p'.1.isLt p'.2.isLt (gridSphere_closed t ht p')
    rw [h] at hσ
    have hpar : ((p.1 : ℕ) + p.2) % 2 = ((p'.1 : ℕ) + p'.2) % 2 := by
      split_ifs at hσ hσ' <;> omega
    simp only [gridParity, hpar]

/-- **Theorem 2.6 of the paper is false for every odd `k = 2t + 1 ≥ 3`.** The paper claims that
no distributed algorithm can 3-colour the `k × k` grid in less than `k / 2` rounds. But `t < k / 2`
rounds suffice for `k = 2t + 1`, even for a proper 2-colouring: a node learns the number of nodes at
distance `t` from it, which determines its colour class (`gridSphere_top_determines_parity`).
The algorithm is a `t`-round LOCAL algorithm in CSLib's sense (`Cslib.Local.IsLocal t`). -/
theorem theorem_2_6_false_odd (t : ℕ) {V : Type*} :
    ∃ A : SimpleGraph V → V → Fin 3, IsLocal t (fun G (_ : V → Unit) v => A G v) ∧
      ColoursGraph A (grid (2 * t + 1)) :=
  ⟨_, grid_colours_of_profile fun p p' h =>
    gridSphere_top_determines_parity t p p' (h t le_rfl)⟩

end Podc.SparseColoringLB
