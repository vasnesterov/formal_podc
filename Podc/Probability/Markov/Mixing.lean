import Cslib.Probability.Markov.Absorption

-- CSLib candidate: Cslib/Probability/Markov/Mixing.lean

/-!
# Total variation distance and mixing for finite Markov chains

Finite chains are row-stochastic matrices `T : Matrix S S ℝ` (as in
`Cslib.Probability.Markov.Absorption`). Following Levin–Peres, `d(t) = max_x ‖T^t(x, ·) - π‖_TV`
and `t_mix = min {t | d(t) ≤ 1/4}`; we avoid `sInf` and state "`d(t) ≤ 1/4`" as `IsMixedAt`.

* `tvDist μ ν = (1/2) ∑ |μ s - ν s|`;
* `sub_le_tvDist`: `μ(A) - ν(A) ≤ ‖μ - ν‖_TV` when `μ` and `ν` have the same total mass;
* `pow_apply_self_ge`: `T^t(x, x) ≥ T(x, x)^t`;
* `not_isMixedAt_of_disjoint`: if `T^t(x, ·)` and `T^t(y, ·)` are supported in disjoint sets,
  then `d(t) > 1/4` (the diameter lower bound of Levin–Peres §7.1.2).
-/

open Matrix Finset

namespace Cslib.Probability.Markov

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Total variation distance of two (signed) vectors. -/
noncomputable def tvDist (μ ν : S → ℝ) : ℝ := (1 / 2) * ∑ s, |μ s - ν s|

/-- `d(t) ≤ 1/4`: the chain started anywhere is `1/4`-close to `π` after `t` steps. -/
def IsMixedAt (T : Matrix S S ℝ) (π : S → ℝ) (t : ℕ) : Prop :=
  ∀ x, tvDist (fun y => (T ^ t) x y) π ≤ 1 / 4

/-- `μ(A) - ν(A) ≤ ‖μ - ν‖_TV` for vectors of equal total mass. -/
theorem sub_le_tvDist {μ ν : S → ℝ} (h : ∑ s, μ s = ∑ s, ν s) (A : Finset S) :
    ∑ s ∈ A, μ s - ∑ s ∈ A, ν s ≤ tvDist μ ν := by
  unfold tvDist
  have hA : ∑ s ∈ A, μ s - ∑ s ∈ A, ν s = ∑ s ∈ A, (μ s - ν s) := by
    rw [Finset.sum_sub_distrib]
  have hAc : ∑ s ∈ Aᶜ, (μ s - ν s) = -(∑ s ∈ A, (μ s - ν s)) := by
    have := Finset.sum_add_sum_compl A (fun s => μ s - ν s)
    rw [Finset.sum_sub_distrib (s := univ), h, sub_self] at this
    linarith
  have h1 : |∑ s ∈ A, (μ s - ν s)| ≤ ∑ s ∈ A, |μ s - ν s| := Finset.abs_sum_le_sum_abs _ _
  have h2 : |∑ s ∈ Aᶜ, (μ s - ν s)| ≤ ∑ s ∈ Aᶜ, |μ s - ν s| := Finset.abs_sum_le_sum_abs _ _
  rw [hAc, abs_neg] at h2
  have h3 := Finset.sum_add_sum_compl A (fun s => |μ s - ν s|)
  rw [hA]
  have := le_abs_self (∑ s ∈ A, (μ s - ν s))
  linarith

/-- `T^t(x, x) ≥ T(x, x)^t` for matrices with nonnegative entries. -/
theorem pow_apply_self_ge {T : Matrix S S ℝ} (hT : ∀ s s', 0 ≤ T s s') (x : S) (t : ℕ) :
    T x x ^ t ≤ (T ^ t) x x := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, pow_succ, mul_apply]
    have hnn : ∀ s s' (n : ℕ), 0 ≤ (T ^ n) s s' := fun s s' n => pow_apply_nonneg hT n s s'
    calc T x x ^ t * T x x ≤ (T ^ t) x x * T x x :=
          mul_le_mul_of_nonneg_right ih (hT x x)
      _ ≤ ∑ j, (T ^ t) x j * T j x :=
          Finset.single_le_sum (f := fun j => (T ^ t) x j * T j x)
            (fun j _ => mul_nonneg (hnn _ _ _) (hT j x)) (Finset.mem_univ x)

/-- **Diameter lower bound.** If after `t` steps the chains started at `x` and at `y` live on
disjoint sets, then `d(t) > 1/4`. -/
theorem not_isMixedAt_of_disjoint {T : Matrix S S ℝ} (hT : T ∈ rowStochastic ℝ S) {π : S → ℝ}
    (hπ : ∑ s, π s = 1) (t : ℕ) (x y : S) (A : Finset S)
    (hx : ∀ s, 0 < (T ^ t) x s → s ∈ A) (hy : ∀ s, 0 < (T ^ t) y s → s ∉ A) :
    ¬ IsMixedAt T π t := by
  intro hmix
  have hst := pow_mem_rowStochastic hT t
  have hnn : ∀ s s', 0 ≤ (T ^ t) s s' := fun s s' => nonneg_of_mem_rowStochastic hst
  have hsum : ∀ s, ∑ s', (T ^ t) s s' = 1 := sum_row_of_mem_rowStochastic hst
  -- mass of `T^t(x, ·)` on `A` is `1`, mass of `T^t(y, ·)` on `A` is `0`
  have hxA : ∑ s ∈ A, (T ^ t) x s = 1 := by
    have hc : ∑ s ∈ Aᶜ, (T ^ t) x s = 0 := by
      refine Finset.sum_eq_zero fun s hs => ?_
      rcases (hnn x s).lt_or_eq with h | h
      · exact absurd (hx s h) (Finset.mem_compl.1 hs)
      · exact h.symm
    have := Finset.sum_add_sum_compl A (fun s => (T ^ t) x s)
    rw [hsum x, hc] at this
    linarith
  have hyA : ∑ s ∈ A, (T ^ t) y s = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    rcases (hnn y s).lt_or_eq with h | h
    · exact absurd hs (hy s h)
    · exact h.symm
  have h1 := sub_le_tvDist (μ := fun s => (T ^ t) x s) (ν := π) (by rw [hsum x, hπ]) A
  have h2 := sub_le_tvDist (μ := π) (ν := fun s => (T ^ t) y s) (by rw [hsum y, hπ]) A
  have hsymm : tvDist π (fun s => (T ^ t) y s) = tvDist (fun s => (T ^ t) y s) π := by
    unfold tvDist; congr 1; exact Finset.sum_congr rfl fun s _ => abs_sub_comm _ _
  rw [hxA] at h1
  rw [hyA, hsymm] at h2
  have := hmix x
  have := hmix y
  linarith

end Cslib.Probability.Markov
