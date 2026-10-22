import Papers.PODC2015.RingColoringAverage.Lemma2

/-!
# Lemma 3: a node with a large radius has many slow nodes around it

Paper, Lemma 3: if a node `v` uses radius `r` in a minimal algorithm, then the average radius of
the nodes at distance at most `r / 2` from `v` is `Ω(r)`.

We prove it for minimal **4-colouring** algorithms (the paper states it for minimal 3-colouring
algorithms and reduces to 4-colouring with "it is sufficient to prove the result for
4-colouring, as it implies the result for 3-colouring"; this reduction is not valid, because a
3-colouring algorithm that is minimal among 3-colouring algorithms need not be minimal among
4-colouring algorithms, which is what Lemma 2 needs; see `differencies.md`). Theorem 1 only needs
the 4-colouring version.

We also only assume `r ≤ r(v)` (not `r = r(v)`), and that the ring has at least `2r + 1`
nodes. With `h = ⌊r/2⌋`:
* `lemma_3_sum`: `r + h (r - h) ≤ ∑_{|j| ≤ h} r(v + j)`;
* `lemma_3`: the average over these `2h + 1` nodes is at least `r / 4`.
-/

namespace Podc.RingColoringAverage

variable {A : Alg (Fin 4)}

/-- The sum over a symmetric window `[-h, h]`, split into the centre and pairs `±(d+1)`. -/
theorem sum_Icc_symm (f : ℤ → ℕ) (h : ℕ) :
    ∑ j ∈ Finset.Icc (-(h : ℤ)) h, f j =
      f 0 + ∑ d ∈ Finset.range h, (f (-((d : ℤ) + 1)) + f ((d : ℤ) + 1)) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have : Finset.Icc (-((h + 1 : ℕ) : ℤ)) ((h + 1 : ℕ) : ℤ) =
        insert (-((h : ℤ) + 1)) (insert ((h : ℤ) + 1) (Finset.Icc (-(h : ℤ)) h)) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [this, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih,
      Finset.sum_range_succ]
    ring

theorem sum_range_two_mul_succ (h : ℕ) : ∑ d ∈ Finset.range h, 2 * (d + 1) = h * (h + 1) := by
  induction h with
  | zero => simp
  | succ h ih => rw [Finset.sum_range_succ, ih]; ring

/-- The pairwise consequence of Lemma 2 used in the proof of Lemma 3: for the two nodes
`v ± d` at distance `d ≥ 1` from `v`, `r ≤ max {r(v - d), r(v + d)} + 2d - 1`. -/
theorem le_radAt_add (hA : A.IsMinimal) (R : IdRing) (v : ℤ) (r : ℕ) (hr : r ≤ A.radAt R v)
    (hn : 2 * r + 1 ≤ R.n) (d : ℕ) (hd : 1 ≤ d) :
    r + 1 ≤ max (A.radAt R (v - d)) (A.radAt R (v + d)) + 2 * d := by
  have hy : v - d + ((2 * d - 1 : ℕ) + 1 : ℤ) = v + d := by push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * d)]; ring
  by_cases hn' : 2 * (max (A.radAt R (v - d)) (A.radAt R (v + d)) + (2 * d - 1)) + 1 ≤ R.n
  · have := lemma_2 hA R (v - d) (2 * d - 1) (by rwa [hy]) d (by exact_mod_cast hd)
      (by push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * d)]; omega)
    rw [hy, show v - d + d = v by ring] at this
    omega
  · omega

/-- **Lemma 3** of [Feuilloley, PODC 2015], sum form: if `r ≤ r(v)` for a minimal 4-colouring
algorithm and `h = ⌊r/2⌋`, then the radii of the `2h + 1` nodes at distance at most `h` from `v`
sum to at least `r + h (r - h)` (which is quadratic in `r`). -/
theorem lemma_3_sum (hA : A.IsMinimal) (R : IdRing) (v : ℤ) (r : ℕ) (hr : r ≤ A.radAt R v)
    (hn : 2 * r + 1 ≤ R.n) :
    r + r / 2 * (r - r / 2) ≤
      ∑ j ∈ Finset.Icc (-((r / 2 : ℕ) : ℤ)) (r / 2 : ℕ), A.radAt R (v + j) := by
  set h := r / 2 with hh
  rw [sum_Icc_symm (fun j => A.radAt R (v + j)) h]
  simp only [add_zero]
  have key : ∀ d ∈ Finset.range h, r + 1 ≤
      (A.radAt R (v + -((d : ℤ) + 1)) + A.radAt R (v + ((d : ℤ) + 1))) + 2 * (d + 1) := by
    intro d _
    have := le_radAt_add hA R v r hr hn (d + 1) (by omega)
    push_cast at this
    rw [← sub_eq_add_neg]
    omega
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_range_two_mul_succ] at hsum
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  have h2 : h * (r - h) + h * (h + 1) = h * (r + 1) := by
    rw [← Nat.mul_add]; congr 1; omega
  nlinarith

/-- Arithmetic: `r (2⌊r/2⌋ + 1) ≤ 4 (r + ⌊r/2⌋ (r - ⌊r/2⌋))`. -/
theorem four_mul_bound (r : ℕ) : r * (2 * (r / 2) + 1) ≤ 4 * (r + r / 2 * (r - r / 2)) := by
  obtain ⟨h, rfl | rfl⟩ := Nat.even_or_odd' r
  · have : 2 * h / 2 = h := by omega
    rw [this, show 2 * h - h = h by omega]; nlinarith
  · have : (2 * h + 1) / 2 = h := by omega
    rw [this, show 2 * h + 1 - h = h + 1 by omega]; nlinarith

/-- **Lemma 3** of [Feuilloley, PODC 2015]: if `r ≤ r(v)` for a minimal 4-colouring algorithm,
the average radius of the nodes at distance at most `⌊r/2⌋` from `v` is at least `r / 4`. -/
theorem lemma_3 (hA : A.IsMinimal) (R : IdRing) (v : ℤ) (r : ℕ) (hr : r ≤ A.radAt R v)
    (hn : 2 * r + 1 ≤ R.n) :
    (r : ℚ) / 4 ≤ (∑ j ∈ Finset.Icc (-((r / 2 : ℕ) : ℤ)) (r / 2 : ℕ), A.radAt R (v + j) : ℕ) /
      (2 * (r / 2 : ℕ) + 1 : ℕ) := by
  have h1 := lemma_3_sum hA R v r hr hn
  have h2 := four_mul_bound r
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  have : r * (2 * (r / 2) + 1) ≤
      4 * ∑ j ∈ Finset.Icc (-((r / 2 : ℕ) : ℤ)) (r / 2 : ℕ), A.radAt R (v + j) := by omega
  exact_mod_cast (by linarith : (r * (2 * (r / 2) + 1) : ℕ) ≤ _ * 4)

end Podc.RingColoringAverage
