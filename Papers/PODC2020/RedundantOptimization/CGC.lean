/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2020.RedundantOptimization.Convex

/-!
# The CGC algorithm and Theorem 2

Section 4 of the paper: the server keeps an estimate `w t`; in iteration `t` it receives one vector
from every agent (honest agent `i` sends `∇Q_i(w t)`, a faulty agent sends anything; a missing
gradient counts as `0`, which is one of the faulty choices), applies the *comparative gradient
clipping* (CGC) filter and moves against the sum of the filtered vectors:

* `threshold f g` — the `(n-f)`-th smallest norm `‖g_{i_{n-f}}‖` (`threshold_spec`);
* `cgc f g j = min 1 (threshold / ‖g j‖) • g j` — the `f` largest vectors are scaled down to the
  threshold norm, the others are unchanged (this is exactly (16), ties included);
* `IsRun` — the iteration (17) against an arbitrary adaptive Byzantine adversary.

`Assumptions` bundles Assumptions 2–4 and 2f-redundancy; Assumption 1 (synchrony) is the run model.
Results:

* `theorem2` — Theorem 2 (ii): `‖w t - [w t]‖² ≤ ρ^t ‖w 0 - [w 0]‖²`, and `ρ < 1`;
* `theorem2_rho_nonneg` — Theorem 2 (i) `0 ≤ ρ`, which needs `W* ≠ E`;
* `theorem2_rho_nonneg_false` — (i) fails when `W* = E` (degenerate case);
* `theorem2_tendsto` — convergence of `w t` to `W*`;
* `mem_Wstar_of_threshold_eq_zero` — the stopping rule of Step S2 is correct;
* `exists_proj` — the Euclidean projection onto `W*` exists (`W*` is closed and convex);
* `example_assumptions` — the hypotheses are satisfiable with `f ≥ 1` (non-vacuity).
-/

open Finset InnerProductSpace
open scoped RealInnerProductSpace

namespace RedundantOptimization

/-! ### Convexity with gradients -/

section Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma mem_argmin_of_hasGradientAt_zero {q : E → ℝ} (hq : ConvexOn ℝ Set.univ q) {x : E}
    (hg : HasGradientAt q 0 x) : x ∈ argmin q := fun y => by
  simpa using ConvexOn.add_inner_le hq hg y

lemma hasGradientAt_eq_zero_of_mem_argmin {q : E → ℝ} {g x : E} (hg : HasGradientAt q g x)
    (hx : x ∈ argmin q) : g = 0 := by
  have := hasFDerivAt_eq_zero_of_mem_argmin (hasGradientAt_iff_hasFDerivAt.1 hg) hx
  exact (toDual ℝ E).injective (by rw [this, map_zero])

lemma hasGradientAt_agg {ι : Type*} (S : Finset ι) {Q : ι → E → ℝ} {G : ι → E → E} {w : E}
    (h : ∀ i ∈ S, HasGradientAt (Q i) (G i w) w) :
    HasGradientAt (agg S Q) (∑ i ∈ S, G i w) w := by
  rw [hasGradientAt_iff_hasFDerivAt, map_sum]
  exact HasFDerivAt.fun_sum fun i hi => hasGradientAt_iff_hasFDerivAt.1 (h i hi)

omit [CompleteSpace E] in
/-- Finite sums of convex functions are convex (the shared `ConvexOn.fun_sum`). -/
lemma convexOn_agg {ι : Type*} {S : Finset ι} {Q : ι → E → ℝ}
    (h : ∀ i ∈ S, ConvexOn ℝ Set.univ (Q i)) : ConvexOn ℝ Set.univ (agg S Q) :=
  ConvexOn.fun_sum h

end Gradient

/-! ### The CGC filter -/

section Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The CGC threshold: the `(n-f)`-th smallest of the norms `‖g j‖` (`‖g_{i_{n-f}}‖` in (16)),
i.e. the least norm value `t` such that at least `n - f` norms are `≤ t`. -/
noncomputable def threshold (f : ℕ) (g : Fin n → E) : ℝ :=
  sInf {t : ℝ | (∃ j, ‖g j‖ = t) ∧ n - f ≤ #{j | ‖g j‖ ≤ t}}

omit [InnerProductSpace ℝ E] in
/-- The threshold is one of the norms, at least `n - f` norms are `≤` it and at least `f + 1` norms
are `≥` it. -/
theorem threshold_spec {f : ℕ} (hf : f < n) (g : Fin n → E) :
    (∃ j, ‖g j‖ = threshold f g) ∧ n - f ≤ #{j | ‖g j‖ ≤ threshold f g} ∧
      f + 1 ≤ #{j | threshold f g ≤ ‖g j‖} := by
  classical
  set A := {t : ℝ | (∃ j, ‖g j‖ = t) ∧ n - f ≤ #{j | ‖g j‖ ≤ t}} with hAdef
  have hfin : A.Finite := (Set.finite_range fun j => ‖g j‖).subset fun t ht => ht.1
  have hne : A.Nonempty := by
    obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image (univ : Finset (Fin n)) (fun j => ‖g j‖)
      ⟨⟨0, by omega⟩, mem_univ _⟩
    refine ⟨‖g j0‖, ⟨j0, rfl⟩, ?_⟩
    have : #{j | ‖g j‖ ≤ ‖g j0‖} = n := by
      rw [Finset.filter_true_of_mem fun j _ => hj0 j (mem_univ j)]; simp
    omega
  have hmem : threshold f g ∈ A := hne.csInf_mem hfin
  refine ⟨hmem.1, hmem.2, ?_⟩
  by_contra hlt
  push Not at hlt
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun j => threshold f g ≤ ‖g j‖)
  simp only [card_univ, Fintype.card_fin, not_le] at hsplit
  set L := (univ : Finset (Fin n)).filter fun j => ‖g j‖ < threshold f g with hLdef
  have hL : n - f ≤ #L := by omega
  have hLne : L.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨j1, hj1L, hj1⟩ := Finset.exists_max_image L (fun j => ‖g j‖) hLne
  have hA : ‖g j1‖ ∈ A := by
    refine ⟨⟨j1, rfl⟩, le_trans hL (Finset.card_le_card ?_)⟩
    intro j hj
    simp only [mem_filter, mem_univ, true_and]
    exact hj1 j hj
  have h1 : threshold f g ≤ ‖g j1‖ := csInf_le hfin.bddBelow hA
  simp only [hLdef, mem_filter, mem_univ, true_and] at hj1L
  linarith

omit [InnerProductSpace ℝ E] in
lemma threshold_nonneg {f : ℕ} (hf : f < n) (g : Fin n → E) : 0 ≤ threshold f g := by
  obtain ⟨⟨j, hj⟩, -, -⟩ := threshold_spec hf g
  rw [← hj]; exact norm_nonneg _

/-- The CGC filter (16): `ĝ_j = min 1 (‖g_{i_{n-f}}‖ / ‖g_j‖) • g_j`. For the `n - f` smallest
vectors the factor is `1`; the `f` largest ones are scaled to norm `‖g_{i_{n-f}}‖`. -/
noncomputable def cgc (f : ℕ) (g : Fin n → E) (j : Fin n) : E :=
  min 1 (threshold f g / ‖g j‖) • g j

lemma norm_cgc_le {f : ℕ} (hf : f < n) (g : Fin n → E) (j : Fin n) :
    ‖cgc f g j‖ ≤ threshold f g := by
  have hτ := threshold_nonneg hf g
  unfold cgc
  rcases eq_or_ne (g j) 0 with h | h
  · simp [h, hτ]
  · have hpos : 0 < ‖g j‖ := norm_pos_iff.2 h
    rw [norm_smul, Real.norm_of_nonneg (le_min zero_le_one (div_nonneg hτ hpos.le))]
    calc min 1 (threshold f g / ‖g j‖) * ‖g j‖ ≤ threshold f g / ‖g j‖ * ‖g j‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hpos.le
      _ = threshold f g := div_mul_cancel₀ _ hpos.ne'

lemma cgc_of_le {f : ℕ} {g : Fin n → E} {j : Fin n} (h : ‖g j‖ ≤ threshold f g) :
    cgc f g j = g j := by
  unfold cgc
  rcases eq_or_ne (g j) 0 with h0 | h0
  · simp [h0]
  · have hpos := norm_pos_iff.2 h0
    rw [min_eq_left ((one_le_div hpos).2 h), one_smul]

lemma cgc_eq_smul {f : ℕ} (hf : f < n) (g : Fin n → E) (j : Fin n) :
    ∃ c : ℝ, 0 ≤ c ∧ cgc f g j = c • g j :=
  ⟨_, le_min zero_le_one (div_nonneg (threshold_nonneg hf g) (norm_nonneg _)), rfl⟩

end Filter

/-! ### Assumptions and runs -/

/-- The hypotheses of Theorem 2 for an execution with honest set `H`: Assumptions 2–4 and
2f-redundancy. (Assumption 1, synchrony, is built into `IsRun`.) -/
structure Assumptions (n f : ℕ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  /-- The honest agents; at most `f` agents are faulty. -/
  H : Finset (Fin n)
  card_H : n - f ≤ H.card
  /-- The cost functions (only the honest ones matter). -/
  Q : Fin n → E → ℝ
  /-- The gradients `∇Q_i`. -/
  G : Fin n → E → E
  /-- Assumption 2: convexity. -/
  convex : ∀ i ∈ H, ConvexOn ℝ Set.univ (Q i)
  /-- Assumption 2: differentiability, with gradient `G i`. -/
  hasGradient : ∀ i ∈ H, ∀ w, HasGradientAt (Q i) (G i w) w
  /-- Assumption 3: the Lipschitz constant `μ > 0` of the honest gradients. -/
  μ : ℝ
  μ_pos : 0 < μ
  lipschitz : ∀ i ∈ H, ∀ w w', ‖G i w - G i w'‖ ≤ μ * ‖w - w'‖
  /-- 2f-redundancy (Definition 1). -/
  redundant : TwoFRedundant n f H Q
  /-- The Euclidean projection `[·]_{W*}` onto `W* = arg min ∑_{i∈H} Q_i` (any nearest-point map;
  it is unique, see `exists_proj`). -/
  proj : E → E
  proj_mem : ∀ w, proj w ∈ argmin (agg H Q)
  proj_min : ∀ w, ∀ v ∈ argmin (agg H Q), ‖w - proj w‖ ≤ ‖w - v‖
  /-- Assumption 4 (relaxed strong convexity) with constant `lam = λ > 0`. -/
  lam : ℝ
  lam_pos : 0 < lam
  strong : ∀ w, lam * ‖w - proj w‖ ^ 2 ≤ ⟪(1 / (H.card : ℝ)) • ∑ i ∈ H, G i w, w - proj w⟫

namespace Assumptions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n f : ℕ} (A : Assumptions n f E)

/-- `W* = arg min_w ∑_{i ∈ H} Q_i(w)`. -/
def Wstar : Set E := argmin (agg A.H A.Q)

/-- The fault-tolerance margin (20): `α = λ / (3μ) - f / n`. -/
noncomputable def α : ℝ := A.lam / (3 * A.μ) - f / n

/-- The step-size bound (21): `η̄ = 6α / (nμ)`. -/
noncomputable def ηbar : ℝ := 6 * A.α / (n * A.μ)

/-- The convergence rate (22): `ρ = 1 - (nμ)² η (η̄ - η)`. -/
noncomputable def ρ (η : ℝ) : ℝ := 1 - (n * A.μ) ^ 2 * η * (A.ηbar - η)

/-- A run of the algorithm with step size `η` (Steps S1, S2 and (17)) against an arbitrary
(adaptive) Byzantine adversary: in every iteration the honest agents send their true gradients at
the current estimate, the faulty agents send arbitrary vectors. -/
def IsRun (η : ℝ) (w : ℕ → E) : Prop :=
  ∀ t, ∃ r : Fin n → E, (∀ i ∈ A.H, r i = A.G i (w t)) ∧ w (t + 1) = w t - η • ∑ j, cgc f r j

lemma sum_grad_eq_zero {S : Finset (Fin n)} (hS : S ⊆ A.H) {p : E}
    (hp : p ∈ argmin (agg S A.Q)) : ∑ i ∈ S, A.G i p = 0 :=
  hasGradientAt_eq_zero_of_mem_argmin
    (hasGradientAt_agg S fun i hi => A.hasGradient i (hS hi) p) hp

/-- Under 2f-redundancy (and `f ≥ 1`) every honest gradient vanishes on `W*` ((29) ⇒ (30)). -/
lemma grad_eq_zero (hf : 1 ≤ f) {i : Fin n} (hi : i ∈ A.H) {p : E} (hp : p ∈ A.Wstar) :
    A.G i p = 0 := by
  have hcard : n - 2 * f ≤ (A.H.erase i).card := by
    rw [card_erase_of_mem hi]; have := A.card_H; omega
  have h1 := A.sum_grad_eq_zero subset_rfl hp
  have h2 := A.sum_grad_eq_zero (erase_subset i A.H)
    (by rw [A.redundant _ (erase_subset i A.H) hcard]; exact hp)
  rw [← add_sum_erase _ _ hi, h2, add_zero] at h1
  exact h1

/-- (30): `‖∇Q_i(w)‖ ≤ μ ‖w - [w]‖` for honest `i` (`f ≥ 1`). -/
lemma norm_grad_le (hf : 1 ≤ f) {i : Fin n} (hi : i ∈ A.H) (w : E) :
    ‖A.G i w‖ ≤ A.μ * ‖w - A.proj w‖ := by
  have := A.lipschitz i hi w (A.proj w)
  rwa [A.grad_eq_zero hf hi (A.proj_mem w), sub_zero] at this

/-- (48): `⟨w - [w], ∇Q_i(w)⟩ ≥ 0` for honest `i` (`f ≥ 1`). -/
lemma inner_grad_nonneg (hf : 1 ≤ f) {i : Fin n} (hi : i ∈ A.H) (w : E) :
    0 ≤ ⟪w - A.proj w, A.G i w⟫ := by
  set p := A.proj w
  have hmin : p ∈ argmin (A.Q i) := by
    apply mem_argmin_of_hasGradientAt_zero (A.convex i hi)
    have := A.hasGradient i hi p
    rwa [A.grad_eq_zero hf hi (A.proj_mem w)] at this
  have h1 := ConvexOn.add_inner_le (A.convex i hi) (A.hasGradient i hi w) p
  have h2 := hmin w
  have : ⟪A.G i w, p - w⟫ = -⟪w - p, A.G i w⟫ := by
    rw [real_inner_comm, ← inner_neg_left, neg_sub]
  linarith

lemma norm_sum_grad_le (w : E) :
    ‖∑ i ∈ A.H, A.G i w‖ ≤ A.H.card * A.μ * ‖w - A.proj w‖ := by
  have h0 := A.sum_grad_eq_zero subset_rfl (A.proj_mem w)
  calc ‖∑ i ∈ A.H, A.G i w‖ = ‖∑ i ∈ A.H, (A.G i w - A.G i (A.proj w))‖ := by
        rw [sum_sub_distrib, h0, sub_zero]
    _ ≤ ∑ i ∈ A.H, ‖A.G i w - A.G i (A.proj w)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ A.H, A.μ * ‖w - A.proj w‖ := sum_le_sum fun i hi => A.lipschitz i hi _ _
    _ = A.H.card * A.μ * ‖w - A.proj w‖ := by rw [sum_const, nsmul_eq_mul]; ring

lemma card_H_pos (hn : 2 * f < n) : 0 < A.H.card := by
  have := A.card_H; omega

/-- Assumption 4 in summed form: `|H| λ ‖w - [w]‖² ≤ ∑_{i∈H} ⟨w - [w], ∇Q_i(w)⟩`. -/
lemma inner_sum_grad_ge (hn : 2 * f < n) (w : E) :
    A.H.card * A.lam * ‖w - A.proj w‖ ^ 2 ≤ ⟪w - A.proj w, ∑ i ∈ A.H, A.G i w⟫ := by
  have h := A.strong w
  rw [real_inner_smul_left, real_inner_comm] at h
  have hc : (0 : ℝ) < A.H.card := by exact_mod_cast A.card_H_pos hn
  have h2 : (A.H.card : ℝ) * (1 / A.H.card * ⟪w - A.proj w, ∑ i ∈ A.H, A.G i w⟫) =
      ⟪w - A.proj w, ∑ i ∈ A.H, A.G i w⟫ := by field_simp
  calc (A.H.card : ℝ) * A.lam * ‖w - A.proj w‖ ^ 2
      = A.H.card * (A.lam * ‖w - A.proj w‖ ^ 2) := by ring
    _ ≤ A.H.card * (1 / A.H.card * ⟪w - A.proj w, ∑ i ∈ A.H, A.G i w⟫) :=
        mul_le_mul_of_nonneg_left h hc.le
    _ = _ := h2

/-- Appendix B: `λ ≤ μ` as soon as `W* ≠ E` (witnessed by a point off `W*`). -/
lemma lam_le_μ (hn : 2 * f < n) {w : E} (hw : w ≠ A.proj w) : A.lam ≤ A.μ := by
  have hD : 0 < ‖w - A.proj w‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
  have hc : (0 : ℝ) < A.H.card := by exact_mod_cast A.card_H_pos hn
  have h1 := A.inner_sum_grad_ge hn w
  have h2 := real_inner_le_norm (w - A.proj w) (∑ i ∈ A.H, A.G i w)
  have h3 := A.norm_sum_grad_le w
  have h4 : A.H.card * A.lam * ‖w - A.proj w‖ ^ 2 ≤ A.H.card * A.μ * ‖w - A.proj w‖ ^ 2 := by
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ ‖w - A.proj w‖ * (A.H.card * A.μ * ‖w - A.proj w‖) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = _ := by ring
  have hpos : 0 < (A.H.card : ℝ) * ‖w - A.proj w‖ ^ 2 := by positivity
  nlinarith

/-- (45): at least `n - 2f` honest agents are among the `n - f` smallest received vectors. -/
lemma exists_H1 (hn : 2 * f < n) (r : Fin n → E) :
    ∃ H1 ⊆ A.H, H1.card + 2 * f = n ∧ ∀ j ∈ H1, ‖r j‖ ≤ threshold f r := by
  classical
  obtain ⟨-, hL, -⟩ := threshold_spec (by omega : f < n) r
  have hc := card_inter_ge hL A.card_H
  obtain ⟨H1, hsub, hcard⟩ := Finset.exists_subset_card_eq hc
  refine ⟨H1, fun j hj => (Finset.mem_inter.1 (hsub hj)).2, by omega, fun j hj => ?_⟩
  have := (Finset.mem_inter.1 (hsub hj)).1
  simpa using this

/-- (39): one of the `f + 1` largest received vectors comes from an honest agent. -/
lemma exists_honest_ge (hn : 2 * f < n) (r : Fin n → E) :
    ∃ σ ∈ A.H, threshold f r ≤ ‖r σ‖ := by
  classical
  obtain ⟨-, -, hU⟩ := threshold_spec (by omega : f < n) r
  have hHc : #A.Hᶜ ≤ f := by
    rw [card_compl, Fintype.card_fin]; have := A.card_H; omega
  obtain ⟨σ, hσ, hσH⟩ := exists_mem_notMem_of_card_le_of_lt hHc hU
  exact ⟨σ, by simpa using hσH, by simpa using hσ⟩

/-- The stopping rule of Step S2: if `‖g_{i_{n-f}}‖ = 0` then the current estimate is in `W*`. -/
theorem mem_Wstar_of_threshold_eq_zero (hn : 2 * f < n) (w : E) (r : Fin n → E)
    (hr : ∀ i ∈ A.H, r i = A.G i w) (h0 : threshold f r = 0) : w ∈ A.Wstar := by
  obtain ⟨H1, hH1, hcard, hle⟩ := A.exists_H1 hn r
  have hz : ∀ j ∈ H1, A.G j w = 0 := by
    intro j hj
    have := hle j hj
    rw [h0, hr j (hH1 hj)] at this
    exact norm_le_zero_iff.1 this
  have hgrad : HasGradientAt (agg H1 A.Q) 0 w := by
    have := hasGradientAt_agg H1 (G := A.G) (w := w) fun i hi => A.hasGradient i (hH1 hi) w
    rwa [Finset.sum_eq_zero hz] at this
  have hmin := mem_argmin_of_hasGradientAt_zero (convexOn_agg fun i hi => A.convex i (hH1 hi)) hgrad
  unfold Wstar
  rwa [← A.redundant H1 hH1 (by omega)]

/-- The two key estimates of Appendix C for one iteration: (42) `‖g‖ ≤ nμ‖w - [w]‖` and (56)
`φ = ⟨w - [w], g⟩ ≥ (nλ - 3μf)‖w - [w]‖²`, where `g` is the sum of the filtered vectors. -/
lemma key_estimates (hn : 2 * f < n) (w : E) (r : Fin n → E) (hr : ∀ i ∈ A.H, r i = A.G i w) :
    ‖∑ j, cgc f r j‖ ≤ n * A.μ * ‖w - A.proj w‖ ∧
      (n * A.lam - 3 * f * A.μ) * ‖w - A.proj w‖ ^ 2 ≤ ⟪w - A.proj w, ∑ j, cgc f r j⟫ := by
  classical
  set e := w - A.proj w with he
  set D := ‖e‖ with hDdef
  have hfn : f < n := by omega
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · -- `f = 0`: no faulty agent and no clipping; plain gradient descent
    have hHuniv : A.H = univ := by
      have h1 := Finset.card_le_univ A.H
      have h2 := A.card_H
      simp only [Fintype.card_fin, Nat.sub_zero] at h1 h2
      exact Finset.eq_univ_of_card _ (by simp only [Fintype.card_fin]; omega)
    obtain ⟨-, hL, -⟩ := threshold_spec hfn r
    have hall : ∀ j, ‖r j‖ ≤ threshold 0 r := by
      intro j
      by_contra hj
      have hlt := Finset.card_lt_card
        ((Finset.filter_ssubset (p := fun j => ‖r j‖ ≤ threshold 0 r)).2 ⟨j, mem_univ j, hj⟩)
      simp only [card_univ, Fintype.card_fin] at hlt
      omega
    have hg : ∑ j, cgc 0 r j = ∑ i ∈ A.H, A.G i w := by
      rw [hHuniv]
      exact Finset.sum_congr rfl fun j _ => by rw [cgc_of_le (hall j), hr j (by simp [hHuniv])]
    have hcardH : (A.H.card : ℝ) = n := by rw [hHuniv]; simp
    rw [hg]
    refine ⟨?_, ?_⟩
    · have := A.norm_sum_grad_le w; rwa [hcardH] at this
    · have := A.inner_sum_grad_ge hn w; rw [hcardH] at this; simpa using this
  · -- `f ≥ 1`
    set τ := threshold f r with hτdef
    have hτ0 : 0 ≤ τ := threshold_nonneg hfn r
    obtain ⟨σ, hσH, hσ⟩ := A.exists_honest_ge hn r
    have hτμ : τ ≤ A.μ * D := by
      calc τ ≤ ‖r σ‖ := hσ
        _ = ‖A.G σ w‖ := by rw [hr σ hσH]
        _ ≤ A.μ * D := A.norm_grad_le hf hσH w
    have hcgc : ∀ j, ‖cgc f r j‖ ≤ A.μ * D := fun j => (norm_cgc_le hfn r j).trans hτμ
    refine ⟨?_, ?_⟩
    · calc ‖∑ j, cgc f r j‖ ≤ ∑ j, ‖cgc f r j‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin n, A.μ * D := sum_le_sum fun j _ => hcgc j
        _ = n * A.μ * D := by simp [sum_const]; ring
    · rcases eq_or_lt_of_le (norm_nonneg e) with hD0 | hDpos
      · -- `w ∈ W*`
        have he0 : e = 0 := norm_eq_zero.1 hD0.symm
        have hD : D = 0 := by rw [hDdef]; exact hD0.symm
        rw [hD, he0]; simp
      have hne : w ≠ A.proj w := by
        intro h
        have : e = 0 := by rw [he, ← h, sub_self]
        rw [this, norm_zero] at hDpos
        exact lt_irrefl _ hDpos
      have hlm : A.lam ≤ A.μ := A.lam_le_μ hn hne
      obtain ⟨H1, hH1, hcard1, hle1⟩ := A.exists_H1 hn r
      -- split the sum over `H1`, `H \ H1` and `Hᶜ`
      have hsplit : ⟪e, ∑ j, cgc f r j⟫ =
          ∑ j ∈ H1, ⟪e, A.G j w⟫ + ∑ j ∈ A.H \ H1, ⟪e, cgc f r j⟫ + ∑ j ∈ A.Hᶜ, ⟪e, cgc f r j⟫ := by
        rw [inner_sum, ← Finset.sum_add_sum_compl A.H, ← Finset.sum_sdiff hH1]
        have : ∑ j ∈ H1, ⟪e, cgc f r j⟫ = ∑ j ∈ H1, ⟪e, A.G j w⟫ :=
          Finset.sum_congr rfl fun j hj => by rw [cgc_of_le (hle1 j hj), hr j (hH1 hj)]
        rw [this]; ring
      -- (47)-(49): the clipped honest terms are nonnegative
      have hmid : 0 ≤ ∑ j ∈ A.H \ H1, ⟪e, cgc f r j⟫ := by
        apply Finset.sum_nonneg
        intro j hj
        have hjH := (Finset.mem_sdiff.1 hj).1
        obtain ⟨c, hc, hcj⟩ := cgc_eq_smul hfn r j
        rw [hcj, hr j hjH, real_inner_smul_right]
        exact mul_nonneg hc (A.inner_grad_nonneg hf hjH w)
      -- (50): the faulty terms are `≥ -μ‖w - [w]‖²` each
      have hbad : -(A.Hᶜ.card * (A.μ * D ^ 2)) ≤ ∑ j ∈ A.Hᶜ, ⟪e, cgc f r j⟫ := by
        have : ∀ j ∈ A.Hᶜ, -(A.μ * D ^ 2) ≤ ⟪e, cgc f r j⟫ := by
          intro j _
          have h1 := abs_real_inner_le_norm e (cgc f r j)
          have h2 := mul_le_mul_of_nonneg_left (hcgc j) (norm_nonneg e)
          have h3 := neg_abs_le ⟪e, cgc f r j⟫
          nlinarith
        have := Finset.sum_le_sum this
        simpa [sum_const, nsmul_eq_mul] using this
      -- (52)-(54): the unclipped honest terms
      have hgood : A.H.card * A.lam * D ^ 2 - (A.H \ H1).card * (A.μ * D ^ 2) ≤
          ∑ j ∈ H1, ⟪e, A.G j w⟫ := by
        have hall := A.inner_sum_grad_ge hn w
        rw [inner_sum, ← Finset.sum_sdiff hH1] at hall
        have hup : ∑ j ∈ A.H \ H1, ⟪e, A.G j w⟫ ≤ (A.H \ H1).card * (A.μ * D ^ 2) := by
          have : ∀ j ∈ A.H \ H1, ⟪e, A.G j w⟫ ≤ A.μ * D ^ 2 := by
            intro j hj
            have h1 := real_inner_le_norm e (A.G j w)
            have h2 := mul_le_mul_of_nonneg_left
              (A.norm_grad_le hf (Finset.mem_sdiff.1 hj).1 w) (norm_nonneg e)
            nlinarith
          have := Finset.sum_le_sum this
          simpa [sum_const, nsmul_eq_mul] using this
        linarith
      -- counting
      have hc1 : (A.H \ H1).card + H1.card = A.H.card := Finset.card_sdiff_add_card_eq_card hH1
      have hc2 : A.H.card + A.Hᶜ.card = n := by simp
      have hc3 : A.Hᶜ.card ≤ f := by have := A.card_H; omega
      have hc1' : ((A.H \ H1).card : ℝ) + H1.card = A.H.card := by exact_mod_cast hc1
      have hc2' : (A.H.card : ℝ) + A.Hᶜ.card = n := by exact_mod_cast hc2
      have hc3' : (A.Hᶜ.card : ℝ) ≤ f := by exact_mod_cast hc3
      have hcard1' : (H1.card : ℝ) + 2 * f = n := by exact_mod_cast hcard1
      have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
      have hlam := A.lam_pos
      -- `(n - |H|) λ ≤ f μ`
      have hkey : (A.Hᶜ.card : ℝ) * A.lam * D ^ 2 ≤ f * A.μ * D ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hD2
        exact mul_le_mul hc3' hlm hlam.le (by positivity)
      have e1 : (((A.H \ H1).card : ℝ) + A.Hᶜ.card) * (A.μ * D ^ 2) = 2 * f * (A.μ * D ^ 2) := by
        rw [show (((A.H \ H1).card : ℝ) + A.Hᶜ.card) = 2 * f by linarith]
      have e2 : (A.H.card : ℝ) * A.lam * D ^ 2 = n * A.lam * D ^ 2 - A.Hᶜ.card * A.lam * D ^ 2 := by
        rw [← hc2']; ring
      rw [hsplit]
      nlinarith

/-- One iteration contracts the squared distance to `W*` ((57)). -/
theorem step (hn : 2 * f < n) {η : ℝ} (hη : 0 ≤ η) (w : E) (r : Fin n → E)
    (hr : ∀ i ∈ A.H, r i = A.G i w) :
    ‖(w - η • ∑ j, cgc f r j) - A.proj (w - η • ∑ j, cgc f r j)‖ ^ 2 ≤
      (1 - 2 * η * (n * A.lam - 3 * f * A.μ) + η ^ 2 * (n * A.μ) ^ 2) * ‖w - A.proj w‖ ^ 2 := by
  set g := ∑ j, cgc f r j
  set p := A.proj w
  set e := w - p
  obtain ⟨hg, hφ⟩ := A.key_estimates hn w r hr
  have h1 : ‖(w - η • g) - A.proj (w - η • g)‖ ≤ ‖(w - η • g) - p‖ :=
    A.proj_min _ p (A.proj_mem w)
  have h2 : (w - η • g) - p = e - η • g := by simp only [e]; abel
  have h3 : ‖e - η • g‖ ^ 2 = ‖e‖ ^ 2 - 2 * (η * ⟪e, g⟫) + η ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg hη]; ring
  have h4 : ‖(w - η • g) - A.proj (w - η • g)‖ ^ 2 ≤ ‖e - η • g‖ ^ 2 := by
    rw [← h2]; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h5 : ‖g‖ ^ 2 ≤ (n * A.μ * ‖e‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  have h6 : η * ((n * A.lam - 3 * f * A.μ) * ‖e‖ ^ 2) ≤ η * ⟪e, g⟫ :=
    mul_le_mul_of_nonneg_left hφ hη
  have h7 : η ^ 2 * ‖g‖ ^ 2 ≤ η ^ 2 * (n * A.μ * ‖e‖) ^ 2 :=
    mul_le_mul_of_nonneg_left h5 (sq_nonneg η)
  calc _ ≤ ‖e - η • g‖ ^ 2 := h4
    _ = ‖e‖ ^ 2 - 2 * (η * ⟪e, g⟫) + η ^ 2 * ‖g‖ ^ 2 := h3
    _ ≤ _ := by nlinarith

lemma ρ_eq (hn : 2 * f < n) (η : ℝ) :
    A.ρ η = 1 - 2 * η * (n * A.lam - 3 * f * A.μ) + η ^ 2 * (n * A.μ) ^ 2 := by
  have hμ := A.μ_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold ρ ηbar α
  field_simp
  ring

/-- **Theorem 2 (ii)** (and `ρ < 1`). Under 2f-redundancy and Assumptions 1–4, if `α > 0` and
`0 < η < η̄`, every run satisfies `‖w t - [w t]‖² ≤ ρ^t ‖w 0 - [w 0]‖²`. (The paper's hypothesis
`α > 0` is implied by `0 < η < η̄ = 6α/(nμ)` and is therefore omitted.) -/
theorem theorem2 (hn : 2 * f < n) {η : ℝ} (hη0 : 0 < η) (hη1 : η < A.ηbar)
    {w : ℕ → E} (hw : A.IsRun η w) :
    A.ρ η < 1 ∧ ∀ t, ‖w t - A.proj (w t)‖ ^ 2 ≤ A.ρ η ^ t * ‖w 0 - A.proj (w 0)‖ ^ 2 := by
  have hμ := A.μ_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ1 : A.ρ η < 1 := by
    unfold ρ
    have : 0 < (n * A.μ) ^ 2 * η * (A.ηbar - η) := by
      have : 0 < A.ηbar - η := by linarith
      positivity
    linarith
  refine ⟨hρ1, ?_⟩
  -- one step
  have hstep : ∀ t, ‖w (t + 1) - A.proj (w (t + 1))‖ ^ 2 ≤ A.ρ η * ‖w t - A.proj (w t)‖ ^ 2 := by
    intro t
    obtain ⟨r, hr, hwt⟩ := hw t
    rw [hwt, A.ρ_eq hn]
    exact A.step hn hη0.le (w t) r hr
  rcases le_or_gt 0 (A.ρ η) with hρ0 | hρ0
  · intro t
    induction t with
    | zero => simp
    | succ t ih =>
      calc _ ≤ A.ρ η * ‖w t - A.proj (w t)‖ ^ 2 := hstep t
        _ ≤ A.ρ η * (A.ρ η ^ t * ‖w 0 - A.proj (w 0)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left ih hρ0
        _ = _ := by ring
  · -- `ρ < 0` forces all distances to vanish
    have hz : ∀ t, ‖w t - A.proj (w t)‖ ^ 2 = 0 := by
      intro t
      have h1 := hstep t
      have h2 : 0 ≤ ‖w (t + 1) - A.proj (w (t + 1))‖ ^ 2 := sq_nonneg _
      have h3 : 0 ≤ ‖w t - A.proj (w t)‖ ^ 2 := sq_nonneg _
      nlinarith
    intro t
    rw [hz t, hz 0, mul_zero]

/-- **Theorem 2 (i)**, `0 ≤ ρ`: true as soon as `W* ≠ E` (Appendix B shows `λ ≤ μ`, hence
`α ≤ 1/3` and `ρ ≥ 1 - 9α² ≥ 0`). See `theorem2_rho_nonneg_false` for the degenerate case. -/
theorem theorem2_rho_nonneg (hn : 2 * f < n) (hα : 0 < A.α) {η : ℝ} (hnd : ∃ w, w ∉ A.Wstar) :
    0 ≤ A.ρ η := by
  obtain ⟨w, hw⟩ := hnd
  have hne : w ≠ A.proj w := fun h => hw (h ▸ A.proj_mem w)
  have hlm := A.lam_le_μ hn hne
  have hμ := A.μ_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hα3 : A.α ≤ 1 / 3 := by
    unfold α
    have : A.lam / (3 * A.μ) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have : (0 : ℝ) ≤ f / n := by positivity
    linarith
  -- `ρ = 1 - 9α² + (nμη - 3α)² ≥ 1 - 9α²`
  have hρ : A.ρ η = 1 - 9 * A.α ^ 2 + (n * A.μ * η - 3 * A.α) ^ 2 := by
    unfold ρ ηbar
    field_simp
    ring
  rw [hρ]
  nlinarith [sq_nonneg (n * A.μ * η - 3 * A.α)]

/-- Convergence: under the hypotheses of Theorem 2 and `W* ≠ E`, the distance from `w t` to `W*`
tends to `0`. -/
theorem theorem2_tendsto (hn : 2 * f < n) (hα : 0 < A.α) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < A.ηbar) {w : ℕ → E} (hw : A.IsRun η w) (hnd : ∃ v, v ∉ A.Wstar) :
    Filter.Tendsto (fun t => ‖w t - A.proj (w t)‖) Filter.atTop (nhds 0) := by
  obtain ⟨hρ1, hbound⟩ := A.theorem2 hn hη0 hη1 hw
  have hρ0 := A.theorem2_rho_nonneg (η := η) hn hα hnd
  have hlim : Filter.Tendsto (fun t => A.ρ η ^ t * ‖w 0 - A.proj (w 0)‖ ^ 2) Filter.atTop
      (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const
      (‖w 0 - A.proj (w 0)‖ ^ 2)
  have hsq : Filter.Tendsto (fun t => ‖w t - A.proj (w t)‖ ^ 2) Filter.atTop (nhds 0) :=
    squeeze_zero (fun t => sq_nonneg _) hbound hlim
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

end Assumptions

/-! ### Existence of the projection -/

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `W*` is closed and convex, so if it is non-empty the Euclidean projection onto it exists.
(Hence the field `proj` of `Assumptions` can always be filled when `W* ≠ ∅`.) -/
theorem exists_proj {n : ℕ} (H : Finset (Fin n)) (Q : Fin n → E → ℝ)
    (hconv : ∀ i ∈ H, ConvexOn ℝ Set.univ (Q i)) (hcont : ∀ i ∈ H, Continuous (Q i))
    (hne : (argmin (agg H Q)).Nonempty) :
    ∃ P : E → E, ∀ w, P w ∈ argmin (agg H Q) ∧ ∀ v ∈ argmin (agg H Q), ‖w - P w‖ ≤ ‖w - v‖ := by
  set K := argmin (agg H Q)
  have hc : Continuous (agg H Q) := by
    have : agg H Q = fun w => ∑ i ∈ H, Q i w := rfl
    rw [this]; exact continuous_finsetSum _ fun i hi => hcont i hi
  have hK : K = ⋂ v, {w | agg H Q w ≤ agg H Q v} := by ext; simp [K, argmin]
  have hclosed : IsClosed K := by
    rw [hK]; exact isClosed_iInter fun v => isClosed_le hc continuous_const
  have hconvK : Convex ℝ K := by
    rw [hK]
    exact convex_iInter fun v => (convexOn_agg hconv).convex_le (agg H Q v) |>.inter
      convex_univ |> fun h => by simpa using h
  have hex : ∀ u, ∃ v ∈ K, ∀ v' ∈ K, ‖u - v‖ ≤ ‖u - v'‖ := by
    intro u
    obtain ⟨v, hv, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconvK u
    refine ⟨v, hv, fun v' hv' => ?_⟩
    rw [hmin]
    exact ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ (⟨v', hv'⟩ : K)
  choose P hP using hex
  exact ⟨P, fun w => ⟨(hP w).1, (hP w).2⟩⟩

end Projection

end RedundantOptimization
