import Mathlib

/-!
# Bayesian Ignorance, Section 4: public random bits as a substitute for the common prior

Formalization of Section 4 (and the appendix proof of Proposition 4.1) of
[Alon–Emek–Feldman–Tennenholtz, *Bayesian Ignorance*, PODC 2010].

## Setting

A *cost tuple* `φ = ⟨k, {A_i}, {T_i}, {C_{i,t}}⟩` consists of finitely many agents `ι`, finite nonempty
action sets `A i`, finite nonempty type sets `T i` and strictly positive costs `C i t a`.
A (pure) strategy profile is `s : ∀ i, T i → A i`; on the type profile `t` it has social cost
`K s t = ∑ i, C i t (s · (t ·))`, and `Kmin t = min_s K s t`.
Distributions are points of `stdSimplex ℝ _`.

* `RoE(φ) = r` (ratio of expectations): `r` is the least real such that every common prior `p` admits a
  strategy profile `s` with `E_p[K s] / E_p[Kmin] ≤ r`.
* `EoR(φ) = r` (expectation of ratios): `r` is the least real such that every `p` admits `s` with
  `E_p[K s / Kmin] ≤ r`.

## Main results

* `Podc.BayesianIgnorance.proposition_4_1` — Proposition 4.1 (`r* = r**`), for a positive matrix `M`
  and a positive vector `v`. We prove the stronger pointwise statement
  `roeBound_iff_eorBound : RoEBound M v r ↔ EoRBound M v r` for **every** `r`, via the bijection
  `p ↦ p · v / ⟨p, v⟩` of the simplex (inverse `p ↦ (p / v) / ⟨p, 1/v⟩`), which maps the ratio of
  expectations at `(p, i)` exactly to the expectation of ratios at `(p', i)`. We also prove that the
  minimum in the definition of `r*`/`r**` exists (`exists_isLeast_eorBound`).
* `Podc.BayesianIgnorance.CostTuple.roe_eq_eor` — `RoE(φ) = EoR(φ)` (both exist and coincide).
* `Podc.BayesianIgnorance.CostTuple.lemma_4_2` — Lemma 4.2: a single mixed strategy profile
  `q ∈ Δ(S)` (chosen with public random bits, without knowing the prior) achieves the ratio
  `RoE(φ)` against every common prior, and no `q` achieves any smaller ratio.
  The abstract matrix versions are `exists_mixed_roeBound` and `exists_lt_mixed_ratio`.

## Notes on the paper's proofs

* The appendix proof of Proposition 4.1 picks a prior `p` "such that for all `i` the ratio is
  `≥ r*`", i.e. it silently assumes that `sup_p min_i ratio(i, p)` is attained. This is true
  (continuity on a compact set) but not argued; our proof avoids it entirely.
* The paper says "`r*` is the minimum real such that …" without showing that the minimum exists;
  we prove it (`exists_isLeast_eorBound`): the set of admissible `r` is a nonempty, bounded below,
  closed set (an intersection of finite unions of closed rays).
* The paper's index sets `[m]`, `[n]` (and the type/action sets) must be nonempty; otherwise `r*` does
  not exist. We assume `Nonempty` explicitly, and also `Nonempty ι` (at least one agent, `k ≥ 1`), so
  that `K(s,t) = ∑_i C_{i,t}(·) > 0`.
* Proposition 4.1 only needs `v > 0` for the equivalence `RoEBound ↔ EoRBound`; `M > 0` is used only
  to show that the minimum exists (boundedness from below).
* In the proof of Lemma 4.2, the step "it suffices to consider priors concentrated on single type
  profiles" is exactly the summation in `exists_mixed_roeBound`: from
  `∑_s q(s) K(s,t) ≤ r · Kmin(t)` for every `t` one gets, multiplying by `p(t)` and summing, the bound
  for every prior `p`.
* The minimax step uses Sion's minimax theorem from Mathlib (`Sion.exists_isSaddlePointOn`) for the
  bilinear payoff `f(q, p) = ∑_s q(s) ∑_t p(t) K(s,t)/Kmin(t)` on `Δ(S) × Δ(T)`.
-/

namespace Podc.BayesianIgnorance

open Finset

-- Mathlib deprecated the set-valued `stdSimplex` in favour of the type `Convexity.StdSimplex`, but
-- Sion's minimax theorem (`Sion.exists_isSaddlePointOn`) is stated for convex compact *sets*.
set_option linter.deprecated false

section Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The "ratio of expectations" bound of Proposition 4.1: for every distribution `p ∈ Δ(n)` some row
`i` satisfies `(∑_j p(j) M(i,j)) / (∑_j p(j) v(j)) ≤ r`. -/
def RoEBound (M : m → n → ℝ) (v : n → ℝ) (r : ℝ) : Prop :=
  ∀ p ∈ stdSimplex ℝ n, ∃ i, (∑ j, p j * M i j) / (∑ j, p j * v j) ≤ r

/-- The "expectation of ratios" bound of Proposition 4.1: for every distribution `p ∈ Δ(n)` some row
`i` satisfies `∑_j p(j) M(i,j) / v(j) ≤ r`. -/
def EoRBound (M : m → n → ℝ) (v : n → ℝ) (r : ℝ) : Prop :=
  ∀ p ∈ stdSimplex ℝ n, ∃ i, ∑ j, p j * (M i j / v j) ≤ r

/-- The `p`-weighted sum of a positive vector is positive. -/
lemma sum_mul_pos_of_mem_stdSimplex {p : n → ℝ} (hp : p ∈ stdSimplex ℝ n) {w : n → ℝ}
    (hw : ∀ j, 0 < w j) : 0 < ∑ j, p j * w j := by
  apply Finset.sum_pos' (fun j _ => mul_nonneg (hp.1 j) (hw j).le)
  by_contra h
  push Not at h
  have h1 : ∑ j, p j ≤ 0 := Finset.sum_nonpos fun j _ => by
    have := h j (Finset.mem_univ _)
    by_contra hpj
    push Not at hpj
    linarith [mul_pos hpj (hw j)]
  linarith [hp.2]

variable {M : m → n → ℝ} {v : n → ℝ}

omit [Fintype m] in
/-- One direction of Proposition 4.1, pointwise in `r`. -/
lemma RoEBound.eorBound (hv : ∀ j, 0 < v j) {r : ℝ} (h : RoEBound M v r) : EoRBound M v r := by
  intro p hp
  set E := ∑ j, p j * (v j)⁻¹ with hE
  have hEpos : 0 < E := sum_mul_pos_of_mem_stdSimplex hp fun j => inv_pos.2 (hv j)
  set p' : n → ℝ := fun j => p j * (v j)⁻¹ / E with hp'
  have hp'mem : p' ∈ stdSimplex ℝ n := by
    refine ⟨fun j => div_nonneg (mul_nonneg (hp.1 j) (inv_pos.2 (hv j)).le) hEpos.le, ?_⟩
    simp only [hp', ← Finset.sum_div, ← hE, div_self hEpos.ne']
  obtain ⟨i, hi⟩ := h p' hp'mem
  refine ⟨i, le_of_eq_of_le ?_ hi⟩
  have h1 : ∑ j, p' j * v j = 1 / E := by
    simp only [hp']
    rw [← hp.2, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := (hv j).ne'
    field_simp
  have h2 : ∑ j, p' j * M i j = (∑ j, p j * (M i j / v j)) / E := by
    simp only [hp']
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := (hv j).ne'
    field_simp
  rw [h1, h2]
  field_simp

omit [Fintype m] in
/-- The other direction of Proposition 4.1, pointwise in `r`. -/
lemma EoRBound.roeBound (hv : ∀ j, 0 < v j) {r : ℝ} (h : EoRBound M v r) : RoEBound M v r := by
  intro p hp
  set D := ∑ j, p j * v j with hD
  have hDpos : 0 < D := sum_mul_pos_of_mem_stdSimplex hp hv
  set p' : n → ℝ := fun j => p j * v j / D with hp'
  have hp'mem : p' ∈ stdSimplex ℝ n := by
    refine ⟨fun j => div_nonneg (mul_nonneg (hp.1 j) (hv j).le) hDpos.le, ?_⟩
    simp only [hp', ← Finset.sum_div, ← hD, div_self hDpos.ne']
  obtain ⟨i, hi⟩ := h p' hp'mem
  refine ⟨i, le_of_eq_of_le ?_ hi⟩
  simp only [hp']
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := (hv j).ne'
  field_simp

omit [Fintype m] in
/-- Proposition 4.1, pointwise form: for every `r`, the ratio-of-expectations bound holds iff the
expectation-of-ratios bound holds. -/
theorem roeBound_iff_eorBound (hv : ∀ j, 0 < v j) (r : ℝ) :
    RoEBound M v r ↔ EoRBound M v r :=
  ⟨RoEBound.eorBound hv, EoRBound.roeBound hv⟩

omit [Fintype m] in
lemma setOf_roeBound_eq (hv : ∀ j, 0 < v j) :
    {r | RoEBound M v r} = {r | EoRBound M v r} :=
  Set.ext fun r => roeBound_iff_eorBound hv r

lemma isClosed_setOf_eorBound : IsClosed {r | EoRBound M v r} := by
  have : {r | EoRBound M v r} =
      ⋂ p ∈ stdSimplex ℝ n, ⋃ i, Set.Ici (∑ j, p j * (M i j / v j)) := by
    ext r
    simp [EoRBound]
  rw [this]
  exact isClosed_biInter fun p _ => isClosed_iUnion_of_finite fun i => isClosed_Ici

/-- The minimum in the definition of `r**` exists. -/
theorem exists_isLeast_eorBound [Nonempty m] [Nonempty n] (hM : ∀ i j, 0 < M i j)
    (hv : ∀ j, 0 < v j) : ∃ r, IsLeast {r | EoRBound M v r} r := by
  classical
  set S := {r | EoRBound M v r}
  have hne : S.Nonempty := by
    refine ⟨∑ i, ∑ j, M i j / v j, fun p hp => ⟨Classical.arbitrary m, ?_⟩⟩
    set i := Classical.arbitrary m
    calc ∑ j, p j * (M i j / v j) ≤ ∑ j, p j * (∑ i, ∑ j, M i j / v j) := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hp.1 j)
          calc M i j / v j ≤ ∑ j, M i j / v j :=
                Finset.single_le_sum (f := fun j => M i j / v j)
                  (fun j _ => (div_pos (hM i j) (hv j)).le) (Finset.mem_univ j)
            _ ≤ ∑ i, ∑ j, M i j / v j :=
                Finset.single_le_sum (f := fun i => ∑ j, M i j / v j)
                  (fun i _ => Finset.sum_nonneg fun j _ => (div_pos (hM i j) (hv j)).le)
                  (Finset.mem_univ i)
      _ = ∑ i, ∑ j, M i j / v j := by rw [← Finset.sum_mul, hp.2, one_mul]
  have hbdd : BddBelow S := by
    refine ⟨0, fun r hr => ?_⟩
    obtain ⟨i, hi⟩ := hr _ (single_mem_stdSimplex ℝ (Classical.arbitrary n))
    refine le_trans (Finset.sum_nonneg fun j _ => ?_) hi
    exact mul_nonneg (by simp [Pi.single_apply]; split_ifs <;> norm_num)
      (div_pos (hM i j) (hv j)).le
  exact ⟨sInf S, isClosed_setOf_eorBound.csInf_mem hne hbdd, fun r hr => csInf_le hbdd hr⟩

/-- **Proposition 4.1** of [Alon–Emek–Feldman–Tennenholtz 2010]: for a positive matrix `M` and a
positive vector `v`, the minimum `r*` of the reals `r` with
`∀ p ∈ Δ(n), ∃ i, (∑_j p(j) M(i,j)) / (∑_j p(j) v(j)) ≤ r` exists and equals the minimum `r**` of
the reals `r` with `∀ p ∈ Δ(n), ∃ i, ∑_j p(j) M(i,j) / v(j) ≤ r`. -/
theorem proposition_4_1 [Nonempty m] [Nonempty n] (hM : ∀ i j, 0 < M i j) (hv : ∀ j, 0 < v j) :
    ∃ r, IsLeast {r | RoEBound M v r} r ∧ IsLeast {r | EoRBound M v r} r := by
  obtain ⟨r, hr⟩ := exists_isLeast_eorBound hM hv
  refine ⟨r, ?_, hr⟩
  rw [setOf_roeBound_eq hv]
  exact hr

/-! ### Lemma 4.2, matrix form -/

/-- The linear functional `x ↦ ∑ i, x i * c i`. -/
private def dotLin {κ : Type*} [Fintype κ] (c : κ → ℝ) : (κ → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i * c i
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum, mul_assoc]

/-- Lemma 4.2 (existence part), matrix form: if the ratio-of-expectations bound `r` holds, then a
single mixed row `q ∈ Δ(m)` achieves it against every `p ∈ Δ(n)`. Proved via Sion's (von Neumann's)
minimax theorem; the final summation over `j` is the paper's "it suffices to consider priors
concentrated on single type profiles". -/
theorem exists_mixed_roeBound [Nonempty m] [Nonempty n]
    (hv : ∀ j, 0 < v j) {r : ℝ} (hr : RoEBound M v r) :
    ∃ q ∈ stdSimplex ℝ m, ∀ p ∈ stdSimplex ℝ n,
      (∑ j, p j * ∑ i, q i * M i j) / (∑ j, p j * v j) ≤ r := by
  classical
  have hE : EoRBound M v r := hr.eorBound hv
  set L : m → n → ℝ := fun i j => M i j / v j with hL
  -- the bilinear payoff
  set f : (m → ℝ) → (n → ℝ) → ℝ := fun q p => ∑ i, q i * ∑ j, p j * L i j with hf
  have hf' : ∀ q p, f q p = ∑ j, p j * ∑ i, q i * L i j := by
    intro q p
    simp only [hf, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hcont : Continuous fun qp : (m → ℝ) × (n → ℝ) => f qp.1 qp.2 := by
    simp only [hf]
    fun_prop
  obtain ⟨q, hq, p₀, hp₀, hsad⟩ := Sion.exists_isSaddlePointOn (f := f)
    (X := stdSimplex ℝ m) (Y := stdSimplex ℝ n)
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary m)⟩ (convex_stdSimplex ℝ m)
    (isCompact_stdSimplex ℝ m)
    (fun p _ => (hcont.comp (Continuous.prodMk_left p)).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun p _ => by
      have : (fun q => f q p) = dotLin (fun i => ∑ j, p j * L i j) := rfl
      rw [this]
      exact ((dotLin _).convexOn (convex_stdSimplex ℝ m)).quasiconvexOn)
    (convex_stdSimplex ℝ n) ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary n)⟩
    (isCompact_stdSimplex ℝ n)
    (fun q _ => (hcont.comp (Continuous.prodMk_right q)).upperSemicontinuous.upperSemicontinuousOn _)
    (fun q _ => by
      have : (fun p => f q p) = dotLin (fun j => ∑ i, q i * L i j) := funext fun p => hf' q p
      rw [this]
      exact ((dotLin _).concaveOn (convex_stdSimplex ℝ n)).quasiconcaveOn)
  refine ⟨q, hq, ?_⟩
  -- the value of the game is at most `r`
  obtain ⟨i₀, hi₀⟩ := hE p₀ hp₀
  have hval : ∀ p ∈ stdSimplex ℝ n, f q p ≤ r := by
    intro p hp
    refine (hsad _ (single_mem_stdSimplex ℝ i₀) p hp).trans (le_of_eq_of_le ?_ hi₀)
    simp [hf, L, Pi.single_apply]
  -- priors concentrated on single type profiles
  have hpt : ∀ j, ∑ i, q i * M i j ≤ r * v j := by
    intro j
    have h := hval _ (single_mem_stdSimplex ℝ j)
    rw [hf'] at h
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, L] at h
    simp only [mul_div_assoc', ← Finset.sum_div] at h
    exact (div_le_iff₀ (hv j)).1 h
  -- summing over `j` with weights `p j`
  intro p hp
  rw [div_le_iff₀ (sum_mul_pos_of_mem_stdSimplex hp hv), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  calc p j * ∑ i, q i * M i j ≤ p j * (r * v j) := mul_le_mul_of_nonneg_left (hpt j) (hp.1 j)
    _ = r * (p j * v j) := by ring

/-- Lemma 4.2 (optimality part), matrix form: if `r` is the least ratio-of-expectations bound, then
no mixed row `q ∈ Δ(m)` achieves any `r' < r` against all `p ∈ Δ(n)`. -/
theorem exists_lt_mixed_ratio (hv : ∀ j, 0 < v j) {r : ℝ} (hr : IsLeast {r | RoEBound M v r} r)
    {q : m → ℝ} (hq : q ∈ stdSimplex ℝ m) {r' : ℝ} (hr' : r' < r) :
    ∃ p ∈ stdSimplex ℝ n, r' < (∑ j, p j * ∑ i, q i * M i j) / (∑ j, p j * v j) := by
  have hnot : ¬ RoEBound M v r' := fun h => absurd (hr.2 h) (not_le.2 hr')
  simp only [RoEBound, not_forall, not_exists, not_le] at hnot
  obtain ⟨p, hp, hlt⟩ := hnot
  refine ⟨p, hp, ?_⟩
  have hD := sum_mul_pos_of_mem_stdSimplex hp hv
  have hlt' : ∀ i, r' * (∑ j, p j * v j) < ∑ j, p j * M i j := fun i =>
    (lt_div_iff₀ hD).1 (hlt i)
  rw [lt_div_iff₀ hD]
  have hswap : ∑ j, p j * ∑ i, q i * M i j = ∑ i, q i * ∑ j, p j * M i j := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hpos := sum_mul_pos_of_mem_stdSimplex hq
    (w := fun i => ∑ j, p j * M i j - r' * (∑ j, p j * v j)) fun i => sub_pos.2 (hlt' i)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq.2, one_mul] at hpos
  rw [hswap]
  linarith

end Matrix

/-! ### Games: `RoE(φ) = EoR(φ)` and Lemma 4.2 -/

/-- The 4-tuple `φ = ⟨k, {A_i}, {T_i}, {C_{i,t}}⟩` of Section 4: agents `ι`, action sets `A i`,
type sets `T i`, and strictly positive costs `C i t a` of agent `i` on type profile `t` and action
profile `a`. -/
structure CostTuple (ι : Type*) (A T : ι → Type*) where
  /-- `C i t a` is the cost `C_{i,t}(a)` of agent `i`. -/
  C : (i : ι) → (∀ j, T j) → (∀ j, A j) → ℝ
  /-- All costs are strictly positive. -/
  C_pos : ∀ i t a, 0 < C i t a

namespace CostTuple

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {A T : ι → Type*}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
  [∀ i, Fintype (T i)] [∀ i, Nonempty (T i)] [∀ i, DecidableEq (T i)]
  (φ : CostTuple ι A T)

/-- Social cost `K(s, t) = ∑_i C_{i,t}(s(t))` of the (pure) strategy profile `s : ∀ i, T i → A i`
on the type profile `t`. -/
def K (s : ∀ i, T i → A i) (t : ∀ i, T i) : ℝ :=
  ∑ i, φ.C i t (fun j => s j (t j))

/-- `Kmin t = min_{s'} K(s', t)`, the optimal social cost on the type profile `t`. -/
noncomputable def Kmin (t : ∀ i, T i) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun s : ∀ i, T i → A i => φ.K s t)

omit [DecidableEq ι] [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
  [∀ i, Fintype (T i)] [∀ i, Nonempty (T i)] [∀ i, DecidableEq (T i)] in
lemma K_pos (s : ∀ i, T i → A i) (t : ∀ i, T i) : 0 < φ.K s t :=
  Finset.sum_pos (fun _ _ => φ.C_pos _ _ _) Finset.univ_nonempty

omit [∀ i, Nonempty (T i)] in
lemma Kmin_pos (t : ∀ i, T i) : 0 < φ.Kmin t :=
  (Finset.lt_inf'_iff _).2 fun s _ => φ.K_pos s t

/-- `RoE(φ) = r` (ratio of expectations): `r` is the least real such that for every common prior
`p ∈ Δ(T)` some strategy profile `s` has `(∑_t p(t) K(s,t)) / (∑_t p(t) Kmin(t)) ≤ r`. -/
def IsRoE (r : ℝ) : Prop :=
  IsLeast {r | ∀ p ∈ stdSimplex ℝ (∀ i, T i), ∃ s : ∀ i, T i → A i,
    (∑ t, p t * φ.K s t) / (∑ t, p t * φ.Kmin t) ≤ r} r

/-- `EoR(φ) = r` (expectation of ratios): `r` is the least real such that for every common prior
`p ∈ Δ(T)` some strategy profile `s` has `∑_t p(t) K(s,t) / Kmin(t) ≤ r`. -/
def IsEoR (r : ℝ) : Prop :=
  IsLeast {r | ∀ p ∈ stdSimplex ℝ (∀ i, T i), ∃ s : ∀ i, T i → A i,
    ∑ t, p t * (φ.K s t / φ.Kmin t) ≤ r} r

omit [Nonempty ι] [∀ i, Nonempty (T i)] in
lemma isRoE_iff (r : ℝ) : φ.IsRoE r ↔ IsLeast {r | RoEBound φ.K φ.Kmin r} r := Iff.rfl

omit [Nonempty ι] [∀ i, Nonempty (T i)] in
lemma isEoR_iff (r : ℝ) : φ.IsEoR r ↔ IsLeast {r | EoRBound φ.K φ.Kmin r} r := Iff.rfl

/-- `RoE(φ) = EoR(φ)` (Section 4 of [Alon–Emek–Feldman–Tennenholtz 2010], as a special case of
Proposition 4.1): both quantities exist and coincide. -/
theorem roe_eq_eor : ∃ r, φ.IsRoE r ∧ φ.IsEoR r :=
  proposition_4_1 (fun s t => φ.K_pos s t) φ.Kmin_pos

omit [∀ i, Nonempty (T i)] in
/-- `RoE(φ) = r ↔ EoR(φ) = r`. -/
theorem isRoE_iff_isEoR (r : ℝ) : φ.IsRoE r ↔ φ.IsEoR r := by
  rw [isRoE_iff, isEoR_iff, setOf_roeBound_eq φ.Kmin_pos]

/-- **Lemma 4.2** of [Alon–Emek–Feldman–Tennenholtz 2010] (public random bits replace the common
prior): if `RoE(φ) = r`, then there is a distribution `q ∈ Δ(S)` over strategy profiles such that for
every common prior `p ∈ Δ(T)`,
`(∑_t p(t) ∑_s q(s) K(s,t)) / (∑_t p(t) Kmin(t)) ≤ r`,
and this fails for every `r' < r` (for every `q` there is a prior `p` with ratio `> r'`). -/
theorem lemma_4_2 {r : ℝ} (hr : φ.IsRoE r) :
    (∃ q ∈ stdSimplex ℝ (∀ i, T i → A i), ∀ p ∈ stdSimplex ℝ (∀ i, T i),
      (∑ t, p t * ∑ s, q s * φ.K s t) / (∑ t, p t * φ.Kmin t) ≤ r) ∧
    ∀ q ∈ stdSimplex ℝ (∀ i, T i → A i), ∀ r' < r, ∃ p ∈ stdSimplex ℝ (∀ i, T i),
      r' < (∑ t, p t * ∑ s, q s * φ.K s t) / (∑ t, p t * φ.Kmin t) :=
  ⟨exists_mixed_roeBound φ.Kmin_pos hr.1,
    fun _ hq _ hr' => exists_lt_mixed_ratio φ.Kmin_pos hr hq hr'⟩

end CostTuple

end Podc.BayesianIgnorance
