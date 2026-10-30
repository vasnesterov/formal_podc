import Mathlib

-- CSLib candidate: finite joint distributions, pinnings, conditional marginals, TV distance
-- (`Cslib/Probability/Finite/Pinning.lean`).

/-!
# Joint distributions, pinnings, conditional marginals (§2 of Feng–Yin, PODC 2018)

A joint distribution over `Σ^V` is given by a nonnegative weight `w : (V → S) → ℝ` (the paper's
`μ`, or the Gibbs weight `w` of (1)); all probabilities are normalized by sums.

* A *pinning* `τ : V → Option S` is a partial configuration: `τ v = some c` fixes `v` to `c`,
  `τ v = none` leaves `v` free (the paper's `τ ∈ Σ^Λ` with `Λ = {v | τ v ≠ none}`).
* `Z w τ` is the total weight of configurations consistent with `τ`; `τ` is `Feasible` iff
  `0 < Z w τ` (the paper's `μ_Λ(τ) > 0`).
* `marg w τ v` is the conditional marginal `μ^τ_v`, `cond w τ` is the conditional
  distribution `μ^τ`.
* `tv p q = ½ ∑ |p x - q x|` is the total variation distance, `MultClose p q ε` the bound
  `err(p, q) ≤ ε` of the multiplicative error (2) (`e^{-ε} q ≤ p ≤ e^{ε} q` pointwise, which also
  covers the paper's convention for zeros).
-/

set_option linter.unusedSectionVars false

namespace Podc.LocalSamplingCounting

open Finset

open scoped Classical

/-- A partial configuration ("pinning") `τ ∈ Σ^Λ`, with `Λ = {v | τ v ≠ none}`. -/
abbrev Pin (V S : Type*) := V → Option S

variable {V S : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]

/-- `σ` extends the pinning `τ`. -/
def Cons (σ : V → S) (τ : Pin V S) : Prop := ∀ v c, τ v = some c → σ v = c

/-- Total weight of the configurations consistent with `τ`. -/
noncomputable def Z (w : (V → S) → ℝ) (τ : Pin V S) : ℝ :=
  ∑ σ, if Cons σ τ then w σ else 0

/-- `τ` is feasible: some configuration of positive weight extends it. -/
def Feasible (w : (V → S) → ℝ) (τ : Pin V S) : Prop := 0 < Z w τ

/-- Numerator of the conditional marginal. -/
noncomputable def margNum (w : (V → S) → ℝ) (τ : Pin V S) (v : V) (c : S) : ℝ :=
  ∑ σ, if Cons σ τ ∧ σ v = c then w σ else 0

/-- The conditional marginal distribution `μ^τ_v`. -/
noncomputable def marg (w : (V → S) → ℝ) (τ : Pin V S) (v : V) (c : S) : ℝ :=
  margNum w τ v c / Z w τ

/-- The conditional distribution `μ^τ` on configurations. -/
noncomputable def cond (w : (V → S) → ℝ) (τ : Pin V S) (σ : V → S) : ℝ :=
  if Cons σ τ then w σ / Z w τ else 0

/-- Marginal at `v` of a distribution `p` on configurations. -/
noncomputable def pmarg (p : (V → S) → ℝ) (v : V) (c : S) : ℝ :=
  ∑ σ, if σ v = c then p σ else 0

/-- Total variation distance `½ ‖p - q‖₁`. -/
noncomputable def tv {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (∑ x, |p x - q x|) / 2

/-- Multiplicative error at most `ε`: `e^{-ε} q ≤ p ≤ e^{ε} q` pointwise (the paper's
`err(q, p) ≤ ε`, eq. (2), with the convention `ln 0 - ln 0 = 0`). -/
def MultClose {α : Type*} (p q : α → ℝ) (ε : ℝ) : Prop :=
  ∀ x, Real.exp (-ε) * q x ≤ p x ∧ p x ≤ Real.exp ε * q x

/-- A probability vector. -/
def IsDist {α : Type*} [Fintype α] (p : α → ℝ) : Prop := (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-! ### Basic lemmas -/

section lemmas

variable {w : (V → S) → ℝ} {τ : Pin V S}

lemma Z_nonneg (hw : ∀ σ, 0 ≤ w σ) (τ : Pin V S) : 0 ≤ Z w τ :=
  sum_nonneg fun σ _ => by split_ifs <;> simp [hw]

lemma margNum_nonneg (hw : ∀ σ, 0 ≤ w σ) (τ : Pin V S) (v : V) (c : S) :
    0 ≤ margNum w τ v c :=
  sum_nonneg fun σ _ => by split_ifs <;> simp [hw]

lemma marg_nonneg (hw : ∀ σ, 0 ≤ w σ) (τ : Pin V S) (v : V) (c : S) : 0 ≤ marg w τ v c :=
  div_nonneg (margNum_nonneg hw τ v c) (Z_nonneg hw τ)

lemma cond_nonneg (hw : ∀ σ, 0 ≤ w σ) (τ : Pin V S) (σ : V → S) : 0 ≤ cond w τ σ := by
  unfold cond; split_ifs
  · exact div_nonneg (hw σ) (Z_nonneg hw τ)
  · rfl

lemma sum_margNum (τ : Pin V S) (v : V) : ∑ c, margNum w τ v c = Z w τ := by
  unfold margNum Z
  rw [Finset.sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  by_cases h : Cons σ τ
  · simp [h]
  · simp [h]

lemma sum_marg (hf : Feasible w τ) (v : V) : ∑ c, marg w τ v c = 1 := by
  unfold marg
  rw [← Finset.sum_div, sum_margNum, div_self hf.ne']

lemma isDist_marg (hw : ∀ σ, 0 ≤ w σ) (hf : Feasible w τ) (v : V) : IsDist (marg w τ v) :=
  ⟨marg_nonneg hw τ v, sum_marg hf v⟩

lemma le_Z_of_cons (hw : ∀ σ, 0 ≤ w σ) {σ : V → S} (h : Cons σ τ) : w σ ≤ Z w τ := by
  unfold Z
  have := Finset.single_le_sum (f := fun σ => if Cons σ τ then w σ else 0)
    (fun σ _ => by split_ifs <;> simp [hw]) (mem_univ σ)
  simpa [h] using this

lemma cons_update_iff {σ : V → S} {v : V} {c : S} :
    Cons σ (Function.update τ v (some c)) ↔ Cons σ τ ∧ σ v = c ∨
      (Cons σ (Function.update τ v (some c)) ∧ τ v ≠ none ∧ τ v ≠ some c) := by
  constructor
  · intro h
    by_cases h1 : τ v = none
    · left
      refine ⟨fun u d hu => ?_, h v c (by simp)⟩
      by_cases huv : u = v
      · subst huv; simp [h1] at hu
      · exact h u d (by simp [Function.update_of_ne huv, hu])
    · by_cases h2 : τ v = some c
      · left
        refine ⟨fun u d hu => ?_, h v c (by simp)⟩
        by_cases huv : u = v
        · subst huv; rw [h2] at hu; cases hu; exact h u c (by simp)
        · exact h u d (by simp [Function.update_of_ne huv, hu])
      · right; exact ⟨h, h1, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h, -⟩)
    · intro u d hu
      by_cases huv : u = v
      · subst huv; simp at hu; rw [← hu]; exact h2
      · exact h1 u d (by simpa [Function.update_of_ne huv] using hu)
    · exact h

/-- Pinning a free vertex: `Cons σ (τ[v ↦ c]) ↔ Cons σ τ ∧ σ v = c`. -/
lemma cons_update_of_none {σ : V → S} {v : V} {c : S} (hv : τ v = none) :
    Cons σ (Function.update τ v (some c)) ↔ Cons σ τ ∧ σ v = c := by
  rw [cons_update_iff]; simp [hv]

lemma margNum_eq_Z_update {v : V} (hv : τ v = none) (c : S) :
    margNum w τ v c = Z w (Function.update τ v (some c)) := by
  unfold margNum Z
  refine sum_congr rfl fun σ _ => ?_
  simp only [cons_update_of_none hv]

lemma marg_eq_div {v : V} (hv : τ v = none) (c : S) :
    marg w τ v c = Z w (Function.update τ v (some c)) / Z w τ := by
  rw [marg, margNum_eq_Z_update hv]

lemma Z_update_le (hw : ∀ σ, 0 ≤ w σ) {v : V} (hv : τ v = none) (c : S) :
    Z w (Function.update τ v (some c)) ≤ Z w τ := by
  rw [← margNum_eq_Z_update hv, ← sum_margNum τ v]
  exact Finset.single_le_sum (fun c _ => margNum_nonneg hw τ v c) (mem_univ c)

/-- For a free vertex `v` of a feasible `τ`: `τ[v ↦ c]` is feasible iff `μ^τ_v(c) > 0`. -/
lemma feasible_update_iff (hw : ∀ σ, 0 ≤ w σ) (hf : Feasible w τ) {v : V} (hv : τ v = none)
    (c : S) : Feasible w (Function.update τ v (some c)) ↔ 0 < marg w τ v c := by
  rw [marg_eq_div hv, Feasible]
  exact ⟨fun h => div_pos h hf, fun h => by
    rcases (Z_nonneg hw (Function.update τ v (some c))).lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at h; simp at h⟩

lemma not_feasible_iff (hw : ∀ σ, 0 ≤ w σ) {τ : Pin V S} : ¬ Feasible w τ ↔ Z w τ = 0 := by
  rw [Feasible, not_lt]; exact ⟨fun h => le_antisymm h (Z_nonneg hw τ), fun h => h.le⟩

lemma marg_eq_zero_of_not_feasible (hw : ∀ σ, 0 ≤ w σ) {v : V} (hv : τ v = none) {c : S}
    (h : ¬ Feasible w (Function.update τ v (some c))) : marg w τ v c = 0 := by
  rw [marg_eq_div hv, (not_feasible_iff hw).1 h, zero_div]

/-- Feasibility is inherited by smaller pinnings: if `τ` extends `ρ`, then `Z w τ ≤ Z w ρ`. -/
lemma Z_mono (hw : ∀ σ, 0 ≤ w σ) {ρ τ : Pin V S} (h : ∀ σ, Cons σ τ → Cons σ ρ) :
    Z w τ ≤ Z w ρ := by
  unfold Z
  refine sum_le_sum fun σ _ => ?_
  by_cases h1 : Cons σ τ
  · simp [h1, h σ h1]
  · simp only [h1, if_false]; split_ifs <;> simp [hw]

lemma sum_cond (hf : Feasible w τ) : ∑ σ, cond w τ σ = 1 := by
  unfold cond
  rw [show (∑ σ, if Cons σ τ then w σ / Z w τ else 0) = Z w τ / Z w τ
    by rw [Z, Finset.sum_div]; exact sum_congr rfl fun σ _ => by split_ifs <;> simp]
  exact div_self hf.ne'

lemma pmarg_cond (τ : Pin V S) (v : V) : pmarg (cond w τ) v = marg w τ v := by
  funext c
  unfold pmarg cond marg margNum
  rw [Finset.sum_div]
  refine sum_congr rfl fun σ _ => ?_
  by_cases h1 : Cons σ τ <;> by_cases h2 : σ v = c <;> simp [h1, h2]

/-! ### Total variation -/

lemma tv_nonneg {α : Type*} [Fintype α] (p q : α → ℝ) : 0 ≤ tv p q :=
  div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) zero_le_two

lemma tv_comm {α : Type*} [Fintype α] (p q : α → ℝ) : tv p q = tv q p := by
  unfold tv; simp_rw [abs_sub_comm]

lemma tv_triangle {α : Type*} [Fintype α] (p q r : α → ℝ) : tv p r ≤ tv p q + tv q r := by
  unfold tv
  rw [← add_div, ← sum_add_distrib]
  gcongr with x
  exact abs_sub_le _ _ _

/-- For two probability vectors, every pointwise difference is at most the TV distance. -/
lemma abs_sub_le_tv {α : Type*} [Fintype α] {p q : α → ℝ} (hp : ∑ x, p x = 1)
    (hq : ∑ x, q x = 1) (a : α) : |p a - q a| ≤ tv p q := by
  unfold tv
  have h0 : ∑ x, (p x - q x) = 0 := by rw [sum_sub_distrib, hp, hq, sub_self]
  have hsplit : p a - q a = -∑ x ∈ univ.erase a, (p x - q x) := by
    rw [← Finset.add_sum_erase _ _ (mem_univ a)] at h0; linarith
  have h1 : |p a - q a| ≤ ∑ x ∈ univ.erase a, |p x - q x| := by
    rw [hsplit, abs_neg]; exact abs_sum_le_sum_abs _ _
  rw [← Finset.add_sum_erase _ _ (mem_univ a)]
  linarith

/-- TV distance of marginals is at most the TV distance of joint distributions. -/
lemma tv_pmarg_le (p q : (V → S) → ℝ) (v : V) : tv (pmarg p v) (pmarg q v) ≤ tv p q := by
  unfold tv pmarg
  gcongr
  calc ∑ c, |(∑ σ, if σ v = c then p σ else 0) - ∑ σ, if σ v = c then q σ else 0|
      ≤ ∑ c, ∑ σ, if σ v = c then |p σ - q σ| else 0 := by
        gcongr with c
        rw [← sum_sub_distrib]
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun σ _ => ?_))
        split_ifs <;> simp
    _ = ∑ σ, |p σ - q σ| := by
        rw [Finset.sum_comm]; exact sum_congr rfl fun σ _ => by simp

/-- TV distance is convex in the first argument (mixtures). -/
lemma tv_mix_le {α ι : Type*} [Fintype α] (s : Finset ι) (a : ι → ℝ) (p : ι → α → ℝ)
    (q : α → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hsum : ∑ i ∈ s, a i = 1) :
    tv (fun x => ∑ i ∈ s, a i * p i x) q ≤ ∑ i ∈ s, a i * tv (p i) q := by
  unfold tv
  simp_rw [mul_div_assoc', ← Finset.sum_div, Finset.mul_sum]
  gcongr
  rw [Finset.sum_comm]
  refine sum_le_sum fun x _ => ?_
  have : (∑ i ∈ s, a i * p i x) - q x = ∑ i ∈ s, a i * (p i x - q x) := by
    simp_rw [mul_sub, sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [this]
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun i hi => ?_))
  rw [abs_mul, abs_of_nonneg (ha i hi)]

end lemmas

end Podc.LocalSamplingCounting
