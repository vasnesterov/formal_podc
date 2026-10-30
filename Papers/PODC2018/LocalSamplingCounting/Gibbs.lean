import Papers.PODC2018.LocalSamplingCounting.Basic

-- CSLib candidate: Gibbs distributions (factor graphs) and the spatial Markov property
-- (`Cslib/Probability/Finite/Gibbs.lean`).

/-!
# Gibbs distributions and the spatial Markov property (Definitions 2.3–2.5, Proposition 2.1)

* `Factor V S`: a constraint `(f, S)`: a nonnegative function of the values on its scope.
* `gibbsW F σ = ∏ᵢ fᵢ(σ_{Sᵢ})` (eq. (1)); `gibbsWOn F B` keeps only factors with scope `⊆ B`.
* `LocFeasible F τ`: no constraint inside the pinned set is violated (Definition 2.5);
  `LocallyAdmissible F`: feasible ⇔ locally feasible for every pinning.
* `marg_eq_local` (the form of Proposition 2.1 used by the algorithms of Lemma 4.1 and
  Theorem 5.1): if all vertices of `B \ I` are pinned and every factor meeting `I` lies inside `B`,
  then the marginal at `v ∈ I` is the one computed from the factors inside `B` and the pinning on
  `B` alone (the formula `μ^{τ'}_v(c) = ∑_{σ∈C, σ_v=c} w_B(σ) / ∑_{σ∈C} w_B(σ)` of the paper).
-/

set_option linter.unusedSectionVars false

namespace Podc.LocalSamplingCounting

open Finset

open scoped Classical

variable {V S : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]

/-- A constraint (factor): a nonnegative function depending only on the values on `scope`. -/
structure Factor (V S : Type*) where
  /-- The scope `S ⊆ V`. -/
  scope : Finset V
  /-- The constraint function, extended to full configurations. -/
  f : (V → S) → ℝ
  nonneg : ∀ σ, 0 ≤ f σ
  dep : ∀ σ σ', (∀ u ∈ scope, σ u = σ' u) → f σ = f σ'

variable {ι : Type*} [Fintype ι]

/-- The Gibbs weight `w(σ) = ∏_{(f,S)∈F} f(σ_S)` (eq. (1)). -/
noncomputable def gibbsW (F : ι → Factor V S) (σ : V → S) : ℝ := ∏ i, (F i).f σ

/-- The weight `w_B` using only the factors whose scope lies in `B`. -/
noncomputable def gibbsWOn (F : ι → Factor V S) (B : Set V) (σ : V → S) : ℝ :=
  ∏ i ∈ univ.filter (fun i => (↑(F i).scope : Set V) ⊆ B), (F i).f σ

/-- The pinning `τ` restricted to `B` (vertices outside `B` become free). -/
noncomputable def restrictPin (τ : Pin V S) (B : Set V) : Pin V S := fun u => if u ∈ B then τ u else none

/-- The pinned set `Λ` of a pinning. -/
def dom (τ : Pin V S) : Set V := {u | τ u ≠ none}

/-- **Definition 2.5.** `τ` is locally feasible: every constraint whose scope is pinned is
satisfied (any extension `σ` of `τ` may be used to evaluate it). -/
def LocFeasible (F : ι → Factor V S) (τ : Pin V S) : Prop :=
  ∀ i, (↑(F i).scope : Set V) ⊆ dom τ → ∀ σ, Cons σ τ → 0 < (F i).f σ

/-- **Definition 2.5.** The Gibbs distribution is locally admissible. -/
def LocallyAdmissible (F : ι → Factor V S) : Prop :=
  ∀ τ : Pin V S, Feasible (gibbsW F) τ ↔ LocFeasible F τ

lemma gibbsW_nonneg (F : ι → Factor V S) (σ : V → S) : 0 ≤ gibbsW F σ :=
  prod_nonneg fun i _ => (F i).nonneg σ

lemma gibbsWOn_nonneg (F : ι → Factor V S) (B : Set V) (σ : V → S) : 0 ≤ gibbsWOn F B σ :=
  prod_nonneg fun i _ => (F i).nonneg σ

lemma gibbsW_eq_mul (F : ι → Factor V S) (B : Set V) (σ : V → S) :
    gibbsW F σ = gibbsWOn F B σ *
      ∏ i ∈ univ.filter (fun i => ¬ (↑(F i).scope : Set V) ⊆ B), (F i).f σ := by
  unfold gibbsW gibbsWOn
  rw [prod_filter_mul_prod_filter_not]

/-- `restrictPin τ B` only depends on `τ` on `B`. -/
lemma restrictPin_congr {τ τ' : Pin V S} {B : Set V} (h : ∀ u ∈ B, τ u = τ' u) :
    restrictPin τ B = restrictPin τ' B := by
  funext u; unfold restrictPin; split_ifs with hu
  · exact h u hu
  · rfl

section split

variable (I : Set V)

/-- Splitting a configuration into its values on `I` and off `I`. -/
noncomputable abbrev splitE : (V → S) ≃ ({x // x ∈ I} → S) × ({x // x ∉ I} → S) :=
  Equiv.piEquivPiSubtypeProd (· ∈ I) (fun _ => S)

lemma splitE_symm_apply_mem (x : {x // x ∈ I} → S) (y : {x // x ∉ I} → S) {u : V}
    (hu : u ∈ I) : (splitE I).symm (x, y) u = x ⟨u, hu⟩ := by
  simp [Equiv.piEquivPiSubtypeProd, hu]

lemma splitE_symm_apply_notMem (x : {x // x ∈ I} → S) (y : {x // x ∉ I} → S) {u : V}
    (hu : u ∉ I) : (splitE I).symm (x, y) u = y ⟨u, hu⟩ := by
  simp [Equiv.piEquivPiSubtypeProd, hu]

lemma sum_split (Φ : (V → S) → ℝ) :
    ∑ σ, Φ σ = ∑ x : {x // x ∈ I} → S, ∑ y : {x // x ∉ I} → S, Φ ((splitE I).symm (x, y)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (splitE I).symm _ _ (fun _ => rfl)).symm

/-- Consistency of `x` (values on `I`) with `τ`. -/
def ConsIn (τ : Pin V S) (x : {x // x ∈ I} → S) : Prop :=
  ∀ (u : V) (hu : u ∈ I) c, τ u = some c → x ⟨u, hu⟩ = c

/-- Consistency of `y` (values off `I`) with `τ`. -/
def ConsOut (τ : Pin V S) (y : {x // x ∉ I} → S) : Prop :=
  ∀ (u : V) (hu : u ∉ I) c, τ u = some c → y ⟨u, hu⟩ = c

lemma cons_splitE_symm (τ : Pin V S) (x : {x // x ∈ I} → S) (y : {x // x ∉ I} → S) :
    Cons ((splitE I).symm (x, y)) τ ↔ ConsIn I τ x ∧ ConsOut I τ y := by
  constructor
  · intro h
    refine ⟨fun u hu c hc => ?_, fun u hu c hc => ?_⟩
    · rw [← splitE_symm_apply_mem I x y hu]; exact h u c hc
    · rw [← splitE_symm_apply_notMem I x y hu]; exact h u c hc
  · rintro ⟨h1, h2⟩ u c hc
    by_cases hu : u ∈ I
    · rw [splitE_symm_apply_mem I x y hu]; exact h1 u hu c hc
    · rw [splitE_symm_apply_notMem I x y hu]; exact h2 u hu c hc

/-- Abstract factorization: if, on configurations consistent with `π`, the weight `W` splits as
`g(x) · h(y)`, then constrained sums split accordingly. -/
lemma sum_cons_factor (π : Pin V S) (W : (V → S) → ℝ) (g : ({x // x ∈ I} → S) → ℝ)
    (h : ({x // x ∉ I} → S) → ℝ)
    (hW : ∀ x y, ConsIn I π x → ConsOut I π y → W ((splitE I).symm (x, y)) = g x * h y)
    (P : ({x // x ∈ I} → S) → Prop) [DecidablePred P] :
    (∑ σ, if Cons σ π ∧ P ((splitE I σ).1) then W σ else 0) =
      (∑ x, if ConsIn I π x ∧ P x then g x else 0) * ∑ y, if ConsOut I π y then h y else 0 := by
  rw [sum_split I, sum_mul]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  simp only [Equiv.apply_symm_apply, cons_splitE_symm]
  by_cases h1 : ConsIn I π x
  · by_cases h2 : ConsOut I π y
    · rw [hW x y h1 h2]; by_cases h3 : P x <;> simp [h1, h2, h3]
    · simp [h2]
  · simp [h1]

end split

variable {F : ι → Factor V S}

/-- **Proposition 2.1, in the form used by the local algorithms.** Let `v ∈ I ⊆ B`, let every
vertex of `B \ I` be pinned by the feasible pinning `τ`, and let every factor whose scope meets
`I` have scope inside `B`. Then the conditional marginal `μ^τ_v` equals the marginal computed from
the factors inside `B` and the pinning `τ` restricted to `B`. In particular it is determined by
`τ` on `B` and by the factors inside `B`. -/
theorem marg_eq_local {I B : Set V} (hIB : I ⊆ B) {v : V} (hv : v ∈ I)
    (hF : ∀ i, (∃ u ∈ (F i).scope, u ∈ I) → (↑(F i).scope : Set V) ⊆ B)
    {τ : Pin V S} (hpin : ∀ u ∈ B, u ∉ I → τ u ≠ none) (hτ : Feasible (gibbsW F) τ) :
    marg (gibbsW F) τ v = marg (gibbsWOn F B) (restrictPin τ B) v := by
  -- a reference configuration consistent with `τ`
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, Cons σ₀ τ := by
    by_contra h; push_neg at h
    unfold Feasible Z at hτ
    simp [h] at hτ
  set y₀ := (splitE I σ₀).2
  set x₀ := (splitE I σ₀).1
  have hy₀ : ConsOut I τ y₀ := by
    have := (cons_splitE_symm I τ x₀ y₀).1 (by
      rw [show (x₀, y₀) = splitE I σ₀ from Prod.mk.eta, Equiv.symm_apply_apply]; exact hσ₀)
    exact this.2
  let g : ({x // x ∈ I} → S) → ℝ := fun x => gibbsWOn F B ((splitE I).symm (x, y₀))
  let hOut : ({x // x ∉ I} → S) → ℝ := fun y =>
    ∏ i ∈ univ.filter (fun i => ¬ (↑(F i).scope : Set V) ⊆ B), (F i).f ((splitE I).symm (x₀, y))
  -- factors inside `B` only see `x` and the pinned values on `B \ I`
  have hgB : ∀ (π : Pin V S), (∀ u ∈ B, π u = τ u) → ∀ x y, ConsOut I π y →
      gibbsWOn F B ((splitE I).symm (x, y)) = g x := by
    intro π hπ x y hy
    unfold gibbsWOn
    refine prod_congr rfl fun i hi => (F i).dep _ _ fun u hu => ?_
    have huB : u ∈ B := (mem_filter.1 hi).2 (by simpa using hu)
    by_cases huI : u ∈ I
    · rw [splitE_symm_apply_mem I _ _ huI, splitE_symm_apply_mem I _ _ huI]
    · rw [splitE_symm_apply_notMem I _ _ huI, splitE_symm_apply_notMem I _ _ huI]
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 (hpin u huB huI)
      rw [hy u huI c ((hπ u huB).trans hc), hy₀ u huI c hc]
  -- factors outside `B` do not see `x`
  have hout : ∀ x y, ∏ i ∈ univ.filter (fun i => ¬ (↑(F i).scope : Set V) ⊆ B),
      (F i).f ((splitE I).symm (x, y)) = hOut y := by
    intro x y
    refine prod_congr rfl fun i hi => (F i).dep _ _ fun u hu => ?_
    have huI : u ∉ I := fun h => (mem_filter.1 hi).2 (hF i ⟨u, hu, h⟩)
    rw [splitE_symm_apply_notMem I _ _ huI, splitE_symm_apply_notMem I _ _ huI]
  have hW : ∀ x y, ConsIn I τ x → ConsOut I τ y →
      gibbsW F ((splitE I).symm (x, y)) = g x * hOut y := by
    intro x y _ hy
    rw [gibbsW_eq_mul F B, hgB τ (fun _ _ => rfl) x y hy, hout]
  have hWB : ∀ x y, ConsIn I (restrictPin τ B) x → ConsOut I (restrictPin τ B) y →
      gibbsWOn F B ((splitE I).symm (x, y)) = g x * 1 := by
    intro x y _ hy
    rw [mul_one]
    exact hgB (restrictPin τ B) (fun u hu => by simp [restrictPin, hu]) x y hy
  have hIn : ∀ x, ConsIn I (restrictPin τ B) x ↔ ConsIn I τ x := by
    intro x
    unfold ConsIn restrictPin
    constructor
    · intro h u hu c hc; exact h u hu c (by simp [hIB hu, hc])
    · intro h u hu c hc; exact h u hu c (by simpa [hIB hu] using hc)
  -- write marginals through the split
  have hmN : ∀ (π : Pin V S) (W : (V → S) → ℝ) (c : S),
      margNum W π v c = ∑ σ, if Cons σ π ∧ (splitE I σ).1 ⟨v, hv⟩ = c
        then W σ else 0 := by
    intro π W c
    unfold margNum
    refine sum_congr rfl fun σ _ => ?_
    simp [Equiv.piEquivPiSubtypeProd]
  have hZ : ∀ (π : Pin V S) (W : (V → S) → ℝ),
      Z W π = ∑ σ, if Cons σ π ∧ True then W σ else 0 := by
    intro π W; unfold Z; simp
  funext c
  unfold marg
  rw [hmN, hZ, sum_cons_factor I τ _ g hOut hW (fun x => x ⟨v, hv⟩ = c),
    sum_cons_factor I τ _ g hOut hW (fun _ => True),
    hmN, hZ, sum_cons_factor I _ _ g (fun _ => 1) hWB (fun x => x ⟨v, hv⟩ = c),
    sum_cons_factor I _ _ g (fun _ => 1) hWB (fun _ => True)]
  simp only [hIn, and_true]
  -- cancel the outer factors
  have hH : (∑ y, if ConsOut I τ y then hOut y else 0) ≠ 0 := by
    intro h0
    have : Z (gibbsW F) τ = 0 := by
      rw [hZ, sum_cons_factor I τ _ g hOut hW (fun _ => True), h0, mul_zero]
    exact hτ.ne' this
  have hH' : (∑ y, if ConsOut I (restrictPin τ B) y then (1 : ℝ) else 0) ≠ 0 := by
    have hy0' : ConsOut I (restrictPin τ B) y₀ := by
      intro u hu c hc
      unfold restrictPin at hc
      split_ifs at hc
      · exact hy₀ u hu c hc
    refine ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ?_)
    have := Finset.single_le_sum (f := fun y => if ConsOut I (restrictPin τ B) y then (1 : ℝ)
      else 0) (fun y _ => by split_ifs <;> norm_num) (mem_univ y₀)
    simpa [hy0'] using this
  rw [mul_div_mul_right _ _ hH, mul_div_mul_right _ _ hH']

end Podc.LocalSamplingCounting
