import Mathlib

/-!
# Finite i.i.d. random fields with resampling (conditioning on a region)

Randomness for anonymous randomized LOCAL algorithms: every node `i : ι` of a (possibly infinite)
network gets an independent random value `x i` from a finite probability space `(Ω, μ)`. All events
we consider depend on finitely many nodes, so probabilities are computed by summing over the
configurations `y : F → Ω` on a finite set `F` of nodes (the field is `default` outside `F`); the
result does not depend on `F` as long as `F` contains the nodes the event depends on
(`expect_eq_of_dependsOn`).

Conditioning on the values in a region `S` is expressed by *resampling* the field outside `S`:
`condE μ F S h x` is the expectation of `h` when the values in `S` are those of `x` and the values
outside `S` are fresh. The key facts are the tower property `expect_mul_condE`, the reduction
`condE_eq_of_dependsOn` (an event that depends on `T ∪ D` with `T ⊆ S`, `D ∩ S = ∅` has the same
conditional probability given `S` and given `T`), and conditional independence of events depending
on pairwise disjoint regions outside `S` (`condE_prod`). All proofs are by finite sums and the
measure-preserving involution `(y, y') ↦ (y|_S ∪ y'|_{Sᶜ}, y'|_S ∪ y|_{Sᶜ})`.

-- CSLib candidate (`Cslib/Probability/Finite/Field.lean`).
-/

-- CSLib candidate
namespace Podc.MinimalSymmetryBreaking

open Finset Function
open scoped Classical

noncomputable section

/-- A probability distribution on a finite type `Ω`, given by its weights. -/
structure FinDist (Ω : Type*) [Fintype Ω] where
  /-- The probability of each outcome. -/
  w : Ω → ℝ
  nonneg : ∀ a, 0 ≤ w a
  sum_eq_one : ∑ a, w a = 1

variable {ι Ω : Type*} [Fintype Ω] [Inhabited Ω] (μ : FinDist Ω)

/-- Extend a configuration on the finite set `F` by the default value outside `F`. -/
def ext (F : Finset ι) (y : F → Ω) : ι → Ω := fun i => if h : i ∈ F then y ⟨i, h⟩ else default

/-- The product weight of a configuration on `F`. -/
def wt {F : Finset ι} (y : F → Ω) : ℝ := ∏ i, μ.w (y i)

/-- The expectation of `g` when the field is i.i.d. `μ` on `F` (and `default` outside `F`). -/
def expect (F : Finset ι) (g : (ι → Ω) → ℝ) : ℝ := ∑ y : F → Ω, wt μ y * g (ext F y)

/-- The indicator function of an event. -/
def ind (E : (ι → Ω) → Prop) (x : ι → Ω) : ℝ := if E x then 1 else 0

/-- The probability of an event when the field is i.i.d. `μ` on `F`. -/
def prob (F : Finset ι) (E : (ι → Ω) → Prop) : ℝ := expect μ F (ind E)

/-- Conditional expectation of `h` given the values of the field in `S`: the values in `S` are
taken from `x`, the others are resampled (i.i.d. `μ` on `F`, `default` outside `F ∪ S`). -/
def condE (F : Finset ι) (S : Set ι) (h : (ι → Ω) → ℝ) (x : ι → Ω) : ℝ :=
  expect μ F (fun z => h (S.piecewise x z))

/-- Conditional probability of `E` given the values of the field in `S`. -/
def cond (F : Finset ι) (S : Set ι) (E : (ι → Ω) → Prop) (x : ι → Ω) : ℝ :=
  condE μ F S (ind E) x

/-! ### Basic facts -/

variable {μ}

lemma ind_nonneg (E : (ι → Ω) → Prop) (x : ι → Ω) : 0 ≤ ind E x := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (E : (ι → Ω) → Prop) (x : ι → Ω) : ind E x ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

lemma wt_nonneg {F : Finset ι} (y : F → Ω) : 0 ≤ wt μ y :=
  prod_nonneg fun i _ => μ.nonneg (y i)

lemma sum_wt (F : Finset ι) : ∑ y : F → Ω, wt μ y = 1 := by
  unfold wt
  rw [← Fintype.prod_sum (fun (_ : F) a => μ.w a)]
  simp [μ.sum_eq_one]

lemma expect_const (F : Finset ι) (c : ℝ) : expect μ F (fun _ => c) = c := by
  unfold expect
  rw [← sum_mul, sum_wt, one_mul]

lemma expect_mono {F : Finset ι} {g h : (ι → Ω) → ℝ} (hgh : ∀ x, g x ≤ h x) :
    expect μ F g ≤ expect μ F h :=
  sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hgh _) (wt_nonneg y)

lemma expect_nonneg {F : Finset ι} {g : (ι → Ω) → ℝ} (hg : ∀ x, 0 ≤ g x) : 0 ≤ expect μ F g :=
  sum_nonneg fun y _ => mul_nonneg (wt_nonneg y) (hg _)

lemma expect_add (F : Finset ι) (g h : (ι → Ω) → ℝ) :
    expect μ F (fun x => g x + h x) = expect μ F g + expect μ F h := by
  simp only [expect, mul_add, sum_add_distrib]

lemma expect_sub (F : Finset ι) (g h : (ι → Ω) → ℝ) :
    expect μ F (fun x => g x - h x) = expect μ F g - expect μ F h := by
  simp only [expect, mul_sub, sum_sub_distrib]

lemma expect_mul_const (F : Finset ι) (g : (ι → Ω) → ℝ) (c : ℝ) :
    expect μ F (fun x => g x * c) = expect μ F g * c := by
  simp only [expect, sum_mul]
  exact sum_congr rfl fun _ _ => by ring

lemma expect_const_mul (F : Finset ι) (g : (ι → Ω) → ℝ) (c : ℝ) :
    expect μ F (fun x => c * g x) = c * expect μ F g := by
  simp only [expect, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

lemma expect_sum {κ : Type*} (F : Finset ι) (s : Finset κ) (g : κ → (ι → Ω) → ℝ) :
    expect μ F (fun x => ∑ j ∈ s, g j x) = ∑ j ∈ s, expect μ F (g j) := by
  simp only [expect, mul_sum]
  exact sum_comm

lemma prob_nonneg (F : Finset ι) (E : (ι → Ω) → Prop) : 0 ≤ prob μ F E :=
  expect_nonneg (ind_nonneg E)

lemma prob_le_one (F : Finset ι) (E : (ι → Ω) → Prop) : prob μ F E ≤ 1 := by
  calc prob μ F E ≤ expect μ F (fun _ => 1) := expect_mono (ind_le_one E)
    _ = 1 := expect_const F 1

lemma prob_mono {F : Finset ι} {E E' : (ι → Ω) → Prop} (h : ∀ x, E x → E' x) :
    prob μ F E ≤ prob μ F E' :=
  expect_mono fun x => by
    unfold ind; by_cases hE : E x
    · simp [hE, h x hE]
    · simp only [hE, if_false]; split_ifs <;> norm_num

lemma condE_nonneg {F : Finset ι} {S : Set ι} {h : (ι → Ω) → ℝ} (hh : ∀ x, 0 ≤ h x)
    (x : ι → Ω) : 0 ≤ condE μ F S h x :=
  expect_nonneg fun _ => hh _

lemma cond_nonneg (F : Finset ι) (S : Set ι) (E : (ι → Ω) → Prop) (x : ι → Ω) :
    0 ≤ cond μ F S E x :=
  condE_nonneg (ind_nonneg E) x

/-! ### The resampling involution -/

/-- Mix two configurations on `F`: take `y` on `S` and `y'` elsewhere. -/
def mix {F : Finset ι} (S : Set ι) (y y' : F → Ω) : F → Ω :=
  fun i => if (i : ι) ∈ S then y i else y' i

lemma ext_mix (F : Finset ι) (S : Set ι) (y y' : F → Ω) :
    ext F (mix S y y') = S.piecewise (ext F y) (ext F y') := by
  funext i
  by_cases hi : i ∈ F <;> by_cases hS : i ∈ S <;> simp [ext, mix, hi, hS, Set.piecewise]

lemma mix_mix_left {F : Finset ι} (S : Set ι) (y y' : F → Ω) :
    mix S (mix S y y') (mix S y' y) = y := by
  funext i; by_cases hS : (i : ι) ∈ S <;> simp [mix, hS]

lemma mix_mix_right {F : Finset ι} (S : Set ι) (y y' : F → Ω) :
    mix S (mix S y' y) (mix S y y') = y' := by
  funext i; by_cases hS : (i : ι) ∈ S <;> simp [mix, hS]

lemma wt_mix_mul {F : Finset ι} (S : Set ι) (y y' : F → Ω) :
    wt μ (mix S y y') * wt μ (mix S y' y) = wt μ y * wt μ y' := by
  unfold wt
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  by_cases hS : (i : ι) ∈ S <;> simp [mix, hS, mul_comm]

/-- The resampling involution on pairs of configurations. -/
def mixEquiv (F : Finset ι) (S : Set ι) : (F → Ω) × (F → Ω) ≃ (F → Ω) × (F → Ω) :=
  Function.Involutive.toPerm (fun p => (mix S p.1 p.2, mix S p.2 p.1)) fun p => by
    ext1 <;> simp [mix_mix_left, mix_mix_right]

/-- The resampling involution preserves the product measure. -/
lemma sum_sum_mix (F : Finset ι) (S : Set ι) (Φ : (F → Ω) → (F → Ω) → ℝ) :
    ∑ y : F → Ω, ∑ y' : F → Ω, wt μ y * wt μ y' * Φ y y' =
      ∑ y : F → Ω, ∑ y' : F → Ω, wt μ y * wt μ y' * Φ (mix S y y') (mix S y' y) := by
  rw [← Fintype.sum_prod_type' (f := fun y y' => wt μ y * wt μ y' * Φ y y'),
    ← Fintype.sum_prod_type' (f := fun y y' => wt μ y * wt μ y' * Φ (mix S y y') (mix S y' y))]
  rw [← (mixEquiv F S).sum_comp]
  refine Fintype.sum_congr _ _ fun p => ?_
  show wt μ (mix S p.1 p.2) * wt μ (mix S p.2 p.1) * Φ (mix S p.1 p.2) (mix S p.2 p.1) = _
  rw [wt_mix_mul]

/-- An expectation as a double sum (the second sum has total weight one). -/
lemma expect_eq_sum_sum (F : Finset ι) (g : (ι → Ω) → ℝ) :
    expect μ F g = ∑ y : F → Ω, ∑ y' : F → Ω, wt μ y * wt μ y' * g (ext F y) := by
  unfold expect
  refine sum_congr rfl fun y _ => ?_
  rw [← sum_mul, ← mul_sum, sum_wt, mul_one]

/-! ### Tower property, locality, independence -/

lemma condE_dependsOn (F : Finset ι) (S : Set ι) (h : (ι → Ω) → ℝ) :
    DependsOn (condE μ F S h) S := by
  intro x x' hxx'
  unfold condE
  congr 1; funext z; congr 1
  funext i; by_cases hi : i ∈ S <;> simp [Set.piecewise, hi, hxx' i]

lemma cond_dependsOn (F : Finset ι) (S : Set ι) (E : (ι → Ω) → Prop) :
    DependsOn (cond μ F S E) S :=
  condE_dependsOn F S _

/-- **Tower property.** For `g` depending only on `S`, `E[g · E[h | S]] = E[g · h]`. -/
theorem expect_mul_condE {F : Finset ι} {S : Set ι} {g : (ι → Ω) → ℝ} (hg : DependsOn g S)
    (h : (ι → Ω) → ℝ) :
    expect μ F (fun x => g x * condE μ F S h x) = expect μ F (fun x => g x * h x) := by
  have lhs : expect μ F (fun x => g x * condE μ F S h x) =
      ∑ y : F → Ω, ∑ y' : F → Ω, wt μ y * wt μ y' * (g (ext F y) * h (ext F (mix S y y'))) := by
    unfold expect condE
    refine sum_congr rfl fun y _ => ?_
    dsimp only
    unfold expect
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun y' _ => ?_
    rw [ext_mix]; ring
  rw [lhs, sum_sum_mix F S, expect_eq_sum_sum]
  refine sum_congr rfl fun y _ => sum_congr rfl fun y' _ => ?_
  rw [mix_mix_left]
  congr 2
  apply hg
  intro i hi
  rw [ext_mix]; simp [Set.piecewise, hi]

/-- Law of total expectation. -/
theorem expect_condE (F : Finset ι) (S : Set ι) (h : (ι → Ω) → ℝ) :
    expect μ F (condE μ F S h) = expect μ F h := by
  have := expect_mul_condE (μ := μ) (F := F) (S := S) (g := fun _ => 1)
    (fun _ _ _ => rfl) h
  simpa using this

/-- Conditioning on `S`, functions that agree whenever the values in `S` are those of `x` have the
same conditional expectation. -/
lemma condE_congr {F : Finset ι} {S : Set ι} {h h' : (ι → Ω) → ℝ} {x : ι → Ω}
    (hh : ∀ z, h (S.piecewise x z) = h' (S.piecewise x z)) : condE μ F S h x = condE μ F S h' x := by
  unfold condE; congr 1; funext z; exact hh z

/-- If `h` depends on `T ∪ D` with `T ⊆ S` and `D` disjoint from `S`, then conditioning on `S` is the
same as conditioning on `T`. -/
theorem condE_eq_of_dependsOn {F : Finset ι} {S T D : Set ι} {h : (ι → Ω) → ℝ}
    (hh : DependsOn h (T ∪ D)) (hTS : T ⊆ S) (hDS : Disjoint D S) (x : ι → Ω) :
    condE μ F S h x = condE μ F T h x := by
  unfold condE; congr 1; funext z
  apply hh
  intro i hi
  rcases hi with hi | hi
  · simp [Set.piecewise, hi, hTS hi]
  · have h1 : i ∉ S := Set.disjoint_left.1 hDS hi
    have h2 : i ∉ T := fun h => h1 (hTS h)
    simp [Set.piecewise, h1, h2]

/-- **Independence** of two functions of disjoint regions. -/
theorem expect_mul_of_disjoint {F : Finset ι} {D D' : Set ι} {k k' : (ι → Ω) → ℝ}
    (hk : DependsOn k D) (hk' : DependsOn k' D') (hD : Disjoint D D') :
    expect μ F (fun x => k x * k' x) = expect μ F k * expect μ F k' := by
  rw [expect_eq_sum_sum, sum_sum_mix F D]
  have : ∀ y y' : F → Ω, k (ext F (mix D y y')) * k' (ext F (mix D y y')) =
      k (ext F y) * k' (ext F y') := by
    intro y y'
    congr 1
    · apply hk; intro i hi; rw [ext_mix]; simp [Set.piecewise, hi]
    · apply hk'; intro i hi
      have : i ∉ D := Set.disjoint_right.1 hD hi
      rw [ext_mix]; simp [Set.piecewise, this]
  simp only [this]
  unfold expect
  rw [sum_mul]
  refine sum_congr rfl fun y _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y' _ => ?_
  ring

/-- **Independence** of finitely many functions of pairwise disjoint regions. -/
theorem expect_prod_of_disjoint {κ : Type*} {F : Finset ι} (J : Finset κ) {D : κ → Set ι}
    {k : κ → (ι → Ω) → ℝ} (hk : ∀ j ∈ J, DependsOn (k j) (D j))
    (hD : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → Disjoint (D j) (D j')) :
    expect μ F (fun x => ∏ j ∈ J, k j x) = ∏ j ∈ J, expect μ F (k j) := by
  induction J using Finset.induction_on with
  | empty => simp [expect_const]
  | insert a J ha ih =>
    simp only [prod_insert ha]
    have hdep : DependsOn (fun x => ∏ j ∈ J, k j x) (⋃ j ∈ J, D j) := by
      intro x x' hxx'
      refine prod_congr rfl fun j hj => hk j (mem_insert_of_mem hj) fun i hi => ?_
      exact hxx' i (Set.mem_biUnion hj hi)
    have hdisj : Disjoint (D a) (⋃ j ∈ J, D j) := by
      rw [Set.disjoint_iUnion₂_right]
      intro j hj
      exact hD a (mem_insert_self a J) j (mem_insert_of_mem hj) (by rintro rfl; exact ha hj)
    rw [expect_mul_of_disjoint (hk a (mem_insert_self a J)) hdep hdisj]
    rw [ih (fun j hj => hk j (mem_insert_of_mem hj))
      (fun j hj j' hj' => hD j (mem_insert_of_mem hj) j' (mem_insert_of_mem hj'))]

/-- **Conditional independence.** Given the values in `S`, functions of `S ∪ D j` with pairwise
disjoint `D j` outside `S` are independent. -/
theorem condE_prod {κ : Type*} {F : Finset ι} {S : Set ι} (J : Finset κ) {D : κ → Set ι}
    {h : κ → (ι → Ω) → ℝ} (hh : ∀ j ∈ J, DependsOn (h j) (S ∪ D j))
    (hD : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → Disjoint (D j) (D j')) (x : ι → Ω) :
    condE μ F S (fun z => ∏ j ∈ J, h j z) x = ∏ j ∈ J, condE μ F S (h j) x := by
  unfold condE
  refine expect_prod_of_disjoint J (D := D) (fun j hj => ?_) hD
  intro z z' hzz'
  apply hh j hj
  intro i hi
  by_cases hiS : i ∈ S
  · simp [Set.piecewise, hiS]
  · have : i ∈ D j := by rcases hi with hi | hi; exacts [absurd hi hiS, hi]
    simp [Set.piecewise, hiS, hzz' i this]

/-! ### Changing the finite support, translations -/

lemma sum_prod_w (κ : Type*) [Fintype κ] [DecidableEq κ] : ∑ y : κ → Ω, ∏ i, μ.w (y i) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : κ) a => μ.w a)]
  simp [μ.sum_eq_one]

/-- The expectation does not depend on the finite support `F`, as long as `F` contains the
nodes the function depends on. -/
theorem expect_eq_of_subset {F₀ F : Finset ι} (hsub : F₀ ⊆ F) {g : (ι → Ω) → ℝ}
    (hg : DependsOn g (F₀ : Set ι)) : expect μ F g = expect μ F₀ g := by
  set p : F → Prop := fun i => (i : ι) ∈ F₀
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => Ω)
  let e₀ : {i : F // p i} ≃ F₀ :=
    Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ F)) (q := (· ∈ F₀)) (fun h => hsub h)
  unfold expect wt
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have hext : ∀ (a : {i : F // p i} → Ω) (b : {i : F // ¬ p i} → Ω),
      g (ext F (e.symm (a, b))) = g (ext F₀ (a ∘ e₀.symm)) := by
    intro a b
    apply hg
    intro i hi
    have hiF : i ∈ F := hsub hi
    have hi' : i ∈ F₀ := hi
    have he₀ : e₀.symm ⟨i, hi'⟩ = ⟨⟨i, hiF⟩, hi'⟩ := e₀.symm_apply_eq.2 rfl
    simp only [ext, dif_pos hiF, dif_pos hi', comp_apply, he₀]
    simp [e, Equiv.piEquivPiSubtypeProd, p, hi']
  have hwt : ∀ (a : {i : F // p i} → Ω) (b : {i : F // ¬ p i} → Ω),
      ∏ i, μ.w (e.symm (a, b) i) = (∏ i, μ.w (a i)) * ∏ i, μ.w (b i) := by
    intro a b
    rw [← Fintype.prod_subtype_mul_prod_subtype p]
    congr 1
    · refine Fintype.prod_congr _ _ fun i => ?_
      simp [e, Equiv.piEquivPiSubtypeProd, i.2]
    · refine Fintype.prod_congr _ _ fun i => ?_
      simp [e, Equiv.piEquivPiSubtypeProd, i.2]
  simp only [hext, hwt]
  have : ∀ a : {i : F // p i} → Ω, ∑ b : {i : F // ¬ p i} → Ω,
      (∏ i, μ.w (a i)) * (∏ i, μ.w (b i)) * g (ext F₀ (a ∘ e₀.symm)) =
      (∏ i, μ.w (a i)) * g (ext F₀ (a ∘ e₀.symm)) := by
    intro a
    rw [← sum_mul, ← mul_sum, sum_prod_w, mul_one]
  simp only [this]
  rw [← (e₀.arrowCongr (Equiv.refl Ω)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun a => ?_
  congr 1
  · simp only [Equiv.arrowCongr, Equiv.refl_symm, Equiv.coe_fn_symm_mk, Equiv.coe_refl,
      comp_apply, id]
    exact Fintype.prod_equiv e₀ _ _ fun i => by simp

/-- Two finite supports give the same expectation if both contain the nodes the function depends
on. -/
theorem expect_congr_support {F₁ F₂ : Finset ι} {g : (ι → Ω) → ℝ}
    (hg : DependsOn g ((F₁ ∩ F₂ : Finset ι) : Set ι)) : expect μ F₁ g = expect μ F₂ g := by
  rw [expect_eq_of_subset inter_subset_left hg, expect_eq_of_subset inter_subset_right hg]

/-- Relabelling the nodes along a bijection. -/
theorem expect_comp_equiv (σ : ι ≃ ι) (F : Finset ι) (g : (ι → Ω) → ℝ) :
    expect μ F (fun x => g (x ∘ σ)) = expect μ (F.map σ.symm.toEmbedding) g := by
  let eF : F ≃ F.map σ.symm.toEmbedding :=
    Equiv.subtypeEquiv σ.symm (fun a => by simp [Finset.mem_map_equiv])
  unfold expect wt
  rw [← (eF.arrowCongr (Equiv.refl Ω)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun y => ?_
  congr 1
  · simp only [Equiv.arrowCongr, Equiv.refl_symm, Equiv.coe_fn_symm_mk, Equiv.coe_refl,
      comp_apply, id]
    exact Fintype.prod_equiv eF _ _ fun i => by simp
  · show g (ext F _ ∘ σ) = g _
    congr 1
    funext i
    simp only [ext, comp_apply, Equiv.arrowCongr, Equiv.coe_fn_symm_mk, Equiv.refl_symm,
      Equiv.coe_refl, id]
    by_cases hi : σ i ∈ F
    · rw [dif_pos hi, dif_pos (by simpa [Finset.mem_map_equiv] using hi)]
      congr 1
      ext; simp [eF]
    · rw [dif_neg hi, dif_neg (by simpa [Finset.mem_map_equiv] using hi)]

/-- Probabilities under relabelling. -/
theorem prob_comp_equiv (σ : ι ≃ ι) (F : Finset ι) (E : (ι → Ω) → Prop) :
    prob μ F (fun x => E (x ∘ σ)) = prob μ (F.map σ.symm.toEmbedding) E :=
  expect_comp_equiv σ F (ind E)

/-- Conditional expectations under relabelling. -/
theorem condE_comp_equiv (σ : ι ≃ ι) (F : Finset ι) (S : Set ι) (h : (ι → Ω) → ℝ)
    (x : ι → Ω) :
    condE μ F S h (x ∘ σ) = condE μ (F.map σ.toEmbedding) (σ.symm ⁻¹' S) (fun y => h (y ∘ σ)) x := by
  unfold condE
  have hpw : ∀ z : ι → Ω, S.piecewise (x ∘ σ) z =
      ((σ.symm ⁻¹' S).piecewise x (z ∘ σ.symm)) ∘ σ := by
    intro z; funext i
    by_cases hi : i ∈ S <;> simp [Set.piecewise, hi]
  simp only [hpw]
  have := expect_comp_equiv (μ := μ) σ.symm F
    (fun z' => h (((σ.symm ⁻¹' S).piecewise x z') ∘ σ))
  simpa using this

/-! ### Frequent values -/

/-- The value `col x` is *infrequent* given `T` with threshold `f` with probability at most
`|α| f`. -/
theorem prob_infrequent_le {α : Type*} [Fintype α] (F : Finset ι) (T : Set ι)
    (col : (ι → Ω) → α) {f : ℝ} (hf : 0 ≤ f) :
    prob μ F (fun x => cond μ F T (fun z => col z = col x) x < f) ≤ Fintype.card α * f := by
  have hsplit : ∀ x, ind (fun x => cond μ F T (fun z => col z = col x) x < f) x =
      ∑ i : α, ind (fun x => cond μ F T (fun z => col z = i) x < f) x * ind (fun x => col x = i) x := by
    intro x
    rw [Finset.sum_eq_single (col x)]
    · simp [ind]
    · intro i _ hi; simp [ind, Ne.symm hi]
    · simp
  unfold prob
  rw [show (ind fun x => cond μ F T (fun z => col z = col x) x < f) =
      fun x => ∑ i : α, ind (fun x => cond μ F T (fun z => col z = i) x < f) x *
        ind (fun x => col x = i) x from funext hsplit, expect_sum]
  have hi : ∀ i : α, expect μ F (fun x => ind (fun x => cond μ F T (fun z => col z = i) x < f) x *
      ind (fun x => col x = i) x) ≤ f := by
    intro i
    have hdep : DependsOn (ind (fun x => cond μ F T (fun z => col z = i) x < f)) T := by
      intro x x' hxx'
      simp only [ind, cond_dependsOn F T _ hxx']
    rw [← expect_mul_condE hdep]
    calc expect μ F (fun x => ind (fun x => cond μ F T (fun z => col z = i) x < f) x *
          condE μ F T (ind fun x => col x = i) x) ≤ expect μ F (fun _ => f) := by
          apply expect_mono; intro x
          unfold ind; split_ifs with h
          · rw [one_mul]; exact h.le
          · rw [zero_mul]; exact hf
      _ = f := expect_const F f
  calc ∑ i : α, _ ≤ ∑ _i : α, f := sum_le_sum fun i _ => hi i
    _ = Fintype.card α * f := by simp

end

end Podc.MinimalSymmetryBreaking
