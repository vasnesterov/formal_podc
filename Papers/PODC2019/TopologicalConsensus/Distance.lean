import Papers.PODC2019.TopologicalConsensus.Model

/-!
# Distance functions and the topologies they induce (Section 4)

* `distTopology d`: the topology `T_d` induced by an arbitrary distance function
  `d : X → X → ℝ` (`U` is open iff every point of `U` has a `d`-ball inside `U`). That this is a
  topology is Lemma 4.1. No symmetry, triangle inequality or definiteness is needed.
* `expDist bad = 2^{-inf {t | bad t}}` (with `2^{-∞} = 0`), the common shape of all execution
  distances of the paper; `expDist_lt_pow_iff`: `expDist bad < 2^{-T} ↔ ∀ t ≤ T, ¬ bad t`.
* `Model.okP p c d`: the configuration `p`-view distance is `0`
  (`c ∼ₚ d` with `p` obedient in both, or `c = d`); `Model.dP` the `p`-view distance of executions
  (Section 4.1), a pseudo-ultrametric (Lemma 4.3: `dP_self`, `dP_comm`, `dP_le_max`).
* `Model.dU = min_p dP p` (uniform minimum distance, Section 4.2), `Model.dNU` (non-uniform
  minimum distance, Section 4.3), and the topologies `Model.τU`, `Model.τNU` that they induce on
  the set `Σ` of admissible executions.
* `Model.dUc`: our corrected uniform distance (obedience required only in the *first* argument),
  see `Characterization.lean`.
-/

namespace TopoConsensus

open Set Filter Topology

set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

/-! ### Lemma 4.1: the topology induced by a distance function -/

/-- The topology `T_d` induced by a distance function `d` (Lemma 4.1). -/
def distTopology {X : Type*} (d : X → X → ℝ) : TopologicalSpace X where
  IsOpen U := ∀ x ∈ U, ∃ ε > 0, ∀ y, d x y < ε → y ∈ U
  isOpen_univ := fun _ _ => ⟨1, one_pos, fun _ _ => trivial⟩
  isOpen_inter := by
    intro U W hU hW x hx
    obtain ⟨ε₁, h₁, hU'⟩ := hU x hx.1
    obtain ⟨ε₂, h₂, hW'⟩ := hW x hx.2
    exact ⟨min ε₁ ε₂, lt_min h₁ h₂, fun y hy =>
      ⟨hU' y (lt_of_lt_of_le hy (min_le_left _ _)), hW' y (lt_of_lt_of_le hy (min_le_right _ _))⟩⟩
  isOpen_sUnion := by
    intro S hS x hx
    obtain ⟨U, hUS, hxU⟩ := mem_sUnion.1 hx
    obtain ⟨ε, hε, hU⟩ := hS U hUS x hxU
    exact ⟨ε, hε, fun y hy => mem_sUnion.2 ⟨U, hUS, hU y hy⟩⟩

theorem isOpen_distTopology_iff {X : Type*} (d : X → X → ℝ) (U : Set X) :
    IsOpen[distTopology d] U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, d x y < ε → y ∈ U := Iff.rfl

/-- Openness can be tested with radii `2^{-T}`. -/
theorem isOpen_distTopology_iff_pow {X : Type*} (d : X → X → ℝ) (U : Set X) :
    IsOpen[distTopology d] U ↔ ∀ x ∈ U, ∃ T : ℕ, ∀ y, d x y < (2⁻¹ : ℝ) ^ T → y ∈ U := by
  rw [isOpen_distTopology_iff]
  constructor
  · intro h x hx
    obtain ⟨ε, hε, hU⟩ := h x hx
    obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2⁻¹ : ℝ) < 1)
    exact ⟨T, fun y hy => hU y (hy.trans hT)⟩
  · intro h x hx
    obtain ⟨T, hT⟩ := h x hx
    exact ⟨_, pow_pos (by norm_num) T, hT⟩

/-! ### `2^{-inf}` distances -/

open Classical in
/-- `expDist bad = 2^{-inf {t | bad t}}`, with `2^{-∞} = 0`. -/
noncomputable def expDist (bad : ℕ → Prop) : ℝ :=
  if h : ∃ t, bad t then (2⁻¹ : ℝ) ^ Nat.find h else 0

theorem expDist_nonneg (bad : ℕ → Prop) : 0 ≤ expDist bad := by
  unfold expDist; split_ifs <;> positivity

theorem expDist_le_one (bad : ℕ → Prop) : expDist bad ≤ 1 := by
  unfold expDist; split_ifs
  · exact pow_le_one₀ (by norm_num) (by norm_num)
  · norm_num

theorem expDist_lt_pow_iff (bad : ℕ → Prop) (T : ℕ) :
    expDist bad < (2⁻¹ : ℝ) ^ T ↔ ∀ t ≤ T, ¬ bad t := by
  classical
  unfold expDist
  split_ifs with h
  · rw [pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)]
    constructor
    · intro hlt t ht hb
      exact absurd (Nat.find_min' h hb) (by omega)
    · intro hall
      by_contra hle
      push Not at hle
      exact hall _ hle (Nat.find_spec h)
  · push Not at h
    simp only [h, not_false_eq_true, implies_true, iff_true]
    positivity

theorem expDist_eq_zero_iff (bad : ℕ → Prop) : expDist bad = 0 ↔ ∀ t, ¬ bad t := by
  classical
  unfold expDist
  split_ifs with h
  · simp only [pow_eq_zero_iff', inv_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_and, false_iff]
    push Not
    exact h
  · push Not at h
    simpa using h

theorem expDist_mono {bad₁ bad₂ : ℕ → Prop} (h : ∀ t, bad₁ t → bad₂ t) :
    expDist bad₁ ≤ expDist bad₂ := by
  classical
  unfold expDist
  split_ifs with h₁ h₂ h₂
  · exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.find_mono (fun t ht => h t ht))
  · exact absurd ⟨_, h _ (Nat.find_spec h₁)⟩ h₂
  · positivity
  · exact le_rfl

theorem expDist_le_max {bad bad₁ bad₂ : ℕ → Prop} (h : ∀ t, bad t → bad₁ t ∨ bad₂ t) :
    expDist bad ≤ max (expDist bad₁) (expDist bad₂) := by
  classical
  by_cases hb : ∃ t, bad t
  · have hN := Nat.find_spec hb
    have hval : expDist bad = (2⁻¹ : ℝ) ^ Nat.find hb := by unfold expDist; rw [dite_eq_left_of_eq_true (eq_true hb)]
    rcases h _ hN with h1 | h2
    · refine le_max_of_le_left ?_
      have : expDist bad₁ = (2⁻¹ : ℝ) ^ Nat.find ⟨_, h1⟩ := by
        unfold expDist; rw [dite_eq_left_of_eq_true (eq_true ⟨_, h1⟩)]
      rw [hval, this]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.find_min' _ h1)
    · refine le_max_of_le_right ?_
      have : expDist bad₂ = (2⁻¹ : ℝ) ^ Nat.find ⟨_, h2⟩ := by
        unfold expDist; rw [dite_eq_left_of_eq_true (eq_true ⟨_, h2⟩)]
      rw [hval, this]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.find_min' _ h2)
  · have : expDist bad = 0 := by unfold expDist; rw [dite_eq_right_of_eq_false (eq_false hb)]
    rw [this]
    exact le_max_of_le_left (expDist_nonneg _)

namespace Model

variable {P C V : Type*} (M : Model P C V)

/-! ### Process-view distance (Section 4.1) -/

/-- The configuration `p`-view distance is `0`: `c ∼ₚ d` and `p ∈ Ob(c) ∩ Ob(d)`, or `c = d`. -/
def okP (p : P) (c d : C) : Prop := (M.indist p c d ∧ p ∈ M.Ob c ∧ p ∈ M.Ob d) ∨ c = d

/-- The `p`-view distance `dₚ(γ, δ)` of executions (Section 4.1). -/
noncomputable def dP (p : P) (γ δ : ℕ → C) : ℝ := expDist fun t => ¬ M.okP p (γ t) (δ t)

theorem okP_refl (p : P) (c : C) : M.okP p c c := Or.inr rfl

theorem okP_symm {p : P} {c d : C} (h : M.okP p c d) : M.okP p d c := by
  rcases h with ⟨h, h1, h2⟩ | rfl
  · exact Or.inl ⟨M.indist_symm h, h2, h1⟩
  · exact Or.inr rfl

theorem okP_trans {p : P} {c d e : C} (h₁ : M.okP p c d) (h₂ : M.okP p d e) : M.okP p c e := by
  rcases h₁ with ⟨h₁, a₁, b₁⟩ | rfl
  · rcases h₂ with ⟨h₂, _, b₂⟩ | rfl
    · exact Or.inl ⟨M.indist_trans h₁ h₂, a₁, b₂⟩
    · exact Or.inl ⟨h₁, a₁, b₁⟩
  · exact h₂

theorem okP_indist {p : P} {c d : C} (h : M.okP p c d) : M.indist p c d := by
  rcases h with ⟨h, -, -⟩ | rfl
  · exact h
  · exact M.indist_refl p c

theorem dP_lt_pow_iff (p : P) (γ δ : ℕ → C) (T : ℕ) :
    M.dP p γ δ < (2⁻¹ : ℝ) ^ T ↔ ∀ t ≤ T, M.okP p (γ t) (δ t) := by
  unfold dP; rw [expDist_lt_pow_iff]; simp

/-- Lemma 4.3: `dₚ` is a pseudometric (even a pseudo-ultrametric). -/
theorem dP_self (p : P) (γ : ℕ → C) : M.dP p γ γ = 0 := by
  unfold dP; rw [expDist_eq_zero_iff]; exact fun t h => h (M.okP_refl p _)

theorem dP_comm (p : P) (γ δ : ℕ → C) : M.dP p γ δ = M.dP p δ γ := by
  unfold dP; congr 1; ext t
  exact not_congr ⟨M.okP_symm, M.okP_symm⟩

theorem dP_le_max (p : P) (β γ δ : ℕ → C) :
    M.dP p β δ ≤ max (M.dP p β γ) (M.dP p γ δ) := by
  unfold dP
  apply expDist_le_max
  intro t h
  by_contra h'
  push Not at h'
  exact h (M.okP_trans h'.1 h'.2)

theorem dP_le_add (p : P) (β γ δ : ℕ → C) : M.dP p β δ ≤ M.dP p β γ + M.dP p γ δ :=
  (M.dP_le_max p β γ δ).trans (max_le_add_of_nonneg (expDist_nonneg _) (expDist_nonneg _))

/-! ### Uniform and non-uniform minimum distances (Sections 4.2, 4.3) -/

variable [Fintype P] [Nonempty P]

/-- The uniform minimum distance `d_u(γ, δ) = min_p dₚ(γ, δ)` (Section 4.2). -/
noncomputable def dU (γ δ : ℕ → C) : ℝ := ⨅ p, M.dP p γ δ

open Classical in
/-- The non-uniform minimum distance (Section 4.3): the minimum of `dₚ` over
`p ∈ Ob(γ) ∩ Ob(δ)`, and `1` if there is no such `p`. -/
noncomputable def dNU (γ δ : ℕ → C) : ℝ :=
  if h : (M.obe γ ∩ M.obe δ).Nonempty then
    haveI := h.to_subtype; ⨅ p : ↥(M.obe γ ∩ M.obe δ), M.dP p γ δ
  else 1

theorem dU_lt_pow_iff (γ δ : ℕ → C) (T : ℕ) :
    M.dU γ δ < (2⁻¹ : ℝ) ^ T ↔ ∃ p, ∀ t ≤ T, M.okP p (γ t) (δ t) := by
  unfold dU
  constructor
  · intro h
    obtain ⟨p, hp⟩ := exists_lt_of_ciInf_lt h
    exact ⟨p, (M.dP_lt_pow_iff p γ δ T).1 hp⟩
  · rintro ⟨p, hp⟩
    exact lt_of_le_of_lt (ciInf_le (Set.finite_range _).bddBelow p) ((M.dP_lt_pow_iff p γ δ T).2 hp)

omit [Nonempty P] in
theorem dNU_lt_pow_iff (γ δ : ℕ → C) (T : ℕ) :
    M.dNU γ δ < (2⁻¹ : ℝ) ^ T ↔ ∃ p ∈ M.obe γ ∩ M.obe δ, ∀ t ≤ T, M.okP p (γ t) (δ t) := by
  unfold dNU
  split_ifs with h
  · have := h.to_subtype
    constructor
    · intro hlt
      obtain ⟨⟨p, hp⟩, hp'⟩ := exists_lt_of_ciInf_lt hlt
      exact ⟨p, hp, (M.dP_lt_pow_iff p γ δ T).1 hp'⟩
    · rintro ⟨p, hp, hp'⟩
      exact lt_of_le_of_lt (ciInf_le (Set.finite_range _).bddBelow ⟨p, hp⟩)
        ((M.dP_lt_pow_iff p γ δ T).2 hp')
  · constructor
    · intro hlt
      exact absurd hlt (not_lt.2 (pow_le_one₀ (by norm_num) (by norm_num)))
    · rintro ⟨p, hp, -⟩
      exact absurd ⟨p, hp⟩ h

/-- `d_u ≤ d_nu`: the non-uniform topology is finer (Section 4.3). -/
theorem dU_le_dNU (γ δ : ℕ → C) : M.dU γ δ ≤ M.dNU γ δ := by
  unfold dNU
  split_ifs with h
  · have := h.to_subtype
    exact le_ciInf fun p => ciInf_le (Set.finite_range _).bddBelow (p : P)
  · exact (ciInf_le (Set.finite_range _).bddBelow (Classical.arbitrary P)).trans
      (expDist_le_one _)

/-- The uniform topology on `Σ`, induced by `d_u`. -/
noncomputable def τU : TopologicalSpace M.adm := distTopology fun γ δ : M.adm => M.dU γ δ

/-- The non-uniform topology on `Σ`, induced by `d_nu`. -/
noncomputable def τNU : TopologicalSpace M.adm := distTopology fun γ δ : M.adm => M.dNU γ δ

theorem isOpen_τU_iff (U : Set M.adm) :
    IsOpen[M.τU] U ↔ ∀ γ ∈ U, ∃ T : ℕ, ∀ δ : M.adm,
      (∃ p, ∀ t ≤ T, M.okP p ((γ : ℕ → C) t) ((δ : ℕ → C) t)) → δ ∈ U := by
  unfold τU
  rw [isOpen_distTopology_iff_pow]
  simp only [dU_lt_pow_iff]

omit [Nonempty P] in
theorem isOpen_τNU_iff (U : Set M.adm) :
    IsOpen[M.τNU] U ↔ ∀ γ ∈ U, ∃ T : ℕ, ∀ δ : M.adm,
      (∃ p ∈ M.obe γ ∩ M.obe δ, ∀ t ≤ T, M.okP p ((γ : ℕ → C) t) ((δ : ℕ → C) t)) → δ ∈ U := by
  unfold τNU
  rw [isOpen_distTopology_iff_pow]
  simp only [dNU_lt_pow_iff]

/-! ### Corrected uniform distance -/

/-- Our corrected configuration distance for uniform consensus: `0` iff `c ∼ₚ d` and `p` is
obedient in `c` (the first argument), or `c = d`. -/
def okU (p : P) (c d : C) : Prop := (M.indist p c d ∧ p ∈ M.Ob c) ∨ c = d

/-- The corrected (asymmetric) `p`-view distance for uniform consensus. -/
noncomputable def dPc (p : P) (γ δ : ℕ → C) : ℝ := expDist fun t => ¬ M.okU p (γ t) (δ t)

/-- The corrected (asymmetric) uniform minimum distance. -/
noncomputable def dUc (γ δ : ℕ → C) : ℝ := ⨅ p, M.dPc p γ δ

/-- The topology on `Σ` induced by the corrected uniform distance. -/
noncomputable def τUc : TopologicalSpace M.adm := distTopology fun γ δ : M.adm => M.dUc γ δ

theorem dUc_lt_pow_iff (γ δ : ℕ → C) (T : ℕ) :
    M.dUc γ δ < (2⁻¹ : ℝ) ^ T ↔ ∃ p, ∀ t ≤ T, M.okU p (γ t) (δ t) := by
  unfold dUc
  have key : ∀ p, M.dPc p γ δ < (2⁻¹ : ℝ) ^ T ↔ ∀ t ≤ T, M.okU p (γ t) (δ t) := by
    intro p; unfold dPc; rw [expDist_lt_pow_iff]; simp
  constructor
  · intro h
    obtain ⟨p, hp⟩ := exists_lt_of_ciInf_lt h
    exact ⟨p, (key p).1 hp⟩
  · rintro ⟨p, hp⟩
    exact lt_of_le_of_lt (ciInf_le (Set.finite_range _).bddBelow p) ((key p).2 hp)

theorem isOpen_τUc_iff (U : Set M.adm) :
    IsOpen[M.τUc] U ↔ ∀ γ ∈ U, ∃ T : ℕ, ∀ δ : M.adm,
      (∃ p, ∀ t ≤ T, M.okU p ((γ : ℕ → C) t) ((δ : ℕ → C) t)) → δ ∈ U := by
  unfold τUc
  rw [isOpen_distTopology_iff_pow]
  simp only [dUc_lt_pow_iff]

/-- In a fault-free model the corrected uniform distance is the paper's `d_u`. -/
theorem dUc_eq_dU (hM : M.FaultFree) (γ δ : ℕ → C) : M.dUc γ δ = M.dU γ δ := by
  have : ∀ p c d, M.okU p c d ↔ M.okP p c d := by
    intro p c d
    simp only [okU, okP, hM c, hM d, Set.mem_univ, and_true]
  unfold dUc dU dPc dP
  simp only [this]

end Model

end TopoConsensus
