import Papers.PODC2019.TopologicalConsensus.Distance

/-!
# The product topology on executions (Lemma 4.2)

Lemma 4.2 of the paper: if `d` is a distance function on `X` taking only the values `0` and `1`,
then the product topology on `X^ω = ℕ → X` (every factor carrying `T_d`) is induced by the
first-difference distance `(γ, δ) ↦ 2^{-inf {t | d(γ t, δ t) > 0}}` (`prodDist d`).

* `lemma_4_2`: the statement, under the additional hypothesis that `d` is reflexive
  (`d x x = 0`), which holds for every distance used in the paper (`distTopology_dP_eq_prod`
  instantiates it for the configuration `p`-view distance).
* `lemma_4_2_false_without_refl`: without reflexivity the statement is false (the paper allows
  any "distance function", i.e. any map `X × X → ℝ`).
* `ball_one_not_isOpen`: the paper's proof uses that the balls `B_1(C) = {D | d(C, D) = 0}` are
  open in `T_d`; this is false when the relation `d = 0` is not transitive. We prove the lemma by a
  chain argument instead: the open sets of `T_d` are upward closed under the reflexive-transitive
  closure of `d x y = 0` (`isOpen_reach`), and a `prodDist`-open set containing `γ` with radius
  `2^{-T}` contains every `δ` whose coordinates `≤ T` are reachable from those of `γ`
  (`mem_of_reach`).
-/

namespace TopoConsensus

open Set Topology Relation

set_option warn.classDefReducibility false

section ProductTopology

variable {X : Type*} (d : X → X → ℝ)

/-- The first-difference distance of Lemma 4.2: `2^{-inf {t | d(γ t, δ t) > 0}}`. -/
noncomputable def prodDist (γ δ : ℕ → X) : ℝ := expDist fun t => 0 < d (γ t) (δ t)

/-- The product topology on `X^ω = ℕ → X`, every factor carrying the topology `T_d`. -/
noncomputable def prodTopology : TopologicalSpace (ℕ → X) :=
  @Pi.topologicalSpace ℕ (fun _ => X) fun _ => distTopology d

theorem prodDist_lt_pow_iff (γ δ : ℕ → X) (T : ℕ) :
    prodDist d γ δ < (2⁻¹ : ℝ) ^ T ↔ ∀ t ≤ T, d (γ t) (δ t) ≤ 0 := by
  unfold prodDist; rw [expDist_lt_pow_iff]; simp

/-- The projections are continuous for the topology induced by `prodDist d` (no assumption on
`d` is needed for this direction). -/
theorem continuous_apply_prodDist (t : ℕ) :
    @Continuous (ℕ → X) X (distTopology (prodDist d)) (distTopology d) fun γ => γ t := by
  refine @Continuous.mk _ _ (distTopology (prodDist d)) (distTopology d) _ fun U hU => ?_
  rw [isOpen_distTopology_iff_pow]
  intro γ hγ
  obtain ⟨ε, hε, hU'⟩ := (isOpen_distTopology_iff d U).1 hU _ hγ
  exact ⟨t, fun δ hδ => hU' _ (lt_of_le_of_lt ((prodDist_lt_pow_iff d γ δ t).1 hδ t le_rfl) hε)⟩

/-- Every product-open set is `prodDist`-open. -/
theorem distTopology_prodDist_le : distTopology (prodDist d) ≤ prodTopology d :=
  le_iInf fun t => continuous_iff_le_induced.1 (continuous_apply_prodDist d t)

/-- The `T_d`-open sets are upward closed under the reflexive-transitive closure of `d = 0`. -/
theorem isOpen_reach (h01 : ∀ x y, d x y = 0 ∨ d x y = 1) (x : X) :
    IsOpen[distTopology d] {y | ReflTransGen (fun a b => d a b = 0) x y} := by
  intro y hy
  refine ⟨1, one_pos, fun z hz => ?_⟩
  have : d y z = 0 := (h01 y z).resolve_right fun h => by rw [h] at hz; exact lt_irrefl _ hz
  exact ReflTransGen.tail hy this

/-- Moving finitely many coordinates along chains of a reflexive relation `R`, one coordinate at a
time, is a chain of coordinatewise `R`-steps. -/
theorem reflTransGen_pi_of_coord {R : X → X → Prop} (hR : ∀ x, R x x) (n : ℕ) :
    ∀ η δ : ℕ → X, (∀ t, n ≤ t → η t = δ t) → (∀ t < n, ReflTransGen R (η t) (δ t)) →
      ReflTransGen (fun η η' : ℕ → X => ∀ t, R (η t) (η' t)) η δ := by
  induction n with
  | zero =>
    intro η δ h _
    rw [funext fun t => h t (Nat.zero_le t)]
  | succ n ih =>
    intro η δ h hc
    have h1 : ReflTransGen (fun η η' : ℕ → X => ∀ t, R (η t) (η' t)) η
        (Function.update η n (δ n)) := by
      have := ReflTransGen.lift (p := fun η η' : ℕ → X => ∀ t, R (η t) (η' t))
        (Function.update η n) (fun a b hab t => by
          by_cases ht : t = n
          · subst ht; simp only [Function.update_self]; exact hab
          · simp only [Function.update_of_ne ht]; exact hR _) _ _ (hc n (Nat.lt_succ_self n))
      simpa only [Function.onFun, Function.update_eq_self] using this
    refine h1.trans (ih _ _ (fun t ht => ?_) (fun t ht => ?_))
    · rcases eq_or_lt_of_le ht with rfl | ht'
      · simp
      · rw [Function.update_of_ne (by omega)]; exact h t ht'
    · rw [Function.update_of_ne (by omega)]; exact hc t (by omega)

variable {d}

/-- A `prodDist`-open set is closed under coordinatewise `d = 0` steps (if `d` is reflexive). -/
theorem mem_of_step {E : Set (ℕ → X)} (hE : IsOpen[distTopology (prodDist d)] E)
    {η η' : ℕ → X} (hη : η ∈ E) (h : ∀ t, d (η t) (η' t) = 0) : η' ∈ E := by
  obtain ⟨T, hT⟩ := (isOpen_distTopology_iff_pow _ _).1 hE η hη
  exact hT _ ((prodDist_lt_pow_iff d η η' T).2 fun t _ => (h t).le)

/-- The chain argument: a `prodDist`-open set containing `γ` with radius `2^{-T}` contains every
`δ` whose coordinates `t ≤ T` are reachable from `γ t` by finitely many `d = 0` steps. -/
theorem mem_of_reach (hrefl : ∀ x, d x x = 0) {E : Set (ℕ → X)}
    (hE : IsOpen[distTopology (prodDist d)] E) {γ : ℕ → X} {T : ℕ}
    (hT : ∀ δ, prodDist d γ δ < (2⁻¹ : ℝ) ^ T → δ ∈ E) {δ : ℕ → X}
    (hδ : ∀ t ≤ T, ReflTransGen (fun a b => d a b = 0) (γ t) (δ t)) : δ ∈ E := by
  classical
  set γ' : ℕ → X := fun t => if t ≤ T then γ t else δ t with hγ'def
  have hγ' : γ' ∈ E := hT _ ((prodDist_lt_pow_iff d γ γ' T).2 fun t ht => by
    simp [hγ'def, ht, hrefl])
  have hchain := reflTransGen_pi_of_coord (R := fun a b => d a b = 0) hrefl (T + 1) γ' δ
    (fun t ht => by simp [hγ'def, show ¬ t ≤ T by omega])
    (fun t ht => by simpa [hγ'def, show t ≤ T by omega] using hδ t (by omega))
  clear_value γ'
  clear hT hδ hγ'def
  induction hchain with
  | refl => exact hγ'
  | tail _ hstep ih => exact mem_of_step hE ih hstep

/-- Every `prodDist`-open set is product-open (needs `d` reflexive and `0/1`-valued). -/
theorem prodTopology_le (h01 : ∀ x y, d x y = 0 ∨ d x y = 1) (hrefl : ∀ x, d x x = 0) :
    prodTopology d ≤ distTopology (prodDist d) := by
  let _ : TopologicalSpace X := distTopology d
  rw [TopologicalSpace.le_def]
  intro E hE
  show IsOpen E
  rw [isOpen_pi_iff]
  intro γ hγ
  obtain ⟨T, hT⟩ := (isOpen_distTopology_iff_pow _ _).1 hE γ hγ
  refine ⟨Finset.range (T + 1), fun t => {y | ReflTransGen (fun a b => d a b = 0) (γ t) y},
    fun t _ => ⟨isOpen_reach d h01 _, ReflTransGen.refl⟩, fun δ hδ => ?_⟩
  exact mem_of_reach hrefl hE hT fun t ht => hδ t (by simp; omega)

variable (d) in
/-- **Lemma 4.2** of the paper (with the missing hypothesis that `d` is reflexive): for a
`0/1`-valued reflexive distance function `d` on `X`, the product topology on `X^ω` (every factor
carrying `T_d`) is the topology induced by `(γ, δ) ↦ 2^{-inf {t | d(γ t, δ t) > 0}}`. -/
theorem lemma_4_2 (h01 : ∀ x y, d x y = 0 ∨ d x y = 1) (hrefl : ∀ x, d x x = 0) :
    prodTopology d = distTopology (prodDist d) :=
  le_antisymm (prodTopology_le h01 hrefl) (distTopology_prodDist_le d)

end ProductTopology

/-! ### Lemma 4.2 needs reflexivity -/

namespace Lemma42Counterexample

/-- A `0/1`-valued, non-reflexive distance on `Bool`: `d(x, y) = 1` iff `y = true`. -/
noncomputable def dBad (_ y : Bool) : ℝ := if y then 1 else 0

theorem dBad_01 : ∀ x y, dBad x y = 0 ∨ dBad x y = 1 := by
  intro x y; cases y <;> simp [dBad]

theorem dBad_not_refl : dBad true true ≠ 0 := by simp [dBad]

/-- The set `{true^ω} ∪ {γ | γ 0 = false}`. -/
def S : Set (ℕ → Bool) := {fun _ => true} ∪ {γ | γ 0 = false}

theorem isOpen_dist_S : IsOpen[distTopology (prodDist dBad)] S := by
  rw [isOpen_distTopology_iff_pow]
  intro γ _
  refine ⟨0, fun δ hδ => Or.inr ?_⟩
  have := (prodDist_lt_pow_iff dBad γ δ 0).1 hδ 0 le_rfl
  show δ 0 = false
  cases h : δ 0
  · rfl
  · norm_num [dBad, h] at this

theorem not_isOpen_prod_S : ¬ IsOpen[prodTopology dBad] S := by
  let _ : TopologicalSpace Bool := distTopology dBad
  intro hS
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hS (fun _ => true) (Or.inl rfl)
  have hfalse : ∀ t ∈ I, false ∈ u t := by
    intro t ht
    obtain ⟨ε, hε, h⟩ := (isOpen_distTopology_iff dBad _).1 (hu t ht).1 true (hu t ht).2
    exact h false (by simp [dBad, hε])
  have hmem : (fun t : ℕ => decide (t = 0)) ∈ (I : Set ℕ).pi u := by
    intro t ht
    by_cases h : t = 0
    · subst h; simpa using (hu 0 ht).2
    · simpa [h] using hfalse t ht
  rcases hsub hmem with h | h
  · have := congrFun h 1; simp at this
  · simp at h

/-- Lemma 4.2 is false for non-reflexive `0/1`-valued distance functions. -/
theorem lemma_4_2_false_without_refl :
    (∀ x y, dBad x y = 0 ∨ dBad x y = 1) ∧ prodTopology dBad ≠ distTopology (prodDist dBad) :=
  ⟨dBad_01, fun h => not_isOpen_prod_S (h ▸ isOpen_dist_S)⟩

end Lemma42Counterexample

/-! ### The proof gap: `B_1(C)` need not be open -/

namespace BallCounterexample

/-- A reflexive `0/1`-valued distance on `Fin 3` whose zero relation `0 → 1 → 2` is not
transitive. -/
noncomputable def dChain (x y : Fin 3) : ℝ :=
  if x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) then 0 else 1

theorem dChain_01 : ∀ x y, dChain x y = 0 ∨ dChain x y = 1 := by
  intro x y; unfold dChain; split_ifs <;> simp

theorem dChain_refl : ∀ x, dChain x x = 0 := by intro x; simp [dChain]

/-- The ball `B_1(0) = {0, 1}` is not open in `T_d`, contrary to the proof of Lemma 4.2. -/
theorem ball_one_not_isOpen : ¬ IsOpen[distTopology dChain] {y | dChain 0 y < 1} := by
  intro h
  obtain ⟨ε, hε, h'⟩ := (isOpen_distTopology_iff dChain _).1 h 1 (by simp [dChain])
  have := h' 2 (by simp [dChain]; exact hε)
  simp [dChain] at this

end BallCounterexample

/-! ### Instance: the `p`-view distance -/

namespace Model

variable {P C V : Type*} (M : Model P C V)

/-- The configuration `p`-view distance of Section 4.1 (`0` iff `M.okP p c e`). -/
noncomputable def dPconf (p : P) (c e : C) : ℝ := by
  classical exact if M.okP p c e then 0 else 1

theorem dP_eq_prodDist (p : P) : M.dP p = prodDist (M.dPconf p) := by
  classical
  funext γ δ
  unfold dP prodDist dPconf
  congr 1
  funext t
  by_cases h : M.okP p (γ t) (δ t) <;> simp [h]

/-- Lemma 4.2 applied to the `p`-view distance: the topology induced by `d_p` on `C^ω` is the
product topology of the configuration `p`-view topology. -/
theorem distTopology_dP_eq_prod (p : P) :
    distTopology (M.dP p) = prodTopology (M.dPconf p) := by
  classical
  rw [M.dP_eq_prodDist, lemma_4_2]
  · intro c e; unfold dPconf; split_ifs <;> simp
  · intro c; simp [dPconf, M.okP_refl]

end Model

end TopoConsensus
