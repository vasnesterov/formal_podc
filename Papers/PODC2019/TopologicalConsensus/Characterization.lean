import Papers.PODC2019.TopologicalConsensus.Distance

/-!
# Topological characterization of consensus (Lemmas 4.4, 4.5, Theorems 5.2, 5.3)

A partition of `Σ` into decision sets `Σ_v` is encoded as a labelling `lab : Σ → V`
(`Σ_v = lab⁻¹{v}`; parts may be empty).

**Necessity (holds in the generic model of Section 3).**
* `isOpen_fiber_τNU` (Lemma 4.5) and `theorem_5_3_necessary`: a non-uniform consensus algorithm
  yields a `d_nu`-clopen partition satisfying validity.
* `isOpen_fiber_τU` (Lemma 4.4) and `theorem_5_2_necessary`: the same for uniform consensus and
  `d_u`.
* `theorem_5_2c_necessary`: the same for uniform consensus and our corrected distance `d_uc`.

**Sufficiency (the universal algorithms).** The paper's termination proof needs that a process's
view determines the global time and the process's earlier views (`Model.LockstepRecall`); without
it the theorems are false (`Counterexamples.lean`). Under this assumption:
* `theorem_5_3` (Theorem 5.3): non-uniform consensus is solvable iff there is a `d_nu`-clopen
  partition with validity.
* `theorem_5_2c` (corrected Theorem 5.2): uniform consensus is solvable iff there is a
  `d_uc`-clopen partition with validity, where `d_uc` only requires obedience in the first
  execution. The paper's Theorem 5.2 (with `d_u`) is false when disobedient processes can have the
  same view as obedient ones (`Counterexamples.theorem_5_2_false`).
* `theorem_5_2_faultFree`: in fault-free models (e.g. dynamic networks under message adversaries,
  the setting of the PODC'19 paper), `d_uc = d_u`, so the paper's Theorem 5.2 holds as stated.
-/

namespace TopoConsensus

open Set Filter Topology

set_option linter.unusedSectionVars false

/-- If all fibres of a map to a type are open, they are all clopen. -/
theorem isClopen_fibers {X W : Type*} [TopologicalSpace X] (lab : X → W)
    (h : ∀ w, IsOpen (lab ⁻¹' {w})) (w : W) : IsClopen (lab ⁻¹' {w}) := by
  refine ⟨?_, h w⟩
  rw [← isOpen_compl_iff]
  have : (lab ⁻¹' {w})ᶜ = ⋃ u ∈ ({w}ᶜ : Set W), lab ⁻¹' {u} := by
    ext x; simp [eq_comm]
  rw [this]
  exact isOpen_biUnion fun u _ => h u

namespace Model

variable {P C V : Type*} (M : Model P C V)

/-! ### The decision function `Δ : Σ → V` of a consensus algorithm -/

theorem exists_common_decision {A : DecisionAlg M} (hT : A.Termination) (hA : A.Agreement)
    (γ : M.adm) : ∃ v, ∀ p ∈ M.obe γ, A.Decides γ p v := by
  obtain ⟨q, hq⟩ := M.ob_nonempty γ γ.2
  obtain ⟨v, hv⟩ := hT γ γ.2 q hq
  refine ⟨v, fun p hp => ?_⟩
  obtain ⟨w, hw⟩ := hT γ γ.2 p hp
  rwa [hA γ γ.2 p hp q hq w v hw hv] at hw

/-- The consensus decision function `Δ(γ)`: the common decision value of the obedient processes. -/
noncomputable def decisionFn {A : DecisionAlg M} (hT : A.Termination) (hA : A.Agreement)
    (γ : M.adm) : V :=
  Classical.choose (M.exists_common_decision hT hA γ)

theorem decisionFn_spec {A : DecisionAlg M} (hT : A.Termination) (hA : A.Agreement) (γ : M.adm) :
    ∀ p ∈ M.obe γ, A.Decides γ p (M.decisionFn hT hA γ) :=
  Classical.choose_spec (M.exists_common_decision hT hA γ)

theorem decisionFn_eq {A : DecisionAlg M} (hT : A.Termination) (hA : A.Agreement) (γ : M.adm)
    {p : P} (hp : p ∈ M.obe γ) {v : V} (hv : A.Decides γ p v) : M.decisionFn hT hA γ = v := by
  obtain ⟨w, hw⟩ := hT γ γ.2 p hp
  exact hA γ γ.2 p hp p hp _ v (M.decisionFn_spec hT hA γ p hp) hv

/-- A finite bound on the decision times of the obedient processes. -/
theorem exists_decision_bound [Finite P] {A : DecisionAlg M} (hT : A.Termination)
    (hA : A.Agreement) (γ : M.adm) :
    ∃ T, ∀ p ∈ M.obe γ, ∃ t ≤ T, A.dec p ((γ : ℕ → C) t) = some (M.decisionFn hT hA γ) := by
  classical
  cases nonempty_fintype P
  have : ∀ p, ∃ t, p ∈ M.obe γ → A.dec p ((γ : ℕ → C) t) = some (M.decisionFn hT hA γ) := by
    intro p
    by_cases hp : p ∈ M.obe γ
    · obtain ⟨t, ht⟩ := M.decisionFn_spec hT hA γ p hp
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => (hp h).elim⟩
  choose f hf using this
  exact ⟨Finset.univ.sup f, fun p hp => ⟨f p, Finset.le_sup (Finset.mem_univ p), hf p hp⟩⟩

variable [Fintype P] [Nonempty P]

/-! ### Necessity -/

/-- Lemma 4.5: the decision function of a non-uniform consensus algorithm is continuous for the
non-uniform topology (all decision sets are open). -/
theorem isOpen_fiber_τNU {A : DecisionAlg M} (hT : A.Termination) (hA : A.Agreement) (v : V) :
    IsOpen[M.τNU] (M.decisionFn hT hA ⁻¹' {v}) := by
  rw [isOpen_τNU_iff]
  intro γ hγ
  obtain ⟨T, hT'⟩ := M.exists_decision_bound hT hA γ
  refine ⟨T, fun δ ⟨p, ⟨hpγ, hpδ⟩, hok⟩ => ?_⟩
  obtain ⟨t, ht, hdec⟩ := hT' p hpγ
  have h1 : A.dec p ((δ : ℕ → C) t) = some (M.decisionFn hT hA γ) := by
    rw [← A.dec_indist p _ _ (M.okP_indist (hok t ht)), hdec]
  simp only [mem_preimage, mem_singleton_iff] at hγ ⊢
  rw [← hγ]
  exact M.decisionFn_eq hT hA δ hpδ ⟨t, h1⟩

/-- Lemma 4.4: the decision function of a uniform consensus algorithm is continuous for the
uniform topology. -/
theorem isOpen_fiber_τU {A : DecisionAlg M} (hT : A.Termination) (hUA : A.UniformAgreement)
    (v : V) :
    IsOpen[M.τU] (M.decisionFn hT (fun γ hγ p _ q _ => hUA γ hγ p q) ⁻¹' {v}) := by
  set hA : A.Agreement := fun γ hγ p _ q _ => hUA γ hγ p q
  rw [isOpen_τU_iff]
  intro γ hγ
  obtain ⟨T₁, hT₁⟩ := M.exists_decision_bound hT hA γ
  obtain ⟨T₀, hT₀⟩ := M.exists_ob_stable γ.2
  refine ⟨max T₀ T₁, fun δ ⟨p, hok⟩ => ?_⟩
  simp only [mem_preimage, mem_singleton_iff] at hγ ⊢
  rw [← hγ]
  -- some process decides `Δ(γ)` in `δ`
  have key : ∃ q, A.Decides δ q (M.decisionFn hT hA γ) := by
    rcases hok _ le_rfl with ⟨-, hpγ, -⟩ | heq
    · rw [hT₀ _ (le_max_left _ _)] at hpγ
      obtain ⟨t, ht, hdec⟩ := hT₁ p hpγ
      refine ⟨p, t, ?_⟩
      rw [← A.dec_indist p _ _ (M.okP_indist (hok t (ht.trans (le_max_right _ _)))), hdec]
    · obtain ⟨q, hq⟩ := M.ob_nonempty γ γ.2
      obtain ⟨t, ht, hdec⟩ := hT₁ q hq
      refine ⟨q, max T₀ T₁, ?_⟩
      rw [← heq]
      exact A.dec_irrev γ γ.2 q t _ (ht.trans (le_max_right _ _)) _ hdec
  obtain ⟨q, hq⟩ := key
  obtain ⟨r, hr⟩ := M.ob_nonempty δ δ.2
  exact hUA δ δ.2 r q _ _ (M.decisionFn_spec hT hA δ r hr) hq

/-- Lemma 4.4 for the corrected uniform distance `d_uc`. -/
theorem isOpen_fiber_τUc {A : DecisionAlg M} (hT : A.Termination) (hUA : A.UniformAgreement)
    (v : V) :
    IsOpen[M.τUc] (M.decisionFn hT (fun γ hγ p _ q _ => hUA γ hγ p q) ⁻¹' {v}) := by
  set hA : A.Agreement := fun γ hγ p _ q _ => hUA γ hγ p q
  rw [isOpen_τUc_iff]
  intro γ hγ
  obtain ⟨T₁, hT₁⟩ := M.exists_decision_bound hT hA γ
  obtain ⟨T₀, hT₀⟩ := M.exists_ob_stable γ.2
  refine ⟨max T₀ T₁, fun δ ⟨p, hok⟩ => ?_⟩
  simp only [mem_preimage, mem_singleton_iff] at hγ ⊢
  rw [← hγ]
  have hind : ∀ t ≤ max T₀ T₁, M.indist p ((γ : ℕ → C) t) ((δ : ℕ → C) t) := by
    intro t ht
    rcases hok t ht with ⟨h, -⟩ | h
    · exact h
    · rw [h]; exact M.indist_refl p _
  have key : ∃ q, A.Decides δ q (M.decisionFn hT hA γ) := by
    rcases hok _ le_rfl with ⟨-, hpγ⟩ | heq
    · rw [hT₀ _ (le_max_left _ _)] at hpγ
      obtain ⟨t, ht, hdec⟩ := hT₁ p hpγ
      refine ⟨p, t, ?_⟩
      rw [← A.dec_indist p _ _ (hind t (ht.trans (le_max_right _ _))), hdec]
    · obtain ⟨q, hq⟩ := M.ob_nonempty γ γ.2
      obtain ⟨t, ht, hdec⟩ := hT₁ q hq
      refine ⟨q, max T₀ T₁, ?_⟩
      rw [← heq]
      exact A.dec_irrev γ γ.2 q t _ (ht.trans (le_max_right _ _)) _ hdec
  obtain ⟨q, hq⟩ := key
  obtain ⟨r, hr⟩ := M.ob_nonempty δ δ.2
  exact hUA δ δ.2 r q _ _ (M.decisionFn_spec hT hA δ r hr) hq

theorem decisionFn_valent {A : DecisionAlg M} (hT : A.Termination) (hA : A.Agreement)
    (hV : A.Validity) (γ : M.adm) (v : V) (hγ : M.Valent γ v) : M.decisionFn hT hA γ = v := by
  obtain ⟨p, hp⟩ := M.ob_nonempty γ γ.2
  exact hV γ γ.2 v hγ p hp _ (M.decisionFn_spec hT hA γ p hp)

/-- Theorem 5.3, "only if" direction (generic model): if non-uniform consensus is solvable, then
`Σ` has a partition into `d_nu`-clopen decision sets such that `v`-valent executions are in `Σ_v`. -/
theorem theorem_5_3_necessary (h : NonUniformSolvable M) :
    ∃ lab : M.adm → V, (∀ v, IsClopen[M.τNU] (lab ⁻¹' {v})) ∧
      ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v := by
  obtain ⟨A, hT, hA, hV⟩ := h
  exact ⟨M.decisionFn hT hA, @isClopen_fibers _ _ M.τNU _ (M.isOpen_fiber_τNU hT hA),
    M.decisionFn_valent hT hA hV⟩

/-- Theorem 5.2, "only if" direction (generic model), for the paper's uniform distance `d_u`. -/
theorem theorem_5_2_necessary (h : UniformSolvable M) :
    ∃ lab : M.adm → V, (∀ v, IsClopen[M.τU] (lab ⁻¹' {v})) ∧
      ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v := by
  obtain ⟨A, hT, hUA, hV⟩ := h
  exact ⟨_, @isClopen_fibers _ _ M.τU _ (M.isOpen_fiber_τU hT hUA),
    M.decisionFn_valent hT _ hV⟩

/-- Corrected Theorem 5.2, "only if" direction (generic model), for the corrected distance. -/
theorem theorem_5_2c_necessary (h : UniformSolvable M) :
    ∃ lab : M.adm → V, (∀ v, IsClopen[M.τUc] (lab ⁻¹' {v})) ∧
      ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v := by
  obtain ⟨A, hT, hUA, hV⟩ := h
  exact ⟨_, @isClopen_fibers _ _ M.τUc _ (M.isOpen_fiber_τUc hT hUA),
    M.decisionFn_valent hT _ hV⟩

/-! ### Sufficiency: the universal non-uniform algorithm (proof of Theorem 5.3) -/

section NonUniform

variable {M} (hM : M.LockstepRecall) (lab : M.adm → V)

/-- `p` decides `v` in configuration `c`: for some time `u` up to the current time, all executions
in which `p` is obedient and has the same time-`u` view as now lie in `Σ_v` (and there is one).
Taking the earliest such `u` makes the decision irrevocable. -/
def DecNU (p : P) (c : C) (v : V) : Prop :=
  ∃ δ : M.adm, ∃ t, M.indist p c ((δ : ℕ → C) t) ∧ ∃ u ≤ t,
    (∃ ε : M.adm, p ∈ M.obe ε ∧ M.indist p ((ε : ℕ → C) u) ((δ : ℕ → C) u)) ∧
    ∀ ε : M.adm, p ∈ M.obe ε → M.indist p ((ε : ℕ → C) u) ((δ : ℕ → C) u) → lab ε = v

include hM in
theorem DecNU_unique {p : P} {c : C} {v w : V} (hv : DecNU lab p c v) (hw : DecNU lab p c w) :
    v = w := by
  obtain ⟨δ, t, hc, u, hu, ⟨ε, hε, hεδ⟩, hall⟩ := hv
  obtain ⟨δ', t', hc', u', hu', ⟨ε', hε', hεδ'⟩, hall'⟩ := hw
  obtain ⟨rfl, hδδ'⟩ := hM p δ δ.2 δ' δ'.2 t t' (M.indist_trans (M.indist_symm hc) hc')
  rcases le_total u u' with h | h
  · -- `ε'` is also a witness for `v` at time `u`
    have := (hM p ε' ε'.2 δ' δ'.2 u' u' hεδ').2 u h
    have h2 : M.indist p ((ε' : ℕ → C) u) ((δ : ℕ → C) u) :=
      M.indist_trans this (M.indist_symm (hδδ' u (h.trans hu')))
    rw [← hall ε' hε' h2, hall' ε' hε' hεδ']
  · have := (hM p ε ε.2 δ δ.2 u u hεδ).2 u' h
    have h2 : M.indist p ((ε : ℕ → C) u') ((δ' : ℕ → C) u') :=
      M.indist_trans this (hδδ' u' (h.trans hu))
    rw [← hall ε hε hεδ, hall' ε hε h2]

theorem DecNU_congr {p : P} {c d : C} (hcd : M.indist p c d) (v : V) :
    DecNU lab p c v ↔ DecNU lab p d v := by
  constructor
  · rintro ⟨δ, t, hc, rest⟩
    exact ⟨δ, t, M.indist_trans (M.indist_symm hcd) hc, rest⟩
  · rintro ⟨δ, t, hc, rest⟩
    exact ⟨δ, t, M.indist_trans hcd hc, rest⟩

include hM in
theorem DecNU_mono {γ : M.adm} {p : P} {s t : ℕ} (hst : s ≤ t) {v : V}
    (h : DecNU lab p ((γ : ℕ → C) s) v) : DecNU lab p ((γ : ℕ → C) t) v := by
  obtain ⟨δ, t₀, hc, u, hu, ⟨ε, hε, hεδ⟩, hall⟩ := h
  obtain ⟨rfl, hγδ⟩ := hM p γ γ.2 δ δ.2 s t₀ hc
  refine ⟨γ, t, M.indist_refl p _, u, hu.trans hst,
    ⟨ε, hε, M.indist_trans hεδ (M.indist_symm (hγδ u hu))⟩, fun ε' hε' h' => ?_⟩
  exact hall ε' hε' (M.indist_trans h' (hγδ u hu))

open Classical in
/-- The universal non-uniform consensus algorithm of Theorem 5.3. -/
noncomputable def universalNU : DecisionAlg M where
  dec p c := if h : ∃ v, DecNU lab p c v then some (Classical.choose h) else none
  dec_indist p c d hcd := by
    have hiff : (∃ v, DecNU lab p c v) ↔ ∃ v, DecNU lab p d v :=
      exists_congr fun v => DecNU_congr lab hcd v
    by_cases h : ∃ v, DecNU lab p c v
    · have h' := hiff.1 h
      rw [dite_eq_left h, dite_eq_left h']
      exact congrArg some (DecNU_unique hM lab (Classical.choose_spec h)
        ((DecNU_congr lab hcd _).2 (Classical.choose_spec h')))
    · rw [dite_eq_right h, dite_eq_right (mt hiff.2 h)]
  dec_irrev γ hγ p s t hst v hv := by
    by_cases h : ∃ v, DecNU lab p (γ s) v
    · rw [dite_eq_left h] at hv
      have hs := Classical.choose_spec h
      rw [Option.some_inj.1 hv] at hs
      have ht := DecNU_mono hM lab (γ := ⟨γ, hγ⟩) hst hs
      rw [dite_eq_left ⟨v, ht⟩]
      exact congrArg some (DecNU_unique hM lab (Classical.choose_spec ⟨v, ht⟩) ht)
    · rw [dite_eq_right h] at hv; exact absurd hv (by simp)

theorem universalNU_dec_eq {p : P} {c : C} {v : V} (h : (universalNU hM lab).dec p c = some v) :
    DecNU lab p c v := by
  classical
  unfold universalNU at h
  dsimp only at h
  split_ifs at h with h'
  · rw [← Option.some_inj.1 h]; exact Classical.choose_spec h'

theorem universalNU_dec_of {p : P} {c : C} {v : V} (h : DecNU lab p c v) :
    (universalNU hM lab).dec p c = some v := by
  classical
  unfold universalNU
  dsimp only
  rw [dite_eq_left ⟨v, h⟩]
  exact congrArg some (DecNU_unique hM lab (Classical.choose_spec ⟨v, h⟩) h)

/-- An obedient process can only decide the label of the execution. -/
theorem universalNU_decides_eq {γ : M.adm} {p : P} (hp : p ∈ M.obe γ) {w : V}
    (h : (universalNU hM lab).Decides γ p w) : lab γ = w := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨δ, t, hc, u, hu, -, hall⟩ := universalNU_dec_eq hM lab hs
  obtain ⟨rfl, hγδ⟩ := hM p γ γ.2 δ δ.2 s t hc
  exact hall γ hp (hγδ u hu)

/-- Theorem 5.3, "if" direction (under `LockstepRecall`): the universal algorithm solves
non-uniform consensus for any partition into `d_nu`-open decision sets with validity. -/
theorem universalNU_solves (hopen : ∀ v, IsOpen[M.τNU] (lab ⁻¹' {v}))
    (hval : ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v) :
    (universalNU hM lab).SolvesNonUniform := by
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ p hp
    obtain ⟨T, hT⟩ := (M.isOpen_τNU_iff _).1 (hopen (lab ⟨γ, hγ⟩)) ⟨γ, hγ⟩ rfl
    refine ⟨lab ⟨γ, hγ⟩, T, universalNU_dec_of hM lab ?_⟩
    refine ⟨⟨γ, hγ⟩, T, M.indist_refl p _, T, le_rfl, ⟨⟨γ, hγ⟩, hp, M.indist_refl p _⟩, ?_⟩
    intro ε hε hεγ
    have hrec := (hM p ε ε.2 γ hγ T T hεγ).2
    exact hT ε ⟨p, ⟨hp, hε⟩, fun t ht =>
      Or.inl ⟨M.indist_symm (hrec t ht), M.obe_subset γ t hp, M.obe_subset ε t hε⟩⟩
  · intro γ hγ p hp q hq v w hv hw
    rw [← universalNU_decides_eq hM lab (γ := ⟨γ, hγ⟩) hp hv,
      ← universalNU_decides_eq hM lab (γ := ⟨γ, hγ⟩) hq hw]
  · intro γ hγ v hv p hp w hw
    rw [← universalNU_decides_eq hM lab (γ := ⟨γ, hγ⟩) hp hw, hval ⟨γ, hγ⟩ v hv]

end NonUniform

/-- **Theorem 5.3** (characterization of non-uniform consensus), under the synchrony assumption
`LockstepRecall` that the paper's proof uses: non-uniform consensus is solvable iff `Σ` can be
partitioned into decision sets `Σ_v` that are clopen in the non-uniform topology and contain all
`v`-valent executions. -/
theorem theorem_5_3 (hM : M.LockstepRecall) :
    NonUniformSolvable M ↔
      ∃ lab : M.adm → V, (∀ v, IsClopen[M.τNU] (lab ⁻¹' {v})) ∧
        ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v := by
  refine ⟨M.theorem_5_3_necessary, fun ⟨lab, hcl, hval⟩ => ?_⟩
  exact ⟨universalNU hM lab, universalNU_solves hM lab (fun v => (hcl v).2) hval⟩

/-! ### Sufficiency: the universal uniform algorithm (corrected Theorem 5.2) -/

section Uniform

variable {M} (hM : M.LockstepRecall) (lab : M.adm → V)

/-- `p` decides `v` in `c` iff all executions in which `p` has the current view lie in `Σ_v`. -/
def DecU (p : P) (c : C) (v : V) : Prop :=
  ∃ δ : M.adm, ∃ t, M.indist p c ((δ : ℕ → C) t) ∧
    ∀ ε : M.adm, M.indist p ((ε : ℕ → C) t) ((δ : ℕ → C) t) → lab ε = v

include hM in
theorem DecU_unique {p : P} {c : C} {v w : V} (hv : DecU lab p c v) (hw : DecU lab p c w) :
    v = w := by
  obtain ⟨δ, t, hc, hall⟩ := hv
  obtain ⟨δ', t', hc', hall'⟩ := hw
  have h := M.indist_trans (M.indist_symm hc) hc'
  obtain ⟨rfl, -⟩ := hM p δ δ.2 δ' δ'.2 t t' h
  rw [← hall δ' (M.indist_symm h), hall' δ' (M.indist_refl p _)]

theorem DecU_congr {p : P} {c d : C} (hcd : M.indist p c d) (v : V) :
    DecU lab p c v ↔ DecU lab p d v := by
  constructor
  · rintro ⟨δ, t, hc, rest⟩
    exact ⟨δ, t, M.indist_trans (M.indist_symm hcd) hc, rest⟩
  · rintro ⟨δ, t, hc, rest⟩
    exact ⟨δ, t, M.indist_trans hcd hc, rest⟩

include hM in
theorem DecU_mono {γ : M.adm} {p : P} {s t : ℕ} (hst : s ≤ t) {v : V}
    (h : DecU lab p ((γ : ℕ → C) s) v) : DecU lab p ((γ : ℕ → C) t) v := by
  obtain ⟨δ, t₀, hc, hall⟩ := h
  obtain ⟨rfl, -⟩ := hM p γ γ.2 δ δ.2 s t₀ hc
  refine ⟨γ, t, M.indist_refl p _, fun ε hε => hall ε ?_⟩
  exact M.indist_trans ((hM p ε ε.2 γ γ.2 t t hε).2 s hst) hc

open Classical in
/-- The universal uniform consensus algorithm (proof of Theorem 5.2). -/
noncomputable def universalU : DecisionAlg M where
  dec p c := if h : ∃ v, DecU lab p c v then some (Classical.choose h) else none
  dec_indist p c d hcd := by
    have hiff : (∃ v, DecU lab p c v) ↔ ∃ v, DecU lab p d v :=
      exists_congr fun v => DecU_congr lab hcd v
    by_cases h : ∃ v, DecU lab p c v
    · have h' := hiff.1 h
      rw [dite_eq_left h, dite_eq_left h']
      exact congrArg some (DecU_unique hM lab (Classical.choose_spec h)
        ((DecU_congr lab hcd _).2 (Classical.choose_spec h')))
    · rw [dite_eq_right h, dite_eq_right (mt hiff.2 h)]
  dec_irrev γ hγ p s t hst v hv := by
    by_cases h : ∃ v, DecU lab p (γ s) v
    · rw [dite_eq_left h] at hv
      have hs := Classical.choose_spec h
      rw [Option.some_inj.1 hv] at hs
      have ht := DecU_mono hM lab (γ := ⟨γ, hγ⟩) hst hs
      rw [dite_eq_left ⟨v, ht⟩]
      exact congrArg some (DecU_unique hM lab (Classical.choose_spec ⟨v, ht⟩) ht)
    · rw [dite_eq_right h] at hv; exact absurd hv (by simp)

theorem universalU_dec_eq {p : P} {c : C} {v : V} (h : (universalU hM lab).dec p c = some v) :
    DecU lab p c v := by
  classical
  unfold universalU at h
  dsimp only at h
  split_ifs at h with h'
  · rw [← Option.some_inj.1 h]; exact Classical.choose_spec h'

theorem universalU_dec_of {p : P} {c : C} {v : V} (h : DecU lab p c v) :
    (universalU hM lab).dec p c = some v := by
  classical
  unfold universalU
  dsimp only
  rw [dite_eq_left ⟨v, h⟩]
  exact congrArg some (DecU_unique hM lab (Classical.choose_spec ⟨v, h⟩) h)

/-- Every process (obedient or not) can only decide the label of the execution. -/
theorem universalU_decides_eq {γ : M.adm} {p : P} {w : V}
    (h : (universalU hM lab).Decides γ p w) : lab γ = w := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨δ, t, hc, hall⟩ := universalU_dec_eq hM lab hs
  obtain ⟨rfl, -⟩ := hM p γ γ.2 δ δ.2 s t hc
  exact hall γ hc

/-- Corrected Theorem 5.2, "if" direction (under `LockstepRecall`). -/
theorem universalU_solves (hopen : ∀ v, IsOpen[M.τUc] (lab ⁻¹' {v}))
    (hval : ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v) :
    (universalU hM lab).SolvesUniform := by
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ p hp
    obtain ⟨T, hT⟩ := (M.isOpen_τUc_iff _).1 (hopen (lab ⟨γ, hγ⟩)) ⟨γ, hγ⟩ rfl
    refine ⟨lab ⟨γ, hγ⟩, T, universalU_dec_of hM lab ⟨⟨γ, hγ⟩, T, M.indist_refl p _, ?_⟩⟩
    intro ε hεγ
    have hrec := (hM p ε ε.2 γ hγ T T hεγ).2
    exact hT ε ⟨p, fun t ht => Or.inl ⟨M.indist_symm (hrec t ht), M.obe_subset γ t hp⟩⟩
  · intro γ hγ p q v w hv hw
    rw [← universalU_decides_eq hM lab (γ := ⟨γ, hγ⟩) hv,
      ← universalU_decides_eq hM lab (γ := ⟨γ, hγ⟩) hw]
  · intro γ hγ v hv p _ w hw
    rw [← universalU_decides_eq hM lab (γ := ⟨γ, hγ⟩) hw, hval ⟨γ, hγ⟩ v hv]

end Uniform

/-- **Corrected Theorem 5.2** (characterization of uniform consensus), under `LockstepRecall`:
uniform consensus is solvable iff `Σ` can be partitioned into decision sets that are clopen for the
corrected uniform distance `d_uc` (which only asks the process to be obedient in the first
execution) and contain all `v`-valent executions. -/
theorem theorem_5_2c (hM : M.LockstepRecall) :
    UniformSolvable M ↔
      ∃ lab : M.adm → V, (∀ v, IsClopen[M.τUc] (lab ⁻¹' {v})) ∧
        ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v := by
  refine ⟨M.theorem_5_2c_necessary, fun ⟨lab, hcl, hval⟩ => ?_⟩
  exact ⟨universalU hM lab, universalU_solves hM lab (fun v => (hcl v).2) hval⟩

theorem τUc_eq_τU (hF : M.FaultFree) : M.τUc = M.τU := by
  unfold τUc τU
  congr 1
  funext γ δ
  exact M.dUc_eq_dU hF γ δ

/-- **Theorem 5.2** as stated in the paper (uniform topology `d_u`) holds in fault-free models
(under `LockstepRecall`), e.g. for dynamic networks under message adversaries. -/
theorem theorem_5_2_faultFree (hM : M.LockstepRecall) (hF : M.FaultFree) :
    UniformSolvable M ↔
      ∃ lab : M.adm → V, (∀ v, IsClopen[M.τU] (lab ⁻¹' {v})) ∧
        ∀ γ : M.adm, ∀ v, M.Valent γ v → lab γ = v := by
  rw [← M.τUc_eq_τU hF]
  exact M.theorem_5_2c hM

/-- In fault-free models uniform and non-uniform consensus coincide. -/
theorem uniformSolvable_iff_nonUniform (hF : M.FaultFree) :
    UniformSolvable M ↔ NonUniformSolvable M := by
  refine ⟨fun ⟨A, hA⟩ => ⟨A, hA.toNonUniform⟩, fun ⟨A, hT, hA, hV⟩ => ⟨A, hT, ?_, hV⟩⟩
  have hob : ∀ γ : ℕ → C, M.obe γ = univ := fun γ => by
    ext p; simp only [mem_obe, mem_univ, iff_true]; intro t; rw [hF]; trivial
  intro γ hγ p q v w hv hw
  exact hA γ hγ p (by rw [hob]; trivial) q (by rw [hob]; trivial) v w hv hw

end Model

end TopoConsensus
