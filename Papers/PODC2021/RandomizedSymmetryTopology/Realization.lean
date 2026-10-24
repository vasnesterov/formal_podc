import Papers.PODC2021.RandomizedSymmetryTopology.ZeroOne

/-!
# Consistency projections, Definition 3.4 and Lemma 3.5

Fraigniaud, Gelles, Lotker, PODC 2021, Section 3.3–3.4.

All complexes in the paper are chromatic and all maps are name-preserving. Restricted to a single
facet `σ = {(i, vᵢ) : i ∈ [n]}`, a chromatic complex on the vertices of `σ` is determined by the
sets of *names* of its simplices, and a name-preserving vertex map between two such complexes is
unique (`(i, vᵢ) ↦ (i, wᵢ)`); it is simplicial iff every simplex of the source is a simplex of the
target. We therefore represent:

* the consistency projection `π(σ)` (Eq. (11)) of a facet `σ` with values `v : Fin n → V` by
  `consistencyComplex v : Set (Finset (Fin n))`, the nonempty sets of names with equal values;
* `π̃(ρ)` (Eq. (18)) for a realization `ρ` at time `t` by `consistencyComplex (M.K ω t)`: the
  relation `i ∼ j` is `Kᵢ(t) = Kⱼ(t)` (Eq. (15));
* the existence of a name-preserving simplicial map `π̃(ρ) → π(τ)` by
  `consistencyComplex κ ⊆ consistencyComplex τ`.

Main results:
* `isFacet_consistencyComplex_iff`: the facets of `π̃(ρ)` are the classes of `∼` (used in
  Lemma 4.3: `dim γ + 1` is the size of a class);
* `lemma_3_5`: Definition 3.1 and Definition 3.4 agree on every global state / realization, hence
  `Pr[P(t) solves O | α] = Pr[S(t) | α]` and the two notions of eventual solvability coincide.
-/

open Finset Filter Topology

namespace Podc.RandomizedSymmetryTopology

variable {n : ℕ}

/-- The consistency projection of a facet with values `v` (Eqs. (11) and (18)), as the set of
name sets of its simplices: nonempty sets of names with pairwise equal values. -/
def consistencyComplex {V : Type*} (v : Fin n → V) : Set (Finset (Fin n)) :=
  {I | I.Nonempty ∧ ∀ i ∈ I, ∀ j ∈ I, v i = v j}

/-- A facet (maximal simplex) of a complex given by its simplices. -/
def IsFacet (C : Set (Finset (Fin n))) (γ : Finset (Fin n)) : Prop :=
  γ ∈ C ∧ ∀ γ' ∈ C, γ ⊆ γ' → γ' = γ

/-- The facets of the consistency projection are exactly the consistency classes. -/
theorem isFacet_consistencyComplex_iff {V : Type*} [DecidableEq V] (v : Fin n → V)
    (γ : Finset (Fin n)) :
    IsFacet (consistencyComplex v) γ ↔ ∃ i, γ = univ.filter fun j => v j = v i := by
  have hcls : ∀ i, (univ.filter fun j => v j = v i) ∈ consistencyComplex v := fun i =>
    ⟨⟨i, by simp⟩, fun a ha b hb => by simp only [mem_filter] at ha hb; rw [ha.2, hb.2]⟩
  constructor
  · rintro ⟨⟨⟨i, hi⟩, hγ⟩, hmax⟩
    refine ⟨i, (hmax _ (hcls i) fun j hj => ?_).symm⟩
    simp [hγ j hj i hi]
  · rintro ⟨i, rfl⟩
    refine ⟨hcls i, fun γ' ⟨_, hγ'⟩ hsub => ?_⟩
    have hi : i ∈ γ' := hsub (by simp)
    refine Finset.Subset.antisymm (fun j hj => ?_) hsub
    simp [hγ' j hj i hi]

/-- **Definition 3.4.** A realization (with global state `κ`) solves `O` if there are `τ ∈ O` and a
name-preserving simplicial map `π̃(ρ) → π(τ)`. -/
def RSolves {Kn Out : Type*} (O : Set (Fin n → Out)) (κ : Fin n → Kn) : Prop :=
  ∃ τ ∈ O, consistencyComplex κ ⊆ consistencyComplex τ

/-- **Lemma 3.5** (pointwise form): a global state solves `O` in the sense of Definition 3.1 iff
its realization solves `O` in the sense of Definition 3.4. (The output type is assumed nonempty,
to extend the decision map outside the values that occur.) -/
theorem solves_iff_rSolves {Kn Out : Type} [Nonempty Out] (O : Task n Out) (κ : Fin n → Kn) :
    Solves O κ ↔ RSolves O κ := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f ∘ κ, hf, fun I ⟨hI, h⟩ => ⟨hI, fun i hi j hj => ?_⟩⟩
    simp [h i hi j hj]
  · rintro ⟨τ, hτ, hsub⟩
    have hpair : ∀ i j, κ i = κ j → τ i = τ j := fun i j h => by
      have : ({i, j} : Finset (Fin n)) ∈ consistencyComplex κ :=
        ⟨⟨i, by simp⟩, fun a ha b hb => by
          simp only [mem_insert, mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [h]⟩
      exact (hsub this).2 i (by simp) j (by simp)
    refine ⟨fun x => if h : ∃ i, κ i = x then τ h.choose else Classical.arbitrary Out, ?_⟩
    convert hτ using 1
    funext i
    have h : ∃ i', κ i' = κ i := ⟨i, rfl⟩
    simp only [Function.comp, h, dite_true]
    exact hpair _ _ h.choose_spec

open Classical in
/-- `Pr[S(t) | α]` (Eq. (20)): the probability that the realization at time `t` solves `O` in the
sense of Definition 3.4. -/
noncomputable def probRSolves {k : ℕ} (M : FullInfoModel n k) {Out : Type} (O : Task n Out)
    (t : ℕ) : ℝ :=
  ((univ.filter fun r : Window k t => RSolves O (M.K (ext r) t)).card : ℝ) / 2 ^ (k * t)

/-- **Lemma 3.5.** `Pr[P(t) solves O | α] = Pr[S(t) | α]` for every `t`; in particular a task is
eventually solvable (Definition 3.3) iff `lim Pr[S(t) | α] = 1`. -/
theorem lemma_3_5 {k : ℕ} (M : FullInfoModel n k) {Out : Type} [Nonempty Out] (O : Task n Out) :
    probSolves M O = probRSolves M O ∧
      (EventuallySolvable M O ↔ Tendsto (probRSolves M O) atTop (𝓝 1)) := by
  have h : probSolves M O = probRSolves M O := by
    funext t
    classical
    unfold probSolves probRSolves
    congr 3
    exact Finset.filter_congr fun r _ => solves_iff_rSolves O (M.K (ext r) t)
  exact ⟨h, by rw [EventuallySolvable, h]⟩

end Podc.RandomizedSymmetryTopology
