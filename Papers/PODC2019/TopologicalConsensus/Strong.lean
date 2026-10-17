import Papers.PODC2019.TopologicalConsensus.Characterization

/-!
# Strong validity (Section 7.1: "strong versions" of Theorems 5.2/5.3)

(SV): the decision value must be the input value of some process. The paper notes that replacing
condition (2) of Theorem 5.2 by "every execution of `Σ_v` has a process with input `v`" gives a
characterization of strong consensus. We prove this for the corrected uniform topology
(`theorem_5_2c_strong`, under `LockstepRecall`).
-/

namespace TopoConsensus

open Set Filter Topology

set_option linter.unusedSectionVars false

namespace DecisionAlg

variable {P C V : Type*} {M : Model P C V} (A : DecisionAlg M)

/-- Strong validity (SV): an obedient process can only decide the input of some process. -/
def StrongValidity : Prop :=
  ∀ γ ∈ M.adm, ∀ p ∈ M.obe γ, ∀ w, A.Decides γ p w → ∃ q, M.input (γ 0) q = w

theorem StrongValidity.validity {A : DecisionAlg M} (h : A.StrongValidity) : A.Validity := by
  intro γ hγ v hv p hp w hw
  obtain ⟨q, hq⟩ := h γ hγ p hp w hw
  rw [← hq, hv q]

end DecisionAlg

/-- Strong uniform consensus ((T), (UA), (SV)) is solvable in `M`. -/
def StrongUniformSolvable {P C V : Type*} (M : Model P C V) : Prop :=
  ∃ A : DecisionAlg M, A.Termination ∧ A.UniformAgreement ∧ A.StrongValidity

theorem StrongUniformSolvable.uniformSolvable {P C V : Type*} {M : Model P C V}
    (h : StrongUniformSolvable M) : UniformSolvable M :=
  let ⟨A, hT, hUA, hSV⟩ := h
  ⟨A, hT, hUA, hSV.validity⟩

namespace Model

variable {P C V : Type*} (M : Model P C V) [Fintype P] [Nonempty P]

/-- The universal uniform algorithm solves strong uniform consensus if every execution of `Σ_v`
has a process with input `v`. -/
theorem universalU_solves_strong (hM : M.LockstepRecall) (lab : M.adm → V)
    (hopen : ∀ v, IsOpen[M.τUc] (lab ⁻¹' {v}))
    (hstrong : ∀ γ : M.adm, ∃ q, M.input ((γ : ℕ → C) 0) q = lab γ) :
    (universalU hM lab).Termination ∧ (universalU hM lab).UniformAgreement ∧
      (universalU hM lab).StrongValidity := by
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
  · intro γ hγ p _ w hw
    rw [← universalU_decides_eq hM lab (γ := ⟨γ, hγ⟩) hw]
    exact hstrong ⟨γ, hγ⟩

/-- **Strong version of (corrected) Theorem 5.2**, under `LockstepRecall`: strong uniform
consensus is solvable iff `Σ` has a partition into `d_uc`-clopen decision sets `Σ_v` such that
every execution in `Σ_v` has a process with input `v`. -/
theorem theorem_5_2c_strong (hM : M.LockstepRecall) :
    StrongUniformSolvable M ↔
      ∃ lab : M.adm → V, (∀ v, IsClopen[M.τUc] (lab ⁻¹' {v})) ∧
        ∀ γ : M.adm, ∃ q, M.input ((γ : ℕ → C) 0) q = lab γ := by
  constructor
  · rintro ⟨A, hT, hUA, hSV⟩
    refine ⟨_, @isClopen_fibers _ _ M.τUc _ (M.isOpen_fiber_τUc hT hUA), fun γ => ?_⟩
    obtain ⟨p, hp⟩ := M.ob_nonempty γ γ.2
    exact hSV γ γ.2 p hp _ (M.decisionFn_spec hT _ γ p hp)
  · rintro ⟨lab, hcl, hstrong⟩
    exact ⟨universalU hM lab, M.universalU_solves_strong hM lab (fun v => (hcl v).2) hstrong⟩

end Model

end TopoConsensus
