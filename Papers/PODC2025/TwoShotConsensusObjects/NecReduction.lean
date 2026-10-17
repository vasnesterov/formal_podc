import Papers.PODC2025.TwoShotConsensusObjects.NecReductionSim

/-!
# Removing one copy of `O` (the construction in the proof of Proposition 2)

If, from a reachable configuration `F` of a consensus algorithm `A`, no process can decide
before accessing copy `k` again, and a "decision rule" `dec p c` (decide the input of `p₀` iff
`dec p c`) on the operation `c` that a process is poised to apply to `k` is consistent on
simultaneously poised pairs and correct for the two solo runs, then consensus can be solved with
one copy of `O` fewer (Proposition 2 of the paper): each process writes its input to a fresh
register, runs `A` from `F` until it is poised on `k`, and decides according to `dec`.
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] [Fintype ιS] {R : ιR → ObjSpec}
  {O : ObjSpec} {m : Fin 2 → Set O.Op}

/-- **The reduction of Proposition 2.** -/
theorem reduction (hR : ∀ j, (R j).RWLike) (A : Alg 2 (withRW (ιS := ιS) R O))
    (hA : WFConsensus A) (h2 : TwoShot A) (hm : Allowed m A)
    (x₀ : Fin 2 → Bool) (β : List (Ev 2)) (hβ : CrashFree β) (k : ιS)
    (dec : Fin 2 → O.Op → Bool)
    -- (H1) nobody outputs from `F` before accessing `k` again
    (H1 : ∀ γ, CrashFree γ → (∀ p, accCount (run (initCfg A x₀) β) γ p (.inr k) = 0) →
      ∀ p v, ¬ (run (run (initCfg A x₀) β) γ).Out p v)
    -- (H2) the decision rule is consistent on simultaneously poised pairs
    (H2 : ∀ γ, CrashFree γ → (∀ p, accCount (run (initCfg A x₀) β) γ p (.inr k) = 0) →
      ∀ (c c' : O.Op) (κ κ' : O.Resp → A.L),
      A.act ((run (run (initCfg A x₀) β) γ).loc 0) = .access (.inr k) c κ →
      A.act ((run (run (initCfg A x₀) β) γ).loc 1) = .access (.inr k) c' κ' →
      dec 0 c = dec 1 c')
    -- (H3) solo runs of `p₀` decide the input of `p₀`
    (H3 : ∀ t, accCount (run (initCfg A x₀) β) (solo 0 t) 0 (.inr k) = 0 →
      ∀ (c : O.Op) (κ : O.Resp → A.L),
      A.act ((run (run (initCfg A x₀) β) (solo 0 t)).loc 0) = .access (.inr k) c κ →
      dec 0 c = true)
    -- (H3') solo runs of `p₁` decide the input of `p₁`
    (H3' : ∀ t, accCount (run (initCfg A x₀) β) (solo 1 t) 1 (.inr k) = 0 →
      ∀ (c : O.Op) (κ : O.Resp → A.L),
      A.act ((run (run (initCfg A x₀) β) (solo 1 t)).loc 1) = .access (.inr k) c κ →
      dec 1 c = false) :
    ∃ (ιR' ιS' : Type) (_ : DecidableEq ιR') (_ : DecidableEq ιS') (_ : Fintype ιS')
      (R' : ιR' → ObjSpec) (_ : ∀ j, (R' j).RWLike) (A' : Alg 2 (withRW (ιS := ιS') R' O)),
      Fintype.card ιS' < Fintype.card ιS ∧ WFConsensus A' ∧ TwoShot A' ∧ Allowed m A' := by
  set F := run (initCfg A x₀) β with hF
  have hyp : NecRed.Hyp A F k dec :=
    { H1 := H1
      H2 := H2
      H3 := fun p t h c κ hc => by
        have hp : p = 0 ∨ p = 1 := by fin_cases p <;> simp
        rcases hp with rfl | rfl
        · simp [NecRed.qOf, H3 t h c κ hc]
        · simp [NecRed.qOf, H3' t h c κ hc] }
  refine ⟨ιR ⊕ Fin 2, {k' // k' ≠ k}, inferInstance, inferInstance, inferInstance, NecRed.R' R,
    ?_, NecRed.A' A F k dec, ?_, NecRed.wfConsensus' hA ⟨x₀, β, hβ, rfl⟩ hyp,
    NecRed.twoShot' hyp ?_, NecRed.allowed' hyp m ?_⟩
  · rintro (j | j)
    · exact hR j
    · exact register_rwLike Bool false
  · exact Fintype.card_subtype_lt (p := fun k' => k' ≠ k) (x := k) (by simp)
  · intro γ hγ q k''
    have := h2 x₀ (β ++ γ) (hβ.append hγ) q k''
    rw [accCount_append, ← hF] at this
    omega
  · intro γ hγ q k'' o κ hact
    exact hm x₀ (β ++ γ) (hβ.append hγ) q k'' o κ (by rw [run_append]; exact hact)

end TwoShotCons
