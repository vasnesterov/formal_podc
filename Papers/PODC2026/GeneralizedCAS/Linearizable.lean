import Papers.PODC2026.GeneralizedCAS.Invariant

/-!
# Algorithm 1 is linearizable (Theorem B.3.1)

The linearization of an execution is the ghost list `lin`: the operations in the order of their
successful CAS on `S` on line 13 (the linearization points of the paper). `HInv` links the ghost
variables to the history of the execution; together with the state invariant `CInv` it shows that
`lin` is a linearization of every execution (`isLinearization_lin`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Podc.GeneralizedCAS

open Cslib.SharedMemory

variable {T : ObjSpec} [LinearOrder T.Op] {P : Type} [DecidableEq P]
variable (cellInit : ℕ → CellVal T.Resp)

/-- The ghost variables agree with the history `α`. -/
structure HInv (α : List (Label P T)) (G : Ghost T P) : Prop where
  k_eq : ∀ q, G.k q = (respsOf α q).length
  ts_op : ∀ τ q k o, G.ts τ = some (q, k, o) → opOf α (q, k) = some o
  lin : IsLinearization α G.lin

lemma not_completed_cur {α : List (Label P T)} {G : Ghost T P} (h : HInv α G) (q : P) :
    ¬ Completed α (q, G.k q) := by
  simp [Completed, h.k_eq q]

theorem arun_hinv {α : List (Label P T)} {C : Cfg T P} {G : Ghost T P}
    (h : arun cellInit α = some (C, G)) : HInv α G := by
  refine arun_induction cellInit (Q := fun α _ G => HInv α G) ?_ ?_ h
  · exact ⟨fun _ => rfl, fun _ _ _ _ h => by simp [ginit] at h, isLinearization_nil⟩
  · intro α C G ℓ C' hα hH hs
    have hI := arun_inv cellInit hα
    have hrun := arun_fst cellInit hα
    cases ℓ with
    | inv p o =>
      obtain ⟨hp, -, -, -⟩ := step_inv_eff cellInit hs
      refine ⟨fun q => by simp [augStep, respsOf_append_inv, hH.k_eq q], fun τ q k o' h' => ?_,
        hH.lin.append_inv p o⟩
      simp only [augStep] at h'
      rw [opOf_append_of_invoked (Invoked.of_opOf_eq_some (hH.ts_op τ q k o' h'))]
      exact hH.ts_op τ q k o' h'
    | ret p r =>
      obtain ⟨hp, hpc, -, -, -⟩ := step_ret_eff cellInit hs
      refine ⟨fun q => ?_, fun τ q k o' h' => ?_, ?_⟩
      · simp only [augStep, Function.update_apply]
        split_ifs with hq
        · subst hq; simp [respsOf_append, hH.k_eq]
        · rw [respsOf_append_ret_of_ne _ _ hq, hH.k_eq q]
      · simp only [augStep] at h'; rw [opOf_append_ret]; exact hH.ts_op τ q k o' h'
      · simp only [augStep]
        apply hH.lin.append_ret_of_respIn
        rw [← hH.k_eq p]; exact hI.ret p r hp hpc
    | tau p =>
      obtain ⟨hp, -, -, -, -⟩ := step_tau_eff cellInit hs
      have hk : (augStep C (.tau p) G).k = G.k := by
        simp only [augStep]; split <;> (try split_ifs) <;> (try split) <;> rfl
      have hts0 : (C.loc p).pc ≠ .l3 → (augStep C (.tau p) G).ts = G.ts := by
        intro hpc
        cases h3 : (C.loc p).pc <;> simp only [augStep, h3] <;> (try split_ifs) <;>
          (try (cases G.ts (C.loc p).ann.time <;> rfl)) <;> first | rfl | exact absurd h3 hpc
      have hts : ∀ τ, (augStep C (.tau p) G).ts τ ≠ G.ts τ →
          (augStep C (.tau p) G).ts τ = (C.pend p).map fun o => (p, G.k p, o) := by
        intro τ hne
        by_cases hpc : (C.loc p).pc = .l3
        · simp only [augStep, hpc] at hne ⊢
          by_cases hτ : τ = C.M.cnt
          · subst hτ; simp
          · simp [Function.update_of_ne hτ] at hne
        · rw [hts0 hpc] at hne; exact absurd rfl hne
      refine ⟨fun q => by rw [hk, respsOf_append_tau, hH.k_eq q], fun τ q k o' h' => ?_, ?_⟩
      · rw [opOf_append_tau]
        by_cases hne : (augStep C (.tau p) G).ts τ = G.ts τ
        · rw [hne] at h'; exact hH.ts_op τ q k o' h'
        · rw [hts τ hne] at h'
          obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hp
          rw [ho] at h'; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl, rfl⟩ := h'
          obtain ⟨-, -, hop⟩ := (alg T P cellInit).run_pend_curOp hrun ho
          simpa [curOp, hH.k_eq] using hop
      · -- the linearization: unchanged, or one new linearization point (line 13)
        by_cases hlin : (augStep C (.tau p) G).lin = G.lin
        · rw [hlin]; exact hH.lin.append_tau p
        · have hpc : (C.loc p).pc = .l13 := by
            by_contra hpc; apply hlin
            simp only [augStep]; split <;> (try split_ifs) <;> (try split) <;> first | rfl | simp_all
          have hS : C.M.S = (C.loc p).snap := by
            by_contra hS; apply hlin
            simp [augStep, hpc, hS]
          obtain ⟨q', o', hts', hnot, -⟩ := hI.l13 p hp hpc hS
          have hl : (augStep C (.tau p) G).lin = G.lin ++ [((q', G.k q'), o')] := by
            simp [augStep, hpc, hS, hts']
          rw [hl]
          refine (hH.lin.push (hH.ts_op _ _ _ _ hts') hnot (not_completed_cur hH q')).append_tau p

/-- The linearization function: the ghost list `lin` of the augmented run. -/
noncomputable def linFun (α : List (Label P T)) : List (OpId P × T.Op) :=
  match arun cellInit α with
  | some (_, G) => G.lin
  | none => []

/-- **Theorem B.3.1.** Algorithm 1 is linearizable with respect to `T`: the operations ordered by
their successful CAS on `S` (line 13) form a linearization of every execution. -/
theorem linearizable : (alg T P cellInit).Linearizable := by
  refine ⟨linFun cellInit, fun α ⟨C, hC⟩ => ?_⟩
  obtain ⟨G, hG⟩ := exists_arun cellInit hC
  simp only [linFun, hG]
  exact (arun_hinv cellInit hG).lin

end Podc.GeneralizedCAS
