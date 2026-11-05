import Papers.PODC2012.LimitedUseSnapshots.PresTau

/-!
# Preservation of the invariant of the corrected Algorithm 2

`inv_of_run`: every execution of `alg P T true` satisfies `Inv`.
-/

set_option linter.unusedSectionVars false

namespace Podc.LimitedUseSnapshots

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] (T : Shape)

/-- Internal steps preserve the invariant. -/
lemma inv_step_tau {α : List (Label P maxArrObj)} {C C' : Cfg P} {p : P}
    (hpast : ∀ β D, β <+: α → (alg P T true).run β = some D → Inv T β D)
    (hrun : (alg P T true).run α = some C)
    (hs : (alg P T true).step C (.tau p) = some C') : Inv T (α ++ [.tau p]) C' := by
  have hI := hpast α C (List.prefix_refl _) hrun
  obtain ⟨-, hT⟩ := step_tau_cases T hs
  cases hT with
  | d0rd v a n l r hl hn hlt hpre => exact inv_tau_d0rd T hI hrun hl hn hlt hpre
  | d0wr v a n a' hl hleaf hdr hpre =>
    have hP := hI.pinv p
    rw [pinv_iff T hl] at hP
    obtain ⟨h1, h2, h3, h4⟩ := hP
    have hc := hpre h2 h3
    exact inv_tau_swWrite T hI hrun (TStep.d0wr v a n a' hl hleaf hdr hpre) h1 h2 hc
      (below_of_leaf hc hleaf) (h4.mono fun _ _ h => leftDom_append_replicate_true h n) hdr
  | upwr v a a' hl hdr =>
    have hP := hI.pinv p
    rw [pinv_iff T hl] at hP
    obtain ⟨h1, h2, h3, h4, h5⟩ := hP
    exact inv_tau_swWrite T hI hrun (TStep.upwr v a a' hl hdr) h1 h2 h3 h4 h5 hdr
  | w1 v hl => exact inv_tau_w1 T hI hrun hl hs
  | s1leaf e a hl hleaf => exact inv_tau_s1leaf T hpast hI hrun hl hleaf
  | s1node e a l r hl hn => exact inv_tau_s1node T hI hrun hl hn
  | s2 e a x hl => exact inv_tau_s2 T hI hrun hl
  | s3 e a x hl =>
    have hP := hI.pinv p
    rw [pinv_iff T hl] at hP
    exact inv_tau_s35 T hI hrun (TStep.s3 e a x hl) hP
  | s4 e a hl => exact inv_tau_s4 T hI hrun hl
  | s5 e a x hl =>
    have hP := hI.pinv p
    rw [pinv_iff T hl] at hP
    exact inv_tau_s35 T hI hrun (TStep.s5 e a x hl) hP

lemma inv_init : Inv T ([] : List (Label P maxArrObj)) (alg P T true).initCfg where
  pinv p := by
    rw [pinv_iff T (l := .idle) rfl]; rfl
  g1 a b := le_of_eq rfl
  q c hc := absurd hc (lt_irrefl 0)
  fs a ha := absurd ha (by simp [sw, Impl.initCfg, alg])
  w h := absurd h (lt_irrefl 0)
  comp y hy := absurd hy (by simp [Completed])
  compScan y r hy := absurd hy (by simp [opOf])
  hist y r hy := absurd hy (by simp [opOf])
  resp0 y o r hy := absurd hy (by simp [opOf])

/-- Every execution of the corrected algorithm satisfies the invariant. -/
theorem inv_of_run {α : List (Label P maxArrObj)} {C : Cfg P}
    (h : (alg P T true).run α = some C) : Inv T α C := by
  have key : ∀ β D, β <+: α → (alg P T true).run β = some D → Inv T β D := by
    refine Impl.run_induction (I := alg P T true)
      (Q := fun α _ => ∀ β D, β <+: α → (alg P T true).run β = some D → Inv T β D) ?_ ?_ h
    · intro β D hβ hD
      obtain rfl := List.prefix_nil.1 hβ
      simp only [Impl.run_nil, Option.some.injEq] at hD
      subst hD; exact inv_init (P := P) T
    · intro α C ℓ C' hrun hpast hs β D hβ hD
      rcases List.prefix_concat_iff.1 hβ with h' | h'
      · subst h'
        have hrun' : (alg P T true).run (α ++ [ℓ]) = some C' := by
          rw [Impl.run_concat, hrun]; exact hs
        rw [hrun'] at hD; cases hD
        have hI := hpast α C (List.prefix_refl _) hrun
        cases ℓ with
        | inv p o => exact inv_step_inv T hI hrun hs
        | ret p r => exact inv_step_ret T hI hrun hs
        | tau p => exact inv_step_tau T hpast hrun hs
      · exact hpast β D h' hD
  exact key α C (List.prefix_refl _) h

end Podc.LimitedUseSnapshots
