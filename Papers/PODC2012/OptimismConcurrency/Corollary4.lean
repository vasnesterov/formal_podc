import Papers.PODC2012.OptimismConcurrency.IRMReject
import Papers.PODC2012.OptimismConcurrency.Serializability

/-!
# Corollary 4: `σ_bad` is not excluded by the class `SM`

Corollary 4 claims that `I_RM` accepts every schedule accepted by an implementation in `P` or
`SM`; its proof combines Theorem 3 (false, `IRMReject.lean`) with the unproved remark that "it is
easy to see that implementations in SM and P can only accept observable schedules".

`sigmaBad_sm`: the schedule `σ_bad` rejected by `I_RM` is exported by a history that is honest,
LS-linearizable, *quiescent* (every operation completed) and safe-strict serializable
(serialization: the three initial inserts, `contains(4)`, `remove(3)`). So nothing in the
definition of `SM` prevents a TM-based implementation from accepting it; e.g. TL2 does (the
read-only `contains(4)` reads `X₃`, `X₄`, whose versions `remove(3)` did not change, and commits
without validation). We do not formalize a TM, so the refutation of Corollary 4 itself is not
mechanized; its proof is broken because it relies on Theorem 3.
-/

namespace Podc.OptimismConcurrency

/-- The serialization of `histBad`. -/
def ordBad : List (TxId ℕ Unit) := [(0, (), 0), (0, (), 1), (0, (), 2), (1, (), 0), (2, (), 0)]

lemma serialWitness_bad : SerialWitness (cseq histBad fun _ => false) ordBad := by
  rw [cseq_false, show complete histBad = histBad by decide]
  have h4 : ∀ t ∈ ordBad, ∀ t' ∈ ordBad, Precedes histBad t t' →
      ordBad.idxOf t < ordBad.idxOf t' := by
    decide +kernel
  exact ⟨by decide +kernel, isTxn_iff_of _ _ 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel), by decide +kernel, fun t t' ht ht' => h4 t ht t' ht'⟩

lemma histBad_live : ∀ t, IsTxn histBad t → ¬ (Incomplete histBad t ∨ Aborted histBad t) :=
  forall_txn_of histBad 3 (fun t => ¬ (Incomplete histBad t ∨ Aborted histBad t))
    (by decide +kernel) (by decide +kernel)

lemma lsl_histBad : LSL_LL histBad := by
  refine ⟨fun p x k hk => ?_, ?_⟩
  · cases x
    by_cases h3 : 3 ≤ p
    · rw [numOps, restrictPX_histBad_ge p h3] at hk; simp [splitOps] at hk
    · have key : ∀ p < 3, ∀ k < (splitOps (restrictPX histBad p ())).length,
          (if p = 0 then pre134.take (10 * k) else pre134) ++
            dropAbort ((splitOps (restrictPX histBad p ())).getD k []) ∈ SigLL := by decide
      exact ⟨_, key p (by omega) k hk⟩
  · obtain ⟨c, hc, -, -⟩ := lpRun_annBad
    exact hwLinearizable_of_lpRun' hc rfl

lemma quiescent_bad : Quiescent histBad :=
  forall_txn_of histBad 3 (fun t => TxComplete histBad t) (by decide +kernel) (by decide +kernel)

/-- `σ_bad` (rejected by `I_RM`) is exported by an honest, LS-linearizable, quiescent,
safe-strict serializable history. -/
theorem sigmaBad_sm : ∃ H : LHist ℕ, Honest H ∧ LSL_LL H ∧ Quiescent H ∧ SafeStrictSer H ∧
    Exports H sigmaBad ∧ ¬ Accepts IRM sigmaBad := by
  refine ⟨histBad, by decide, lsl_histBad, quiescent_bad,
    ⟨⟨fun _ => false, fun _ h => absurd h (by simp), ordBad, serialWitness_bad⟩,
      fun t ht hl => ?_⟩, sched_histBad, irm_rejects⟩
  exact absurd hl (histBad_live t ht)

end Podc.OptimismConcurrency
