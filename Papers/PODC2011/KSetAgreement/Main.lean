import Papers.PODC2011.KSetAgreement.AlgorithmLiveness
import Papers.PODC2011.KSetAgreement.Degenerate
import Papers.PODC2011.KSetAgreement.Abstract

/-!
# Main results of [BRS11]

* `theorem8`: with up to `f < n` initially dead processes (and at least `n` input values),
  `k`-set agreement is solvable iff `k * n > (k + 1) * f`.
* `theorem2_vs_theorem8`: Theorem 2's bound is not the bound of Theorem 8 — for `n = 5`, `f = 3`,
  `k = 2`, 2-set agreement is impossible with `f - 1` initial crashes plus one crash during the run
  (Theorem 2, asynchronous processes) but solvable with up to `f` initially dead processes.

See also `theorem2`, `corollary5`, `theorem1_async` (`Theorem2.lean`),
`Abstract.theorem1_corrected`, `Abstract.Counterexample.theorem1_statement_false`
(`Abstract.lean`), `theorem8_false_of_f_eq_n`, `theorem2_false_of_f_eq_n` (`Degenerate.lean`).
-/

namespace KSetAgreement

/-- **Theorem 8** of [BRS11]: in an asynchronous system with `n` processes, up to `f < n` of which
may be initially dead, `k`-set agreement (inputs from `V`, `|V| ≥ n`) is solvable if and only if
`k * n > (k + 1) * f`. -/
theorem theorem8 (n f k : ℕ) (V : Type) (hf : f < n) (hV : Nonempty (Fin n ↪ V)) :
    (∃ (M S : Type) (_ : DecidableEq M) (A : KAlgorithm (Fin n) M S V),
      SolvesKSA A k (InitDead f)) ↔ (k + 1) * f < k * n := by
  refine ⟨fun ⟨M, S, _, A, hA⟩ => ?_, fun hk => InitDeadAlg.initDead_possible n f k V hk⟩
  by_contra hk
  push Not at hk
  have hk' : k * n ≤ (k + 1) * f := by linarith
  have hkn : k + 1 ≤ n := by
    by_contra h
    push Not at h
    have : (k + 1) * f < (k + 1) * n := Nat.mul_lt_mul_of_pos_left hf (by omega)
    nlinarith
  obtain ⟨e⟩ := hV
  exact initDead_impossible A (by simp) hf hk' (fun i => e (Fin.castLE hkn i))
    (e.injective.comp (Fin.castLE_injective hkn)) hA

/-- Theorem 2 does not "tightly capture" Theorem 8: for `n = 5`, `f = 3`, `k = 2` (where
`k (n - f) = 4 ≤ n - 1`), 2-set agreement is impossible with Theorem 2's failure pattern but
solvable with up to 3 initially dead processes. -/
theorem theorem2_vs_theorem8 :
    (∀ (M S : Type) [DecidableEq M] (A : KAlgorithm (Fin 5) M S (Fin 5)),
      ¬ SolvesKSA A 2 (OneCrash 3)) ∧
    ∃ (M S : Type) (_ : DecidableEq M) (A : KAlgorithm (Fin 5) M S (Fin 5)),
      SolvesKSA A 2 (InitDead 3) :=
  ⟨fun _ _ _ A => theorem2 (n := 5) A (by simp) (by norm_num) (by norm_num) (by norm_num)
      (fun i => Fin.castLE (by norm_num) i) (Fin.castLE_injective (by norm_num)),
    InitDeadAlg.initDead_possible 5 3 2 (Fin 5) (by norm_num)⟩

end KSetAgreement
