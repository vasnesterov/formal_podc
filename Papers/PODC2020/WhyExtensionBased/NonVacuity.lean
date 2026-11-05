import Papers.PODC2020.WhyExtensionBased.Main

/-!
# Sanity checks

* The game is winnable: `0`-set agreement (no value may be output, which is impossible as soon as
  there is a process) has an extension-based impossibility proof — the trivial prover wins because the
  initial configurations already admit no valid output vector. So `¬ HasEBProof` in Theorem 5.7 is not
  vacuous.
* The hypotheses of `theorem_5_7` are satisfiable (`n = 3`, `k = 2`, the case singled out in the
  paper's screening).
-/

namespace Podc.WhyExtensionBased

open Cslib.NIS

variable {P X : Type} [DecidableEq P]

/-- `0`-set agreement among a nonempty set of processes has an extension-based impossibility
proof. -/
theorem hasEBProof_setAgreement_zero [Nonempty P] [Finite P] [Inhabited X] :
    HasEBProof (P := P) (setAgreement X 0) := by
  refine ⟨fun _ => .oracle (initC default) (∅, default), fun δ pl hc hv => ?_⟩
  have hst : ∀ k, states pl k = GState.start := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => show (states pl k).next (pl k).1 = _; rw [hc k, ih]; rfl
  refine ⟨fun k => ?_, Or.inl ⟨0, initC default, Or.inl ⟨default, (reinit_initC _ _).symm⟩, ?_⟩⟩
  · rw [hc k, hst k]
    exact ⟨Or.inl ⟨default, (reinit_initC _ _).symm⟩, trivial⟩
  · refine ⟨Set.mem_univ _, ?_⟩
    rintro ⟨y, ⟨-, hy⟩, -⟩
    obtain ⟨j⟩ := ‹Nonempty P›
    have : (Set.range y).Nonempty := ⟨y j, j, rfl⟩
    have := (Set.ncard_pos (Set.toFinite _)).2 this
    omega

/-- The hypotheses of Theorem 5.7 are satisfiable: `3` processes, `2`-set agreement. -/
example : ¬ HasEBProof (P := Fin 3) (setAgreement (Fin 3) 2) :=
  theorem_5_7 (n := 3) (k := 2) le_rfl (by norm_num)

end Podc.WhyExtensionBased
