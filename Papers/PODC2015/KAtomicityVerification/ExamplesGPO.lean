import Papers.PODC2015.KAtomicityVerification.GPO
import Papers.PODC2015.KAtomicityVerification.Examples

/-!
# GPO on the example history of Figure 3.1 (Section 4.2)

Running the computable `History.gpo` on the history of Fig. 3.1 confirms the paper's Section 4.2:

* without `w(5)` (Assumption 4.1 holds): GPO answers YES for `k = 3` and NO for `k = 2`, both
  correct (`fig31'_kAtomic_three_not_two`);
* with `w(5)` (Assumption 4.1 fails, `fig31_not_assumption41`): GPO answers NO for `k = 3`,
  which is wrong since the history is 3-atomic (`fig31_kAtomic_three`). So Assumption 4.1 cannot
  be dropped from GPO's correctness theorem.

The tie-breaking linear order on values (needed by `gpo`) is the paper's numbering.
-/

namespace Podc.KAtomicityVerification

/-- The numbering of the values of Fig. 3.1. -/
def Val.toNat : Val → ℕ
  | .v1 => 1 | .v2 => 2 | .v3 => 3 | .v4 => 4 | .v5 => 5

/-- The numbering of the values of Fig. 3.1 without `5`. -/
def Val4.toNat : Val4 → ℕ
  | .v1 => 1 | .v2 => 2 | .v3 => 3 | .v4 => 4

instance : LinearOrder Val :=
  LinearOrder.lift' Val.toNat (by intro a b h; cases a <;> cases b <;> simp_all [Val.toNat])

instance : LinearOrder Val4 :=
  LinearOrder.lift' Val4.toNat (by intro a b h; cases a <;> cases b <;> simp_all [Val4.toNat])

/-- Section 4.2: without `w(5)`, GPO returns YES for `k = 3`. -/
theorem fig31'_gpo_three : fig31'.gpo 3 = true := by decide +kernel

/-- Section 4.2: without `w(5)`, GPO returns NO for `k = 2`. -/
theorem fig31'_gpo_two : fig31'.gpo 2 = false := by decide +kernel

/-- Section 4.2: on the full history (violating Assumption 4.1), GPO returns NO for `k = 3`
although the history is 3-atomic. -/
theorem fig31_gpo_three_wrong : fig31.gpo 3 = false ∧ fig31.KAtomic 3 :=
  ⟨by decide +kernel, fig31_kAtomic_three⟩

end Podc.KAtomicityVerification
