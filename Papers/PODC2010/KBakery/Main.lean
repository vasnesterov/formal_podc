import Papers.PODC2010.KBakery.Exclusion
import Papers.PODC2010.KBakery.FCFS
import Papers.PODC2010.KBakery.Fife
import Papers.PODC2010.KBakery.Liveness
import Papers.PODC2010.KBakery.RMRDSM
import Papers.PODC2010.KBakery.RMRCC
import Papers.PODC2010.KBakery.NonVacuity

/-!
# The k-Bakery (Danek, PODC 2010): main theorems

* `theorem_8`: the unshaded algorithm of Figure 2 satisfies k-exclusion, starvation freedom,
  k-FCFS, and has RMR complexity `Θ(N)` in the DSM and CC models.
* `theorem_9`: the full (FIFE) algorithm of Figure 2 satisfies k-exclusion, starvation freedom,
  FIFE (with the explicit bound `4N + 7`), k-FCFS, and RMR complexity `Θ(N)` in both models.

Passages: `p` leaves the NCS with its step at time `t₀` and does not return to the NCS strictly
between `t₀` and `t₁` (`InPassage`); the passage is complete if `p` is back in the NCS at `t₁`.
-/

set_option linter.unusedSectionVars false

namespace Podc.KBakery

open Finset

variable {P : Type} [LinearOrder P] [Fintype P]

/-- `[t₀, t₁)` is (a prefix of) one passage of `p`: `p` leaves the NCS at time `t₀` and has not
returned to it before `t₁`. -/
def Run.InPassage {fife : Bool} {k : ℕ} (r : Run fife k P) (p : P) (t₀ t₁ : ℕ) : Prop :=
  (r.s t₀).pc p = .ncs ∧ r.sched t₀ = p ∧ t₀ < t₁ ∧ ∀ t, t₀ < t → t < t₁ → (r.s t).pc p ≠ .ncs

lemma ccTotal_false {N : ℕ} (h : 1 ≤ N) : ccTotal false N = 9 * N - 6 := by
  simp [ccTotal, ccReserve]; omega

lemma ccTotal_true {N : ℕ} (h : 1 ≤ N) : ccTotal true N = 13 * N - 6 := by
  simp [ccTotal, ccReserve]; omega

open Classical in
/-- **Theorem 8** of the paper (Theorem 5.9 of the thesis). The unshaded algorithm of Figure 2
satisfies k-exclusion, starvation freedom (if fewer than `k` processes crash) and k-FCFS; a
passage makes at most `4(N − 1)` RMRs in the DSM model (exactly `4(N − 1)` if it is complete) and
at most `9N − 6` RMRs in the CC model (at least `3N − 1` if it is complete). -/
theorem theorem_8 (k : ℕ) :
    (∀ s : Cfg P, Reachable false k s → (univ.filter fun q => s.pc q = .cs).card ≤ k) ∧
    (∀ r : Run false k P, (univ.filter fun q => r.Crashed q).card < k →
      ∀ p, ¬ r.Crashed p → ∀ t₀, ((r.s t₀).pc p).InTrying → ∃ t ≥ t₀, (r.s t).pc p = .cs) ∧
    (∀ (r : Run false k P) (Y : Finset P), Y.card = k → ∀ p t₀,
      (r.s t₀).pc p = .ncs → (∀ q ∈ Y, ((r.s t₀).pc q).InWaiting) →
      ∀ t₁, t₀ ≤ t₁ → (r.s t₁).pc p = .cs → ∃ q ∈ Y, ∃ t, t₀ ≤ t ∧ t ≤ t₁ ∧ (r.s t).pc q = .cs) ∧
    (∀ (r : Run false k P) p t₀ t₁, r.InPassage p t₀ t₁ →
      r.rmrs rmrDSM p t₀ t₁ ≤ 4 * (Fintype.card P - 1) ∧
      ((r.s t₁).pc p = .ncs → r.rmrs rmrDSM p t₀ t₁ = 4 * (Fintype.card P - 1))) ∧
    (∀ (r : Run false k P) p t₀ t₁, r.InPassage p t₀ t₁ →
      r.rmrs rmrCC p t₀ t₁ ≤ 9 * Fintype.card P - 6 ∧
      ((r.s t₁).pc p = .ncs → 3 * Fintype.card P - 1 ≤ r.rmrs rmrCC p t₀ t₁)) := by
  refine ⟨fun s hs => k_exclusion hs, fun r hcr p hp t₀ ht => starvation_freedom r hcr p hp t₀ ht,
    fun r Y hY p t₀ hp hY₀ t₁ h h₁ => k_fcfs r Y hY p t₀ hp hY₀ t₁ h h₁, ?_, ?_⟩
  · rintro r p t₀ t₁ ⟨hp, hs, h₀₁, hin⟩
    exact ⟨rmr_dsm_le r p hp hs h₀₁ hin, fun hend => rmr_dsm_complete r p hp hs h₀₁ hin hend⟩
  · rintro r p t₀ t₁ ⟨hp, hs, h₀₁, hin⟩
    have hN : 1 ≤ Fintype.card P := Fintype.card_pos_iff.2 ⟨p⟩
    rw [← ccTotal_false hN]
    exact ⟨rmr_cc_le r p hp hs h₀₁ hin, fun hend => rmr_cc_complete_ge r p hp hs h₀₁ hin hend⟩

open Classical in
/-- **Theorem 9** of the paper (Theorem 5.20 of the thesis). The full algorithm of Figure 2
satisfies k-exclusion, starvation freedom (if fewer than `k` processes crash), FIFE (with the
bound `4N + 7` on the number of own steps) and k-FCFS; a passage makes at most `5(N − 1)` RMRs in
the DSM model (exactly `5(N − 1)` if it is complete) and at most `13N − 6` RMRs in the CC model
(at least `3N − 1` if it is complete). -/
theorem theorem_9 (k : ℕ) :
    (∀ s : Cfg P, Reachable true k s → (univ.filter fun q => s.pc q = .cs).card ≤ k) ∧
    (∀ r : Run true k P, (univ.filter fun q => r.Crashed q).card < k →
      ∀ p, ¬ r.Crashed p → ∀ t₀, ((r.s t₀).pc p).InTrying → ∃ t ≥ t₀, (r.s t).pc p = .cs) ∧
    (∀ (r : Run true k P) p q t₀ t₁, ((r.s t₀).pc p).InWaiting → (r.s t₀).pc q = .ncs →
      t₀ ≤ t₁ → (r.s t₁).pc q = .cs → (∀ t, t₀ ≤ t → t ≤ t₁ → (r.s t).pc p ≠ .cs) →
      ∀ t₂, t₁ ≤ t₂ → 4 * Fintype.card P + 7 ≤ r.stepsOf p t₁ t₂ →
        ∃ t, t₁ ≤ t ∧ t ≤ t₂ ∧ (r.s t).pc p = .cs) ∧
    (∀ (r : Run true k P) (Y : Finset P), Y.card = k → ∀ p t₀,
      (r.s t₀).pc p = .ncs → (∀ q ∈ Y, ((r.s t₀).pc q).InWaiting) →
      ∀ t₁, t₀ ≤ t₁ → (r.s t₁).pc p = .cs → ∃ q ∈ Y, ∃ t, t₀ ≤ t ∧ t ≤ t₁ ∧ (r.s t).pc q = .cs) ∧
    (∀ (r : Run true k P) p t₀ t₁, r.InPassage p t₀ t₁ →
      r.rmrs rmrDSM p t₀ t₁ ≤ 5 * (Fintype.card P - 1) ∧
      ((r.s t₁).pc p = .ncs → r.rmrs rmrDSM p t₀ t₁ = 5 * (Fintype.card P - 1))) ∧
    (∀ (r : Run true k P) p t₀ t₁, r.InPassage p t₀ t₁ →
      r.rmrs rmrCC p t₀ t₁ ≤ 13 * Fintype.card P - 6 ∧
      ((r.s t₁).pc p = .ncs → 3 * Fintype.card P - 1 ≤ r.rmrs rmrCC p t₀ t₁)) := by
  refine ⟨fun s hs => k_exclusion hs, fun r hcr p hp t₀ ht => starvation_freedom r hcr p hp t₀ ht,
    fun r p q t₀ t₁ hp hq h h₁ hcs t₂ h₂ hst => fife r p q t₀ t₁ hp hq h h₁ hcs t₂ h₂ hst,
    fun r Y hY p t₀ hp hY₀ t₁ h h₁ => k_fcfs r Y hY p t₀ hp hY₀ t₁ h h₁, ?_, ?_⟩
  · rintro r p t₀ t₁ ⟨hp, hs, h₀₁, hin⟩
    exact ⟨rmr_dsm_le r p hp hs h₀₁ hin, fun hend => rmr_dsm_complete r p hp hs h₀₁ hin hend⟩
  · rintro r p t₀ t₁ ⟨hp, hs, h₀₁, hin⟩
    have hN : 1 ≤ Fintype.card P := Fintype.card_pos_iff.2 ⟨p⟩
    rw [← ccTotal_true hN]
    exact ⟨rmr_cc_le r p hp hs h₀₁ hin, fun hend => rmr_cc_complete_ge r p hp hs h₀₁ hin hend⟩

end Podc.KBakery
