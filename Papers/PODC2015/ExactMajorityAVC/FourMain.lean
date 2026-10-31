import Papers.PODC2015.ExactMajorityAVC.FourTreeA
import Papers.PODC2015.ExactMajorityAVC.FourTreeB

/-!
# Theorem B.1, structural part: correct four-state protocols behave like the known one

`theorem_B_1_invariant`: every symmetric four-state protocol satisfying the three correctness
properties of Theorem B.1 preserves `#S0 − #S1` in every interaction — the hypothesis of
Claim B.8, from which the paper derives the `Ω(1/ϵ)` bound (see `FourLowerBound.lean`).

Proof: Claims B.2–B.5 (`FourClaims.lean`) fix `γ` and the same-output transitions; the remaining
cases (Claims B.6, B.7 and Cases 1–3 of the paper) are discharged by the certified case trees
`treeA`/`treeB` (one for each of `γ(X) = 0` and `γ(X) = 1`).
-/

namespace Podc.ExactMajorityAVC.Four

open Cslib.PopulationProtocol Q4 Multiset

variable {P : Protocol Q4} {γ : Q4 → Bool}

lemma pair_eq (p q : Q4) : pair (p, q) = {p, q} := rfl

/-- **Theorem B.1 (structural part).** Every four-state exact-majority protocol satisfying the
three correctness properties of Theorem B.1, with unordered interactions, keeps `#S0 − #S1`
invariant in every interaction. -/
theorem theorem_B_1_invariant (hC : Correct P γ) (hS : Symmetric P) : Invariant P := by
  have g0 : γ S0 = false := gamma_S hC false
  have g1 : γ S1 = true := gamma_S hC true
  have hXY := gamma_X_ne_gamma_Y hC
  cases hX : γ X
  · have hY : γ Y = true := by cases h : γ Y <;> simp_all
    have s0 : Side γ false X := ⟨by decide, hX, fun q hq => by cases q <;> simp_all⟩
    have s1 : Side γ true Y := ⟨by decide, hY, fun q hq => by cases q <;> simp_all⟩
    have hγ : ∀ q, γ q = gammaA q := fun q => by cases q <;> simp [gammaA, *]
    have hbase : Agrees P baseA := by
      intro e he
      simp only [baseA, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl
      · exact claim_B_5 hC s0 g0 g0
      · exact claim_B_5 hC s0 g0 hX
      · exact claim_B_5 hC s0 hX hX
      · exact claim_B_5 hC s1 g1 g1
      · exact claim_B_5 hC s1 g1 hY
      · exact claim_B_5 hC s1 hY hY
    exact checkTree_sound hC hS hγ treeA hbase treeA_check
  · have hY : γ Y = false := by cases h : γ Y <;> simp_all
    have s0 : Side γ false Y := ⟨by decide, hY, fun q hq => by cases q <;> simp_all⟩
    have s1 : Side γ true X := ⟨by decide, hX, fun q hq => by cases q <;> simp_all⟩
    have hγ : ∀ q, γ q = gammaB q := fun q => by cases q <;> simp [gammaB, *]
    have hbase : Agrees P baseB := by
      intro e he
      simp only [baseB, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl
      · exact claim_B_5 hC s0 g0 g0
      · exact claim_B_5 hC s0 g0 hY
      · exact claim_B_5 hC s0 hY hY
      · exact claim_B_5 hC s1 g1 g1
      · exact claim_B_5 hC s1 g1 hX
      · exact claim_B_5 hC s1 hX hX
    exact checkTree_sound hC hS hγ treeB hbase treeB_check

lemma diff_add (c c' : Multiset Q4) : diff (c + c') = diff c + diff c' := by
  simp only [diff, count_add]; omega

/-- Along every execution `#S0 − #S1` stays constant. -/
theorem Invariant.reach (h : Invariant P) {c c' : Multiset Q4} (hr : Reach P c c') :
    diff c' = diff c := by
  induction hr with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨p, q, r, rfl, rfl⟩ := exists_of_step hs
    rw [← ih]
    have e1 : (P.δ p q).1 ::ₘ (P.δ p q).2 ::ₘ r = pair (P.δ p q) + r := by
      simp [pair, insert_eq_cons]
    have e2 : p ::ₘ q ::ₘ r = ({p, q} : Multiset Q4) + r := by simp [insert_eq_cons]
    rw [e1, e2, diff_add, diff_add, h]

end Podc.ExactMajorityAVC.Four
