import Papers.PODC2012.OrderPreservingByzRenaming.ConstTime
import Papers.PODC2012.OrderPreservingByzRenaming.Counterexample8

/-!
# Lemma 2 of arXiv:1205.0477v2 fails for `3t < N ≤ 3t²`

The paper states "Lemmas 1 and 2 hold for `N > 3t`", and Algorithm 2 (for `N > 3t`) starts its
approximation with `Skew₂ := 3t²`. For `N = 7`, `t = 2` the skew is at least 14 > 3t² = 12.

*Execution.* Correct processes `0, …, 4` with ids `10, …, 14`; Byzantine processes `5, 6`. In Round 1,
process `5` sends id `1` to `0, 1, 2` and id `2` to `3, 4`; process `6` sends `2` to `0` and `3` to
`1, 2, 3`. So the fake ids `1, 2, 3` are each received by three correct processes. In Round 2 both
Byzantine processes send process `0` the echo `{10, 11, 12, 1, 2, 3, 4}`, which is valid there, and
nothing to the others. At process `0` the fake ids `1, 2, 3` get 5 = N − t echoes and hence offset
`N = 7`, and `4` gets offset 2. Elsewhere they have 3 echoes and offset 3. So process `0` computes
`newId[10] = 30` and the others compute `16`.
-/

namespace Podc.OrderPreservingByzRenaming.ConstTime

open Cslib.Byzantine.LockStep TwoRound

namespace Cex7

/-- Byzantine processes. -/
def F : Finset (Fin 7) := {5, 6}

/-- Ids: process `j` has id `10 + j`. -/
def x (j : Fin 7) : ℕ := j.val + 10

/-- The adversary. -/
def adv (r : ℕ) (b p : Fin 7) : Option Msg :=
  match r with
  | 0 => if b.val = 5 then (if p.val ≤ 2 then some (.ident 1) else some (.ident 2))
         else if p.val = 0 then some (.ident 2) else if p.val ≤ 3 then some (.ident 3) else none
  | 1 => if p.val = 0 then some (.echo {10, 11, 12, 1, 2, 3, 4}) else none
  | _ => none

/-- The scenario. -/
def scen : Scenario (Fin 7) ℕ Msg where
  byz := ↑F
  input := x
  adv := adv

lemma hF : ∀ j, j ∈ scen.byz ↔ j ∈ F := fun _ => Iff.rfl

lemma newid0 : newidG 2 (inb1C F x adv 0) (inb2C F x adv 0) 10 = 30 := by decide +kernel

lemma newid1 : newidG 2 (inb1C F x adv 1) (inb2C F x adv 1) 10 = 16 := by decide +kernel

lemma newid1' : newidG 2 (inb1C F x adv 1) (inb2C F x adv 1) 11 = 23 := by decide +kernel

end Cex7

/-- **Lemma 2 fails for `N > 3t`**: for `N = 7 > 3t`, `t = 2`, two correct processes compute values
of the correct id `10` that differ by `14 > 3t² = 12` (the run has 2 Byzantine processes, reliable
links and distinct correct ids). -/
theorem lemma_2_false_of_gt_3t :
    7 > 3 * 2 ∧ Cex7.scen.byz ∈ (atMost 2 : AdvStructure (Fin 7)) ∧
      (0 : Fin 7) ∉ Cex7.scen.byz ∧ (1 : Fin 7) ∉ Cex7.scen.byz ∧
      newidG 2 (inb1 Cex7.scen 0) (inb2 Cex7.scen 0) 10 =
        newidG 2 (inb1 Cex7.scen 1) (inb2 Cex7.scen 1) 10 + 14 ∧ 14 > 3 * 2 ^ 2 := by
  refine ⟨by norm_num, by simp [Cex7.scen, Set.ncard_coe_finset, Cex7.F],
    by simp [Cex7.scen, Cex7.F], by simp [Cex7.scen, Cex7.F], ?_, by norm_num⟩
  rw [inb1_eq_inb1C Cex7.hF, inb2_eq_inb2C Cex7.hF, inb1_eq_inb1C Cex7.hF, inb2_eq_inb2C Cex7.hF]
  exact Cex7.newid0.trans (by erw [Cex7.newid1])

end Podc.OrderPreservingByzRenaming.ConstTime
