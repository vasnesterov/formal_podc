import Papers.PODC2022.BluntingAdversary.Main
import Papers.PODC2022.BluntingAdversary.Clean

/-!
# Theorem 4.2 for any number of random steps (weaker bound)

`Prob[P(O^k) → B] ≤ Prob[P(O^a) → B] + (1 - q)` with `q = (max{0, k - r}/k)^(n-1)`, from
`Pr[B] ≤ Pr[B ∧ X] + Pr[¬X]` (`MDP.opt_add_le`), the corrected Lemma 4.3 (`optBX_le_prob_atom`)
and Lemma 4.5 (`Clean.optNX_le`). Together with `prob_iter_le_prob_impl` this gives
`Prob[O^k] ≤ min (Prob[O], Prob[O^a] + 1 - q)`. The paper's stronger bound
`Prob[O^a] + (1 - q)(Prob[O] - Prob[O^a])` is proved only for `r = 1` (`theorem_4_2_r1`).
-/

set_option linter.unusedSectionVars false

namespace Podc.BluntingAdversary

open Cslib.SharedMemory Removal
open scoped Classical

variable {P : Type} [Fintype P] [Nonempty P] [DecidableEq P] {A : ObjSpec} {C L : Type}
  {ι : Type} [DecidableEq ι] {Bs : ι → ObjSpec}
  {Pr : Program P A C} {I : Impl A Bs P L} {Pi : P → L → Prop} {k r : ℕ}

/-- **Lemma 4.5.** For every adversary against `P(O^k)`, `Pr[X] ≥ (max{0,k-r}/k)^(n-1)`. -/
theorem lemma_4_5 (hEF : EffectFree I Pi) (hWF : PreambleWF I Pi) (hk : 1 ≤ k)
    (hr : AtMostRandom Pr (implSem I Pi) r) :
    (sys Pr (iterSem I Pi k)).opt payNX (initCfg Pr (iterSem I Pi k)) ≤
      1 - (((k - r : ℕ) : ℝ) / k) ^ (Fintype.card P - 1) :=
  Clean.optNX_le hEF hWF hk hr

/-- **Theorem 4.2, weaker form valid for every `r`.** -/
theorem theorem_4_2_weak (hall : ∀ p o, I.allowed p o) (hTSL : TailStronglyLinearizable I Pi)
    (hEF : EffectFree I Pi) (hWF : PreambleWF I Pi) (hk : 1 ≤ k)
    (hr : AtMostRandom Pr (implSem I Pi) r) (B : (P → C) → Prop) :
    prob Pr (iterSem I Pi k) B ≤
      prob Pr (atomSem A) B + (1 - (((k - r : ℕ) : ℝ) / k) ^ (Fintype.card P - 1)) := by
  have hpX : ∀ s : Cfg P C (LK L) (Mem Bs), 0 ≤ payNX s := fun s => by
    unfold payNX; split_ifs <;> norm_num
  have hpX1 : ∀ s : Cfg P C (LK L) (Mem Bs), payNX s ≤ 1 := fun s => by
    unfold payNX; split_ifs <;> norm_num
  have hpBX : ∀ s : Cfg P C (LK L) (Mem Bs), 0 ≤ payBX B s := fun s => by
    unfold payBX; split_ifs <;> norm_num
  have hpBX1 : ∀ s : Cfg P C (LK L) (Mem Bs), payBX B s ≤ 1 := fun s => by
    unfold payBX; split_ifs <;> norm_num
  have hsplit := MDP.opt_add_le (M := sys Pr (iterSem I Pi k)) (pay := payB B) hpBX hpBX1 hpX hpX1
    (fun s => by
      unfold payB payBX payNX
      by_cases hB : B s.cl <;> by_cases hx : ∃ p, (s.lo p).xbad = true <;>
        simp_all <;> split_ifs <;> norm_num) (initCfg Pr (iterSem I Pi k))
  have h1 := optBX_le_prob_atom (Pr := Pr) hall hTSL hEF hWF hk B
  have h2 := lemma_4_5 (Pr := Pr) hEF hWF hk hr
  unfold prob
  unfold prob at h1
  linarith

/-- Both corrected bounds together. -/
theorem theorem_4_2_corrected (hall : ∀ p o, I.allowed p o) (hTSL : TailStronglyLinearizable I Pi)
    (hEF : EffectFree I Pi) (hWF : PreambleWF I Pi) (hk : 1 ≤ k)
    (hr : AtMostRandom Pr (implSem I Pi) r) (B : (P → C) → Prop) :
    prob Pr (iterSem I Pi k) B ≤ min (prob Pr (implSem I Pi) B)
      (prob Pr (atomSem A) B + (1 - (((k - r : ℕ) : ℝ) / k) ^ (Fintype.card P - 1))) :=
  le_min (prob_iter_le_prob_impl hEF hWF hk B) (theorem_4_2_weak hall hTSL hEF hWF hk hr B)

end Podc.BluntingAdversary
