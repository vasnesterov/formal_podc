import Papers.PODC2022.ConsensusFromSwap.Alg1AgreeBasic

/-!
# Algorithm 1, k-agreement: Lemma 5

If `cfg s` is `⟨V, p⟩`-total, `cfg s'` (`s ≤ s'`) is `⟨V', p'⟩`-total and `V ⋠ V'`, then there are
`N` distinct processes, all different from `p` and `p'`, that swap different objects during
`[s, s')`, whose lap counters dominate `V` at time `s'`, and which are undecided at time `s`.

Instead of the paper's "first non-dominating swap on each object" argument we prove a forward
invariant (`destrInv`): every object whose lap counter does not dominate `V` is assigned a
"destroyer" (the process that first swapped a non-dominating counter over a dominating one), the
assignment is injective on such objects, and every destroyer's lap counter dominates `V`.
-/

namespace ConsensusFromSwap.Alg1.Agree.Sched

open ConsensusFromSwap

set_option linter.unusedSectionVars false

variable {P : Type} [DecidableEq P] {m N : ℕ} [NeZero m] [NeZero N] (E : Sched P m N)

/-- The invariant behind Lemma 5 (for a `⟨V, p⟩`-total configuration at time `s`): the objects
whose lap counter does not dominate `V` at time `t` have distinct destroyers. -/
def DestrInv (s : ℕ) (V : Lap m) (p : P) (t : ℕ) : Prop :=
  ∃ d : Fin N → P, ∀ i, ¬ V ≤ ((E.cfg t).mem i).1 →
    V ≤ (E.st t (d i)).U ∧ d i ≠ p ∧ (E.st s (d i)).dec = none ∧
    (∃ u, s ≤ u ∧ u < t ∧ E.σ u = d i ∧ E.Wr u i) ∧
    ∀ j, ¬ V ≤ ((E.cfg t).mem j).1 → d j = d i → j = i

lemma U_ge_of_total {s t : ℕ} {V : Lap m} {p : P} (hT : E.Total s V p) (hst : s ≤ t) :
    V ≤ (E.st t p).U :=
  hT.2 ▸ E.st_U_mono hst p

lemma destrInv {s t : ℕ} {V : Lap m} {p : P} (hT : E.Total s V p) (hst : s ≤ t) :
    E.DestrInv s V p t := by
  induction t, hst using Nat.le_induction with
  | base =>
    refine ⟨fun _ => p, fun i hi => absurd ?_ hi⟩
    rw [hT.1 i]
  | succ t hst ih =>
    classical
    obtain ⟨d, hd⟩ := ih
    set q := E.σ t with hq
    -- Classification of non-dominating objects at time `t + 1`.
    have key : ∀ i, ¬ V ≤ ((E.cfg (t + 1)).mem i).1 →
        (E.Wr t i ∧ V ≤ ((E.cfg t).mem i).1 ∧ ¬ V ≤ (E.st t q).U) ∨
        (¬ (E.Wr t i ∧ V ≤ ((E.cfg t).mem i).1) ∧ ¬ V ≤ ((E.cfg t).mem i).1) := by
      intro i hi
      by_cases hW : E.Wr t i
      · rw [E.mem_succ_of_wr hW] at hi
        by_cases hV : V ≤ ((E.cfg t).mem i).1
        · exact Or.inl ⟨hW, hV, hi⟩
        · exact Or.inr ⟨fun h => hV h.2, hV⟩
      · rw [E.mem_succ_of_not_wr hW] at hi
        exact Or.inr ⟨fun h => hW h.1, hi⟩
    refine ⟨fun i => if E.Wr t i ∧ V ≤ ((E.cfg t).mem i).1 then q else d i, fun i hi => ?_⟩
    rcases key i hi with ⟨hW, hV, hU⟩ | ⟨hA, hV⟩
    · simp only [hW, hV, and_self, ite_true]
      refine ⟨?_, ?_, E.dec_none_of_le hst hW.1, ⟨t, hst, Nat.lt_succ_self t, rfl, hW⟩, ?_⟩
      · rw [E.st_succ_self hq.symm hW.1]
        refine hV.trans (le_of_eq_of_le ?_ (resp_le_after _ _))
        rw [hW.2]
      · rintro rfl
        exact hU (E.U_ge_of_total hT hst)
      · intro j hj hdj
        rcases key j hj with ⟨hW', _, _⟩ | ⟨hA', hV'⟩
        · exact hW'.2.symm.trans hW.2
        · simp only [hA', ite_false] at hdj
          exact absurd (hdj ▸ (hd j hV').1) hU
    · simp only [hA, ite_false]
      obtain ⟨h1, h2, h3, ⟨u, hu1, hu2, hu3, hu4⟩, h5⟩ := hd i hV
      refine ⟨h1.trans (E.st_U_succ t _), h2, h3, ⟨u, hu1, by omega, hu3, hu4⟩, ?_⟩
      intro j hj hdj
      rcases key j hj with ⟨hW', hV', hU'⟩ | ⟨hA', hV'⟩
      · simp only [hW', hV', and_self, ite_true] at hdj
        exact absurd (hdj ▸ h1) hU'
      · simp only [hA', ite_false] at hdj
        exact h5 j hV' hdj

/-- **Lemma 5** of [Ovens, PODC 2022]. Let `cfg s` be `⟨V, p⟩`-total and `cfg s'` be
`⟨V', p'⟩`-total with `s ≤ s'` and `V ⋠ V'`. Then there are `N` (`= n − k`) distinct processes
`d i`, different from `p` and `p'`, such that `d i` swaps object `i` during `[s, s')`, the lap
counter of `d i` at time `s'` dominates `V`, and (an addition used in Lemma 6) `d i` has not
decided at time `s`. -/
theorem lemma5 {s s' : ℕ} {V V' : Lap m} {p p' : P} (hT : E.Total s V p) (hT' : E.Total s' V' p')
    (hss' : s ≤ s') (hV : ¬ V ≤ V') :
    ∃ d : Fin N → P, Function.Injective d ∧ ∀ i, d i ≠ p ∧ d i ≠ p' ∧
      V ≤ (E.st s' (d i)).U ∧ (E.st s (d i)).dec = none ∧
      ∃ u, s ≤ u ∧ u < s' ∧ E.σ u = d i ∧ E.Wr u i := by
  obtain ⟨d, hd⟩ := E.destrInv hT hss'
  have hnd : ∀ i, ¬ V ≤ ((E.cfg s').mem i).1 := fun i => by rw [hT'.1 i]; exact hV
  refine ⟨d, fun i j hij => ((hd j (hnd j)).2.2.2.2 i (hnd i) hij), fun i => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := hd i (hnd i)
  refine ⟨h2, ?_, h1, h3, h4⟩
  rintro hp'
  rw [hp', hT'.2] at h1
  exact hV h1

end ConsensusFromSwap.Alg1.Agree.Sched
