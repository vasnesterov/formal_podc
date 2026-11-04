import Papers.PODC2011.AtMostOnceEffectiveness.Main

/-!
# Theorem 4.4 fails when `n ≤ β + m − 2`

For `n < β + m − 1` the formula `n − (β + m − 2)` is `≤ 0`, but `KK_β` may still be forced to
perform jobs. Smallest instance: `m = n = β = 2`, `f = 1`. The formula gives `0`, but every fair
run with at most one crash performs a job: as long as no job is performed, process `0` always
targets job `1` and process `1` job `2`, so no `check` fails and no process can terminate
(`noJob_inv`). Together with Theorem 2.1 (`E ≤ n − f = 1`), `E_{KK_2}(2, 2, 1) = 1`.
-/

namespace Podc.AtMostOnceEffectiveness

open Function

/-- The invariant of `KK_2` with `m = n = 2` while no job has been performed. -/
def NoJobInv (C : Config 2 Reg ℕ LState) : Prop :=
  C.log = [] → ∀ p : Fin 2, (C.loc p).status ≠ .finished ∧
    ((C.loc p).status = .compNext → (C.loc p).tryS = ∅) ∧
    ((C.loc p).status ≠ .compNext → (C.loc p).nxt = p.val + 1) ∧
    (C.mem (.next p) = 0 ∨ C.mem (.next p) = p.val + 1) ∧
    p.val + 1 ∉ (C.loc p).tryS

lemma doneS_empty_of_log_nil {C : Config 2 Reg ℕ LState} (hC : (kk 2 2 2).Reachable C)
    (hl : C.log = []) (p : Fin 2) : (C.loc p).doneS = ∅ := by
  obtain ⟨hI, hI2⟩ := inv_of_reachable (by norm_num) hC
  have h := (hI2.doneRec p).trans (recorded_subset_jobs hI)
  have hj : Alg.jobs 2 C = ∅ := by simp [Alg.jobs, hl]
  rw [hj] at h
  exact Finset.subset_empty.mp h

lemma noJob_inv {C : Config 2 Reg ℕ LState} (hC : (kk 2 2 2).Reachable C) : NoJobInv C := by
  induction hC with
  | init =>
    intro _ p
    simp [Alg.init, kk, LState.init]
  | @step C C' q hC hs ih =>
    intro hl
    obtain ⟨l, hl'⟩ := Alg.step_log hs
    have hl0 : C.log = [] := by rw [hl] at hl'; exact (List.append_eq_nil_iff.mp hl'.symm).1
    have E := ih hl0
    have hd := doneS_empty_of_log_nil hC hl0
    obtain ⟨hI, -⟩ := inv_of_reachable (by norm_num) hC
    have hks := step_inv hs
    intro p
    by_cases hpq : p = q
    · subst hpq
      obtain ⟨e1, e2, e3, e4, e5⟩ := E p
      have hfree : free 2 (C.loc p) = {1, 2} := by rw [free, hd p]; decide
      cases hks with
      | compNext h hb =>
        simp only [update_self]
        have ht := e2 h
        rw [ht, hfree] at *
        have hk : kIdx 2 p.val 2 = p.val + 1 := by unfold kIdx; have := p.isLt; split_ifs <;> omega
        have hr : rank ({1, 2} : Finset ℕ) (p.val + 1) = p.val + 1 := by
          have := p.isLt
          apply rank_eq_of_below _ (by omega)
          · interval_cases (p.val) <;> decide
          · interval_cases (p.val) <;> decide
        refine ⟨by simp, by simp, by simp [hfree, hk, hr], e4, by simp⟩
      | finish h hb =>
        exfalso; apply hb; rw [e2 h, hfree]; decide
      | setNext h =>
        simp only [update_self]
        refine ⟨by simp, by simp, fun _ => e3 (by rw [h]; simp), Or.inr (by simp [e3 (by rw [h]; simp)]), e5⟩
      | tryRead h hq =>
        simp only [update_self, adv_status, adv_nxt, adv_tryS]
        have hqm := hI.qlt p (Or.inl h)
        set a : Fin 2 := ⟨(C.loc p).q, hqm⟩
        have hap : a ≠ p := fun e => hq (by have := congrArg Fin.val e; simp [a] at this; omega)
        obtain ⟨-, -, -, f4, -⟩ := E a
        refine ⟨by split_ifs <;> simp [h], by split_ifs <;> simp [h], fun _ => e3 (by rw [h]; simp),
          e4, ?_⟩
        unfold addTry
        intro hm
        split_ifs at hm with hv
        · rcases Finset.mem_insert.mp hm with hm | hm
          · have : C.mem (.next a) = a.val + 1 := by
              rcases f4 with f4 | f4
              · simp [a] at f4; omega
              · exact f4
            simp only [a] at this
            have hap' : a.val ≠ p.val := fun e => hap (Fin.ext e)
            simp only [a] at hap'
            omega
          · exact e5 hm
        · exact e5 hm
      | trySkip h hq =>
        simp only [update_self, adv_status, adv_nxt, adv_tryS]
        exact ⟨by split_ifs <;> simp [h], by split_ifs <;> simp [h], fun _ => e3 (by rw [h]; simp),
          e4, e5⟩
      | doneRead h hq hp hv =>
        simp only [update_self]
        exact ⟨by simp [h], by simp [h], fun _ => e3 (by rw [h]; simp), e4, e5⟩
      | doneAdv h hq =>
        simp only [update_self, adv_status, adv_nxt, adv_tryS]
        exact ⟨by split_ifs <;> simp [h], by split_ifs <;> simp [h], fun _ => e3 (by rw [h]; simp),
          e4, e5⟩
      | checkOk h h1 h2 =>
        simp only [update_self]
        exact ⟨by simp, by simp, fun _ => e3 (by rw [h]; simp), e4, e5⟩
      | checkFail h h1 =>
        exfalso
        rw [e3 (by rw [h]; simp), hd p] at h1
        simp only [Finset.notMem_empty, or_false] at h1
        exact e5 h1
      | perform h => simp at hl
      | writeDone h =>
        exfalso
        have := hI.plogEq p
        simp [plog, pend, h, hl0] at this
    · rw [hks.loc_ne hpq, hks.mem_next_ne _ (val_ne_of_ne hpq)]
      exact E p

/-- In `KK_2` with `m = n = 2`, every fair run with at most one crash performs a job. -/
theorem kk222_do_pos (r : (kk 2 2 2).Run) (F : Finset (Fin 2)) (hF : F.card ≤ 1)
    (hfair : r.Fair F) : 1 ≤ r.Do 2 := by
  obtain ⟨K, hK⟩ := lemma_4_3 (by norm_num) r
  obtain ⟨p, hp⟩ : ∃ p, p ∉ F := by
    by_contra h; push Not at h
    have : F = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [this] at hF; simp at hF
  obtain ⟨k', hk', h⟩ := hfair p hp K
  have hh : (kk 2 2 2).Halted (r.cfg K) p := by
    rcases h with h | h
    · rw [hK k' hk'] at h; exact absurd h (by simp)
    · rwa [r.cfg_eq_of_stutter hK k' hk'] at h
  rw [halted_iff] at hh
  have hlog : (r.cfg K).log ≠ [] := fun hl => (noJob_inv (r.reachable K) hl p).1 hh
  obtain ⟨hI, -⟩ := inv_of_reachable (by norm_num) (r.reachable K)
  obtain ⟨⟨q, j⟩, he⟩ := List.exists_mem_of_ne_nil _ hlog
  have hj : j ∈ plog (r.cfg K) q := by
    unfold plog; exact List.mem_map.mpr ⟨(q, j), List.mem_filter.mpr ⟨he, by simp⟩, rfl⟩
  rw [hI.plogEq q, List.mem_append] at hj
  have hjJ : j ∈ Finset.Icc 1 2 := by
    rcases hj with hj | hj
    · exact hI.lineJ q j hj
    · unfold pend at hj; split_ifs at hj with hs
      · simp only [List.mem_singleton] at hj; subst hj
        exact hI.nxtJ q (by simp [hs]) (by simp [hs])
      · simp at hj
  have : j ∈ Alg.jobs 2 (r.cfg K) := by
    simp only [Alg.jobs, Finset.mem_filter]
    exact ⟨hjJ, List.mem_map.mpr ⟨(q, j), he, rfl⟩⟩
  have h1 : 1 ≤ Alg.Do 2 (r.cfg K) := Finset.card_pos.mpr ⟨j, this⟩
  exact h1.trans (r.do_cfg_le 2 K)

/-- **Theorem 4.4 is false for `n ≤ β + m − 2`**: for `m = n = β = 2` and `f = 1 = m − 1`, the
effectiveness of `KK_β` is `1`, while the paper's formula gives `n − (β + m − 2) = 0`. -/
theorem theorem_4_4_false_small :
    (kk 2 2 2).effectiveness 2 1 = 1 ∧ (kk 2 2 2).effectiveness 2 1 ≠ 2 - (2 + 2 - 2) := by
  have hle := kk_effectiveness_le (m := 2) (n := 2) (β := 2) (by norm_num) 1
  have hge : 1 ≤ (kk 2 2 2).effectiveness 2 1 := by
    apply le_csInf
    · exact ⟨_, Alg.advFinal (kk 2 2 2) 2 1 (by norm_num), Alg.advRun (kk 2 2 2) 2 1 (by norm_num),
        Alg.advFinal_card_le _ _ _ _, Alg.advRun_fair _ _ _ _, rfl⟩
    · rintro d ⟨F, r, hF, hfair, rfl⟩
      exact kk222_do_pos r F hF hfair
  have : (kk 2 2 2).effectiveness 2 1 = 1 := le_antisymm (by simpa using hle) hge
  exact ⟨this, by rw [this]; norm_num⟩

end Podc.AtMostOnceEffectiveness
