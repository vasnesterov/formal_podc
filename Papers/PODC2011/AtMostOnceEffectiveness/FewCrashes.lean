import Papers.PODC2011.AtMostOnceEffectiveness.Degenerate

/-!
# Theorem 4.4 fails for fewer than `m − 1` crashes

Theorem 4.4 claims `E_{KK_β}(n, m, f) = n − (β + m − 2)` for *every* `f ≤ m − 1`, but its matching
adversary crashes `m − 1` processes. With fewer crashes the value can be larger, also when
`n ≥ β + m − 1`. Smallest instance: `m = 2`, `β = 4`, `n = 5`, `f = 0`, where the formula gives
`1` but every fair crash-free run performs at least two jobs.

* Process `1` (paper id 2) always picks an element of rank `≥ 2` of a subset of `{1, …, 5}`, so it
  never announces or performs job `1` (`u1`). Hence process `0` (paper id 1), whose first target is
  job `1`, cannot fail its first `check` and cannot terminate before job `1` is performed
  (`invA`).
* As long as only job `1` has been performed, process `0` only announces jobs `1` or `2`, so
  process `1`, whose first target is job `3` (`kIdx 2 1 5 = 3`), cannot fail its first `check` and
  cannot terminate before it performs a job `≠ 1` (`invB`).
* By wait-freedom (Lemma 4.3) and fairness, both processes terminate, so both kinds of jobs are
  performed.

Exhaustive model checking (`kk_modelcheck.py`) gives further counterexamples, e.g.
`(n, m, β, f) = (9, 2, 6, 0)` (`E = 4` vs `3`) and `(8, 3, 6, 1)` (`E = 2` vs `1`).
-/

namespace Podc.AtMostOnceEffectiveness

namespace FewCrashes

open Function Finset

/-- Every job in the log of `KK_β` is one of `1, …, n`. -/
lemma log_mem_J {m n : ℕ} {C : Config m Reg ℕ LState} (hI : Inv m n C) {e : Fin m × ℕ}
    (he : e ∈ C.log) : e.2 ∈ Icc 1 n := by
  have hj : e.2 ∈ plog C e.1 := by
    unfold plog; exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, by simp⟩, rfl⟩
  rw [hI.plogEq, List.mem_append] at hj
  rcases hj with hj | hj
  · exact hI.lineJ _ _ hj
  · unfold pend at hj; split_ifs at hj with hs
    · simp only [List.mem_singleton] at hj; rw [hj]
      exact hI.nxtJ _ (by simp [hs]) (by simp [hs])
    · simp at hj

/-- A process in status `done` has performed its job `NEXT_p`. -/
lemma nxt_mem_log_of_done {m n : ℕ} {C : Config m Reg ℕ LState} (hI : Inv m n C) {p : Fin m}
    (h : (C.loc p).status = .done) : ∃ e ∈ C.log, e.2 = (C.loc p).nxt := by
  have hj : (C.loc p).nxt ∈ plog C p := by rw [hI.plogEq]; simp [pend, h]
  unfold plog at hj
  obtain ⟨e, he, hee⟩ := List.mem_map.mp hj
  exact ⟨e, (List.mem_filter.mp he).1, hee⟩

/-- `DONE_p` only contains performed jobs. -/
lemma doneS_mem_log {m n β : ℕ} (hβ : 1 ≤ β) {C : Config m Reg ℕ LState}
    (hC : (kk m n β).Reachable C) (p : Fin m) {x : ℕ} (hx : x ∈ (C.loc p).doneS) :
    ∃ e ∈ C.log, e.2 = x := by
  obtain ⟨hI, hI2⟩ := inv_of_reachable hβ hC
  have h := ((hI2.doneRec p).trans (recorded_subset_jobs hI)) hx
  simp only [Alg.jobs, mem_filter, List.mem_map] at h
  obtain ⟨-, e, he, rfl⟩ := h
  exact ⟨e, he, rfl⟩

/-- An element of rank `k ≥ 2` of a subset of `{1, …, n}` is not `1`. -/
lemma rank_ne_one {S : Finset ℕ} {n : ℕ} (hS : S ⊆ Icc 1 n) {k : ℕ} (hk : 2 ≤ k)
    (hkS : k ≤ S.card) : rank S k ≠ 1 := by
  intro h
  have hb := below_rank (S := S) (by omega) hkS
  rw [h] at hb
  have : below S 1 = 0 := by
    unfold below
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    have := mem_Icc.mp (hS hx)
    omega
  omega

/-- The element of rank `1` (the minimum) is not above an element of the set. -/
lemma rank_one_ne {S : Finset ℕ} {x y : ℕ} (hx : x ∈ S) (hxy : x < y) : rank S 1 ≠ y := by
  intro h
  have hb := below_rank (S := S) le_rfl (Finset.card_pos.mpr ⟨x, hx⟩)
  rw [h] at hb
  have : 0 < below S y := Finset.card_pos.mpr ⟨x, by simp [hx, hxy]⟩
  omega

lemma kIdx_zero (F : ℕ) : kIdx 2 0 F = 1 := by unfold kIdx; split_ifs <;> simp

/-- Process `1` never announces job `1`. -/
lemma u1 {C : Config 2 Reg ℕ LState} (hC : (kk 2 5 4).Reachable C) :
    (C.loc 1).nxt ≠ 1 ∧ C.mem (.next 1) ≠ 1 := by
  induction hC with
  | init => simp [Alg.init, kk, LState.init]
  | @step C C' q hC hs ih =>
    have hks := step_inv hs
    by_cases hq : q = 1
    · subst hq
      cases hks with
      | compNext h hb =>
        simp only [update_self]
        refine ⟨?_, ih.2⟩
        have hsub : free 5 (C.loc 1) \ (C.loc 1).tryS ⊆ Icc 1 5 :=
          sdiff_subset.trans sdiff_subset
        have hc1 : (free 5 (C.loc 1) \ (C.loc 1).tryS).card ≤ (free 5 (C.loc 1)).card :=
          card_le_card sdiff_subset
        have hc2 : (free 5 (C.loc 1)).card ≤ 5 := by
          have := card_le_card (show free 5 (C.loc 1) ⊆ Icc 1 5 from sdiff_subset)
          simpa using this
        apply rank_ne_one hsub
        · unfold kIdx; split_ifs <;> (simp; try omega)
        · unfold kIdx; split_ifs <;> simp <;> omega
      | setNext h => simp [update_self, ih.1]
      | finish h hb => simpa [update_self] using ih
      | tryRead h hq => simpa [update_self] using ih
      | trySkip h hq => simpa [update_self] using ih
      | doneRead h hq hpos hv => simpa [update_self] using ih
      | doneAdv h hq => simpa [update_self] using ih
      | checkOk h h1 h2 => simpa [update_self] using ih
      | checkFail h h1 => simpa [update_self] using ih
      | perform h => simpa [update_self] using ih
      | writeDone h => simpa [update_self] using ih
    · rw [hks.loc_ne (Ne.symm hq), hks.mem_next_ne 1 (fun e => hq (Fin.ext e.symm))]
      exact ih

/-- While job `1` has not been performed, process `0` is in its first iteration with target `1`. -/
def InvA (C : Config 2 Reg ℕ LState) : Prop :=
  (∀ e ∈ C.log, e.2 ≠ 1) →
    (C.loc 0).status ≠ .finished ∧
    ((C.loc 0).status = .compNext → (C.loc 0).tryS = ∅ ∧ (C.loc 0).doneS = ∅) ∧
    ((C.loc 0).status ≠ .compNext → (C.loc 0).nxt = 1) ∧
    1 ∉ (C.loc 0).tryS

lemma invA {C : Config 2 Reg ℕ LState} (hC : (kk 2 5 4).Reachable C) : InvA C := by
  induction hC with
  | init =>
    intro _
    simp [Alg.init, kk, LState.init]
  | @step C C' q hC hs ih =>
    intro hl
    obtain ⟨l, hl'⟩ := Alg.step_log hs
    have hl0 : ∀ e ∈ C.log, e.2 ≠ 1 := fun e he => hl e (by rw [hl']; exact List.mem_append_left _ he)
    obtain ⟨e1, e2, e3, e4⟩ := ih hl0
    obtain ⟨hI, -⟩ := inv_of_reachable (by norm_num) hC
    have hks := step_inv hs
    by_cases hq : q = 0
    · subst hq
      cases hks with
      | compNext h hb =>
        simp only [update_self]
        obtain ⟨ht, hd⟩ := e2 h
        have hfree : free 5 (C.loc 0) = Icc 1 5 := by rw [free, hd]; simp
        refine ⟨by simp, by simp, ?_, by simp⟩
        intro _
        simp only [ht, hfree, sdiff_empty]
        rw [show (Icc 1 5).card = 5 by simp]
        simp only [Fin.isValue, Fin.val_zero, kIdx_zero]
        exact Adversary.rank_Icc (by simp)
      | finish h hb =>
        exfalso; apply hb
        obtain ⟨ht, hd⟩ := e2 h
        rw [ht, free, hd]; simp
      | setNext h =>
        simp only [update_self]
        exact ⟨by simp, by simp, fun _ => e3 (by rw [h]; simp), e4⟩
      | tryRead h hq =>
        simp only [update_self, adv_status, adv_nxt, adv_tryS]
        refine ⟨by split_ifs <;> simp [h], by split_ifs <;> simp [h],
          fun _ => e3 (by rw [h]; simp), ?_⟩
        have hq1 : (C.loc 0).q = 1 := by
          have := hI.qlt 0 (Or.inl h); simp at hq; omega
        rw [hq1]
        have hu := (u1 hC).2
        unfold addTry
        split_ifs
        · simp only [mem_insert, not_or]; exact ⟨fun e => hu (by simpa using e.symm), e4⟩
        · exact e4
      | trySkip h hq =>
        simp only [update_self, adv_status, adv_nxt, adv_tryS]
        exact ⟨by split_ifs <;> simp [h], by split_ifs <;> simp [h], fun _ => e3 (by rw [h]; simp),
          e4⟩
      | doneRead h hq hpos hv =>
        simp only [update_self]
        exact ⟨by simp [h], by simp [h], fun _ => e3 (by rw [h]; simp), e4⟩
      | doneAdv h hq =>
        simp only [update_self, adv_status, adv_nxt, adv_tryS]
        exact ⟨by split_ifs <;> simp [h], by split_ifs <;> simp [h], fun _ => e3 (by rw [h]; simp),
          e4⟩
      | checkOk h h1 h2 =>
        simp only [update_self]
        exact ⟨by simp, by simp, fun _ => e3 (by rw [h]; simp), e4⟩
      | checkFail h h1 =>
        exfalso
        rw [e3 (by rw [h]; simp)] at h1
        rcases h1 with h1 | h1
        · exact e4 h1
        · obtain ⟨e, he, hee⟩ := doneS_mem_log (by norm_num) hC 0 h1
          exact hl0 e he hee
      | perform h =>
        exfalso
        exact hl (0, (C.loc 0).nxt) (by simp) (e3 (by rw [h]; simp))
      | writeDone h =>
        exfalso
        obtain ⟨e, he, hee⟩ := nxt_mem_log_of_done hI h
        exact hl0 e he (by rw [hee]; exact e3 (by rw [h]; simp))
    · rw [hks.loc_ne (Ne.symm hq)]
      exact ⟨e1, e2, e3, e4⟩

/-- While only job `1` has been performed, process `1` is in its first iteration with target
`3`, and process `0` never announces job `3`. -/
def InvB (C : Config 2 Reg ℕ LState) : Prop :=
  (∀ e ∈ C.log, e.2 = 1) →
    (C.loc 1).status ≠ .finished ∧
    ((C.loc 1).status = .compNext → (C.loc 1).tryS = ∅ ∧ (C.loc 1).doneS = ∅) ∧
    ((C.loc 1).status ≠ .compNext → (C.loc 1).nxt = 3) ∧
    (C.mem (.next 1) = 0 ∨ C.mem (.next 1) = 3) ∧
    3 ∉ (C.loc 1).tryS ∧
    (C.loc 0).nxt ≠ 3 ∧ C.mem (.next 0) ≠ 3 ∧ (C.loc 0).tryS ⊆ {3}

lemma invB {C : Config 2 Reg ℕ LState} (hC : (kk 2 5 4).Reachable C) : InvB C := by
  induction hC with
  | init =>
    intro _
    simp [Alg.init, kk, LState.init]
  | @step C C' q hC hs ih =>
    intro hl
    obtain ⟨l, hl'⟩ := Alg.step_log hs
    have hl0 : ∀ e ∈ C.log, e.2 = 1 := fun e he => hl e (by rw [hl']; exact List.mem_append_left _ he)
    obtain ⟨e1, e2, e3, e4, e5, f1, f2, f3⟩ := ih hl0
    obtain ⟨hI, -⟩ := inv_of_reachable (by norm_num) hC
    have hks := step_inv hs
    have hdone : ∀ p, (C.loc p).doneS ⊆ {1} := by
      intro p x hx
      obtain ⟨e, he, hee⟩ := doneS_mem_log (by norm_num) hC p hx
      rw [← hee, hl0 e he]; simp
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    by_cases hq : q = 1
    · subst hq
      have hf : C'.loc 0 = C.loc 0 := hks.loc_ne h01
      have hm : C'.mem (.next 0) = C.mem (.next 0) := hks.mem_next_ne _ (by simp)
      rw [hf, hm]
      cases hks with
      | compNext h hb =>
        simp only [update_self]
        obtain ⟨ht, hd⟩ := e2 h
        have hfree : free 5 (C.loc 1) = Icc 1 5 := by rw [free, hd]; simp
        refine ⟨by simp, by simp, ?_, e4, by simp, f1, f2, f3⟩
        intro _
        simp only [ht, hfree, sdiff_empty]
        rw [show (Icc 1 5).card = 5 by simp]
        rw [show kIdx 2 ((1 : Fin 2) : ℕ) 5 = 3 by decide]
        exact Adversary.rank_Icc (by simp)
      | finish h hb =>
        exfalso; apply hb
        obtain ⟨ht, hd⟩ := e2 h
        rw [ht, free, hd]; simp
      | setNext h =>
        simp only [update_self]
        refine ⟨by simp, by simp, fun _ => e3 (by rw [h]; simp), ?_, e5, f1, ?_, f3⟩
        · right; simp [e3 (by rw [h]; simp)]
        · simpa [update_of_ne] using f2
      | tryRead h hq =>
        simp only [update_self, adv_status, adv_nxt, adv_tryS]
        refine ⟨by split_ifs <;> simp [h], by split_ifs <;> simp [h],
          fun _ => e3 (by rw [h]; simp), e4, ?_, f1, f2, f3⟩
        have hq1 : (C.loc 1).q = 0 := by
          have := hI.qlt 1 (Or.inl h); simp at hq; omega
        rw [hq1]
        unfold addTry
        split_ifs
        · simp only [mem_insert, not_or]; exact ⟨fun e => f2 (by simpa using e.symm), e5⟩
        · exact e5
      | trySkip h hq =>
        simp only [update_self, adv_status, adv_nxt, adv_tryS]
        exact ⟨by split_ifs <;> simp [h], by split_ifs <;> simp [h], fun _ => e3 (by rw [h]; simp),
          e4, e5, f1, f2, f3⟩
      | doneRead h hq hpos hv =>
        simp only [update_self]
        exact ⟨by simp [h], by simp [h], fun _ => e3 (by rw [h]; simp), e4, e5, f1, f2, f3⟩
      | doneAdv h hq =>
        simp only [update_self, adv_status, adv_nxt, adv_tryS]
        exact ⟨by split_ifs <;> simp [h], by split_ifs <;> simp [h], fun _ => e3 (by rw [h]; simp),
          e4, e5, f1, f2, f3⟩
      | checkOk h h1 h2 =>
        simp only [update_self]
        exact ⟨by simp, by simp, fun _ => e3 (by rw [h]; simp), e4, e5, f1, f2, f3⟩
      | checkFail h h1 =>
        exfalso
        rw [e3 (by rw [h]; simp)] at h1
        rcases h1 with h1 | h1
        · exact e5 h1
        · have := hdone 1 h1; simp at this
      | perform h =>
        exfalso
        have := hl (1, (C.loc 1).nxt) (by simp)
        rw [e3 (by rw [h]; simp)] at this
        simp at this
      | writeDone h =>
        exfalso
        obtain ⟨e, he, hee⟩ := nxt_mem_log_of_done hI h
        have := hl0 e he
        rw [hee, e3 (by rw [h]; simp)] at this
        simp at this
    · have hq0 : q = 0 := by omega
      subst hq0
      have hf : C'.loc 1 = C.loc 1 := hks.loc_ne (Ne.symm h01)
      have hm : C'.mem (.next 1) = C.mem (.next 1) := hks.mem_next_ne _ (by simp)
      rw [hf, hm]
      refine ⟨e1, e2, e3, e4, e5, ?_⟩
      cases hks with
      | compNext h hb =>
        simp only [update_self]
        refine ⟨?_, f2, by simp⟩
        simp only [Fin.isValue, Fin.val_zero, kIdx_zero]
        apply rank_one_ne (x := 2) _ (by norm_num)
        simp only [mem_sdiff, free, mem_Icc]
        refine ⟨⟨by norm_num, fun h2 => ?_⟩, fun h2 => ?_⟩
        · have := hdone 0 h2; simp at this
        · have := f3 h2; simp at this
      | setNext h =>
        simp only [update_self]
        exact ⟨f1, by simpa using f1, f3⟩
      | tryRead h hq =>
        simp only [update_self, adv_nxt, adv_tryS]
        refine ⟨f1, by simpa [update_of_ne] using f2, ?_⟩
        have hq1 : (C.loc 0).q = 1 := by
          have := hI.qlt 0 (Or.inl h); simp at hq; omega
        rw [hq1]
        unfold addTry
        split_ifs with hv
        · apply insert_subset _ f3
          rcases e4 with e4 | e4
          · omega
          · simp [e4]
        · exact f3
      | finish h hb =>
        simp only [update_self]
        exact ⟨f1, by simpa [update_of_ne] using f2, f3⟩
      | trySkip h hq =>
        simp only [update_self, adv_nxt, adv_tryS]
        exact ⟨f1, by simpa [update_of_ne] using f2, f3⟩
      | doneRead h hq hpos hv =>
        simp only [update_self]
        exact ⟨f1, by simpa [update_of_ne] using f2, f3⟩
      | doneAdv h hq =>
        simp only [update_self, adv_nxt, adv_tryS]
        exact ⟨f1, by simpa [update_of_ne] using f2, f3⟩
      | checkOk h h1 h2 =>
        simp only [update_self]
        exact ⟨f1, by simpa [update_of_ne] using f2, f3⟩
      | checkFail h h1 =>
        simp only [update_self]
        exact ⟨f1, by simpa [update_of_ne] using f2, f3⟩
      | perform h =>
        simp only [update_self]
        exact ⟨f1, by simpa [update_of_ne] using f2, f3⟩
      | writeDone h =>
        simp only [update_self]
        exact ⟨f1, by simpa [update_of_ne] using f2, f3⟩

/-- In `KK_4` with `m = 2` and `n = 5`, every fair crash-free run performs at least two jobs. -/
theorem kk254_do_ge (r : (kk 2 5 4).Run) (F : Finset (Fin 2)) (hF : F.card ≤ 0)
    (hfair : r.Fair F) : 2 ≤ r.Do 5 := by
  obtain ⟨K, hK⟩ := lemma_4_3 (by norm_num) r
  have hF0 : F = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hF)
  have hhalt : ∀ p : Fin 2, ((r.cfg K).loc p).status = Status.finished := by
    intro p
    obtain ⟨k', hk', h⟩ := hfair p (by simp [hF0]) K
    have hh : (kk 2 5 4).Halted (r.cfg K) p := by
      rcases h with h | h
      · rw [hK k' hk'] at h; exact absurd h (by simp)
      · rwa [r.cfg_eq_of_stutter hK k' hk'] at h
    exact halted_iff.mp hh
  have hR := r.reachable K
  obtain ⟨hI, -⟩ := inv_of_reachable (by norm_num) hR
  -- job `1` is performed
  have h1 : ∃ e ∈ (r.cfg K).log, e.2 = 1 := by
    by_contra hc; push Not at hc
    exact (invA hR hc).1 (hhalt 0)
  -- some job `≠ 1` is performed
  have h2 : ∃ e ∈ (r.cfg K).log, e.2 ≠ 1 := by
    by_contra hc; push Not at hc
    exact (invB hR hc).1 (hhalt 1)
  obtain ⟨a, ha, ha1⟩ := h1
  obtain ⟨b, hb, hb1⟩ := h2
  have hmem : ∀ e ∈ (r.cfg K).log, e.2 ∈ Alg.jobs 5 (r.cfg K) := fun e he =>
    Finset.mem_filter.mpr ⟨log_mem_J hI he, List.mem_map.mpr ⟨e, he, rfl⟩⟩
  have hsub : ({a.2, b.2} : Finset ℕ) ⊆ Alg.jobs 5 (r.cfg K) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hmem a ha
    · exact hmem b hb
  have hcard : 2 ≤ Alg.Do 5 (r.cfg K) := by
    have := card_le_card hsub
    rw [card_pair (by rw [ha1]; exact Ne.symm hb1)] at this
    exact this
  exact hcard.trans (r.do_cfg_le 5 K)

end FewCrashes

open FewCrashes in
/-- **Theorem 4.4 is false for `f < m − 1` crashes**, also when `n ≥ β + m − 1`: for `m = 2`,
`β = 4 ≥ m`, `n = 5 = β + m − 1` and `f = 0 ≤ m − 1`, the paper's value is
`n − (β + m − 2) = 1`, but `E_{KK_4}(5, 2, 0) ≥ 2`. -/
theorem theorem_4_4_false_few_crashes :
    2 ≤ (kk 2 5 4).effectiveness 5 0 ∧ (kk 2 5 4).effectiveness 5 0 ≠ 5 - (4 + 2 - 2) := by
  have hge : 2 ≤ (kk 2 5 4).effectiveness 5 0 := by
    apply le_csInf
    · exact ⟨_, Alg.advFinal (kk 2 5 4) 5 0 (by norm_num), Alg.advRun (kk 2 5 4) 5 0 (by norm_num),
        Alg.advFinal_card_le _ _ _ _, Alg.advRun_fair _ _ _ _, rfl⟩
    · rintro d ⟨F, r, hF, hfair, rfl⟩
      exact kk254_do_ge r F hF hfair
  exact ⟨hge, by omega⟩

end Podc.AtMostOnceEffectiveness
