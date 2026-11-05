import Papers.PODC2014.DistributedUniversality.InvD

/-! # Preservation of `InvD` -/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

theorem not_mem_nextProp {M : Mode} {lastOp : Fin n → Fin k → Option ℕ} {i : Fin n} {y : Fin k}
    {hh : List (Op n)} {c : ℕ} (hc : (i, c) ∉ hh) : nextProp M lastOp i y hh c ∉ hh := by
  unfold nextProp
  split_ifs
  · dsimp only
    split
    · split_ifs with h1
      · exact hc
      · exact h1
    · exact hc
  · exact hc

section Fields
variable (I : InvA M s) (B : InvB M s) (C : InvC M s) (D : InvD M s) (hM : M.Good)
  (h : stepFn M s a = some s')
include I B C D hM h

theorem InvD.my_nin_step : ∀ i x, pastLoc (s'.loc i).pc → ¬ pastUpd (s'.loc i).pc x →
    (i, (s'.loc i).cnt x) ∉ (s'.loc i).hist x := by
  intro i y hl hu
  by_cases hi : i = a.proc
  · subst hi
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hl hu ⊢
    all_goals first
      | (simp at hl; done)
      | (revert hl; simp [startPC]; split_ifs <;> simp; done)
      | (split_ifs at hl <;> simp at hl; done)
      | (unfold afterN1 at hl; split_ifs at hl <;> simp at hl; done)
      | skip
    · -- loc
      split_ifs with hd
      · have hfresh : s.invAt a.proc y ((s.loc a.proc).cnt y + 1) = none := by
          cases hh : s.invAt a.proc y ((s.loc a.proc).cnt y + 1) with
          | none => rfl
          | some t => have := C.inv_cnt _ _ _ _ hh; omega
        intro hm
        rcases mem_merge hm with h1 | ⟨q, h1⟩
        · exact C.not_mem_hist_of_fresh hfresh _ h1
        · exact C.not_mem_hist_of_fresh hfresh q (((B.gs_gst _ q y).trans (B.gst_hist q y)).subset h1)
      · exact hd
    all_goals
      rw [pastUpd_updPC hm] at hu
      have hne : y ≠ ⟨m, hm⟩ := fun e => by subst e; simp at hu
      try simp only [Function.update_of_ne hne]
      exact D.my_nin _ y (by simp [hpc]) (by simp [hpc]; omega)
  · rw [loc_ne h hi] at hl hu ⊢
    exact D.my_nin i y hl hu

theorem InvD.oper_nin_step : ∀ i x, pastUpd (s'.loc i).pc x →
    (s'.loc i).oper x ∉ (s'.loc i).hist x := by
  intro i y hu
  by_cases hi : i = a.proc
  · subst hi
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hu ⊢
    all_goals first
      | (simp at hu; done)
      | (revert hu; simp [startPC]; split_ifs <;> simp; done)
      | (split_ifs at hu <;> simp at hu; done)
      | (split_ifs at hu <;> simp [afterN1] at hu <;> (try split_ifs at hu) <;> simp at hu; done)
      | (split_ifs at hu with hk
         · simp at hu
         · exact absurd y.isLt (by omega))
      | skip
    all_goals
      rw [pastUpd_updPC hm] at hu
      by_cases hy : y = ⟨m, hm⟩
      · subst hy
        simp only [Function.update_self]
        first
        | exact not_mem_nextProp (D.my_nin _ _ (by simp [hpc]) (by simp [hpc]))
        | (apply not_mem_nextProp
           have hfresh : s.invAt a.proc ⟨m, hm⟩ ((s.loc a.proc).cnt ⟨m, hm⟩ + 1) = none := by
             cases hh : s.invAt a.proc ⟨m, hm⟩ ((s.loc a.proc).cnt ⟨m, hm⟩ + 1) with
             | none => rfl
             | some t => have := C.inv_cnt _ _ _ _ hh; omega
           intro hm'
           simp only [List.mem_append, List.mem_singleton] at hm'
           rcases hm' with hm' | hm'
           · exact C.not_mem_hist_of_fresh hfresh _ hm'
           · rw [hmine] at hm'; simp at hm')
        | (apply not_mem_nextProp
           intro hm'
           simp only [List.mem_append, List.mem_singleton] at hm'
           rcases hm' with hm' | hm'
           · exact D.my_nin _ _ (by simp [hpc]) (by simp [hpc]) hm'
           · exact hmine hm'.symm)
        | exact hnin
      · have hy' : y.val < m := by
          have : y.val ≠ m := fun e => hy (Fin.ext e)
          omega
        simp only [Function.update_of_ne hy]
        exact D.oper_nin _ y (by simp [hpc, hy'])
  · rw [loc_ne h hi] at hu ⊢
    exact D.oper_nin i y hu

theorem retAt_mono : ∀ i x c, s.retAt i x c ≠ none → s'.retAt i x c ≠ none := by
  intro i y c hc
  du_step_cases h <;> simp only [tInit_retAt, tN1Inv_retAt, tN1Resp_retAt, tScInv_retAt, tScResp_retAt, tAcInv_retAt, tAcResp_retAt, tCollect_retAt, tLoc_retAt, tUpdIn_retAt, tUpdMine_retAt, tUpdOther_retAt, tUpdAdopt_retAt, tWrite_retAt] <;> first | exact hc | (split_ifs <;> simp [hc])

theorem InvD.res_cnt_step : ∀ i x c, (x, c) ∈ (s'.loc i).res →
    c + 1 = (s'.loc i).cnt x ∧ pastUpd (s'.loc i).pc x := by
  intro i y c hr
  by_cases hi : i = a.proc
  · subst hi
    have hbad : ¬ pastUpd (s.loc a.proc).pc y → (y, c) ∉ (s.loc a.proc).res :=
      fun hn hr' => hn (D.res_cnt _ y c hr').2
    have hupd : ∀ mm (hmm : mm < k), (s.loc a.proc).pc = .upd mm → (y, c) ∈ (s.loc a.proc).res →
        c + 1 = (s.loc a.proc).cnt y ∧ pastUpd (updPC (k := k) mm) y := by
      intro mm hmm hpc' hr'
      obtain ⟨h1, h2⟩ := D.res_cnt _ y c hr'
      simp only [hpc', pastUpd_upd] at h2
      exact ⟨h1, by rw [pastUpd_updPC hmm]; omega⟩
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hr ⊢
    · exact absurd hr (hbad (by simp [hpc]))
    · exact absurd hr (hbad (by simp [hpc]))
    · exact absurd hr (hbad (by simp [hpc]))
    · exact absurd hr (hbad (by simp [hpc]))
    · exact absurd hr (hbad (by simp [hpc]))
    · exact absurd hr (hbad (by simp [hpc]))
    · exact absurd hr (hbad (by simp [hpc]))
    · exact absurd hr (hbad (by simp [hpc]))
    · exact absurd hr (hbad (by simp [hpc]))
    · exact hupd m hm hpc hr
    · simp only [List.mem_cons, Prod.mk.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩ | hr
      · exact ⟨by simp, by rw [pastUpd_updPC hm]⟩
      · obtain ⟨h1, h2⟩ := hupd m hm hpc hr
        have h3 := (D.res_cnt _ y c hr).2
        simp only [hpc, pastUpd_upd] at h3
        have hne : y ≠ ⟨m, hm⟩ := fun e => by subst e; simp at h3
        exact ⟨by simp [Function.update_of_ne hne, h1], h2⟩
    · exact hupd m hm hpc hr
    · exact hupd m hm hpc hr
    · simp at hr
  · rw [loc_ne h hi] at hr ⊢
    exact D.res_cnt i y c hr

theorem InvD.ret_cnt_step : ∀ i x c, c < (s'.loc i).cnt x →
    s'.retAt i x c ≠ none ∨ (x, c) ∈ (s'.loc i).res := by
  intro i y c hc
  have hrm := retAt_mono I B C D hM h
  have hgen : c < (s.loc i).cnt y → (s'.loc i).res = (s.loc i).res →
      s'.retAt i y c ≠ none ∨ (y, c) ∈ (s'.loc i).res := by
    intro hc' hres
    rw [hres]
    rcases D.ret_cnt i y c hc' with h1 | h1
    · exact Or.inl (hrm _ _ _ h1)
    · exact Or.inr h1
  by_cases hi : i = a.proc
  · subst hi
    have hnores : (s.loc a.proc).pc = .loc → ∀ c', (y, c') ∉ (s.loc a.proc).res := by
      intro hpc c' hr; have := (D.res_cnt _ y c' hr).2; simp [hpc] at this
    du_step_cases h
    · simp at hc
    · exact hgen (by simpa using hc) (by simp)
    · exact hgen (by simpa using hc) (by simp)
    · exact hgen (by simpa using hc) (by simp)
    · exact hgen (by simpa using hc) (by simp)
    · exact hgen (by simpa using hc) (by simp)
    · exact hgen (by simpa using hc) (by simp)
    · exact hgen (by simpa using hc) (by simp)
    · -- loc
      simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hc ⊢
      split_ifs at hc with hd
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
        · rcases D.ret_cnt _ y c hc with h1 | h1
          · exact Or.inl (hrm _ _ _ h1)
          · exact absurd h1 (hnores hpc c)
        · left; simp [hd]
      · rcases D.ret_cnt _ y c hc with h1 | h1
        · exact Or.inl (hrm _ _ _ h1)
        · exact absurd h1 (hnores hpc c)
    · exact hgen (by simpa using hc) (by simp)
    · -- upd mine
      simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hc ⊢
      by_cases hy : y = ⟨m, hm⟩
      · subst hy
        simp only [Function.update_self] at hc
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
        · rcases D.ret_cnt _ _ c hc with h1 | h1
          · exact Or.inl (hrm _ _ _ h1)
          · exact Or.inr (List.mem_cons_of_mem _ h1)
        · right; simp
      · simp only [Function.update_of_ne hy] at hc
        rcases D.ret_cnt _ y c hc with h1 | h1
        · exact Or.inl (hrm _ _ _ h1)
        · exact Or.inr (List.mem_cons_of_mem _ h1)
    · exact hgen (by simpa using hc) (by simp)
    · exact hgen (by simpa using hc) (by simp)
    · -- write
      simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hc ⊢
      rcases D.ret_cnt _ y c hc with h1 | h1
      · exact Or.inl (hrm _ _ _ h1)
      · left; simp [h1]
  · rw [loc_ne h hi] at hc
    exact hgen hc (by rw [loc_ne h hi])

theorem InvD.last_cnt_step : ∀ i x, (s'.loc i).pc ≠ .init →
    s'.lastOp i x = some ((s'.loc i).cnt x) := by
  intro i y hni
  by_cases hi : i = a.proc
  · subst hi
    have hgen : (s'.lastOp a.proc y = s.lastOp a.proc y) →
        (s'.loc a.proc).cnt y = (s.loc a.proc).cnt y → (s.loc a.proc).pc ≠ .init →
        s'.lastOp a.proc y = some ((s'.loc a.proc).cnt y) := by
      intro h1 h2 h3; rw [h1, h2]; exact D.last_cnt _ y h3
    du_step_cases h
    · simp
    · exact hgen (by simp) (by simp) (by simp [hpc])
    · exact hgen (by simp) (by simp) (by simp [hpc])
    · exact hgen (by simp) (by simp) (by simp [hpc])
    · exact hgen (by simp) (by simp) (by simp [hpc])
    · exact hgen (by simp) (by simp) (by simp [hpc])
    · exact hgen (by simp) (by simp) (by simp [hpc])
    · exact hgen (by simp) (by simp) (by simp [hpc])
    · simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, tInit_lastOp, tN1Inv_lastOp, tN1Resp_lastOp, tScInv_lastOp, tScResp_lastOp, tAcInv_lastOp, tAcResp_lastOp, tCollect_lastOp, tLoc_lastOp, tUpdIn_lastOp, tUpdMine_lastOp, tUpdOther_lastOp, tUpdAdopt_lastOp, tWrite_lastOp, Function.update_self]
      by_cases hd : (a.proc, (s.loc a.proc).cnt y) ∈ mergedHist s a.proc y
      · simp [hd]
      · simp only [hd, and_false, ↓reduceIte]; exact D.last_cnt _ y (by simp [hpc])
    · exact hgen (by simp) (by simp) (by simp [hpc])
    · simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, tInit_lastOp, tN1Inv_lastOp, tN1Resp_lastOp, tScInv_lastOp, tScResp_lastOp, tAcInv_lastOp, tAcResp_lastOp, tCollect_lastOp, tLoc_lastOp, tUpdIn_lastOp, tUpdMine_lastOp, tUpdOther_lastOp, tUpdAdopt_lastOp, tWrite_lastOp, Function.update_self]
      by_cases hy : y = ⟨m, hm⟩
      · subst hy; simp
      · simp only [hy, and_false, ↓reduceIte, Function.update_of_ne hy]
        exact D.last_cnt _ y (by simp [hpc])
    · exact hgen (by simp) (by simp) (by simp [hpc])
    · exact hgen (by simp) (by simp) (by simp [hpc])
    · exact hgen (by simp) (by simp) (by simp [hpc])
  · rw [loc_ne h hi] at hni ⊢
    have : s'.lastOp i y = s.lastOp i y := by
      du_step_cases h <;> simp only [tInit_lastOp, tN1Inv_lastOp, tN1Resp_lastOp, tScInv_lastOp, tScResp_lastOp, tAcInv_lastOp, tAcResp_lastOp, tCollect_lastOp, tLoc_lastOp, tUpdIn_lastOp, tUpdMine_lastOp, tUpdOther_lastOp, tUpdAdopt_lastOp, tWrite_lastOp] <;> simp [hi]
    rw [this]; exact D.last_cnt i y hni

theorem InvD.step : InvD M s' where
  my_nin := InvD.my_nin_step I B C D hM h
  oper_nin := InvD.oper_nin_step I B C D hM h
  res_cnt := InvD.res_cnt_step I B C D hM h
  ret_cnt := InvD.ret_cnt_step I B C D hM h
  last_cnt := InvD.last_cnt_step I B C D hM h

end Fields

/-- The full invariant of reachable states. -/
structure Inv (M : Mode) (s : St n k) : Prop where
  A : InvA M s
  B : InvB M s
  C : InvC M s
  D : InvD M s

theorem Reachable.invAll (hM : M.Good) (hs : Reachable M s) : Inv M s := by
  induction hs with
  | refl => exact ⟨invA_init M, invB_init M, invC_init M, invD_init M⟩
  | tail _ hst ih =>
    obtain ⟨a, ha⟩ := hst
    obtain ⟨I, B, C, D⟩ := ih
    exact ⟨I.step ha, B.step I hM ha, C.step I B hM ha, D.step I B C hM ha⟩

end Podc.DistributedUniversality
