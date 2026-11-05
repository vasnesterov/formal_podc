import Papers.PODC2014.DistributedUniversality.InvC

/-! # Preservation of `InvC` -/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

theorem InvC.IV_of_acR (I : InvA M s) (C : InvC M s) {r b y j t w}
    (h1 : s.acR r b y j = some (t, w)) : IV s y w := by
  obtain ⟨-, -, ⟨j', hj'⟩, -⟩ := I.acR_inv _ _ _ _ _ _ h1
  exact C.v_acI _ _ _ _ _ hj'

theorem InvC.IV_acop (I : InvA M s) (C : InvC M s) {i : Fin n} (hpa : pastAC (s.loc i).pc)
    (y : Fin k) : IV s y ((s.loc i).acop y) := by
  have hf := I.finR_loc i hpa y
  rcases I.finR_src _ _ _ _ hf with h1 | ⟨-, h1⟩ <;> exact C.IV_of_acR I h1

theorem IV_nextProp {s : St n k} {M : Mode} {lastOp : Fin n → Fin k → Option ℕ} {i : Fin n}
    {y : Fin k} {hh : List (Op n)} {c : ℕ}
    (hl : ∀ j c', lastOp j y = some c' → IV s y (j, c')) (hc : IV s y (i, c)) :
    IV s y (nextProp M lastOp i y hh c) := by
  unfold nextProp
  split_ifs
  · dsimp only
    split
    · split_ifs
      · exact hc
      · exact hl _ _ ‹_›
    · exact hc
  · exact hc

section Fields
variable (I : InvA M s) (B : InvB M s) (C : InvC M s) (hM : M.Good) (h : stepFn M s a = some s')
include I B C hM h

theorem InvC.invAt_mono : ∀ i m c t, s.invAt i m c = some t → s'.invAt i m c = some t := by
  intro i y c t ht
  du_step_cases h <;> simp only [tInit_invAt, tN1Inv_invAt, tN1Resp_invAt, tScInv_invAt,
    tScResp_invAt, tAcInv_invAt, tAcResp_invAt, tCollect_invAt, tLoc_invAt, tUpdIn_invAt,
    tUpdMine_invAt, tUpdOther_invAt, tUpdAdopt_invAt, tWrite_invAt, ht]
  · split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      rw [C.inv_init _ _ _ hpc] at ht; simp at ht
    · rfl
  · split_ifs with hc
    · obtain ⟨rfl, -, rfl⟩ := hc
      have := C.inv_cnt _ _ _ _ ht; omega
    · rfl
  · split_ifs with hc
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      have := C.inv_cnt _ _ _ _ ht; omega
    · rfl

theorem InvC.IV_mono {m : Fin k} {o : Op n} (hv : IV s m o) : IV s' m o := by
  obtain ⟨t, ht⟩ := hv; exact ⟨t, InvC.invAt_mono I B C hM h _ _ _ _ ht⟩

theorem InvC.invAt_new {i m c t} (ht : s'.invAt i m c = some t) (hold : s.invAt i m c ≠ some t) :
    t = s.time ∧ i = a.proc ∧ c = (s'.loc a.proc).cnt m := by
  du_step_cases h <;> simp only [tInit_invAt, tN1Inv_invAt, tN1Resp_invAt, tScInv_invAt, tScResp_invAt, tAcInv_invAt, tAcResp_invAt, tCollect_invAt, tLoc_invAt, tUpdIn_invAt, tUpdMine_invAt, tUpdOther_invAt, tUpdAdopt_invAt, tWrite_invAt] at ht <;> try exact absurd ht hold
  all_goals
    split_ifs at ht with hc
    · simp only [Option.some.injEq] at ht
      first
      | (obtain ⟨rfl, rfl⟩ := hc; exact ⟨ht.symm, rfl, by simp⟩)
      | (obtain ⟨rfl, hd, rfl⟩ := hc; exact ⟨ht.symm, rfl, by simp [hd]⟩)
      | (obtain ⟨rfl, rfl, rfl⟩ := hc; exact ⟨ht.symm, rfl, by simp⟩)
    · exact absurd ht hold

theorem InvC.time_inv_step : ∀ i m c t, s'.invAt i m c = some t → t < s'.time := by
  intro i y c t ht
  have htime : s'.time = s.time + 1 := by du_step_cases h <;> rfl
  rw [htime]
  by_cases hold : s.invAt i y c = some t
  · have := C.time_inv _ _ _ _ hold; omega
  · have := (InvC.invAt_new I B C hM h ht hold).1; omega

theorem InvC.cnt_mono (i : Fin n) (y : Fin k) (hni : (s.loc i).pc ≠ .init) :
    (s.loc i).cnt y ≤ (s'.loc i).cnt y := by
  by_cases hi : i = a.proc
  · subst hi
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] <;> try exact le_rfl
    · exact absurd hpc hni
    · split_ifs <;> omega
    · by_cases hy : y = ⟨m, hm⟩
      · subst hy; simp
      · simp [Function.update_of_ne hy]
  · rw [loc_ne h hi]

theorem InvC.inv_cnt_step : ∀ i m c t, s'.invAt i m c = some t → c ≤ (s'.loc i).cnt m := by
  intro i y c t ht
  by_cases hold : s.invAt i y c = some t
  · have h1 := C.inv_cnt _ _ _ _ hold
    have hni : (s.loc i).pc ≠ .init := fun e => by rw [C.inv_init _ _ _ e] at hold; simp at hold
    exact h1.trans (InvC.cnt_mono I B C hM h i y hni)
  · obtain ⟨-, rfl, rfl⟩ := InvC.invAt_new I B C hM h ht hold
    exact le_rfl

theorem InvC.inv_init_step : ∀ i m c, (s'.loc i).pc = .init → s'.invAt i m c = none := by
  intro i y c hpc'
  by_cases hi : i = a.proc
  · subst hi
    exfalso
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hpc' <;>
      first
      | (simp [startPC] at hpc'; split_ifs at hpc' <;> simp at hpc'; done)
      | (simp at hpc'; done)
      | (unfold updPC at hpc'; split_ifs at hpc' <;> simp at hpc'; done)
      | (split_ifs at hpc' <;> simp [afterN1] at hpc' <;> (try split_ifs at hpc') <;>
          simp at hpc')
  · rw [loc_ne h hi] at hpc'
    have hpre := C.inv_init i y c hpc'
    cases ht : s'.invAt i y c with
    | none => rfl
    | some t =>
      have := (InvC.invAt_new I B C hM h ht (by rw [hpre]; simp)).2.1
      exact absurd this hi

theorem InvC.v_lastOp_step : ∀ j m c, s'.lastOp j m = some c → IV s' m (j, c) := by
  intro j y c hc
  by_cases hold : s.lastOp j y = some c
  · exact InvC.IV_mono I B C hM h (C.v_lastOp _ _ _ hold)
  · du_step_cases h <;> simp only [tInit_lastOp, tN1Inv_lastOp, tN1Resp_lastOp, tScInv_lastOp,
      tScResp_lastOp, tAcInv_lastOp, tAcResp_lastOp, tCollect_lastOp, tLoc_lastOp,
      tUpdIn_lastOp, tUpdMine_lastOp, tUpdOther_lastOp, tUpdAdopt_lastOp, tWrite_lastOp] at hc ⊢ <;>
      try exact absurd hc hold
    all_goals
      split_ifs at hc with hcc
      · simp only [Option.some.injEq] at hc
        subst hc
        first
        | (obtain rfl := hcc; exact ⟨s.time, by simp⟩)
        | (obtain ⟨rfl, hd⟩ := hcc; exact ⟨s.time, by simp [hd]⟩)
        | (obtain ⟨rfl, rfl⟩ := hcc; exact ⟨s.time, by simp⟩)
      · exact absurd hc hold

theorem InvC.v_loc_step : ∀ i m, (s'.loc i).pc ≠ .init →
    IV s' m ((s'.loc i).oper m) ∧ IV s' m (i, (s'.loc i).cnt m) := by
  intro i y hni
  have hmono := fun {m o} => @InvC.IV_mono _ _ _ _ _ _ I B C hM h m o
  by_cases hi : i = a.proc
  · subst hi
    have hlast := InvC.v_lastOp_step I B C hM h
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hni ⊢
    · exact ⟨⟨s.time, by simp⟩, ⟨s.time, by simp⟩⟩
    all_goals first
      | exact ⟨hmono (C.v_loc _ y (by simp [hpc])).1, hmono (C.v_loc _ y (by simp [hpc])).2⟩
      | skip
    · -- loc
      refine ⟨hmono (C.v_loc _ y (by simp [hpc])).1, ?_⟩
      split_ifs with hd
      · exact ⟨s.time, by simp [hd]⟩
      · exact hmono (C.v_loc _ y (by simp [hpc])).2
    all_goals
      have hpre := C.v_loc a.proc y (by simp [hpc])
      by_cases hy : y = ⟨m, hm⟩
      · subst hy
        simp only [Function.update_self]
        first
        | exact ⟨IV_nextProp (fun j c hc => hlast j _ c (by simpa using hc)) (hmono hpre.2),
            hmono hpre.2⟩
        | exact ⟨IV_nextProp (fun j c hc => hlast j _ c (by simpa using hc)) ⟨s.time, by simp⟩,
            ⟨s.time, by simp⟩⟩
        | exact ⟨hmono (C.IV_acop I (by simp [hpc]) _), hmono hpre.2⟩
      · simp only [Function.update_of_ne hy]
        exact ⟨hmono hpre.1, hmono hpre.2⟩
  · rw [loc_ne h hi] at hni ⊢
    exact ⟨hmono (C.v_loc i y hni).1, hmono (C.v_loc i y hni).2⟩

theorem InvC.v_acI_step : ∀ r b y j w, s'.acI r b y j = some w → IV s' y w := by
  intro r b y j w hw
  have hmono := fun {m o} => @InvC.IV_mono _ _ _ _ _ _ I B C hM h m o
  by_cases hold : s.acI r b y j = some w
  · exact hmono (C.v_acI _ _ _ _ _ hold)
  · obtain ⟨rfl, rfl, hc⟩ := I.acI_new h hw hold
    rcases hc with ⟨-, m, hpc, -, rfl⟩ | ⟨-, jj, hpc, hy, rfl⟩
    · exact hmono (C.v_loc _ y (by simp [hpc])).1
    · refine hmono ?_
      obtain ⟨hscR, hord, -, hyy⟩ := I.ph1_loc a.proc jj (Or.inl hpc)
      have hxn := not_mem_take_of_getElem? (hord ▸ ordOf_nodup _) hy
      unfold acVal
      cases hd : (s.loc a.proc).scd y with
      | some v =>
        obtain ⟨j', u, hu, huy⟩ := I.scR_valid _ _ _ _ _ hscR hd
        simpa [huy] using C.v_scI _ _ _ y hu
      | none =>
        simp only [Option.getD_none]
        split_ifs with hc
        · exact C.IV_of_acR I (((hyy y).2.1 hxn).2 hc.1)
        · exact (C.v_loc _ y (by simp [hpc])).1

theorem InvC.v_scI_step : ∀ r j u y, s'.scI r j = some u → IV s' y (u y) := by
  intro r j u y hu
  have hmono := fun {m o} => @InvC.IV_mono _ _ _ _ _ _ I B C hM h m o
  by_cases hold : s.scI r j = some u
  · exact hmono (C.v_scI _ _ _ y hold)
  · obtain ⟨rfl, rfl, hpc, rfl⟩ := I.scI_new h hu hold
    refine hmono ?_
    split_ifs with hc
    · exact C.IV_of_acR I (I.sc_loc _ (Or.inl hpc) hc y)
    · exact (C.v_loc _ y (by simp [hpc])).1

theorem InvC.v_opRec_step : ∀ r m j w, s'.opRec r m j = some w → IV s' m w := by
  intro r y j w hw
  have hmono := fun {m o} => @InvC.IV_mono _ _ _ _ _ _ I B C hM h m o
  by_cases hold : s.opRec r y j = some w
  · exact hmono (C.v_opRec _ _ _ _ hold)
  · obtain ⟨rfl, hc⟩ := I.opRec_new h hw hold
    rcases hc with ⟨hpc, -, rfl⟩ | ⟨hpc, -, rfl⟩
    · refine ⟨s.time, ?_⟩
      du_step_cases h <;> simp only [hpc, reduceCtorEq] at * <;> simp
    · exact hmono (C.v_loc _ y (by simp [hpc])).1

theorem InvC.v_hist_step : ∀ i m o, o ∈ (s'.loc i).hist m → IV s' m o := by
  intro i y o ho
  have hmono := fun {m o} => @InvC.IV_mono _ _ _ _ _ _ I B C hM h m o
  by_cases hi : i = a.proc
  · subst hi
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at ho <;>
      first
      | exact hmono (C.v_hist _ y o ho)
      | skip
    · -- loc: merged history
      rcases mem_merge ho with h1 | ⟨q, h1⟩
      · exact hmono (C.v_hist _ y o h1)
      · exact hmono (C.v_hist q y o (((B.gs_gst _ q y).trans (B.gst_hist q y)).subset h1))
    all_goals
      by_cases hy : y = ⟨m, hm⟩
      · subst hy
        simp only [Function.update_self, List.mem_append, List.mem_singleton] at ho
        rcases ho with ho | rfl
        · exact hmono (C.v_hist _ _ o ho)
        · exact hmono (C.IV_acop I (by simp [hpc]) _)
      · simp only [Function.update_of_ne hy] at ho
        exact hmono (C.v_hist _ y o ho)
  · rw [loc_ne h hi] at ho
    exact hmono (C.v_hist i y o ho)

theorem InvC.v_G_step : ∀ m o, o ∈ s'.G m → IV s' m o := by
  intro y o ho
  have hmono := fun {m o} => @InvC.IV_mono _ _ _ _ _ _ I B C hM h m o
  rcases GB_cases h y with ⟨h1, -⟩ | ⟨mm, hpc, -, -, -, -, h1, -⟩
  · rw [h1] at ho; exact hmono (C.v_G y o ho)
  · rw [h1] at ho
    simp only [List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact hmono (C.v_G y o ho)
    · exact hmono (C.IV_acop I (by simp [hpc]) _)

theorem InvC.lin_mono : ∀ m o t, s.lin m o = some t → s'.lin m o = some t := by
  intro y o t ht
  du_step_cases h <;> simp only [tInit_lin, tN1Inv_lin, tN1Resp_lin, tScInv_lin, tScResp_lin, tAcInv_lin, tAcResp_lin, tCollect_lin, tLoc_lin, tUpdIn_lin, tUpdMine_lin, tUpdOther_lin, tUpdAdopt_lin, tWrite_lin, ht]
  all_goals simp

theorem InvC.lin_new {m o t} (ht : s'.lin m o = some t) (hold : s.lin m o ≠ some t) :
    (s.loc a.proc).pc = .write ∧ s.lin m o = none ∧ o ∈ (s.loc a.proc).hist m ∧ t = s.time ∧
      s'.gst a.proc = (s.loc a.proc).hist ∧ s'.G = s.G := by
  du_step_cases h <;> simp only [tInit_lin, tN1Inv_lin, tN1Resp_lin, tScInv_lin, tScResp_lin, tAcInv_lin, tAcResp_lin, tCollect_lin, tLoc_lin, tUpdIn_lin, tUpdMine_lin, tUpdOther_lin, tUpdAdopt_lin, tWrite_lin] at ht <;> try exact absurd ht hold
  split_ifs at ht with hc
  · simp only [Option.some.injEq] at ht
    refine ⟨hpc, by simpa using hc.1, hc.2, ht.symm, by funext z; simp, rfl⟩
  · exact absurd ht hold

theorem InvC.lin_gst_step : ∀ q m o, o ∈ s'.gst q m → ∃ t, s'.lin m o = some t := by
  intro q y o ho
  have hlm := InvC.lin_mono I B C hM h
  by_cases hw : (s.loc a.proc).pc = .write ∧ q = a.proc
  · obtain ⟨hpc, rfl⟩ := hw
    have hg : s'.gst a.proc y = (s.loc a.proc).hist y := by
      du_step_cases h <;> simp only [hpc, reduceCtorEq] at * <;> simp
    rw [hg] at ho
    cases hl : s.lin y o with
    | some t => exact ⟨t, hlm _ _ _ hl⟩
    | none =>
      refine ⟨s.time, ?_⟩
      du_step_cases h <;> simp only [hpc, reduceCtorEq] at *
      simp [hl, ho]
  · have hg : s'.gst q y = s.gst q y := by
      du_step_cases h <;> try rfl
      simp only [tWrite_gst]
      by_cases hq : q = a.proc
      · exact absurd ⟨hpc, hq⟩ hw
      · simp [Function.update_of_ne hq]
    rw [hg] at ho
    obtain ⟨t, ht⟩ := C.lin_gst q y o ho
    exact ⟨t, hlm _ _ _ ht⟩

theorem InvC.lin_inv_step : ∀ m o t, s'.lin m o = some t → t < s'.time ∧
    ∃ ti, s'.invAt o.1 m o.2 = some ti ∧ ti ≤ t := by
  intro y o t ht
  have htime : s'.time = s.time + 1 := by du_step_cases h <;> rfl
  rw [htime]
  by_cases hold : s.lin y o = some t
  · obtain ⟨h1, ti, h2, h3⟩ := C.lin_inv _ _ _ hold
    exact ⟨by omega, ti, InvC.invAt_mono I B C hM h _ _ _ _ h2, h3⟩
  · obtain ⟨-, -, ho, rfl, -, -⟩ := InvC.lin_new I B C hM h ht hold
    obtain ⟨ti, hti⟩ := C.v_hist _ y o ho
    have := C.time_inv _ _ _ _ hti
    exact ⟨by omega, ti, InvC.invAt_mono I B C hM h _ _ _ _ hti, by omega⟩

theorem InvC.lin_pre_step : ∀ m o t, s'.lin m o = some t → ∃ hh, hh <+: s'.G m ∧ o ∈ hh ∧
    ∀ o' ∈ hh, ∃ t', s'.lin m o' = some t' ∧ t' ≤ t := by
  intro y o t ht
  have hlm := InvC.lin_mono I B C hM h
  by_cases hold : s.lin y o = some t
  · obtain ⟨hh, h1, h2, h3⟩ := C.lin_pre _ _ _ hold
    refine ⟨hh, h1.trans (G_prefix h y), h2, fun o' ho' => ?_⟩
    obtain ⟨t', h4, h5⟩ := h3 o' ho'
    exact ⟨t', hlm _ _ _ h4, h5⟩
  · obtain ⟨hpc, -, ho, rfl, -, hG⟩ := InvC.lin_new I B C hM h ht hold
    refine ⟨(s.loc a.proc).hist y, by rw [hG]; exact B.hist_G _ y, ho, fun o' ho' => ?_⟩
    cases hl : s.lin y o' with
    | some t' =>
      exact ⟨t', hlm _ _ _ hl, le_of_lt (C.lin_inv _ _ _ hl).1⟩
    | none =>
      refine ⟨s.time, ?_, le_rfl⟩
      du_step_cases h <;> simp only [hpc, reduceCtorEq] at *
      simp [hl, ho']

theorem InvC.res_hist_step : ∀ i m c, (m, c) ∈ (s'.loc i).res → (i, c) ∈ (s'.loc i).hist m ∧
    ∃ hh, s'.retH i m c = some hh := by
  intro i y c hr
  have hretH : ∀ hh, s.retH i y c = some hh → ∃ hh', s'.retH i y c = some hh' := by
    intro hh hh1
    du_step_cases h <;> simp only [tInit_retH, tN1Inv_retH, tN1Resp_retH, tScInv_retH, tScResp_retH,
      tAcInv_retH, tAcResp_retH, tCollect_retH, tLoc_retH, tUpdIn_retH, tUpdMine_retH,
      tUpdOther_retH, tUpdAdopt_retH, tWrite_retH, hh1] <;> first | exact ⟨_, rfl⟩ | (split_ifs <;> simp)
  by_cases hi : i = a.proc
  · subst hi
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hr ⊢
    all_goals first
      | (simp at hr; done)
      | (simp only [List.mem_cons, Prod.mk.injEq] at hr
         rcases hr with ⟨rfl, rfl⟩ | hr
         · exact ⟨by simp [hmine],
             (s.loc a.proc).hist ⟨m, hm⟩ ++ [(s.loc a.proc).acop ⟨m, hm⟩], by simp⟩
         · obtain ⟨h1, hh, h2⟩ := C.res_hist _ y c hr
           refine ⟨?_, hretH hh h2⟩
           by_cases hy : y = ⟨m, hm⟩
           · subst hy; simp [h1]
           · simp [Function.update_of_ne hy, h1])
      | (obtain ⟨h1, hh, h2⟩ := C.res_hist _ y c hr
         refine ⟨?_, hretH hh h2⟩
         first
         | exact h1
         | exact ((merge_spec _ _ _ (B.hist_G _ y) (fun q => gs_le_G B _ q y)).2.1).subset h1
         | (by_cases hy : y = ⟨m, hm⟩
            · subst hy; simp [h1]
            · simp [Function.update_of_ne hy, h1]))
  · rw [loc_ne h hi] at hr ⊢
    obtain ⟨h1, hh, h2⟩ := C.res_hist i y c hr
    exact ⟨h1, hretH hh h2⟩

theorem InvC.ret_lin_step : ∀ i m c t, s'.retAt i m c = some t →
    ∃ tl, s'.lin m (i, c) = some tl ∧ tl ≤ t := by
  intro i y c t ht
  have hlm := InvC.lin_mono I B C hM h
  by_cases hold : s.retAt i y c = some t
  · obtain ⟨tl, h1, h2⟩ := C.ret_lin _ _ _ _ hold
    exact ⟨tl, hlm _ _ _ h1, h2⟩
  · du_step_cases h <;> simp only [tInit_retAt, tN1Inv_retAt, tN1Resp_retAt, tScInv_retAt,
      tScResp_retAt, tAcInv_retAt, tAcResp_retAt, tCollect_retAt, tLoc_retAt, tUpdIn_retAt,
      tUpdMine_retAt, tUpdOther_retAt, tUpdAdopt_retAt, tWrite_retAt] at ht <;>
      try exact absurd ht hold
    · -- returns at line 10
      split_ifs at ht with hc
      · obtain ⟨rfl, hd, rfl⟩ := hc
        simp only [Option.some.injEq] at ht; subst ht
        have hgst : ∀ o, o ∈ (s.loc a.proc).hist y ∨ (∃ q, o ∈ (s.loc a.proc).gs q y) →
            ∃ q, o ∈ s.gst q y := by
          rintro o (h1 | ⟨q, h1⟩)
          · exact ⟨a.proc, by rw [← B.hist_eq _ y (by simp [hpc])]; exact h1⟩
          · exact ⟨q, (B.gs_gst _ q y).subset h1⟩
        obtain ⟨q, hq⟩ := hgst _ (mem_merge hd)
        obtain ⟨tl, htl⟩ := C.lin_gst q y _ hq
        exact ⟨tl, hlm _ _ _ htl, le_of_lt (C.lin_inv _ _ _ htl).1⟩
      · exact absurd ht hold
    · -- returns at line 31
      split_ifs at ht with hc
      · obtain ⟨rfl, hres⟩ := hc
        simp only [Option.some.injEq] at ht; subst ht
        have hin := (C.res_hist _ _ _ hres).1
        cases hl : s.lin y (a.proc, c) with
        | some tl => exact ⟨tl, hlm _ _ _ hl, le_of_lt (C.lin_inv _ _ _ hl).1⟩
        | none => exact ⟨s.time, by simp [hl, hin], le_rfl⟩
      · exact absurd ht hold

theorem InvC.ret_H_step : ∀ i m c hh, s'.retH i m c = some hh → hh <+: s'.G m ∧ (i, c) ∈ hh := by
  intro i y c hh ht
  by_cases hold : s.retH i y c = some hh
  · obtain ⟨h1, h2⟩ := C.ret_H _ _ _ _ hold
    exact ⟨h1.trans (G_prefix h y), h2⟩
  · have hBpost := InvB.hist_G_step I B hM h
    du_step_cases h <;> simp only [tInit_retH, tN1Inv_retH, tN1Resp_retH, tScInv_retH,
      tScResp_retH, tAcInv_retH, tAcResp_retH, tCollect_retH, tLoc_retH, tUpdIn_retH,
      tUpdMine_retH, tUpdOther_retH, tUpdAdopt_retH, tWrite_retH] at ht <;>
      try exact absurd ht hold
    · split_ifs at ht with hc
      · obtain ⟨rfl, hd, rfl⟩ := hc
        simp only [Option.some.injEq] at ht; subst ht
        exact ⟨(merge_spec _ _ _ (B.hist_G _ y) (fun q => gs_le_G B _ q y)).1, hd⟩
      · exact absurd ht hold
    · split_ifs at ht with hc
      · obtain ⟨rfl, rfl, rfl⟩ := hc
        simp only [Option.some.injEq] at ht; subst ht
        have := hBpost a.proc ⟨m, hm⟩
        simp only [tUpdMine_loc, Function.update_self] at this
        exact ⟨this, by simp [hmine]⟩
      · exact absurd ht hold

theorem InvC.step : InvC M s' where
  time_inv := InvC.time_inv_step I B C hM h
  inv_cnt := InvC.inv_cnt_step I B C hM h
  inv_init := InvC.inv_init_step I B C hM h
  v_lastOp := InvC.v_lastOp_step I B C hM h
  v_loc := InvC.v_loc_step I B C hM h
  v_acI := InvC.v_acI_step I B C hM h
  v_scI := InvC.v_scI_step I B C hM h
  v_opRec := InvC.v_opRec_step I B C hM h
  v_hist := InvC.v_hist_step I B C hM h
  v_G := InvC.v_G_step I B C hM h
  lin_gst := InvC.lin_gst_step I B C hM h
  lin_inv := InvC.lin_inv_step I B C hM h
  lin_pre := InvC.lin_pre_step I B C hM h
  res_hist := InvC.res_hist_step I B C hM h
  ret_lin := InvC.ret_lin_step I B C hM h
  ret_H := InvC.ret_H_step I B C hM h

end Fields

/-- All reachable states satisfy the three invariants. -/
theorem Reachable.inv3 (hM : M.Good) (hs : Reachable M s) : InvA M s ∧ InvB M s ∧ InvC M s := by
  induction hs with
  | refl => exact ⟨invA_init M, invB_init M, invC_init M⟩
  | tail _ hst ih =>
    obtain ⟨a, ha⟩ := hst
    obtain ⟨I, B, C⟩ := ih
    exact ⟨I.step ha, B.step I hM ha, C.step I B hM ha⟩

end Podc.DistributedUniversality
