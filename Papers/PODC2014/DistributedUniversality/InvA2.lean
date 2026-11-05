import Papers.PODC2014.DistributedUniversality.InvA

/-! # Preservation of the local bookkeeping invariants of `InvA` -/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

theorem InvA.oper_rec_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ i m, (s'.loc i).pc ≠ .init → ¬ pastUpd (s'.loc i).pc m →
      s'.opRec (s'.loc i).r m i = some ((s'.loc i).oper m) := by
  intro i y hni hnp
  by_cases hi : i = a.proc
  · subst hi
    have hmono := I.opRec_mono h
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hni hnp ⊢
    · simp
    all_goals first
      | exact hmono _ _ _ _ (I.oper_rec _ y (by simp [hpc]) (by simp [hpc]))
      | simp
      | skip
    all_goals
      try unfold updPC at hnp
      split_ifs at hnp with hk
      · simp only [pastUpd_upd, not_lt] at hnp
        have hne : y ≠ ⟨m, hm⟩ := by intro he; subst he; simp at hnp
        rw [Function.update_of_ne hne]
        first
        | exact hmono _ _ _ _ (I.oper_rec _ y (by simp [hpc]) (by simp [hpc]; omega))
        | simp
      · simp at hnp
  · rw [loc_ne h hi] at hni hnp ⊢
    rw [opRec_ne h hi]
    exact I.oper_rec i y hni hnp

/-- The post-state program counter of the stepping process is not an N1 / SC counter unless the
step is one of the listed ones. -/
theorem InvA.n1_loc_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ i m', ((s'.loc i).pc = .n1Inv m' ∨ (s'.loc i).pc = .n1Resp m') → ∀ y : Fin k,
      (y.val < m' → s'.acR (s'.loc i).r false y i = some ((s'.loc i).tag y, (s'.loc i).acop y)) ∧
      (m' ≤ y.val → s'.acR (s'.loc i).r false y i = none) ∧
      ((m' < y.val ∨ ((s'.loc i).pc = .n1Inv m' ∧ m' = y.val)) →
        s'.acI (s'.loc i).r false y i = none) := by
  intro i m' hpc' y
  by_cases hi : i = a.proc
  · subst hi
    have hr0 := I.init_r a.proc
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hpc' ⊢
    · -- init
      simp only [startPC] at hpc'
      split_ifs at hpc' <;> simp at hpc'
      obtain rfl := hpc'
      have hr : (s.loc a.proc).r = 0 := hr0.1 hpc
      refine ⟨by simp, fun _ => ?_, fun _ => ?_⟩
      · simp only [tInit_acR]
        cases hh : s.acR 1 false y a.proc with
        | none => rfl
        | some tw => have := I.acR_le _ _ _ _ _ hh; omega
      · simp only [tInit_acI]
        cases hh : s.acI 1 false y a.proc with
        | none => rfl
        | some tw => have := I.acI_le _ _ _ _ _ hh; omega
    · -- n1Inv
      simp at hpc'; subst hpc'
      have hp := I.n1_loc a.proc m (Or.inl hpc) y
      refine ⟨fun hy => by simpa using hp.1 hy, fun hy => by simpa using hp.2.1 hy, ?_⟩
      intro hy
      simp only [PC.n1Resp.injEq, reduceCtorEq, false_and, or_false] at hy
      simp only [tN1Inv_acI]
      rw [if_neg (by intro hc; have := congrArg Fin.val hc.2.2.1; simp at this; omega)]
      exact hp.2.2 (Or.inl hy)
    · -- n1Resp
      have hp := I.n1_loc a.proc m (Or.inr hpc) y
      split_ifs at hpc' with hk
      · simp at hpc'; subst hpc'
        refine ⟨fun hy => ?_, fun hy => ?_, fun hy => ?_⟩
        · simp only [tN1Resp_acR]
          by_cases hym : y = ⟨m, hm⟩
          · subst hym; simp
          · have : y.val < m := by
              have : y.val ≠ m := fun h' => hym (Fin.ext h'); omega
            rw [if_neg (by intro hc; exact hym hc.2.2.1)]
            simpa [Function.update_of_ne hym] using hp.1 this
        · simp only [tN1Resp_acR]
          rw [if_neg (by intro hc; have := congrArg Fin.val hc.2.2.1; simp at this; omega)]
          exact hp.2.1 (by omega)
        · simp only [tN1Resp_acI]
          exact hp.2.2 (Or.inl (by rcases hy with hy | ⟨-, hy⟩ <;> omega))
      · simp [afterN1] at hpc'; split_ifs at hpc' <;> simp at hpc'
    · simp at hpc'
    all_goals first
      | simp at hpc'
      | (unfold updPC at hpc'; split_ifs at hpc' <;> simp at hpc')
      | (split_ifs at hpc' <;> simp at hpc')
      | skip
    -- write
    simp only [startPC] at hpc'
    split_ifs at hpc' <;> simp at hpc'
    obtain rfl := hpc'
    refine ⟨by simp, fun _ => ?_, fun _ => ?_⟩
    · simp only [tWrite_acR]
      cases hh : s.acR ((s.loc a.proc).r + 1) false y a.proc with
      | none => rfl
      | some tw => have := I.acR_le _ _ _ _ _ hh; omega
    · simp only [tWrite_acI]
      cases hh : s.acI ((s.loc a.proc).r + 1) false y a.proc with
      | none => rfl
      | some tw => have := I.acI_le _ _ _ _ _ hh; omega
  · rw [loc_ne h hi] at hpc' ⊢
    simp only [acR_ne h hi, acI_ne h hi]
    exact I.n1_loc i m' hpc' y

/-- Closing tactic for impossible post program counters. -/
macro "du_pc_absurd" hpc':ident : tactic => `(tactic| first
  | simp at $hpc':ident
  | (unfold updPC at $hpc':ident; split_ifs at $hpc':ident <;> simp at $hpc':ident)
  | (unfold startPC at $hpc':ident; split_ifs at $hpc':ident <;> simp at $hpc':ident)
  | (split_ifs at $hpc':ident <;> simp [afterN1] at $hpc':ident <;>
      (try split_ifs at $hpc':ident) <;> simp at $hpc':ident))

theorem InvA.n1_pend_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ i m (hm : m < k), (s'.loc i).pc = .n1Resp m →
      s'.acI (s'.loc i).r false ⟨m, hm⟩ i = some ((s'.loc i).oper ⟨m, hm⟩) := by
  intro i m0 hm0 hpc'
  by_cases hi : i = a.proc
  · subst hi
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hpc' ⊢
    case _ => du_pc_absurd hpc'
    all_goals first
      | (simp at hpc'; subst hpc'; simp)
      | du_pc_absurd hpc'
  · rw [loc_ne h hi] at hpc' ⊢
    rw [acI_ne h hi]
    exact I.n1_pend i m0 hm0 hpc'

theorem InvA.ph1_none_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ i, prePh1 (s'.loc i).pc → ∀ y, s'.acR (s'.loc i).r true y i = none ∧
      s'.acI (s'.loc i).r true y i = none := by
  intro i hpc' y
  by_cases hi : i = a.proc
  · subst hi
    have hr0 := I.init_r a.proc
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hpc' ⊢
    · have hr : (s.loc a.proc).r = 0 := hr0.1 hpc
      simp only [tInit_acR, tInit_acI]
      constructor
      · cases hh : s.acR 1 true y a.proc with
        | none => rfl
        | some tw => have := I.acR_le _ _ _ _ _ hh; omega
      · cases hh : s.acI 1 true y a.proc with
        | none => rfl
        | some tw => have := I.acI_le _ _ _ _ _ hh; omega
    · simpa using I.ph1_none _ (by simp [hpc]) y
    · simp only [tN1Resp_acR, tN1Resp_acI]
      rw [if_neg (by simp)]
      exact I.ph1_none _ (by simp [hpc]) y
    · simpa using I.ph1_none _ (by simp [hpc]) y
    all_goals first
      | (simp at hpc'; done)
      | (unfold updPC at hpc'; split_ifs at hpc' <;> simp at hpc'; done)
      | (split_ifs at hpc' <;> simp at hpc'; done)
      | skip
    simp only [tWrite_acR, tWrite_acI]
    constructor
    · cases hh : s.acR ((s.loc a.proc).r + 1) true y a.proc with
      | none => rfl
      | some tw => have := I.acR_le _ _ _ _ _ hh; omega
    · cases hh : s.acI ((s.loc a.proc).r + 1) true y a.proc with
      | none => rfl
      | some tw => have := I.acI_le _ _ _ _ _ hh; omega
  · rw [loc_ne h hi] at hpc' ⊢
    simp only [acR_ne h hi, acI_ne h hi]
    exact I.ph1_none i hpc' y

theorem InvA.scI_none_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ i, ((∃ m, (s'.loc i).pc = .n1Inv m) ∨ (∃ m, (s'.loc i).pc = .n1Resp m) ∨
      (s'.loc i).pc = .scInv) → s'.scI (s'.loc i).r i = none := by
  intro i hpc'
  by_cases hi : i = a.proc
  · subst hi
    have hr0 := I.init_r a.proc
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hpc' ⊢
    · have hr : (s.loc a.proc).r = 0 := hr0.1 hpc
      simp only [tInit_scI]
      cases hh : s.scI 1 a.proc with
      | none => rfl
      | some tw => have := I.scI_le _ _ _ hh; omega
    · simpa using I.scI_none _ (Or.inl ⟨_, hpc⟩)
    · simpa using I.scI_none _ (Or.inr (Or.inl ⟨_, hpc⟩))
    all_goals first
      | (simp at hpc'; done)
      | (unfold updPC at hpc'; split_ifs at hpc' <;> simp at hpc'; done)
      | (split_ifs at hpc' <;> simp at hpc'; done)
      | skip
    simp only [tWrite_scI]
    cases hh : s.scI ((s.loc a.proc).r + 1) a.proc with
    | none => rfl
    | some tw => have := I.scI_le _ _ _ hh; omega
  · rw [loc_ne h hi] at hpc' ⊢
    rw [scI_ne h hi]
    exact I.scI_none i hpc'

theorem InvA.sc_loc_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ i, ((s'.loc i).pc = .scInv ∨ (s'.loc i).pc = .scResp) → M.ca = true → ∀ y,
      s'.acR (s'.loc i).r false y i = some ((s'.loc i).tag y, (s'.loc i).acop y) := by
  intro i hpc' hca y
  by_cases hi : i = a.proc
  · subst hi
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hpc' ⊢
    · simp [startPC, hca] at hpc'
    · simp at hpc'
    · -- n1Resp, last
      have hp := I.n1_loc a.proc m (Or.inr hpc) y
      split_ifs at hpc' with hk
      · simp at hpc'
      · simp only [tN1Resp_acR]
        by_cases hym : y = ⟨m, hm⟩
        · subst hym; simp
        · have : y.val < m := by
            have : y.val ≠ m := fun h' => hym (Fin.ext h'); have := y.isLt; omega
          rw [if_neg (by intro hc; exact hym hc.2.2.1)]
          simpa [Function.update_of_ne hym] using hp.1 this
    · simpa using I.sc_loc _ (Or.inl hpc) hca y
    all_goals first
      | (simp at hpc'; done)
      | (unfold updPC at hpc'; split_ifs at hpc' <;> simp at hpc'; done)
      | (split_ifs at hpc' <;> simp at hpc'; done)
      | skip
    simp [startPC, hca] at hpc'
  · rw [loc_ne h hi] at hpc' ⊢
    simp only [acR_ne h hi]
    exact I.sc_loc i hpc' hca y

theorem InvA.ph1_loc_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ i j, ((s'.loc i).pc = .acInv j ∨ (s'.loc i).pc = .acResp j) →
    s'.scR (s'.loc i).r i = some (s'.loc i).scd ∧ (s'.loc i).ord = ordOf (s'.loc i).scd ∧ j ≤ k ∧
    ∀ y, (y ∈ (s'.loc i).ord.take j →
        s'.acR (s'.loc i).r true y i = some ((s'.loc i).tag y, (s'.loc i).acop y)) ∧
      (y ∉ (s'.loc i).ord.take j → s'.acR (s'.loc i).r true y i = none ∧
        (M.ca = true → s'.acR (s'.loc i).r false y i = some ((s'.loc i).tag y, (s'.loc i).acop y))) ∧
      (y ∉ (s'.loc i).ord.take (if (s'.loc i).pc = .acInv j then j else j + 1) →
        s'.acI (s'.loc i).r true y i = none) := by
  intro i j0 hpc'
  by_cases hi : i = a.proc
  · subst hi
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hpc' ⊢
    all_goals first
      | (simp at hpc'; done)
      | (unfold updPC at hpc'; split_ifs at hpc' <;> simp at hpc'; done)
      | (unfold startPC at hpc'; split_ifs at hpc' <;> simp at hpc'; done)
      | (split_ifs at hpc' <;> simp [afterN1] at hpc' <;> (try split_ifs at hpc') <;>
          simp at hpc'; done)
      | skip
    · -- scResp
      simp at hpc'; subst hpc'
      refine ⟨by simp, trivial, Nat.zero_le _, fun y => ⟨by simp, fun _ => ?_, fun _ => ?_⟩⟩
      · have := I.ph1_none a.proc (by simp [hpc]) y
        rw [tScResp_acR, tScResp_acR]
        exact ⟨this.1, fun hca => I.sc_loc _ (Or.inr hpc) hca y⟩
      · rw [tScResp_acI]; exact (I.ph1_none a.proc (by simp [hpc]) y).2
    · -- acInv
      simp at hpc'; subst hpc'
      obtain ⟨h1, h2, h3, h4⟩ := I.ph1_loc a.proc j (Or.inl hpc)
      refine ⟨by simpa using h1, h2, h3, fun y => ⟨fun hy => by simpa using (h4 y).1 hy,
        fun hy => by simpa using (h4 y).2.1 hy, fun hy => ?_⟩⟩
      simp only [reduceCtorEq, ↓reduceIte] at hy
      simp only [tAcInv_acI]
      rw [take_succ_of_getElem? hx] at hy
      have hyx : y ≠ x := by intro e; subst e; simp at hy
      rw [if_neg (by intro hc; exact hyx hc.2.2.1)]
      refine (h4 y).2.2 ?_
      simp only [hpc, ↓reduceIte]
      intro hm; exact hy (List.mem_append_left _ hm)
    · -- acResp
      split_ifs at hpc' with hk
      · simp at hpc'; subst hpc'
        simp only [hk, ↓reduceIte]
        obtain ⟨h1, h2, h3, h4⟩ := I.ph1_loc a.proc j (Or.inr hpc)
        have hlen : (s.loc a.proc).ord.length = k := by rw [h2]; exact length_ordOf _
        refine ⟨by simpa using h1, h2, by omega, fun y => ⟨fun hy => ?_, fun hy => ?_, fun hy => ?_⟩⟩
        · rw [take_succ_of_getElem? hx] at hy
          simp only [tAcResp_acR]
          by_cases hyx : y = x
          · subst hyx; simp
          · rw [if_neg (by intro hc; exact hyx hc.2.2.1)]
            have hy' : y ∈ (s.loc a.proc).ord.take j := by simpa [hyx] using hy
            simpa [Function.update_of_ne hyx] using (h4 y).1 hy'
        · rw [take_succ_of_getElem? hx] at hy
          have hyx : y ≠ x := by intro e; subst e; simp at hy
          have hy' : y ∉ (s.loc a.proc).ord.take j := fun hm => hy (List.mem_append_left _ hm)
          simp only [tAcResp_acR]
          rw [if_neg (by intro hc; exact hyx hc.2.2.1), if_neg (by simp)]
          exact ⟨(h4 y).2.1 hy' |>.1, fun hca => by
            simpa [Function.update_of_ne hyx] using ((h4 y).2.1 hy').2 hca⟩
        · simp only [tAcResp_acI]
          have := (h4 y).2.2
          simp only [hpc, reduceCtorEq, ↓reduceIte] at this
          exact this hy
      · simp at hpc'
  · rw [loc_ne h hi] at hpc' ⊢
    simp only [acR_ne h hi, acI_ne h hi, scR_ne h hi]
    exact I.ph1_loc i j0 hpc'

theorem InvA.ac_pend_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ i j x, (s'.loc i).pc = .acResp j → (s'.loc i).ord[j]? = some x →
      s'.acI (s'.loc i).r true x i = some (acVal M (s'.loc i) x) := by
  intro i j0 x0 hpc' hx0
  by_cases hi : i = a.proc
  · subst hi
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hpc' hx0 ⊢
    all_goals first
      | (simp at hpc'; done)
      | (unfold updPC at hpc'; split_ifs at hpc' <;> simp at hpc'; done)
      | (unfold startPC at hpc'; split_ifs at hpc' <;> simp at hpc'; done)
      | (split_ifs at hpc' <;> simp [afterN1] at hpc' <;> (try split_ifs at hpc') <;>
          simp at hpc'; done)
      | skip
    simp at hpc'; subst hpc'
    rw [hx] at hx0
    simp only [Option.some.injEq] at hx0; subst hx0
    rw [tAcInv_acI]; simp only [and_self, ↓reduceIte]; rfl
  · rw [loc_ne h hi] at hpc' hx0 ⊢
    rw [acI_ne h hi]
    exact I.ac_pend i j0 x0 hpc' hx0

theorem InvA.finR_loc_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ i, pastAC (s'.loc i).pc → ∀ y,
      s'.finR (s'.loc i).r y i = some ((s'.loc i).tag y, (s'.loc i).acop y) := by
  intro i hpc' y
  by_cases hi : i = a.proc
  · subst hi
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hpc' ⊢
    · simp [startPC] at hpc'; split_ifs at hpc' <;> simp at hpc'
    · simp at hpc'
    · split_ifs at hpc' with hk
      · simp at hpc'
      · unfold afterN1 at hpc'
        split_ifs at hpc' with hall
        · rw [tN1Resp_finR, if_pos ⟨rfl, rfl, hk, hall⟩]
        · simp at hpc'
    · simp at hpc'
    · simp at hpc'
    · simp at hpc'
    · split_ifs at hpc' with hk
      · simp at hpc'
      · rw [tAcResp_finR, if_pos ⟨rfl, rfl, hk⟩]
    all_goals first
      | (simp [startPC] at hpc'; split_ifs at hpc' <;> simp at hpc'; done)
      | exact I.finR_loc a.proc (by simp [hpc]) y
  · rw [loc_ne h hi] at hpc' ⊢
    rw [finR_ne h hi]
    exact I.finR_loc i hpc' y

theorem InvA.finR_fut_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r m j tw, s'.finR r m j = some tw →
      r < (s'.loc j).r ∨ (r = (s'.loc j).r ∧ pastAC (s'.loc j).pc) := by
  intro r y j0 tw hw
  by_cases hold : s.finR r y j0 = some tw
  · have hf := I.finR_fut _ _ _ _ hold
    by_cases hj : j0 = a.proc
    · subst hj
      have hr := r_mono h (fun i => (I.init_r i).1) a.proc
      rcases hf with hf | ⟨rfl, hf⟩
      · exact Or.inl (lt_of_lt_of_le hf hr)
      · du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] <;>
          first
          | (simp [hpc] at hf; done)
          | (left; omega)
          | (right; refine ⟨trivial, ?_⟩; first
              | trivial
              | (unfold updPC; split_ifs <;> trivial)
              | (split_ifs <;> trivial))
    · rw [loc_ne h hj]; exact hf
  · obtain ⟨rfl, rfl, hpc', hr', -⟩ := I.finR_new h hw hold
    right; rw [hr', hpc']; exact ⟨rfl, trivial⟩

theorem InvA.finR_past_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ i r m, 1 ≤ r → r < (s'.loc i).r → ∃ tw, s'.finR r m i = some tw := by
  intro i r y h1 h2
  by_cases hi : i = a.proc
  · subst hi
    have hr := r_post h
    by_cases hp : r < (s.loc a.proc).r
    · obtain ⟨tw, htw⟩ := I.finR_past _ _ y h1 hp
      exact ⟨tw, I.finR_mono h _ _ _ _ htw⟩
    · split_ifs at hr with hc1 hc2
      · omega
      · have : r = (s.loc a.proc).r := by omega
        subst this
        exact ⟨_, I.finR_mono h _ _ _ _ (I.finR_loc a.proc (by simp [hc2]) y)⟩
      · omega
  · rw [loc_ne h hi] at h2
    rw [finR_ne h hi]
    exact I.finR_past i r y h1 h2

theorem InvA.acI0_ca_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r y j w, s'.acI r false y j = some w → M.ca = true := by
  intro r y j w hw
  by_cases hold : s.acI r false y j = some w
  · exact I.acI0_ca _ _ _ _ hold
  · obtain ⟨-, -, hc⟩ := I.acI_new h hw hold
    rcases hc with ⟨-, m, hpc, -⟩ | ⟨h1, -⟩
    · exact I.ca_n1 _ _ (Or.inl hpc)
    · simp at h1

theorem InvA.finR_pos_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r m j tw, s'.finR r m j = some tw → 1 ≤ r := by
  intro r y j tw hw
  by_cases hold : s.finR r y j = some tw
  · exact I.finR_pos _ _ _ _ hold
  · obtain ⟨rfl, rfl, -, hr', -⟩ := I.finR_new h hw hold
    have hr := r_post h
    have := I.init_r a.proc
    by_cases hpc : (s.loc a.proc).pc = .init
    · simp only [hpc, ↓reduceIte] at hr; omega
    · have : (s.loc a.proc).r ≠ 0 := fun h0 => hpc (this.2 h0)
      omega

theorem InvA.step (I : InvA M s) (h : stepFn M s a = some s') : InvA M s' where
  ca_n1 := I.ca_n1_step h
  init_r := I.init_r_step h
  acR_inv := I.acR_inv_step h
  acR_agree := I.acR_agree_step h
  acI0 := I.acI0_step h
  acI1 := I.acI1_step h
  acI1ca := I.acI1ca_step h
  scI_prov := I.scI_prov_step h
  scI_ca := I.scI_ca_step h
  scR_valid := I.scR_valid_step h
  finR_src := I.finR_src_step h
  acR_le := I.acR_le_step h
  opRec_le := I.opRec_le_step h
  finR_fut := I.finR_fut_step h
  finR_past := I.finR_past_step h
  oper_rec := I.oper_rec_step h
  n1_loc := I.n1_loc_step h
  n1_pend := I.n1_pend_step h
  ph1_none := I.ph1_none_step h
  acI_le := I.acI_le_step h
  sc_loc := I.sc_loc_step h
  ph1_loc := I.ph1_loc_step h
  ac_pend := I.ac_pend_step h
  scI_le := I.scI_le_step h
  scI_none := I.scI_none_step h
  finR_loc := I.finR_loc_step h
  acI0_ca := I.acI0_ca_step h
  finR_pos := I.finR_pos_step h

theorem InvA.of_reachable (hs : Reachable M s) : InvA M s := by
  induction hs with
  | refl => exact invA_init M
  | tail _ hst ih => obtain ⟨a, ha⟩ := hst; exact ih.step ha

end Podc.DistributedUniversality
