import Papers.PODC2014.DistributedUniversality.Chain

/-! # Preservation of `InvB`: frame facts -/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

theorem nodup_append_single {α : Type*} {l : List α} {x : α} (h1 : x ∉ l) (h2 : l.Nodup) :
    (l ++ [x]).Nodup := by
  rw [List.nodup_append]
  refine ⟨h2, List.nodup_singleton x, ?_⟩
  intro b hb c hc e
  simp only [List.mem_singleton] at hc
  subst hc; subst e; exact h1 hb

/-- `G` and `born` change only when a process appends to a history equal to `G` (line 18). -/
theorem GB_cases (h : stepFn M s a = some s') (y : Fin k) :
    (s'.G y = s.G y ∧ s'.born y = s.born y) ∨
    (∃ mm, (s.loc a.proc).pc = .upd mm ∧ y.val = mm ∧ (s.loc a.proc).tag y = true ∧
      (s.loc a.proc).acop y ∉ (s.loc a.proc).hist y ∧ (s.loc a.proc).hist y = s.G y ∧
      s'.G y = s.G y ++ [(s.loc a.proc).acop y] ∧
      s'.born y = s.born y ++ [(s.loc a.proc).r]) := by
  du_step_cases h <;> try exact Or.inl ⟨rfl, rfl⟩
  all_goals
    simp only [tUpdMine_G, tUpdMine_born, tUpdOther_G, tUpdOther_born]
    by_cases hc : (s.loc a.proc).hist ⟨m, hm⟩ = s.G ⟨m, hm⟩
    · by_cases hy : y = ⟨m, hm⟩
      · subst hy
        exact Or.inr ⟨m, hpc, rfl, htag, hnin, hc, by simp [hc], by simp [hc]⟩
      · left; simp [hc, Function.update_of_ne hy]
    · left; simp [hc]

theorem G_prefix (h : stepFn M s a = some s') (y : Fin k) : s.G y <+: s'.G y := by
  rcases GB_cases h y with ⟨h1, -⟩ | ⟨-, -, -, -, -, -, h1, -⟩ <;> rw [h1]
  exact List.prefix_append _ _

theorem born_prefix (h : stepFn M s a = some s') (y : Fin k) : s.born y <+: s'.born y := by
  rcases GB_cases h y with ⟨-, h1⟩ | ⟨-, -, -, -, -, -, -, h1⟩ <;> rw [h1]
  exact List.prefix_append _ _

theorem gs_le_G (B : InvB M s) (i q : Fin n) (y : Fin k) : (s.loc i).gs q y <+: s.G y :=
  ((B.gs_gst i q y).trans (B.gst_hist q y)).trans (B.hist_G q y)

theorem hist_mono (B : InvB M s) (h : stepFn M s a = some s') (p : Fin n) (y : Fin k) :
    (s.loc p).hist y <+: (s'.loc p).hist y := by
  by_cases hp : p = a.proc
  · subst hp
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc,
      tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc,
      tUpdAdopt_loc, tWrite_loc, Function.update_self] <;> try exact List.prefix_refl _
    · exact (merge_spec _ _ _ (B.hist_G _ y) (fun q => gs_le_G B _ q y)).2.1
    all_goals
      by_cases hy : y = ⟨m, hm⟩
      · subst hy; simp
      · simp [Function.update_of_ne hy]
  · rw [loc_ne h hp]

theorem gst_mono (B : InvB M s) (h : stepFn M s a = some s') (q : Fin n) (y : Fin k) :
    s.gst q y <+: s'.gst q y := by
  du_step_cases h <;> try exact List.prefix_refl _
  simp only [tWrite_gst]
  by_cases hq : q = a.proc
  · subst hq; simpa using B.gst_hist _ y
  · simp [Function.update_of_ne hq]

section Fields
variable (I : InvA M s) (B : InvB M s) (hM : M.Good) (h : stepFn M s a = some s')
include I B hM h

theorem InvB.G_nodup_step : ∀ y, (s'.G y).Nodup := by
  intro y
  rcases GB_cases h y with ⟨h1, -⟩ | ⟨-, -, -, -, hnin, heq, h1, -⟩ <;> rw [h1]
  · exact B.G_nodup y
  · rw [heq] at hnin
    exact nodup_append_single hnin (B.G_nodup y)

theorem InvB.born_len_step : ∀ y, (s'.born y).length = (s'.G y).length := by
  intro y
  rcases GB_cases h y with ⟨h1, h2⟩ | ⟨-, -, -, -, -, -, h1, h2⟩ <;> rw [h1, h2]
  · exact B.born_len y
  · simp [B.born_len y]

theorem InvB.hist_G_step : ∀ p y, (s'.loc p).hist y <+: s'.G y := by
  intro p y
  by_cases hp : p = a.proc
  · subst hp
    have hG := G_prefix h y
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] <;>
      try exact (B.hist_G _ y).trans hG
    · exact ((merge_spec _ _ _ (B.hist_G _ y) (fun q => gs_le_G B _ q y)).1).trans hG
    all_goals
      by_cases hy : y = ⟨m, hm⟩
      · subst hy
        simp only [Function.update_self]
        by_cases he : (s.loc a.proc).hist ⟨m, hm⟩ = s.G ⟨m, hm⟩
        · simp [he]
        · obtain ⟨hx, hxe⟩ := chain_next I B hM hpc htag hnin he
          refine List.IsPrefix.trans ?_ hG
          rw [List.prefix_iff_eq_take, List.length_append, List.length_singleton,
            List.take_succ, List.getElem?_eq_getElem hx, hxe,
            ← List.prefix_iff_eq_take.1 (B.hist_G _ _)]
          rfl
      · simp only [Function.update_of_ne hy]
        exact (B.hist_G _ y).trans hG
  · rw [loc_ne h hp]
    exact (B.hist_G p y).trans (G_prefix h y)

theorem InvB.gst_hist_step : ∀ p y, s'.gst p y <+: (s'.loc p).hist y := by
  intro p y
  by_cases hp : p = a.proc
  · subst hp
    by_cases hw : (s.loc a.proc).pc = .write
    · du_step_cases h <;> simp only [hpc, reduceCtorEq] at hw
      simp
    · have : s'.gst a.proc y = s.gst a.proc y := by
        du_step_cases h <;> first | rfl | exact absurd hpc hw
      rw [this]
      exact (B.gst_hist _ y).trans (hist_mono B h _ y)
  · have : s'.gst p y = s.gst p y := by
      du_step_cases h <;> first | rfl | simp [Function.update_of_ne hp]
    rw [this, loc_ne h hp]
    exact B.gst_hist p y

theorem InvB.gs_gst_step : ∀ p q y, (s'.loc p).gs q y <+: s'.gst q y := by
  intro p q0 y
  refine List.IsPrefix.trans ?_ (gst_mono B h q0 y)
  by_cases hp : p = a.proc
  · subst hp
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] <;> try exact B.gs_gst _ q0 y
    by_cases hq' : q0 = ⟨q, hq⟩
    · subst hq'; simp
    · simp only [Function.update_of_ne hq']; exact B.gs_gst _ q0 y
  · rw [loc_ne h hp]; exact B.gs_gst p q0 y

theorem InvB.hist_eq_step : ∀ p y, ¬ pastLoc (s'.loc p).pc → (s'.loc p).hist y = s'.gst p y := by
  intro p y hp'
  by_cases hp : p = a.proc
  · subst hp
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hp' ⊢ <;>
      first
      | (exfalso; apply hp'; unfold updPC; split_ifs <;> trivial)
      | (exfalso; apply hp'; split_ifs <;> trivial)
      | exact B.hist_eq _ y (by simp [hpc])
      | simp
  · rw [loc_ne h hp] at hp' ⊢
    have : s'.gst p y = s.gst p y := by
      du_step_cases h <;> first | rfl | simp [Function.update_of_ne hp]
    rw [this]; exact B.hist_eq p y hp'

end Fields

end Podc.DistributedUniversality
