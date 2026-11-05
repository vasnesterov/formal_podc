import Papers.PODC2014.DistributedUniversality.InvBStep

/-! # Preservation of `InvB`: proposals, knowledge and the birth records of `G` -/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

theorem pastUpd_updPC {m : ℕ} (hm : m < k) (y : Fin k) :
    pastUpd (updPC (k := k) m) y ↔ y.val ≤ m := by
  unfold updPC
  split_ifs with hk
  · simp only [pastUpd_upd]; omega
  · simp only [pastUpd_write, true_iff]; have := y.isLt; omega

/-- A uniform round of the post-state that some process has already completed was uniform before. -/
theorem InvA.unif_pre_of_lt (I : InvA M s) (h : stepFn M s a = some s') {ρ y V} {p : Fin n}
    (hU : Unif s' ρ y V) (hlt : ρ < (s'.loc p).r) : Unif s ρ y V := by
  have I' := I.step h
  have h1 := I'.unif_pos hU
  refine unif_pre (I.finR_mono h) ?_ hU
  by_cases hp : ρ < (s.loc p).r
  · exact I.finR_nonempty y h1 hp
  · by_cases hpa : p = a.proc
    · subst hpa
      have hr := r_post h
      split_ifs at hr with hc1 hc2
      · omega
      · have : ρ = (s.loc a.proc).r := by omega
        subst this
        exact ⟨a.proc, _, I.finR_loc a.proc (by simp [hc2]) y⟩
      · omega
    · rw [loc_ne h hpa] at hlt; omega

section Fields
variable (I : InvA M s) (B : InvB M s) (hM : M.Good) (h : stepFn M s a = some s')
include I B hM h

theorem InvB.opPost_step : ∀ p y, pastUpd (s'.loc p).pc y →
    ∃ b v, s'.finR (s'.loc p).r y p = some (b, v) ∧
      ((s'.loc p).oper y = v ∨ v ∈ (s'.loc p).hist y) := by
  intro p y hpu
  by_cases hp : p = a.proc
  · subst hp
    have hfm := I.finR_mono h
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hpu ⊢
    all_goals first
      | (exfalso; revert hpu; simp [startPC]; split_ifs <;> simp; done)
      | (exfalso; revert hpu; simp; done)
      | (exfalso; revert hpu; split_ifs <;> simp [afterN1] <;> (try split_ifs) <;> simp; done)
      | skip
    -- loc
    · split_ifs at hpu with hk
      · simp at hpu
      · exact absurd y.isLt (by omega)
    all_goals
      rw [pastUpd_updPC hm] at hpu
      rcases Nat.lt_or_ge y.val m with hy | hy
      · have hne : y ≠ ⟨m, hm⟩ := fun e => by subst e; simp at hy
        obtain ⟨b, v, h1, h2⟩ := B.opPost a.proc y (by simp [hpc, hy])
        refine ⟨b, v, hfm _ _ _ _ h1, ?_⟩
        simp only [Function.update_of_ne hne]
        rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr h2
      · have hye : y = ⟨m, hm⟩ := Fin.ext (by simp; omega)
        subst hye
        have hf := I.finR_loc a.proc (by simp [hpc]) ⟨m, hm⟩
        refine ⟨_, _, hfm _ _ _ _ hf, ?_⟩
        first
        | exact Or.inr hin
        | (right; simp)
        | (left; simp)
  · rw [loc_ne h hp] at hpu ⊢
    rw [finR_ne h hp]
    exact B.opPost p y hpu

theorem InvB.opPre_step : ∀ p y, 2 ≤ (s'.loc p).r → ¬ pastUpd (s'.loc p).pc y →
    ∃ b v, s'.finR ((s'.loc p).r - 1) y p = some (b, v) ∧
      ((s'.loc p).oper y = v ∨ v ∈ s'.gst p y) := by
  intro p y hr2 hpu
  have hfm := I.finR_mono h
  by_cases hp : p = a.proc
  · subst hp
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hpu hr2 ⊢
    all_goals first
      | omega
      | (obtain ⟨b, v, h1, h2⟩ := B.opPre _ y hr2 (by simp [hpc])
         exact ⟨b, v, hfm _ _ _ _ h1, h2⟩)
      | skip
    all_goals first
      | (rw [pastUpd_updPC hm] at hpu
         have hy : m < y.val := by omega
         have hne : y ≠ ⟨m, hm⟩ := fun e => by subst e; simp at hy
         obtain ⟨b, v, h1, h2⟩ := B.opPre a.proc y hr2 (by simp [hpc]; omega)
         refine ⟨b, v, hfm _ _ _ _ h1, ?_⟩
         simp only [Function.update_of_ne hne]
         simpa using h2)
      | (obtain ⟨b, v, h1, h2⟩ := B.opPost a.proc y (by simp [hpc])
         refine ⟨b, v, by simpa using hfm _ _ _ _ h1, ?_⟩
         simpa using h2)
  · rw [loc_ne h hp] at hr2 hpu ⊢
    have hg : s'.gst p y = s.gst p y := by
      du_step_cases h <;> first | rfl | simp [Function.update_of_ne hp]
    rw [hg]
    obtain ⟨b, v, h1, h2⟩ := B.opPre p y hr2 hpu
    exact ⟨b, v, hfm _ _ _ _ h1, h2⟩

theorem InvB.PIa_step : ∀ ρ y V j W, Unif s' ρ y V → s'.opRec (ρ + 1) y j = some W → W ≠ V →
    ∃ q, V ∈ s'.gst q y := by
  intro ρ y V j W hU hW hne
  have I' := I.step h
  have hρ := I'.unif_pos hU
  by_cases hold : s.opRec (ρ + 1) y j = some W
  · have hle := (I.opRec_le _ _ _ _ hold).2
    have hlt : ρ < (s'.loc j).r := lt_of_lt_of_le (by omega) (le_trans hle (r_mono h (fun i => (I.init_r i).1) j))
    have hUp := I.unif_pre_of_lt h hU hlt
    obtain ⟨q, hq⟩ := B.PIa ρ y V j W hUp hold hne
    exact ⟨q, (gst_mono B h q y).subset hq⟩
  · obtain ⟨rfl, hc⟩ := I.opRec_new h hW hold
    rcases hc with ⟨-, h1, -⟩ | ⟨hpc, h1, rfl⟩
    · omega
    · have hρr : ρ = (s.loc a.proc).r := by omega
      subst hρr
      obtain ⟨b, v, hf, hv⟩ := B.opPost a.proc y (by simp [hpc])
      have hvV : v = V := hU.2 _ _ _ (I.finR_mono h _ _ _ _ hf)
      subst hvV
      rcases hv with hv | hv
      · exact absurd hv hne
      · refine ⟨a.proc, ?_⟩
        du_step_cases h <;> simp only [hpc, reduceCtorEq] at *
        simpa using hv

/-- `CI` when a process reaches line 5: it has seen a proposal different from `V`, which was made
by a process that already wrote `V` into its `GSTATE` register. -/
theorem InvB.CI_new {p : Fin n} {y : Fin k} {V : Op n} (hpc' : (s'.loc p).pc = .collect 0)
    (hr2 : 2 ≤ (s'.loc p).r) (hU : Unif s' ((s'.loc p).r - 1) y V)
    (hne : s'.finR (s'.loc p).r y p ≠ some (true, V)) : ∃ q, V ∈ s'.gst q y := by
  have I' := I.step h
  have hf := I'.finR_loc p (by simp [hpc']) y
  rcases I'.cf hf V with ⟨ht, hW⟩ | ⟨j, W', hj, hW'⟩
  · exact absurd (by rw [hf, ht, hW]) hne
  · have hr : (s'.loc p).r - 1 + 1 = (s'.loc p).r := by omega
    rw [← hr] at hj
    exact InvB.PIa_step I B hM h _ y V j W' hU hj hW'

theorem InvB.CI_step : ∀ p y V, 2 ≤ (s'.loc p).r → pastAC (s'.loc p).pc →
    Unif s' ((s'.loc p).r - 1) y V → s'.finR (s'.loc p).r y p ≠ some (true, V) →
    (∃ q, V ∈ s'.gst q y ∧ (collected (s'.loc p).pc q → V ∈ (s'.loc p).gs q y)) ∧
    (pastLoc (s'.loc p).pc → V ∈ (s'.loc p).hist y) := by
  intro p y V hr2 hpa hU hne
  have hUp : Unif s ((s'.loc p).r - 1) y V := I.unif_pre_of_lt (p := p) h hU (by omega)
  have hgm := gst_mono B h
  by_cases hp : p = a.proc
  · subst hp
    by_cases hpre : pastAC (s.loc a.proc).pc
    · have hr : (s'.loc a.proc).r = (s.loc a.proc).r := by
        have := r_post h
        rw [this]
        have h1 : (s.loc a.proc).pc ≠ .init := fun e => by simp [e] at hpre
        by_cases hw : (s.loc a.proc).pc = .write
        · exfalso
          du_step_cases h <;> simp only [hpc, reduceCtorEq] at hw
          revert hpa; simp [startPC]; split_ifs <;> simp
        · simp [h1, hw]
      rw [hr] at hr2 hUp hne
      have hne' : s.finR (s.loc a.proc).r y a.proc ≠ some (true, V) :=
        fun e => hne (I.finR_mono h _ _ _ _ e)
      obtain ⟨⟨q0, hq0, hcol⟩, hloc⟩ := B.CI a.proc y V hr2 hpre hUp hne'
      du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hpa ⊢ <;>
        first
        | (rw [hpc] at hpre; simp at hpre; done)
        | (exfalso; revert hpa; simp [startPC]; split_ifs <;> simp; done)
        | skip
      · -- collect
        refine ⟨⟨q0, hgm _ _ |>.subset hq0, fun hc => ?_⟩, fun hl => ?_⟩
        · by_cases hqq : q0 = ⟨q, hq⟩
          · subst hqq; simp [hq0]
          · simp only [Function.update_of_ne hqq]
            apply hcol
            simp only [hpc, collected_collect]
            have : q0.val ≠ q := fun e => hqq (Fin.ext e)
            split_ifs at hc <;> simp at hc <;> omega
        · split_ifs at hl <;> simp at hl
      · -- loc
        have hv := hcol (by simp [hpc])
        refine ⟨⟨q0, hgm _ _ |>.subset hq0, fun _ => hv⟩, fun _ => ?_⟩
        exact ((merge_spec _ _ _ (B.hist_G _ y) (fun q => gs_le_G B _ q y)).2.2 q0).subset hv
      all_goals
        refine ⟨⟨q0, hgm _ _ |>.subset hq0, fun _ => hcol (by simp [hpc])⟩, fun _ => ?_⟩
        have hv := hloc (by simp [hpc])
        first
        | exact hv
        | (by_cases hy : y = ⟨m, hm⟩
           · subst hy; simp [hv]
           · simp [Function.update_of_ne hy, hv])
    · -- the process reaches line 5 in this step
      have hc0 : (s'.loc a.proc).pc = .collect 0 := by
        du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hpa ⊢ <;>
          first
          | (simp [hpc] at hpre; done)
          | (exfalso; revert hpa; simp [startPC]; split_ifs <;> simp; done)
          | (exfalso; revert hpa; simp; done)
          | (unfold afterN1 at hpa ⊢; split_ifs at hpa ⊢ <;> simp at hpa ⊢)
          | (split_ifs at hpa ⊢ <;> simp at hpa ⊢)
      obtain ⟨q, hq⟩ := InvB.CI_new I B hM h hc0 hr2 hU hne
      refine ⟨⟨q, hq, fun hcol => ?_⟩, fun hl => ?_⟩
      · rw [hc0] at hcol; simp at hcol
      · rw [hc0] at hl; simp at hl
  · rw [loc_ne h hp] at hr2 hpa hUp hne ⊢
    rw [finR_ne h hp] at hne
    obtain ⟨⟨q0, hq0, hcol⟩, hloc⟩ := B.CI p y V hr2 hpa hUp hne
    exact ⟨⟨q0, hgm _ _ |>.subset hq0, hcol⟩, hloc⟩

/-- The knowledge invariant (the heart of Lemma 3): a process that has completed lines 16–28 of
round `ρ + 1` for object `m` knows the value of every uniform round `ρ`. -/
theorem InvB.know_step : ∀ p ρ y V, Unif s' ρ y V → passedUpd (s'.loc p) (ρ + 1) y →
    V ∈ (s'.loc p).hist y := by
  intro p ρ y V hU hpu
  have hlt : ρ < (s'.loc p).r := by rcases hpu with h1 | ⟨h1, -⟩ <;> omega
  have hUp := I.unif_pre_of_lt h hU hlt
  have hρ := I.unif_pos hUp
  by_cases hp : p = a.proc
  · subst hp
    by_cases hpp : passedUpd (s.loc a.proc) (ρ + 1) y
    · exact (hist_mono B h _ y).subset (B.know _ ρ y V hUp hpp)
    · have hpp1 : ¬ ρ + 1 < (s.loc a.proc).r := fun h' => hpp (Or.inl h')
      have hpp2 : ¬ (ρ + 1 = (s.loc a.proc).r ∧ pastUpd (s.loc a.proc).pc y) :=
        fun h' => hpp (Or.inr h')
      have hupd : ∀ mm (hmm : mm < k), (s.loc a.proc).pc = .upd mm →
          pastUpd (updPC (k := k) mm) y → (s'.loc a.proc).r = (s.loc a.proc).r →
          ρ + 1 = (s.loc a.proc).r ∧ y = ⟨mm, hmm⟩ := by
        intro mm hmm hpc' hpu' hr'
        rw [pastUpd_updPC hmm] at hpu'
        rcases hpu with h1 | ⟨h1, h2⟩
        · omega
        · refine ⟨by omega, Fin.ext ?_⟩
          by_contra hne
          have hne' : y.val ≠ mm := by simpa using hne
          exact hpp2 ⟨by omega, by simp [hpc']; omega⟩
      unfold passedUpd at hpu
      du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hpu ⊢
      · rcases hpu with h1 | ⟨h1, h2⟩
        · omega
        · revert h2; simp [startPC]; split_ifs <;> simp
      · exfalso; rcases hpu with h1 | ⟨-, h2⟩
        · exact hpp1 h1
        · simp at h2
      · exfalso; rcases hpu with h1 | ⟨-, h2⟩
        · exact hpp1 h1
        · split_ifs at h2
          · simp at h2
          · unfold afterN1 at h2; split_ifs at h2 <;> simp at h2
      · exfalso; rcases hpu with h1 | ⟨-, h2⟩
        · exact hpp1 h1
        · simp at h2
      · exfalso; rcases hpu with h1 | ⟨-, h2⟩
        · exact hpp1 h1
        · simp at h2
      · exfalso; rcases hpu with h1 | ⟨-, h2⟩
        · exact hpp1 h1
        · simp at h2
      · exfalso; rcases hpu with h1 | ⟨-, h2⟩
        · exact hpp1 h1
        · split_ifs at h2 <;> simp at h2
      · exfalso; rcases hpu with h1 | ⟨-, h2⟩
        · exact hpp1 h1
        · split_ifs at h2 <;> simp at h2
      · exfalso; rcases hpu with h1 | ⟨-, h2⟩
        · exact hpp1 h1
        · split_ifs at h2 with hk
          · simp at h2
          · exact absurd y.isLt (by omega)
      all_goals
        first
        | (exfalso; rcases hpu with h1 | ⟨h1, h2⟩
           · exact hpp2 ⟨by omega, by simp [hpc]⟩
           · revert h2; simp only [startPC]; split_ifs <;> simp)
        | skip
      all_goals
        rcases hpu with h1 | ⟨-, h2⟩
        · exact (hpp1 h1).elim
        obtain ⟨hρr, rfl⟩ := hupd m hm hpc h2 (by simp)
        have hf := I.finR_loc a.proc (by simp [hpc]) ⟨m, hm⟩
        have hU' : Unif s ((s.loc a.proc).r - 1) ⟨m, hm⟩ V := by
          have : (s.loc a.proc).r - 1 = ρ := by omega
          rw [this]; exact hUp
        by_cases hc : (s.loc a.proc).tag ⟨m, hm⟩ = true ∧ (s.loc a.proc).acop ⟨m, hm⟩ = V
        · first
          | (rw [← hc.2]; exact hin)
          | (simp [hc.2])
          | (exact absurd hc.1 (by simp [htag]))
        · have hne : s.finR (s.loc a.proc).r ⟨m, hm⟩ a.proc ≠ some (true, V) := by
            rw [hf]; intro e; simp at e; exact hc ⟨e.1, e.2⟩
          have hv := (B.CI a.proc ⟨m, hm⟩ V (by omega) (by simp [hpc]) hU' hne).2 (by simp [hpc])
          first
          | exact hv
          | simp [hv]
  · rw [loc_ne h hp] at hpu ⊢
    exact B.know p ρ y V hUp hpu

end Fields

end Podc.DistributedUniversality
