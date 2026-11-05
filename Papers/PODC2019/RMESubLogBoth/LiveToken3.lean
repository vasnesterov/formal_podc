import Papers.PODC2019.RMESubLogBoth.LiveToken2

/-!
# Liveness, part 3 (cont.): the rank under one step
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation Classical

/-- Phase 2 of a passage of `p` with node `yp`: lines 14, 15, 25, 26. -/
def Ph2 (c : Cfg k) (p : Fin k) (yp : ℕ) : Prop :=
  c.node p = some yp ∧
    ((∃ m, c.pc p = .l14 yp m) ∨ (∃ m, c.pc p = .l15 yp m) ∨ (∃ v, c.pc p = .l25 yp v) ∨
      c.pc p = .l26 yp)

section
variable {c c' : Cfg k} {own : ℕ → ℕ}

/-- In phase 2, `yp` is behind some node. -/
lemma Ph2.bh (hG : Glob c own) (hL : ∀ q, LI c own q) {p : Fin k} {yp : ℕ} (h : Ph2 c p yp) :
    ∃ m, c.Bh yp m := by
  obtain ⟨hn, h1 | h1 | h1 | h1⟩ := h
  · obtain ⟨m, hm⟩ := h1; exact ⟨m, p, hn, Cfg.vp_of_ovr_some (by simp [hm])⟩
  · obtain ⟨m, hm⟩ := h1
    have := hL p; unfold LI at this; rw [hm] at this
    exact ⟨m, bh_of_pred hG hL this.2.1⟩
  · obtain ⟨v, hm⟩ := h1
    have := hL p; unfold LI at this; rw [hm] at this
    obtain ⟨-, h2, ⟨m, rfl⟩, -⟩ := this
    exact ⟨m, bh_of_pred hG hL h2⟩
  · have := hL p; unfold LI at this; rw [h1] at this
    obtain ⟨-, ⟨m, h2, -⟩, -⟩ := this
    exact ⟨m, bh_of_pred hG hL h2⟩

/-- In phase 2, the holder of the right to the CS is `yp` or one of its ancestors. -/
lemma Ph2.holder (hG : Glob c own) (hL : ∀ q, LI c own q) (hNR : NoRec c) {p : Fin k} {yp : ℕ}
    (h : Ph2 c p yp) : ∃ s x, c.node s = some x ∧ c.InH x ∧ ReflTransGen c.Bh yp x := by
  obtain ⟨m, hm⟩ := h.bh hG hL
  obtain ⟨x, hx, hr⟩ := exists_holder hG hL hNR yp m hm
  obtain ⟨s, hs⟩ := hx.1
  exact ⟨s, x, hs, hx, hr⟩

lemma Ph2.not_l13 {p : Fin k} {yp : ℕ} (h : Ph2 c p yp) (x : ℕ) : c.pc p ≠ .l13 x := by
  obtain ⟨-, ⟨m, h1⟩ | ⟨m, h1⟩ | ⟨v, h1⟩ | h1⟩ := h <;> rw [h1] <;> simp

/-- `Bh` is functional. -/
lemma bh_fun (hG : Glob c own) {y z z' : ℕ} (h : c.Bh y z) (h' : c.Bh y z') : z = z' := by
  obtain ⟨j, hj, hv⟩ := h
  obtain ⟨j', hj', hv'⟩ := h'
  have := hG.node_inj hj hj'; subst this
  rw [hv] at hv'; cases hv'; rfl

/-- The holder at line 25 sees its predecessor released. -/
lemma HO.l25 (hG : Glob c own) (hL : ∀ q, LI c own q) {s : Fin k} {x m : ℕ}
    (hpc : c.pc s = .l25 x (.node m)) (hs : HO c s) : c.csig m = true := by
  obtain ⟨z, hz, ⟨-, hH⟩⟩ := hs
  have hLs := hL s; unfold LI at hLs; rw [hpc] at hLs
  rw [hLs.1] at hz; cases hz
  rcases hH with h | ⟨w, hw, hr⟩ | ⟨h, -⟩
  · rw [hLs.2.1] at h; cases h
  · have := bh_fun hG hw (bh_of_pred hG hL hLs.2.1); subst this; exact hr.2
  · rw [hLs.2.1] at h; cases h

/-- A non-holder at line 25 does not see its predecessor released. -/
lemma not_HO_l25 (hG : Glob c own) (hL : ∀ q, LI c own q) {s : Fin k} {x m : ℕ}
    (hpc : c.pc s = .l25 x (.node m)) (hs : ¬ HO c s) : c.csig m = false := by
  have hLs := hL s; unfold LI at hLs; rw [hpc] at hLs
  cases hc : c.csig m
  · rfl
  · exact absurd ⟨x, hLs.1, ⟨s, hLs.1⟩, .inr (.inl ⟨m, bh_of_pred hG hL hLs.2.1,
      hG.csigPred m hc, hc⟩)⟩ hs

/-- Steps that only change the program counter of `s` (keeping overrides). -/
lemma token_setPc {s : Fin k} {r : PC k} {own' : ℕ → ℕ} (hG : Glob c own)
    (hG' : Glob (c.setPc s r) own') {yp : ℕ} (ho : r.ovr = (c.pc s).ovr) (hlt : HO c s → HW r < HW (c.pc s)) :
    (¬ HO c s → tokMu (c.setPc s r) yp = tokMu c yp ∧ ∀ q, HO (c.setPc s r) q ↔ HO c q) ∧
      (HO c s → tokMu (c.setPc s r) yp < tokMu c yp) := by
  have hBh : (c.setPc s r).Bh = c.Bh := Bh_congr rfl (vp_setPc ho)
  have hH : (c.setPc s r).InH = c.InH := InH_setPc ho
  refine ⟨fun hs => tokMu_view_other rfl hBh rfl hH hs (fun j hj => by simp [hj]), fun hs => ?_⟩
  exact tokMu_view_owner hG hG' rfl hBh rfl hH hs (by simpa using hlt hs)

/-- A step that keeps nodes, `Bh`, `Rel` and `InH`. -/
lemma token_view {s : Fin k} {own' : ℕ → ℕ} (hG : Glob c own) (hG' : Glob c' own') {yp : ℕ}
    (hn : c'.node = c.node) (hBh : c'.Bh = c.Bh) (hRel : c'.Rel = c.Rel) (hH : c'.InH = c.InH)
    (hpc : ∀ j, j ≠ s → c'.pc j = c.pc j) (hlt : HO c s → HW (c'.pc s) < HW (c.pc s)) :
    (¬ HO c s → tokMu c' yp = tokMu c yp ∧ ∀ q, HO c' q ↔ HO c q) ∧
      (HO c s → tokMu c' yp < tokMu c yp) :=
  ⟨fun hs => tokMu_view_other hn hBh hRel hH hs hpc,
    fun hs => tokMu_view_owner hG hG' hn hBh hRel hH hs (hlt hs)⟩

lemma token_l14 (hG : Glob c own) (hL : ∀ q, LI c own q) {own' : ℕ → ℕ} {s : Fin k} {x m : ℕ}
    (h : c.pc s = .l14 x m) {yp : ℕ}
    (hc' : c' = { c with pred := Function.update c.pred x (.node m),
                         pc := Function.update c.pc s (.l15 x m) }) (hG' : Glob c' own') :
    (¬ HO c s → tokMu c' yp = tokMu c yp ∧ ∀ q, HO c' q ↔ HO c q) ∧
      (HO c s → tokMu c' yp < tokMu c yp) := by
  obtain ⟨hn, hx⟩ := (hL s).node_of_pc_l14 h
  have hnode : c'.node = c.node := by rw [hc']
  have hcsig : c'.csig = c.csig := by rw [hc']
  have htail : c'.tail = c.tail := by rw [hc']
  have hpcs : c'.pc s = .l15 x m := by rw [hc']; simp
  have hpco : ∀ j, j ≠ s → c'.pc j = c.pc j := fun j hj => by rw [hc']; simp [hj]
  have hpred : ∀ a, a ≠ x → c'.pred a = c.pred a := fun a ha => by rw [hc']; simp [ha]
  have hpx : c'.pred x = .node m := by rw [hc']; simp
  have hvp : ∀ j, c'.vp j = c.vp j := by
    intro j
    by_cases hj : j = s
    · subst hj
      rw [Cfg.vp_of_ovr_some (c := c) (m := m) (by simp [h]),
        Cfg.vp_of_ovr_none (c := c') (by simp [hpcs, PC.ovr]) (by rw [hnode]; exact hn), hpx]
    · exact vp_eq_other hG hn hj (hpco j hj) (by rw [hnode]) hpred
  have hBh : c'.Bh = c.Bh := Bh_congr hnode hvp
  have hp2 : ∀ a, c'.pred a = c.pred a ∨ ((c.pred a ≠ .incs ∧ c.pred a ≠ .exit) ∧
      (c'.pred a ≠ .incs ∧ c'.pred a ≠ .exit)) := by
    intro a
    by_cases ha : a = x
    · subst ha; right; simp [hpx, hx]
    · left; exact hpred a ha
  have hRel : c'.Rel = c.Rel := Rel_eq_of_pred hcsig (fun a => by
    rcases hp2 a with h1 | ⟨⟨-, h1⟩, -, h2⟩
    · exact .inl h1
    · exact .inr ⟨h1, h2⟩)
  have hH : c'.InH = c.InH := InH_eq_of_pred hnode hBh hRel htail hcsig hp2
  exact token_view hG hG' hnode hBh hRel hH hpco (fun _ => by simp [hpcs, h, HW])

lemma token_l15 (hG : Glob c own) {own' : ℕ → ℕ} {s : Fin k} {x m : ℕ}
    (h : c.pc s = .l15 x m) {yp : ℕ}
    (hc' : c' = { c with nn := Function.update c.nn x true,
                         pc := Function.update c.pc s (.l25 x (.node m)) }) (hG' : Glob c' own') :
    (¬ HO c s → tokMu c' yp = tokMu c yp ∧ ∀ q, HO c' q ↔ HO c q) ∧
      (HO c s → tokMu c' yp < tokMu c yp) := by
  have hnode : c'.node = c.node := by rw [hc']
  have hpred : c'.pred = c.pred := by rw [hc']
  have hcsig : c'.csig = c.csig := by rw [hc']
  have htail : c'.tail = c.tail := by rw [hc']
  have hpcs : c'.pc s = .l25 x (.node m) := by rw [hc']; simp
  have hpco : ∀ j, j ≠ s → c'.pc j = c.pc j := fun j hj => by rw [hc']; simp [hj]
  have hvp : ∀ j, c'.vp j = c.vp j := fun j => by
    refine vp_congr ?_ (by rw [hnode]) (fun _ _ => by rw [hpred])
    by_cases hj : j = s
    · subst hj; simp [hpcs, h, PC.ovr]
    · rw [hpco j hj]
  have hBh : c'.Bh = c.Bh := Bh_congr hnode hvp
  have hH : c'.InH = c.InH := InH_congr hnode hvp hpred hcsig htail
  exact token_view hG hG' hnode hBh (Rel_congr hpred hcsig) hH hpco
    (fun _ => by simp [hpcs, h, HW])

lemma tokMu_owner_lt {own' : ℕ → ℕ} (hG : Glob c own) (hG' : Glob c' own') {s : Fin k}
    {yp : ℕ} (ha : ∀ q, Anc c' yp q ↔ Anc c yp q) (hho : ∀ q, HO c' q ↔ HO c q) (hs : HO c s)
    (hlt : HW (c'.pc s) < HW (c.pc s)) : tokMu c' yp < tokMu c yp := by
  unfold tokMu
  rw [hstage_eq hG hs, hstage_eq hG' ((hho s).mpr hs)]
  have : (Finset.univ.filter (Anc c' yp)) = Finset.univ.filter (Anc c yp) := by
    ext q; simp [ha q]
  rw [this]; omega

/-- Line 26 (only the holder can execute it). -/
lemma token_l26 (hG : Glob c own) (hL : ∀ q, LI c own q) {own' : ℕ → ℕ} {s : Fin k} {x : ℕ}
    (h : c.pc s = .l26 x) {yp : ℕ}
    (hc' : c' = { c with pred := Function.update c.pred x .incs,
                         pc := Function.update c.pc s (.cs x) }) (hG' : Glob c' own') :
    HO c s ∧ (tokMu c' yp < tokMu c yp ∨ x = yp) := by
  have hLs := hL s; unfold LI at hLs; rw [h] at hLs
  obtain ⟨hn, ⟨m, hxm, hm⟩, -⟩ := hLs
  have hbxm : c.Bh x m := bh_of_pred hG hL hxm
  have hHx : c.InH x := ⟨⟨s, hn⟩, .inr (.inl ⟨m, hbxm, hm⟩)⟩
  have hs : HO c s := ⟨x, hn, hHx⟩
  refine ⟨hs, ?_⟩
  by_cases hxy : x = yp
  · exact .inr hxy
  left
  have hnode : c'.node = c.node := by rw [hc']
  have hcsig : c'.csig = c.csig := by rw [hc']
  have htail : c'.tail = c.tail := by rw [hc']
  have hpcs : c'.pc s = .cs x := by rw [hc']; simp
  have hpco : ∀ j, j ≠ s → c'.pc j = c.pc j := fun j hj => by rw [hc']; simp [hj]
  have hpred : ∀ a, a ≠ x → c'.pred a = c.pred a := fun a ha => by rw [hc']; simp [ha]
  have hpx : c'.pred x = .incs := by rw [hc']; simp
  have hvps : c'.vp s = .incs := by
    rw [Cfg.vp_of_ovr_none (c := c') (by simp [hpcs, PC.ovr]) (by rw [hnode]; exact hn), hpx]
  have hvpo : ∀ j, j ≠ s → c'.vp j = c.vp j := fun j hj =>
    vp_eq_other hG hn hj (hpco j hj) (by rw [hnode]) hpred
  have hBh : ∀ a b, c'.Bh a b ↔ c.Bh a b ∧ a ≠ x := by
    intro a b
    constructor
    · rintro ⟨j, hj, hv⟩
      rw [hnode] at hj
      by_cases hjs : j = s
      · subst hjs; rw [hvps] at hv; cases hv
      · refine ⟨⟨j, hj, by rwa [← hvpo j hjs]⟩, fun hax => hjs (hG.node_inj hj (hax ▸ hn))⟩
    · rintro ⟨⟨j, hj, hv⟩, hax⟩
      have hjs : j ≠ s := fun hjs => hax (by rw [hjs, hn] at hj; exact (Option.some.inj hj).symm)
      exact ⟨j, by rw [hnode]; exact hj, by rw [hvpo j hjs]; exact hv⟩
  have hRel : c'.Rel = c.Rel := Rel_eq_of_pred hcsig (fun a => by
    by_cases ha : a = x
    · subst ha; right; simp [hpx, hxm]
    · exact .inl (hpred a ha))
  have hH : ∀ y, c'.InH y ↔ c.InH y := by
    intro y
    by_cases hyx : y = x
    · subst hyx
      exact ⟨fun _ => hHx, fun _ => ⟨by rw [Cfg.Act, hnode]; exact ⟨s, hn⟩, .inl hpx⟩⟩
    · simp only [Cfg.InH, Cfg.Act, hnode, hpred y hyx, hcsig, htail, hRel]
      constructor
      · rintro ⟨h1, h2 | ⟨z, hz, hRz⟩ | ⟨h2, h3, h4⟩⟩
        · exact ⟨h1, .inl h2⟩
        · exact ⟨h1, .inr (.inl ⟨z, ((hBh y z).mp hz).1, hRz⟩)⟩
        · refine ⟨h1, .inr (.inr ⟨h2, h3, ?_⟩)⟩
          rcases h4 with ⟨w, hw⟩ | h4
          · exact .inl ⟨w, ((hBh w y).mp hw).1⟩
          · exact .inr h4
      · rintro ⟨h1, h2 | ⟨z, hz, hRz⟩ | ⟨h2, h3, h4⟩⟩
        · exact ⟨h1, .inl h2⟩
        · exact ⟨h1, .inr (.inl ⟨z, (hBh y z).mpr ⟨hz, hyx⟩, hRz⟩)⟩
        · refine ⟨h1, .inr (.inr ⟨h2, h3, ?_⟩)⟩
          rcases h4 with ⟨w, hw⟩ | h4
          · by_cases hwx : w = x
            · subst hwx
              have := bh_fun hG hw hbxm; subst this
              rw [hm.2] at h3; cases h3
            · exact .inl ⟨w, (hBh w y).mpr ⟨hw, hwx⟩⟩
          · exact .inr h4
  have hho : ∀ q, HO c' q ↔ HO c q := fun q => by simp only [HO, hnode, hH]
  have ha : ∀ q, Anc c' yp q ↔ Anc c yp q := by
    intro q
    simp only [Anc, hnode, hRel]
    constructor
    · rintro ⟨z, hz, hr, hRz⟩
      exact ⟨z, hz, TransGen.mono (fun a b hab => ((hBh a b).mp hab).1) _ _ hr, hRz⟩
    · rintro ⟨z, hz, hr, hRz⟩
      refine ⟨z, hz, ?_, hRz⟩
      clear hz
      induction hr with
      | single e =>
        refine .single ((hBh _ _).mpr ⟨e, fun hax => ?_⟩)
        subst hax; have := bh_fun hG e hbxm; subst this; exact hRz hm
      | @tail a z _ e ih =>
        refine .tail (ih (fun hRa => not_bh_of_rel hL hRa e)) ((hBh _ _).mpr ⟨e, fun hax => ?_⟩)
        subst hax; have := bh_fun hG e hbxm; subst this; exact hRz hm
  exact tokMu_owner_lt hG hG' ha hho hs (by simp [hpcs, h, HW])

end

end Podc.RMESubLogBoth
