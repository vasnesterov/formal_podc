import Papers.PODC2019.RMESubLogBoth.InvShared
import Papers.PODC2019.RMESubLogBoth.InvLocal

/-!
# Invariant preservation: steps of non-repairer lines
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

open Relation

/-- Line 14. -/
lemma inv_step_l14 {c : Cfg k} (hI : Inv c) (p : Fin k) (x m : ℕ) (h : c.pc p = .l14 x m) :
    Inv { c with pred := Function.update c.pred x (.node m),
                 pc := Function.update c.pc p (.l15 x m) } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨hn, hpx, hnnx, hcx⟩ := hLp
  set c' : Cfg k := { c with
    pred := Function.update c.pred x (.node m), pc := Function.update c.pc p (.l15 x m) }
  have hpred : ∀ a, a ≠ x → c'.pred a = c.pred a := fun a ha => by simp [c', ha]
  have hpc : ∀ j, j ≠ p → c'.pc j = c.pc j := fun j hj => by simp [c', hj]
  have hvp : ∀ j, c'.vp j = c.vp j := by
    intro j
    by_cases hjp : j = p
    · subst hjp
      rw [Cfg.vp_of_ovr_some (by simp [h] : (c.pc j).ovr = some m),
        Cfg.vp_of_ovr_none (by simp [c', PC.ovr]) (by simpa [c'] using hn)]
      simp [c']
    · exact vp_eq_other hG hn hjp (hpc j hjp) rfl hpred
  have hBh : c'.Bh = c.Bh := Bh_congr rfl hvp
  have hpred' : ∀ a, c'.pred a = c.pred a ∨ ((c.pred a ≠ .incs ∧ c.pred a ≠ .exit) ∧
      (c'.pred a ≠ .incs ∧ c'.pred a ≠ .exit)) := by
    intro a
    by_cases hax : a = x
    · subst hax; right; simp [c', hpx]
    · exact .inl (hpred a hax)
  have hRel : c'.Rel = c.Rel := Rel_eq_of_pred rfl (fun a => by
    rcases hpred' a with h1 | ⟨⟨-, h1⟩, -, h2⟩
    · exact .inl h1
    · exact .inr ⟨h1, h2⟩)
  have hInH : c'.InH = c.InH := InH_eq_of_pred rfl hBh hRel rfl rfl hpred'
  refine inv_of_local hG hL hn (fun _ _ => rfl) (.inl rfl) rfl rfl hpred (fun _ _ => rfl)
    (fun _ _ => rfl) hpc (by simp [c']) ?_ (by rw [hRel]; exact fun _ h => h) (fun _ h => h)
    (by rw [hBh]; exact fun _ _ h => h) (fun j v h => by rwa [hvp] at h) (by simp [c'])
    (fun h => by simp [c'] at h ⊢; rw [hcx] at h; cases h)
    (by simp [c']) (by rw [hInH]; exact hG.hUniq) (by rw [hRel, hInH]; exact hG.relTail)
    ?_ (hInH_of_sub (by rw [hInH]; exact fun _ h => h) p) (hcs_of_incs ?_ p) ?_
  · intro a
    by_cases hax : a = x
    · subst hax; right; left; simp [c', hpx]
    · exact .inl (hpred a hax)
  · intro j hj
    by_cases hjp : j = p
    · subst hjp; simp [c', PC.InR] at hj
    · rw [hpc j hjp] at hj; exact hG.holder j hj
  · intro a ha
    by_cases hax : a = x
    · subst hax; rw [hpx] at ha; cases ha
    · rw [hpred a hax, ha]; simp
  · unfold LI; simp [c', hn, hnnx, hcx]


/-- Holder condition for steps that do not touch `holder` and move `p` out of `RLock`'s CS. -/
lemma hold_of_out {c c' : Cfg k} {own : ℕ → ℕ} (hG : Glob c own) {p : Fin k}
    (hpc : ∀ j, j ≠ p → c'.pc j = c.pc j) (hp : ¬ (c'.pc p).InR)
    (hh : c'.holder = c.holder) : ∀ j, (c'.pc j).InR → c'.holder = some j := by
  intro j hj
  by_cases hjp : j = p
  · subst hjp; exact absurd hj hp
  · rw [hpc j hjp] at hj; rw [hh]; exact hG.holder j hj

/-- Line 15. -/
lemma inv_step_l15 {c : Cfg k} (hI : Inv c) (p : Fin k) (x m : ℕ) (h : c.pc p = .l15 x m) :
    Inv { c with nn := Function.update c.nn x true,
                 pc := Function.update c.pc p (.l25 x (.node m)) } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨hn, hpx, hnnx, hcx⟩ := hLp
  set c' : Cfg k := { c with
    nn := Function.update c.nn x true, pc := Function.update c.pc p (.l25 x (.node m)) }
  have hpc : ∀ j, j ≠ p → c'.pc j = c.pc j := fun j hj => by simp [c', hj]
  have hvp : ∀ j, c'.vp j = c.vp j := vp_eq_all rfl rfl (fun j => by
    by_cases hjp : j = p
    · subst hjp; simp [c', h, PC.ovr]
    · rw [hpc j hjp])
  have hBh : c'.Bh = c.Bh := Bh_congr rfl hvp
  have hRel : c'.Rel = c.Rel := Rel_congr rfl rfl
  have hInH : c'.InH = c.InH := InH_congr rfl hvp rfl rfl rfl
  refine inv_of_local hG hL hn (fun _ _ => rfl) (.inl rfl) rfl rfl (fun _ _ => rfl)
    (fun a ha => by simp [c', ha]) (fun _ _ => rfl) hpc (by simp [c']) (PredStep.of_eq rfl)
    (by rw [hRel]; exact fun _ h => h)
    (fun a ha => by by_cases hax : a = x <;> simp [c', hax, ha])
    (by rw [hBh]; exact fun _ _ h => h) (fun j v h => by rwa [hvp] at h)
    (fun _ => by simp [c', hpx]) (fun h => by simp [c', hcx] at h)
    (fun _ => by simp [c']) (by rw [hInH]; exact hG.hUniq)
    (by rw [hRel, hInH]; exact hG.relTail)
    (hold_of_out hG hpc (by simp [c', PC.InR]) rfl)
    (hInH_of_sub (by rw [hInH]; exact fun _ h => h) p)
    (hcs_of_incs (fun a ha => by simp [c', ha]) p) ?_
  unfold LI; simp [c', hn, hpx]

/-- Line 23. -/
lemma inv_step_l23 {c : Cfg k} (hI : Inv c) (p : Fin k) (x : ℕ) (v : PV) (h : c.pc p = .l23 x v) :
    Inv { c with nn := Function.update c.nn x true,
                 pc := Function.update c.pc p (.l24 x v) } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨hn, hpx, hv⟩ := hLp
  set c' : Cfg k := { c with
    nn := Function.update c.nn x true, pc := Function.update c.pc p (.l24 x v) }
  have hpc : ∀ j, j ≠ p → c'.pc j = c.pc j := fun j hj => by simp [c', hj]
  have hvp : ∀ j, c'.vp j = c.vp j := vp_eq_all rfl rfl (fun j => by
    by_cases hjp : j = p
    · subst hjp; simp [c', h, PC.ovr]
    · rw [hpc j hjp])
  have hBh : c'.Bh = c.Bh := Bh_congr rfl hvp
  have hRel : c'.Rel = c.Rel := Rel_congr rfl rfl
  have hInH : c'.InH = c.InH := InH_congr rfl hvp rfl rfl rfl
  have hpn : c.pred x ≠ .nil := by rw [hpx]; rcases hv with rfl | ⟨m, rfl⟩ <;> simp
  refine inv_of_local hG hL hn (fun _ _ => rfl) (.inl rfl) rfl rfl (fun _ _ => rfl)
    (fun a ha => by simp [c', ha]) (fun _ _ => rfl) hpc (by simp [c']) (PredStep.of_eq rfl)
    (by rw [hRel]; exact fun _ h => h)
    (fun a ha => by by_cases hax : a = x <;> simp [c', hax, ha])
    (by rw [hBh]; exact fun _ _ h => h) (fun j v h => by rwa [hvp] at h)
    (fun _ => hpn) (fun h => hG.csigPred x h)
    (fun _ => by simp [c']) (by rw [hInH]; exact hG.hUniq)
    (by rw [hRel, hInH]; exact hG.relTail)
    (hold_of_out hG hpc (by simp [c', PC.InR]) rfl)
    (hInH_of_sub (by rw [hInH]; exact fun _ h => h) p)
    (hcs_of_incs (fun a ha => by simp [c', ha]) p) ?_
  unfold LI; simp [c', hn, hpx]; exact hv

/-- Line 18 (write). -/
lemma inv_step_l18w {c : Cfg k} (hI : Inv c) (p : Fin k) (x : ℕ) (h : c.pc p = .l18w x) :
    Inv { c with pred := Function.update c.pred x .crash,
                 pc := Function.update c.pc p (.l19 x) } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨hn, hpx⟩ := hLp
  set c' : Cfg k := { c with
    pred := Function.update c.pred x .crash, pc := Function.update c.pc p (.l19 x) }
  have hpred : ∀ a, a ≠ x → c'.pred a = c.pred a := fun a ha => by simp [c', ha]
  have hpc : ∀ j, j ≠ p → c'.pc j = c.pc j := fun j hj => by simp [c', hj]
  have hvp : ∀ j v, c'.vp j = .node v ↔ c.vp j = .node v := by
    intro j v
    by_cases hjp : j = p
    · subst hjp
      rw [Cfg.vp_of_ovr_none (by simp [h, PC.ovr]) hn,
        Cfg.vp_of_ovr_none (by simp [c', PC.ovr]) (by simpa [c'] using hn)]
      simp [c', hpx]
    · rw [vp_eq_other hG hn hjp (hpc j hjp) rfl hpred]
  have hBh : c'.Bh = c.Bh := by
    funext a b; apply propext; constructor <;> rintro ⟨j, h1, h2⟩
    · exact ⟨j, h1, (hvp j b).mp h2⟩
    · exact ⟨j, h1, (hvp j b).mpr h2⟩
  have hpred' : ∀ a, c'.pred a = c.pred a ∨ ((c.pred a ≠ .incs ∧ c.pred a ≠ .exit) ∧
      (c'.pred a ≠ .incs ∧ c'.pred a ≠ .exit)) := by
    intro a
    by_cases hax : a = x
    · subst hax; right; simp [c', hpx]
    · exact .inl (hpred a hax)
  have hRel : c'.Rel = c.Rel := Rel_eq_of_pred rfl (fun a => by
    rcases hpred' a with h1 | ⟨⟨-, h1⟩, -, h2⟩
    · exact .inl h1
    · exact .inr ⟨h1, h2⟩)
  have hInH : c'.InH = c.InH := InH_eq_of_pred rfl hBh hRel rfl rfl hpred'
  refine inv_of_local hG hL hn (fun _ _ => rfl) (.inl rfl) rfl rfl hpred (fun _ _ => rfl)
    (fun _ _ => rfl) hpc (by simp [c']) ?_ (by rw [hRel]; exact fun _ h => h) (fun _ h => h)
    (by rw [hBh]; exact fun _ _ h => h) (fun j v h => (hvp j v).mp h) (by simp [c'])
    (fun h => absurd (hG.csigPred x h) (by rw [hpx]; simp)) (by simp [c'])
    (by rw [hInH]; exact hG.hUniq) (by rw [hRel, hInH]; exact hG.relTail)
    (hold_of_out hG hpc (by simp [c', PC.InR]) rfl)
    (hInH_of_sub (by rw [hInH]; exact fun _ h => h) p) (hcs_of_incs ?_ p) ?_
  · intro a
    by_cases hax : a = x
    · subst hax; right; left; simp [c', hpx]
    · exact .inl (hpred a hax)
  · intro a ha
    by_cases hax : a = x
    · subst hax; rw [hpx] at ha; cases ha
    · rw [hpred a hax, ha]; simp
  · unfold LI; simp [c', hn]


/-- Line 26. -/
lemma inv_step_l26 {c : Cfg k} (hI : Inv c) (p : Fin k) (x : ℕ) (h : c.pc p = .l26 x) :
    Inv { c with pred := Function.update c.pred x .incs,
                 pc := Function.update c.pc p (.cs x) } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨hn, ⟨m, hpx, hRm⟩, hnnx⟩ := hLp
  set c' : Cfg k := { c with
    pred := Function.update c.pred x .incs, pc := Function.update c.pc p (.cs x) }
  have hpred : ∀ a, a ≠ x → c'.pred a = c.pred a := fun a ha => by simp [c', ha]
  have hpc : ∀ j, j ≠ p → c'.pc j = c.pc j := fun j hj => by simp [c', hj]
  have hvp : ∀ j v, c'.vp j = .node v → c.vp j = .node v := by
    intro j v hj
    by_cases hjp : j = p
    · subst hjp
      rw [Cfg.vp_of_ovr_none (by simp [c', PC.ovr]) (by simpa [c'] using hn)] at hj
      simp [c'] at hj
    · rwa [vp_eq_other hG hn hjp (hpc j hjp) rfl hpred] at hj
  have hBh := Bh_sub_of (c := c) (c' := c') (fun _ _ h => h) hvp
  have hRel : c'.Rel = c.Rel := Rel_eq_of_pred rfl (fun a => by
    by_cases hax : a = x
    · subst hax; right; simp [c', hpx]
    · exact .inl (hpred a hax))
  have hInH : ∀ y, c'.InH y → c.InH y := by
    intro y hy
    by_cases hyx : y = x
    · subst hyx; exact ⟨⟨p, hn⟩, .inr (.inl ⟨m, bh_of_pred hG hL hpx, hRm⟩)⟩
    · exact InH_sub_of (c := c) (c' := c') (fun _ _ h => h) hBh
        (by rw [hRel]; exact fun _ h => h) rfl (hpred y hyx) rfl hy
  refine inv_of_local hG hL hn (fun _ _ => rfl) (.inl rfl) rfl rfl hpred (fun _ _ => rfl)
    (fun _ _ => rfl) hpc (by simp [c']) ?_ (by rw [hRel]; exact fun _ h => h) (fun _ h => h)
    hBh hvp (by simp [c'])
    (fun h => absurd (hG.csigPred x h) (by rw [hpx]; simp)) (fun _ => hnnx)
    (fun y y' h1 h2 => hG.hUniq y y' (hInH y h1) (hInH y' h2))
    (fun h1 y h2 => hG.relTail (by rw [← hRel]; exact h1) y (hInH y h2))
    (hold_of_out hG hpc (by simp [c', PC.InR]) rfl)
    (hInH_of_sub hInH p) (hcs_of_incs ?_ p) ?_
  · intro a
    by_cases hax : a = x
    · subst hax; right; right; right
      exact ⟨m, hpx, bh_of_pred hG hL hpx, hRm, by simp [c']⟩
    · exact .inl (hpred a hax)
  · intro a ha
    by_cases hax : a = x
    · subst hax; simp [c']
    · rw [hpred a hax, ha]; simp
  · unfold LI; simp [c', hn, hnnx]

/-- Line 27 (the step of a process in the CS). -/
lemma inv_step_cs {c : Cfg k} (hI : Inv c) (p : Fin k) (x : ℕ) (h : c.pc p = .cs x) :
    Inv { c with pred := Function.update c.pred x .exit,
                 pc := Function.update c.pc p (.l28 x) } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨hn, hpx, hnnx⟩ := hLp
  have hcx : c.csig x = false := by
    cases hc : c.csig x
    · rfl
    · exact absurd (hG.csigPred x hc) (by rw [hpx]; simp)
  set c' : Cfg k := { c with
    pred := Function.update c.pred x .exit, pc := Function.update c.pc p (.l28 x) }
  have hpred : ∀ a, a ≠ x → c'.pred a = c.pred a := fun a ha => by simp [c', ha]
  have hpc : ∀ j, j ≠ p → c'.pc j = c.pc j := fun j hj => by simp [c', hj]
  have hvp : ∀ j v, c'.vp j = .node v → c.vp j = .node v := by
    intro j v hj
    by_cases hjp : j = p
    · subst hjp
      rw [Cfg.vp_of_ovr_none (by simp [c', PC.ovr]) (by simpa [c'] using hn)] at hj
      simp [c'] at hj
    · rwa [vp_eq_other hG hn hjp (hpc j hjp) rfl hpred] at hj
  have hBh := Bh_sub_of (c := c) (c' := c') (fun _ _ h => h) hvp
  have hRel : c'.Rel = c.Rel := by
    funext z
    by_cases hzx : z = x
    · subst hzx; simp [Cfg.Rel, c', hpx, hcx]
    · simp [Cfg.Rel, c', hzx]
  have hInHx : c.InH x := ⟨⟨p, hn⟩, .inl hpx⟩
  have hInH : ∀ y, y ≠ x → c'.InH y → c.InH y := fun y hyx hy =>
    InH_sub_of (c := c) (c' := c') (fun _ _ h => h) hBh (by rw [hRel]; exact fun _ h => h) rfl
      (hpred y hyx) rfl hy
  have hInH' : ∀ y, c'.InH y → c.InH y := by
    intro y hy
    by_cases hyx : y = x
    · subst hyx; exact hInHx
    · exact hInH y hyx hy
  refine inv_of_local hG hL hn (fun _ _ => rfl) (.inl rfl) rfl rfl hpred (fun _ _ => rfl)
    (fun _ _ => rfl) hpc (by simp [c']) ?_ (by rw [hRel]; exact fun _ h => h) (fun _ h => h)
    hBh hvp (by simp [c']) (fun _ => by simp [c']) (fun _ => hnnx)
    (fun y y' h1 h2 => hG.hUniq y y' (hInH' y h1) (hInH' y' h2))
    (fun h1 y h2 => hG.relTail (by rw [← hRel]; exact h1) y (hInH' y h2))
    (hold_of_out hG hpc (by simp [c', PC.InR]) rfl)
    (hInH_of_sub hInH' p) ?_ ?_
  · intro a
    by_cases hax : a = x
    · subst hax; right; right; left; simp [c', hpx]
    · exact .inl (hpred a hax)
  · intro q _ _ x' tl V E EA mp tp hp dn hS hP σ hσ h1 h2 hA y hy
    have hsx : pstart σ = x := by
      by_contra hne; rw [hpred _ hne, h1] at h2; cases h2
    obtain ⟨hmax, hio, -⟩ := hP.hp σ hσ
    obtain ⟨-, -, hnb, htl⟩ := hS.attach_hp hG hL hP hA hmax hio
    rw [hsx] at hnb htl
    by_cases hyx : y = x
    · subst hyx
      obtain ⟨-, h3 | ⟨z, hz, -⟩ | ⟨-, -, ⟨w, hw⟩ | ht⟩⟩ := hy
      · simp [c'] at h3
      · rcases pred_of_bh hL (hBh _ _ hz) with h4 | ⟨_, _, _, h4⟩ | ⟨_, _, _, h4⟩ <;>
          rw [hpx] at h4 <;> cases h4
      · exact hnb w (hBh _ _ hw)
      · exact htl ht
    · exact hyx (hG.hUniq y x (hInH y hyx hy) hInHx)
  · unfold LI; simp [c', hn, hnnx, hcx]


/-- Setting `CS_Signal` of `p`'s node `x` with `Pred x = &Exit` (lines 22 and 28). -/
lemma inv_csig_step {c : Cfg k} {own : ℕ → ℕ} (hG : Glob c own) (hL : ∀ j, LI c own j)
    {p : Fin k} {x : ℕ} (hn : c.node p = some x) (hpx : c.pred x = .exit)
    (hov : (c.pc p).ovr = none) {r : PC k} (hr : r.ovr = none) (hrR : ¬ r.InR)
    (hr13 : ∀ a, r ≠ .l13 a)
    (hself : LI { c with csig := Function.update c.csig x true,
                         pc := Function.update c.pc p r } own p) :
    Inv { c with csig := Function.update c.csig x true, pc := Function.update c.pc p r } := by
  set c' : Cfg k := { c with csig := Function.update c.csig x true, pc := Function.update c.pc p r }
  have hcsig : ∀ a, a ≠ x → c'.csig a = c.csig a := fun a ha => by simp [c', ha]
  have hpc : ∀ j, j ≠ p → c'.pc j = c.pc j := fun j hj => by simp [c', hj]
  have hvp : ∀ j, c'.vp j = c.vp j := vp_eq_all rfl rfl (fun j => by
    by_cases hjp : j = p
    · subst hjp; simp [c', hov, hr]
    · rw [hpc j hjp])
  have hBh : c'.Bh = c.Bh := Bh_congr rfl hvp
  have hnoBhx : ∀ z, ¬ c.Bh x z := fun z hz => by
    rcases pred_of_bh hL hz with h4 | ⟨_, _, _, h4⟩ | ⟨_, _, _, h4⟩ <;> rw [hpx] at h4 <;> cases h4
  have hRel' : ∀ z, c'.Rel z → c.Rel z ∨ (z = x ∧ c.csig x = false) := by
    rintro z ⟨h1, h2⟩
    by_cases hzx : z = x
    · subst hzx
      cases hc : c.csig z
      · exact .inr ⟨rfl, rfl⟩
      · exact .inl ⟨h1, hc⟩
    · rw [hcsig z hzx] at h2; exact .inl ⟨h1, h2⟩
  have hRel : ∀ z, c.Rel z → c'.Rel z := by
    rintro z ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_cases hzx : z = x
    · subst hzx; simp [c']
    · rw [hcsig z hzx]; exact h2
  have hInH' : ∀ y, c'.InH y → y ≠ x ∧ (c.InH y ∨ (c.Bh y x ∧ c.InH x)) := by
    intro y hy
    obtain ⟨⟨j, hj⟩, h1 | ⟨z, hz, hRz⟩ | ⟨h1, h2, h3⟩⟩ := hy
    · refine ⟨fun hyx => ?_, .inl ⟨⟨j, hj⟩, .inl h1⟩⟩
      subst hyx; rw [show c'.pred y = c.pred y from rfl, hpx] at h1; cases h1
    · rw [hBh] at hz
      refine ⟨fun hyx => hnoBhx z (hyx ▸ hz), ?_⟩
      rcases hRel' z hRz with h4 | ⟨rfl, h4⟩
      · exact .inl ⟨⟨j, hj⟩, .inr (.inl ⟨z, hz, h4⟩)⟩
      · exact .inr ⟨hz, ⟨p, hn⟩, .inr (.inr ⟨hpx, h4, .inl ⟨y, hz⟩⟩)⟩
    · have hyx : y ≠ x := by rintro rfl; simp [c'] at h2
      refine ⟨hyx, .inl ⟨⟨j, hj⟩, .inr (.inr ⟨h1, by rwa [← hcsig y hyx], ?_⟩)⟩⟩
      rwa [hBh] at h3
  refine inv_of_local hG hL hn (fun _ _ => rfl) (.inl rfl) rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) hcsig hpc (by simp [c', hr13]) (PredStep.of_eq rfl) hRel (fun _ h => h)
    (by rw [hBh]; exact fun _ _ h => h) (fun j v h => by rwa [hvp] at h)
    (fun _ => by simp [c', hpx]) (fun _ => hpx) (fun _ => hG.ioNN x (.inr hpx)) ?_ ?_
    (hold_of_out hG hpc (by simp [c', hrR]) rfl) ?_ (hcs_of_incs (fun a ha => by simp [c', ha]) p)
    hself
  · intro y y' h1 h2
    obtain ⟨hyx, h1 | ⟨h1, h1'⟩⟩ := hInH' y h1 <;> obtain ⟨hyx', h2 | ⟨h2, h2'⟩⟩ := hInH' y' h2
    · exact hG.hUniq y y' h1 h2
    · exact absurd (hG.hUniq y x h1 h2') hyx
    · exact absurd (hG.hUniq y' x h2 h1') hyx'
    · exact hG.bhInj y y' x h1 h2
  · intro ht y hy
    obtain ⟨hyx, h1 | ⟨h1, h1'⟩⟩ := hInH' y hy
    · rcases hRel' _ ht with h2 | ⟨h2, h3⟩
      · exact hG.relTail h2 y h1
      · have hx : c.InH x := ⟨⟨p, hn⟩, .inr (.inr ⟨hpx, h3, .inr h2⟩)⟩
        exact hyx (hG.hUniq y x h1 hx)
    · rcases hRel' _ ht with h2 | ⟨h2, -⟩
      · exact hG.relTail h2 x h1'
      · exact hG.noBhTail y (by rw [show c.tail = x from h2]; exact h1)
  · intro q _ _ x' tl V E EA mp tp hp dn _ _ _ h1 y hy
    obtain ⟨-, h2 | ⟨-, h2⟩⟩ := hInH' y hy
    · exact h1 y h2
    · exact h1 x h2

/-- Line 22 (line 28 of the inner exit). -/
lemma inv_step_l22a {c : Cfg k} (hI : Inv c) (p : Fin k) (x : ℕ) (h : c.pc p = .l22a x) :
    Inv { c with csig := Function.update c.csig x true,
                 pc := Function.update c.pc p .l22b } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨hn, hpx⟩ := hLp
  refine inv_csig_step hG hL hn hpx (by simp [h, PC.ovr]) rfl (by simp [PC.InR]) (by simp) ?_
  unfold LI; simp only [Function.update_self]
  exact ⟨x, hn, hpx, by simp⟩

/-- Line 28. -/
lemma inv_step_l28 {c : Cfg k} (hI : Inv c) (p : Fin k) (x : ℕ) (h : c.pc p = .l28 x) :
    Inv { c with csig := Function.update c.csig x true,
                 pc := Function.update c.pc p .l29 } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨hn, hpx, -, -⟩ := hLp
  refine inv_csig_step hG hL hn hpx (by simp [h, PC.ovr]) rfl (by simp [PC.InR]) (by simp) ?_
  unfold LI; simp only [Function.update_self]
  exact ⟨x, hn, hpx, by simp⟩


/-- A step that changes only `holder` and the program counter of `p` (keeping `ovr = none`). -/
lemma inv_holder_step {c : Cfg k} {own : ℕ → ℕ} (hG : Glob c own) (hL : ∀ j, LI c own j)
    {p : Fin k} {x : ℕ} (hn : c.node p = some x) (hov : (c.pc p).ovr = none) {r : PC k}
    (hr : r.ovr = none) (hr13 : ∀ a, r ≠ .l13 a) (o : Option (Fin k))
    (hhold : ∀ j, (Function.update c.pc p r j).InR → o = some j)
    (hself : LI { c with holder := o, pc := Function.update c.pc p r } own p) :
    Inv { c with holder := o, pc := Function.update c.pc p r } := by
  set c' : Cfg k := { c with holder := o, pc := Function.update c.pc p r }
  have hpc : ∀ j, j ≠ p → c'.pc j = c.pc j := fun j hj => by simp [c', hj]
  have hvp : ∀ j, c'.vp j = c.vp j := vp_eq_all rfl rfl (fun j => by
    by_cases hjp : j = p
    · subst hjp; simp [c', hov, hr]
    · rw [hpc j hjp])
  have hBh : c'.Bh = c.Bh := Bh_congr rfl hvp
  have hRel : c'.Rel = c.Rel := Rel_congr rfl rfl
  have hInH : c'.InH = c.InH := InH_congr rfl hvp rfl rfl rfl
  exact inv_of_local hG hL hn (fun _ _ => rfl) (.inl rfl) rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) hpc (by simp [c', hr13]) (PredStep.of_eq rfl)
    (by rw [hRel]; exact fun _ h => h) (fun _ h => h)
    (by rw [hBh]; exact fun _ _ h => h) (fun j v h => by rwa [hvp] at h)
    (fun h => hG.nnPred x h) (fun h => hG.csigPred x h) (fun h => hG.ioNN x h)
    (by rw [hInH]; exact hG.hUniq) (by rw [hRel, hInH]; exact hG.relTail) hhold
    (hInH_of_sub (by rw [hInH]; exact fun _ h => h) p)
    (hcs_of_incs (fun a ha => by simp [c', ha]) p) hself

/-- Line 24: acquire `RLock`. -/
lemma inv_step_l24_acq {c : Cfg k} (hI : Inv c) (p : Fin k) (x : ℕ) (v : PV)
    (h : c.pc p = .l24 x v) (hl : c.holder = none ∨ c.holder = some p) :
    Inv { c with holder := some p, pc := Function.update c.pc p (.l30 x v) } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨hn, hpx, hv, hnnx⟩ := hLp
  refine inv_holder_step hG hL hn (by simp [h, PC.ovr]) rfl (by simp) _ ?_ ?_
  · intro j hj
    by_cases hjp : j = p
    · rw [hjp]
    · simp [hjp] at hj
      rcases hl with hl | hl <;> rw [hG.holder j hj] at hl <;> cases hl
      exact absurd rfl hjp
  · unfold LI; simp only [Function.update_self]
    exact ⟨hn, hpx, hv, hnnx⟩

/-- Exit section of `RLock`. -/
lemma inv_step_rx {c : Cfg k} (hI : Inv c) (p : Fin k) (x : ℕ) (v : PV) (h : c.pc p = .rx x v) :
    Inv { c with holder := none, pc := Function.update c.pc p (.l25 x v) } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨hn, hpx, hv, hnnx⟩ := hLp
  refine inv_holder_step hG hL hn (by simp [h, PC.ovr]) rfl (by simp) _ ?_ ?_
  · intro j hj
    by_cases hjp : j = p
    · subst hjp; simp [PC.InR] at hj
    · simp [hjp] at hj
      have h1 := hG.holder j hj
      rw [hG.holder p (by rw [h]; trivial)] at h1
      cases h1; exact absurd rfl hjp
  · unfold LI; simp only [Function.update_self]
    exact ⟨hn, hpx, hv, hnnx⟩

/-- `Node[p] ← NIL` for a released node (lines 22 and 29). -/
lemma inv_release_step {c : Cfg k} {own : ℕ → ℕ} (hG : Glob c own) (hL : ∀ j, LI c own j)
    {p : Fin k} {x : ℕ} (hn : c.node p = some x) (hRx : c.Rel x)
    (hov : (c.pc p).ovr = none) {r : PC k} (hr : r.ovr = none) (hrR : ¬ r.InR)
    (hr13 : ∀ a, r ≠ .l13 a)
    (hself : LI { c with node := Function.update c.node p none,
                         pc := Function.update c.pc p r } own p) :
    Inv { c with node := Function.update c.node p none, pc := Function.update c.pc p r } := by
  set c' : Cfg k := { c with node := Function.update c.node p none,
                             pc := Function.update c.pc p r }
  have hpc : ∀ j, j ≠ p → c'.pc j = c.pc j := fun j hj => by simp [c', hj]
  have hnodeq : ∀ j, j ≠ p → c'.node j = c.node j := fun j hj => by simp [c', hj]
  have hnsub : ∀ j a, c'.node j = some a → c.node j = some a := by
    intro j a hj
    by_cases hjp : j = p
    · subst hjp; simp [c'] at hj
    · rwa [← hnodeq j hjp]
  have hvp : ∀ j v, c'.vp j = .node v → c.vp j = .node v := by
    intro j v hj
    by_cases hjp : j = p
    · subst hjp; simp [Cfg.vp, c', hr] at hj
    · rwa [vp_congr (by rw [hpc j hjp]) (hnodeq j hjp) (fun _ _ => rfl)] at hj
  have hBh := Bh_sub_of hnsub hvp
  have hInH : ∀ y, c'.InH y → c.InH y := fun y hy =>
    InH_sub_of hnsub hBh (fun _ h => h) rfl rfl rfl hy
  exact inv_of_local hG hL hn hnodeq (.inr ⟨by simp [c'], hRx⟩) rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) hpc (by simp [c', hr13]) (PredStep.of_eq rfl)
    (fun _ h => h) (fun _ h => h) hBh hvp
    (fun h => hG.nnPred x h) (fun h => hG.csigPred x h) (fun h => hG.ioNN x h)
    (fun y y' h1 h2 => hG.hUniq y y' (hInH y h1) (hInH y' h2))
    (fun h1 y h2 => hG.relTail h1 y (hInH y h2))
    (hold_of_out hG hpc (by simp [c', hrR]) rfl) (hInH_of_sub hInH p)
    (hcs_of_incs (fun a ha => by simp [c', ha]) p) hself

/-- Line 22 (line 29 of the inner exit), then back to line 10. -/
lemma inv_step_l22b {c : Cfg k} (hI : Inv c) (p : Fin k) (h : c.pc p = .l22b) :
    Inv { c with node := Function.update c.node p none, pc := Function.update c.pc p .l10 } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨x, hn, hRx⟩ := hLp
  refine inv_release_step hG hL hn hRx (by simp [h, PC.ovr]) rfl (by simp [PC.InR]) (by simp) ?_
  unfold LI; simp

/-- Line 29. -/
lemma inv_step_l29 {c : Cfg k} (hI : Inv c) (p : Fin k) (h : c.pc p = .l29) :
    Inv { c with node := Function.update c.node p none, pc := Function.update c.pc p .rem } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨x, hn, hRx⟩ := hLp
  refine inv_release_step hG hL hn hRx (by simp [h, PC.ovr]) rfl (by simp [PC.InR]) (by simp) ?_
  unfold LI; simp


/-! ### Steps that only change the program counter -/

/-- Line 10, `Node[p] = NIL`. -/
lemma inv_step_l10_nil {c : Cfg k} (hI : Inv c) (p : Fin k) (h : c.pc p = .rem ∨ c.pc p = .l10)
    (hn : c.node p = none) : Inv (c.setPc p .l11) := by
  obtain ⟨own, hG, hL⟩ := hI
  refine inv_setPc hG hL ?_ (by simp) (by simp [PC.InR]) ?_
  · rcases h with h | h <;> simp [h, PC.ovr]
  · unfold LI; simpa using hn

/-- Lines 10, 16–17, `Node[p] ≠ NIL`. -/
lemma inv_step_l10_some {c : Cfg k} (hI : Inv c) (p : Fin k) (h : c.pc p = .rem ∨ c.pc p = .l10)
    (x : ℕ) (hn : c.node p = some x) : Inv (c.setPc p (.l18 x)) := by
  obtain ⟨own, hG, hL⟩ := hI
  refine inv_setPc hG hL ?_ (by simp) (by simp [PC.InR]) ?_
  · rcases h with h | h <;> simp [h, PC.ovr]
  · unfold LI; simpa using hn

/-- Line 18 (read). -/
lemma inv_step_l18 {c : Cfg k} (hI : Inv c) (p : Fin k) (x : ℕ) (h : c.pc p = .l18 x) :
    Inv (c.setPc p (if c.pred x = .nil then .l18w x else .l19 x)) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  by_cases hpx : c.pred x = .nil
  · simp only [hpx, ↓reduceIte]
    refine inv_setPc hG hL (by simp [h, PC.ovr]) (by simp) (by simp [PC.InR]) ?_
    unfold LI; simp [hLp, hpx]
  · simp only [hpx, ↓reduceIte]
    refine inv_setPc hG hL (by simp [h, PC.ovr]) (by simp) (by simp [PC.InR]) ?_
    unfold LI; simp [hLp, hpx]

/-- Lines 19–21. -/
lemma inv_step_l19 {c : Cfg k} (hI : Inv c) (p : Fin k) (x : ℕ) (h : c.pc p = .l19 x) :
    Inv (c.setPc p (match c.pred x with
        | .incs => .cs x
        | .exit => .l22a x
        | v => .l23 x v)) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨hn, hpx⟩ := hLp
  cases hv : c.pred x with
  | nil => exact absurd hv hpx
  | crash =>
    refine inv_setPc hG hL (by simp [h, PC.ovr]) (by simp) (by simp [PC.InR]) ?_
    unfold LI; simp [hn, hv]
  | incs =>
    refine inv_setPc hG hL (by simp [h, PC.ovr]) (by simp) (by simp [PC.InR]) ?_
    unfold LI; simp [hn, hv, hG.ioNN x (.inl hv)]
  | exit =>
    refine inv_setPc hG hL (by simp [h, PC.ovr]) (by simp) (by simp [PC.InR]) ?_
    unfold LI; simp [hn, hv]
  | node m =>
    refine inv_setPc hG hL (by simp [h, PC.ovr]) (by simp) (by simp [PC.InR]) ?_
    unfold LI; simp [hn, hv]

/-- Line 24: busy-wait (the configuration is unchanged). -/
lemma inv_step_l24_wait {c : Cfg k} (hI : Inv c) (p : Fin k) (x : ℕ) (v : PV)
    (_h : c.pc p = .l24 x v) (q : Fin k) (_hl : c.holder = some q) (_hq : q ≠ p) : Inv c := hI

/-- Line 30. -/
lemma inv_step_l30 {c : Cfg k} (hI : Inv c) (p : Fin k) (x : ℕ) (v : PV) (h : c.pc p = .l30 x v) :
    Inv (c.setPc p (if v = .crash then .l31 x else .rx x v)) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨hn, hpx, hv, hnnx⟩ := hLp
  have hhold : c.holder = some p := hG.holder p (by rw [h]; trivial)
  by_cases hvc : v = .crash
  · simp only [hvc, ↓reduceIte]
    refine inv_setPc hG hL (by simp [h, PC.ovr]) (by simp) (fun _ => hhold) ?_
    unfold LI; simp [hn, hpx, hvc, hnnx]
  · simp only [hvc, ↓reduceIte]
    refine inv_setPc hG hL (by simp [h, PC.ovr]) (by simp) (fun _ => hhold) ?_
    unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn]
    exact ⟨hn, hpx, hv.resolve_left hvc, hnnx⟩

/-- Line 25. -/
lemma inv_step_l25 {c : Cfg k} (hI : Inv c) (p : Fin k) (x : ℕ) (v : PV) (h : c.pc p = .l25 x v) :
    Inv (c.setPc p (match v with
        | .node m => if c.csig m then .l26 x else .l25 x v
        | _ => .l25 x v)) := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨hn, hpx, ⟨m, rfl⟩, hnnx⟩ := hLp
  by_cases hcm : c.csig m = true
  · simp only [hcm, ↓reduceIte]
    refine inv_setPc hG hL (by simp [h, PC.ovr]) (by simp) (by simp [PC.InR]) ?_
    unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn]
    exact ⟨hn, ⟨m, hpx, hG.csigPred m hcm, hcm⟩, hnnx⟩
  · simp only [hcm]
    refine inv_setPc hG hL (by simp [h, PC.ovr]) (by simp) (by simp [PC.InR]) ?_
    unfold LI; simp only [Cfg.setPc_pc_self, Cfg.setPc_node, Cfg.setPc_pred, Cfg.setPc_nn]
    exact ⟨hn, hpx, ⟨m, rfl⟩, hnnx⟩


/-! ### Crashes -/

/-- A crash of `p`. -/
lemma inv_crash {c : Cfg k} (hI : Inv c) (p : Fin k) : Inv (c.crash p) := by
  obtain ⟨own, hG, hL⟩ := hI
  unfold Cfg.crash
  cases hn : c.node p with
  | none =>
    have hov : (c.pc p).ovr = none := by
      cases hpc : c.pc p <;> simp only [PC.ovr]
      · rw [((hL p).node_of_pc_l14 hpc).1] at hn; cases hn
      · rw [((hL p).node_of_pc_l49 hpc).1] at hn; cases hn
    exact inv_setPc hG hL (by rw [hov]; rfl) (by simp) (by simp [PC.InR]) (by unfold LI; simp)
  | some x =>
    set c' : Cfg k := c.setPc p .l10
    have hpc : ∀ j, j ≠ p → c'.pc j = c.pc j := fun j hj => by simp [c', hj]
    have hvp : ∀ j v, c'.vp j = .node v → c.vp j = .node v := by
      intro j v hj
      by_cases hjp : j = p
      · subst hjp
        rw [Cfg.vp_of_ovr_none (by simp [c', PC.ovr]) (by simpa [c'] using hn)] at hj
        rcases vp_cases hL j hn with h1 | ⟨m, -, -, h1⟩ | ⟨m, -, -, h1⟩
        · rw [h1]; exact hj
        · rw [show c'.pred x = c.pred x from rfl, h1] at hj; cases hj
        · rw [show c'.pred x = c.pred x from rfl, h1] at hj; cases hj
      · rwa [vp_congr (c := c) (c' := c') (by rw [hpc j hjp]) rfl (fun _ _ => rfl)] at hj
    have hBh := Bh_sub_of (c := c) (c' := c') (fun _ _ h => h) hvp
    have hInH : ∀ y, c'.InH y → c.InH y := fun y hy =>
      InH_sub_of (c := c) (c' := c') (fun _ _ h => h) hBh (fun _ h => h) rfl rfl rfl hy
    exact inv_of_local hG hL hn (fun _ _ => rfl) (.inl rfl) rfl rfl (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) hpc (by simp [c']) (PredStep.of_eq rfl)
      (fun _ h => h) (fun _ h => h) hBh hvp
      (fun h => hG.nnPred x h) (fun h => hG.csigPred x h) (fun h => hG.ioNN x h)
      (fun y y' h1 h2 => hG.hUniq y y' (hInH y h1) (hInH y' h2))
      (fun h1 y h2 => hG.relTail h1 y (hInH y h2))
      (hold_of_out hG hpc (by simp [c', PC.InR]) rfl) (hInH_of_sub hInH p)
      (hcs_of_incs (fun a ha => by simp [c', ha]) p) (by unfold LI; simp [c'])

/-! ### Lines 11–12: allocation -/

/-- Lines 11–12 (the ghost `own` records `p` as the owner of the new node). -/
lemma inv_step_l11 {c : Cfg k} (hI : Inv c) (p : Fin k) (h : c.pc p = .l11) :
    Inv { c with node := Function.update c.node p (some c.nxt), nxt := c.nxt + 1,
                 pc := Function.update c.pc p (.l13 c.nxt) } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  have hn : c.node p = none := hLp
  set c' : Cfg k := { c with
    node := Function.update c.node p (some c.nxt), nxt := c.nxt + 1,
    pc := Function.update c.pc p (.l13 c.nxt) }
  set own' := Function.update own c.nxt p.val
  obtain ⟨hf1, hf2, hf3⟩ := hG.fresh c.nxt le_rfl
  have hpc : ∀ j, j ≠ p → c'.pc j = c.pc j := fun j hj => by simp [c', hj]
  have hnodeq : ∀ j, j ≠ p → c'.node j = c.node j := fun j hj => by simp [c', hj]
  have hvpp : c.vp p = .nil := by simp [Cfg.vp, h, PC.ovr, hn]
  have hvp : ∀ j, c'.vp j = c.vp j := by
    intro j
    by_cases hjp : j = p
    · subst hjp; rw [hvpp]; simp [Cfg.vp, c', PC.ovr, hf1]
    · exact vp_congr (by rw [hpc j hjp]) (hnodeq j hjp) (fun _ _ => rfl)
  have hBh : c'.Bh = c.Bh := by
    funext a b; apply propext; constructor
    · rintro ⟨j, h1, h2⟩
      by_cases hjp : j = p
      · subst hjp; rw [hvp, hvpp] at h2; cases h2
      · exact ⟨j, by rwa [← hnodeq j hjp], by rwa [← hvp]⟩
    · rintro ⟨j, h1, h2⟩
      have hjp : j ≠ p := by rintro rfl; rw [hn] at h1; cases h1
      exact ⟨j, by rwa [hnodeq j hjp], by rwa [hvp]⟩
  have hnodes : ∀ j a, c'.node j = some a → c.node j = some a ∨ c.nxt ≤ a := by
    intro j a hj
    by_cases hjp : j = p
    · subst hjp; simp [c'] at hj; exact .inr hj.le
    · rw [hnodeq j hjp] at hj; exact .inl hj
  have hRel : c'.Rel = c.Rel := Rel_congr rfl rfl
  have hInH : ∀ y, c'.InH y → c.InH y := by
    intro y hy
    obtain ⟨⟨j, hj⟩, h1⟩ := hy
    rcases hnodes j y hj with h2 | h2
    · refine ⟨⟨j, h2⟩, ?_⟩
      rw [hBh, hRel] at h1; exact h1
    · exfalso
      have hy : c.pred y = .nil := (hG.fresh y h2).1
      rcases h1 with h1 | ⟨z, hz, -⟩ | ⟨h1, -⟩
      · rw [show c'.pred y = c.pred y from rfl, hy] at h1; cases h1
      · rw [hBh] at hz; exact absurd (hG.pos_of_bh hz).2 (not_lt.mpr h2)
      · rw [show c'.pred y = c.pred y from rfl, hy] at h1; cases h1
  have hown : ∀ a, a < c.nxt → own' a = own a := fun a ha => by simp [own', ha.ne]
  refine ⟨own', ?_, ?_⟩
  · refine
      { own := by
          intro j a hj
          by_cases hjp : j = p
          · subst hjp; simp [c'] at hj; subst hj; simp [own']
          · rw [hnodeq j hjp] at hj
            rw [hown a (hG.nodeLt j a hj).2]; exact hG.own j a hj
        nodeLt := by
          intro j a hj
          by_cases hjp : j = p
          · subst hjp; simp [c'] at hj; subst hj; exact ⟨hG.nxtPos, by simp [c']⟩
          · rw [hnodeq j hjp] at hj
            have := hG.nodeLt j a hj
            exact ⟨this.1, by simp [c']; omega⟩
        fresh := fun a ha => hG.fresh a (by simp [c'] at ha; omega)
        special := hG.special
        nxtPos := by simp [c']
        table := by
          intro a h1 h2
          simp only [c'] at h2
          by_cases ha : a = c.nxt
          · exact .inl ⟨p, by simp [c', ha]⟩
          · rcases hG.table a h1 (by omega) with ⟨j, hj⟩ | h3
            · have hjp : j ≠ p := by rintro rfl; rw [hn] at hj; cases hj
              exact .inl ⟨j, by rwa [hnodeq j hjp]⟩
            · exact .inr h3
        nnPred := hG.nnPred
        csigPred := hG.csigPred
        ioNN := hG.ioNN
        tailLt := by simp only [c']; have := hG.tailLt; omega
        bhLt := fun y z hb => by
          rw [hBh] at hb; have := hG.bhLt y z hb; simp only [c']; omega
        bhInj := by rw [hBh]; exact hG.bhInj
        noBhTail := by rw [hBh]; exact hG.noBhTail
        hUniq := fun y y' h1 h2 => hG.hUniq y y' (hInH y h1) (hInH y' h2)
        relTail := fun h1 y h2 => hG.relTail (by rw [← hRel]; exact h1) y (hInH y h2)
        wf := by rw [hBh]; exact hG.wf
        holder := hold_of_out hG hpc (by simp [c', PC.InR]) rfl }
  · intro q
    by_cases hqp : q = p
    · subst hqp
      unfold LI
      simp only [c', Function.update_self]
      refine ⟨trivial, hf1, hf2, hf3, fun w hw => ?_, hG.tailLt.ne⟩
      have : c'.Bh w c.nxt := hw
      rw [hBh] at this; exact absurd (hG.bhLt w _ this) (lt_irrefl _)
    · refine LI.transfer hG hL (hpc q hqp) (hnodeq q hqp) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) (PredStep.of_eq rfl) (by rw [hRel]; exact fun _ h => h)
        (by simp [c']) hown ?_ hnodes (fun _ h => h) ?_ ?_
        ((hInH_of_sub hInH p) q hqp) ((hcs_of_incs (fun a ha => by simp [c', ha]) p) q hqp) ?_
      · intro j a hj
        by_cases hjp : j = p
        · subst hjp; simp [c'] at hj; exact .inr hj.le
        · rw [hpc j hjp] at hj; exact .inl hj
      · intro y _ h1 h2; rw [hBh]; exact ⟨h1, h2⟩
      · intro _ x tl V E i EA hs
        exact ScanBh.of_sub hs (by rw [hBh]; exact fun _ _ h => h) rfl
          (fun j v h => by rwa [hvp] at h)
      · intro y s _ h1 h2 h3; rw [hBh]; exact ⟨h1, h2, h3⟩


/-! ### Line 13: `FAS(Tail, mynode)` -/

/-- Line 13. -/
lemma inv_step_l13 {c : Cfg k} (hI : Inv c) (p : Fin k) (x : ℕ) (h : c.pc p = .l13 x) :
    Inv { c with tail := x, pc := Function.update c.pc p (.l14 x c.tail) } := by
  obtain ⟨own, hG, hL⟩ := hI
  have hLp := hL p
  unfold LI at hLp; rw [h] at hLp
  obtain ⟨hn, hpx, hnnx, hcx, hnb, htx⟩ := hLp
  set c' : Cfg k := { c with tail := x, pc := Function.update c.pc p (.l14 x c.tail) }
  have hpc : ∀ j, j ≠ p → c'.pc j = c.pc j := fun j hj => by simp [c', hj]
  have hvpp : c.vp p = .nil := by rw [Cfg.vp_of_ovr_none (by simp [h, PC.ovr]) hn, hpx]
  have hvpp' : c'.vp p = .node c.tail := Cfg.vp_of_ovr_some (by simp [c'])
  have hvpo : ∀ j, j ≠ p → c'.vp j = c.vp j := fun j hj =>
    vp_congr (c := c) (c' := c') (by rw [hpc j hj]) rfl (fun _ _ => rfl)
  have hnoBhx : ∀ b, ¬ c.Bh x b := by
    rintro b ⟨j, hj, hv⟩
    have := hG.node_inj hj hn; subst this; rw [hvpp] at hv; cases hv
  have hBh : ∀ a b, c'.Bh a b ↔ c.Bh a b ∨ (a = x ∧ b = c.tail) := by
    intro a b; constructor
    · rintro ⟨j, hj, hv⟩
      have hj' : c.node j = some a := hj
      by_cases hjp : j = p
      · subst hjp; rw [hn] at hj'; cases hj'
        rw [hvpp'] at hv; cases hv; exact .inr ⟨rfl, rfl⟩
      · exact .inl ⟨j, hj', by rw [← hvpo j hjp]; exact hv⟩
    · rintro (⟨j, hj, hv⟩ | ⟨rfl, rfl⟩)
      · have hjp : j ≠ p := by rintro rfl; rw [hvpp] at hv; cases hv
        exact ⟨j, hj, by rw [hvpo j hjp]; exact hv⟩
      · exact ⟨p, hn, hvpp'⟩
  have hRelx : ¬ c.Rel x := fun h1 => by have := h1.1; rw [hpx] at this; cases this
  have hInH : ∀ y, c'.InH y → c.InH y ∨ (y = x ∧ c.Rel c.tail) := by
    rintro y ⟨hA, h1 | ⟨z, hz, hRz⟩ | ⟨h1, h2, h3⟩⟩
    · exact .inl ⟨hA, .inl h1⟩
    · rcases (hBh y z).mp hz with hz | ⟨rfl, rfl⟩
      · exact .inl ⟨hA, .inr (.inl ⟨z, hz, hRz⟩)⟩
      · exact .inr ⟨rfl, hRz⟩
    · rcases h3 with ⟨w, hw⟩ | h3
      · rcases (hBh w y).mp hw with hw | ⟨rfl, rfl⟩
        · exact .inl ⟨hA, .inr (.inr ⟨h1, h2, .inl ⟨w, hw⟩⟩)⟩
        · exact .inl ⟨hA, .inr (.inr ⟨h1, h2, .inr rfl⟩)⟩
      · exfalso; have h4 : x = y := h3; subst h4
        have h5 : c.pred x = .exit := h1
        rw [hpx] at h5; cases h5
  have hrtg : ∀ a b, ReflTransGen c'.Bh a b → a ≠ x → ReflTransGen c.Bh a b := by
    intro a b hab
    induction hab using ReflTransGen.head_induction_on with
    | refl => intro _; exact .refl
    | @head a d e1 _ ih =>
      intro hax
      rcases (hBh a d).mp e1 with e1 | ⟨h1, -⟩
      · exact .head e1 (ih (fun hdx => hnb a (hdx ▸ e1)))
      · exact absurd h1 hax
  refine ⟨own, ?_, ?_⟩
  · refine
      { own := hG.own
        nodeLt := hG.nodeLt
        fresh := hG.fresh
        special := hG.special
        nxtPos := hG.nxtPos
        table := hG.table
        nnPred := hG.nnPred
        csigPred := hG.csigPred
        ioNN := hG.ioNN
        tailLt := (hG.nodeLt p x hn).2
        bhLt := fun y z hb => by
          rcases (hBh y z).mp hb with hb | ⟨-, rfl⟩
          · exact hG.bhLt y z hb
          · exact hG.tailLt
        bhInj := fun y y' z g1 g2 => by
          rcases (hBh y z).mp g1 with h1 | ⟨rfl, rfl⟩ <;>
            rcases (hBh y' _).mp g2 with h2 | ⟨rfl, h3⟩
          · exact hG.bhInj y y' _ h1 h2
          · subst h3; exact absurd h1 (hG.noBhTail y)
          · exact absurd h2 (hG.noBhTail y')
          · rfl
        noBhTail := fun y hb => by
          rcases (hBh y x).mp hb with hb | ⟨-, h1⟩
          · exact hnb y hb
          · exact htx h1.symm
        hUniq := fun y y' g1 g2 => by
          rcases hInH y g1 with h1 | ⟨rfl, h3⟩ <;> rcases hInH y' g2 with h2 | ⟨rfl, h4⟩
          · exact hG.hUniq y y' h1 h2
          · exact absurd h1 (hG.relTail h4 y)
          · exact absurd h2 (hG.relTail h3 y')
          · rfl
        relTail := fun h1 => absurd h1 hRelx
        wf := by
          have key : ∀ a, Acc (flip c.Bh) a → a ≠ x → Acc (flip c'.Bh) a := by
            intro a ha
            induction ha with
            | intro a _ ih =>
              intro hax
              refine Acc.intro a (fun b hb => ?_)
              rcases (hBh a b).mp hb with hb | ⟨h1, -⟩
              · exact ih b hb (fun hbx => hnb a (hbx ▸ hb))
              · exact absurd h1 hax
          refine ⟨fun a => ?_⟩
          by_cases hax : a = x
          · subst hax
            refine Acc.intro _ (fun b hb => ?_)
            rcases (hBh _ b).mp hb with hb | ⟨-, rfl⟩
            · exact absurd hb (hnoBhx b)
            · exact key _ (hG.wf.apply _) (fun h1 => htx h1)
          · exact key a (hG.wf.apply a) hax
        holder := hold_of_out hG hpc (by simp [c', PC.InR]) rfl }
  · intro q
    by_cases hqp : q = p
    · subst hqp; unfold LI; simp only [c', Function.update_self]
      exact ⟨hn, hpx, hnnx, hcx⟩
    have hyx : ∀ y, c.node q = some y → y ≠ x := by
      rintro y hy rfl; exact hqp (hG.node_inj hy hn)
    have hLq := hL q
    refine LI.transfer hG hL (hpc q hqp) rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (PredStep.of_eq rfl) (fun _ h => h) le_rfl (fun _ _ => rfl) ?_ (fun j a hj => .inl hj)
      (fun _ h => h) ?_ ?_ ?_ ((hcs_of_incs (fun a ha => by simp [c', ha]) p) q hqp) ?_
    · intro j a hj
      by_cases hjp : j = p
      · subst hjp; simp [c'] at hj
      · rw [hpc j hjp] at hj; exact .inl hj
    · intro y hq h1 h2
      unfold LI at hLq; rw [hq] at hLq
      have hy := hyx y hLq.1
      refine ⟨fun w hw => ?_, fun h3 => hy h3.symm⟩
      rcases (hBh w y).mp hw with hw | ⟨-, rfl⟩
      · exact h1 w hw
      · exact h2 rfl
    · intro _ x' tl V E i EA hs
      have hxEA : x ∉ EA := hs.l13Late p x h
      refine ⟨.inr hxEA, ?_, ?_, ?_, ?_, ?_⟩
      · intro a b hab haEA
        rcases (hBh a b).mp hab with hab | ⟨-, rfl⟩
        · exact hs.bhLate a b hab haEA
        · exact hs.tail
      · intro a b hab haEA
        rcases (hBh a b).mp hab with hab | ⟨rfl, -⟩
        · exact hs.bhEarly a b hab haEA
        · exact absurd haEA hxEA
      · intro u v w he hw
        rcases (hBh w v).mp hw with hw | ⟨-, rfl⟩
        · exact hs.E2 u v w he hw
        · exact absurd rfl (hs.Etail u _ he)
      · intro u v he hv
        have hv' : v = x := hv
        subst hv'; exact hs.El13 u _ p he h
      · intro j a v hj haEA hv
        by_cases hjp : j = p
        · subst hjp
          have : c.node j = some a := hj
          rw [hn] at this; cases this; exact absurd haEA hxEA
        · rw [← hvpo j hjp]; exact hv
    · intro hR x' tl V E EA mp tp hp dn hs hP hA h1 y hy
      rcases hInH y hy with h2 | ⟨-, h2⟩
      · exact h1 y h2
      · exact hs.attach_not_rel_tail hG hL hP hA h2
    · intro y s hq h1 h2 h3
      unfold LI at hLq; rw [hq] at hLq
      obtain ⟨h4, -, -, -, -, -, h7, -, -⟩ := hLq
      have hy := hyx y h4
      have hs : s ≠ x := fun hsx => h7 p (hsx ▸ h)
      refine ⟨fun w hw => ?_, fun h5 => hs h5.symm, fun h5 => ?_⟩
      · rcases (hBh w s).mp hw with hw | ⟨-, rfl⟩
        · exact h1 w hw
        · exact h2 rfl
      · rcases ReflTransGen.cases_head h5 with h6 | ⟨b, e1, h6⟩
        · exact hy h6.symm
        · rcases (hBh x b).mp e1 with e1 | ⟨-, rfl⟩
          · exact hnoBhx b e1
          · exact h3 (hrtg _ y h6 (fun h1 => htx h1))

end Podc.RMESubLogBoth
