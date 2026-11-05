import Papers.PODC2023.DuraCAS.CStepFrame

/-!
# Simulation of the DurEC steps that write shared memory without linearizing anything

Line 7 (`h.Val ← v`), line 10 (the install), line 15 (help on `DetVal`).
-/

set_option linter.unusedSectionVars false

namespace Podc.DuraCAS

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

/-- Line 15: helping `g.DetVal` up to `e` (the help is only possible while `(g, e)` is the pending
install, Lemma A.10.2 corrected). -/
theorem step_f15_cas {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} {g e d}
    (hI : Inv s a) (hf : (s.ps p).fr = some f) (hpc : f.pc = .f15 g e d)
    (hc : d < e ∧ s.m.det g = d) :
    Inv (setFrame s p { s.m with det := Function.update s.m.det g e } { f with pc := .f16 g e })
      a := by
  have hF := (hI.p p).fr f hf
  have h5 := hF.stage
  simp only [StageOK, hpc] at h5
  have hpa : PendAt s.m f.o g e := by
    rcases h5.2.1 with h | ⟨-, h⟩
    · exact h
    · have := hI.g.lsDet g; omega
  -- the intermediate state: memory updated, frame still at line 15
  have hI1 : Inv { s with m := { s.m with det := Function.update s.m.det g e } } a := by
    refine ⟨hI.Y, hI.hist, hI.nid, hI.g.of_det hpa, fun q => (hI.p q).of_det hI.g hpa, ?_⟩
    intro o g' hx hp; exact hI.own o g' hx hp
  have hF1 := (hI1.p p).fr f hf
  have hw : f.pc.IsFwd := by rw [hpc]; simp [FPc.IsFwd]
  refine hI1.local (f := f) hf rfl rfl rfl rfl (fun _ => rfl) (hF1.fwd_next hw (by simp [FPc.IsFwd]) ?_)
  have h6 := hF1.stage
  simp only [StageOK, hpc] at h6
  exact ⟨h6.1, h6.2.1, fun _ => by simp⟩

/-- Line 7: `h.Val ← v` (the process has no pending install, so no helper reads `h.Val`). -/
theorem step_l7 {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V}
    (hI : Inv s a) (hf : (s.ps p).fr = some f) (hpc : f.pc = .l7) :
    Inv (setFrame s p { s.m with hval := Function.update s.m.hval f.h f.v } { f with pc := .l8 })
      a := by
  have hP := hI.p p
  have hF := hP.fr f hf
  have hw : ¬ f.pc.IsFwd := by rw [hpc]; simp [FPc.IsFwd]
  have hfree := hI.noPend_of_pre hf hw
  have hk := hF.sc_of_pre hw
  have hrf := hF.r_false_of_pre hw
  have hI1 : Inv { s with m := { s.m with hval := Function.update s.m.hval f.h f.v } } a := by
    refine ⟨hI.Y, hI.hist, hI.nid, hI.g.of_hval _ _, fun q => ?_, ?_⟩
    · by_cases hqp : q = p
      · subst hqp
        apply hP.transfer
        · intro _ _; exact Iff.rfl
        · intro x hx; rw [hP.orph_none_of_sc hf hk] at hx; cases hx
        · intro f' hf' _ hk'; rw [hf] at hf'; cases hf'; exact ⟨(hF.2.2.1 hk').1, fun h => absurd h hw⟩
        · intro f' hf' _; rw [hf] at hf'; cases hf'
          simp only [StageOK, hpc]; exact hrf
      · exact (hI.p q).of_hval (by rw [hF.1]; exact Ne.symm hqp)
          (fun o hx => hfree o _ hx hF.1)
    · intro o g' hx hp; exact hI.own o g' hx hp
  have hF1 := (hI1.p p).fr f hf
  refine hI1.local (f := f) hf rfl rfl rfl rfl (fun _ => rfl) ?_
  obtain ⟨h1, h2, h3, h4, -⟩ := hF1
  refine ⟨h1, h2, fun hk' => ⟨(h3 hk').1, fun h => absurd h (by simp [FPc.IsFwd])⟩,
    fun hk' => (by rw [hk] at hk'; cases hk'), ?_⟩
  exact ⟨hrf, by simp⟩

/-- Line 10, successful `CAS` on `X`: **an install** (Lemmas A.1, A.2: it happens only when no
install is pending, and increases `X.seq` from `s = Y.seq`). Nothing is linearized yet. -/
theorem step_l10_install {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} {hh}
    (hI : Inv s a) (hf : (s.ps p).fr = some f) (hpc : f.pc = .l10 hh)
    (heq : s.m.X f.o = (hh, f.s)) :
    Inv (setFrame s p { s.m with X := Function.update s.m.X f.o (some f.h, f.sh) }
      { f with r := true, pc := .f13 }) a := by
  have hP := hI.p p
  have hF := hP.fr f hf
  have hw : ¬ f.pc.IsFwd := by rw [hpc]; simp [FPc.IsFwd]
  have hfree := hI.noPend_of_pre hf hw
  have hk := hF.sc_of_pre hw
  have hrf := hF.r_false_of_pre hw
  have hs := (hF.2.2.1 hk).1
  have hyx := hI.g.yx f.o
  rw [heq] at hyx; simp only at hyx
  have hYs : (s.m.Y f.o).1 = f.s := by omega
  have hnp : ¬ Pend s.m f.o := by unfold Pend; rw [heq]; simp only; omega
  have h5 := hF.stage
  simp only [StageOK, hpc] at h5
  obtain ⟨-, hv, -, hsh⟩ := h5
  have hsh' : f.sh = max (a.ls f.h) (s.m.Y f.o).1 + 1 := by rw [hYs]; exact hsh
  have hlt : f.s < f.sh := by rw [hsh]; omega
  have hfree' : ∀ o g, (s.m.X o).1 = some g → g.1 = f.h.1 → ¬ Pend s.m o :=
    fun o g hx hg => hfree o g hx (hg.trans hF.1)
  have hX : ∀ o, o ≠ f.o → (Function.update s.m.X f.o (some f.h, f.sh)) o = s.m.X o :=
    fun o ho => Function.update_of_ne ho _ _
  refine ⟨hI.Y, hI.hist, hI.nid, hI.g.of_install hnp hsh' hfree', ?_, ?_⟩
  · apply forall_update_PInv' _ (fun q _ => (hI.p q).of_install hnp (by omega))
    refine ⟨hP.op, hP.idle, fun hi => ?_, ?_, ?_, ?_⟩
    · have := hP.idleFr hi; rw [hf] at this; cases this
    · rw [hP.pc]
      have hm' : ¬ (f.sh ≤ (s.m.Y f.o).1) := by omega
      simp [apcOf, hf, Moved, hk, hm', hrf]
    · intro x hx; rw [hP.orph_none_of_sc hf hk] at hx; cases hx
    · intro f' hf'; simp only [Option.some.injEq] at hf'; subst hf'
      refine ⟨hF.1, hF.2.1, fun _ => ⟨hs, fun _ => ⟨fun _ => ⟨hlt, Or.inr ⟨by simp, hYs, hv⟩⟩,
        fun h => by simp at h⟩⟩, fun hk' => (by rw [hk] at hk'; cases hk'), trivial⟩
  · intro o g hx hp
    simp only [setFrame] at hx hp ⊢
    by_cases ho : o = f.o
    · subst ho
      simp only [Function.update_self, Option.some.injEq] at hx; subst hx
      left
      exact ⟨{ f with r := true, pc := .f13 }, by simp [hF.1], hk, rfl, rfl, rfl,
        by simp⟩
    · simp only [hX o ho] at hx
      have hp' : Pend s.m o := by unfold Pend at hp ⊢; simpa [hX o ho] using hp
      have hgp : g.1 ≠ p := fun h => hfree o g hx h hp'
      rcases hI.own o g hx hp' with ⟨f0, hf0, h⟩ | ⟨x, hx', h⟩
      · left; refine ⟨f0, by simp [Function.update_of_ne hgp, hf0], ?_⟩
        simpa [hX o ho] using h
      · exact Or.inr ⟨x, hx', h⟩

/-- Simulation of one step of an active DurEC call. -/
theorem sim_frame {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} (hI : Inv s a)
    (hf : (s.ps p).fr = some f) :
    ∃ a', Relation.ReflTransGen AStep a a' ∧ Inv (pstep s p) a' := by
  have hps : pstep s p = match fstep s.m f with
      | (m', .cont f') => setFrame s p m' f'
      | (m', .done r) => applyNext s p m' (afterCall (s.ps p).pc r) := by
    simp only [pstep, hf]; rfl
  rw [hps]
  cases hpc : f.pc with
  | l7 => simp only [fstep, hpc]; exact ⟨a, .refl, step_l7 hI hf hpc⟩
  | l8 => simp only [fstep, hpc]; exact ⟨a, .refl, step_l8 hI hf hpc⟩
  | l9 hh => simp only [fstep, hpc]; exact ⟨a, .refl, step_l9 hI hf hpc⟩
  | l10 hh =>
    simp only [fstep, hpc]
    split_ifs with h
    · exact ⟨a, .refl, step_l10_install hI hf hpc h⟩
    · exact ⟨a, .refl, step_l10_fail hI hf hpc h⟩
  | f13 => simp only [fstep, hpc]; exact ⟨a, .refl, step_f13 hI hf hpc⟩
  | f14 x =>
    simp only [fstep, hpc]
    cases hx : x.1 with
    | none => simp only; exact step_f14_none hI hf hpc hx
    | some g => simp only; exact ⟨a, .refl, step_f14 hI hf hpc hx⟩
  | f15 g e d =>
    simp only [fstep, hpc]
    split_ifs with h
    · exact ⟨a, .refl, step_f15_cas hI hf hpc h⟩
    · exact ⟨a, .refl, step_f15_skip hI hf hpc h⟩
  | f16 g e => simp only [fstep, hpc]; exact ⟨a, .refl, step_f16 hI hf hpc⟩
  | f17 g e vh => simp only [fstep, hpc]; exact ⟨a, .refl, step_f17 hI hf hpc⟩
  | f18 g e vh y =>
    simp only [fstep, hpc]
    split_ifs with h
    · exact step_f18_move hI hf hpc h
    · exact step_f18_skip hI hf hpc h

end Podc.DuraCAS
