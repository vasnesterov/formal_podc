import Papers.PODC2023.DuraCAS.CStepBase

/-!
# Simulation of the steps of an active DurEC call

Moves (Lemmas A.4, A.5: the first move after an install moves the installer's value, and
linearizes the installer, Definition A.8) and returns of DurEC calls (Lemmas A.3, A.6, A.7: a
`FORWARD` that started after an install completes only after it is moved; a hitchhiker fails).
-/

set_option linter.unusedSectionVars false

namespace Podc.DuraCAS

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

theorem PInv.orph_none_of_sc {m : Mem P K V} {ls p st ap f} (h : PInv m ls p st ap)
    (hf : st.fr = some f) (hk : f.kind = .sc) : ap.orph = none := by
  cases hor : ap.orph with
  | none => rfl
  | some x =>
    obtain ⟨-, -, -, -, -, r, j, -, hpc, -⟩ := h.orph x hor
    exact absurd hpc ((h.fr f hf).sc_not_recv hk j)

theorem FrameOK.sc_of_pre {m : Mem P K V} {ls p st orph f} (h : FrameOK m ls p st orph f)
    (hw : ¬ f.pc.IsFwd) : f.kind = .sc := by
  cases hk : f.kind
  · rfl
  · exact absurd (h.2.2.2.1 hk) hw

theorem FrameOK.r_false_of_pre {m : Mem P K V} {ls p st orph f} (h : FrameOK m ls p st orph f)
    (hw : ¬ f.pc.IsFwd) : f.r = false := by
  have := h.2.2.2.2; revert this hw; unfold StageOK
  cases f.pc <;> simp [FPc.IsFwd] <;> intros <;> assumption

theorem FrameOK.fwd_of_r {m : Mem P K V} {ls p st orph f} (h : FrameOK m ls p st orph f)
    (hr : f.r = true) : f.pc.IsFwd := by
  by_contra hw; rw [h.r_false_of_pre hw] at hr; cases hr

/-- A process in lines 7–10 of `ECSC` has no pending install. -/
theorem Inv.noPend_of_pre {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V}
    (hI : Inv s a) (hf : (s.ps p).fr = some f) (hw : ¬ f.pc.IsFwd) :
    ∀ o g, (s.m.X o).1 = some g → g.1 = p → ¬ Pend s.m o := by
  intro o g hx hgp hp
  have hP := hI.p p
  have hF := hP.fr f hf
  have hk := hF.sc_of_pre hw
  rcases owner_cases (hI.own o g hx hp) hx (hgp ▸ hP) with
    ⟨f0, hf0, -, hr, -⟩ | ⟨x, hx', -⟩
  · rw [hgp, hf] at hf0; cases hf0; rw [hF.r_false_of_pre hw] at hr; cases hr
  · rw [hgp, hP.orph_none_of_sc hf hk] at hx'; cases hx'

theorem forall_update_PInv' {m : Mem P K V} {ls : Hd P → ℕ} {ps : P → PState P K V}
    {aps : P → APS P K V} {p : P} {st : PState P K V}
    (hp : PInv m ls p st (aps p)) (hq : ∀ q, q ≠ p → PInv m ls q (ps q) (aps q)) :
    ∀ q, PInv m ls q (Function.update ps p st q) (aps q) := by
  intro q
  by_cases hqp : q = p
  · subst hqp; simpa using hp
  · simpa [Function.update_of_ne hqp] using hq q hqp

/-- A step of an active call that changes neither the shared memory nor the A-level state. -/
theorem Inv.local {s : St P K V} {a : AS P K V} {p : P} {f f' : Frame P K V} (hI : Inv s a)
    (hf : (s.ps p).fr = some f) (hk : f'.kind = f.kind) (ho : f'.o = f.o) (hh : f'.h = f.h)
    (hr : f'.r = f.r) (hsh : f.r = true → f'.sh = f.sh)
    (hOK : FrameOK s.m a.ls p (s.ps p) (a.ps p).orph f') :
    Inv (setFrame s p s.m f') a := by
  have hP := hI.p p
  have hmv : Moved s.m f' ↔ Moved s.m f := by
    unfold Moved; rw [hk, hr, ho]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [← hsh h2]; exact h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [hsh h2]; exact h3⟩
  refine ⟨hI.Y, hI.hist, hI.nid, hI.g, ?_, ?_⟩
  · apply forall_update_PInv' _ (fun q _ => hI.p q)
    refine ⟨hP.op, hP.idle, fun hi => ?_, ?_, hP.orph, ?_⟩
    · have := hP.idleFr hi; rw [hf] at this; cases this
    · rw [hP.pc]; simp [apcOf, hf, hmv]
    · intro f'' hf''; simp only [Option.some.injEq] at hf''; subst hf''; exact hOK
  · intro o g hx hp
    rcases hI.own o g hx hp with ⟨f0, hf0, h1, h2, h3, h4, h5⟩ | ⟨x, hx', h⟩
    · left
      by_cases hgp : g.1 = p
      · rw [hgp, hf] at hf0; cases hf0
        refine ⟨f', by simp [setFrame, hgp], by rw [hk]; exact h1, by rw [hr]; exact h2,
          by rw [ho]; exact h3, by rw [hh]; exact h4, by rw [hsh h2]; exact h5⟩
      · exact ⟨f0, by simp [setFrame, Function.update_of_ne hgp, hf0], h1, h2, h3, h4, h5⟩
    · exact Or.inr ⟨x, hx', h⟩

/-- Owners of the other pending installs are unaffected by a move. -/
theorem Inv.own_move {s : St P K V} {a : AS P K V} {o : Obj K} {g : Hd P} {e : ℕ}
    {vh : V × Bool} (hI : Inv s a) (hpa : PendAt s.m o g e) (aps : P → APS P K V)
    (haps : ∀ q, q ≠ g.1 → aps q = a.ps q) :
    ∀ o' g', (s.m.X o').1 = some g' →
      Pend { s.m with Y := Function.update s.m.Y o (e, vh) } o' →
      Owner { s.m with Y := Function.update s.m.Y o (e, vh) } s.ps aps o' g' := by
  intro o' g' hx hp
  obtain ⟨ho, hp⟩ := Pend.of_move hpa hp
  have hne : g'.1 ≠ g.1 := fun h =>
    ho (hI.g.uniq o' o g' g hx (by rw [hpa.1]) hp hpa.2 h)
  rcases hI.own o' g' hx hp with ⟨f0, h⟩ | ⟨x, hx', h⟩
  · exact Or.inl ⟨f0, h⟩
  · exact Or.inr ⟨x, by rw [haps _ hne]; exact hx', h⟩

/-- **A move** (line 18) of the pending install `(g, e)` of `o`, by any process: the A-level
linearizes the installer (an active `ECSC`, Definition A.8.1) or lets the orphan take effect. The
moved value is the installer's (Lemma A.5). -/
theorem Inv.move {s : St P K V} {a : AS P K V} {o : Obj K} {g : Hd P} {e : ℕ} {vh : V × Bool}
    (hI : Inv s a) (hpa : PendAt s.m o g e) (hdet : s.m.det g = e) (hvh : vh = s.m.hval g) :
    ∃ a1, AStep a a1 ∧
      Inv { s with m := { s.m with Y := Function.update s.m.Y o (e, vh) } } a1 := by
  have hx : (s.m.X o).1 = some g := by rw [hpa.1]
  have hseq : e = max (a.ls g) (s.m.Y o).1 + 1 := by
    have := hI.g.pendSeq o g hx hpa.2; rw [hpa.1] at this; exact this
  have hYe : (s.m.Y o).1 < e := by have := hpa.2; unfold Pend at this; rw [hpa.1] at this; exact this
  rcases owner_cases (hI.own o g hx hpa.2) hx (hI.p g.1) with
    ⟨f0, hf0, hk, hr, hfo, hfh, hsh, hw, hor⟩ | ⟨x, hx', hxo, hxh, hrec⟩
  · have hP := hI.p g.1
    have hF := hP.fr f0 hf0
    have hsh' : f0.sh = e := by rw [hsh, hpa.1]
    obtain ⟨hlt, hmv⟩ := ((hF.2.2.1 hk).2 hw).1 hr
    have hnm : ¬ f0.sh ≤ (s.m.Y f0.o).1 := by rw [hsh', hfo]; omega
    obtain ⟨-, hys, hv⟩ := hmv.resolve_left hnm
    rw [hfo] at hys
    obtain ⟨r, hr', hsc, -⟩ := hF.2.1
    have hapc : (a.ps g.1).pc = .at (s.ps g.1).pc := by
      rw [hP.pc]; simp [apcOf, hf0, Moved, hnm]
    have hst := astep_sc (hP.op.trans hr') hapc (hsc hk)
    have hec : ecsc a.Y a.ls ⟨f0.o, f0.h, f0.s, f0.v⟩ =
        (Function.update s.m.Y o (e, vh), Function.update a.ls g e, true) := by
      rw [ecsc_succ (by simp only; rw [hI.Y, hfo, hys])]
      simp only [hfo, hfh, hI.Y, hseq, hys, hvh, ← hv]
    rw [hec] at hst
    refine ⟨_, hst, hI.Y ▸ rfl, hI.hist, hI.nid, ?_, ?_, ?_⟩
    · exact hI.g.of_move hpa hdet
    · intro q
      by_cases hq : q = g.1
      · subst hq; simp only [Function.update_self]
        exact hP.of_move_frame hI.g hpa hf0 hk hr hfo hsh' hw hor
      · simp only [Function.update_of_ne hq]
        exact (hI.p q).of_move hI.g hpa (Ne.symm hq)
    · exact hI.own_move hpa _ (fun q hq => by simp [Function.update_of_ne hq])
  · have hP := hI.p g.1
    obtain ⟨-, -, -, hxs, hxv, -⟩ := hP.orph x hx'
    have hst := astep_orph hx' (by rw [hI.Y, hxs])
    have hec : ecsc a.Y a.ls x =
        (Function.update s.m.Y o (e, vh), Function.update a.ls g e, true) := by
      rw [ecsc_succ (by rw [hI.Y, hxs])]
      rw [hxo] at hxs
      simp only [hxo, hxh, hI.Y, hseq, hxs, hvh, hxv]
    rw [hec] at hst
    refine ⟨_, hst, hI.Y ▸ rfl, hI.hist, hI.nid, ?_, ?_, ?_⟩
    · exact hI.g.of_move hpa hdet
    · intro q
      by_cases hq : q = g.1
      · subst hq; simp only [Function.update_self]
        exact hP.of_move_orph hI.g hpa hrec
      · simp only [Function.update_of_ne hq]
        exact (hI.p q).of_move hI.g hpa (Ne.symm hq)
    · exact hI.own_move hpa _ (fun q hq => by simp [Function.update_of_ne hq])

/-- **Return of a DurEC call** whose obligation is fulfilled (`¬ Need`): an installer is
linearized (Lemma A.4), a hitchhiker fails (Lemmas A.6, A.7), a `RECOVER` has moved the orphan
of its object (Lemma A.3). -/
theorem Inv.ret {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} (hI : Inv s a)
    (hf : (s.ps p).fr = some f) (hw : f.pc.IsFwd) (hN : ¬ Need s.m (a.ps p).orph f) :
    ∃ a', Relation.ReflTransGen AStep a a' ∧
      Inv (applyNext s p s.m (afterCall (s.ps p).pc f.r)) a' := by
  have hP := hI.p p
  have hF := hP.fr f hf
  obtain ⟨-, ⟨r, hr, hsc, hrecv⟩, hScOK, -, -⟩ := hF
  have hiff : Moved s.m f ↔ (f.kind = .sc ∧ f.r = true) := by
    refine ⟨fun h => ⟨h.1, h.2.1⟩, fun ⟨hk, hrt⟩ => ⟨hk, hrt, ?_⟩⟩
    obtain ⟨hlt, hm⟩ := ((hScOK hk).2 hw).1 hrt
    rcases hm with hm | ⟨hx, hy, -⟩
    · exact hm
    · exfalso; apply hN
      refine ⟨by unfold Pend; rw [hx, hy]; exact hlt, Or.inr (Or.inl ⟨hk, hrt, by rw [hy]; exact hlt⟩)⟩
  refine ret_frame hI.Y hI.hist hI.nid hI.g (fun q _ => hI.p q) ?_ (hP.op.trans hr) hr hsc hrecv
    ?_ ?_ ?_ ?_
  · intro o g hx hp
    by_cases hgp : g.1 = p
    · right; refine ⟨hgp, ?_⟩
      rcases owner_cases (hI.own o g hx hp) hx (hI.p g.1) with
        ⟨f0, hf0, hk, hrt, hfo, -, hsh, -⟩ | ⟨x, hx', hxo, -⟩
      · exfalso; rw [hgp, hf] at hf0; cases hf0
        apply hN
        refine ⟨hfo ▸ hp, Or.inr (Or.inl ⟨hk, hrt, ?_⟩)⟩
        rw [hsh, hfo]; exact hp
      · exact ⟨x, hgp ▸ hx', hxo⟩
    · exact Or.inl ⟨hgp, hI.own o g hx hp⟩
  · rw [hP.pc]; simp only [apcOf, hf]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  · intro hk hrf hy
    apply hN
    have := ((hScOK hk).2 hw).2 hrf
    exact ⟨by unfold Pend; omega, Or.inl ⟨hk, hrf, hy⟩⟩
  · intro hk; exact hP.orph_none_of_sc hf hk
  · intro hk x hx
    refine ⟨fun hxo => hN ⟨?_, Or.inr (Or.inr ⟨hk, x, hx, hxo⟩)⟩, hP.orph x hx⟩
    rw [← hxo]; exact (hP.orph x hx).2.2.1

/-! ## Frame steps without effect on shared memory -/

theorem step_l8 {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} (hI : Inv s a)
    (hf : (s.ps p).fr = some f) (hpc : f.pc = .l8) :
    Inv (setFrame s p s.m { f with pc := .l9 (s.m.X f.o).1 }) a := by
  have hF := (hI.p p).fr f hf
  refine hI.local hf rfl rfl rfl rfl (fun _ => rfl) ?_
  obtain ⟨h1, h2, h3, h4, h5⟩ := hF
  have hw : ¬ f.pc.IsFwd := by rw [hpc]; simp [FPc.IsFwd]
  refine ⟨h1, h2, fun hk => ⟨(h3 hk).1, fun h => absurd h (by simp [FPc.IsFwd])⟩,
    fun hk => absurd (h4 hk) hw, ?_⟩
  simp only [StageOK, hpc] at h5
  exact ⟨h5.1, h5.2, fun _ => rfl⟩

theorem step_l9 {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} {hh} (hI : Inv s a)
    (hf : (s.ps p).fr = some f) (hpc : f.pc = .l9 hh) :
    Inv (setFrame s p s.m { f with sh := max (s.m.det f.h) f.s + 1, pc := .l10 hh }) a := by
  have hF := (hI.p p).fr f hf
  have hw : ¬ f.pc.IsFwd := by rw [hpc]; simp [FPc.IsFwd]
  have hrf := hF.r_false_of_pre hw
  refine hI.local hf rfl rfl rfl rfl (fun h => by simp [hrf] at h) ?_
  have hdet : s.m.det f.h = a.ls f.h :=
    hI.g.detEq _ (fun o hx => hI.noPend_of_pre hf hw o _ hx hF.1)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hF
  refine ⟨h1, h2, fun hk => ⟨(h3 hk).1, fun h => absurd h (by simp [FPc.IsFwd])⟩,
    fun hk => absurd (h4 hk) hw, ?_⟩
  simp only [StageOK, hpc] at h5
  exact ⟨h5.1, h5.2.1, h5.2.2, by rw [hdet]⟩

theorem step_l10_fail {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} {hh}
    (hI : Inv s a) (hf : (s.ps p).fr = some f) (hpc : f.pc = .l10 hh)
    (hne : ¬ s.m.X f.o = (hh, f.s)) :
    Inv (setFrame s p s.m { f with r := false, pc := .f13 }) a := by
  have hF := (hI.p p).fr f hf
  have hw : ¬ f.pc.IsFwd := by rw [hpc]; simp [FPc.IsFwd]
  have hrf := hF.r_false_of_pre hw
  have hk := hF.sc_of_pre hw
  refine hI.local hf rfl rfl rfl hrf.symm (fun h => by simp [hrf] at h) ?_
  obtain ⟨h1, h2, h3, h4, h5⟩ := hF
  have hyx := hI.g.yx f.o
  simp only [StageOK, hpc] at h5
  have hs := (h3 hk).1
  refine ⟨h1, h2, fun _ => ⟨hs, fun _ => ⟨fun h => (by cases h), fun _ => ?_⟩⟩,
    fun hk' => (by rw [hk] at hk'; cases hk'), trivial⟩
  show f.s < (s.m.X f.o).2
  rcases Nat.lt_or_ge f.s (s.m.X f.o).2 with h | h
  · exact h
  · exfalso; apply hne
    have heq : (s.m.X f.o).2 = f.s := by omega
    exact Prod.ext (h5.2.2.1 heq) heq

theorem fresh_cur {m : Mem P K V} {ls : Hd P → ℕ} (hg : CGInv m ls) (o : Obj K) (g : Hd P)
    (hx : (m.X o).1 = some g) : Fresh m ls o g (m.X o).2 := by
  by_cases hp : Pend m o
  · exact Or.inl ⟨Prod.ext hx rfl, hp⟩
  · exact Or.inr ⟨by unfold Pend at hp; omega, hg.done o g hx hp⟩

theorem step_f13 {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} (hI : Inv s a)
    (hf : (s.ps p).fr = some f) (hpc : f.pc = .f13) :
    Inv (setFrame s p s.m { f with pc := .f14 (s.m.X f.o) }) a := by
  have hF := (hI.p p).fr f hf
  refine hI.local hf rfl rfl rfl rfl (fun _ => rfl) ?_
  obtain ⟨h1, h2, h3, h4, h5⟩ := hF
  have hw : f.pc.IsFwd := by rw [hpc]; simp [FPc.IsFwd]
  refine ⟨h1, h2, fun hk => ⟨(h3 hk).1, fun _ => (h3 hk).2 hw⟩, fun _ => trivial, ?_⟩
  exact ⟨fun _ => rfl, fun g hx => fresh_cur hI.g f.o g hx⟩

theorem FrameOK.fwd_next {m : Mem P K V} {ls p st orph f} (h : FrameOK m ls p st orph f)
    (hw : f.pc.IsFwd) {pc' : FPc P V} (hw' : pc'.IsFwd)
    (hst : StageOK m ls { f with pc := pc' } (Need m orph f)) :
    FrameOK m ls p st orph { f with pc := pc' } := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, fun hk => ⟨(h3 hk).1, fun _ => (h3 hk).2 hw⟩, fun _ => hw', hst⟩

theorem FrameOK.stage {m : Mem P K V} {ls p st orph f} (h : FrameOK m ls p st orph f) :
    StageOK m ls f (Need m orph f) := h.2.2.2.2

theorem step_f14 {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} {x g}
    (hI : Inv s a) (hf : (s.ps p).fr = some f) (hpc : f.pc = .f14 x) (hx : x.1 = some g) :
    Inv (setFrame s p s.m { f with pc := .f15 g x.2 (s.m.det g) }) a := by
  have hF := (hI.p p).fr f hf
  have hw : f.pc.IsFwd := by rw [hpc]; simp [FPc.IsFwd]
  refine hI.local hf rfl rfl rfl rfl (fun _ => rfl) (hF.fwd_next hw (by simp [FPc.IsFwd]) ?_)
  have h5 := hF.stage
  simp only [StageOK, hpc] at h5
  refine ⟨fun hn => by rw [← h5.1 hn, ← hx], h5.2 g hx, fun hp => ?_⟩
  have hX : (s.m.X f.o).1 = some g := by rw [hp.1]
  rcases hI.g.pendDet f.o g hX hp.2 with hd | hd
  · right; refine ⟨rfl, ?_⟩
    have := hI.g.pendSeq f.o g hX hp.2
    rw [hd]; rw [hp.1] at this; simp only at this; omega
  · left; rw [hd, hp.1]

theorem step_f15_skip {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} {g e d}
    (hI : Inv s a) (hf : (s.ps p).fr = some f) (hpc : f.pc = .f15 g e d)
    (hc : ¬ (d < e ∧ s.m.det g = d)) :
    Inv (setFrame s p s.m { f with pc := .f16 g e }) a := by
  have hF := (hI.p p).fr f hf
  have hw : f.pc.IsFwd := by rw [hpc]; simp [FPc.IsFwd]
  refine hI.local hf rfl rfl rfl rfl (fun _ => rfl) (hF.fwd_next hw (by simp [FPc.IsFwd]) ?_)
  have h5 := hF.stage
  simp only [StageOK, hpc] at h5
  refine ⟨h5.1, h5.2.1, fun hp => ?_⟩
  rcases h5.2.2 hp with h | h
  · exact h
  · exact absurd ⟨h.2, h.1⟩ hc

theorem step_f16 {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} {g e}
    (hI : Inv s a) (hf : (s.ps p).fr = some f) (hpc : f.pc = .f16 g e) :
    Inv (setFrame s p s.m { f with pc := .f17 g e (s.m.hval g) }) a := by
  have hF := (hI.p p).fr f hf
  have hw : f.pc.IsFwd := by rw [hpc]; simp [FPc.IsFwd]
  refine hI.local hf rfl rfl rfl rfl (fun _ => rfl) (hF.fwd_next hw (by simp [FPc.IsFwd]) ?_)
  have h5 := hF.stage
  simp only [StageOK, hpc] at h5
  exact ⟨h5.1, h5.2.1, fun hp => ⟨h5.2.2 hp, rfl⟩⟩

theorem step_f17 {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} {g e vh}
    (hI : Inv s a) (hf : (s.ps p).fr = some f) (hpc : f.pc = .f17 g e vh) :
    Inv (setFrame s p s.m { f with pc := .f18 g e vh (s.m.Y f.o) }) a := by
  have hF := (hI.p p).fr f hf
  have hw : f.pc.IsFwd := by rw [hpc]; simp [FPc.IsFwd]
  refine hI.local hf rfl rfl rfl rfl (fun _ => rfl) (hF.fwd_next hw (by simp [FPc.IsFwd]) ?_)
  have h5 := hF.stage
  simp only [StageOK, hpc] at h5
  exact ⟨fun hn => ⟨h5.1 hn, rfl⟩, h5.2.1, h5.2.2⟩

/-! ## Returns -/

theorem step_f14_none {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} {x}
    (hI : Inv s a) (hf : (s.ps p).fr = some f) (hpc : f.pc = .f14 x) (hx : x.1 = none) :
    ∃ a', Relation.ReflTransGen AStep a a' ∧
      Inv (applyNext s p s.m (afterCall (s.ps p).pc f.r)) a' := by
  have hF := (hI.p p).fr f hf
  have hw : f.pc.IsFwd := by rw [hpc]; simp [FPc.IsFwd]
  refine hI.ret hf hw (fun hn => ?_)
  have h5 := hF.stage
  simp only [StageOK, hpc] at h5
  have h0 := h5.1 hn
  have := hI.g.xnone f.o (by rw [← h0, hx])
  have := hn.1; unfold Pend at this; omega

theorem step_f18_skip {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} {g e vh y}
    (hI : Inv s a) (hf : (s.ps p).fr = some f) (hpc : f.pc = .f18 g e vh y)
    (hc : ¬ (y.1 < e ∧ s.m.Y f.o = y)) :
    ∃ a', Relation.ReflTransGen AStep a a' ∧
      Inv (applyNext s p s.m (afterCall (s.ps p).pc f.r)) a' := by
  have hF := (hI.p p).fr f hf
  have hw : f.pc.IsFwd := by rw [hpc]; simp [FPc.IsFwd]
  refine hI.ret hf hw (fun hn => ?_)
  have h5 := hF.stage
  simp only [StageOK, hpc] at h5
  obtain ⟨hX, hY⟩ := h5.1 hn
  have := hn.1; unfold Pend at this; rw [hX] at this
  exact hc ⟨by rw [hY]; exact this, hY.symm⟩

theorem step_f18_move {s : St P K V} {a : AS P K V} {p : P} {f : Frame P K V} {g e vh y}
    (hI : Inv s a) (hf : (s.ps p).fr = some f) (hpc : f.pc = .f18 g e vh y)
    (hc : y.1 < e ∧ s.m.Y f.o = y) :
    ∃ a', Relation.ReflTransGen AStep a a' ∧
      Inv (applyNext s p { s.m with Y := Function.update s.m.Y f.o (e, vh) }
        (afterCall (s.ps p).pc f.r)) a' := by
  have hF := (hI.p p).fr f hf
  have hw : f.pc.IsFwd := by rw [hpc]; simp [FPc.IsFwd]
  have h5 := hF.stage
  simp only [StageOK, hpc] at h5
  have hpa : PendAt s.m f.o g e := by
    rcases h5.2.1 with h | ⟨h, -⟩
    · exact h
    · rw [hc.2] at h; omega
  obtain ⟨hdet, hvh⟩ := h5.2.2 hpa
  obtain ⟨a1, hst, hI1⟩ := hI.move hpa hdet hvh
  obtain ⟨a', hr, hI'⟩ := hI1.ret (f := f) hf hw (fun hn => by
    have := hn.1; simp [Pend, hpa.1] at this)
  exact ⟨a', Relation.ReflTransGen.head hst hr, hI'⟩

end Podc.DuraCAS
