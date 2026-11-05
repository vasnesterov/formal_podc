import Papers.PODC2023.DuraCAS.CInv

/-!
# The per-process invariant is stable under memory changes made by other processes

The four kinds of shared-memory changes of DurEC: a write of `h.Val` (line 7), an install
(line 10), a help on `DetVal` (line 15), a move (line 18, with the ghost update of `ls`).
-/

set_option linter.unusedSectionVars false

namespace Podc.DuraCAS

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

theorem PInv.transfer' {m m' : Mem P K V} {ls ls' : Hd P → ℕ} {p : P} {st : PState P K V}
    {ap ap' : APS P K V} (h : PInv m ls p st ap) (hop : ap'.op = ap.op) (hor : ap'.orph = ap.orph)
    (hpc : ap'.pc = apcOf m' st)
    (hOrph : ∀ x, ap.orph = some x → COrphOK m p st x → COrphOK m' p st x)
    (hSc : ∀ f, st.fr = some f → FrameOK m ls p st ap.orph f → f.kind = .sc → ScOK m' f)
    (hStage : ∀ f, st.fr = some f → FrameOK m ls p st ap.orph f →
      StageOK m' ls' f (Need m' ap.orph f)) :
    PInv m' ls' p st ap' := by
  refine ⟨hop ▸ h.op, h.idle, h.idleFr, hpc, fun x hx => hOrph x (hor ▸ hx) (h.orph x (hor ▸ hx)),
    fun f hf => ?_⟩
  have hfo := h.fr f hf
  obtain ⟨h1, h2, h3, h4, h5⟩ := id hfo
  rw [hor]
  exact ⟨h1, h2, hSc f hf hfo, h4, hStage f hf hfo⟩

theorem PInv.transfer {m m' : Mem P K V} {ls ls' : Hd P → ℕ} {p : P} {st : PState P K V}
    {ap : APS P K V} (h : PInv m ls p st ap)
    (hMoved : ∀ f, st.fr = some f → (Moved m' f ↔ Moved m f))
    (hOrph : ∀ x, ap.orph = some x → COrphOK m p st x → COrphOK m' p st x)
    (hSc : ∀ f, st.fr = some f → FrameOK m ls p st ap.orph f → f.kind = .sc → ScOK m' f)
    (hStage : ∀ f, st.fr = some f → FrameOK m ls p st ap.orph f →
      StageOK m' ls' f (Need m' ap.orph f)) :
    PInv m' ls' p st ap := by
  refine h.transfer' rfl rfl ?_ hOrph hSc hStage
  rw [h.pc]; unfold apcOf
  cases hf : st.fr with
  | none => rfl
  | some f => simp only [hMoved f hf]

/-- Stability under an install on `o0` (by another process). -/
theorem PInv.of_install {m : Mem P K V} {ls : Hd P → ℕ} {q : P} {st : PState P K V}
    {ap : APS P K V} (h : PInv m ls q st ap) {o0 : Obj K} {hd : Hd P} {sh : ℕ}
    (hnp : ¬ Pend m o0) (hsh : (m.Y o0).1 < sh) :
    PInv { m with X := Function.update m.X o0 (some hd, sh) } ls q st ap := by
  have hX : ∀ o, o ≠ o0 → (Function.update m.X o0 (some hd, sh)) o = m.X o :=
    fun o ho => Function.update_of_ne ho _ _
  have hP : ∀ o, o ≠ o0 → (Pend { m with X := Function.update m.X o0 (some hd, sh) } o ↔
      Pend m o) := fun o ho => by simp [Pend, hX o ho]
  have hPA : ∀ o g e, o ≠ o0 →
      (PendAt { m with X := Function.update m.X o0 (some hd, sh) } o g e ↔ PendAt m o g e) :=
    fun o g e ho => by simp [PendAt, Pend, hX o ho]
  apply h.transfer
  · intro f _; exact Iff.rfl
  · intro x hx ⟨h1, h2, h3, h4, h5, h6⟩
    have hne : x.o ≠ o0 := by rintro rfl; exact hnp h3
    exact ⟨h1, by simp [hX _ hne, h2], (hP _ hne).2 h3, h4, h5, h6⟩
  · intro f hf hfo hk
    obtain ⟨hs, hfw⟩ := hfo.2.2.1 hk
    refine ⟨hs, fun hw => ⟨fun hr => ?_, fun hr => ?_⟩⟩
    · obtain ⟨hlt, hmv⟩ := (hfw hw).1 hr
      refine ⟨hlt, ?_⟩
      rcases hmv with hmv | ⟨hx, hy, hv⟩
      · exact Or.inl hmv
      · right
        by_cases hfo0 : f.o = o0
        · exfalso; apply hnp; rw [← hfo0]; unfold Pend; rw [hx, hy]; exact hlt
        · simp only [hX _ hfo0]; exact ⟨hx, hy, hv⟩
    · have := (hfw hw).2 hr
      by_cases hfo0 : f.o = o0
      · simp only [hfo0, Function.update_self]; rw [hfo0] at hs; omega
      · simp only [hX _ hfo0]; exact this
  · intro f hf hfo
    obtain ⟨_, _, hsc, hrec, hst⟩ := hfo
    apply hst.transfer
    · intro hw hn
      by_cases hfo0 : f.o = o0
      · exfalso
        obtain ⟨-, hn⟩ := hn
        rcases hn with ⟨hk, hr, hy⟩ | ⟨hk, hr, hy⟩ | ⟨hk, x, hx, hxo⟩
        · have := ((hsc hk).2 hw).2 hr
          apply hnp; rw [← hfo0]; unfold Pend; simp only at hy; omega
        · obtain ⟨hlt, hmv⟩ := ((hsc hk).2 hw).1 hr
          simp only at hy
          rcases hmv with hmv | ⟨hx, hy', -⟩
          · omega
          · apply hnp; rw [← hfo0]; unfold Pend; rw [hx, hy']; exact hlt
        · obtain ⟨-, -, h3, -⟩ := h.orph x hx
          rw [hxo, hfo0] at h3; exact hnp h3
      · refine ⟨⟨(hP _ hfo0).1 hn.1, hn.2⟩, hX _ hfo0, rfl⟩
    · intro g e hF
      by_cases hfo0 : f.o = o0
      · rcases hF with ⟨-, hp⟩ | hF
        · rw [hfo0] at hp; exact absurd hp hnp
        · exact Or.inr hF
      · rcases hF with hp | hF
        · exact Or.inl ((hPA _ _ _ hfo0).2 hp)
        · exact Or.inr hF
    · intro g e hF hp
      by_cases hfo0 : f.o = o0
      · exfalso
        obtain ⟨hx, -⟩ := hp
        simp only [hfo0, Function.update_self, Prod.mk.injEq, Option.some.injEq] at hx
        rcases hF with ⟨-, hp⟩ | ⟨hF, -⟩
        · rw [hfo0] at hp; exact hnp hp
        · rw [hfo0] at hF; omega
      · exact ⟨(hPA _ _ _ hfo0).1 hp, Or.inl rfl, rfl⟩
    · intro hw
      refine ⟨rfl, rfl, fun hs => ?_⟩
      by_cases hfo0 : f.o = o0
      · exfalso
        cases hk : f.kind
        · have := (hsc hk).1
          simp only [hfo0, Function.update_self] at hs; rw [hfo0] at this; omega
        · exact hw (hrec hk)
      · exact hX _ hfo0

/-- Stability under a write of `h0.Val` (line 7) by another process with no pending install. -/
theorem PInv.of_hval {m : Mem P K V} {ls : Hd P → ℕ} {q : P} {st : PState P K V}
    {ap : APS P K V} (h : PInv m ls q st ap) {h0 : Hd P} {v : V × Bool} (hq : h0.1 ≠ q)
    (hnp : ∀ o, (m.X o).1 = some h0 → ¬ Pend m o) :
    PInv { m with hval := Function.update m.hval h0 v } ls q st ap := by
  have hv : ∀ g : Hd P, g.1 = q → Function.update m.hval h0 v g = m.hval g := by
    intro g hg; apply Function.update_of_ne; rintro rfl; exact hq hg
  apply h.transfer
  · intro f _; exact Iff.rfl
  · intro x hx ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, by simp only [hv _ h1]; exact h5, h6⟩
  · intro f hf hfo hk
    obtain ⟨hs, hfw⟩ := hfo.2.2.1 hk
    refine ⟨hs, fun hw => ⟨fun hr => ?_, (hfw hw).2⟩⟩
    obtain ⟨hlt, hmv⟩ := (hfw hw).1 hr
    refine ⟨hlt, ?_⟩
    simp only [hv _ hfo.1]; exact hmv
  · intro f hf hfo
    obtain ⟨hh, _, _, _, hst⟩ := hfo
    apply hst.transfer
    · intro _ hn; exact ⟨hn, rfl, rfl⟩
    · intro g e hF; exact hF
    · intro g e _ hp
      refine ⟨hp, Or.inl rfl, ?_⟩
      apply Function.update_of_ne; rintro rfl
      exact hnp f.o (by have := hp.1; simp only at this; rw [this]) hp.2
    · intro _; exact ⟨hv _ hh, rfl, fun _ => rfl⟩

/-- Stability under a help on `g0.DetVal` (line 15), which writes the sequence number `e0` of the
pending install of `g0`. -/
theorem PInv.of_det {m : Mem P K V} {ls : Hd P → ℕ} {q : P} {st : PState P K V}
    {ap : APS P K V} (h : PInv m ls q st ap) (hg : CGInv m ls) {o0 : Obj K} {g0 : Hd P} {e0 : ℕ}
    (hpa : PendAt m o0 g0 e0) :
    PInv { m with det := Function.update m.det g0 e0 } ls q st ap := by
  apply h.transfer
  · intro f _; exact Iff.rfl
  · intro x _ hx; exact hx
  · intro f _ hfo hk; exact hfo.2.2.1 hk
  · intro f hf hfo
    obtain ⟨hh, _, _, _, hst⟩ := hfo
    apply hst.transfer
    · intro _ hn; exact ⟨hn, rfl, rfl⟩
    · intro g e hF; exact hF
    · intro g e _ hp
      refine ⟨hp, ?_, rfl⟩
      by_cases hg0 : g = g0
      · subst hg0
        have := hg.uniq _ _ _ _ (by rw [hp.1]) (by rw [hpa.1]) hp.2 hpa.2 rfl
        have hx := hp.1
        simp only at hx; rw [this, hpa.1] at hx
        simp only [Prod.mk.injEq] at hx
        right; simp [hx.2]
      · left; exact Function.update_of_ne hg0 _ _
    · intro _; exact ⟨rfl, rfl, fun _ => rfl⟩

/-- Stability under a move on `o0` of the install `(g0, e0)` of another process (with the ghost
update `ls g0 := e0`). -/
theorem PInv.of_move {m : Mem P K V} {ls : Hd P → ℕ} {q : P} {st : PState P K V}
    {ap : APS P K V} (h : PInv m ls q st ap) (hg : CGInv m ls) {o0 : Obj K} {g0 : Hd P} {e0 : ℕ}
    {vh : V × Bool} (hpa : PendAt m o0 g0 e0) (hq : g0.1 ≠ q) :
    PInv { m with Y := Function.update m.Y o0 (e0, vh) } (Function.update ls g0 e0) q st ap := by
  obtain ⟨hX0, hP0⟩ := hpa
  have hP0' := hP0
  unfold Pend at hP0'; rw [hX0] at hP0'; simp only at hP0'
  have hls0 : ls g0 < e0 := by
    have := hg.pendSeq o0 g0 (by rw [hX0]) hP0; rw [hX0] at this; simp only at this; omega
  have hY : ∀ o, o ≠ o0 → (Function.update m.Y o0 (e0, vh)) o = m.Y o :=
    fun o ho => Function.update_of_ne ho _ _
  have hYle : ∀ o, (m.Y o).1 ≤ ((Function.update m.Y o0 (e0, vh)) o).1 := by
    intro o; by_cases ho : o = o0
    · subst ho; simp; omega
    · rw [hY o ho]
  have hlsle : ∀ g, ls g ≤ Function.update ls g0 e0 g := by
    intro g; by_cases hg' : g = g0
    · subst hg'; simp; omega
    · rw [Function.update_of_ne hg']
  have hnp' : ¬ Pend { m with Y := Function.update m.Y o0 (e0, vh) } o0 := by
    simp [Pend, hX0]
  have hP : ∀ o, o ≠ o0 → (Pend { m with Y := Function.update m.Y o0 (e0, vh) } o ↔
      Pend m o) := fun o ho => by simp [Pend, hY o ho]
  have hPA : ∀ o g e, o ≠ o0 →
      (PendAt { m with Y := Function.update m.Y o0 (e0, vh) } o g e ↔ PendAt m o g e) :=
    fun o g e ho => by simp [PendAt, Pend, hY o ho]
  -- an installing frame of `q` on `o0` has been moved already
  have hmv : ∀ f, st.fr = some f → f.o = o0 → f.kind = .sc → f.r = true → Moved m f := by
    intro f hf hfo hk hr
    have hfr := h.fr f hf
    have hw : f.pc.IsFwd := by
      have := hfr.2.2.2.2; revert this; unfold StageOK
      cases f.pc <;> simp [FPc.IsFwd, hr]
    obtain ⟨-, hm⟩ := ((hfr.2.2.1 hk).2 hw).1 hr
    rcases hm with hm | ⟨hx, -, -⟩
    · exact ⟨hk, hr, hm⟩
    · rw [hfo, hX0] at hx; simp only [Prod.mk.injEq, Option.some.injEq] at hx
      exact absurd (hx.1 ▸ hfr.1) hq
  apply h.transfer
  · intro f hf
    unfold Moved
    by_cases hfo : f.o = o0
    · constructor
      · rintro ⟨hk, hr, -⟩; exact hmv f hf hfo hk hr
      · rintro ⟨hk, hr, hs⟩; exact ⟨hk, hr, le_trans hs (hYle _)⟩
    · simp only [hY _ hfo]
  · intro x hx ⟨h1, h2, h3, h4, h5, h6⟩
    have hne : x.o ≠ o0 := by
      rintro hxo; rw [hxo, hX0] at h2; simp only [Option.some.injEq] at h2
      exact hq (h2 ▸ h1)
    exact ⟨h1, h2, (hP _ hne).2 h3, by simp only [hY _ hne]; exact h4, h5, h6⟩
  · intro f hf hfo hk
    obtain ⟨hs, hfw⟩ := hfo.2.2.1 hk
    refine ⟨le_trans hs (hYle _), fun hw => ⟨fun hr => ?_, (hfw hw).2⟩⟩
    obtain ⟨hlt, hm⟩ := (hfw hw).1 hr
    refine ⟨hlt, ?_⟩
    by_cases hfo : f.o = o0
    · exact Or.inl (le_trans (hmv f hf hfo hk hr).2.2 (hYle _))
    · simp only [hY _ hfo]; exact hm
  · intro f hf hfo
    obtain ⟨hh, _, _, _, hst⟩ := hfo
    apply hst.transfer
    · intro _ hn
      by_cases hfo : f.o = o0
      · exact absurd (hfo ▸ hn.1) hnp'
      · refine ⟨⟨(hP _ hfo).1 hn.1, ?_⟩, rfl, hY _ hfo⟩
        have := hn.2; simp only [hY _ hfo] at this; exact this
    · intro g e hF
      by_cases hfo : f.o = o0
      · right
        rcases hF with ⟨hx, -⟩ | ⟨h1, h2⟩
        · rw [hfo, hX0] at hx; simp only [Prod.mk.injEq, Option.some.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          simp [hfo]
        · exact ⟨le_trans h1 (hYle _), le_trans h2 (hlsle _)⟩
      · rcases hF with hp | ⟨h1, h2⟩
        · exact Or.inl ((hPA _ _ _ hfo).2 hp)
        · right; simp only [hY _ hfo]; exact ⟨h1, le_trans h2 (hlsle _)⟩
    · intro g e _ hp
      by_cases hfo : f.o = o0
      · exact absurd (hfo ▸ hp.2) hnp'
      · exact ⟨(hPA _ _ _ hfo).1 hp, Or.inl rfl, rfl⟩
    · intro _
      refine ⟨rfl, ?_, fun _ => rfl⟩
      apply Function.update_of_ne; rintro rfl; exact hq hh

/-! ## The memory invariant under the four kinds of changes -/

theorem CGInv.of_hval {m : Mem P K V} {ls : Hd P → ℕ} (hg : CGInv m ls) (h0 : Hd P) (v : V × Bool) :
    CGInv { m with hval := Function.update m.hval h0 v } ls :=
  ⟨hg.1, hg.2, hg.3, hg.4, hg.5, hg.6, hg.7, hg.8⟩

theorem CGInv.of_det {m : Mem P K V} {ls : Hd P → ℕ} (hg : CGInv m ls) {o0 : Obj K} {g0 : Hd P}
    {e0 : ℕ} (hpa : PendAt m o0 g0 e0) :
    CGInv { m with det := Function.update m.det g0 e0 } ls := by
  obtain ⟨hX0, hP0⟩ := hpa
  have hls0 : ls g0 < e0 := by
    have := hg.pendSeq o0 g0 (by rw [hX0]) hP0; rw [hX0] at this; simp only at this; omega
  refine ⟨hg.yx, hg.xnone, hg.done, hg.pendSeq, ?_, ?_, ?_, hg.uniq⟩
  · intro o g hx hp
    by_cases hg0 : g = g0
    · subst hg0
      have := hg.uniq _ _ _ _ hx (by rw [hX0]) hp hP0 rfl
      subst this; right; simp [hX0]
    · simp only [Function.update_of_ne hg0]; exact hg.pendDet o g hx hp
  · intro g
    by_cases hg0 : g = g0
    · subst hg0; simp; omega
    · simp only [Function.update_of_ne hg0]; exact hg.lsDet g
  · intro g hn
    by_cases hg0 : g = g0
    · subst hg0; exact absurd hP0 (hn o0 (by rw [hX0]))
    · simp only [Function.update_of_ne hg0]; exact hg.detEq g hn

theorem CGInv.of_install {m : Mem P K V} {ls : Hd P → ℕ} (hg : CGInv m ls) {o0 : Obj K}
    {h0 : Hd P} {sh : ℕ} (hnp : ¬ Pend m o0) (hsh : sh = max (ls h0) (m.Y o0).1 + 1)
    (hfree : ∀ o g, (m.X o).1 = some g → g.1 = h0.1 → ¬ Pend m o) :
    CGInv { m with X := Function.update m.X o0 (some h0, sh) } ls := by
  have hX : ∀ o, o ≠ o0 → (Function.update m.X o0 (some h0, sh)) o = m.X o :=
    fun o ho => Function.update_of_ne ho _ _
  have hP : ∀ o, o ≠ o0 → (Pend { m with X := Function.update m.X o0 (some h0, sh) } o ↔
      Pend m o) := fun o ho => by simp [Pend, hX o ho]
  have hP0 : Pend { m with X := Function.update m.X o0 (some h0, sh) } o0 := by
    simp [Pend, hsh]
  have hdet : m.det h0 = ls h0 := hg.detEq h0 (fun o hx => hfree o h0 hx rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_, hg.lsDet, ?_, ?_⟩
  · intro o; by_cases ho : o = o0
    · subst ho; simp [hsh]; omega
    · simp only [hX o ho]; exact hg.yx o
  · intro o; by_cases ho : o = o0
    · subst ho; simp
    · simp only [hX o ho]; exact hg.xnone o
  · intro o g; by_cases ho : o = o0
    · subst ho; intro _ h; exact absurd hP0 h
    · simp only [hX o ho]; intro hx hn; exact hg.done o g hx (fun h => hn ((hP o ho).2 h))
  · intro o g; by_cases ho : o = o0
    · subst ho; simp only [Function.update_self, Option.some.injEq]; rintro rfl _; exact hsh
    · simp only [hX o ho]; intro hx hp; exact hg.pendSeq o g hx ((hP o ho).1 hp)
  · intro o g; by_cases ho : o = o0
    · subst ho; simp only [Function.update_self, Option.some.injEq]; rintro rfl _
      exact Or.inl hdet
    · simp only [hX o ho]; intro hx hp; exact hg.pendDet o g hx ((hP o ho).1 hp)
  · intro g hn; apply hg.detEq g; intro o hx hp
    by_cases ho : o = o0
    · subst ho; exact hnp hp
    · exact hn o (by simp only [hX o ho]; exact hx) ((hP o ho).2 hp)
  · intro o o' g g' hx hx' hp hp' hgg
    by_cases ho : o = o0 <;> by_cases ho' : o' = o0
    · rw [ho, ho']
    · exfalso; subst ho
      simp only [Function.update_self, Option.some.injEq] at hx; subst hx
      simp only [hX o' ho'] at hx'
      exact hfree o' g' hx' hgg.symm ((hP o' ho').1 hp')
    · exfalso; subst ho'
      simp only [Function.update_self, Option.some.injEq] at hx'; subst hx'
      simp only [hX o ho] at hx
      exact hfree o g hx hgg ((hP o ho).1 hp)
    · simp only [hX o ho] at hx; simp only [hX o' ho'] at hx'
      exact hg.uniq o o' g g' hx hx' ((hP o ho).1 hp) ((hP o' ho').1 hp') hgg

theorem CGInv.of_move {m : Mem P K V} {ls : Hd P → ℕ} (hg : CGInv m ls) {o0 : Obj K} {g0 : Hd P}
    {e0 : ℕ} {vh : V × Bool} (hpa : PendAt m o0 g0 e0) (hdet : m.det g0 = e0) :
    CGInv { m with Y := Function.update m.Y o0 (e0, vh) } (Function.update ls g0 e0) := by
  obtain ⟨hX0, hP0⟩ := hpa
  have hY : ∀ o, o ≠ o0 → (Function.update m.Y o0 (e0, vh)) o = m.Y o :=
    fun o ho => Function.update_of_ne ho _ _
  have hnp' : ¬ Pend { m with Y := Function.update m.Y o0 (e0, vh) } o0 := by
    simp [Pend, hX0]
  have hP : ∀ o, o ≠ o0 → (Pend { m with Y := Function.update m.Y o0 (e0, vh) } o ↔
      Pend m o) := fun o ho => by simp [Pend, hY o ho]
  have hls0 : ls g0 < e0 := by
    have := hg.pendSeq o0 g0 (by rw [hX0]) hP0; rw [hX0] at this; simp only at this; omega
  have hlsle : ∀ g, ls g ≤ Function.update ls g0 e0 g := by
    intro g; by_cases hg' : g = g0
    · subst hg'; simp; omega
    · rw [Function.update_of_ne hg']
  -- a pending install other than `o0` is not of handle `g0`
  have hne : ∀ o g, o ≠ o0 → (m.X o).1 = some g → Pend m o → g ≠ g0 := by
    rintro o g ho hx hp rfl
    exact ho (hg.uniq o o0 g g hx (by rw [hX0]) hp hP0 rfl)
  refine ⟨?_, hg.xnone, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o; by_cases ho : o = o0
    · subst ho; simp [hX0]
    · simp only [hY o ho]; exact hg.yx o
  · intro o g; by_cases ho : o = o0
    · subst ho; simp only [hX0, Option.some.injEq]; rintro rfl _; simp
    · intro hx hn
      exact le_trans (hg.done o g hx (fun h => hn ((hP o ho).2 h))) (hlsle g)
  · intro o g; by_cases ho : o = o0
    · subst ho; intro _ h; exact absurd h hnp'
    · intro hx hp; have hp' := (hP o ho).1 hp
      simp only [hY o ho, Function.update_of_ne (hne o g ho hx hp')]
      exact hg.pendSeq o g hx hp'
  · intro o g; by_cases ho : o = o0
    · subst ho; intro _ h; exact absurd h hnp'
    · intro hx hp; have hp' := (hP o ho).1 hp
      simp only [Function.update_of_ne (hne o g ho hx hp')]
      exact hg.pendDet o g hx hp'
  · intro g; by_cases hg' : g = g0
    · subst hg'; simp [hdet]
    · simp only [Function.update_of_ne hg']; exact hg.lsDet g
  · intro g hn; by_cases hg' : g = g0
    · subst hg'; simp [hdet]
    · simp only [Function.update_of_ne hg']
      apply hg.detEq g; intro o hx hp
      by_cases ho : o = o0
      · subst ho; rw [hX0] at hx; simp only [Option.some.injEq] at hx; exact hg' hx.symm
      · exact hn o hx ((hP o ho).2 hp)
  · intro o o' g g' hx hx' hp hp' hgg
    have ho : o ≠ o0 := fun h => hnp' (h ▸ hp)
    have ho' : o' ≠ o0 := fun h => hnp' (h ▸ hp')
    exact hg.uniq o o' g g' hx hx' ((hP o ho).1 hp) ((hP o' ho').1 hp') hgg

/-! ## Moves: the owner of the moved install -/

section move
variable {m : Mem P K V} {ls : Hd P → ℕ} {o0 : Obj K} {g0 : Hd P} {e0 : ℕ} {vh : V × Bool}

theorem Fresh.of_move (hg : CGInv m ls) (hpa : PendAt m o0 g0 e0) {o g e}
    (hF : Fresh m ls o g e) :
    Fresh { m with Y := Function.update m.Y o0 (e0, vh) } (Function.update ls g0 e0) o g e := by
  obtain ⟨hX0, hP0⟩ := hpa
  have hP0' := hP0
  unfold Pend at hP0'; rw [hX0] at hP0'; simp only at hP0'
  have hls0 : ls g0 < e0 := by
    have := hg.pendSeq o0 g0 (by rw [hX0]) hP0; rw [hX0] at this; simp only at this; omega
  have hYle : ∀ o, (m.Y o).1 ≤ ((Function.update m.Y o0 (e0, vh)) o).1 := by
    intro o; by_cases ho : o = o0
    · subst ho; simp; omega
    · rw [Function.update_of_ne ho]
  have hlsle : ∀ g, ls g ≤ Function.update ls g0 e0 g := by
    intro g; by_cases hg' : g = g0
    · subst hg'; simp; omega
    · rw [Function.update_of_ne hg']
  by_cases ho : o = o0
  · subst ho; right
    rcases hF with ⟨hx, -⟩ | ⟨h1, h2⟩
    · rw [hX0] at hx; simp only [Prod.mk.injEq, Option.some.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      simp
    · exact ⟨le_trans h1 (hYle _), le_trans h2 (hlsle _)⟩
  · rcases hF with ⟨hx, hp⟩ | ⟨h1, h2⟩
    · left; refine ⟨hx, ?_⟩; simp only [Pend, Function.update_of_ne ho]; exact hp
    · right; simp only [Function.update_of_ne ho]; exact ⟨h1, le_trans h2 (hlsle _)⟩

theorem Pend.of_move (hpa : PendAt m o0 g0 e0) {o}
    (hp : Pend { m with Y := Function.update m.Y o0 (e0, vh) } o) : o ≠ o0 ∧ Pend m o := by
  have ho : o ≠ o0 := by
    rintro rfl; unfold Pend at hp; simp [hpa.1] at hp
  refine ⟨ho, ?_⟩; unfold Pend at hp ⊢; simpa [Function.update_of_ne ho] using hp

/-- The process owning the moved install by its active frame: the `ECSC` is linearized. -/
theorem PInv.of_move_frame {q : P} {st : PState P K V} {ap : APS P K V}
    (h : PInv m ls q st ap) (hg : CGInv m ls) (hpa : PendAt m o0 g0 e0)
    {f0 : Frame P K V} (hf0 : st.fr = some f0) (hk : f0.kind = .sc) (hr : f0.r = true)
    (ho : f0.o = o0) (hsh : f0.sh = e0) (hw : f0.pc.IsFwd) (hor : ap.orph = none) :
    PInv { m with Y := Function.update m.Y o0 (e0, vh) } (Function.update ls g0 e0) q st
      { ap with pc := .aft st.pc true } := by
  have hfr := h.fr f0 hf0
  have hlt : f0.s < f0.sh := (((hfr.2.2.1 hk).2 hw).1 hr).1
  have hmv : Moved { m with Y := Function.update m.Y o0 (e0, vh) } f0 := by
    refine ⟨hk, hr, ?_⟩; simp [ho, hsh]
  refine h.transfer' rfl rfl ?_ ?_ ?_ ?_
  · simp [apcOf, hf0, hmv]
  · intro x hx; rw [hor] at hx; cases hx
  · intro f hf _ _
    rw [hf0] at hf; cases hf
    refine ⟨?_, fun _ => ⟨fun _ => ⟨hlt, Or.inl hmv.2.2⟩, fun h' => by rw [hr] at h'; cases h'⟩⟩
    simp [ho]; omega
  · intro f hf hfo
    rw [hf0] at hf; cases hf
    apply hfo.2.2.2.2.transfer
    · intro _ hn; exact absurd (ho ▸ hn.1) (fun hp => (Pend.of_move hpa hp).1 rfl)
    · intro g e hF; exact hF.of_move hg hpa
    · intro g e _ hp
      have := Pend.of_move hpa hp.2
      exact ⟨⟨hp.1, this.2⟩, Or.inl rfl, rfl⟩
    · intro h'; exact absurd hw h'

/-- The process owning the moved install as an orphan: the orphan takes effect. -/
theorem PInv.of_move_orph {q : P} {st : PState P K V} {ap : APS P K V}
    (h : PInv m ls q st ap) (hg : CGInv m ls) (hpa : PendAt m o0 g0 e0)
    (hrec : ∀ f, st.fr = some f → f.kind = .recov) :
    PInv { m with Y := Function.update m.Y o0 (e0, vh) } (Function.update ls g0 e0) q st
      { ap with orph := none } := by
  refine ⟨h.op, h.idle, h.idleFr, ?_, fun x hx => (by cases hx), fun f hf => ?_⟩
  · show ap.pc = _
    rw [h.pc]; unfold apcOf
    cases hf : st.fr with
    | none => rfl
    | some f =>
      have hk := hrec f hf
      simp [Moved, hk]
  · have hk := hrec f hf
    obtain ⟨h1, h2, -, h4, h5⟩ := h.fr f hf
    refine ⟨h1, h2, fun h' => (by rw [hk] at h'; cases h'), h4, ?_⟩
    apply h5.transfer
    · intro _ hn
      exfalso
      rcases hn.2 with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, x, hx, -⟩
      · rw [hk] at h'; cases h'
      · rw [hk] at h'; cases h'
      · cases hx
    · intro g e hF; exact hF.of_move hg hpa
    · intro g e _ hp
      have := Pend.of_move hpa hp.2
      exact ⟨⟨hp.1, this.2⟩, Or.inl rfl, rfl⟩
    · intro h'; exact absurd (h4 hk) h'

end move

end Podc.DuraCAS
