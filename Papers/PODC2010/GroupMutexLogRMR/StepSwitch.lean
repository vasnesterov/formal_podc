import Papers.PODC2010.GroupMutexLogRMR.Frame

/-!
# Preservation of `Inv`: successful `SC`s on `S` (lines 5.4 and 16.10): the session switches

Both steps switch `S` from `(s₀, e₀) = (S.1, S.2.1)` to `(sh, dh)` (the value of `Min(Q)` read
by `p`), clear every link on `S`, and move `p` to line 5.5 resp. 16.11. Before the step no
process of session `s₀` is of side `e₀` (`NoSide`), `sh ≠ s₀`, and some process of session `sh`
and side `dh` is at lines 5.1–8 (`ExW`). `sw_inv` shows that such a switch preserves the global
clauses and the clauses of every other process; the two step theorems add the clauses of `p`.
-/

namespace Podc.GroupMutexLogRMR

variable {n : ℕ} {J : Type}

/-- The configuration after a successful `SC(S, (sh, dh, s_p))` by `p` that moves `p` to `pc'`. -/
def sw_cfg (c : Cfg n J) (p : Fin n) (sh : J) (dh : Bool) (pc' : PC) : Cfg n J :=
  (c.scS (sh, dh, (c.loc p).s)).setLoc p { c.loc p with pc := pc' }

/-- The two switching moves of the program counter: 5.4 → 5.5 and 16.10 → 16.11. -/
def SwPC (a b : PC) : Prop := (a = .l5_4 ∧ b = .l5_5) ∨ (a = .l16_10 ∧ b = .l16_11)

section SwCfg

variable (c : Cfg n J) (p : Fin n) (sh : J) (dh : Bool) (pc' : PC)

@[simp] theorem sw_cfg_S : (sw_cfg c p sh dh pc').S = (sh, dh, (c.loc p).s) := rfl
@[simp] theorem sw_cfg_linkS : (sw_cfg c p sh dh pc').linkS = fun _ => false := rfl
@[simp] theorem sw_cfg_Ex : (sw_cfg c p sh dh pc').Ex = c.Ex := rfl
@[simp] theorem sw_cfg_G : (sw_cfg c p sh dh pc').G = c.G := rfl
@[simp] theorem sw_cfg_In : (sw_cfg c p sh dh pc').In = c.In := rfl
@[simp] theorem sw_cfg_Out : (sw_cfg c p sh dh pc').Out = c.Out := rfl
@[simp] theorem sw_cfg_Exclear : (sw_cfg c p sh dh pc').Exclear = c.Exclear := rfl
@[simp] theorem sw_cfg_C : (sw_cfg c p sh dh pc').C = c.C := rfl
@[simp] theorem sw_cfg_Q : (sw_cfg c p sh dh pc').Q = c.Q := rfl
@[simp] theorem sw_cfg_linkEx : (sw_cfg c p sh dh pc').linkEx = c.linkEx := rfl

theorem sw_cfg_loc_ne {z : Fin n} (hz : z ≠ p) : (sw_cfg c p sh dh pc').loc z = c.loc z := by
  simp [sw_cfg, Function.update_of_ne hz, Cfg.scS]

@[simp] theorem sw_cfg_loc_self : (sw_cfg c p sh dh pc').loc p = { c.loc p with pc := pc' } := by
  simp [sw_cfg, Cfg.scS]

@[simp] theorem sw_cfg_s (z : Fin n) : ((sw_cfg c p sh dh pc').loc z).s = (c.loc z).s := by
  by_cases hz : z = p
  · subst hz; simp
  · rw [sw_cfg_loc_ne c p sh dh pc' hz]

@[simp] theorem sw_cfg_d (z : Fin n) : ((sw_cfg c p sh dh pc').loc z).d = (c.loc z).d := by
  by_cases hz : z = p
  · subst hz; simp
  · rw [sw_cfg_loc_ne c p sh dh pc' hz]

@[simp] theorem sw_cfg_tm (z : Fin n) : ((sw_cfg c p sh dh pc').loc z).tm = (c.loc z).tm := by
  by_cases hz : z = p
  · subst hz; simp
  · rw [sw_cfg_loc_ne c p sh dh pc' hz]

@[simp] theorem sw_cfg_a (z : Fin n) : ((sw_cfg c p sh dh pc').loc z).a = (c.loc z).a := by
  by_cases hz : z = p
  · subst hz; simp
  · rw [sw_cfg_loc_ne c p sh dh pc' hz]

@[simp] theorem sw_cfg_b (z : Fin n) : ((sw_cfg c p sh dh pc').loc z).b = (c.loc z).b := by
  by_cases hz : z = p
  · subst hz; simp
  · rw [sw_cfg_loc_ne c p sh dh pc' hz]

end SwCfg

variable [DecidableEq J]

variable {c : Cfg n J} {p : Fin n} {sh : J} {dh : Bool} {pc' : PC}

omit [DecidableEq J] in
theorem sw_pc (hpc : SwPC (c.loc p).pc pc') (z : Fin n) :
    ((sw_cfg c p sh dh pc').loc z).pc = (c.loc z).pc ∨
      (z = p ∧ SwPC (c.loc z).pc ((sw_cfg c p sh dh pc').loc z).pc) := by
  by_cases hz : z = p
  · subst hz; right; exact ⟨rfl, by simpa using hpc⟩
  · left; rw [sw_cfg_loc_ne c p sh dh pc' hz]

theorem sw_cnt (hpc : SwPC (c.loc p).pc pc') (z : Fin n) (s : J) (d : Bool) :
    ((sw_cfg c p sh dh pc').loc z).cnt s d = (c.loc z).cnt s d := by
  by_cases hz : z = p
  · subst hz
    rcases hpc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [Loc.cnt, h1, h2, PC.btw, PC.idx]
  · rw [sw_cfg_loc_ne c p sh dh pc' hz]

omit [DecidableEq J] in
theorem sw_pside (hpc : SwPC (c.loc p).pc pc') (z : Fin n) :
    ((sw_cfg c p sh dh pc').loc z).pside = (c.loc z).pside := by
  by_cases hz : z = p
  · subst hz
    rcases hpc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [Loc.pside, h1, h2, PC.btw, PC.idx]
  · rw [sw_cfg_loc_ne c p sh dh pc' hz]

omit [DecidableEq J] in
/-- `pside` at lines 1.7–16.6. -/
theorem sw_pside_of {l : Loc J} (h : PC.btw .l1_7 .l16_6 l.pc) : l.pside = some l.d := by
  have h6 : l.pc ≠ .l1_6 := by intro h'; rw [h'] at h; exact absurd h.1 (by decide)
  have h' : PC.btw .l1_4 .l16_6 l.pc := ⟨le_trans (by decide) h.1, h.2⟩
  simp [Loc.pside, h6, h']

omit [DecidableEq J] in
theorem sw_ns_false {s : J} {e : Bool} (hns : NoSide c s e) {m : Fin n} (hs : (c.loc m).s = s)
    (hd : (c.loc m).d = e) (h : PC.btw .l1_7 .l16_6 (c.loc m).pc) : False :=
  (hns m hs).2.2 (by rw [sw_pside_of h, hd])

theorem sw_bool : ∀ a b e : Bool, a ≠ e → b ≠ e → a = b := by decide

/-- Nobody is at lines 5.5 or 16.11 when nobody is of `S`'s side. -/
theorem sw_noU (hI : Inv c) (hns : NoSide c c.S.1 c.S.2.1) (z : Fin n) :
    (c.loc z).pc ≠ .l5_5 ∧ (c.loc z).pc ≠ .l16_11 := by
  constructor
  · intro h5
    obtain ⟨sh', dh', -, h1, h2⟩ := (hI.li z).p5 h5
    by_cases hs : sh' = (c.loc z).s
    · obtain ⟨e1, e2, e3⟩ := h2 hs
      exact sw_ns_false hns (by rw [e1, hs]) (by rw [e2, e3]) (by rw [h5]; decide)
    · obtain ⟨e1, -, m, m1, m2, m3⟩ := h1 hs
      exact sw_ns_false hns (by rw [e1, m1]) (by rw [e1, m2])
        ⟨le_trans (by decide) m3.1, le_trans m3.2 (by decide)⟩
  · intro h11
    obtain ⟨sh', dh', -, e1, -, -, m, m1, m2, m3⟩ := (hI.li z).p11 h11
    exact sw_ns_false hns (by rw [e1, m1]) (by rw [e1, m2])
      ⟨le_trans (by decide) m3.1, le_trans m3.2 (by decide)⟩

/-- `Out[S.1] = S.2.1` when nobody is of `S`'s side (by `g8`). -/
theorem sw_out0 (hI : Inv c) (hns : NoSide c c.S.1 c.S.2.1) : c.Out c.S.1 = c.S.2.1 := by
  by_contra h
  obtain ⟨z, hz, -⟩ := hI.g8 h
  rcases hz with hz | hz
  · exact (sw_noU hI hns z).1 hz
  · exact (sw_noU hI hns z).2 hz

theorem sw_In_sh (hI : Inv c) (hne : sh ≠ c.S.1) (hw : ExW c sh dh .l5_1 .l8) : c.In sh = dh := by
  obtain ⟨m, m1, m2, m3⟩ := hw
  exact (hI.g7 sh m (Ne.symm hne) m1 dh (by
    rw [sw_pside_of ⟨le_trans (by decide) m3.1, le_trans m3.2 (by decide)⟩, m2])).symm

theorem sw_Out_sh (hI : Inv c) (hne : sh ≠ c.S.1) (hw : ExW c sh dh .l5_1 .l8) : c.Out sh ≠ dh := by
  rcases hI.g4 sh with h | ⟨h, -⟩
  · rw [← sw_In_sh hI hne hw]; exact Ne.symm h
  · exact absurd h.symm hne

omit [DecidableEq J] in
theorem sw_ExW (hpc : SwPC (c.loc p).pc pc') {s' : J} {d' : Bool} (hw : ExW c s' d' .l5_1 .l8) :
    ExW (sw_cfg c p sh dh pc') s' d' .l5_1 .l8 := by
  obtain ⟨m, m1, m2, m3⟩ := hw
  refine ⟨m, by simpa using m1, by simpa using m2, ?_⟩
  rcases sw_pc hpc m with e | ⟨-, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩
  · rw [e]; exact m3
  · rw [e2]; decide
  · rw [e1] at m3; exact absurd m3 (by decide)

/-- The clauses of every process `y ≠ p` survive a switch. -/
theorem sw_LI_other (hI : Inv c) (hpc : SwPC (c.loc p).pc pc') (hns : NoSide c c.S.1 c.S.2.1)
    (hne : sh ≠ c.S.1) (hw : ExW c sh dh .l5_1 .l8) {y : Fin n} (hy : y ≠ p) :
    LI (sw_cfg c p sh dh pc') y := by
  have hL := hI.li y
  have ly : (sw_cfg c p sh dh pc').loc y = c.loc y := sw_cfg_loc_ne c p sh dh pc' hy
  have hU := sw_noU hI hns
  constructor
  · rw [ly, sw_cfg_G]; exact hL.tm
  · -- l1
    rw [ly, sw_cfg_S]
    intro h1 h2 h3
    exfalso
    have hd := hI.g7 sh y (Ne.symm hne) h2.symm (c.loc y).d
      (sw_pside_of ⟨h1.1, le_trans h1.2 (by decide)⟩)
    rw [sw_In_sh hI hne hw] at hd
    rw [hd] at h3
    simp at h3
  · -- l14
    rw [ly, sw_cfg_S, sw_cfg_In]
    intro h1
    rcases hL.l14 h1 with h | ⟨h2, h3⟩
    · exact Or.inl h
    · exfalso
      rcases h1 with h1 | h1
      · exact (hns y h2.symm).2.2 (by simp [Loc.pside, h1, PC.btw, PC.idx, h3])
      · exact (hns y h2.symm).1 h1
  · -- l16
    rw [ly]
    intro h1
    exact absurd h1 (hns y (hL.l16 h1).1.symm).2.1
  · -- i5
    rw [ly]
    intro h1
    obtain ⟨h2, h3, -⟩ := hL.i5 h1
    exact (sw_ns_false hns h2.symm h3.symm ⟨le_trans (by decide) h1.1, h1.2⟩).elim
  · -- i7
    rw [ly]
    intro h1
    have h := hL.i7 h1
    exact (sw_ns_false hns (by rw [h]) (by rw [h]) (by rw [h1]; decide)).elim
  · -- i8
    rw [ly, sw_cfg_Out]
    intro h1 h2
    obtain ⟨h3, h4⟩ := hL.i8 h1 h2
    exact (sw_ns_false hns h3.symm h4.symm ⟨h1.1, le_trans h1.2 (by decide)⟩).elim
  · intro _ h; simp at h
  · intro _ h; simp at h
  · intro _ h; simp at h
  · rw [ly]; intro h1; exact absurd h1 (hU y).1
  · intro _ h; simp at h
  · intro _ h; simp at h
  · intro _ h; simp at h
  · -- x3
    rw [ly, sw_cfg_linkEx]
    intro h1 h2 dh' hb'
    obtain ⟨m, m1, m2, m3, m4⟩ := hL.x3 h1 h2 dh' hb'
    refine ⟨m, by simpa using m1, by simpa using m2, ?_⟩
    rcases sw_pc hpc m with e | ⟨-, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩
    · rw [e]; exact ⟨m3, m4⟩
    · rw [e2]; exact ⟨by decide, fun h => absurd h (by decide)⟩
    · rw [e1] at m3; exact absurd m3 (by decide)
  · intro _ h; simp at h
  · intro _ h; simp at h
  · rw [ly]; intro h1; exact absurd h1 (hU y).2
  · rw [ly, sw_cfg_linkEx, sw_cfg_Ex]; exact hL.w1
  · -- w2
    rw [ly, sw_cfg_linkEx]
    intro h1 h2 z hz
    have hz' : PC.btw .l11 .l16_3 (c.loc z).pc ∨ ((c.loc z).pc = .l10 ∧ c.linkEx z = false) := by
      rcases sw_pc hpc z with e | ⟨-, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩
      · rw [e] at hz; exact hz
      · rw [e2] at hz; simp [PC.btw, PC.idx] at hz
      · rw [e2] at hz; simp [PC.btw, PC.idx] at hz
    obtain ⟨k1, k2, k3⟩ := hL.w2 h1 h2 z hz'
    exact ⟨by simpa using k1, by simpa using k2, k3⟩
  · rw [ly, sw_cfg_linkEx, sw_cfg_Ex]; exact hL.w3
  · -- w4
    rw [ly, sw_cfg_linkEx, sw_cfg_S]
    intro _ _ _
    obtain ⟨m, m1, m2, m3⟩ := sw_ExW (sh := sh) (dh := dh) hpc hw
    exact ⟨m, m1, m2, ⟨m3.1, le_trans m3.2 (by decide)⟩,
      fun h => by rw [h] at m3; exact absurd m3 (by decide)⟩
  · rw [ly, sw_cfg_linkEx, sw_cfg_Exclear]; exact hL.w5
  · -- win
    rw [ly, sw_cfg_Ex, sw_cfg_Exclear, sw_cfg_linkEx]
    intro h1
    obtain ⟨e1, e2, e3⟩ := hL.win h1
    refine ⟨e1, e2, fun z hzy => ?_⟩
    have h := e3 z hzy
    rcases sw_pc hpc z with e | ⟨-, ⟨f1, f2⟩ | ⟨f1, f2⟩⟩
    · rw [e, sw_cfg_a]; exact h
    · rw [f2]; simp [PC.btw, PC.idx]
    · rw [f1] at h; exact absurd (by decide) h.1
  · -- winS
    rw [ly, sw_cfg_S]
    intro _ _
    obtain ⟨m, m1, m2, m3⟩ := sw_ExW (sh := sh) (dh := dh) hpc hw
    exact ⟨m, m1, m2, ⟨m3.1, le_trans m3.2 (by decide)⟩⟩
  · -- p13
    rw [ly, sw_cfg_S, sw_cfg_Out]
    intro h1
    right
    have hwin : PC.btw .l16_10 .l16_14 (c.loc y).pc := by rw [h1]; decide
    have hy0 : (c.loc y).s = c.S.1 := by
      by_contra hne'
      obtain ⟨m, m1, m2, m3⟩ := hL.winS hwin (Ne.symm hne')
      exact sw_ns_false hns m1 m2 ⟨le_trans (by decide) m3.1, le_trans m3.2 (by decide)⟩
    rcases hL.p13 h1 with h | ⟨-, h3, h4⟩
    · have ha1 : (c.loc y).a.1 = c.S.1 := by rw [h]
      have ha2 : (c.loc y).a.2 = c.S.2.1 := by rw [h]
      refine ⟨?_, ?_, ?_⟩
      · rw [ha1, ha2]; exact sw_out0 hI hns
      · rw [ha1]; exact hne
      · rw [ha1, hy0]
    · exact absurd (h4.trans hy0).symm h3

/-- **A switch preserves the invariant**, given the clauses of `p` after the step. -/
theorem sw_inv (hI : Inv c) (hpc : SwPC (c.loc p).pc pc') (hb : (c.loc p).b = some (sh, dh))
    (hns : NoSide c c.S.1 c.S.2.1) (hne : sh ≠ c.S.1) (hw : ExW c sh dh .l5_1 .l8)
    (hLp : LI (sw_cfg c p sh dh pc') p) : Inv (sw_cfg c p sh dh pc') := by
  have hU := sw_noU hI hns
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s d
    rw [sw_cfg_C, hI.gC s d]
    exact Finset.sum_congr rfl fun z _ => (sw_cnt hpc z s d).symm
  · intro z
    rw [sw_cfg_Q, hI.gQ z]
    rcases sw_pc (sh := sh) (dh := dh) hpc z with e | ⟨rfl, -⟩
    · simp only [e, sw_cfg_s, sw_cfg_d, sw_cfg_tm]
    · rcases hpc with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> simp [f1, f2, PC.btw, PC.idx]
  · intro s
    rw [sw_cfg_In, sw_cfg_Out]
    left
    rcases hI.g4 s with h | ⟨h1, h2⟩
    · exact h
    · subst h1; rw [← h2]; exact hI.in_ne_of_noSide hns
  · intro s h1 _
    rw [sw_cfg_S] at h1 ⊢
    obtain ⟨m, m1, m2, m3⟩ := sw_ExW (sh := sh) (dh := dh) hpc hw
    refine ⟨m, m1.trans h1, ?_, ⟨le_trans (by decide) m3.1, le_trans m3.2 (by decide)⟩⟩
    rw [sw_pside_of ⟨le_trans (by decide) m3.1, le_trans m3.2 (by decide)⟩, m2]
  · intro s y h1 h2 e he
    rw [sw_cfg_S] at h1
    rw [sw_cfg_In]
    rw [sw_cfg_s] at h2
    rw [sw_pside hpc] at he
    by_cases hs : c.S.1 = s
    · subst hs
      exact sw_bool _ _ _ (fun h => (hns y h2).2.2 (by rw [he, h]))
        (hI.in_ne_of_noSide hns)
    · exact hI.g7 s y hs h2 e he
  · intro y z hyz hy
    by_cases hyp : y = p
    · subst hyp
      rw [sw_cfg_loc_ne c y sh dh pc' (Ne.symm hyz)]
      exact hU z
    · rw [sw_cfg_loc_ne c p sh dh pc' hyp] at hy
      exfalso
      rcases hy with h | h
      · exact (hU y).1 h
      · exact (hU y).2 h
  · intro _
    refine ⟨p, ?_, by simp [hb], by simp⟩
    rcases hpc with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  · intro y
    by_cases hy : y = p
    · subst hy; exact hLp
    · exact sw_LI_other hI hpc hns hne hw hy

/-- Line 5.4, successful `SC(S, (sh, dh, s))`. -/
theorem inv_step_l5_4_succ (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l5_4)
    (hl : c.linkS p = true) : Inv (c.step p σ) := by
  have hL := hI.li p
  obtain ⟨sh, dh, hb, hw0⟩ := hL.a2 (Or.inr hp) hl
  obtain ⟨hns, hsh⟩ := hL.a3 hp hl
  have hne := hsh sh dh hb
  have hw := hw0 hne
  have hstep : c.step p σ = sw_cfg c p sh dh .l5_5 := by
    simp [Cfg.step, hp, hb, hl, sw_cfg, Cfg.scS]
  rw [hstep]
  have hpc : SwPC (c.loc p).pc .l5_5 := Or.inl ⟨hp, rfl⟩
  apply sw_inv hI hpc hb hns hne hw
  -- `p` is of side `dh` if it is of session `sh`
  have hdp : (c.loc p).s = sh → (c.loc p).d = dh := fun h => by
    have := hI.g7 sh p (Ne.symm hne) h (c.loc p).d (sw_pside_of (by rw [hp]; decide))
    rw [this, sw_In_sh hI hne hw]
  constructor <;> simp only [sw_cfg_loc_self, sw_cfg_linkS, sw_cfg_S, sw_cfg_G, sw_cfg_Out,
    sw_cfg_In, sw_cfg_Ex, sw_cfg_Exclear, sw_cfg_linkEx]
  case tm => intro _; exact hL.tm (by rw [hp]; decide)
  case l1 => intro _ h2 h3; exfalso; rw [hdp h2.symm] at h3; simp at h3
  case i8 =>
    intro _ h2
    obtain ⟨h3, h4⟩ := hL.i8 (by rw [hp]; decide) h2
    exact (sw_ns_false hns h3.symm h4.symm (by rw [hp]; decide)).elim
  case p5 =>
    intro _
    exact ⟨sh, dh, hb, fun _ => ⟨rfl, sw_Out_sh hI hne hw, sw_ExW hpc hw⟩,
      fun h => ⟨rfl, rfl, hdp h.symm⟩⟩
  all_goals (intro h; first | exact absurd h (by decide) | simp at h)

/-- Line 16.10, successful `SC(S, (sh, dh, s))`. -/
theorem inv_step_l16_10_succ (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_10)
    (hl : c.linkS p = true) : Inv (c.step p σ) := by
  have hL := hI.li p
  obtain ⟨hns0, sh, dh, hb, hne0, hw⟩ := hL.e3 hp hl
  obtain ⟨hS1, hS2⟩ := hL.e1 (by rw [hp]; decide) hl
  have hns : NoSide c c.S.1 c.S.2.1 := by rw [hS1, hS2]; exact hns0
  have hne : sh ≠ c.S.1 := by rw [hS1]; exact hne0
  have hstep : c.step p σ = sw_cfg c p sh dh .l16_11 := by
    simp [Cfg.step, hp, hb, hl, sw_cfg, Cfg.scS]
  rw [hstep]
  have hpc : SwPC (c.loc p).pc .l16_11 := Or.inr ⟨hp, rfl⟩
  apply sw_inv hI hpc hb hns hne hw
  obtain ⟨e1, e2, e3⟩ := hL.win (by rw [hp]; decide)
  constructor <;> simp only [sw_cfg_loc_self, sw_cfg_linkS, sw_cfg_S, sw_cfg_G, sw_cfg_Out,
    sw_cfg_In, sw_cfg_Ex, sw_cfg_Exclear, sw_cfg_linkEx]
  case p11 => intro _; exact ⟨sh, dh, hb, rfl, hne0, sw_Out_sh hI hne hw, sw_ExW hpc hw⟩
  case win =>
    intro _
    refine ⟨e1, e2, fun z hz => ?_⟩
    rw [sw_cfg_loc_ne c p sh dh .l16_11 hz]
    exact e3 z hz
  case winS =>
    intro _ _
    obtain ⟨m, m1, m2, m3⟩ := sw_ExW (sh := sh) (dh := dh) hpc hw
    exact ⟨m, m1, m2, ⟨m3.1, le_trans m3.2 (by decide)⟩⟩
  all_goals (intro h; first | exact absurd h (by decide) | simp at h)

end Podc.GroupMutexLogRMR
