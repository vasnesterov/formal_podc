import Papers.PODC2010.GroupMutexLogRMR.Frame

/-!
# Preservation of `Inv`: local steps of lines 5.1–16.12 (only the local state, the own links, `C`, `Q` change)
-/

namespace Podc.GroupMutexLogRMR

variable {n : ℕ} {J : Type} [DecidableEq J] {c : Cfg n J}

omit [DecidableEq J] in
@[local simp] theorem lo_llS_loc (c₀ : Cfg n J) (q : Fin n) : (c₀.llS q).loc = c₀.loc := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llS_linkEx (c₀ : Cfg n J) (q : Fin n) : (c₀.llS q).linkEx = c₀.linkEx := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llS_S (c₀ : Cfg n J) (q : Fin n) : (c₀.llS q).S = c₀.S := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llS_Ex (c₀ : Cfg n J) (q : Fin n) : (c₀.llS q).Ex = c₀.Ex := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llS_C (c₀ : Cfg n J) (q : Fin n) : (c₀.llS q).C = c₀.C := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llS_Q (c₀ : Cfg n J) (q : Fin n) : (c₀.llS q).Q = c₀.Q := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llS_G (c₀ : Cfg n J) (q : Fin n) : (c₀.llS q).G = c₀.G := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llS_In (c₀ : Cfg n J) (q : Fin n) : (c₀.llS q).In = c₀.In := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llS_Out (c₀ : Cfg n J) (q : Fin n) : (c₀.llS q).Out = c₀.Out := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llS_Exclear (c₀ : Cfg n J) (q : Fin n) : (c₀.llS q).Exclear = c₀.Exclear := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llEx_loc (c₀ : Cfg n J) (q : Fin n) : (c₀.llEx q).loc = c₀.loc := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llEx_linkS (c₀ : Cfg n J) (q : Fin n) : (c₀.llEx q).linkS = c₀.linkS := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llEx_S (c₀ : Cfg n J) (q : Fin n) : (c₀.llEx q).S = c₀.S := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llEx_Ex (c₀ : Cfg n J) (q : Fin n) : (c₀.llEx q).Ex = c₀.Ex := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llEx_C (c₀ : Cfg n J) (q : Fin n) : (c₀.llEx q).C = c₀.C := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llEx_Q (c₀ : Cfg n J) (q : Fin n) : (c₀.llEx q).Q = c₀.Q := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llEx_G (c₀ : Cfg n J) (q : Fin n) : (c₀.llEx q).G = c₀.G := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llEx_In (c₀ : Cfg n J) (q : Fin n) : (c₀.llEx q).In = c₀.In := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llEx_Out (c₀ : Cfg n J) (q : Fin n) : (c₀.llEx q).Out = c₀.Out := rfl
omit [DecidableEq J] in
@[local simp] theorem lo_llEx_Exclear (c₀ : Cfg n J) (q : Fin n) : (c₀.llEx q).Exclear = c₀.Exclear := rfl
@[local simp] theorem lo_decC_loc (c₀ : Cfg n J) (s : J) (d : Bool) : (c₀.decC s d).loc = c₀.loc := rfl
@[local simp] theorem lo_decC_linkS (c₀ : Cfg n J) (s : J) (d : Bool) : (c₀.decC s d).linkS = c₀.linkS := rfl
@[local simp] theorem lo_decC_linkEx (c₀ : Cfg n J) (s : J) (d : Bool) : (c₀.decC s d).linkEx = c₀.linkEx := rfl
@[local simp] theorem lo_decC_S (c₀ : Cfg n J) (s : J) (d : Bool) : (c₀.decC s d).S = c₀.S := rfl
@[local simp] theorem lo_decC_Ex (c₀ : Cfg n J) (s : J) (d : Bool) : (c₀.decC s d).Ex = c₀.Ex := rfl
@[local simp] theorem lo_decC_Q (c₀ : Cfg n J) (s : J) (d : Bool) : (c₀.decC s d).Q = c₀.Q := rfl
@[local simp] theorem lo_decC_G (c₀ : Cfg n J) (s : J) (d : Bool) : (c₀.decC s d).G = c₀.G := rfl
@[local simp] theorem lo_decC_In (c₀ : Cfg n J) (s : J) (d : Bool) : (c₀.decC s d).In = c₀.In := rfl
@[local simp] theorem lo_decC_Out (c₀ : Cfg n J) (s : J) (d : Bool) : (c₀.decC s d).Out = c₀.Out := rfl
@[local simp] theorem lo_decC_Exclear (c₀ : Cfg n J) (s : J) (d : Bool) : (c₀.decC s d).Exclear = c₀.Exclear := rfl


omit [DecidableEq J] in
/-- The `ns` obligation of `LocalOK` when `p` keeps its session and side and stays off 1.5/1.6. -/
theorem lo_ns {c' : Cfg n J} {p : Fin n} (hs : (c'.loc p).s = (c.loc p).s)
    (hps : ∀ e, (c'.loc p).pside = some e → (c.loc p).pside = some e) (h5 : (c'.loc p).pc ≠ .l1_5)
    (h6 : (c'.loc p).pc ≠ .l1_6) :
    NoSide c c.S.1 c.S.2.1 → minQ c.Q ≠ none → (∀ sh dh, minQ c.Q = some (sh, dh) → sh ≠ c.S.1) →
    (c'.loc p).s = c.S.1 →
    (c'.loc p).pc ≠ .l1_5 ∧ (c'.loc p).pc ≠ .l1_6 ∧ (c'.loc p).pside ≠ some c.S.2.1 := by
  intro hns _ _ hsS
  exact ⟨h5, h6, fun he => (hns p (hs ▸ hsS)).2.2 (hps _ he)⟩

set_option hygiene false in
/-- The frame fields and the `ns` field of `LocalOK` for a step built from `setLoc`, `llS`, `llEx`,
`Q`/`C` updates, in which `p` keeps its session and does not gain a side (needs `hp`). The
remaining goals are tagged `refine_1` … `refine_6` = `r8 r10 r12 r162 w2 win`. -/
macro "lo_frame" : tactic => `(tactic| refine ⟨rfl, rfl, le_rfl, rfl, rfl, rfl,
  fun z hz => by simp [Function.update_of_ne hz], fun z hz => by simp [Function.update_of_ne hz],
  fun z hz => by simp [Function.update_of_ne hz], ?_, ?_, ?_, ?_,
  lo_ns (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp) (by simp), ?_, ?_⟩)

omit [DecidableEq J] in
/-- An `ExW` witness survives a step of `p` if `p` was not in the range. -/
theorem lo_ExW {c' : Cfg n J} {p : Fin n} (hloc : ∀ z, z ≠ p → c'.loc z = c.loc z) {lo hi : PC}
    (hp : ¬ PC.btw lo hi (c.loc p).pc) {s : J} {d : Bool} (h : ExW c s d lo hi) :
    ExW c' s d lo hi := by
  obtain ⟨m, h1, h2, h3⟩ := h
  have hm : m ≠ p := by rintro rfl; exact hp h3
  exact ⟨m, by rw [hloc m hm]; exact h1, by rw [hloc m hm]; exact h2, by rw [hloc m hm]; exact h3⟩

/-- `C[s,e] = 0` gives `NoSide`. -/
theorem lo_noSide_of_C (hI : Inv c) {s : J} {e : Bool} (h : c.C s e = 0) : NoSide c s e := by
  intro z hz
  have h0 := cnt_eq_zero_of_C hI h z
  refine ⟨fun h5 => ?_, fun h6 => ?_, fun he => ?_⟩
  · simp [Loc.cnt, hz, h5, PC.btw, PC.idx] at h0
  · simp [Loc.cnt, hz, h6, PC.btw, PC.idx] at h0
  · have := Loc.cnt_of_pside he; rw [hz] at this; omega

omit [DecidableEq J] in
/-- `NoSide` survives a step of `p` that does not break it for `p`. -/
theorem lo_noSide {c' : Cfg n J} {p : Fin n} (hloc : ∀ z, z ≠ p → c'.loc z = c.loc z) {s : J}
    {e : Bool} (h : NoSide c s e)
    (hp : (c'.loc p).s = s → (c'.loc p).pc ≠ .l1_5 ∧ (c'.loc p).pc ≠ .l1_6 ∧
      (c'.loc p).pside ≠ some e) : NoSide c' s e := by
  intro z hz
  by_cases hzp : z = p
  · subst hzp; exact hp hz
  · rw [hloc z hzp] at hz ⊢; exact h z hz

omit [DecidableEq J] in
/-- Clause `l1` of `p` survives a step of `p` within lines 4–8. -/
theorem lo_l1 {c' : Cfg n J} {p : Fin n} (hL : LI c p) (h : LocalOK c c' p)
    (hpc : PC.btw .l4 .l8 (c.loc p).pc) (hpc' : PC.btw .l4 .l8 (c'.loc p).pc)
    (hs : (c'.loc p).s = (c.loc p).s) (hd : (c'.loc p).d = (c.loc p).d)
    (htm : (c'.loc p).tm = (c.loc p).tm) :
    PC.btw .l1_7 .l8 (c'.loc p).pc → c'.S.1 = (c'.loc p).s → c'.S.2.1 = !(c'.loc p).d →
    ∃ q, (c'.loc q).s ≠ (c'.loc p).s ∧ PC.btw .l5_1 .l8 (c'.loc q).pc ∧
      ((c'.loc p).pc = .l3 → (c'.loc q).tm < c'.G) ∧
      (PC.btw .l4 .l8 (c'.loc p).pc → (c'.loc q).tm < (c'.loc p).tm) := by
  intro _ h2 h3
  rw [h.S, hs] at h2; rw [h.S, hd] at h3
  obtain ⟨q, q1, q2, -, q4⟩ := hL.l1 ⟨le_trans (by decide) hpc.1, hpc.2⟩ h2 h3
  have hq : q ≠ p := by rintro rfl; exact q1 rfl
  refine ⟨q, ?_, ?_, fun h3' => ?_, fun _ => ?_⟩ <;> rw [h.loc q hq]
  · rw [hs]; exact q1
  · exact q2
  · rw [h3'] at hpc'; exact absurd hpc'.1 (by decide)
  · rw [htm]; exact q4 hpc

omit [DecidableEq J] in
/-- Clause `w2` of `p` survives a step of `p` within lines 16.4–16.9. -/
theorem lo_w2 {c' : Cfg n J} {p : Fin n} (hL : LI c p) (h : LocalOK c c' p)
    (hpc : PC.btw .l16_4 .l16_9 (c.loc p).pc) (hpc' : PC.btw .l16_4 .l16_9 (c'.loc p).pc)
    (hs : (c'.loc p).s = (c.loc p).s) (hd : (c'.loc p).d = (c.loc p).d)
    (hl : c'.linkEx p = c.linkEx p) (h9 : (c'.loc p).pc = .l16_9 → (c.loc p).pc = .l16_9) :
    PC.btw .l16_4 .l16_9 (c'.loc p).pc → c'.linkEx p = true → ∀ z,
    (PC.btw .l11 .l16_3 (c'.loc z).pc ∨ ((c'.loc z).pc = .l10 ∧ c'.linkEx z = false)) →
    (c'.loc z).s = (c'.loc p).s ∧ (c'.loc z).d = (c'.loc p).d ∧ (c'.loc p).pc ≠ .l16_9 := by
  intro _ h2 z hz
  rw [hl] at h2
  by_cases hzp : z = p
  · subst hzp
    exfalso
    rcases hz with hz | ⟨hz, -⟩
    · btw_omega
    · rw [hz] at hpc'; exact absurd hpc'.1 (by decide)
  · rw [h.loc z hzp, h.linkEx z hzp] at hz
    obtain ⟨k1, k2, k3⟩ := hL.w2 hpc h2 z hz
    rw [h.loc z hzp, hs, hd]
    exact ⟨k1, k2, fun h' => k3 (h9 h')⟩

omit [DecidableEq J] in
/-- Clause `w4` of `p` survives a step of `p` within lines 16.4–16.9. -/
theorem lo_w4 {c' : Cfg n J} {p : Fin n} (hL : LI c p) (h : LocalOK c c' p)
    (hpc : PC.btw .l16_4 .l16_9 (c.loc p).pc)
    (hs : (c'.loc p).s = (c.loc p).s) (hd : (c'.loc p).d = (c.loc p).d)
    (hl : c'.linkEx p = c.linkEx p) :
    PC.btw .l16_4 .l16_9 (c'.loc p).pc → c'.linkEx p = true →
    ¬ (c'.S.1 = (c'.loc p).s ∧ c'.S.2.1 = (c'.loc p).d) →
    ∃ m, (c'.loc m).s = c'.S.1 ∧ (c'.loc m).d = c'.S.2.1 ∧ PC.btw .l5_1 .l10 (c'.loc m).pc ∧
      ((c'.loc m).pc = .l10 → c'.linkEx m = true) := by
  intro _ h2 h3
  rw [hl] at h2
  simp only [h.S, hs, hd] at h3 ⊢
  obtain ⟨m, m1, m2, m3, m4⟩ := hL.w4 hpc h2 h3
  have hm : m ≠ p := by rintro rfl; btw_omega
  refine ⟨m, ?_, ?_, ?_, ?_⟩ <;> rw [h.loc m hm] <;> (try rw [h.linkEx m hm]) <;> assumption

omit [DecidableEq J] in
/-- Clause `win` of `p` survives a step of `p` within lines 16.10–16.14. -/
theorem lo_win {c' : Cfg n J} {p : Fin n} (hL : LI c p) (h : LocalOK c c' p)
    (hpc : PC.btw .l16_10 .l16_14 (c.loc p).pc) (hs : (c'.loc p).s = (c.loc p).s) :
    PC.btw .l16_10 .l16_14 (c'.loc p).pc →
    c'.Ex = some (c'.loc p).s ∧ c'.Exclear (c'.loc p).s = false ∧ ∀ z, z ≠ p →
      ¬ PC.btw .l16_10 .l16_14 (c'.loc z).pc ∧
      (PC.btw .l11 .l16_3 (c'.loc z).pc →
        (c'.loc z).pc = .l11 ∨ ((c'.loc z).pc = .l12 ∧ (c'.loc z).a.1 = (c'.loc p).s)) ∧
      ((c'.loc z).pc = .l10 → c'.linkEx z = false) ∧
      (PC.btw .l16_4 .l16_9 (c'.loc z).pc → c'.linkEx z = false) := by
  intro _
  obtain ⟨e1, e2, e3⟩ := hL.win hpc
  rw [h.Ex, h.Exclear, hs]
  refine ⟨e1, e2, fun z hz => ?_⟩
  rw [h.loc z hz, h.linkEx z hz]
  exact e3 z hz

omit [DecidableEq J] in
/-- Clause `winS` of `p` survives a step of `p` within lines 16.10–16.14. -/
theorem lo_winS {c' : Cfg n J} {p : Fin n} (hL : LI c p) (h : LocalOK c c' p)
    (hpc : PC.btw .l16_10 .l16_14 (c.loc p).pc) (hs : (c'.loc p).s = (c.loc p).s) :
    PC.btw .l16_10 .l16_14 (c'.loc p).pc → c'.S.1 ≠ (c'.loc p).s →
      ExW c' c'.S.1 c'.S.2.1 .l5_1 .l12 := by
  intro _ h2
  rw [h.S, hs] at *
  exact lo_ExW h.loc (fun h' => by btw_omega) (hL.winS hpc h2)

/-- The `hg5` obligation of `Inv.of_local` when `p` stays a witness of `g5` if it was one. -/
theorem lo_g5 (hI : Inv c) {c' : Cfg n J} {p : Fin n} (hloc : ∀ z, z ≠ p → c'.loc z = c.loc z)
    (hp : (c.loc p).pside = some c.S.2.1 → PC.btw .l1_4 .l15 (c.loc p).pc →
      (c'.loc p).s = (c.loc p).s ∧ (c'.loc p).pside = some c.S.2.1 ∧
        PC.btw .l1_4 .l15 (c'.loc p).pc) :
    ∀ s, c.S.1 = s → c.In s = c.S.2.1 → ∃ y, (c'.loc y).s = s ∧
      (c'.loc y).pside = some c.S.2.1 ∧ PC.btw .l1_4 .l15 (c'.loc y).pc := by
  intro s hs hin
  obtain ⟨y, h1, h2, h3⟩ := hI.g5 s hs hin
  by_cases hy : y = p
  · subst hy
    obtain ⟨k1, k2, k3⟩ := hp h2 h3
    exact ⟨y, k1.trans h1, k2, k3⟩
  · exact ⟨y, by rw [hloc y hy]; exact h1, by rw [hloc y hy]; exact h2, by rw [hloc y hy]; exact h3⟩

/-- The `hg7` obligation of `Inv.of_local` when `p` keeps its session and does not gain a side. -/
theorem lo_g7 (hI : Inv c) {c' : Cfg n J} {p : Fin n} (hs : (c'.loc p).s = (c.loc p).s)
    (hps : ∀ e, (c'.loc p).pside = some e → (c.loc p).pside = some e) :
    c.S.1 ≠ (c'.loc p).s → ∀ e, (c'.loc p).pside = some e → e = c.In (c'.loc p).s := by
  intro h e he
  rw [hs] at h ⊢
  exact hI.g7 _ p h rfl e (hps e he)

/-- The element of `Q` realizing `Min(Q)`. -/
theorem lo_minQ_mem (hI : Inv c) {sh : J} {dh : Bool} (hm : minQ c.Q = some (sh, dh)) :
    ∃ r, (c.loc r).s = sh ∧ (c.loc r).d = dh ∧ PC.btw .l5_1 .l13 (c.loc r).pc := by
  obtain ⟨r, t, hr, -⟩ := minQ_eq_some hm
  obtain ⟨hb, he⟩ := hI.q_eq_some hr
  simp only [Prod.mk.injEq] at he
  exact ⟨r, he.1.symm, he.2.1.symm, hb⟩

/-- If `Min(Q)` is not of the session of `S`, its element is at lines 5.1–8. -/
theorem lo_minQ_wit (hI : Inv c) {sh : J} {dh : Bool} (hm : minQ c.Q = some (sh, dh))
    (hne : c.S.1 ≠ sh) : ExW c sh dh .l5_1 .l8 := by
  obtain ⟨r, h1, h2, h3⟩ := lo_minQ_mem hI hm
  refine ⟨r, h1, h2, h3.1, ?_⟩
  by_contra h9
  have := ((hI.li r).i5 (by btw_omega)).1
  exact hne (this.trans h1)

omit [DecidableEq J] in
/-- Clause `x3` of `p` survives a step of `p` within lines 16.8–16.9. -/
theorem lo_x3 {c' : Cfg n J} {p : Fin n} (hL : LI c p) (h : LocalOK c c' p)
    (hpc : PC.btw .l16_8 .l16_9 (c.loc p).pc) (hs : (c'.loc p).s = (c.loc p).s)
    (hb : (c'.loc p).b = (c.loc p).b) (hl : c'.linkEx p = c.linkEx p) :
    PC.btw .l16_8 .l16_9 (c'.loc p).pc → c'.linkEx p = true → ∀ dh,
    (c'.loc p).b = some ((c'.loc p).s, dh) → ∃ m, (c'.loc m).s = (c'.loc p).s ∧ (c'.loc m).d = dh ∧
      PC.btw .l5_1 .l16_2 (c'.loc m).pc ∧ ((c'.loc m).pc = .l16_2 → c'.linkEx m = true) := by
  intro _ h2 dh h3
  rw [hl] at h2; rw [hb, hs] at h3; rw [hs]
  obtain ⟨m, m1, m2, m3, m4⟩ := hL.x3 hpc h2 dh h3
  have hm : m ≠ p := by rintro rfl; btw_omega
  refine ⟨m, ?_, ?_, ?_, ?_⟩ <;> rw [h.loc m hm] <;> (try rw [h.linkEx m hm]) <;> assumption

theorem inv_step_l5_1 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l5_1) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hstep : c.step p σ =
      (c.llS p).setLoc p { c.loc p with pc := .l5_2, a := (c.S.1, c.S.2.1) } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c ((c.llS p).setLoc p { c.loc p with pc := .l5_2, a := (c.S.1, c.S.2.1) }) p := by
    lo_frame
    all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · constructor
    case l1 => exact lo_l1 hL hLO (by rw [hp]; decide) (by simp [PC.btw, PC.idx]) (by simp) (by simp)
                 (by simp)
    all_goals simp [PC.btw, PC.idx]
    · exact hL.tm (by simp [hp, PC.btw, PC.idx])
    · exact hL.i8 (by simp [hp, PC.btw, PC.idx])

theorem inv_step_l5_2 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l5_2) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l5_3, b := minQ c.Q } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l5_3, b := minQ c.Q }) p := by
    lo_frame
    all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · constructor
    case l1 => exact lo_l1 hL hLO (by rw [hp]; decide) (by simp [PC.btw, PC.idx]) (by simp) (by simp)
                 (by simp)
    case a2 =>
      intro _ _
      obtain ⟨⟨sh, dh⟩, hm⟩ := Option.ne_none_iff_exists'.mp
        (hI.minQ_ne_none (z := p) (by rw [hp]; decide))
      exact ⟨sh, dh, by simpa using hm, fun hne =>
        ExW_of_local hLO (lo_minQ_wit hI hm (Ne.symm hne)) (Or.inl (Ne.symm hne))⟩
    all_goals simp [PC.btw, PC.idx]
    · exact hL.tm (by simp [hp, PC.btw, PC.idx])
    · exact hL.i8 (by simp [hp, PC.btw, PC.idx])
    · exact hL.a1 (Or.inl hp)

theorem inv_step_l5_3 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l5_3) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  rcases hb : (c.loc p).b with _ | ⟨sh, dh⟩
  · have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l6 } := by simp [Cfg.step, hp, hb]
    rw [hstep]
    have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l6 }) p := by
      lo_frame
      all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
    apply Inv.of_local hI hLO
    · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · simp
    · simp [hp]
    · constructor
      case l1 => exact lo_l1 hL hLO (by rw [hp]; decide) (by simp [PC.btw, PC.idx]) (by simp) (by simp)
                   (by simp)
      all_goals simp [PC.btw, PC.idx]
      · exact hL.tm (by simp [hp, PC.btw, PC.idx])
      · exact hL.i8 (by simp [hp, PC.btw, PC.idx])
  by_cases h : c.C (c.loc p).a.1 (c.loc p).a.2 = 0 ∧ sh ≠ (c.loc p).a.1
  · have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l5_4 } := by
      simp only [Cfg.step, hp, hb, ite_eq_left h, Cfg.go_eq]
    rw [hstep]
    have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l5_4 }) p := by
      lo_frame
      all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
    apply Inv.of_local hI hLO
    · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · simp
    · simp [hp]
    · constructor
      case l1 => exact lo_l1 hL hLO (by rw [hp]; decide) (by simp [PC.btw, PC.idx]) (by simp) (by simp)
                   (by simp)
      case a2 =>
        intro _ hl
        obtain ⟨sh', dh', hb', hw⟩ := hL.a2 (Or.inl hp) hl
        exact ⟨sh', dh', by simpa using hb', fun hne => ExW_of_local hLO (hw hne) (Or.inl (Ne.symm hne))⟩
      case a3 =>
        intro _ hl
        have ha := hL.a1 (Or.inr hp) hl
        have hns : NoSide c c.S.1 c.S.2.1 := by have := lo_noSide_of_C hI h.1; rwa [ha] at this
        refine ⟨lo_noSide hLO.loc hns (fun hs => ?_), fun sh' dh' hb' => ?_⟩
        · have h2 := hns p (by simpa using hs)
          simp only [Cfg.setLoc_loc, Function.update_self]
          refine ⟨by simp, by simp, ?_⟩
          simpa [Loc.pside, hp, PC.btw, PC.idx] using h2.2.2
        · simp [hb] at hb'
          obtain ⟨rfl, rfl⟩ := hb'
          have := h.2; rw [ha] at this; exact this
      all_goals simp [PC.btw, PC.idx]
      · exact hL.tm (by simp [hp, PC.btw, PC.idx])
      · exact hL.i8 (by simp [hp, PC.btw, PC.idx])
  · have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l6 } := by
      simp only [Cfg.step, hp, hb, ite_eq_right h, Cfg.go_eq]
    rw [hstep]
    have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l6 }) p := by
      lo_frame
      all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
    apply Inv.of_local hI hLO
    · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · simp
    · simp [hp]
    · constructor
      case l1 => exact lo_l1 hL hLO (by rw [hp]; decide) (by simp [PC.btw, PC.idx]) (by simp) (by simp)
                   (by simp)
      all_goals simp [PC.btw, PC.idx]
      · exact hL.tm (by simp [hp, PC.btw, PC.idx])
      · exact hL.i8 (by simp [hp, PC.btw, PC.idx])

theorem inv_step_l6 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l6) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  by_cases h : c.S = ((c.loc p).s, (c.loc p).d, (c.loc p).s)
  · have hstep : c.step p σ = (c.llS p).setLoc p { c.loc p with pc := .l7 } := by
      simp [Cfg.step, hp, h]
    rw [hstep]
    have hLO : LocalOK c ((c.llS p).setLoc p { c.loc p with pc := .l7 }) p := by
      lo_frame
      all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
    apply Inv.of_local hI hLO
    · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · simp
    · simp [hp]
    · constructor
      case l1 => exact lo_l1 hL hLO (by rw [hp]; decide) (by simp [PC.btw, PC.idx]) (by simp) (by simp)
                   (by simp)
      case i7 => intro _; simpa using h
      all_goals simp [PC.btw, PC.idx]
      · exact hL.tm (by simp [hp, PC.btw, PC.idx])
      · exact hL.i8 (by simp [hp, PC.btw, PC.idx])
  · have hstep : c.step p σ = (c.llS p).setLoc p { c.loc p with pc := .l8 } := by
      simp [Cfg.step, hp, h]
    rw [hstep]
    have hLO : LocalOK c ((c.llS p).setLoc p { c.loc p with pc := .l8 }) p := by
      lo_frame
      all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
    apply Inv.of_local hI hLO
    · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · simp
    · simp [hp]
    · constructor
      case l1 => exact lo_l1 hL hLO (by rw [hp]; decide) (by simp [PC.btw, PC.idx]) (by simp) (by simp)
                   (by simp)
      all_goals simp [PC.btw, PC.idx]
      · exact hL.tm (by simp [hp, PC.btw, PC.idx])
      · exact hL.i8 (by simp [hp, PC.btw, PC.idx])

theorem inv_step_l8 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l8) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  by_cases h : c.Out (c.loc p).s = (c.loc p).d
  swap
  · have hstep : c.step p σ = c := by simp [Cfg.step, hp, h]
    rw [hstep]; exact hI
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l9 } := by simp [Cfg.step, hp, h]
  rw [hstep]
  have hi8 := hL.i8 (by rw [hp]; decide) h
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l9 }) p := by
    lo_frame
    case refine_1 => exact fun _ => Or.inr ⟨hi8.1, hi8.2, h⟩
    all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · constructor <;> simp [PC.btw, PC.idx]
    · exact hL.tm (by simp [hp, PC.btw, PC.idx])
    · exact ⟨hi8.1, hi8.2, h⟩

theorem inv_step_l9 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l9) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  by_cases hE : c.Ex = none
  · have hstep : c.step p σ = (c.llEx p).setLoc p { c.loc p with pc := .l10 } := by
      simp [Cfg.step, hp, hE]
    rw [hstep]
    have hLO : LocalOK c ((c.llEx p).setLoc p { c.loc p with pc := .l10 }) p := by
      lo_frame
      all_goals simp [hp, hE, PC.btw, PC.idx, WinOK, SameSDT]
    apply Inv.of_local hI hLO
    · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · simp
    · simp [hp]
    · constructor <;> simp [PC.btw, PC.idx]
      · exact hL.tm (by simp [hp, PC.btw, PC.idx])
      · exact hL.i5 (by simp [hp, PC.btw, PC.idx])
  · have hstep : c.step p σ = (c.llEx p).setLoc p { c.loc p with pc := .l11 } := by
      simp [Cfg.step, hp, hE]
    rw [hstep]
    have hLO : LocalOK c ((c.llEx p).setLoc p { c.loc p with pc := .l11 }) p := by
      lo_frame
      case refine_2 => exact fun _ _ => Or.inr hE
      all_goals simp [hp, hE, PC.btw, PC.idx, WinOK, SameSDT]
    apply Inv.of_local hI hLO
    · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · simp
    · simp [hp]
    · constructor <;> simp [PC.btw, PC.idx]
      · exact hL.tm (by simp [hp, PC.btw, PC.idx])
      · exact hL.i5 (by simp [hp, PC.btw, PC.idx])

theorem inv_step_l11 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l11) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  rcases hE : c.Ex with _ | se
  · have hstep : c.step p σ = (c.llEx p).setLoc p { c.loc p with pc := .cs } := by
      simp [Cfg.step, hp, hE]
    rw [hstep]
    have hLO : LocalOK c ((c.llEx p).setLoc p { c.loc p with pc := .cs }) p := by
      lo_frame
      case refine_3 => exact fun _ => Or.inr (Or.inl ⟨hp, hE⟩)
      all_goals simp [hp, hE, PC.btw, PC.idx, WinOK, SameSDT]
    apply Inv.of_local hI hLO
    · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · simp
    · simp [hp]
    · constructor <;> simp [PC.btw, PC.idx]
      · exact hL.tm (by simp [hp, PC.btw, PC.idx])
      · exact hL.i5 (by simp [hp, PC.btw, PC.idx])
  · have hstep : c.step p σ =
        (c.llEx p).setLoc p { c.loc p with pc := .l12, a := (se, (c.loc p).a.2) } := by
      simp [Cfg.step, hp, hE]
    rw [hstep]
    have hLO : LocalOK c ((c.llEx p).setLoc p
        { c.loc p with pc := .l12, a := (se, (c.loc p).a.2) }) p := by
      lo_frame
      all_goals simp [hp, hE, PC.btw, PC.idx, WinOK, SameSDT]
    apply Inv.of_local hI hLO
    · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · simp
    · simp [hp]
    · constructor <;> simp [PC.btw, PC.idx]
      · exact hL.tm (by simp [hp, PC.btw, PC.idx])
      · exact hL.i5 (by simp [hp, PC.btw, PC.idx])

theorem inv_step_l12 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l12) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  by_cases h : c.Exclear (c.loc p).a.1 = true
  swap
  · have hstep : c.step p σ = c := by simp [Cfg.step, hp, h]
    rw [hstep]; exact hI
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .cs } := by simp [Cfg.step, hp, h]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .cs }) p := by
    lo_frame
    case refine_3 => exact fun _ => Or.inr (Or.inr ⟨hp, h⟩)
    case refine_6 =>
      intro s _ hE hW
      exfalso
      have := hW.2.1 (by rw [hp]; decide)
      rw [hp] at this
      simp only [reduceCtorEq, false_or, true_and] at this
      rw [this] at h; rw [h] at hE; cases hE
    all_goals simp [hp, PC.btw, PC.idx, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · constructor <;> simp [PC.btw, PC.idx]
    · exact hL.tm (by simp [hp, PC.btw, PC.idx])
    · exact hL.i5 (by simp [hp, PC.btw, PC.idx])

theorem inv_step_cs (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .cs) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l13 } := by simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l13 }) p := by
    refine ⟨rfl, rfl, le_rfl, rfl, rfl, rfl, fun z hz => by simp [Function.update_of_ne hz],
      fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_,
      lo_ns (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp) (by simp), ?_, ?_⟩ <;>
      simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · simp only [Cfg.setLoc_Q]; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · have hL := hI.li p
    constructor <;> simp [PC.btw, PC.idx]
    · exact hL.tm (by simp [hp, PC.btw, PC.idx])
    · exact hL.i5 (by simp [hp, PC.btw, PC.idx])

theorem inv_step_l13 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l13) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ =
      ({ c with Q := Function.update c.Q p none } : Cfg n J).setLoc p { c.loc p with pc := .l14 } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c (({ c with Q := Function.update c.Q p none } : Cfg n J).setLoc p
      { c.loc p with pc := .l14 }) p := by
    lo_frame
    all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro z hz; simp [Function.update_of_ne hz]
  · simp [PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · have hL := hI.li p
    constructor <;> simp [PC.btw, PC.idx]
    · exact hL.i5 (by simp [hp, PC.btw, PC.idx])

theorem inv_step_l14 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l14) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hi5 := hL.i5 (by rw [hp]; decide)
  by_cases hm : minQ c.Q = none ∨ (minQ c.Q).map Prod.fst ≠ some (c.loc p).s
  · have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l15 } := by
      simp only [Cfg.step, hp, ite_eq_left hm, Cfg.go_eq]
    rw [hstep]
    have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l15 }) p := by
      lo_frame
      all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
    apply Inv.of_local hI hLO
    · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · simp
    · simp [hp]
    · constructor <;> simp [PC.btw, PC.idx]
      exact hi5
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l16_1 } := by
    simp only [Cfg.step, hp, ite_eq_right hm, Cfg.go_eq]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l16_1 }) p := by
    lo_frame
    all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · intro s hs hin
    obtain ⟨y, h1, h2, h3⟩ := hI.g5 s hs hin
    by_cases hy : y = p
    · subst hy
      push Not at hm
      obtain ⟨⟨sh, e⟩, hme⟩ := Option.ne_none_iff_exists'.mp hm.1
      have hsh : sh = (c.loc y).s := by rw [hme] at hm; simpa using hm.2
      subst hsh
      have he := hI.minQ_side hme (hs.trans h1.symm)
      obtain ⟨r, r1, r2, r3⟩ := lo_minQ_mem hI hme
      have hr : r ≠ y := by rintro rfl; rw [hp] at r3; exact absurd r3.2 (by decide)
      refine ⟨r, ?_, ?_, ?_⟩ <;> rw [hLO.loc r hr]
      · exact r1.trans h1
      · rw [Loc.pside_of_btw ⟨le_trans (by decide) r3.1, le_trans r3.2 (by decide)⟩, r2, he]
      · exact ⟨le_trans (by decide) r3.1, le_trans r3.2 (by decide)⟩
    · exact ⟨y, by rw [hLO.loc y hy]; exact h1, by rw [hLO.loc y hy]; exact h2,
        by rw [hLO.loc y hy]; exact h3⟩
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · constructor <;> simp [PC.btw, PC.idx]
    exact hi5

theorem inv_step_l16_1 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_1) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ = (c.llEx p).setLoc p { c.loc p with pc := .l16_2 } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c ((c.llEx p).setLoc p { c.loc p with pc := .l16_2 }) p := by
    lo_frame
    all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · have hL := hI.li p
    constructor <;> simp [PC.btw, PC.idx]
    · exact hL.i5 (by simp [hp, PC.btw, PC.idx])

theorem inv_step_l16_3 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_3) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ = (c.llEx p).setLoc p { c.loc p with pc := .l16_4 } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c ((c.llEx p).setLoc p { c.loc p with pc := .l16_4 }) p := by
    lo_frame
    all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · have hL := hI.li p
    have hi5 := hL.i5 (by simp [hp, PC.btw, PC.idx])
    constructor
    case w2 =>
      intro _ _ z hz
      have hzp : z ≠ p := by rintro rfl; simp [PC.btw, PC.idx] at hz
      rw [hLO.loc z hzp, hLO.linkEx z hzp] at hz
      rw [hLO.loc z hzp]
      have hz' : PC.btw .l9 .l16_6 (c.loc z).pc := by
        rcases hz with hz | ⟨hz, -⟩
        · btw_omega
        · rw [hz]; decide
      have h1 := (hI.li z).i5 hz'
      simp only [Cfg.setLoc_loc, Function.update_self]
      exact ⟨h1.1.symm.trans hi5.1, h1.2.1.symm.trans hi5.2.1, by simp⟩
    case w4 => intro _ _ h; simp at h; exact absurd hi5.2.1 (h hi5.1)
    all_goals simp [PC.btw, PC.idx]
    · exact hi5
    · exact hL.w3 (Or.inl hp)

theorem inv_step_l16_4 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_4) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ = (c.llS p).setLoc p { c.loc p with pc := .l16_5 } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c ((c.llS p).setLoc p { c.loc p with pc := .l16_5 }) p := by
    lo_frame
    all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · have hL := hI.li p
    have hi5 := hL.i5 (by simp [hp, PC.btw, PC.idx])
    have hpc : PC.btw .l16_4 .l16_9 (c.loc p).pc := by rw [hp]; decide
    constructor
    case w2 => exact lo_w2 hL hLO hpc (by simp [PC.btw, PC.idx]) (by simp) (by simp) rfl (by simp)
    case w4 => exact lo_w4 hL hLO hpc (by simp) (by simp) rfl
    all_goals simp [PC.btw, PC.idx]
    · exact hi5
    · exact ⟨hi5.1, hi5.2.1⟩
    · exact hL.w1 hpc

theorem inv_step_l16_6 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_6) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hpc : PC.btw .l16_4 .l16_9 (c.loc p).pc := by rw [hp]; decide
  have hstep : c.step p σ =
      (c.decC (c.loc p).s (c.loc p).d).setLoc p { c.loc p with pc := .l16_7 } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c ((c.decC (c.loc p).s (c.loc p).d).setLoc p { c.loc p with pc := .l16_7 }) p := by
    lo_frame
    all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d
    have hpos := hI.C_ne_zero_of_pside (z := p) (e := (c.loc p).d)
      (by simp [Loc.pside, hp, PC.btw, PC.idx])
    simp only [Cfg.setLoc_C, Cfg.decC_C, Cfg.setLoc_loc, Function.update_self]
    by_cases hs : s = (c.loc p).s
    · subst hs
      by_cases hd : d = (c.loc p).d
      · subst hd; simp [Loc.cnt, hp, PC.btw, PC.idx]; omega
      · simp [Loc.cnt, hp, PC.btw, PC.idx, hd, Ne.symm hd]
    · simp [Loc.cnt, hs, Ne.symm hs]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · constructor
    case w2 => exact lo_w2 hL hLO hpc (by simp [PC.btw, PC.idx]) (by simp) (by simp) rfl (by simp)
    case w4 => exact lo_w4 hL hLO hpc (by simp) (by simp) rfl
    all_goals simp [PC.btw, PC.idx]
    · exact hL.e1 (by rw [hp]; decide)
    · exact hL.w1 hpc
    · exact hL.w5 (by rw [hp]; decide)

theorem inv_step_l16_7 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_7) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hpc : PC.btw .l16_4 .l16_9 (c.loc p).pc := by rw [hp]; decide
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l16_8, b := minQ c.Q } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l16_8, b := minQ c.Q }) p := by
    lo_frame
    all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · constructor
    case w2 => exact lo_w2 hL hLO hpc (by simp [PC.btw, PC.idx]) (by simp) (by simp) rfl (by simp)
    case w4 => exact lo_w4 hL hLO hpc (by simp) (by simp) rfl
    case x3 =>
      intro _ _ dh hb
      have hb' : minQ c.Q = some ((c.loc p).s, dh) := by simpa using hb
      obtain ⟨r, r1, r2, r3⟩ := lo_minQ_mem hI hb'
      have hr : r ≠ p := by rintro rfl; rw [hp] at r3; exact absurd r3.2 (by decide)
      refine ⟨r, ?_, ?_, ?_, ?_⟩ <;> rw [hLO.loc r hr]
      · simpa using r1
      · exact r2
      · exact ⟨r3.1, le_trans r3.2 (by decide)⟩
      · intro h; rw [h] at r3; exact absurd r3.2 (by decide)
    case x2 =>
      intro _ hl sh dh hm hne
      have hm' : minQ c.Q = some (sh, dh) := by simpa using hm
      have he := hL.e1 (by rw [hp]; decide) hl
      exact lo_ExW hLO.loc (by simp [hp, PC.btw, PC.idx])
        (lo_minQ_wit hI hm' (by rw [he.1]; exact fun h => hne (by simpa using h.symm)))
    all_goals simp [PC.btw, PC.idx]
    · exact hL.e1 (by rw [hp]; decide)
    · intro hl hm
      have he := hL.e1 (by rw [hp]; decide) hl
      have := hI.minQ_side hm he.1
      rw [he.2] at this
      cases h : (c.loc p).d <;> simp [h] at this
    · exact hL.w1 hpc
    · exact hL.w5 (by rw [hp]; decide)

theorem inv_step_l16_8 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_8) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hpc : PC.btw .l16_4 .l16_9 (c.loc p).pc := by rw [hp]; decide
  by_cases h : c.C (c.loc p).s (c.loc p).d = 0 ∧ (c.loc p).b ≠ none
  swap
  · have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .rem } := by
      simp only [Cfg.step, hp, ite_eq_right h, Cfg.go_eq]
    rw [hstep]
    have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .rem }) p := by
      lo_frame
      all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
    apply Inv.of_local hI hLO
    · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · simp
    · simp [hp]
    · constructor <;> simp [PC.btw, PC.idx]
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l16_9 } := by
    simp only [Cfg.step, hp, ite_eq_left h, Cfg.go_eq]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l16_9 }) p := by
    lo_frame
    all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · constructor
    case w2 =>
      intro _ hlE z hz
      exfalso
      have hzp : z ≠ p := by rintro rfl; simp [PC.btw, PC.idx] at hz
      rw [hLO.loc z hzp, hLO.linkEx z hzp] at hz
      obtain ⟨k1, k2, -⟩ := hL.w2 hpc hlE z hz
      have hz' : PC.btw .l2 .l16_6 (c.loc z).pc := by
        rcases hz with hz | ⟨hz, -⟩
        · btw_omega
        · rw [hz]; decide
      exact hI.C_ne_zero_of_pside (Loc.pside_of_btw hz') (by rw [k1, k2]; exact h.1)
    case w4 => exact lo_w4 hL hLO hpc (by simp) (by simp) rfl
    case x3 => exact lo_x3 hL hLO (by rw [hp]; decide) (by simp) (by simp) rfl
    case e2 =>
      intro _ hlS hlE
      obtain ⟨⟨sh, dh⟩, hb⟩ := Option.ne_none_iff_exists'.mp h.2
      have hns := lo_noSide_of_C hI h.1
      refine ⟨?_, sh, dh, by simpa using hb, ?_⟩
      · simp only [Cfg.setLoc_loc, Function.update_self]
        exact lo_noSide hLO.loc hns (fun _ => by simp [Loc.pside, PC.btw, PC.idx])
      intro hsh
      have hsh' : sh = (c.loc p).s := by simpa using hsh
      rw [hsh'] at hb
      by_cases hd : dh = (c.loc p).d
      · obtain ⟨m, m1, m2, m3, -⟩ := hL.x3 (by rw [hp]; decide) hlE dh hb
        exact hI.C_ne_zero_of_pside (z := m)
          (Loc.pside_of_btw ⟨le_trans (by decide) m3.1, le_trans m3.2 (by decide)⟩)
          (by rw [m1, m2, hd]; exact h.1)
      · apply hL.x1 (by rw [hp]; decide) hlS
        rw [hb]
        cases dh <;> cases hdp : (c.loc p).d <;> simp [hdp] at hd ⊢
    case x2 =>
      intro _ hl sh dh hb hne
      exact lo_ExW hLO.loc (by simp [hp, PC.btw, PC.idx])
        (hL.x2 (by rw [hp]; decide) hl sh dh (by simpa using hb) (by simpa using hne))
    all_goals simp [PC.btw, PC.idx]
    · exact hL.e1 (by rw [hp]; decide)
    · exact hL.x1 (by rw [hp]; decide)
    · exact hL.w1 hpc
    · exact hL.w5 (by rw [hp]; decide)

theorem inv_step_l16_12 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_12) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hpc : PC.btw .l16_10 .l16_14 (c.loc p).pc := by rw [hp]; decide
  by_cases h : c.S.1 = c.S.2.2
  · have hstep : c.step p σ =
        c.setLoc p { c.loc p with pc := .l16_13, a := (c.S.1, c.S.2.1) } := by
      simp only [Cfg.step, hp, ite_eq_left h]
    rw [hstep]
    have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l16_13, a := (c.S.1, c.S.2.1) }) p := by
      lo_frame
      all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
    apply Inv.of_local hI hLO
    · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · simp
    · simp [hp]
    · constructor
      case win => exact lo_win hL hLO hpc (by simp)
      case winS => exact lo_winS hL hLO hpc (by simp)
      case p13 =>
        intro _; left
        simp only [Cfg.setLoc_S, Cfg.setLoc_loc, Function.update_self]
        exact Prod.ext rfl (Prod.ext rfl h.symm)
      all_goals simp [PC.btw, PC.idx]
  · have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l16_14 } := by
      simp only [Cfg.step, hp, ite_eq_right h, Cfg.go_eq]
    rw [hstep]
    have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l16_14 }) p := by
      lo_frame
      all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
    apply Inv.of_local hI hLO
    · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    · simp
    · simp [hp]
    · constructor
      case win => exact lo_win hL hLO hpc (by simp)
      case winS => exact lo_winS hL hLO hpc (by simp)
      all_goals simp [PC.btw, PC.idx]

theorem inv_step_l5_4_fail (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l5_4) (hl : c.linkS p = false) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l6 } := by
    rcases hb : (c.loc p).b with _ | ⟨sh, dh⟩ <;> simp [Cfg.step, hp, hl, hb]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l6 }) p := by
    lo_frame
    all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; show c.C s d + _ = c.C s d + _; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · constructor
    case l1 => exact lo_l1 hL hLO (by rw [hp]; decide) (by simp [PC.btw, PC.idx]) (by simp) (by simp)
                 (by simp)
    all_goals simp [PC.btw, PC.idx]
    · exact hL.tm (by simp [hp, PC.btw, PC.idx])
    · exact hL.i8 (by simp [hp, PC.btw, PC.idx])

theorem inv_step_l10_fail (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l10) (hl : c.linkEx p = false) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l11 } := by
    simp [Cfg.step, hp, hl]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l11 }) p := by
    lo_frame
    all_goals simp [hp, hl, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · have hL := hI.li p
    constructor <;> simp [PC.btw, PC.idx]
    · exact hL.tm (by simp [hp, PC.btw, PC.idx])
    · exact hL.i5 (by simp [hp, PC.btw, PC.idx])

theorem inv_step_l16_2_fail (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_2) (hl : c.linkEx p = false) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l16_3 } := by
    simp [Cfg.step, hp, hl]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l16_3 }) p := by
    lo_frame
    all_goals simp [hp, hl, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · have hL := hI.li p
    constructor <;> simp [PC.btw, PC.idx]
    · exact hL.i5 (by simp [hp, PC.btw, PC.idx])
    · exact hL.w3 (Or.inr ⟨hp, hl⟩)

theorem inv_step_l16_9_fail (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_9) (hl : c.linkEx p = false) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .rem } := by
    simp [Cfg.step, hp, hl]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .rem }) p := by
    lo_frame
    all_goals simp [hp, hl, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · constructor <;> simp [PC.btw, PC.idx]

theorem inv_step_l16_10_fail (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_10) (hl : c.linkS p = false) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l16_12 } := by
    rcases hb : (c.loc p).b with _ | ⟨sh, dh⟩ <;> simp [Cfg.step, hp, hl, hb]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l16_12 }) p := by
    lo_frame
    all_goals simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply Inv.of_local hI hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · show c.Q p = _; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact lo_g5 hI hLO.loc (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · exact lo_g7 hI (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx])
  · simp
  · simp [hp]
  · have hL := hI.li p
    have hpc : PC.btw .l16_10 .l16_14 (c.loc p).pc := by rw [hp]; decide
    constructor
    case win => exact lo_win hL hLO hpc (by simp)
    case winS => exact lo_winS hL hLO hpc (by simp)
    all_goals simp [PC.btw, PC.idx]

end Podc.GroupMutexLogRMR
