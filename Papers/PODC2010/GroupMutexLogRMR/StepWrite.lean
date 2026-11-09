import Papers.PODC2010.GroupMutexLogRMR.Frame

/-!
# Preservation of `Inv`: steps writing `Out`, `In`, `Exclear`, and successful `SC`s on `Ex`
-/

namespace Podc.GroupMutexLogRMR

variable {n : ℕ} {J : Type} [DecidableEq J] {c : Cfg n J}

/-! ## Helpers: a step of `p` that only changes `p`'s program counter (plus one shared field) -/

section WrHelpers

variable (c)

omit [DecidableEq J] in
theorem wr_go_loc_self (p : Fin n) (pc : PC) : (c.go p pc).loc p = { c.loc p with pc := pc } := by
  simp

omit [DecidableEq J] in
theorem wr_go_loc_ne {p z : Fin n} (pc : PC) (h : z ≠ p) : (c.go p pc).loc z = c.loc z := by
  simp [Function.update_of_ne h]

variable {c}

theorem wr_go_gC (hI : Inv c) (p : Fin n) (pc : PC)
    (hcnt : ∀ s d, ({ c.loc p with pc := pc } : Loc J).cnt s d = (c.loc p).cnt s d) (s : J) (d : Bool) :
    (c.go p pc).C s d = ∑ y, ((c.go p pc).loc y).cnt s d := by
  have h := sum_cnt_update c.loc p { c.loc p with pc := pc } s d
  rw [hcnt] at h
  simp only [Cfg.go_eq, Cfg.setLoc_C, Cfg.setLoc_loc]
  rw [hI.gC s d]
  exact (Nat.add_right_cancel h).symm

theorem wr_go_gQ (hI : Inv c) (p : Fin n) (pc : PC)
    (hq : PC.btw .l5_1 .l13 pc ↔ PC.btw .l5_1 .l13 (c.loc p).pc) (y : Fin n) :
    (c.go p pc).Q y = if PC.btw .l5_1 .l13 ((c.go p pc).loc y).pc then
      some (((c.go p pc).loc y).s, ((c.go p pc).loc y).d, ((c.go p pc).loc y).tm) else none := by
  by_cases hy : y = p
  · subst hy
    simp only [Cfg.go_eq, Cfg.setLoc_Q, Cfg.setLoc_loc, Function.update_self]
    rw [hI.gQ y]; exact if_congr hq.symm rfl rfl
  · simp only [Cfg.go_eq, Cfg.setLoc_Q, Cfg.setLoc_loc, Function.update_of_ne hy]
    exact hI.gQ y

theorem wr_go_g5 (hI : Inv c) (p : Fin n) (pc : PC)
    (hps : ({ c.loc p with pc := pc } : Loc J).pside = (c.loc p).pside)
    (hr : PC.btw .l1_4 .l15 pc ↔ PC.btw .l1_4 .l15 (c.loc p).pc) (s : J)
    (h1 : (c.go p pc).S.1 = s) (h2 : (c.go p pc).In s = (c.go p pc).S.2.1) :
    ∃ y, ((c.go p pc).loc y).s = s ∧ ((c.go p pc).loc y).pside = some (c.go p pc).S.2.1 ∧
      PC.btw .l1_4 .l15 ((c.go p pc).loc y).pc := by
  simp only [Cfg.go_eq, Cfg.setLoc_S, Cfg.setLoc_In, Cfg.setLoc_loc] at h1 h2 ⊢
  obtain ⟨y, y1, y2, y3⟩ := hI.g5 s h1 h2
  refine ⟨y, ?_⟩
  by_cases hy : y = p
  · subst hy; rw [Function.update_self]; exact ⟨y1, hps.trans y2, hr.2 y3⟩
  · rw [Function.update_of_ne hy]; exact ⟨y1, y2, y3⟩

theorem wr_go_g7 (hI : Inv c) (p : Fin n) (pc : PC)
    (hps : ({ c.loc p with pc := pc } : Loc J).pside = (c.loc p).pside) (s : J) (y : Fin n)
    (h1 : (c.go p pc).S.1 ≠ s) (h2 : ((c.go p pc).loc y).s = s) (e : Bool)
    (h3 : ((c.go p pc).loc y).pside = some e) : e = (c.go p pc).In s := by
  simp only [Cfg.go_eq, Cfg.setLoc_S, Cfg.setLoc_In, Cfg.setLoc_loc] at h1 h2 h3 ⊢
  by_cases hy : y = p
  · subst hy; rw [Function.update_self] at h2 h3
    exact hI.g7 s y h1 h2 e (hps.symm.trans h3)
  · rw [Function.update_of_ne hy] at h2 h3
    exact hI.g7 s y h1 h2 e h3

theorem wr_go_gU (hI : Inv c) (p : Fin n) (pc : PC) (hU : pc ≠ .l5_5 ∧ pc ≠ .l16_11) (y z : Fin n)
    (hyz : y ≠ z) (hy : ((c.go p pc).loc y).pc = .l5_5 ∨ ((c.go p pc).loc y).pc = .l16_11) :
    ((c.go p pc).loc z).pc ≠ .l5_5 ∧ ((c.go p pc).loc z).pc ≠ .l16_11 := by
  by_cases hyp : y = p
  · subst hyp; rw [wr_go_loc_self] at hy; exact absurd hy (by rcases hU with ⟨h1, h2⟩; tauto)
  · rw [wr_go_loc_ne c pc hyp] at hy
    by_cases hzp : z = p
    · subst hzp; rw [wr_go_loc_self]; exact hU
    · rw [wr_go_loc_ne c pc hzp]; exact hI.gU y z hyz hy

theorem wr_go_g8 (hI : Inv c) (p : Fin n) (pc : PC)
    (hU' : (c.loc p).pc ≠ .l5_5 ∧ (c.loc p).pc ≠ .l16_11)
    (hout : (c.go p pc).Out (c.go p pc).S.1 ≠ (c.go p pc).S.2.1) :
    ∃ z, (((c.go p pc).loc z).pc = .l5_5 ∨ ((c.go p pc).loc z).pc = .l16_11) ∧
      ((c.go p pc).loc z).b = some ((c.go p pc).S.1, (c.go p pc).S.2.1) ∧
      ((c.go p pc).loc z).s = (c.go p pc).S.2.2 := by
  obtain ⟨z, z1, z2, z3⟩ := hI.g8 hout
  have hzp : z ≠ p := by rintro rfl; rcases z1 with h1 | h1; exacts [hU'.1 h1, hU'.2 h1]
  refine ⟨z, ?_⟩
  rw [wr_go_loc_ne c pc hzp]
  exact ⟨z1, z2, z3⟩

/-- Writing `Out[S.1] ← S.2.1`: the per-process clauses that mention `Out`. -/
theorem wr_LI_setOut {c1 : Cfg n J} {y : Fin n} (h : LI c1 y) (O : J → Bool)
    (hO : ∀ u, u ≠ c1.S.1 → O u = c1.Out u) (he : O c1.S.1 = c1.S.2.1)
    (h5 : (c1.loc y).pc = .l5_5 → c1.S.1 = c1.S.2.2)
    (h11 : (c1.loc y).pc = .l16_11 → c1.S.1 = c1.S.2.2) :
    LI { c1 with Out := O } y :=
  { h with
    i5 := fun hb => by
      obtain ⟨a, b, -⟩ := h.i5 hb
      refine ⟨a, b, ?_⟩
      show O (c1.loc y).s = (c1.loc y).d
      rw [← a, he, b]
    i8 := fun hb hO' => by
      change O (c1.loc y).s = (c1.loc y).d at hO'
      by_cases hs : (c1.loc y).s = c1.S.1
      · rw [hs, he] at hO'; exact ⟨hs.symm, hO'⟩
      · rw [hO _ hs] at hO'; exact h.i8 hb hO'
    p5 := fun hb => by
      obtain ⟨sh, dh, hb', h1, h2⟩ := h.p5 hb
      refine ⟨sh, dh, hb', fun hne => ?_, h2⟩
      obtain ⟨e1, -, -⟩ := h1 hne
      have := h5 hb
      rw [e1] at this
      exact absurd this hne
    p11 := fun hb => by
      obtain ⟨sh, dh, -, e1, e2, -⟩ := h.p11 hb
      have := h11 hb
      rw [e1] at this
      exact absurd this e2
    p13 := fun hb => (h.p13 hb).imp id (fun ⟨e1, e2, e3⟩ =>
      ⟨by show O _ = _; rw [hO _ (Ne.symm e2)]; exact e1, e2, e3⟩) }

theorem wr_g4_setOut (hI : Inv c) (O : J → Bool) (hO : ∀ u, u ≠ c.S.1 → O u = c.Out u)
    (he : O c.S.1 = c.S.2.1) (s : J) : c.In s ≠ O s ∨ (c.S.1 = s ∧ c.S.2.1 = O s) := by
  by_cases hs : s = c.S.1
  · subst hs; exact Or.inr ⟨rfl, he.symm⟩
  · rw [hO s hs]; exact hI.g4 s

omit [DecidableEq J] in
theorem wr_ns_go {p : Fin n} {pc : PC}
    (hps : ∀ e, ({ c.loc p with pc := pc } : Loc J).pside = some e → (c.loc p).pside = some e)
    (h56 : pc ≠ .l1_5 ∧ pc ≠ .l1_6) :
    NoSide c c.S.1 c.S.2.1 → minQ c.Q ≠ none → (∀ sh dh, minQ c.Q = some (sh, dh) → sh ≠ c.S.1) →
    ((c.go p pc).loc p).s = c.S.1 → ((c.go p pc).loc p).pc ≠ .l1_5 ∧
      ((c.go p pc).loc p).pc ≠ .l1_6 ∧ ((c.go p pc).loc p).pside ≠ some c.S.2.1 := by
  intro hns _ _ hs
  rw [wr_go_loc_self] at hs ⊢
  exact ⟨h56.1, h56.2, fun h => (hns p hs).2.2 (hps _ h)⟩

theorem wr_go_win (hI : Inv c) {p : Fin n} (pc : PC) (hp : PC.btw .l16_10 .l16_14 (c.loc p).pc) :
    (c.go p pc).Ex = some ((c.go p pc).loc p).s ∧
      (c.go p pc).Exclear ((c.go p pc).loc p).s = false ∧
      ∀ z, z ≠ p → WinOK (c.go p pc) ((c.go p pc).loc p).s z := by
  obtain ⟨e1, e2, e3⟩ := (hI.li p).win hp
  rw [wr_go_loc_self]
  refine ⟨e1, e2, fun z hz => ?_⟩
  unfold WinOK; rw [wr_go_loc_ne c pc hz]; exact e3 z hz

theorem wr_go_winS (hI : Inv c) {p : Fin n} (pc : PC) (hp : PC.btw .l16_10 .l16_14 (c.loc p).pc)
    (h : (c.go p pc).S.1 ≠ ((c.go p pc).loc p).s) :
    ExW (c.go p pc) (c.go p pc).S.1 (c.go p pc).S.2.1 .l5_1 .l12 := by
  rw [wr_go_loc_self] at h
  obtain ⟨m, m1, m2, m3⟩ := (hI.li p).winS hp h
  have hm : m ≠ p := by rintro rfl; exact absurd (le_trans hp.1 m3.2) (by decide)
  refine ⟨m, ?_⟩
  rw [wr_go_loc_ne c pc hm]
  exact ⟨m1, m2, m3⟩

/-- Assembly for a local step that only moves `p` to `pc`. -/
theorem wr_inv_go (hI : Inv c) (p : Fin n) (pc : PC) (hLO : LocalOK c (c.go p pc) p)
    (hcnt : ∀ s d, ({ c.loc p with pc := pc } : Loc J).cnt s d = (c.loc p).cnt s d)
    (hq : PC.btw .l5_1 .l13 pc ↔ PC.btw .l5_1 .l13 (c.loc p).pc)
    (hps : ({ c.loc p with pc := pc } : Loc J).pside = (c.loc p).pside)
    (hr : PC.btw .l1_4 .l15 pc ↔ PC.btw .l1_4 .l15 (c.loc p).pc)
    (hU : pc ≠ .l5_5 ∧ pc ≠ .l16_11) (hU' : (c.loc p).pc ≠ .l5_5 ∧ (c.loc p).pc ≠ .l16_11)
    (hLp : LI (c.go p pc) p) : Inv (c.go p pc) := by
  refine ⟨wr_go_gC hI p pc hcnt, wr_go_gQ hI p pc hq, hI.g4, wr_go_g5 hI p pc hps hr,
    wr_go_g7 hI p pc hps, wr_go_gU hI p pc hU, wr_go_g8 hI p pc hU', fun y => ?_⟩
  by_cases hy : y = p
  · subst hy; exact hLp
  · exact LI_frame_local hI hLO hy

omit [DecidableEq J] in
/-- Writing `Exclear`: the per-process clauses that mention it. -/
theorem wr_LI_setExclear {c1 : Cfg n J} {y : Fin n} (h : LI c1 y) (E : J → Bool)
    (hw5 : PC.btw .l16_6 .l16_9 (c1.loc y).pc → c1.linkEx y = true → E (c1.loc y).s = false)
    (hwin : PC.btw .l16_10 .l16_14 (c1.loc y).pc → E (c1.loc y).s = false) :
    LI { c1 with Exclear := E } y :=
  { h with
    w5 := hw5
    win := fun hb => ⟨(h.win hb).1, hwin hb, (h.win hb).2.2⟩ }

omit [DecidableEq J] in
theorem wr_go_ExW {p : Fin n} (pc : PC) (hp8 : ¬ PC.btw .l5_1 .l8 (c.loc p).pc) {s : J} {d : Bool}
    (h : ExW c s d .l5_1 .l8) : ExW (c.go p pc) s d .l5_1 .l8 := by
  obtain ⟨m, m1, m2, m3⟩ := h
  have hm : m ≠ p := by rintro rfl; exact hp8 m3
  exact ⟨m, by rw [wr_go_loc_ne c pc hm]; exact ⟨m1, m2, m3⟩⟩

omit [DecidableEq J] in
theorem wr_go_NoSide {p : Fin n} (pc : PC)
    (hps : ∀ e, ({ c.loc p with pc := pc } : Loc J).pside = some e → (c.loc p).pside = some e)
    (h56 : pc ≠ .l1_5 ∧ pc ≠ .l1_6) {s : J} {e : Bool} (h : NoSide c s e) :
    NoSide (c.go p pc) s e := by
  intro z hz
  by_cases hzp : z = p
  · subst hzp
    rw [wr_go_loc_self] at hz ⊢
    exact ⟨h56.1, h56.2, fun h' => (h z hz).2.2 (hps _ h')⟩
  · rw [wr_go_loc_ne c pc hzp] at hz ⊢; exact h z hz

/-- Frame lemma for a successful `SC` on `Ex` by `p` (which only moves `p` to `pc`): the clauses
of a process `y ≠ p` that is not a winner. -/
theorem wr_LI_frameEx (hI : Inv c) {p y : Fin n} (pc : PC) (v : Option J) (hy : y ≠ p)
    (hp8 : ¬ PC.btw .l5_1 .l8 (c.loc p).pc)
    (hps : ∀ e, ({ c.loc p with pc := pc } : Loc J).pside = some e → (c.loc p).pside = some e)
    (h56 : pc ≠ .l1_5 ∧ pc ≠ .l1_6)
    (hnw : ¬ PC.btw .l16_10 .l16_14 (c.loc y).pc)
    (hw3 : ((c.loc y).pc = .l16_3 ∨ (c.loc y).pc = .l16_2) → v = none) :
    LI { c.go p pc with Ex := v, linkEx := fun _ => false } y := by
  have hL := hI.li y
  have hExW : ∀ {s d}, ExW c s d .l5_1 .l8 →
      ExW { c.go p pc with Ex := v, linkEx := fun _ => false } s d .l5_1 .l8 :=
    fun h => wr_go_ExW pc hp8 h
  have hNS : ∀ {s e}, NoSide c s e → NoSide { c.go p pc with Ex := v, linkEx := fun _ => false } s e :=
    fun h => wr_go_NoSide pc hps h56 h
  set c' : Cfg n J := { c.go p pc with Ex := v, linkEx := fun _ => false } with hc'
  have hS : c'.S = c.S := rfl
  have hG : c'.G = c.G := rfl
  have hIn : c'.In = c.In := rfl
  have hOut : c'.Out = c.Out := rfl
  have hlS : c'.linkS = c.linkS := rfl
  have hlE : c'.linkEx = fun _ => false := rfl
  have hEx : c'.Ex = v := rfl
  have hlz : ∀ z, z ≠ p → c'.loc z = c.loc z := fun z hz => wr_go_loc_ne c pc hz
  have hly := hlz y hy
  constructor
  · rw [hly, hG]; exact hL.tm
  · rw [hly, hS]
    intro h1 h2 h3
    obtain ⟨q, q1, q2, q3, q4⟩ := hL.l1 h1 h2 h3
    have hq : q ≠ p := by rintro rfl; exact hp8 q2
    refine ⟨q, ?_⟩
    rw [hlz q hq, hG]; exact ⟨q1, q2, q3, q4⟩
  · rw [hly, hS, hIn]; exact hL.l14
  · rw [hly, hS]; exact hL.l16
  · rw [hly, hS, hOut]; exact hL.i5
  · rw [hly, hS]; exact hL.i7
  · rw [hly, hS, hOut]; exact hL.i8
  · rw [hly, hS, hlS]; exact hL.a1
  · rw [hly, hS, hlS]
    intro h1 h2
    obtain ⟨sh, dh, hb, hw⟩ := hL.a2 h1 h2
    exact ⟨sh, dh, hb, fun hne => hExW (hw hne)⟩
  · rw [hly, hS, hlS]
    intro h1 h2
    obtain ⟨hns, hsh⟩ := hL.a3 h1 h2
    exact ⟨hNS hns, hsh⟩
  · rw [hly, hS, hOut]
    intro h1
    obtain ⟨sh, dh, hb, hne, heq⟩ := hL.p5 h1
    refine ⟨sh, dh, hb, fun hs => ?_, heq⟩
    obtain ⟨e1, e2, e3⟩ := hne hs
    exact ⟨e1, e2, hExW e3⟩
  · rw [hly, hS, hlS]; exact hL.e1
  · rw [hly, hlS]; exact hL.x1
  · rw [hly, hlS]
    intro h1 h2 sh dh hb hne
    exact hExW (hL.x2 h1 h2 sh dh hb hne)
  · rw [hlE]; intro _ h; simp at h
  · rw [hlE]; intro _ _ h; simp at h
  · rw [hly, hlS]
    intro h1 h2
    obtain ⟨hns, sh, dh, hb, hne, hw⟩ := hL.e3 h1 h2
    exact ⟨hNS hns, sh, dh, hb, hne, hExW hw⟩
  · rw [hly]; intro h; exact absurd (by rw [h]; decide) hnw
  · rw [hlE]; intro _ h; simp at h
  · rw [hlE]; intro _ h; simp at h
  · rw [hly, hEx, hlE]
    intro h
    apply hw3
    rcases h with h | ⟨h, -⟩
    exacts [Or.inl h, Or.inr h]
  · rw [hlE]; intro _ h; simp at h
  · rw [hlE]; intro _ h; simp at h
  · rw [hly]; intro h; exact absurd h hnw
  · rw [hly]; intro h; exact absurd h hnw
  · rw [hly]; intro h; exact absurd (by rw [h]; decide) hnw

/-- Assembly for a successful `SC` on `Ex` that moves `p` to `pc`. -/
theorem wr_inv_scEx (hI : Inv c) (p : Fin n) (pc : PC) (v : Option J)
    (hcnt : ∀ s d, ({ c.loc p with pc := pc } : Loc J).cnt s d = (c.loc p).cnt s d)
    (hq : PC.btw .l5_1 .l13 pc ↔ PC.btw .l5_1 .l13 (c.loc p).pc)
    (hps : ({ c.loc p with pc := pc } : Loc J).pside = (c.loc p).pside)
    (hr : PC.btw .l1_4 .l15 pc ↔ PC.btw .l1_4 .l15 (c.loc p).pc)
    (hU : pc ≠ .l5_5 ∧ pc ≠ .l16_11) (hU' : (c.loc p).pc ≠ .l5_5 ∧ (c.loc p).pc ≠ .l16_11)
    (hli : ∀ y, LI { c.go p pc with Ex := v, linkEx := fun _ => false } y) :
    Inv { c.go p pc with Ex := v, linkEx := fun _ => false } :=
  ⟨wr_go_gC hI p pc hcnt, wr_go_gQ hI p pc hq, hI.g4, wr_go_g5 hI p pc hps hr,
    wr_go_g7 hI p pc hps, wr_go_gU hI p pc hU, wr_go_g8 hI p pc hU', hli⟩

/-- Assembly for a step that writes `Out[S.1] ← S.2.1` and moves `p` to `pc`. -/
theorem wr_inv_setOut (hI : Inv c) (p : Fin n) (pc : PC) (hLO : LocalOK c (c.go p pc) p)
    (hcnt : ∀ s d, ({ c.loc p with pc := pc } : Loc J).cnt s d = (c.loc p).cnt s d)
    (hq : PC.btw .l5_1 .l13 pc ↔ PC.btw .l5_1 .l13 (c.loc p).pc)
    (hps : ({ c.loc p with pc := pc } : Loc J).pside = (c.loc p).pside)
    (hr : PC.btw .l1_4 .l15 pc ↔ PC.btw .l1_4 .l15 (c.loc p).pc)
    (hU : pc ≠ .l5_5 ∧ pc ≠ .l16_11)
    (h5 : ∀ y, y ≠ p → (c.loc y).pc = .l5_5 → c.S.1 = c.S.2.2)
    (h11 : ∀ y, y ≠ p → (c.loc y).pc = .l16_11 → c.S.1 = c.S.2.2)
    (hLp : LI { c.go p pc with Out := Function.update c.Out c.S.1 c.S.2.1 } p) :
    Inv { c.go p pc with Out := Function.update c.Out c.S.1 c.S.2.1 } := by
  refine ⟨wr_go_gC hI p pc hcnt, wr_go_gQ hI p pc hq,
    wr_g4_setOut hI _ (fun u hu => Function.update_of_ne hu _ _) (Function.update_self _ _ _),
    wr_go_g5 hI p pc hps hr, wr_go_g7 hI p pc hps, wr_go_gU hI p pc hU, ?_, ?_⟩
  · intro h; exact (h (Function.update_self c.S.1 c.S.2.1 c.Out)).elim
  · intro y
    by_cases hy : y = p
    · subst hy; exact hLp
    · exact wr_LI_setOut (LI_frame_local hI hLO hy) _ (fun u hu => Function.update_of_ne hu _ _)
        (Function.update_self _ _ _)
        (fun h => h5 y hy (by rwa [wr_go_loc_ne c pc hy] at h))
        (fun h => h11 y hy (by rwa [wr_go_loc_ne c pc hy] at h))

end WrHelpers

theorem inv_step_l5_5 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l5_5) :
    Inv (c.step p σ) := by
  obtain ⟨sh, dh, hb, hne, heq⟩ := (hI.li p).p5 hp
  have hS : c.S.1 = sh ∧ c.S.2.1 = dh := by
    by_cases h : sh = (c.loc p).s
    · exact ⟨(heq h).1, (heq h).2.1⟩
    · have := (hne h).1; rw [this]; exact ⟨rfl, rfl⟩
  obtain ⟨hS1, hS2⟩ := hS
  subst hS1 hS2
  have hstep : c.step p σ = { c.go p .l6 with Out := Function.update c.Out c.S.1 c.S.2.1 } := by
    simp only [Cfg.step, hp, hb]; rfl
  rw [hstep]
  have hLO : LocalOK c (c.go p .l6) p := by
    refine ⟨rfl, rfl, le_rfl, rfl, rfl, rfl, fun z hz => wr_go_loc_ne c _ hz, fun _ _ => rfl,
      fun _ _ => rfl, ?_, ?_, ?_, ?_, wr_ns_go (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp), ?_, ?_⟩ <;>
      simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  have hU := fun y (hy : y ≠ p) => hI.gU p y (Ne.symm hy) (Or.inl hp)
  apply wr_inv_setOut hI p .l6 hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · simp [hp, PC.btw, PC.idx]
  · simp [Loc.pside, hp, PC.btw, PC.idx]
  · simp [hp, PC.btw, PC.idx]
  · simp
  · intro y hy h; exact absurd h (hU y hy).1
  · intro y hy h; exact absurd h (hU y hy).2
  · constructor <;> simp [PC.btw, PC.idx]
    case tm => exact (hI.li p).tm (by rw [hp]; decide)
    case l1 =>
      intro h1 h2
      by_cases h : c.S.1 = (c.loc p).s
      · rw [(heq h).2.2] at h2; simp at h2
      · exact absurd h1 h
    case i8 =>
      intro h
      by_cases hs : (c.loc p).s = c.S.1
      · rw [hs, Function.update_self] at h; exact ⟨hs.symm, h⟩
      · rw [Function.update_of_ne hs] at h; exact (hI.li p).i8 (by rw [hp]; decide) h

theorem inv_step_l7 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l7) :
    Inv (c.step p σ) := by
  have hi7 := (hI.li p).i7 hp
  have hstep : c.step p σ = { c.go p .l8 with Out := Function.update c.Out c.S.1 c.S.2.1 } := by
    simp only [Cfg.step, hp]; rw [hi7]; rfl
  rw [hstep]
  have hLO : LocalOK c (c.go p .l8) p := by
    refine ⟨rfl, rfl, le_rfl, rfl, rfl, rfl, fun z hz => wr_go_loc_ne c _ hz, fun _ _ => rfl,
      fun _ _ => rfl, ?_, ?_, ?_, ?_, wr_ns_go (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp), ?_, ?_⟩ <;>
      simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  apply wr_inv_setOut hI p .l8 hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · simp [hp, PC.btw, PC.idx]
  · simp [Loc.pside, hp, PC.btw, PC.idx]
  · simp [hp, PC.btw, PC.idx]
  · simp
  · intros; rw [hi7]
  · intros; rw [hi7]
  · constructor <;> simp [PC.btw, PC.idx]
    case tm => exact (hI.li p).tm (by rw [hp]; decide)
    case l1 => intro _ h; rw [hi7] at h; simp at h
    case i8 => intro _; rw [hi7]; simp

theorem inv_step_l16_11 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_11) :
    Inv (c.step p σ) := by
  obtain ⟨sh, dh, hb, hS, -, -, -⟩ := (hI.li p).p11 hp
  have hS1 : c.S.1 = sh := by rw [hS]
  have hS2 : c.S.2.1 = dh := by rw [hS]
  subst hS1 hS2
  have hstep : c.step p σ = { c.go p .l16_12 with Out := Function.update c.Out c.S.1 c.S.2.1 } := by
    simp only [Cfg.step, hp, hb]; rfl
  rw [hstep]
  have hLO : LocalOK c (c.go p .l16_12) p := by
    refine ⟨rfl, rfl, le_rfl, rfl, rfl, rfl, fun z hz => wr_go_loc_ne c _ hz, fun _ _ => rfl,
      fun _ _ => rfl, ?_, ?_, ?_, ?_, wr_ns_go (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp), ?_, ?_⟩ <;>
      simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  have hU := fun y (hy : y ≠ p) => hI.gU p y (Ne.symm hy) (Or.inr hp)
  have hwin := (hI.li p).win (by rw [hp]; decide)
  apply wr_inv_setOut hI p .l16_12 hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · simp [hp, PC.btw, PC.idx]
  · simp [Loc.pside, hp, PC.btw, PC.idx]
  · simp [hp, PC.btw, PC.idx]
  · simp
  · intro y hy h; exact absurd h (hU y hy).1
  · intro y hy h; exact absurd h (hU y hy).2
  · constructor
    case win => exact fun _ => wr_go_win hI _ (by rw [hp]; decide)
    case winS => exact fun _ => wr_go_winS hI _ (by rw [hp]; decide)
    all_goals simp [PC.btw, PC.idx]

theorem inv_step_l16_13 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_13) :
    Inv (c.step p σ) := by
  have hLO : LocalOK c (c.go p .l16_14) p := by
    refine ⟨rfl, rfl, le_rfl, rfl, rfl, rfl, fun z hz => wr_go_loc_ne c _ hz, fun _ _ => rfl,
      fun _ _ => rfl, ?_, ?_, ?_, ?_, wr_ns_go (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp), ?_, ?_⟩ <;>
      simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  have hLp : ∀ O : J → Bool, LI { c.go p .l16_14 with Out := O } p := by
    intro O
    constructor
    case win => exact fun _ => wr_go_win hI _ (by rw [hp]; decide)
    case winS => exact fun _ => wr_go_winS hI _ (by rw [hp]; decide)
    all_goals simp [PC.btw, PC.idx]
  rcases (hI.li p).p13 hp with hS | ⟨hO, -, -⟩
  · have hS1 : c.S.1 = (c.loc p).a.1 := by rw [hS]
    have hS2 : c.S.2.1 = (c.loc p).a.2 := by rw [hS]
    have hS3 : c.S.1 = c.S.2.2 := by rw [hS]
    have hstep : c.step p σ = { c.go p .l16_14 with Out := Function.update c.Out c.S.1 c.S.2.1 } := by
      simp only [Cfg.step, hp]; rw [← hS1, ← hS2]; rfl
    rw [hstep]
    apply wr_inv_setOut hI p .l16_14 hLO
    · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · simp [hp, PC.btw, PC.idx]
    · simp [Loc.pside, hp, PC.btw, PC.idx]
    · simp [hp, PC.btw, PC.idx]
    · simp
    · intros; exact hS3
    · intros; exact hS3
    · exact hLp _
  · have hstep : c.step p σ = c.go p .l16_14 := by
      simp only [Cfg.step, hp]
      have : Function.update c.Out (c.loc p).a.1 (c.loc p).a.2 = c.Out := by
        rw [← hO]; exact Function.update_eq_self _ _
      simp only [Cfg.setOut, this]
    rw [hstep]
    apply wr_inv_go hI p .l16_14 hLO
    · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · simp [hp, PC.btw, PC.idx]
    · simp [Loc.pside, hp, PC.btw, PC.idx]
    · simp [hp, PC.btw, PC.idx]
    · simp
    · simp [hp]
    · exact hLp c.Out

theorem inv_step_l15 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l15) :
    Inv (c.step p σ) := by
  obtain ⟨hS1, hS2, hO⟩ := (hI.li p).i5 (by rw [hp]; decide)
  have hstep : c.step p σ =
      { c.go p .l16_1 with In := Function.update c.In (c.loc p).s (!(c.loc p).d) } := by
    simp only [Cfg.step, hp]; rfl
  rw [hstep]
  have hLO : LocalOK c (c.go p .l16_1) p := by
    refine ⟨rfl, rfl, le_rfl, rfl, rfl, rfl, fun z hz => wr_go_loc_ne c _ hz, fun _ _ => rfl,
      fun _ _ => rfl, ?_, ?_, ?_, ?_, wr_ns_go (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp), ?_, ?_⟩ <;>
      simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  refine ⟨wr_go_gC hI p _ (by intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]),
    wr_go_gQ hI p _ (by simp [hp, PC.btw, PC.idx]), ?_, ?_, ?_,
    wr_go_gU hI p _ (by simp), wr_go_g8 hI p _ (by simp [hp]), ?_⟩
  · intro t
    change Function.update c.In (c.loc p).s (!(c.loc p).d) t ≠ c.Out t ∨
      (c.S.1 = t ∧ c.S.2.1 = c.Out t)
    by_cases ht : t = (c.loc p).s
    · subst ht; left; rw [Function.update_self, hO]; simp
    · rw [Function.update_of_ne ht]; exact hI.g4 t
  · intro t h1 h2
    change c.S.1 = t at h1
    change Function.update c.In (c.loc p).s (!(c.loc p).d) t = c.S.2.1 at h2
    by_cases ht : t = (c.loc p).s
    · subst ht; rw [Function.update_self, hS2] at h2; simp at h2
    · rw [Function.update_of_ne ht] at h2
      obtain ⟨y, y1, y2, y3⟩ := hI.g5 t h1 h2
      have hy : y ≠ p := by rintro rfl; exact ht y1.symm
      refine ⟨y, ?_⟩
      change (((c.go p .l16_1).loc y).s = t ∧ ((c.go p .l16_1).loc y).pside = some c.S.2.1 ∧
        PC.btw .l1_4 .l15 ((c.go p .l16_1).loc y).pc)
      rw [wr_go_loc_ne c _ hy]; exact ⟨y1, y2, y3⟩
  · intro t y h1 h2 e h3
    change c.S.1 ≠ t at h1
    change ((c.go p .l16_1).loc y).s = t at h2
    change ((c.go p .l16_1).loc y).pside = some e at h3
    change e = Function.update c.In (c.loc p).s (!(c.loc p).d) t
    have ht : t ≠ (c.loc p).s := fun h => h1 (hS1.trans h.symm)
    rw [Function.update_of_ne ht]
    have hy : y ≠ p := by rintro rfl; rw [wr_go_loc_self] at h2; exact ht h2.symm
    rw [wr_go_loc_ne c _ hy] at h2 h3
    exact hI.g7 t y h1 h2 e h3
  · intro y
    by_cases hy : y = p
    · subst hy
      constructor
      case i5 => intro _; simp [hS1, hS2, hO]
      all_goals simp [PC.btw, PC.idx]
    · refine { LI_frame_local hI hLO hy with l14 := ?_ }
      change ((c.go p .l16_1).loc y).pc = .l1_4 ∨ ((c.go p .l16_1).loc y).pc = .l1_5 →
        ((c.go p .l16_1).loc y).d = Function.update c.In (c.loc p).s (!(c.loc p).d) ((c.go p .l16_1).loc y).s ∨
          (c.S.1 = ((c.go p .l16_1).loc y).s ∧ c.S.2.1 = ((c.go p .l16_1).loc y).d)
      rw [wr_go_loc_ne c _ hy]
      intro h
      by_cases hs : (c.loc y).s = (c.loc p).s
      · rw [hs, Function.update_self]
        by_cases hd : (c.loc y).d = (c.loc p).d
        · exact Or.inr ⟨hS1, hS2.trans hd.symm⟩
        · left; cases h1 : (c.loc y).d <;> cases h2 : (c.loc p).d <;> simp_all
      · rw [Function.update_of_ne hs]; exact (hI.li y).l14 h

theorem inv_step_l16_5 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_5) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ =
      { c.go p .l16_6 with Exclear := Function.update c.Exclear (c.loc p).s false } := by
    simp only [Cfg.step, hp]; rfl
  rw [hstep]
  have hLO : LocalOK c (c.go p .l16_6) p := by
    refine ⟨rfl, rfl, le_rfl, rfl, rfl, rfl, fun z hz => wr_go_loc_ne c _ hz, fun _ _ => rfl,
      fun _ _ => rfl, ?_, ?_, ?_, ?_, wr_ns_go (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp), ?_, ?_⟩ <;>
      simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  have hL := hI.li p
  refine ⟨wr_go_gC hI p _ (by intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]),
    wr_go_gQ hI p _ (by simp [hp, PC.btw, PC.idx]), hI.g4,
    wr_go_g5 hI p _ (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp [hp, PC.btw, PC.idx]),
    wr_go_g7 hI p _ (by simp [Loc.pside, hp, PC.btw, PC.idx]),
    wr_go_gU hI p _ (by simp), wr_go_g8 hI p _ (by simp [hp]), fun y => ?_⟩
  by_cases hy : y = p
  · subst hy
    constructor
    case w2 =>
      intro _ h2 z hz
      change PC.btw .l11 .l16_3 ((c.go y .l16_6).loc z).pc ∨
        (((c.go y .l16_6).loc z).pc = .l10 ∧ c.linkEx z = false) at hz
      change ((c.go y .l16_6).loc z).s = ((c.go y .l16_6).loc y).s ∧
        ((c.go y .l16_6).loc z).d = ((c.go y .l16_6).loc y).d ∧ ((c.go y .l16_6).loc y).pc ≠ .l16_9
      by_cases hzp : z = y
      · subst hzp; rw [wr_go_loc_self] at hz; simp [PC.btw, PC.idx] at hz
      · rw [wr_go_loc_ne c _ hzp] at hz ⊢; rw [wr_go_loc_self]
        obtain ⟨a, b, -⟩ := hL.w2 (by rw [hp]; decide) h2 z hz
        exact ⟨a, b, by simp⟩
    case w4 =>
      intro _ h2 h3
      change ¬ (c.S.1 = ((c.go y .l16_6).loc y).s ∧ c.S.2.1 = ((c.go y .l16_6).loc y).d) at h3
      rw [wr_go_loc_self] at h3
      obtain ⟨m, m1, m2, m3, m4⟩ := hL.w4 (by rw [hp]; decide) h2 h3
      have hm : m ≠ y := by rintro rfl; rw [hp] at m3; exact absurd m3.2 (by decide)
      refine ⟨m, ?_⟩
      change ((c.go y .l16_6).loc m).s = c.S.1 ∧ ((c.go y .l16_6).loc m).d = c.S.2.1 ∧
        PC.btw .l5_1 .l10 ((c.go y .l16_6).loc m).pc ∧
        (((c.go y .l16_6).loc m).pc = .l10 → c.linkEx m = true)
      rw [wr_go_loc_ne c _ hm]; exact ⟨m1, m2, m3, m4⟩
    all_goals simp [PC.btw, PC.idx]
    case i5 => exact hL.i5 (by rw [hp]; decide)
    case e1 => exact hL.e1 (by rw [hp]; decide)
    case w1 => exact hL.w1 (by rw [hp]; decide)
  · refine wr_LI_setExclear (LI_frame_local hI hLO hy) _ ?_ ?_ <;> rw [wr_go_loc_ne c _ hy]
    · intro h1 h2
      by_cases hs : (c.loc y).s = (c.loc p).s
      · rw [hs, Function.update_self]
      · rw [Function.update_of_ne hs]; exact (hI.li y).w5 h1 h2
    · intro h1
      by_cases hs : (c.loc y).s = (c.loc p).s
      · rw [hs, Function.update_self]
      · rw [Function.update_of_ne hs]; exact ((hI.li y).win h1).2.1

theorem inv_step_l16_14 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_14) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ =
      { c.go p .rem with Exclear := Function.update c.Exclear (c.loc p).s true } := by
    simp only [Cfg.step, hp]; rfl
  rw [hstep]
  have hLO : LocalOK c (c.go p .rem) p := by
    refine ⟨rfl, rfl, le_rfl, rfl, rfl, rfl, fun z hz => wr_go_loc_ne c _ hz, fun _ _ => rfl,
      fun _ _ => rfl, ?_, ?_, ?_, ?_, wr_ns_go (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp), ?_, ?_⟩ <;>
      simp [hp, PC.btw, PC.idx, WinOK, SameSDT]
  obtain ⟨-, -, hwin⟩ := (hI.li p).win (by rw [hp]; decide)
  refine ⟨wr_go_gC hI p _ (by intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]),
    wr_go_gQ hI p _ (by simp [hp, PC.btw, PC.idx]), hI.g4,
    wr_go_g5 hI p _ (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp [hp, PC.btw, PC.idx]),
    wr_go_g7 hI p _ (by simp [Loc.pside, hp, PC.btw, PC.idx]),
    wr_go_gU hI p _ (by simp), wr_go_g8 hI p _ (by simp [hp]), fun y => ?_⟩
  by_cases hy : y = p
  · subst hy
    constructor <;> simp [PC.btw, PC.idx]
  · refine wr_LI_setExclear (LI_frame_local hI hLO hy) _ ?_ ?_ <;> rw [wr_go_loc_ne c _ hy]
    · intro h1 h2
      by_cases hs : (c.loc y).s = (c.loc p).s
      · have := (hwin y hy).2.2.2 ⟨le_trans (by decide) h1.1, h1.2⟩
        change c.linkEx y = true at h2
        rw [this] at h2; cases h2
      · rw [Function.update_of_ne hs]; exact (hI.li y).w5 h1 h2
    · intro h1; exact absurd h1 (hwin y hy).1

theorem inv_step_l10_succ (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l10) (hl : c.linkEx p = true) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ = { c.go p .l11 with Ex := none, linkEx := fun _ => false } := by
    simp only [Cfg.step, hp, hl, ite_true]; rfl
  rw [hstep]
  apply wr_inv_scEx hI p .l11 none (by intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx])
    (by simp [hp, PC.btw, PC.idx]) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    (by simp [hp, PC.btw, PC.idx]) (by simp) (by simp [hp])
  intro y
  by_cases hy : y = p
  · subst hy
    constructor
    all_goals simp [PC.btw, PC.idx]
    case tm => exact (hI.li y).tm (by rw [hp]; decide)
    case i5 => exact (hI.li y).i5 (by rw [hp]; decide)
  · refine wr_LI_frameEx hI .l11 none hy (by simp [hp, PC.btw, PC.idx])
      (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp) (fun h => ?_) (fun _ => rfl)
    have := ((hI.li y).win h).2.2 p (Ne.symm hy)
    rw [this.2.2.1 hp] at hl; cases hl

theorem inv_step_l16_2_succ (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_2) (hl : c.linkEx p = true) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ = { c.go p .l16_3 with Ex := none, linkEx := fun _ => false } := by
    simp only [Cfg.step, hp, hl, ite_true]; rfl
  rw [hstep]
  apply wr_inv_scEx hI p .l16_3 none (by intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx])
    (by simp [hp, PC.btw, PC.idx]) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    (by simp [hp, PC.btw, PC.idx]) (by simp) (by simp [hp])
  intro y
  by_cases hy : y = p
  · subst hy
    constructor
    all_goals simp [PC.btw, PC.idx]
    case i5 => exact (hI.li y).i5 (by rw [hp]; decide)
  · refine wr_LI_frameEx hI .l16_3 none hy (by simp [hp, PC.btw, PC.idx])
      (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp) (fun h => ?_) (fun _ => rfl)
    have := (((hI.li y).win h).2.2 p (Ne.symm hy)).2.1 (by rw [hp]; decide)
    rw [hp] at this
    rcases this with h' | ⟨h', -⟩ <;> cases h'

theorem inv_step_l16_9_succ (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l16_9) (hl : c.linkEx p = true) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ =
      { c.go p .l16_10 with Ex := some (c.loc p).s, linkEx := fun _ => false } := by
    simp only [Cfg.step, hp, hl, ite_true]; rfl
  rw [hstep]
  have hL := hI.li p
  -- nobody else is a winner
  have hnw : ∀ y, y ≠ p → ¬ PC.btw .l16_10 .l16_14 (c.loc y).pc := by
    intro y hy h
    have := ((hI.li y).win h).2.2 p (Ne.symm hy)
    rw [this.2.2.2 (by rw [hp]; decide)] at hl; cases hl
  -- nobody is at lines 11..16.3
  have hw2 : ∀ z, ¬ PC.btw .l11 .l16_3 (c.loc z).pc := by
    intro z hz
    exact (hL.w2 (by rw [hp]; decide) hl z (Or.inl hz)).2.2 hp
  have hps : ∀ e, ({ c.loc p with pc := .l16_10 } : Loc J).pside = some e → (c.loc p).pside = some e := by
    simp [Loc.pside, PC.btw, PC.idx]
  apply wr_inv_scEx hI p .l16_10 _ (by intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx])
    (by simp [hp, PC.btw, PC.idx]) (by simp [Loc.pside, hp, PC.btw, PC.idx])
    (by simp [hp, PC.btw, PC.idx]) (by simp) (by simp [hp])
  intro y
  by_cases hy : y = p
  · subst hy
    constructor
    case e1 =>
      intro _ h
      have := hL.e1 (by rw [hp]; decide) h
      rw [wr_go_loc_self]; exact this
    case e3 =>
      intro _ h
      change c.linkS y = true at h
      obtain ⟨hns, sh, dh, hb, hne⟩ := hL.e2 hp h hl
      have hw := hL.x2 (by rw [hp]; decide) h sh dh hb hne
      change NoSide (c.go y .l16_10) ((c.go y .l16_10).loc y).s ((c.go y .l16_10).loc y).d ∧
        ∃ sh dh, ((c.go y .l16_10).loc y).b = some (sh, dh) ∧ sh ≠ ((c.go y .l16_10).loc y).s ∧
          ExW (c.go y .l16_10) sh dh .l5_1 .l8
      rw [wr_go_loc_self]
      exact ⟨wr_go_NoSide _ hps (by simp) hns, sh, dh, hb, hne,
        wr_go_ExW _ (by rw [hp]; decide) hw⟩
    case win =>
      intro _
      change some (c.loc y).s = some ((c.go y .l16_10).loc y).s ∧
        c.Exclear ((c.go y .l16_10).loc y).s = false ∧
        ∀ z, z ≠ y → WinOK { c.go y .l16_10 with Ex := some (c.loc y).s, linkEx := fun _ => false }
          ((c.go y .l16_10).loc y).s z
      rw [wr_go_loc_self]
      refine ⟨rfl, hL.w5 (by rw [hp]; decide) hl, fun z hz => ?_⟩
      unfold WinOK
      change ¬ PC.btw .l16_10 .l16_14 ((c.go y .l16_10).loc z).pc ∧
        (PC.btw .l11 .l16_3 ((c.go y .l16_10).loc z).pc → _) ∧ _ ∧ _
      rw [wr_go_loc_ne c _ hz]
      exact ⟨hnw z hz, fun h => absurd h (hw2 z), fun _ => rfl, fun _ => rfl⟩
    case winS =>
      intro _ h
      change c.S.1 ≠ ((c.go y .l16_10).loc y).s at h
      rw [wr_go_loc_self] at h
      obtain ⟨m, m1, m2, m3, m4⟩ := hL.w4 (by rw [hp]; decide) hl (fun h' => h h'.1)
      have hm : m ≠ y := by rintro rfl; rw [hp] at m3; exact absurd m3.2 (by decide)
      refine ⟨m, ?_⟩
      change ((c.go y .l16_10).loc m).s = c.S.1 ∧ ((c.go y .l16_10).loc m).d = c.S.2.1 ∧
        PC.btw .l5_1 .l12 ((c.go y .l16_10).loc m).pc
      rw [wr_go_loc_ne c _ hm]
      exact ⟨m1, m2, m3.1, le_trans m3.2 (by decide)⟩
    all_goals simp [PC.btw, PC.idx]
  · refine wr_LI_frameEx hI .l16_10 _ hy (by simp [hp, PC.btw, PC.idx]) hps (by simp)
      (hnw y hy) (fun h => ?_)
    exact absurd (by rcases h with h | h <;> rw [h] <;> decide) (hw2 y)

end Podc.GroupMutexLogRMR
