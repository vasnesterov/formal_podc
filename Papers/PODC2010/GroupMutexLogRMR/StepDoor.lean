import Papers.PODC2010.GroupMutexLogRMR.Frame

/-!
# Preservation of `Inv`: the doorway: remainder section and lines 1.1–4
-/

namespace Podc.GroupMutexLogRMR

variable {n : ℕ} {J : Type} [DecidableEq J] {c : Cfg n J}

namespace Cfg

variable (c : Cfg n J)

@[simp] theorem door_incC_loc (s : J) (d : Bool) : (c.incC s d).loc = c.loc := rfl
@[simp] theorem door_incC_Q (s : J) (d : Bool) : (c.incC s d).Q = c.Q := rfl
@[simp] theorem door_incC_S (s : J) (d : Bool) : (c.incC s d).S = c.S := rfl
@[simp] theorem door_incC_G (s : J) (d : Bool) : (c.incC s d).G = c.G := rfl
@[simp] theorem door_incC_In (s : J) (d : Bool) : (c.incC s d).In = c.In := rfl
@[simp] theorem door_incC_Out (s : J) (d : Bool) : (c.incC s d).Out = c.Out := rfl
@[simp] theorem door_incC_Ex (s : J) (d : Bool) : (c.incC s d).Ex = c.Ex := rfl
@[simp] theorem door_incC_Exclear (s : J) (d : Bool) : (c.incC s d).Exclear = c.Exclear := rfl
@[simp] theorem door_incC_linkS (s : J) (d : Bool) : (c.incC s d).linkS = c.linkS := rfl
@[simp] theorem door_incC_linkEx (s : J) (d : Bool) : (c.incC s d).linkEx = c.linkEx := rfl
@[simp] theorem door_decC_loc (s : J) (d : Bool) : (c.decC s d).loc = c.loc := rfl
@[simp] theorem door_decC_Q (s : J) (d : Bool) : (c.decC s d).Q = c.Q := rfl
@[simp] theorem door_decC_S (s : J) (d : Bool) : (c.decC s d).S = c.S := rfl
@[simp] theorem door_decC_G (s : J) (d : Bool) : (c.decC s d).G = c.G := rfl
@[simp] theorem door_decC_In (s : J) (d : Bool) : (c.decC s d).In = c.In := rfl
@[simp] theorem door_decC_Out (s : J) (d : Bool) : (c.decC s d).Out = c.Out := rfl
@[simp] theorem door_decC_Ex (s : J) (d : Bool) : (c.decC s d).Ex = c.Ex := rfl
@[simp] theorem door_decC_Exclear (s : J) (d : Bool) : (c.decC s d).Exclear = c.Exclear := rfl
@[simp] theorem door_decC_linkS (s : J) (d : Bool) : (c.decC s d).linkS = c.linkS := rfl
@[simp] theorem door_decC_linkEx (s : J) (d : Bool) : (c.decC s d).linkEx = c.linkEx := rfl
@[simp] theorem door_llS_loc (p : Fin n) : (c.llS p).loc = c.loc := rfl
@[simp] theorem door_llS_Q (p : Fin n) : (c.llS p).Q = c.Q := rfl
@[simp] theorem door_llS_S (p : Fin n) : (c.llS p).S = c.S := rfl
@[simp] theorem door_llS_C (p : Fin n) : (c.llS p).C = c.C := rfl
@[simp] theorem door_llS_G (p : Fin n) : (c.llS p).G = c.G := rfl
@[simp] theorem door_llS_In (p : Fin n) : (c.llS p).In = c.In := rfl
@[simp] theorem door_llS_Out (p : Fin n) : (c.llS p).Out = c.Out := rfl
@[simp] theorem door_llS_Ex (p : Fin n) : (c.llS p).Ex = c.Ex := rfl
@[simp] theorem door_llS_Exclear (p : Fin n) : (c.llS p).Exclear = c.Exclear := rfl
@[simp] theorem door_llS_linkEx (p : Fin n) : (c.llS p).linkEx = c.linkEx := rfl

end Cfg

/-- `LocalOK` for a step of `p` inside the doorway (old pc ≤ line 4, new pc ≤ line 5.1). -/
theorem door_localOK {c' : Cfg n J} {p : Fin n}
    (hS : c'.S = c.S) (hEx : c'.Ex = c.Ex) (hG : c.G ≤ c'.G) (hIn : c'.In = c.In)
    (hOut : c'.Out = c.Out) (hExc : c'.Exclear = c.Exclear) (hloc : ∀ z, z ≠ p → c'.loc z = c.loc z)
    (hlS : ∀ z, z ≠ p → c'.linkS z = c.linkS z) (hlE : ∀ z, z ≠ p → c'.linkEx z = c.linkEx z)
    (hold : (c.loc p).pc.idx ≤ 10) (hnew : (c'.loc p).pc.idx ≤ 11)
    (hns : NoSide c c.S.1 c.S.2.1 → minQ c.Q ≠ none → (∀ sh dh, minQ c.Q = some (sh, dh) → sh ≠ c.S.1) →
      (c'.loc p).s = c.S.1 → (c'.loc p).pc ≠ .l1_5 ∧ (c'.loc p).pc ≠ .l1_6 ∧
        (c'.loc p).pside ≠ some c.S.2.1) :
    LocalOK c c' p := by
  refine ⟨hS, hEx, hG, hIn, hOut, hExc, hloc, hlS, hlE, ?_, ?_, ?_, ?_, hns, ?_, ?_⟩
  · intro h; exfalso; btw_omega
  · intro h; exfalso; btw_omega
  · intro h; exfalso; btw_omega
  · intro h; exfalso; btw_omega
  · intro _ h
    exfalso
    rcases h with h | ⟨h, -⟩
    · btw_omega
    · rw [h] at hnew; exact absurd hnew (by decide)
  · intro s _ _ _
    refine ⟨fun h => by btw_omega, fun h => by btw_omega, fun h => ?_, fun h => by btw_omega⟩
    rw [h] at hnew; exact absurd hnew (by decide)

/-- The `ns` obligation when `p` keeps its session and side and stays off lines 1.5–1.6. -/
theorem ns_of_same {c' : Cfg n J} {p : Fin n} (hs : (c'.loc p).s = (c.loc p).s)
    (hps : (c'.loc p).pside = (c.loc p).pside) (h5 : (c'.loc p).pc ≠ .l1_5) (h6 : (c'.loc p).pc ≠ .l1_6) :
    NoSide c c.S.1 c.S.2.1 → minQ c.Q ≠ none → (∀ sh dh, minQ c.Q = some (sh, dh) → sh ≠ c.S.1) →
      (c'.loc p).s = c.S.1 → (c'.loc p).pc ≠ .l1_5 ∧ (c'.loc p).pc ≠ .l1_6 ∧
        (c'.loc p).pside ≠ some c.S.2.1 := by
  intro hns _ _ hsS
  rw [hs] at hsS
  exact ⟨h5, h6, by rw [hps]; exact (hns p hsS).2.2⟩

/-- `g5` is kept when `p` does not leave the range and keeps its `pside`, or was not a witness. -/
theorem g5_of_same {c' : Cfg n J} {p : Fin n} (hI : Inv c) (hS : c'.S = c.S) (hIn : c'.In = c.In)
    (hloc : ∀ z, z ≠ p → c'.loc z = c.loc z)
    (hp : ∀ s, (c.loc p).s = s → (c.loc p).pside = some c.S.2.1 → PC.btw .l1_4 .l15 (c.loc p).pc →
      (c'.loc p).s = s ∧ (c'.loc p).pside = some c.S.2.1 ∧ PC.btw .l1_4 .l15 (c'.loc p).pc) :
    ∀ s, c.S.1 = s → c.In s = c.S.2.1 → ∃ y, (c'.loc y).s = s ∧
      (c'.loc y).pside = some c.S.2.1 ∧ PC.btw .l1_4 .l15 (c'.loc y).pc := by
  intro s hs hin
  obtain ⟨y, h1, h2, h3⟩ := hI.g5 s hs hin
  by_cases hy : y = p
  · subst hy; exact ⟨y, hp s h1 h2 h3⟩
  · exact ⟨y, by rw [hloc y hy]; exact h1, by rw [hloc y hy]; exact h2, by rw [hloc y hy]; exact h3⟩

/-- `i8` from `l14` and `g4`. -/
theorem i8_of_l14 (hI : Inv c) {s : J} {d : Bool} (h : d = c.In s ∨ (c.S.1 = s ∧ c.S.2.1 = d))
    (hout : c.Out s = d) : c.S.1 = s ∧ c.S.2.1 = d := by
  rcases h with h | h
  · rcases hI.g4 s with h4 | h4
    · exact absurd (h.symm.trans hout.symm) h4
    · exact ⟨h4.1, h4.2.trans hout⟩
  · exact h

/-- A witness for `l1` from `Min(Q)` being of another session. -/
theorem l1_of_minQ (hI : Inv c) {s : J} {s' : J} {d' : Bool} (hm : minQ c.Q = some (s', d'))
    (hne : s' ≠ s) (hS : c.S.1 = s) :
    ∃ q, (c.loc q).s ≠ s ∧ PC.btw .l5_1 .l8 (c.loc q).pc := by
  obtain ⟨r, t, hr, -⟩ := minQ_eq_some hm
  obtain ⟨hb, he⟩ := hI.q_eq_some hr
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, -, -⟩ := he
  refine ⟨r, by rw [← h1]; exact hne, ?_⟩
  by_contra h8
  have h9 : PC.btw .l9 .l16_6 (c.loc r).pc := by btw_omega
  have := ((hI.li r).i5 h9).1
  exact hne (by rw [h1, ← this, hS])

theorem inv_step_rem (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .rem) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l1_1, s := σ } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l1_1, s := σ }) p :=
    door_localOK (p := p) rfl rfl le_rfl rfl rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hp]; decide) (by simp [PC.idx])
      (fun _ _ _ _ => by simp [Loc.pside, PC.btw, PC.idx])
  apply Inv.of_local hI hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · simp only [Cfg.setLoc_Q, Cfg.door_incC_Q, Cfg.door_decC_Q, Cfg.door_llS_Q]; rw [hI.gQ p]
    simp [hp, PC.btw, PC.idx]
  · exact g5_of_same hI rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun s _ _ h3 => by rw [hp] at h3; exact absurd h3.1 (by decide))
  · intro _ e he; simp [Loc.pside, PC.btw, PC.idx] at he
  · simp
  · simp [hp]
  · constructor <;> simp [PC.btw, PC.idx]

theorem inv_step_l1_1 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l1_1) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ = (c.incC (c.loc p).s false).setLoc p { c.loc p with pc := .l1_2 } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c ((c.incC (c.loc p).s false).setLoc p { c.loc p with pc := .l1_2 }) p :=
    door_localOK (p := p) rfl rfl le_rfl rfl rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hp]; decide) (by simp [PC.idx])
      (fun _ _ _ _ => by simp [Loc.pside, PC.btw, PC.idx])
  apply Inv.of_local hI hLO
  · intro s d
    simp only [Cfg.setLoc_C, Cfg.incC_C, Loc.cnt, hp, Function.update_self]
    by_cases hs : s = (c.loc p).s
    · subst hs; cases d <;> simp [PC.btw, PC.idx]
    · simp [Function.update_of_ne hs, hs, Ne.symm hs]
  · intro _ _; rfl
  · simp only [Cfg.setLoc_Q, Cfg.door_incC_Q, Cfg.door_decC_Q, Cfg.door_llS_Q]; rw [hI.gQ p]
    simp [hp, PC.btw, PC.idx]
  · exact g5_of_same hI rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun s _ _ h3 => by rw [hp] at h3; exact absurd h3.1 (by decide))
  · intro _ e he; simp [Loc.pside, PC.btw, PC.idx] at he
  · simp
  · simp [hp]
  · constructor <;> simp [PC.btw, PC.idx]

theorem inv_step_l1_2 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l1_2) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ = (c.incC (c.loc p).s true).setLoc p { c.loc p with pc := .l1_3 } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c ((c.incC (c.loc p).s true).setLoc p { c.loc p with pc := .l1_3 }) p :=
    door_localOK (p := p) rfl rfl le_rfl rfl rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hp]; decide) (by simp [PC.idx])
      (fun _ _ _ _ => by simp [Loc.pside, PC.btw, PC.idx])
  apply Inv.of_local hI hLO
  · intro s d
    simp only [Cfg.setLoc_C, Cfg.incC_C, Loc.cnt, hp, Function.update_self]
    by_cases hs : s = (c.loc p).s
    · subst hs; cases d <;> simp [PC.btw, PC.idx]
    · simp [Function.update_of_ne hs, hs, Ne.symm hs]
  · intro _ _; rfl
  · simp only [Cfg.setLoc_Q, Cfg.door_incC_Q, Cfg.door_decC_Q, Cfg.door_llS_Q]; rw [hI.gQ p]
    simp [hp, PC.btw, PC.idx]
  · exact g5_of_same hI rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun s _ _ h3 => by rw [hp] at h3; exact absurd h3.1 (by decide))
  · intro _ e he; simp [Loc.pside, PC.btw, PC.idx] at he
  · simp
  · simp [hp]
  · constructor <;> simp [PC.btw, PC.idx]

theorem inv_step_l1_3 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l1_3) :
    Inv (c.step p σ) := by
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l1_4, d := c.In (c.loc p).s } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l1_4, d := c.In (c.loc p).s }) p := by
    refine ⟨rfl, rfl, le_rfl, rfl, rfl, rfl, fun z hz => by simp [Function.update_of_ne hz], fun _ _ => rfl,
      fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hp, PC.btw, PC.idx, WinOK]
    intro hns _ _ hs
    simp [Loc.pside, PC.btw, PC.idx]
    rw [hs]; exact hI.in_ne_of_noSide hns
  apply Inv.of_local hI hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · simp only [Cfg.setLoc_Q, Cfg.door_incC_Q, Cfg.door_decC_Q, Cfg.door_llS_Q]; rw [hI.gQ p]
    simp [hp, PC.btw, PC.idx]
  · intro s hs hin
    obtain ⟨y, h1, h2, h3⟩ := hI.g5 s hs hin
    have hy : y ≠ p := by rintro rfl; rw [hp] at h3; exact absurd h3.1 (by decide)
    exact ⟨y, by simpa [Function.update_of_ne hy] using h1, by simpa [Function.update_of_ne hy] using h2,
      by simpa [Function.update_of_ne hy] using h3⟩
  · intro _ e he
    simp [Loc.pside, PC.btw, PC.idx] at he; simp [he]
  · simp
  · simp [hp]
  · constructor <;> simp [PC.btw, PC.idx]

theorem inv_step_l1_4 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l1_4) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hl14 := hL.l14 (Or.inl hp)
  by_cases hm : minQ c.Q = none ∨ (minQ c.Q).map Prod.fst = some (c.loc p).s
  · have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l1_5 } := by
      simp only [Cfg.step, hp, if_pos hm, Cfg.go_eq]
    rw [hstep]
    have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l1_5 }) p :=
      door_localOK (p := p) rfl rfl le_rfl rfl rfl rfl (fun z hz => Function.update_of_ne hz _ _)
        (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hp]; decide) (by simp [PC.idx])
        (fun _ hne hsh hs => by
          exfalso
          simp only [Cfg.setLoc_loc, Function.update_self] at hs
          rcases hm with hm | hm
          · exact hne hm
          · obtain ⟨⟨s', d'⟩, he⟩ : ∃ e, minQ c.Q = some e := Option.ne_none_iff_exists'.1 hne
            rw [he] at hm
            simp only [Option.map_some, Option.some.injEq] at hm
            exact hsh s' d' he (hm.trans hs))
    apply Inv.of_local hI hLO
    · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · simp only [Cfg.setLoc_Q]; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact g5_of_same hI rfl rfl (fun z hz => Function.update_of_ne hz _ _)
        (fun s h1 h2 _ => ⟨by simpa using h1, by simpa [Loc.pside, hp, PC.btw, PC.idx] using h2, by simp [PC.btw, PC.idx]⟩)
    · intro hs e he
      simp only [Cfg.setLoc_loc, Function.update_self] at hs he ⊢
      have := hI.g7 _ p hs rfl e
      simp [Loc.pside, hp, PC.btw, PC.idx] at he this ⊢
      exact this he
    · simp
    · simp [hp]
    · constructor <;> simp [PC.btw, PC.idx, hl14]
  · have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l1_7 } := by
      simp only [Cfg.step, hp, if_neg hm, Cfg.go_eq]
    rw [hstep]
    have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l1_7 }) p :=
      door_localOK (p := p) rfl rfl le_rfl rfl rfl rfl (fun z hz => Function.update_of_ne hz _ _)
        (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hp]; decide) (by simp [PC.idx])
        (ns_of_same (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp) (by simp))
    apply Inv.of_local hI hLO
    · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · simp only [Cfg.setLoc_Q]; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact g5_of_same hI rfl rfl (fun z hz => Function.update_of_ne hz _ _)
        (fun s h1 h2 _ => ⟨by simpa using h1, by simpa [Loc.pside, hp, PC.btw, PC.idx] using h2, by simp [PC.btw, PC.idx]⟩)
    · intro hs e he
      simp only [Cfg.setLoc_loc, Function.update_self] at hs he ⊢
      have := hI.g7 _ p hs rfl e
      simp [Loc.pside, hp, PC.btw, PC.idx] at he this ⊢
      exact this he
    · simp
    · simp [hp]
    · constructor <;> simp (config := {failIfUnchanged := false}) [PC.btw, PC.idx]
      case l1 =>
        intro hS hSd
        push_neg at hm
        obtain ⟨⟨s', d'⟩, he⟩ : ∃ e, minQ c.Q = some e := Option.ne_none_iff_exists'.1 hm.1
        have hne : s' ≠ (c.loc p).s := by
          intro h; apply hm.2; rw [he, h]; rfl
        obtain ⟨q, q1, q2⟩ := l1_of_minQ hI he hne hS
        have hqp : q ≠ p := by rintro rfl; exact q1 rfl
        exact ⟨q, by rw [Function.update_of_ne hqp]; exact q1, by rw [Function.update_of_ne hqp]; exact q2⟩
      case i8 =>
        exact i8_of_l14 hI hl14

theorem inv_step_l1_5 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l1_5) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hl14 := hL.l14 (Or.inr hp)
  by_cases hc : c.S.1 = (c.loc p).s ∧ c.S.2.1 = !(c.loc p).d
  · have hstep : c.step p σ = (c.llS p).setLoc p { c.loc p with pc := .l1_6 } := by
      simp only [Cfg.step, hp, if_pos hc, Cfg.go_eq]; rfl
    rw [hstep]
    have hLO : LocalOK c ((c.llS p).setLoc p { c.loc p with pc := .l1_6 }) p :=
      door_localOK (p := p) rfl rfl le_rfl rfl rfl rfl (fun z hz => Function.update_of_ne hz _ _)
        (fun z hz => Function.update_of_ne hz _ _) (fun _ _ => rfl) (by rw [hp]; decide) (by simp [PC.idx])
        (fun hns _ _ hs => by
          exfalso
          simp only [Cfg.setLoc_loc, Function.update_self] at hs
          exact (hns p hs).1 hp)
    apply Inv.of_local hI hLO
    · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · simp only [Cfg.setLoc_Q, Cfg.door_llS_Q]; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · refine g5_of_same hI rfl rfl (fun z hz => Function.update_of_ne hz _ _) (fun s h1 h2 _ => ?_)
      exfalso
      simp [Loc.pside, hp, PC.btw, PC.idx] at h2
      rw [hc.2] at h2
      cases h : (c.loc p).d <;> rw [h] at h2 <;> simp at h2
    · intro hs; exfalso; apply hs; simpa using hc.1
    · simp
    · simp [hp]
    · constructor <;> simp (config := {failIfUnchanged := false}) [PC.btw, PC.idx]
      case l16 => exact hc
  · have hstep : c.step p σ = (c.llS p).setLoc p { c.loc p with pc := .l1_7 } := by
      simp only [Cfg.step, hp, if_neg hc, Cfg.go_eq]; rfl
    rw [hstep]
    have hLO : LocalOK c ((c.llS p).setLoc p { c.loc p with pc := .l1_7 }) p :=
      door_localOK (p := p) rfl rfl le_rfl rfl rfl rfl (fun z hz => Function.update_of_ne hz _ _)
        (fun z hz => Function.update_of_ne hz _ _) (fun _ _ => rfl) (by rw [hp]; decide) (by simp [PC.idx])
        (ns_of_same (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp) (by simp))
    apply Inv.of_local hI hLO
    · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
    · intro _ _; rfl
    · simp only [Cfg.setLoc_Q, Cfg.door_llS_Q]; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
    · exact g5_of_same hI rfl rfl (fun z hz => Function.update_of_ne hz _ _)
        (fun s h1 h2 _ => ⟨by simpa using h1, by simpa [Loc.pside, hp, PC.btw, PC.idx] using h2,
          by simp [PC.btw, PC.idx]⟩)
    · intro hs e he
      simp only [Cfg.setLoc_loc, Function.update_self] at hs he ⊢
      have := hI.g7 _ p hs rfl e
      simp [Loc.pside, hp, PC.btw, PC.idx] at he this ⊢
      exact this he
    · simp
    · simp [hp]
    · constructor <;> simp (config := {failIfUnchanged := false}) [PC.btw, PC.idx]
      case l1 => intro h1 h2; exact absurd ⟨h1, h2⟩ hc
      case i8 => exact i8_of_l14 hI hl14

theorem inv_step_l1_6 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l1_6) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hl16 := hL.l16 hp
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l1_7, d := !(c.loc p).d } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l1_7, d := !(c.loc p).d }) p :=
    door_localOK (p := p) rfl rfl le_rfl rfl rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hp]; decide) (by simp [PC.idx])
      (fun hns _ _ hs => by
        exfalso
        simp only [Cfg.setLoc_loc, Function.update_self] at hs
        exact (hns p hs).2.1 hp)
  apply Inv.of_local hI hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · simp only [Cfg.setLoc_Q]; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact g5_of_same hI rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun s h1 h2 _ => ⟨by simpa using h1, by simpa [Loc.pside, hp, PC.btw, PC.idx] using h2,
        by simp [PC.btw, PC.idx]⟩)
  · intro hs; exfalso; apply hs; simpa using hl16.1
  · simp
  · simp [hp]
  · constructor <;> simp (config := {failIfUnchanged := false}) [PC.btw, PC.idx]
    case l1 => intro _ h2; rw [hl16.2] at h2; simp at h2
    case i8 => intro _; exact ⟨hl16.1, hl16.2⟩

theorem inv_step_l1_7 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l1_7) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hstep : c.step p σ = (c.decC (c.loc p).s (!(c.loc p).d)).setLoc p { c.loc p with pc := .l2 } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c ((c.decC (c.loc p).s (!(c.loc p).d)).setLoc p { c.loc p with pc := .l2 }) p :=
    door_localOK (p := p) rfl rfl le_rfl rfl rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hp]; decide) (by simp [PC.idx])
      (ns_of_same (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp) (by simp))
  have hpos : c.C (c.loc p).s (!(c.loc p).d) ≠ 0 :=
    C_pos_of_cnt hI p (by simp [Loc.cnt, hp, PC.btw, PC.idx])
  apply Inv.of_local hI hLO
  · intro s d
    simp only [Cfg.setLoc_C, Cfg.decC_C, Loc.cnt, hp, Function.update_self]
    by_cases hs : s = (c.loc p).s
    · subst hs
      by_cases hd : d = !(c.loc p).d
      · subst hd; simp [PC.btw, PC.idx]; omega
      · have hd' : d = (c.loc p).d := by cases d <;> cases h : (c.loc p).d <;> simp_all
        subst hd'
        simp [PC.btw, PC.idx, Function.update_of_ne hd]
    · simp [Function.update_of_ne hs, hs, Ne.symm hs]
  · intro _ _; rfl
  · simp only [Cfg.setLoc_Q, Cfg.door_decC_Q]; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact g5_of_same hI rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun s h1 h2 _ => ⟨by simpa using h1, by simpa [Loc.pside, hp, PC.btw, PC.idx] using h2,
        by simp [PC.btw, PC.idx]⟩)
  · intro hs e he
    simp only [Cfg.setLoc_loc, Function.update_self] at hs he ⊢
    have := hI.g7 _ p hs rfl e
    simp [Loc.pside, hp, PC.btw, PC.idx] at he this ⊢
    exact this he
  · simp
  · simp [hp]
  · constructor <;> simp (config := {failIfUnchanged := false}) [PC.btw, PC.idx]
    case l1 =>
      intro h1 h2
      obtain ⟨q, q1, q2, -, -⟩ := hL.l1 (by rw [hp]; decide) h1 h2
      have hqp : q ≠ p := by rintro rfl; exact q1 rfl
      exact ⟨q, by rw [Function.update_of_ne hqp]; exact q1, by rw [Function.update_of_ne hqp]; exact q2⟩
    case i8 => exact hL.i8 (by rw [hp]; decide)

theorem inv_step_l2 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l2) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hstep : c.step p σ = ({ c with G := c.G + 1 } : Cfg n J).setLoc p { c.loc p with pc := .l3 } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c (({ c with G := c.G + 1 } : Cfg n J).setLoc p { c.loc p with pc := .l3 }) p :=
    door_localOK (p := p) rfl rfl (by simp) rfl rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hp]; decide) (by simp [PC.idx])
      (ns_of_same (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp) (by simp))
  apply Inv.of_local hI hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · simp only [Cfg.setLoc_Q]; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact g5_of_same hI rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun s h1 h2 _ => ⟨by simpa using h1, by simpa [Loc.pside, hp, PC.btw, PC.idx] using h2,
        by simp [PC.btw, PC.idx]⟩)
  · intro hs e he
    simp only [Cfg.setLoc_loc, Function.update_self] at hs he ⊢
    have := hI.g7 _ p hs rfl e
    simp [Loc.pside, hp, PC.btw, PC.idx] at he this ⊢
    exact this he
  · simp
  · simp [hp]
  · constructor <;> simp (config := {failIfUnchanged := false}) [PC.btw, PC.idx]
    case l1 =>
      intro h1 h2
      obtain ⟨q, q1, q2, -, -⟩ := hL.l1 (by rw [hp]; decide) h1 h2
      have hqp : q ≠ p := by rintro rfl; exact q1 rfl
      refine ⟨q, by rw [Function.update_of_ne hqp]; exact q1, by rw [Function.update_of_ne hqp]; exact q2, ?_⟩
      rw [Function.update_of_ne hqp]
      have := (hI.li q).tm ⟨le_trans (by decide) q2.1, le_trans q2.2 (by decide)⟩
      omega
    case i8 => exact hL.i8 (by rw [hp]; decide)

theorem inv_step_l3 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l3) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hstep : c.step p σ = c.setLoc p { c.loc p with pc := .l4, tm := c.G } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c (c.setLoc p { c.loc p with pc := .l4, tm := c.G }) p :=
    door_localOK (p := p) rfl rfl le_rfl rfl rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hp]; decide) (by simp [PC.idx])
      (ns_of_same (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp) (by simp))
  apply Inv.of_local hI hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro _ _; rfl
  · simp only [Cfg.setLoc_Q]; rw [hI.gQ p]; simp [hp, PC.btw, PC.idx]
  · exact g5_of_same hI rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun s h1 h2 _ => ⟨by simpa using h1, by simpa [Loc.pside, hp, PC.btw, PC.idx] using h2,
        by simp [PC.btw, PC.idx]⟩)
  · intro hs e he
    simp only [Cfg.setLoc_loc, Function.update_self] at hs he ⊢
    have := hI.g7 _ p hs rfl e
    simp [Loc.pside, hp, PC.btw, PC.idx] at he this ⊢
    exact this he
  · simp
  · simp [hp]
  · constructor <;> simp (config := {failIfUnchanged := false}) [PC.btw, PC.idx]
    case l1 =>
      intro h1 h2
      obtain ⟨q, q1, q2, q3, -⟩ := hL.l1 (by rw [hp]; decide) h1 h2
      have hqp : q ≠ p := by rintro rfl; exact q1 rfl
      refine ⟨q, by rw [Function.update_of_ne hqp]; exact q1, by rw [Function.update_of_ne hqp]; exact q2, ?_⟩
      rw [Function.update_of_ne hqp]; exact q3 hp
    case i8 => exact hL.i8 (by rw [hp]; decide)

theorem inv_step_l4 (hI : Inv c) (p : Fin n) (σ : J) (hp : (c.loc p).pc = .l4) :
    Inv (c.step p σ) := by
  have hL := hI.li p
  have hstep : c.step p σ = ({ c with Q := Function.update c.Q p (some ((c.loc p).s, (c.loc p).d,
      (c.loc p).tm)) } : Cfg n J).setLoc p { c.loc p with pc := .l5_1 } := by
    simp [Cfg.step, hp]
  rw [hstep]
  have hLO : LocalOK c (({ c with Q := Function.update c.Q p (some ((c.loc p).s, (c.loc p).d,
      (c.loc p).tm)) } : Cfg n J).setLoc p { c.loc p with pc := .l5_1 }) p :=
    door_localOK (p := p) rfl rfl le_rfl rfl rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hp]; decide) (by simp [PC.idx])
      (ns_of_same (by simp) (by simp [Loc.pside, hp, PC.btw, PC.idx]) (by simp) (by simp))
  apply Inv.of_local hI hLO
  · intro s d; simp [Loc.cnt, hp, PC.btw, PC.idx]
  · intro z hz; exact Function.update_of_ne hz _ _
  · simp [PC.btw, PC.idx]
  · exact g5_of_same hI rfl rfl (fun z hz => Function.update_of_ne hz _ _)
      (fun s h1 h2 _ => ⟨by simpa using h1, by simpa [Loc.pside, hp, PC.btw, PC.idx] using h2,
        by simp [PC.btw, PC.idx]⟩)
  · intro hs e he
    simp only [Cfg.setLoc_loc, Function.update_self] at hs he ⊢
    have := hI.g7 _ p hs rfl e
    simp [Loc.pside, hp, PC.btw, PC.idx] at he this ⊢
    exact this he
  · simp
  · simp [hp]
  · constructor <;> simp (config := {failIfUnchanged := false}) [PC.btw, PC.idx]
    case tm => exact hL.tm (by rw [hp]; decide)
    case l1 =>
      intro h1 h2
      obtain ⟨q, q1, q2, -, q4⟩ := hL.l1 (by rw [hp]; decide) h1 h2
      have hqp : q ≠ p := by rintro rfl; exact q1 rfl
      refine ⟨q, by rw [Function.update_of_ne hqp]; exact q1, by rw [Function.update_of_ne hqp]; exact q2, ?_⟩
      rw [Function.update_of_ne hqp]; exact q4 (by rw [hp]; decide)
    case i8 => exact hL.i8 (by rw [hp]; decide)

end Podc.GroupMutexLogRMR
