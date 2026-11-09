import Papers.PODC2010.GroupMutexLogRMR.Inv

/-!
# Lemmas for the preservation proof of `Inv`
-/

namespace Podc.GroupMutexLogRMR

/-- Arithmetic on program-counter positions. -/
macro "btw_omega" : tactic => `(tactic| (simp only [PC.btw, PC.idx] at *; omega))

variable {n : ℕ} {J : Type} [DecidableEq J]

namespace Cfg

variable (c : Cfg n J) (p : Fin n)

@[simp] theorem setLoc_S (l : Loc J) : (c.setLoc p l).S = c.S := rfl
@[simp] theorem setLoc_Ex (l : Loc J) : (c.setLoc p l).Ex = c.Ex := rfl
@[simp] theorem setLoc_G (l : Loc J) : (c.setLoc p l).G = c.G := rfl
@[simp] theorem setLoc_In (l : Loc J) : (c.setLoc p l).In = c.In := rfl
@[simp] theorem setLoc_Out (l : Loc J) : (c.setLoc p l).Out = c.Out := rfl
@[simp] theorem setLoc_Exclear (l : Loc J) : (c.setLoc p l).Exclear = c.Exclear := rfl
@[simp] theorem setLoc_C (l : Loc J) : (c.setLoc p l).C = c.C := rfl
@[simp] theorem setLoc_Q (l : Loc J) : (c.setLoc p l).Q = c.Q := rfl
@[simp] theorem setLoc_linkS (l : Loc J) : (c.setLoc p l).linkS = c.linkS := rfl
@[simp] theorem setLoc_linkEx (l : Loc J) : (c.setLoc p l).linkEx = c.linkEx := rfl
@[simp] theorem setLoc_loc (l : Loc J) : (c.setLoc p l).loc = Function.update c.loc p l := rfl

@[simp] theorem go_eq (pc : PC) : c.go p pc = c.setLoc p { c.loc p with pc := pc } := rfl

@[simp] theorem incC_C (s : J) (d : Bool) :
    (c.incC s d).C = Function.update c.C s (Function.update (c.C s) d (c.C s d + 1)) := rfl
@[simp] theorem decC_C (s : J) (d : Bool) :
    (c.decC s d).C = Function.update c.C s (Function.update (c.C s) d (c.C s d - 1)) := rfl
@[simp] theorem llS_linkS : (c.llS p).linkS = Function.update c.linkS p true := rfl
@[simp] theorem llEx_linkEx : (c.llEx p).linkEx = Function.update c.linkEx p true := rfl
@[simp] theorem scS_S (v : J × Bool × J) : (c.scS v).S = v := rfl
@[simp] theorem scS_linkS (v : J × Bool × J) : (c.scS v).linkS = fun _ => false := rfl
@[simp] theorem scEx_Ex (v : Option J) : (c.scEx v).Ex = v := rfl
@[simp] theorem scEx_linkEx (v : Option J) : (c.scEx v).linkEx = fun _ => false := rfl
@[simp] theorem setOut_Out (s : J) (d : Bool) : (c.setOut s d).Out = Function.update c.Out s d := rfl
@[simp] theorem setExclear_Exclear (s : J) (v : Bool) :
    (c.setExclear s v).Exclear = Function.update c.Exclear s v := rfl

end Cfg

section Lemmas

variable {c : Cfg n J}

theorem Inv.q_of_btw (hI : Inv c) {z : Fin n} (h : PC.btw .l5_1 .l13 (c.loc z).pc) :
    c.Q z = some ((c.loc z).s, (c.loc z).d, (c.loc z).tm) := by
  rw [hI.gQ z, if_pos h]

theorem Inv.q_eq_some (hI : Inv c) {z : Fin n} {e : J × Bool × ℕ} (h : c.Q z = some e) :
    PC.btw .l5_1 .l13 (c.loc z).pc ∧ e = ((c.loc z).s, (c.loc z).d, (c.loc z).tm) := by
  rw [hI.gQ z] at h
  split_ifs at h with hb
  · exact ⟨hb, (Option.some.inj h).symm⟩

/-- `pside` in the queue range. -/
theorem Loc.pside_of_btw {l : Loc J} (h : PC.btw .l2 .l16_6 l.pc) : l.pside = some l.d := by
  unfold Loc.pside
  rw [if_neg, if_pos]
  · exact ⟨le_trans (by decide) h.1, h.2⟩
  · intro h'; rw [h'] at h; exact absurd h.1 (by decide)

/-- A process of a side contributes to the counter of that side. -/
theorem Loc.cnt_of_pside {l : Loc J} {e : Bool} (h : l.pside = some e) : l.cnt l.s e = 1 := by
  unfold Loc.pside at h
  unfold Loc.cnt
  rw [if_pos rfl]
  by_cases h6 : l.pc = .l1_6
  · rw [if_neg (by rw [h6]; decide), if_pos (by rw [h6]; decide)]
  · rw [if_neg h6] at h
    split_ifs at h with hb
    cases h
    by_cases h2 : l.pc = .l1_2
    · rw [h2] at hb; exact absurd hb.1 (by decide)
    · rw [if_neg h2]
      by_cases h3 : PC.btw .l1_3 .l1_7 l.pc
      · rw [if_pos h3]
      · rw [if_neg h3, if_pos]
        refine ⟨?_, rfl⟩
        have : l.pc.idx ≠ 6 := by
          intro h6'
          apply h6
          cases hpc : l.pc <;> simp_all [PC.idx]
        btw_omega

theorem Inv.C_ne_zero_of_pside (hI : Inv c) {z : Fin n} {e : Bool} (h : (c.loc z).pside = some e) :
    c.C (c.loc z).s e ≠ 0 :=
  C_pos_of_cnt hI z (by rw [Loc.cnt_of_pside h]; decide)

/-- **Lemma 1 consequence**: when `S` is of session `s`, a minimal element of `Q` of session `s`
has the side of `S`. -/
theorem Inv.minQ_side (hI : Inv c) {s : J} {d : Bool} (hm : minQ c.Q = some (s, d))
    (hs : c.S.1 = s) : c.S.2.1 = d := by
  obtain ⟨r, t, hr, hmin⟩ := minQ_eq_some hm
  obtain ⟨hb, he⟩ := hI.q_eq_some hr
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  by_contra hne
  have hSd : c.S.2.1 = !(c.loc r).d := by
    cases h1 : c.S.2.1 <;> cases h2 : (c.loc r).d <;> simp_all
  by_cases h9 : PC.btw .l9 .l13 (c.loc r).pc
  · exact hne ((hI.li r).i5 ⟨h9.1, le_trans h9.2 (by decide)⟩).2.1
  · have h8 : PC.btw .l1_7 .l8 (c.loc r).pc := by btw_omega
    obtain ⟨q, -, hq, -, hlt⟩ := (hI.li r).l1 h8 hs hSd
    have hq' := hI.q_of_btw (z := q) ⟨hq.1, le_trans hq.2 (by decide)⟩
    have := hmin q _ _ _ hq'
    have := hlt (by btw_omega)
    omega

/-- With no process of `S`'s side, `Min(Q)` is not of `S`'s session. -/
theorem Inv.minQ_ne_sess (hI : Inv c) (hns : NoSide c c.S.1 c.S.2.1) {s : J} {d : Bool}
    (hm : minQ c.Q = some (s, d)) : s ≠ c.S.1 := by
  intro hs
  have hd := hI.minQ_side hm hs.symm
  obtain ⟨r, t, hr, -⟩ := minQ_eq_some hm
  obtain ⟨hb, he⟩ := hI.q_eq_some hr
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have := (hns r hs).2.2
  rw [Loc.pside_of_btw ⟨le_trans (by decide) hb.1, le_trans hb.2 (by decide)⟩, hd] at this
  exact this rfl

theorem Inv.minQ_ne_none (hI : Inv c) {z : Fin n} (h : PC.btw .l5_1 .l13 (c.loc z).pc) :
    minQ c.Q ≠ none := by
  intro h0
  rw [minQ_eq_none] at h0
  have := h0 z
  rw [hI.q_of_btw h] at this
  exact Option.some_ne_none _ this

/-- `In[S.1] ≠ S.2.1` when nobody is of `S`'s side. -/
theorem Inv.in_ne_of_noSide (hI : Inv c) (hns : NoSide c c.S.1 c.S.2.1) : c.In c.S.1 ≠ c.S.2.1 := by
  intro h
  obtain ⟨y, h1, h2, -⟩ := hI.g5 c.S.1 rfl h
  exact (hns y h1).2.2 h2

end Lemmas

end Podc.GroupMutexLogRMR
