import Papers.PODC2026.RandomizedWaitFreeLocks.Alg1Frame

/-!
# Algorithm 1: preservation of the invariant by local steps (lines 1, 3, 4 (failing), 6, 8)
-/

namespace Podc.RandomizedWaitFreeLocks.Alg1

variable {P D : Type*} [DecidableEq P] [DecidableEq D] (own : D → P)

lemma Inv.L_fresh {c : Cfg P D} (hI : Inv own c) : c.eTo c.L = c.lastChg ∧ c.everL c.L := by
  cases hL : c.L with
  | none => simp [hI.f1' hL]
  | some ω => simpa using hI.f1 ω hL

macro "pcsimp" : tactic => `(tactic| simp_all [PC.inAct, PC.hap, PC.post, PC.h24, PC.hap2,
  PC.h24₂, PC.isCas])

macro "pcs" : tactic => `(tactic| (simp only [PC.inAct, PC.hap, PC.post, PC.h24, PC.hap2,
  PC.h24₂, PC.isCas, Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, Bool.or_self, reduceCtorEq, PC.exS.injEq, PC.exE.injEq, PC.rdR.injEq,
  PC.cas.injEq, PC.rdL.injEq, false_or, or_false, IsEmpty.forall_iff, forall_const, Bool.false_eq_true,
  imp_false, not_true, false_imp_iff, true_and, and_true, tick_L, tick_R, tick_C, tick_done, tick_T,
  tick_lastW, tick_lastChg, tick_eT, tick_started, tick_act, tick_retT, tick_failed, tick_loc,
  eTo_tick, everL_tick, le_refl] at *))

lemma inv_rdL {c : Cfg P D} {p : P} {i : Bool} (hI : Inv own c) (h : (c.loc p).pc = .rdL i) :
    Inv own (c.tick.upd p { c.loc p with pc := .exS i, w := c.L, a := c.T + 1 }) := by
  have hl6 := hI.l6_le p (by simp [h, PC.hap])
  refine hI.tick.frame own { c.loc p with pc := .exS i, w := c.L, a := c.T + 1 } rfl rfl rfl
    (by simp [h]) (by simp [h, PC.inAct]) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (intros; try pcsimp)
  case refine_1 => omega
  case refine_7 => have h1 := hI.L_fresh; have := hI.lastChg_le; exact ⟨by omega, h1.2⟩
  case refine_12 δ h1 h2 h3 _ => rw [← h3]; exact (hI.f7 δ h1 h2).2.2
  case refine_16 δ h1 h2 h3 h4 =>
    cases i
    · simp at h3
    · exact hI.g2 p δ h1 h2 (by simp [h, PC.hap2]) h4

lemma inv_wr0 {c : Cfg P D} {p : P} (hI : Inv own c) (h : (c.loc p).pc = .wr) :
    Inv own (c.tick.upd p { c.loc p with pc := .rdL false, l6 := c.T + 1 }) := by
  refine hI.tick.frame own { c.loc p with pc := .rdL false, l6 := c.T + 1 } rfl rfl rfl
    (by simp [h]) (by simp [h, PC.inAct]) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (intros; try pcs)
  case refine_12 δ h1 h2 h3 _ =>
    have := (hI.f7 δ h1 h2).2.1; rw [h3, h] at this; simp [PC.hap] at this

lemma Inv.R_fresh {c : Cfg P D} (hI : Inv own c) {δ : D} (hR : c.R = some δ)
    (hL : c.L ≠ some δ) : c.eT δ = 0 := by
  by_contra h; exact hL (hI.f5 δ hR h)

lemma inv_rdR {c : Cfg P D} {p : P} (hI : Inv own c) {i : Bool} (h : (c.loc p).pc = .rdR i) :
    Inv own (c.tick.upd p { c.loc p with pc := .cas i, d := c.R, rb := c.T + 1 }) := by
  have ha := hI.a_bd p (by cases i <;> simp [h, PC.h24])
  have hl6 := hI.l6_le p (by cases i <;> simp [h, PC.hap])
  have hf3 := hI.f3 p (by cases i <;> simp [h, PC.h24])
  have hf3c := hI.f3c p (by cases i <;> simp [h, PC.h24])
  refine hI.tick.frame own { c.loc p with pc := .cas i, d := c.R, rb := c.T + 1 } rfl rfl rfl
    (by simp [h]) (by simp [h, PC.inAct]) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (intros; try pcs)
  case refine_1 => omega
  case refine_2 => omega
  case refine_3 => omega
  case refine_5 ω hw _ => exact hI.e2 p i ω (Or.inl h) hw
  case refine_7 => exact hf3
  case refine_8 h1 _ => exact hf3c h1
  case refine_9 hL hR _ =>
    cases hRc : c.R with
    | none => exact absurd (by rw [hRc, ← (hI.f5' hRc).1, hL]) hR
    | some δ =>
      have he : c.eT δ = 0 := hI.R_fresh own hRc (by rw [hL]; rw [hRc] at hR; exact Ne.symm hR)
      obtain ⟨h1, h2, h3⟩ := hI.f7 δ hRc he
      refine ⟨δ, rfl, he, ?_, ?_⟩ <;> split_ifs with ho
      · simp only; rw [← ho]; exact h1
      · exact h1
      · simp [PC.hap]
      · exact h2
  case refine_11 h1 h2 _ => exact h2
  case refine_12 δ h1 h2 h3 _ => rw [← h3]; exact (hI.f7 δ h1 h2).2.2
  case refine_16 δ h1 h2 h3 h4 =>
    cases i
    · simp at h3
    · exact hI.g2 p δ h1 h2 (by simp [h, PC.hap2]) h4
  case refine_17 δ h1 h2 h3 h4 =>
    cases i
    · simp at h3
    · exact hI.g3 p δ h1 h2 (by simp [h, PC.h24₂]) h4
  case refine_19 δ hL hR hne hc hLy _ =>
    split_ifs at hc hLy ⊢ with ho
    · simpa [hR] using hne
    · have he : c.eT δ = 0 := hI.R_fresh own hR (by rw [hL]; rw [hR] at hne; exact Ne.symm hne)
      obtain ⟨h1, h2, h3⟩ := hI.f7 δ hR he
      have hcas : ∃ j, (c.loc (own δ)).pc = .cas j := by
        revert hc; cases (c.loc (own δ)).pc <;> simp [PC.isCas]
      obtain ⟨j, hj⟩ := hcas
      have hrb := hI.rb_bd _ j hj
      have hab := hI.a_bd (own δ) (by simp [hj, PC.h24])
      have hd := hI.ib _ j hj (by omega)
      rw [hd, hR]
      intro heq
      have := (hI.f1 δ (by rw [hLy, ← heq])).2
      exact this he
  case refine_20 x j δ hx hxc hLx hdx hne ho hLp _ =>
    have := hI.f6 x j hxc hLx hne
    rwa [← hLx, hLp] at this
  case refine_21 δ hL hR hne hc _ =>
    split_ifs at hc ⊢ with ho
    · exact hL
    · have he : c.eT δ = 0 := hI.R_fresh own hR (by rw [hL]; rw [hR] at hne; exact Ne.symm hne)
      obtain ⟨h1, h2, h3⟩ := hI.f7 δ hR he
      exact hI.g3 (own δ) δ hR he hc (by omega)
  case refine_22 x j δ hx hxc hLx hdx hne ho hc =>
    cases i
    · simp at hc
    · have := hI.ik x j δ hxc hLx hdx hne (by rw [ho]; simp [h, PC.h24₂])
      rwa [ho] at this

lemma Inv.cas_ok {c : Cfg P D} (hI : Inv own c) {p : P} {i : Bool} (h : (c.loc p).pc = .cas i)
    (hL : c.L = (c.loc p).w) {δ : D} (hR : c.R = some δ) (he : c.eT δ = 0)
    (hW : c.lastW < (c.loc p).rb) : (c.loc p).d ≠ (c.loc p).w := by
  rw [hI.ib p i h hW, hR, ← hL]
  intro h'; exact (hI.f1 δ h'.symm).2 he

lemma inv_cas0_fail' {c : Cfg P D} {p : P} (hI : Inv own c) (h : (c.loc p).pc = .cas false) (hf : ¬ (c.L = (c.loc p).w ∧ (c.loc p).d ≠ (c.loc p).w)) :
    Inv own (c.upd p { c.loc p with pc := .rdL true }) := by
  refine hI.frame own { c.loc p with pc := .rdL true } rfl rfl rfl
    (by simp [h]) (by simp [h, PC.inAct]) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (intros; try pcs)
  case refine_1 => have := hI.l6_le p (by simp [h, PC.hap]); omega
  case refine_12 δ h1 h2 h3 _ => rw [← h3]; exact (hI.f7 δ h1 h2).2.2
  case refine_16 δ h1 h2 h3 _ =>
    have ha := hI.a_bd p (by simp [h, PC.h24])
    have hrb := hI.rb_bd p false h
    by_cases hL : c.L = (c.loc p).w
    · have hd : (c.loc p).d = (c.loc p).w := by by_contra hne; exact hf ⟨hL, hne⟩
      have hdR := hI.ib p false h (by omega)
      have : c.L = some δ := by rw [hL, ← hd, hdR, h1]
      exact absurd (hI.f1 δ this).2 (by simpa using h2)
    · have := hI.f3c p (by simp [h, PC.h24])
      by_contra hlt
      exact hL (this (by omega))


lemma inv_cas0_fail {c : Cfg P D} {p : P} (hI : Inv own c) (h : (c.loc p).pc = .cas false)
    (hf : ¬ (c.L = (c.loc p).w ∧ (c.loc p).d ≠ (c.loc p).w)) :
    Inv own (c.tick.upd p { c.loc p with pc := .rdL true }) :=
  inv_cas0_fail' own hI.tick h hf

lemma inv_cas1_fail' {c : Cfg P D} {p : P} (hI : Inv own c) (h : (c.loc p).pc = .cas true) (hf : ¬ (c.L = (c.loc p).w ∧ (c.loc p).d ≠ (c.loc p).w)) :
    Inv own (c.upd p { c.loc p with pc := .rd8 }) := by
  refine hI.frame own { c.loc p with pc := .rd8 } rfl rfl rfl
    (by simp [h]) (by simp [h, PC.inAct]) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (intros; try pcs)
  case refine_1 => have := hI.l6_le p (by simp [h, PC.hap]); omega
  case refine_10 x j δ hx hxc hLx hdx hne he ho =>
    have hLp := hI.ik x j δ hxc hLx hdx hne (by rw [ho]; simp [h, PC.h24₂])
    rw [ho] at hLp
    have := hI.ij x j δ hxc hLx hdx hne (by rw [ho]; simp [h, PC.isCas]) (by rw [ho]; exact hLp)
    rw [ho] at this
    exact absurd ⟨hLp, this⟩ hf
  case refine_12 δ hR he ho hd =>
    obtain ⟨-, -, h3⟩ := hI.f7 δ hR he
    rw [ho] at h3
    have ha := hI.a_bd p (by simp [h, PC.h24])
    have hrb := hI.rb_bd p true h
    have hLp := hI.g3 p δ hR he (by simp [h, PC.h24₂]) (by omega)
    exact absurd ⟨hLp, hI.cas_ok own h hLp hR he (by omega)⟩ hf
  case refine_15 δ hR he _ _ =>
    have hle : c.lastW ≤ (c.loc p).l6 := by assumption
    have ha := hI.a_bd p (by simp [h, PC.h24])
    have hrb := hI.rb_bd p true h
    have hLp := hI.g3 p δ hR he (by simp [h, PC.h24₂]) hle
    exact absurd ⟨hLp, hI.cas_ok own h hLp hR he (by omega)⟩ hf


lemma inv_cas1_fail {c : Cfg P D} {p : P} (hI : Inv own c) (h : (c.loc p).pc = .cas true)
    (hf : ¬ (c.L = (c.loc p).w ∧ (c.loc p).d ≠ (c.loc p).w)) :
    Inv own (c.tick.upd p { c.loc p with pc := .rd8 }) :=
  inv_cas1_fail' own hI.tick h hf

lemma Inv.f4_owner {c : Cfg P D} (hI : Inv own c) {x : P} {i : Bool} {δ : D}
    (h1 : (c.loc x).pc = .cas i) (h2 : c.L = (c.loc x).w) (h3 : (c.loc x).d = some δ)
    (h4 : (c.loc x).d ≠ (c.loc x).w) : (c.loc (own δ)).pc.hap = true := by
  obtain ⟨δ', h5, -, -, h6⟩ := hI.f4 x i h1 h2 h4
  rw [h3] at h5; cases h5; exact h6

lemma Inv.f7_hap {c : Cfg P D} (hI : Inv own c) {δ : D} (hR : c.R = some δ) (he : c.eT δ = 0) :
    (c.loc (own δ)).pc.hap = true := (hI.f7 δ hR he).2.1

set_option hygiene false in
/-- Finishing tactic for the obligations of `Inv.frame` at a step of `p` (`h` : old pc). -/
macro "fin" : tactic => `(tactic| first
  | omega
  | assumption
  | (simp [h, PC.inAct]; done)
  | (have := hI.l6_le p (by simp [h, PC.hap, PC.post]); omega)
  | (have := hI.a_bd p (by simp [h, PC.h24]); omega)
  | exact hI.f3 p (by simp [h, PC.h24])
  | exact hI.f3c p (by simp [h, PC.h24]) ‹_›
  | exact hI.e1 p _ _ (Or.inl h) ‹_›
  | exact hI.e3 p _ (Or.inl h) ‹_›
  | (rw [← ‹own _ = p›]; exact (hI.f7 _ ‹c.R = some _› ‹c.eT _ = 0›).2.2)
  | exact hI.g2 p _ ‹c.R = some _› ‹c.eT _ = 0› (by simp [h, PC.hap2]) ‹c.lastW ≤ _›
  | exact hI.g3 p _ ‹c.R = some _› ‹c.eT _ = 0› (by simp [h, PC.h24₂]) ‹c.lastW ≤ _›
  | (have := hI.ik _ _ _ ‹(c.loc _).pc = .cas _› ‹c.L = (c.loc _).w› ‹(c.loc _).d = some _›
        ‹(c.loc _).d ≠ (c.loc _).w› (by rw [‹own _ = p›]; simp [h, PC.h24₂])
     rwa [‹own _ = p›] at this)
  | exact absurd (hI.f4_owner own ‹(c.loc _).pc = .cas _› ‹c.L = (c.loc _).w›
        ‹(c.loc _).d = some _› ‹(c.loc _).d ≠ (c.loc _).w›) (by rw [‹own _ = p›, h]; simp [PC.hap])
  | exact absurd (hI.f7_hap own ‹c.R = some _› ‹c.eT _ = 0›) (by rw [‹own _ = p›, h]; simp [PC.hap])
  | (have := hI.g1 p _ ‹c.R = some _› ‹c.eT _ = 0› (by simp [h, PC.hap, PC.post]) ‹c.lastW ≤ _›
     simp [h, PC.hap] at this)
  | (exfalso; have := hw.symm.trans ‹(c.loc p).w = some _›; simp at this; done)
  | (have e := hw.symm.trans ‹(c.loc p).w = some _›; cases e; exact hd)
  | (have e := hw.symm.trans ‹(c.loc p).dsc = some _›; cases e; exact hd)
  | (left; exact hL.trans ‹(c.loc p).dsc = some _›)
  | exact hI.f2 _ ‹c.eT _ ≠ 0› (fun e => hL (e.trans ‹(c.loc p).dsc = some _›.symm)))

lemma inv_rd8_yes {c : Cfg P D} {p : P} (hI : Inv own c) (h : (c.loc p).pc = .rd8) (hL : c.L = (c.loc p).dsc) :
    Inv own (c.tick.upd p { c.loc p with pc := .exS8 }) := by
  refine hI.tick.frame own { c.loc p with pc := .exS8 } rfl rfl rfl
    (by simp [h]) (by simp [h, PC.inAct]) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (intros; try pcs)
  all_goals (try fin)

lemma inv_rd8_no {c : Cfg P D} {p : P} (hI : Inv own c) (h : (c.loc p).pc = .rd8) (hL : c.L ≠ (c.loc p).dsc) :
    Inv own (c.tick.upd p { c.loc p with pc := .fad }) := by
  refine hI.tick.frame own { c.loc p with pc := .fad } rfl rfl rfl
    (by simp [h]) (by simp [h, PC.inAct]) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (intros; try pcs)
  all_goals (try fin)

lemma inv_exS_none {c : Cfg P D} {p : P} (hI : Inv own c) {i : Bool} (h : (c.loc p).pc = .exS i) (hw : (c.loc p).w = none) :
    Inv own (c.tick.upd p { c.loc p with pc := .exE i }) := by
  cases i <;>
  · refine hI.tick.frame own _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (try rfl)
    all_goals (intros; try pcs)
    all_goals (try fin)

lemma inv_exE_none {c : Cfg P D} {p : P} (hI : Inv own c) {i : Bool} (h : (c.loc p).pc = .exE i) (hw : (c.loc p).w = none) :
    Inv own (c.tick.upd p { c.loc p with pc := .rdR i }) := by
  cases i <;>
  · refine hI.tick.frame own _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (try rfl)
    all_goals (intros; try pcs)
    all_goals (try fin)

lemma inv_exS_frame {c : Cfg P D} {p : P} (hI : Inv own c) {i : Bool} (h : (c.loc p).pc = .exS i) :
    Inv own (c.tick.upd p { c.loc p with pc := .exE i }) := by
  cases i <;>
  · refine hI.tick.frame own _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (try rfl)
    all_goals (intros; try pcs)
    all_goals (try fin)

lemma inv_exE_frame {c : Cfg P D} {p : P} (hI : Inv own c) {i ω} (h : (c.loc p).pc = .exE i) (hw : (c.loc p).w = some ω) (hd : c.done ω = true) :
    Inv own (c.tick.upd p { c.loc p with pc := .rdR i }) := by
  cases i <;>
  · refine hI.tick.frame own _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (try rfl)
    all_goals (intros; try pcs)
    all_goals (try fin)

lemma inv_exS8_frame {c : Cfg P D} {p : P} (hI : Inv own c) (h : (c.loc p).pc = .exS8) :
    Inv own (c.tick.upd p { c.loc p with pc := .exE8 }) := by
  refine hI.tick.frame own { c.loc p with pc := .exE8 } rfl rfl rfl
    (by simp [h]) (by simp [h, PC.inAct]) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (intros; try pcs)
  all_goals (try fin)

lemma inv_exE8_frame {c : Cfg P D} {p : P} (hI : Inv own c) {δ} (h : (c.loc p).pc = .exE8) (hw : (c.loc p).dsc = some δ) (hd : c.done δ = true) :
    Inv own (c.tick.upd p { c.loc p with pc := .fad }) := by
  refine hI.tick.frame own { c.loc p with pc := .fad } rfl rfl rfl
    (by simp [h]) (by simp [h, PC.inAct]) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (intros; try pcs)
  all_goals (try fin)

end Podc.RandomizedWaitFreeLocks.Alg1
