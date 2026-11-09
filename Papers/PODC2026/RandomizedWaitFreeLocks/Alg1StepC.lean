import Papers.PODC2026.RandomizedWaitFreeLocks.Alg1StepB

/-!
# Algorithm 1: preservation of the invariant by the write of line 6 and a successful CAS of
line 4 (a promotion)
-/

namespace Podc.RandomizedWaitFreeLocks.Alg1

variable {P D : Type*} [DecidableEq P] [DecidableEq D] (own : D → P)

lemma PC.hap2_of_h24₂ {q : PC} (h : q.h24₂ = true) : q.hap2 = true := by
  cases q <;> (try (rename_i b; cases b)) <;> simp_all [PC.h24₂, PC.hap2]

/-- A descriptor whose owner is at line 6 was never the value of `L` (Lemma 4.3(a)). -/
lemma Inv.eT_wr {c : Cfg P D} (hI : Inv own c) {p : P} {δ : D} (h : (c.loc p).pc = .wr)
    (hd : (c.loc p).dsc = some δ) : c.eT δ = 0 := by
  by_contra he
  rcases hI.o1 δ he with h1 | ⟨h1, h2⟩
  · rw [hI.o3 p δ hd] at h1; cases h1
  · rw [hI.own_dsc p δ hd, h] at h2; simp [PC.hap, PC.post] at h2

/-- Line 6 with a write. -/
lemma inv_wr1 {c : Cfg P D} {p : P} {δ : D} (hI : Inv own c) (h : (c.loc p).pc = .wr)
    (hd : (c.loc p).dsc = some δ) :
    Inv own { (c.tick.upd p { c.loc p with pc := .rdL false, l6 := c.T + 1 }) with
      R := (c.loc p).dsc, lastW := c.T + 1 } := by
  have h1 := inv_wr0 own hI h
  have he := hI.eT_wr own h hd
  have hown := hI.own_dsc p δ hd
  have Lo : ∀ x, x ≠ p → ((c.tick.upd p { c.loc p with pc := .rdL false, l6 := c.T + 1 }).loc x)
      = c.loc x := fun x hx => by simp [hx]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37⟩ := h1
  refine ⟨a1, a2, a3, a4, by simp, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21, ?f5, ?f5', ?f6, ?f7, a26, a27, a28, a29, ?g1, ?g2, ?g3, ?ib, a34, a35, a36, a37⟩
  case f5 => intro δ' h1 h2; simp only [hd] at h1; cases h1; exact absurd he h2
  case f5' => intro h'; simp [hd] at h'
  case f6 =>
    intro x i hx hL hne
    have hxp : x ≠ p := by rintro rfl; simp at hx
    simp only [Lo x hxp] at hx hL hne ⊢
    simp only [upd_L, tick_L] at hL
    intro e
    have : c.L = some δ := by rw [hL, ← e]; exact hd
    exact (hI.f1 δ this).2 he
  case f7 =>
    intro δ' h1 h2; simp only [hd] at h1; cases h1
    simp only [hown, upd_loc, if_pos rfl]
    exact ⟨hd, by simp [PC.hap], rfl⟩
  case g1 =>
    intro x δ' h1 h2 h3 h4
    rcases eq_or_ne x p with rfl | hxp
    · simp [PC.hap]
    · simp only [Lo x hxp] at h3 h4 ⊢
      have := hI.l6_le x h3; simp at h4; omega
  case g2 =>
    intro x δ' h1 h2 h3 h4
    rcases eq_or_ne x p with rfl | hxp
    · simp [PC.hap2] at h3
    · simp only [Lo x hxp] at h3 h4
      have := hI.l6_le x (by revert h3; cases (c.loc x).pc <;> simp [PC.hap2, PC.hap]); simp at h4
      omega
  case g3 =>
    intro x δ' h1 h2 h3 h4
    rcases eq_or_ne x p with rfl | hxp
    · simp [PC.h24₂] at h3
    · simp only [Lo x hxp] at h3 h4
      have := hI.l6_le x (by revert h3; cases (c.loc x).pc <;> simp [PC.h24₂, PC.hap]); simp at h4
      omega
  case ib =>
    intro x i hx hlt
    rcases eq_or_ne x p with rfl | hxp
    · simp at hx
    · simp only [Lo x hxp] at hx hlt ⊢
      have := (hI.rb_bd x i hx).2; omega

/-- A successful non-trivial CAS of line 4 (a promotion of `δ`), before `p` moves on. -/
lemma Inv.change {c : Cfg P D} (hI : Inv own c) {p : P} {i : Bool} {δ : D}
    (h : (c.loc p).pc = .cas i) (hL : c.L = (c.loc p).w) (hne : (c.loc p).d ≠ (c.loc p).w)
    (hδ : (c.loc p).d = some δ) :
    Inv own { c.tick with
      L := (c.loc p).d, lastChg := c.T + 1, eT := Function.update c.eT δ (c.T + 1) } := by
  rw [hδ]
  obtain ⟨δ0, hd0, he, hod, hoh⟩ := hI.f4 p i h hL hne
  rw [hδ] at hd0; cases hd0
  have hT := hI.tick
  have hw_ne : ∀ x, (c.loc x).pc.h24 = true → (c.loc x).w ≠ some δ := by
    intro x hx e; have := (hI.f3 x hx).2; rw [e] at this; exact this he
  have hcas24 : ∀ x j, (c.loc x).pc = .cas j → (c.loc x).pc.h24 = true := by
    intro x j hx; rw [hx]; simp [PC.h24]
  have hdone_L : ∀ ω, c.L = some ω → c.done ω = true := by
    intro ω hω; exact hI.e2 p i ω (Or.inr h) (by rw [← hL, hω])
  have hupd : ∀ ω, ω ≠ δ → Function.update c.eT δ (c.T + 1) ω = c.eT ω :=
    fun ω hω => Function.update_of_ne hω _ _
  have hab := hI.a_bd p (hcas24 p i h)
  have hrb := hI.rb_bd p i h
  refine ⟨hT.idle_iff, hT.own_dsc, hT.act_iff, hT.C_eq, hT.lastW_le, by simp, ?eT_le, hT.l6_le,
    hT.a_bd, hT.rb_bd, hT.fT_bd, ?e1, hT.e2, ?e3, ?e4, ?f1, ?f1', ?f2, ?f3, ?f3c, ?f4, ?f5, ?f5',
    ?f6, ?f7, ?o1, ?o2, hT.o3, hT.o4, ?g1, ?g2, ?g3, hT.ib, ?ij, ?ik, hT.k1, hT.k2⟩
  all_goals dsimp only [Cfg.tick]
  case eT_le =>
    intro ω; by_cases e : ω = δ
    · subst e; simp
    · rw [hupd ω e]; have := hI.eT_le ω; simp; omega
  case e1 =>
    intro x j ω h1 h2; right
    rcases hI.e1 x j ω h1 h2 with h3 | h3
    · exact hdone_L ω h3
    · exact h3
  case e3 =>
    intro x ω h1 h2; right
    rcases hI.e3 x ω h1 h2 with h3 | h3
    · exact hdone_L ω h3
    · exact h3
  case e4 =>
    intro ω h1 h2
    have := hdone_L ω (hI.e4 ω h1 h2)
    rw [this] at h2; cases h2
  case f1 => intro ω h1; cases h1; simp
  case f1' => intro h1; simp at h1
  case f2 =>
    intro ω h1 h2
    have hωδ : ω ≠ δ := by rintro rfl; exact h2 rfl
    simp only [hupd ω hωδ] at h1
    by_cases h3 : c.L = some ω
    · exact hdone_L ω h3
    · exact hI.f2 ω h1 h3
  case f3 =>
    intro x hx
    have h1 := hI.f3 x hx
    have h2 := hw_ne x hx
    rcases hw : (c.loc x).w with _ | ω
    · simp [Cfg.eTo, Cfg.everL, hw] at h1 ⊢; exact h1
    · have : ω ≠ δ := by rintro rfl; exact h2 hw
      simp only [Cfg.eTo, Cfg.everL, hw, hupd ω this] at h1 ⊢; exact h1
  case f3c =>
    intro x hx h1
    have := (hI.a_bd x hx).2; omega
  case f4 =>
    intro x j hx h1; exact absurd h1.symm (hw_ne x (hcas24 x j hx))
  case f5 =>
    intro δ' h1 h2
    by_cases e : δ' = δ
    · subst e; rfl
    · simp only [hupd δ' e] at h2
      have h3 := hI.f5 δ' h1 h2
      exact absurd (by rw [h1, ← h3, hL]) (hI.f6 p i h hL hne)
  case f5' =>
    intro h1
    obtain ⟨-, h2⟩ := hI.f5' h1
    have := hI.ib p i h (by omega)
    rw [hδ, h1] at this; cases this
  case f6 =>
    intro x j hx h1; exact absurd h1.symm (hw_ne x (hcas24 x j hx))
  case f7 =>
    intro δ' h1 h2
    have e : δ' ≠ δ := by rintro rfl; simp at h2
    simp only [hupd δ' e] at h2
    exact hI.f7 δ' h1 h2
  case o1 =>
    intro δ' h1
    by_cases e : δ' = δ
    · subst e; right; exact ⟨hod, by simp [hoh]⟩
    · simp only [hupd δ' e] at h1; exact hI.o1 δ' h1
  case o2 =>
    intro δ' h1 h2 h3
    by_cases e : δ' = δ
    · subst e; rcases h3 with h3 | h3 <;> rw [h3] at hoh <;> simp [PC.hap] at hoh
    · simp only [hupd δ' e] at h1; exact hI.o2 δ' h1 h2 h3
  case g1 =>
    intro x δ' h1 h2
    have e : δ' ≠ δ := by rintro rfl; simp at h2
    simp only [hupd δ' e] at h2
    exact hI.g1 x δ' h1 h2
  case g2 =>
    intros; have := hI.lastW_le; simp; omega
  case g3 =>
    intro x δ' h1 h2 h3 h4
    have e : δ' ≠ δ := by rintro rfl; simp at h2
    simp only [hupd δ' e] at h2
    have hg2 := hI.g2 x δ' h1 h2 (PC.hap2_of_h24₂ h3) h4
    have hfr := hI.L_fresh own
    have hf3 := (hI.f3 p (hcas24 p i h)).1
    rw [← hL] at hf3
    have := hI.ib p i h (by omega)
    rw [hδ, h1] at this; cases this; exact absurd rfl e
  case ij =>
    intro x j δ' hx h1; exact absurd h1.symm (hw_ne x (hcas24 x j hx))
  case ik =>
    intro x j δ' hx h1; exact absurd h1.symm (hw_ne x (hcas24 x j hx))

end Podc.RandomizedWaitFreeLocks.Alg1

namespace Podc.RandomizedWaitFreeLocks.Alg1

variable {P D : Type*} [DecidableEq P] [DecidableEq D] (own : D → P)

/-- The invariant is preserved by every step. -/
lemma inv_step {c : Cfg P D} (hI : Inv own c) (a : Act P D) (b : Bool) :
    Inv own (step own c a b).1 := by
  cases a with
  | invoke p δ =>
    simp only [step]
    split_ifs with hg
    · exact inv_invoke own hI hg.1 hg.2.1 hg.2.2
    · exact hI.tick
  | sched p =>
    cases hq : (c.loc p).pc with
    | idle => simp only [step, hq]; exact hI.tick
    | wr =>
      cases b
      · simp only [step, hq]; exact inv_wr0 own hI hq
      · obtain ⟨δ, hd⟩ : ∃ δ, (c.loc p).dsc = some δ := by
          cases h' : (c.loc p).dsc with
          | none => exact absurd ((hI.idle_iff p).2 h') (by rw [hq]; simp)
          | some δ => exact ⟨δ, rfl⟩
        simp only [step, hq, if_true]; exact inv_wr1 own hI hq hd
    | rdL i => simp only [step, hq]; exact inv_rdL own hI hq
    | exS i =>
      simp only [step, hq]
      split
      · rename_i hw; exact (inv_exS_frame own hI hq).setStarted own _ (hI.e1 p i _ (Or.inl hq) hw)
      · rename_i hw; exact inv_exS_none own hI hq hw
    | exE i =>
      simp only [step, hq]
      split
      · rename_i ω hw; exact inv_exE_frame own (hI.setDone own ω) (ω := ω) hq hw (by simp)
      · rename_i hw; exact inv_exE_none own hI hq hw
    | rdR i => simp only [step, hq]; exact inv_rdR own hI hq
    | cas i =>
      by_cases hok : c.L = (c.loc p).w ∧ (c.loc p).d ≠ (c.loc p).w
      · obtain ⟨δ, hδ, -⟩ := hI.f4 p i hq hok.1 hok.2
        have h2 := hI.change own hq hok.1 hok.2 hδ
        cases i
        · simp only [step, hq, if_pos hok, Bool.false_eq_true, if_false]
          split
          · rename_i δ' hδ'; rw [hδ] at hδ'; cases hδ'
            exact inv_cas0_fail' own h2 hq (fun h => h.2 h.1)
          · rename_i hδ'; rw [hδ] at hδ'; cases hδ'
        · simp only [step, hq, if_pos hok, if_true]
          split
          · rename_i δ' hδ'; rw [hδ] at hδ'; cases hδ'
            exact inv_cas1_fail' own h2 hq (fun h => h.2 h.1)
          · rename_i hδ'; rw [hδ] at hδ'; cases hδ'
      · cases i
        · simp only [step, hq, if_neg hok]; exact inv_cas0_fail own hI hq hok
        · simp only [step, hq, if_neg hok]; exact inv_cas1_fail own hI hq hok
    | rd8 =>
      by_cases hL : c.L = (c.loc p).dsc
      · simp only [step, hq, if_pos hL]; exact inv_rd8_yes own hI hq hL
      · simp only [step, hq, if_neg hL]; exact inv_rd8_no own hI hq hL
    | exS8 =>
      simp only [step, hq]
      split
      · rename_i δ hd; exact (inv_exS8_frame own hI hq).setStarted own δ (hI.e3 p δ (Or.inl hq) hd)
      · exact hI.tick
    | exE8 =>
      simp only [step, hq]
      split
      · rename_i δ hd; exact inv_exE8_frame own (hI.setDone own δ) (δ := δ) hq hd (by simp)
      · exact hI.tick
    | fad => simp only [step, hq]; exact inv_fad own hI hq
    | ret =>
      simp only [step, hq]
      split
      · rename_i δ hd
        split_ifs with hdn
        · exact inv_ret own hI hq hd _ _ (by rw [if_pos hdn]; try rfl)
        · exact inv_ret own hI hq hd _ _ (by rw [if_neg hdn]; try rfl)
      · exact hI.tick

/-- The invariant holds in every reachable configuration. -/
theorem inv_reach {c : Cfg P D} (h : Reach own c) : Inv own c :=
  Reachable.induction (init := init) (step := step own) (inv_init own)
    (fun c a b _ hI => inv_step own hI a b) h

end Podc.RandomizedWaitFreeLocks.Alg1
