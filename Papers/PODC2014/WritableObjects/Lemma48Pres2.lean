import Papers.PODC2014.WritableObjects.Lemma48Pres1

/-!
# Lemma 4.8, part 7: preservation of the hint invariants
-/

namespace Podc.WritableObjects.WF

open Cslib.SharedMemory

variable {n : ℕ} {T : ObjSpec} [NeZero n] {W : Writable T} {c c' : Cfg n T}

lemma nr_w (l : Loc n T) (h : stage l.pc = 3) (o : Fin 4) (ho : o ≠ 0) :
    l.nr o (cq l.ctr) = 4 * (l.ctr + n) + o := by
  unfold Loc.nr Loc.U
  have : max o.val 1 ≤ 3 := by have := o.isLt; omega
  rw [h, if_pos this, nextR_succ_of_eq (cq l.ctr).isLt rfl]
  omega

lemma Step.m_mono (hs : Step W c c') : ∀ q, (c.loc q).m ≤ (c'.loc q).m := by
  intro q
  cases hs <;> (simp only [Function.update_apply]; split_ifs <;> simp_all)

lemma Step.ctr_mono (hs : Step W c c') : ∀ q, (c.loc q).ctr ≤ (c'.loc q).ctr := by
  intro q
  cases hs <;> (simp only [Function.update_apply]; split_ifs <;> simp_all)

theorem Inv.hint_step (hI : Inv W c) (hs : Step W c c') : ∀ p q h, c'.hH p q = some h →
    h.f.1 = p ∧ (c'.loc p).SlotProt h.f 2 q ∧ (c'.loc p).lc h.f = h.w ∧ h.s = Sval n h.m14 ∧
    h.m14 ≤ h.m18 ∧ h.m18 ≤ (c'.loc q).m ∧
    (h.w < (c'.loc p).ctr ∨
      (h.w = (c'.loc p).ctr ∧ isW1921 (c'.loc p).pc ∧ cq (c'.loc p).ctr = q)) := by
  intro p' q' h' hh
  have hm := hs.m_mono
  cases hs
  case l18 p v f s m14 olds olds' hpc =>
    by_cases hnew : p' = p ∧ q' = cq (c.loc p).ctr
    · obtain ⟨rfl, rfl⟩ := hnew
      simp only [Function.update_self, Option.some.injEq] at hh; subst hh
      obtain ⟨h1, h2, h3⟩ := hI.chosen p' f (by simp [hpc, curF])
      have hl := (hI.locRd p').1 s m14 (by simp [hpc, smOf])
      refine ⟨h1, ?_, by simpa using h3, hl.1, hl.2, hm _, Or.inr ⟨by simp, by simp [isW1921], by simp⟩⟩
      simp only [Function.update_self]
      unfold Loc.SlotProt
      refine Loc.Prot.congr (h2.mono ?_) rfl (Loc.U_congr rfl (by simp [stage, hpc]))
      rw [nr_w _ (by simp [stage]) 2 (by decide)]; simp; omega
    · have hh' : c.hH p' q' = some h' := by
        by_cases hp : p' = p
        · subst hp
          have hq : q' ≠ cq (c.loc p').ctr := fun hq => hnew ⟨rfl, hq⟩
          simpa [Function.update_of_ne hq] using hh
        · simpa [Function.update_of_ne hp] using hh
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI.hint p' q' h' hh'
      refine ⟨h1, ?_, ?_, h4, h5, le_trans h6 (hm q'), ?_⟩
      all_goals simp only [Function.update_apply]; split_ifs with hp
      · subst hp; exact h2.congr rfl (Loc.U_congr rfl (by simp [stage, hpc]))
      · exact h2
      · subst hp; simpa using h3
      · exact h3
      · subst hp; rcases h7 with h7 | h7
        · exact Or.inl h7
        · simp [hpc, isW1921] at h7
      · exact h7
  case l44 q x r hpc =>
    have hh' : c.hH p' q' = some h' := by
      by_cases hp : p' = cq x
      · subst hp
        by_cases hq : q' = q
        · subst hq; simp at hh
        · simpa [Function.update_of_ne hq] using hh
      · simpa [Function.update_of_ne hp] using hh
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI.hint p' q' h' hh'
    refine ⟨h1, ?_, ?_, h4, h5, le_trans h6 (hm q'), ?_⟩
    all_goals simp only [Function.update_apply]; split_ifs with hp
    · subst hp; exact h2.congr rfl (Loc.U_congr rfl (by simp [stage, hpc]))
    · exact h2
    · subst hp; simpa using h3
    · exact h3
    · subst hp; simpa [hpc, isW1921] using h7
    · exact h7
  case rec27 p v f hpc hf =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI.hint p' q' h' hh
    refine ⟨h1, ?_, ?_, h4, h5, le_trans h6 (hm q'), ?_⟩
    all_goals simp only [Function.update_apply]; split_ifs with hp
    · subst hp; subst h1
      exact Loc.r27_slot hpc (hI.qok _) (by decide) h2 rfl (fun h => absurd h (by decide))
    · exact h2
    · subst hp
      have hne : h'.f ≠ f := fun e => h2.1 (e ▸ hf)
      simpa [Function.update_of_ne hne] using h3
    · exact h3
    · subst hp; simpa [hpc, isW1921] using h7
    · exact h7
  case rec29 p v f hpc =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI.hint p' q' h' hh
    refine ⟨h1, ?_, ?_, h4, h5, le_trans h6 (hm q'), ?_⟩
    all_goals simp only [Function.update_apply]; split_ifs with hp
    · subst hp; subst h1
      refine Loc.r29_slot hpc (hI.qok _) (by decide) h2 rfl ?_
      intro _ hq; subst hq
      have hh2 : c.hH h'.f.1 (cq (c.loc h'.f.1).ctr) = some h' := hh
      simp [hh2]
    · exact h2
    · subst hp; simpa using h3
    · exact h3
    · subst hp; simpa [hpc, isW1921] using h7
    · exact h7
  case rec31 p v f hpc =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI.hint p' q' h' hh
    refine ⟨h1, ?_, ?_, h4, h5, le_trans h6 (hm q'), ?_⟩
    all_goals simp only [Function.update_apply]; split_ifs with hp
    · subst hp; subst h1
      exact Loc.r31_slot hpc (hI.qok _) (by decide) h2 rfl (fun h => absurd h (by decide))
    · exact h2
    · subst hp; simpa using h3
    · exact h3
    · subst hp; simpa [hpc, isW1921] using h7
    · exact h7
  case l21 p v f s' m19 τ19 π hpc =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI.hint p' q' h' hh
    refine ⟨h1, ?_, ?_, h4, h5, le_trans h6 (hm q'), ?_⟩
    all_goals simp only [Function.update_apply]; split_ifs with hp
    · subst hp
      exact h2.congr rfl (by funext o; have := o.isLt; simp [Loc.U, stage, hpc]; omega)
    · exact h2
    · subst hp; simpa using h3
    · exact h3
    · subst hp; left; simp only; omega
    · exact h7
  case l23 p v f hpc =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI.hint p' q' h' hh
    refine ⟨h1, ?_, ?_, h4, h5, le_trans h6 (hm q'), ?_⟩
    all_goals simp only [Function.update_apply]; split_ifs with hp
    · subst hp
      exact h2.congr rfl (by funext o; have := o.isLt; simp [Loc.U, stage, hpc]; omega)
    · exact h2
    · subst hp; simpa using h3
    · exact h3
    · subst hp; left; simp only; rcases h7 with h7 | h7
      · omega
      · simp [hpc, isW1921] at h7
    · exact h7
  all_goals
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI.hint p' q' h' hh
    refine ⟨h1, ?_, ?_, h4, h5, le_trans h6 (hm q'), ?_⟩
    all_goals simp only [Function.update_apply]; split_ifs with hp
    all_goals first
      | exact h2
      | exact h3
      | exact h7
      | (subst hp; exact h2.congr rfl (Loc.U_congr rfl (by simp [stage, *])))
      | (subst hp; simpa using h3)
      | (subst hp; simpa [*, isW1921] using h7)

lemma Step.tau_of_m (hs : Step W c c') : ∀ q, (c'.loc q).m = (c.loc q).m →
    (c'.loc q).τ35 = (c.loc q).τ35 := by
  intro q
  cases hs <;> (simp only [Function.update_apply]; split_ifs <;> simp_all)

theorem Inv.hint'_step (hI : Inv W c) (hs : Step W c c') : ∀ p q b, c'.hH' p q = some b →
    b.f.1 = p ∧ (c'.loc p).SlotProt b.f 3 q ∧
    (c'.loc p).lc b.f = b.w ∧ b.w < (c'.loc p).ctr ∧ (c'.loc p).pp b.f = some b.π ∧
    b.s = Sval n b.m19 ∧ b.m19 ≤ (c'.loc q).m ∧ (b.m19 = (c'.loc q).m → (c'.loc q).τ35 ≤ b.π) := by
  intro p' q' b hb
  have hm := hs.m_mono
  have hτ := hs.tau_of_m
  have last : ∀ b : HE' n, b.m19 ≤ (c.loc q').m → (b.m19 = (c.loc q').m → (c.loc q').τ35 ≤ b.π) →
      b.m19 ≤ (c'.loc q').m ∧ (b.m19 = (c'.loc q').m → (c'.loc q').τ35 ≤ b.π) := by
    intro b h1 h2
    refine ⟨le_trans h1 (hm q'), fun e => ?_⟩
    have : (c'.loc q').m = (c.loc q').m := le_antisymm (e ▸ h1) (hm q')
    rw [hτ q' this]; exact h2 (this ▸ e)
  cases hs
  case l21 p v f s' m19 τ19 π hpc =>
    by_cases hnew : p' = p ∧ q' = cq (c.loc p).ctr
    · obtain ⟨rfl, rfl⟩ := hnew
      simp only [Function.update_self, Option.some.injEq] at hb; subst hb
      obtain ⟨h1, h2, h3⟩ := hI.chosen p' f (by simp [hpc, curF])
      have hl := (hI.locRd p').2.2.2.2 s' m19 τ19 (by simp [hpc, s19Of])
      have hw := hI.w21 p' _ _ _ _ _ _ hpc
      refine ⟨h1, ?_, by simpa using h3, by simp, by simpa using hw.1, hl.1,
        last ⟨f, s', (c.loc p').ctr, m19, π⟩ hl.2.1 (fun e => le_trans (hl.2.2.1 e) hw.2)⟩
      simp only [Function.update_self]
      unfold Loc.SlotProt
      refine Loc.Prot.congr (h2.mono ?_) rfl
        (by funext o; have := o.isLt; simp [Loc.U, stage, hpc]; omega)
      have e := nr_w (c.loc p') (by simp [stage, hpc]) 3 (by decide)
      have e2 : ({ c.loc p' with pc := .wRet v, ctr := (c.loc p').ctr + 1 } : Loc n T).nr 3
          (cq (c.loc p').ctr) = (c.loc p').nr 3 (cq (c.loc p').ctr) := by
        unfold Loc.nr; congr 1; simp [Loc.U, stage, hpc]
      rw [e2, e]; simp; omega
    · have hb' : c.hH' p' q' = some b := by
        by_cases hp : p' = p
        · subst hp
          have hq : q' ≠ cq (c.loc p').ctr := fun hq => hnew ⟨rfl, hq⟩
          simpa [Function.update_of_ne hq] using hb
        · simpa [Function.update_of_ne hp] using hb
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.hint' p' q' b hb'
      refine ⟨h1, ?_, ?_, ?_, ?_, h6, last b h7 h8⟩
      all_goals simp only [Function.update_apply]; split_ifs with hp
      · subst hp
        exact h2.congr rfl (by funext o; have := o.isLt; simp [Loc.U, stage, hpc]; omega)
      · exact h2
      · subst hp; simpa using h3
      · exact h3
      · subst hp; simp only; omega
      · exact h4
      · subst hp; simpa using h5
      · exact h5
  case l45 q x r hpc =>
    have hb' : c.hH' p' q' = some b := by
      by_cases hp : p' = cq x
      · subst hp
        by_cases hq : q' = q
        · subst hq; simp at hb
        · simpa [Function.update_of_ne hq] using hb
      · simpa [Function.update_of_ne hp] using hb
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.hint' p' q' b hb'
    refine ⟨h1, ?_, ?_, ?_, ?_, h6, last b h7 h8⟩
    all_goals simp only [Function.update_apply]; split_ifs with hp
    all_goals first
      | exact h2 | exact h3 | exact h4 | exact h5
      | (subst hp; exact h2.congr rfl (Loc.U_congr rfl (by simp [stage, hpc])))
      | (subst hp; simpa using h3) | (subst hp; simpa using h4) | (subst hp; simpa using h5)
  case rec27 p v f hpc hf =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.hint' p' q' b hb
    refine ⟨h1, ?_, ?_, ?_, ?_, h6, last b h7 h8⟩
    all_goals simp only [Function.update_apply]; split_ifs with hp
    all_goals first
      | exact h2 | exact h3 | exact h4 | exact h5
      | (subst hp; subst h1
         exact Loc.r27_slot hpc (hI.qok _) (by decide) h2 rfl (fun h => absurd h (by decide)))
      | (subst hp
         have hne : b.f ≠ f := fun e => h2.1 (e ▸ hf)
         first
           | simpa [Function.update_of_ne hne] using h3
           | simpa using h4
           | simpa [Function.update_of_ne hne] using h5)
  case rec29 p v f hpc =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.hint' p' q' b hb
    refine ⟨h1, ?_, ?_, ?_, ?_, h6, last b h7 h8⟩
    all_goals simp only [Function.update_apply]; split_ifs with hp
    all_goals first
      | exact h2 | exact h3 | exact h4 | exact h5
      | (subst hp; subst h1
         exact Loc.r29_slot hpc (hI.qok _) (by decide) h2 rfl (fun h => absurd h (by decide)))
      | (subst hp; simpa using h3) | (subst hp; simpa using h4) | (subst hp; simpa using h5)
  case rec31 p v f hpc =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.hint' p' q' b hb
    refine ⟨h1, ?_, ?_, ?_, ?_, h6, last b h7 h8⟩
    all_goals simp only [Function.update_apply]; split_ifs with hp
    all_goals first
      | exact h2 | exact h3 | exact h4 | exact h5
      | (subst hp; subst h1
         refine Loc.r31_slot hpc (hI.qok _) (by decide) h2 rfl ?_
         intro _ hq; subst hq
         have hb2 : c.hH' b.f.1 (cq (c.loc b.f.1).ctr) = some b := hb
         simp [hb2])
      | (subst hp; simpa using h3) | (subst hp; simpa using h4) | (subst hp; simpa using h5)
  case l20 p v f s' m19 τ19 hpc =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.hint' p' q' b hb
    refine ⟨h1, ?_, ?_, ?_, ?_, h6, last b h7 h8⟩
    all_goals simp only [Function.update_apply]; split_ifs with hp
    all_goals first
      | exact h2 | exact h3 | exact h4 | exact h5
      | (subst hp; exact h2.congr rfl (Loc.U_congr rfl (by simp [stage, hpc])))
      | (subst hp; simpa using h3) | (subst hp; simpa using h4)
      | (subst hp
         have hne : b.f ≠ f := by
           intro e; subst e
           have := (hI.chosen p' b.f (by simp [hpc, curF])).2.2; omega
         simpa [Function.update_of_ne hne] using h5)
  case l23 p v f hpc =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.hint' p' q' b hb
    refine ⟨h1, ?_, ?_, ?_, ?_, h6, last b h7 h8⟩
    all_goals simp only [Function.update_apply]; split_ifs with hp
    all_goals first
      | exact h2 | exact h3 | exact h4 | exact h5
      | (subst hp
         exact h2.congr rfl (by funext o; have := o.isLt; simp [Loc.U, stage, hpc]; omega))
      | (subst hp; simpa using h3) | (subst hp; simp only; omega)
      | (subst hp
         have hne : b.f ≠ f := by
           intro e; subst e
           have := (hI.chosen p' b.f (by simp [hpc, curF])).2.2; omega
         simpa [Function.update_of_ne hne] using h5)
  all_goals
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.hint' p' q' b hb
    refine ⟨h1, ?_, ?_, ?_, ?_, h6, last b h7 h8⟩
    all_goals simp only [Function.update_apply]; split_ifs with hp
    all_goals first
      | exact h2 | exact h3 | exact h4 | exact h5
      | (subst hp; exact h2.congr rfl (Loc.U_congr rfl (by simp [stage, *])))
      | (subst hp; simpa using h3) | (subst hp; simpa using h4) | (subst hp; simpa using h5)

lemma done44_le (l : Loc n T) : done44 l ≤ l.m := by unfold done44; split_ifs <;> omega

theorem Inv.reset_step (hI : Inv W c) (hs : Step W c c') : ∀ p q h, c'.hH p q = some h →
    ∀ e, h.m18 < e → e ≤ done44 (c'.loc q) → (e - 1) % n ≠ p.val := by
  intro p' q' h' hh e he1 he2
  have hs_m := hs.m_mono
  cases hs
  case l18 p v f s m14 olds olds' hpc =>
    by_cases hnew : p' = p ∧ q' = cq (c.loc p).ctr
    · obtain ⟨rfl, rfl⟩ := hnew
      simp only [Function.update_self, Option.some.injEq] at hh; subst hh
      exfalso
      simp only at he1
      revert he2
      simp only [Function.update_apply]; split_ifs with hq
      · rw [hq] at he1; simp [done44, pre44]; omega
      · have := done44_le (c.loc (cq (c.loc p').ctr)); omega
    · have hh' : c.hH p' q' = some h' := by
        by_cases hp : p' = p
        · subst hp
          have hq : q' ≠ cq (c.loc p').ctr := fun hq => hnew ⟨rfl, hq⟩
          simpa [Function.update_of_ne hq] using hh
        · simpa [Function.update_of_ne hp] using hh
      refine hI.reset p' q' h' hh' e he1 ?_
      revert he2; simp only [Function.update_apply]; split_ifs with hq
      · subst hq; simp [done44, pre44, hpc]
      · exact id
  case l44 q x r hpc =>
    by_cases hreset : p' = cq x ∧ q' = q
    · obtain ⟨rfl, rfl⟩ := hreset; simp at hh
    · have hh' : c.hH p' q' = some h' := by
        by_cases hp : p' = cq x
        · subst hp
          have hq : q' ≠ q := fun hq => hreset ⟨rfl, hq⟩
          simpa [Function.update_of_ne hq] using hh
        · simpa [Function.update_of_ne hp] using hh
      have hw := hI.exec q; simp only [ExecInv, hpc] at hw
      obtain ⟨hx, hm1, -⟩ := hw
      rw [hI.sEq q] at hx
      have hxm := Sval_mod hm1 hx
      revert he2; simp only [Function.update_apply]; split_ifs with hq
      · subst hq
        simp only [done44, pre44, hpc, if_true, Bool.false_eq_true, if_false]
        intro he2
        rcases Nat.lt_or_ge e (c.loc q').m with hlt | hge
        · exact hI.reset p' q' h' hh' e he1 (by simp [done44, pre44, hpc]; omega)
        · have : e = (c.loc q').m := by omega
          subst this
          intro hcontra
          apply hreset; refine ⟨Fin.ext ?_, rfl⟩
          simp only [cq]; omega
      · exact hI.reset p' q' h' hh' e he1
  all_goals
    have hh' : c.hH p' q' = some h' := hh
    refine hI.reset p' q' h' hh' e he1 ?_
    revert he2; simp only [Function.update_apply]; split_ifs with hq
    · subst hq; simp [done44, pre44, *]
    · exact id

theorem Inv.pairIn_step (hI : Inv W c) (hs : Step W c c') : ∀ p q, isW1921 (c'.loc p).pc →
    cq (c'.loc p).ctr = q → ∀ h, c'.hH p q = some h →
    h.w = (c'.loc p).ctr ∧ curF (c'.loc p).pc = some h.f ∧ M18c (c'.loc p).pc h.m18 := by
  intro p' q' hw hq h' hh
  cases hs
  case l18 p v f s m14 olds olds' hpc =>
    by_cases hp : p' = p
    · subst hp
      simp only [Function.update_self] at hq hh ⊢
      subst hq
      simp only [Function.update_self, Option.some.injEq] at hh; subst hh
      simp [curF, M18c]
    · simp only [Function.update_of_ne hp] at hw hq hh ⊢
      exact hI.pairIn p' q' hw hq h' hh
  case l19 p v f hpc =>
    by_cases hp : p' = p
    · subst hp
      simp only [Function.update_self] at hq hh ⊢
      obtain ⟨h1, h2, -⟩ := hI.pairIn p' q' (by simp [hpc, isW1921]) hq h' hh
      have h6 := (hI.hint p' q' h' hh).2.2.2.2.2.1
      subst hq
      exact ⟨h1, by simpa [curF, hpc] using h2, by simpa [M18c] using h6⟩
    · simp only [Function.update_of_ne hp] at hw hq hh ⊢
      exact hI.pairIn p' q' hw hq h' hh
  case l20 p v f s' m19 τ19 hpc =>
    by_cases hp : p' = p
    · subst hp
      simp only [Function.update_self] at hq hh ⊢
      obtain ⟨h1, h2, h3⟩ := hI.pairIn p' q' (by simp [hpc, isW1921]) hq h' hh
      exact ⟨h1, by simpa [curF, hpc] using h2, by simpa [M18c, hpc] using h3⟩
    · simp only [Function.update_of_ne hp] at hw hq hh ⊢
      exact hI.pairIn p' q' hw hq h' hh
  case l44 q x r hpc =>
    have hh' : c.hH p' q' = some h' := by
      by_cases hp : p' = cq x
      · subst hp
        by_cases hq' : q' = q
        · subst hq'; simp at hh
        · simpa [Function.update_of_ne hq'] using hh
      · simpa [Function.update_of_ne hp] using hh
    revert hw hq; simp only [Function.update_apply]; split_ifs with hp
    · subst hp; simp [isW1921]
    · intro hw hq; exact hI.pairIn p' q' hw hq h' hh'
  all_goals
    revert hw hq; simp only [Function.update_apply]; split_ifs with hp
    all_goals first
      | (intro hw hq; exact hI.pairIn p' q' hw hq h' hh)
      | (subst hp; simp [isW1921])
      | (subst hp; simp [isW1921, *])

theorem Inv.pairOut_step (hI : Inv W c) (hs : Step W c c') : ∀ p q,
    ¬ (isW1921 (c'.loc p).pc ∧ cq (c'.loc p).ctr = q) → ∀ h b,
    c'.hH p q = some h → c'.hH' p q = some b → h.w = b.w ∧ h.f = b.f ∧ h.m18 ≤ b.m19 := by
  intro p' q' hcond h' b hh hb
  cases hs
  case l21 p v f s' m19 τ19 π hpc =>
    by_cases hnew : p' = p ∧ q' = cq (c.loc p).ctr
    · obtain ⟨rfl, rfl⟩ := hnew
      simp only [Function.update_self, Option.some.injEq] at hb; subst hb
      obtain ⟨h1, h2, h3⟩ := hI.pairIn p' _ (by simp [hpc, isW1921]) rfl h' hh
      simp only [hpc, curF, Option.some.injEq, M18c] at h2 h3
      exact ⟨h1, h2.symm, h3⟩
    · have hb' : c.hH' p' q' = some b := by
        by_cases hp : p' = p
        · subst hp
          have hq : q' ≠ cq (c.loc p').ctr := fun hq => hnew ⟨rfl, hq⟩
          simpa [Function.update_of_ne hq] using hb
        · simpa [Function.update_of_ne hp] using hb
      refine hI.pairOut p' q' ?_ h' b hh hb'
      by_cases hp : p' = p
      · subst hp; intro h; exact hnew ⟨rfl, h.2.symm⟩
      · simpa [Function.update_of_ne hp] using hcond
  case l18 p v f s m14 olds olds' hpc =>
    by_cases hnew : p' = p ∧ q' = cq (c.loc p).ctr
    · obtain ⟨rfl, rfl⟩ := hnew
      exact absurd ⟨by simp [isW1921], by simp⟩ hcond
    · have hh' : c.hH p' q' = some h' := by
        by_cases hp : p' = p
        · subst hp
          have hq : q' ≠ cq (c.loc p').ctr := fun hq => hnew ⟨rfl, hq⟩
          simpa [Function.update_of_ne hq] using hh
        · simpa [Function.update_of_ne hp] using hh
      refine hI.pairOut p' q' ?_ h' b hh' hb
      by_cases hp : p' = p
      · subst hp; simp [hpc, isW1921]
      · simpa [Function.update_of_ne hp] using hcond
  case l44 q x r hpc =>
    have hh' : c.hH p' q' = some h' := by
      by_cases hp : p' = cq x
      · subst hp
        by_cases hq' : q' = q
        · subst hq'; simp at hh
        · simpa [Function.update_of_ne hq'] using hh
      · simpa [Function.update_of_ne hp] using hh
    refine hI.pairOut p' q' ?_ h' b hh' hb
    revert hcond; simp only [Function.update_apply]; split_ifs with hp
    · subst hp; simp [isW1921, hpc]
    · exact id
  case l45 q x r hpc =>
    have hb' : c.hH' p' q' = some b := by
      by_cases hp : p' = cq x
      · subst hp
        by_cases hq' : q' = q
        · subst hq'; simp at hb
        · simpa [Function.update_of_ne hq'] using hb
      · simpa [Function.update_of_ne hp] using hb
    refine hI.pairOut p' q' ?_ h' b hh hb'
    revert hcond; simp only [Function.update_apply]; split_ifs with hp
    · subst hp; simp [isW1921, hpc]
    · exact id
  all_goals
    refine hI.pairOut p' q' ?_ h' b hh hb
    revert hcond; simp only [Function.update_apply]; split_ifs with hp
    · subst hp; simp [isW1921, *]
    · exact id

theorem Inv.mono_step (hI : Inv W c) (hs : Step W c c') : ∀ p, Mono c' p := by
  intro p' m14 hm14 b hb
  cases hs
  case l14 p v f hpc =>
    by_cases hp : p' = p
    · subst hp
      simp only [Function.update_self, m14Of, Option.some.injEq] at hm14 hb; subst hm14
      exact (hI.hint' p' _ b hb).2.2.2.2.2.2.1
    · simp only [Function.update_of_ne hp] at hm14 hb ⊢; exact hI.mono p' m14 hm14 b hb
  case l45 q x r hpc =>
    by_cases hp : p' = q
    · subst hp; simp [m14Of, hpc] at hm14
    · simp only [Function.update_of_ne hp] at hm14 hb
      refine hI.mono p' m14 hm14 b ?_
      by_cases hp' : p' = cq x
      · subst hp'
        by_cases hq : cq (c.loc (cq x)).ctr = q
        · rw [hq] at hb; simp at hb
        · simpa [Function.update_of_ne hq] using hb
      · simpa [Function.update_of_ne hp'] using hb
  case l21 p v f s' m19 τ19 π hpc =>
    by_cases hp : p' = p
    · subst hp; simp [m14Of] at hm14
    · simp only [Function.update_of_ne hp] at hm14 hb; exact hI.mono p' m14 hm14 b hb
  all_goals
    revert hm14 hb; simp only [Function.update_apply]; split_ifs with hp
    · subst hp; intro hm14 hb; simp only [m14Of, Option.some.injEq, reduceCtorEq] at hm14
      all_goals first
        | (subst hm14; exact hI.mono p' _ (by simp [*, m14Of]) b hb)
        | exact hI.mono p' m14 (by simp [*, m14Of]) b hb
    · exact fun h1 h2 => hI.mono p' m14 h1 b h2

lemma LocRd.frame {c c' : Cfg n T} {p : Fin n} (h : LocRd c p) (hl : c'.loc p = c.loc p)
    (hH : c'.hH p (cq (c.loc p).ctr) = c.hH p (cq (c.loc p).ctr) ∨
      c'.hH p (cq (c.loc p).ctr) = none)
    (hH' : c'.hH' p (cq (c.loc p).ctr) = c.hH' p (cq (c.loc p).ctr) ∨
      c'.hH' p (cq (c.loc p).ctr) = none)
    (hm : (c.loc (cq (c.loc p).ctr)).m ≤ (c'.loc (cq (c.loc p).ctr)).m)
    (hτ : (c'.loc (cq (c.loc p).ctr)).m = (c.loc (cq (c.loc p).ctr)).m →
      (c'.loc (cq (c.loc p).ctr)).τ35 = (c.loc (cq (c.loc p).ctr)).τ35)
    (htr : c.tr.length ≤ c'.tr.length) : LocRd c' p := by
  obtain ⟨A, B, C, D, E⟩ := h
  rw [LocRd, hl]
  refine ⟨fun s m14 h1 => ?_, fun olds h1 b h2 => ?_, fun olds h1 b h2 => ?_, D, fun s m19 τ h1 => ?_⟩
  · obtain ⟨e1, e2⟩ := A s m14 h1; exact ⟨e1, le_trans e2 hm⟩
  · rcases hH with e | e
    · rw [e] at h2; exact B olds h1 b h2
    · rw [e] at h2; simp at h2
  · rcases hH' with e | e
    · rw [e] at h2; exact C olds h1 b h2
    · rw [e] at h2; simp at h2
  · obtain ⟨e1, e2, e3, e4⟩ := E s m19 τ h1
    refine ⟨e1, le_trans e2 hm, fun e => ?_, le_trans e4 htr⟩
    have : (c'.loc (cq (c.loc p).ctr)).m = (c.loc (cq (c.loc p).ctr)).m :=
      le_antisymm (e ▸ e2) hm
    rw [hτ this]; exact e3 (this ▸ e)

lemma LocRd.of_none {c : Cfg n T} {p : Fin n} (h1 : smOf (c.loc p).pc = none)
    (h2 : oldsOf (c.loc p).pc = none) (h3 : olds'Of (c.loc p).pc = none)
    (h4 : ∀ v f s m14 olds olds', (c.loc p).pc ≠ .w18 v f s m14 olds olds')
    (h5 : s19Of (c.loc p).pc = none) : LocRd c p := by
  refine ⟨fun _ _ h => ?_, fun _ h => ?_, fun _ h => ?_,
    fun _ _ _ _ _ _ h => absurd h (h4 _ _ _ _ _ _), fun _ _ _ h => ?_⟩ <;> simp_all

set_option hygiene false in
/-- Generic case of `locRd_step`: the stepping process is at a line without the local values of
lines 15–21, and the other processes only see their shared variables grow. -/
local macro "locrd_gen" p:ident : tactic => `(tactic| (
  by_cases hp : p' = $p
  · subst hp; exact LocRd.of_none (by simp [smOf]) (by simp [oldsOf]) (by simp [olds'Of])
      (by simp) (by simp [s19Of])
  · exact old.frame (by simp [Function.update_of_ne hp]) (Or.inl rfl) (Or.inl rfl)
      (hm _) (hτ _) htr))

theorem Inv.locRd_step (hI : Inv W c) (hs : Step W c c') : ∀ p, LocRd c' p := by
  intro p'
  have hm := hs.m_mono
  have hτ := hs.tau_of_m
  have htr : c.tr.length ≤ c'.tr.length := by cases hs <;> simp
  have old := hI.locRd p'
  cases hs
  case l14 p v f hpc =>
    by_cases hp : p' = p
    · subst hp
      refine ⟨fun s m14 h1 => ?_, fun _ h => by simp [oldsOf] at h, fun _ h => by simp [olds'Of] at h,
        fun _ _ _ _ _ _ h => by simp at h, fun _ _ _ h => by simp [s19Of] at h⟩
      simp only [Function.update_self, smOf, Option.some.injEq, Prod.mk.injEq] at h1 ⊢
      obtain ⟨rfl, rfl⟩ := h1
      refine ⟨hI.sEq _, ?_⟩
      by_cases hq : cq (c.loc p').ctr = p'
      · rw [hq]; simp
      · simp [Function.update_of_ne hq]
    · exact old.frame (by simp [Function.update_of_ne hp]) (Or.inl rfl) (Or.inl rfl)
        (hm _) (hτ _) htr
  case l15 p v f s m14 hpc =>
    by_cases hp : p' = p
    · subst hp
      obtain ⟨A, -, -, -, -⟩ := old
      refine ⟨fun s' m14' h1 => ?_, fun olds h1 b h2 => ?_, fun _ h => by simp [olds'Of] at h,
        fun _ _ _ _ _ _ h => by simp at h, fun _ _ _ h => by simp [s19Of] at h⟩
      · simp only [Function.update_self, smOf, Option.some.injEq, Prod.mk.injEq] at h1 ⊢
        obtain ⟨rfl, rfl⟩ := h1
        have := A s m14 (by simp [hpc, smOf])
        by_cases hq : cq (c.loc p').ctr = p'
        · rw [hq] at this ⊢; simpa using this
        · simpa [Function.update_of_ne hq] using this
      · simp only [Function.update_self, oldsOf, Option.some.injEq] at h1 h2 ⊢
        subst h1; simp [h2]
    · exact old.frame (by simp [Function.update_of_ne hp]) (Or.inl rfl) (Or.inl rfl)
        (hm _) (hτ _) htr
  case l16w p v f s m14 olds hpc hc =>
    by_cases hp : p' = p
    · subst hp
      obtain ⟨A, B, -, -, -⟩ := old
      refine ⟨fun s' m14' h1 => ?_, fun olds' h1 b h2 => ?_, fun olds' h1 b h2 => ?_,
        fun _ _ _ _ _ _ h => ?_, fun _ _ _ h => by simp [s19Of] at h⟩
      · simp only [Function.update_self, smOf, Option.some.injEq, Prod.mk.injEq] at h1 ⊢
        obtain ⟨rfl, rfl⟩ := h1
        have := A s m14 (by simp [hpc, smOf])
        by_cases hq : cq (c.loc p').ctr = p'
        · rw [hq] at this ⊢; simpa using this
        · simpa [Function.update_of_ne hq] using this
      · simp only [Function.update_self, oldsOf, Option.some.injEq] at h1 h2 ⊢
        subst h1; exact B olds (by simp [hpc, oldsOf]) b h2
      · simp only [Function.update_self, olds'Of, Option.some.injEq] at h1 h2 ⊢
        subst h1; simp [h2]
      · simp only [Function.update_self, PC.w18.injEq] at h
        obtain ⟨-, -, rfl, -, rfl, rfl⟩ := h; exact hc
    · exact old.frame (by simp [Function.update_of_ne hp]) (Or.inl rfl) (Or.inl rfl)
        (hm _) (hτ _) htr
  case l19 p v f hpc =>
    by_cases hp : p' = p
    · subst hp
      refine ⟨fun _ _ h => by simp [smOf] at h, fun _ h => by simp [oldsOf] at h,
        fun _ h => by simp [olds'Of] at h, fun _ _ _ _ _ _ h => by simp at h, fun s' m19 τ h1 => ?_⟩
      simp only [Function.update_self, s19Of, Option.some.injEq, Prod.mk.injEq] at h1 ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h1
      refine ⟨hI.sEq _, ?_, ?_, le_rfl⟩
      · by_cases hq : cq (c.loc p').ctr = p'
        · rw [hq]; simp
        · simp [Function.update_of_ne hq]
      · intro _
        by_cases hq : cq (c.loc p').ctr = p'
        · rw [hq]; simpa using hI.tau35 p'
        · simpa [Function.update_of_ne hq] using hI.tau35 _
    · exact old.frame (by simp [Function.update_of_ne hp]) (Or.inl rfl) (Or.inl rfl)
        (hm _) (hτ _) htr
  case l20 p v f s' m19 τ19 hpc =>
    by_cases hp : p' = p
    · subst hp
      obtain ⟨-, -, -, -, E⟩ := old
      refine ⟨fun _ _ h => by simp [smOf] at h, fun _ h => by simp [oldsOf] at h,
        fun _ h => by simp [olds'Of] at h, fun _ _ _ _ _ _ h => by simp at h, fun s'' m τ h1 => ?_⟩
      simp only [Function.update_self, s19Of, Option.some.injEq, Prod.mk.injEq] at h1 ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h1
      obtain ⟨e1, e2, e3, e4⟩ := E s' m19 τ19 (by simp [hpc, s19Of])
      have hq : cq (c.loc p').ctr ≠ p' ∨ cq (c.loc p').ctr = p' := (em _).symm
      rcases hq with hq | hq
      · simp only [Function.update_of_ne hq]; exact ⟨e1, e2, e3, by simp; omega⟩
      · rw [hq] at e2 e3 ⊢; simp only [Function.update_self]; exact ⟨e1, e2, e3, by simp; omega⟩
    · exact old.frame (by simp [Function.update_of_ne hp]) (Or.inl rfl) (Or.inl rfl)
        (hm _) (hτ _) htr
  case l44 q x r hpc =>
    by_cases hp : p' = q
    · subst hp; exact LocRd.of_none (by simp [smOf]) (by simp [oldsOf]) (by simp [olds'Of])
        (by simp) (by simp [s19Of])
    · refine old.frame (by simp [Function.update_of_ne hp]) ?_ (Or.inl rfl) (hm _) (hτ _) htr
      by_cases hp' : p' = cq x
      · subst hp'
        by_cases hq : cq (c.loc (cq x)).ctr = q
        · right; rw [hq]; simp
        · left; simp [Function.update_of_ne hq]
      · left; simp [Function.update_of_ne hp']
  case l45 q x r hpc =>
    by_cases hp : p' = q
    · subst hp; exact LocRd.of_none (by simp [smOf]) (by simp [oldsOf]) (by simp [olds'Of])
        (by simp) (by simp [s19Of])
    · refine old.frame (by simp [Function.update_of_ne hp]) (Or.inl rfl) ?_ (hm _) (hτ _) htr
      by_cases hp' : p' = cq x
      · subst hp'
        by_cases hq : cq (c.loc (cq x)).ctr = q
        · right; rw [hq]; simp
        · left; simp [Function.update_of_ne hq]
      · left; simp [Function.update_of_ne hp']
  case l18 p v f s m14 olds olds' hpc =>
    by_cases hp : p' = p
    · subst hp; exact LocRd.of_none (by simp [smOf]) (by simp [oldsOf]) (by simp [olds'Of])
        (by simp) (by simp [s19Of])
    · exact old.frame (by simp [Function.update_of_ne hp]) (Or.inl (by simp [Function.update_of_ne hp]))
        (Or.inl rfl) (hm _) (hτ _) htr
  case l21 p v f s' m19 τ19 π hpc =>
    by_cases hp : p' = p
    · subst hp; exact LocRd.of_none (by simp [smOf]) (by simp [oldsOf]) (by simp [olds'Of])
        (by simp) (by simp [s19Of])
    · exact old.frame (by simp [Function.update_of_ne hp]) (Or.inl rfl)
        (Or.inl (by simp [Function.update_of_ne hp])) (hm _) (hτ _) htr
  case winv p v h => locrd_gen p
  case rec27 p v f h hf => locrd_gen p
  case rec29 p v f h => locrd_gen p
  case rec31 p v f h => locrd_gen p
  case swinv p v f h => locrd_gen p
  case swret p v f r h => locrd_gen p
  case l16s p v f s m14 olds h hc => locrd_gen p
  case l23 p v f h => locrd_gen p
  case wret p v h => locrd_gen p
  case einv q o ho h => locrd_gen q
  case l34 q o h => locrd_gen q
  case l35 q o x h => locrd_gen q
  case l36 q o x h => locrd_gen q
  case l37 q o x i g ts h => locrd_gen q
  case l39 q o x i g ts h => locrd_gen q
  case l40h q o x i g ts hv h hb hb' h1 h2 h3 h4 h5 => locrd_gen q
  case l40d q o x i g ts hv h hn => locrd_gen q
  case opinv q o x i ts h => locrd_gen q
  case opret q x i ts t r h => locrd_gen q
  case eret q r h => locrd_gen q

end Podc.WritableObjects.WF
