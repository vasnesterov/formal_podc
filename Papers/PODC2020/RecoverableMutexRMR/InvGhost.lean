import Papers.PODC2020.RecoverableMutexRMR.InvQuiet

/-!
# Preservation of the invariant by the FAI steps (lines 4, 15, 28) and crashes
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

theorem inv_step_l4 {s : Cfg P} {g : Ghost P} {p : P}  (hI : Inv s g)
    (hpc : s.pc p = .l4) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, h2⟩ := hL
  simp only [Cfg.step, Ghost.next, hpc]
  set s' : Cfg P := { s with C := s.C + 1, pc := Function.update s.pc p (.l5 (s.C + 1)) } with hs'
  set g' : Ghost P :=
    { g with own := Function.update g.own (s.C + 1) (some p),
             cur := Function.update g.cur p (s.C + 1),
             pend := Function.update g.pend p true,
             cr := Function.update g.cr p false,
             lost := if g.cr p = true ∧ s.A (g.cur p) = .empty then insert (g.cur p) g.lost
               else g.lost } with hg'
  have hAC : s.A (s.C + 1) = .empty := by
    by_contra h; have := (hI.A_ne _ h).2; omega
  have hpcq : ∀ q, q ≠ p → s'.pc q = s.pc q := fun q hq => by simp [hs', Function.update_of_ne hq]
  have hpcp : s'.pc p = .l5 (s.C + 1) := by simp [hs']
  have hcurq : ∀ q, q ≠ p → g'.cur q = g.cur q := fun q hq => by simp [hg', Function.update_of_ne hq]
  have hpendp : g.pend p = true → s.A (g.cur p) = .skipped :=
    hI.skipped_of_pend (by simp [hpc, PendPC])
  have hnI : ¬ inI s g p := fun h => h.2.1 (hpendp h.2.2)
  have hinIq : ∀ q, q ≠ p → (inI s' g' q ↔ inI s g q) := fun q hq => by
    simp [inI, hs', hg', Function.update_of_ne hq]
  have hinIp' : inI s' g' p := by simp [inI, hs', hg', hAC]
  have hownx : ∀ x, x ≠ s.C + 1 → g'.own x = g.own x := fun x hx => by
    simp [hg', Function.update_of_ne hx]
  have eI : Isize s' g' = Isize s g + 1 := by
    have := card_filter_update (inI s' g') (inI s g) p hinIq
    simp only [hinIp', hnI, if_true, if_false] at this; exact this
  have eC : crCount s' g' + (if (g.cr p = true ∧ s.A (g.cur p) ≠ .skipped) then 1 else 0) =
      crCount s g + 0 := by
    have := card_filter_update (fun q => g'.cr q = true ∧ s'.A (g'.cur q) ≠ .skipped)
      (fun q => g.cr q = true ∧ s.A (g.cur q) ≠ .skipped) p
      (fun q hq => by simp [hs', hg', Function.update_of_ne hq])
    have h0 : ¬ (g'.cr p = true ∧ s'.A (g'.cur p) ≠ .skipped) := by simp [hg']
    simp only [h0, if_false] at this; exact this
  have eL : lostCount s' g' ≤ lostCount s g +
      (if g.cr p = true ∧ s.A (g.cur p) = .empty then 1 else 0) := by
    unfold lostCount
    rw [show s'.A = s.A from rfl]
    by_cases hc : g.cr p = true ∧ s.A (g.cur p) = .empty
    · simp only [hg', hc, and_self, if_true]
      rw [Finset.filter_insert]
      split_ifs
      · exact Finset.card_insert_le _ _
      · omega
    · simp only [hg', hc, if_false]; omega
  have hcL : (if g.cr p = true ∧ s.A (g.cur p) = .empty then 1 else 0) ≤
      (if (g.cr p = true ∧ s.A (g.cur p) ≠ .skipped) then 1 else 0) := by
    split_ifs with ha hb <;> try omega
    exact absurd ⟨ha.1, by rw [ha.2]; simp⟩ hb
  have hPhi : Phi s' g' = Phi s g := by
    unfold Phi; rw [eI, show s'.D = s.D from rfl, show s'.C = s.C + 1 from rfl]; push_cast; ring
  have hJ : ∀ ℓ, ℓ ≤ s.T → ℓ + 1 ≤ s.C → (JHyp s g ℓ → 1 ≤ Phi s g) →
      JHyp s' g' ℓ → 1 ≤ Phi s' g' := by
    rintro ℓ - hℓ h ⟨hj1, o, ho, hoc⟩
    by_cases e : o = p
    · subst e; simp [hg'] at hoc; omega
    · rw [hPhi]; exact h ⟨hj1, o, (hinIq o e).1 ho, by rw [← hcurq o e]; exact hoc⟩
  exact {
    T_le := by have := hI.T_le; simp [hs']; omega
    A_ne := fun x hx => by have := hI.A_ne x hx; simp [hs']; omega
    A_tok := hI.A_tok
    done := hI.done
    grant := hI.grant
    future := fun q x hx hlt => by
      rcases hI.future q x hx hlt with k | ⟨k1, k2, k3, k4⟩
      · exact Or.inl k
      · by_cases e : q = p
        · subst e; simp [OnTrack, hpc] at k4
        · exact Or.inr ⟨k1, k2, k3, (OnTrack_congr (hpcq q e) rfl).2 k4⟩
    own_claimed := fun x q hx => by
      rw [hownx x (by rintro rfl; rw [hAC] at hx; cases hx)]; exact hI.own_claimed x q hx
    own_le := fun x q hx => by
      by_cases e : x = s.C + 1
      · subst e; simp [hs']
      · rw [hownx x e] at hx; have := hI.own_le x q hx; simp [hs']; omega
    own_ex := fun x hx hxC => by
      by_cases e : x = s.C + 1
      · subst e; exact ⟨p, by simp [hg']⟩
      · rw [hownx x e]; exact hI.own_ex x hx (by simp [hs'] at hxC; omega)
    cur_le := fun q => by
      by_cases e : q = p
      · subst e; simp [hg', hs']
      · rw [hcurq q e]; have := hI.cur_le q; simp [hs']; omega
    own_cur := fun q hq => by
      by_cases e : q = p
      · subst e; simp [hg']
      · rw [hcurq q e] at hq ⊢
        have := hI.cur_le q
        rw [hownx _ (by omega)]; exact hI.own_cur q hq
    W_cur := fun q hq => by
      by_cases e : q = p
      · subst e; rw [h2] at hq; simp at hq
      · rw [hcurq q e]; exact hI.W_cur q hq
    X_W := hI.X_W
    pend_pc := fun q hq => by
      by_cases e : q = p
      · subst e; left; rw [hpcp]; simp [PendPC]
      · rw [hpcq q e, hcurq q e]
        exact hI.pend_pc q (by simpa [hg', Function.update_of_ne e] using hq)
    cr_pc := fun q hq => by
      by_cases e : q = p
      · subst e; rw [hpcp] at hq; simp [CrPC] at hq
      · rw [hpcq q e] at hq; simpa [hg', Function.update_of_ne e] using hI.cr_pc q hq
    l3_cr := fun q hq => by
      by_cases e : q = p
      · subst e; rw [hpcp] at hq; cases hq
      · rw [hpcq q e] at hq; simpa [hg', Function.update_of_ne e] using hI.l3_cr q hq
    I_cr := fun q hq => by
      by_cases e : q = p
      · subst e; simp [hg']
      · simpa [hg', Function.update_of_ne e] using hI.I_cr q ((hinIq q e).1 hq)
    lost_wit := fun x hx hxC hA => by
      by_cases e : x = s.C + 1
      · subst e; right; exact ⟨p, by simp [hg'], by simp [hg'], by simp [hg']⟩
      · have hxC' : x ≤ s.C := by simp [hs'] at hxC; omega
        rcases hI.lost_wit x hx hxC' hA with k | ⟨o, k1, k2, k3⟩
        · left; simp only [hg']; split_ifs <;> simp [k]
        · by_cases eo : o = p
          · subst eo
            have hcr : g.cr o = true := by
              rcases k3 with k3 | k3
              · have := hpendp k3; rw [k2, hA] at this; cases this
              · exact k3
            left; simp only [hg']; rw [if_pos ⟨hcr, by rw [k2]; exact hA⟩]
            simp [k2]
          · right; refine ⟨o, by rw [hownx x e]; exact k1, by rw [hcurq o eo]; exact k2, ?_⟩
            simpa [hg', Function.update_of_ne eo] using k3
    phi_nonneg := by rw [hPhi]; exact hI.phi_nonneg
    psi_bound := by
      have := hI.psi_bound
      have e1 : nR15 s' = nR15 s := by
        unfold nR15; congr 1; apply Finset.filter_congr; intro q _
        by_cases e : q = p
        · subst e; simp [hpcp, hpc]
        · rw [hpcq q e]
      have e2 : nSkipped s' = nSkipped s := by
        unfold nSkipped
        rw [show s'.C + 1 = (s.C + 1) + 1 from rfl, Finset.range_add_one, Finset.filter_insert]
        simp [hAC, hs']
      have e3 : g'.ncr = g.ncr := rfl
      unfold Psi at this ⊢
      rw [hPhi, e1, e2, e3]
      have : (crCount s' g' : ℤ) + lostCount s' g' ≤ crCount s g + lostCount s g := by
        have a1 : crCount s' g' + lostCount s' g' ≤ crCount s g + lostCount s g := by omega
        exact_mod_cast a1
      linarith
    loc := fun q => by
      by_cases e : q = p
      · subst e; simp only [LI, hpcp]
        exact ⟨h1, h2, by simp [hg'], by omega, Or.inl hAC, by simp [hg']⟩
      · exact LI_frame (hI.loc q) (hpcq q e) rfl (Or.inl rfl) le_rfl (by simp [hs']) le_rfl
          (fun _ _ => rfl) (fun x r h h' => absurd (h.symm.trans h') (by simp))
          (hcurq q e) (by simp [hg', Function.update_of_ne e])
          (by simp [hg', Function.update_of_ne e]) hJ }

theorem inv_step_w28 {s : Cfg P} {g : Ghost P} {p : P} {w : ℕ} (hI : Inv s g)
    (hpc : s.pc p = .w28 w) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc, RetInv] at hL
  obtain ⟨h1, h2, h3, h4⟩ := hL
  have hcur : g.cur p = w := by rw [← hI.W_cur p (by omega), h2]
  simp only [Cfg.step, Ghost.next, hpc]
  set s' : Cfg P := { s with D := s.D + 1, pc := Function.update s.pc p (.m34 (.wr w)) } with hs'
  set g' : Ghost P :=
    { g with pend := Function.update g.pend p false, cr := Function.update g.cr p false } with hg'
  have hpcq : ∀ q, q ≠ p → s'.pc q = s.pc q := fun q hq => by simp [hs', Function.update_of_ne hq]
  have hpcp : s'.pc p = .m34 (.wr w) := by simp [hs']
  have hinIq : ∀ q, q ≠ p → (inI s' g' q ↔ inI s g q) := fun q hq => by
    simp [inI, hs', hg', Function.update_of_ne hq]
  have hinIp' : ¬ inI s' g' p := by simp [inI, hg']
  have hinIp : inI s g p ↔ g.pend p = true := by
    simp [inI, hcur, h3, h4]
  have eI : Isize s' g' + (if inI s g p then 1 else 0) = Isize s g + 0 := by
    have := card_filter_update (inI s' g') (inI s g) p hinIq
    simp only [hinIp', if_false] at this; exact this
  have eC : crCount s' g' + (if (g.cr p = true ∧ s.A (g.cur p) ≠ .skipped) then 1 else 0) =
      crCount s g + 0 := by
    have := card_filter_update (fun q => g'.cr q = true ∧ s'.A (g'.cur q) ≠ .skipped)
      (fun q => g.cr q = true ∧ s.A (g.cur q) ≠ .skipped) p
      (fun q hq => by simp [hs', hg', Function.update_of_ne hq])
    have h0 : ¬ (g'.cr p = true ∧ s'.A (g'.cur p) ≠ .skipped) := by simp [hg']
    simp only [h0, if_false] at this; exact this
  have ePhi' : Phi s' g' = (s.D : ℤ) + 1 + (Isize s' g' : ℤ) - s.C := by
    unfold Phi; rw [show s'.D = s.D + 1 from rfl, show s'.C = s.C from rfl]; push_cast; ring
  have hl : lostCount s' g' = lostCount s g := rfl
  have hc := hI.cr_pc p (by simp [hpc, CrPC])
  have hic := hI.I_cr p
  have hPhi : Phi s g ≤ Phi s' g' ∧ Psi s' g' = Psi s g := by
    unfold Psi; rw [ePhi', hl]; unfold Phi
    by_cases hpd : g.pend p = true
    · have hp : inI s g p := hinIp.2 hpd
      have hcr : g.cr p = false := hic hp
      simp only [hp, if_true, hcr, Bool.false_eq_true, false_and, if_false] at eI eC
      constructor <;> push_cast <;> omega
    · have hp : ¬ inI s g p := fun h => hpd (hinIp.1 h)
      have hcr : g.cr p = true := by rcases hc with h | h; exact absurd h hpd; exact h
      have hsk : s.A (g.cur p) ≠ .skipped := by rw [hcur, h4]; simp
      simp only [hp, if_false, hcr, hsk, true_and, ne_eq, not_false_eq_true, if_true] at eI eC
      constructor <;> push_cast <;> omega
  have hPsi := hPhi.2
  have hJ : ∀ ℓ, ℓ ≤ s.T → ℓ + 1 ≤ s.C → (JHyp s g ℓ → 1 ≤ Phi s g) →
      JHyp s' g' ℓ → 1 ≤ Phi s' g' := by
    rintro ℓ - - h ⟨hj1, o, ho, hoc⟩
    have ho' : inI s g o := by
      by_cases e : o = p
      · subst e; exact absurd ho hinIp'
      · exact (hinIq o e).1 ho
    have := h ⟨hj1, o, ho', hoc⟩
    linarith [hPhi.1]
  exact {
    T_le := hI.T_le
    A_ne := hI.A_ne
    A_tok := hI.A_tok
    done := hI.done
    grant := hI.grant
    future := fun q x hx hlt => by
      by_cases hq : q = p
      · subst hq
        rcases hI.future q x hx hlt with k | ⟨-, k2, -⟩
        · exact Or.inl k
        · rw [k2] at h2; simp at h2; omega
      · rcases hI.future q x hx hlt with k | ⟨k1, k2, k3, k4⟩
        · exact Or.inl k
        · exact Or.inr ⟨k1, k2, k3, (OnTrack_congr (hpcq q hq) rfl).2 k4⟩
    own_claimed := hI.own_claimed
    own_le := hI.own_le
    own_ex := hI.own_ex
    cur_le := hI.cur_le
    own_cur := hI.own_cur
    W_cur := hI.W_cur
    X_W := hI.X_W
    pend_pc := fun q hq => by
      by_cases e : q = p
      · subst e; simp [hg'] at hq
      · simp only [hg', Function.update_of_ne e] at hq
        rw [hpcq q e]; exact hI.pend_pc q hq
    cr_pc := fun q hq => by
      by_cases e : q = p
      · subst e; rw [hpcp] at hq; simp [CrPC] at hq
      · rw [hpcq q e] at hq; simpa [hg', Function.update_of_ne e] using hI.cr_pc q hq
    l3_cr := fun q hq => by
      by_cases e : q = p
      · subst e; rw [hpcp] at hq; cases hq
      · rw [hpcq q e] at hq; simpa [hg', Function.update_of_ne e] using hI.l3_cr q hq
    I_cr := fun q hq => by
      by_cases e : q = p
      · subst e; exact absurd hq hinIp'
      · simpa [hg', Function.update_of_ne e] using hI.I_cr q ((hinIq q e).1 hq)
    lost_wit := fun x hx hxC hA => by
      rcases hI.lost_wit x hx hxC hA with k | ⟨o, k1, k2, k3⟩
      · exact Or.inl k
      · right; refine ⟨o, k1, k2, ?_⟩
        by_cases e : o = p
        · subst e; rw [hcur] at k2; subst k2; rw [h4] at hA; cases hA
        · simpa [hg', Function.update_of_ne e] using k3
    phi_nonneg := by linarith [hPhi.1, hI.phi_nonneg]
    psi_bound := by
      rw [hPsi]
      have e1 : nR15 s' = nR15 s := by
        unfold nR15; congr 1; apply Finset.filter_congr; intro q _
        by_cases e : q = p
        · subst e; simp [hpcp, hpc]
        · rw [hpcq q e]
      rw [e1]; exact hI.psi_bound
    loc := fun q => by
      by_cases e : q = p
      · subst e; simp only [LI, hpcp, RetInv]; exact ⟨h1, h2, h3, h4⟩
      · exact LI_frame (hI.loc q) (hpcq q e) rfl (Or.inl rfl) le_rfl le_rfl (by simp [hs'])
          (fun _ _ => rfl) (fun x r h h' => by rw [h] at h'; cases h')
          rfl (by simp [hg', Function.update_of_ne e]) (by simp [hg', Function.update_of_ne e]) hJ }

theorem inv_step_r15 {s : Cfg P} {g : Ghost P} {p : P}  (hI : Inv s g)
    (hpc : s.pc p = .r15) : Inv (s.step p) (g.next s (.step p)) := by
  simp only [Cfg.step, Ghost.next, hpc]
  set s' : Cfg P := { s with D := s.D + 1, pc := Function.update s.pc p .r16 } with hs'
  set g' : Ghost P :=
    { g with pend := Function.update g.pend p false, cr := Function.update g.cr p true } with hg'
  have hpcq : ∀ q, q ≠ p → s'.pc q = s.pc q := fun q hq => by simp [hs', Function.update_of_ne hq]
  have hpcp : s'.pc p = .r16 := by simp [hs']
  have hinIq : ∀ q, q ≠ p → (inI s' g' q ↔ inI s g q) := fun q hq => by
    simp [inI, hs', hg', Function.update_of_ne hq]
  have hinIp' : ¬ inI s' g' p := by simp [inI, hg']
  have eI : Isize s' g' + (if inI s g p then 1 else 0) = Isize s g + 0 := by
    have := card_filter_update (inI s' g') (inI s g) p hinIq
    simp only [hinIp', if_false] at this; exact this
  have eC : crCount s' g' + (if (g.cr p = true ∧ s.A (g.cur p) ≠ .skipped) then 1 else 0) =
      crCount s g + (if s.A (g.cur p) ≠ .skipped then 1 else 0) := by
    have := card_filter_update (fun q => g'.cr q = true ∧ s'.A (g'.cur q) ≠ .skipped)
      (fun q => g.cr q = true ∧ s.A (g.cur q) ≠ .skipped) p
      (fun q hq => by simp [hs', hg', Function.update_of_ne hq])
    have h0 : (g'.cr p = true ∧ s'.A (g'.cur p) ≠ .skipped) ↔ s.A (g.cur p) ≠ .skipped := by
      simp [hg', hs']
    simp only [h0] at this; exact this
  have eR : nR15 s' + 1 = nR15 s := by
    have := card_filter_update (fun q => s'.pc q = .r15) (fun q => s.pc q = .r15) p
      (fun q hq => by rw [hpcq q hq])
    simp only [hpcp, hpc, if_true] at this
    have h0 : ¬ (PC.r16 : PC P) = .r15 := by simp
    simp only [h0, if_false, add_zero] at this
    exact this
  have ePhi' : Phi s' g' = (s.D : ℤ) + 1 + (Isize s' g' : ℤ) - s.C := by
    unfold Phi; rw [show s'.D = s.D + 1 from rfl, show s'.C = s.C from rfl]; push_cast; ring
  have hl : lostCount s' g' = lostCount s g := rfl
  have hPhi : Phi s g ≤ Phi s' g' ∧ Psi s' g' ≤ Psi s g + 2 := by
    unfold Psi; rw [ePhi', hl]; unfold Phi
    split_ifs at eI eC <;> constructor <;> push_cast <;> omega
  have hJ : ∀ ℓ, ℓ ≤ s.T → ℓ + 1 ≤ s.C → (JHyp s g ℓ → 1 ≤ Phi s g) →
      JHyp s' g' ℓ → 1 ≤ Phi s' g' := by
    rintro ℓ - - h ⟨hj1, o, ho, hoc⟩
    have ho' : inI s g o := by
      by_cases e : o = p
      · subst e; exact absurd ho hinIp'
      · exact (hinIq o e).1 ho
    have := h ⟨hj1, o, ho', hoc⟩
    linarith [hPhi.1]
  exact {
    T_le := hI.T_le
    A_ne := hI.A_ne
    A_tok := hI.A_tok
    done := hI.done
    grant := hI.grant
    future := fun q x hx hlt => by
      rcases hI.future q x hx hlt with k | ⟨k1, k2, k3, k4⟩
      · exact Or.inl k
      · refine Or.inr ⟨k1, k2, k3, ?_⟩
        by_cases e : q = p
        · subst e; simp [OnTrack, hpcp]
        · exact (OnTrack_congr (hpcq q e) rfl).2 k4
    own_claimed := hI.own_claimed
    own_le := hI.own_le
    own_ex := hI.own_ex
    cur_le := hI.cur_le
    own_cur := hI.own_cur
    W_cur := hI.W_cur
    X_W := hI.X_W
    pend_pc := fun q hq => by
      by_cases e : q = p
      · subst e; simp [hg'] at hq
      · simp only [hg', Function.update_of_ne e] at hq
        rw [hpcq q e]; exact hI.pend_pc q hq
    cr_pc := fun q hq => by
      by_cases e : q = p
      · subst e; right; simp [hg']
      · rw [hpcq q e] at hq; simpa [hg', Function.update_of_ne e] using hI.cr_pc q hq
    l3_cr := fun q hq => by
      by_cases e : q = p
      · subst e; rw [hpcp] at hq; cases hq
      · rw [hpcq q e] at hq; simpa [hg', Function.update_of_ne e] using hI.l3_cr q hq
    I_cr := fun q hq => by
      by_cases e : q = p
      · subst e; exact absurd hq hinIp'
      · simpa [hg', Function.update_of_ne e] using hI.I_cr q ((hinIq q e).1 hq)
    lost_wit := fun x hx hxC hA => by
      rcases hI.lost_wit x hx hxC hA with k | ⟨o, k1, k2, k3⟩
      · exact Or.inl k
      · right; refine ⟨o, k1, k2, ?_⟩
        by_cases e : o = p
        · subst e; right; simp [hg']
        · simpa [hg', Function.update_of_ne e] using k3
    phi_nonneg := by linarith [hPhi.1, hI.phi_nonneg]
    psi_bound := by
      have := hI.psi_bound
      have e2 : nSkipped s' = nSkipped s := rfl
      have e3 : g'.ncr = g.ncr := rfl
      rw [e2, e3]
      have : (nR15 s' : ℤ) + 1 = nR15 s := by exact_mod_cast eR
      linarith [hPhi.2]
    loc := fun q => by
      by_cases e : q = p
      · subst e; simp only [LI, hpcp]; simp [hg']
      · exact LI_frame (hI.loc q) (hpcq q e) rfl (Or.inl rfl) le_rfl le_rfl (by simp [hs'])
          (fun _ _ => rfl) (fun x r h h' => by rw [h] at h'; cases h')
          rfl (by simp [hg', Function.update_of_ne e]) (by simp [hg', Function.update_of_ne e]) hJ }

theorem inv_crash {s : Cfg P} {g : Ghost P} (hI : Inv s g) (p : P) :
    Inv (s.crash p) (g.next s (.crash p)) := by
  by_cases h0 : s.pc p = .rem
  · simp only [Cfg.crash, Ghost.next, h0, if_true]; exact hI
  simp only [Cfg.crash, Ghost.next, h0, if_false]
  set s' := s.setPc p .r15 with hs'
  set g' : Ghost P := { g with ncr := g.ncr + 1 } with hg'
  have hpcq : ∀ q, q ≠ p → s'.pc q = s.pc q := fun q hq => by simp [hs', Function.update_of_ne hq]
  have hpcp : s'.pc p = .r15 := by simp [hs']
  have eR : nR15 s' ≤ nR15 s + 1 := by
    have := card_filter_update (fun q => s'.pc q = .r15) (fun q => s.pc q = .r15) p
      (fun q hq => by rw [hpcq q hq])
    unfold nR15
    simp only [hpcp, if_true] at this
    split_ifs at this <;> omega
  exact {
    T_le := hI.T_le
    A_ne := hI.A_ne
    A_tok := hI.A_tok
    done := hI.done
    grant := hI.grant
    future := fun q x hx hlt => by
      rcases hI.future q x hx hlt with k | ⟨k1, k2, k3, k4⟩
      · exact Or.inl k
      · refine Or.inr ⟨k1, k2, k3, ?_⟩
        by_cases e : q = p
        · subst e; simp [OnTrack, hpcp]
        · exact (OnTrack_congr (hpcq q e) rfl).2 k4
    own_claimed := hI.own_claimed
    own_le := hI.own_le
    own_ex := hI.own_ex
    cur_le := hI.cur_le
    own_cur := hI.own_cur
    W_cur := hI.W_cur
    X_W := hI.X_W
    pend_pc := fun q hq => by
      by_cases e : q = p
      · subst e; left; rw [hpcp]; simp [PendPC]
      · rw [hpcq q e]; exact hI.pend_pc q hq
    cr_pc := fun q hq => by
      by_cases e : q = p
      · subst e; rw [hpcp] at hq; simp [CrPC] at hq
      · rw [hpcq q e] at hq; exact hI.cr_pc q hq
    l3_cr := fun q hq => by
      by_cases e : q = p
      · subst e; rw [hpcp] at hq; cases hq
      · rw [hpcq q e] at hq; exact hI.l3_cr q hq
    I_cr := hI.I_cr
    lost_wit := hI.lost_wit
    phi_nonneg := hI.phi_nonneg
    psi_bound := by
      have := hI.psi_bound
      have e1 : Psi s' g' = Psi s g := rfl
      have e2 : nSkipped s' = nSkipped s := rfl
      rw [e1, e2]
      have : (nR15 s' : ℤ) ≤ nR15 s + 1 := by exact_mod_cast eR
      simp only [hg']; push_cast; linarith
    loc := fun q => by
      by_cases e : q = p
      · subst e; simp only [LI, hpcp]
      · exact LI_frame (hI.loc q) (hpcq q e) rfl (Or.inl rfl) le_rfl le_rfl le_rfl
          (fun _ _ => rfl) (fun x r h h' => absurd (h.symm.trans h') (by simp))
          rfl rfl rfl (fun _ _ _ h => h) }

end Podc.RecoverableMutexRMR
