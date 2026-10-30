import Papers.PODC2020.RecoverableMutexRMR.InvQuiet

/-!
# Preservation of the invariant by Token moves and skips (lines 42, 46, 48)
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

/-- Moving `Token` from `T` to `T + 1` when ticket `T + 1` is skipped or done. -/
theorem inv_advance {s : Cfg P} {g : Ghost P} (hI : Inv s g)
    (h : s.A (s.T + 1) = .skipped ∨ ∃ q, s.A (s.T + 1) = .claimed q ∧ (s.W q).1 ≠ s.T + 1) :
    Inv { s with T := s.T + 1 } g := by
  set s' : Cfg P := { s with T := s.T + 1 } with hs'
  have hT' : s'.T = s.T + 1 := rfl
  have hne : s.A (s.T + 1) ≠ .empty := by rcases h with h | ⟨q, h, -⟩ <;> rw [h] <;> simp
  have nograntq : ∀ q, (s.W q).2 = true → False := by
    intro q hq
    obtain ⟨g1, g2⟩ := hI.grant q hq
    rcases h with h | ⟨q', h, h'⟩
    · rw [h] at g2; cases g2
    · rw [h] at g2; cases g2; exact h' g1
  exact {
    T_le := by rw [hT']; exact (hI.A_ne _ hne).2
    A_ne := hI.A_ne
    A_tok := fun x hx hxT => by
      rw [hT'] at hxT
      by_cases e : x = s.T + 1
      · subst e; exact hne
      · exact hI.A_tok x hx (by omega)
    done := fun x q hx hA => by
      rw [hT'] at hx
      by_cases e : x = s.T + 1
      · subst e
        rcases h with h | ⟨q', h, h'⟩
        · rw [h] at hA; cases hA
        · rw [h] at hA; cases hA; exact h'
      · exact hI.done x q (by omega) hA
    grant := fun q hq => (nograntq q hq).elim
    future := fun q x hx hlt => by
      rw [hT'] at hlt
      rcases hI.future q x hx (by omega) with k | ⟨k1, -⟩
      · exact Or.inl k
      · omega
    own_claimed := hI.own_claimed
    own_le := hI.own_le
    own_ex := hI.own_ex
    cur_le := hI.cur_le
    own_cur := hI.own_cur
    W_cur := hI.W_cur
    X_W := hI.X_W
    pend_pc := hI.pend_pc
    cr_pc := hI.cr_pc
    l3_cr := hI.l3_cr
    I_cr := hI.I_cr
    lost_wit := hI.lost_wit
    phi_nonneg := hI.phi_nonneg
    psi_bound := hI.psi_bound
    loc := fun q => LI_frame (hI.loc q) rfl rfl (Or.inl rfl) (by rw [hT']; omega) le_rfl le_rfl
      (fun _ _ => rfl) (fun x r h h' => by simp [hs', h'] at h) rfl rfl rfl (fun _ _ _ h => h) }

/-- The effect of a successful CAS of line 46 (skipping ticket `T + 1`). -/
theorem inv_skip {s : Cfg P} {g : Ghost P} {p : P} {r : Ret} (hI : Inv s g)
    (hpc : s.pc p = .m46 r s.T) (hA : s.A (s.T + 1) = .empty) :
    Inv { s with A := Function.update s.A (s.T + 1) .skipped } g := by
  set x0 := s.T + 1 with hx0
  set s' : Cfg P := { s with A := Function.update s.A x0 .skipped } with hs'
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, -, h3, h4⟩ := hL
  have hAx : ∀ x, x ≠ x0 → s'.A x = s.A x := fun x hx => by
    simp [hs', Function.update_of_ne hx]
  have hA0 : s'.A x0 = .skipped := by simp [hs']
  have hsk : ∀ x, s'.A x ≠ .skipped ↔ (s.A x ≠ .skipped ∧ x ≠ x0) := by
    intro x; by_cases e : x = x0
    · subst e; simp [hA0]
    · rw [hAx x e]; simp [e]
  have hemp : ∀ x, s'.A x = .empty ↔ (s.A x = .empty ∧ x ≠ x0) := by
    intro x; by_cases e : x = x0
    · subst e; simp [hA0]
    · rw [hAx x e]; simp [e]
  have hcl : ∀ x q, s'.A x = .claimed q ↔ s.A x = .claimed q := by
    intro x q; by_cases e : x = x0
    · subst e; simp [hA0, hA]
    · rw [hAx x e]
  have hne : ∀ x, s.A x ≠ .empty → s'.A x = s.A x := fun x hx =>
    hAx x (by rintro rfl; exact hx hA)
  have hx0C : x0 ≤ s.C := h3
  have hx00 : x0 ≠ 0 := by omega
  -- counting
  have hinI : ∀ q, inI s' g q ↔ (inI s g q ∧ ¬ g.cur q = x0) := by
    intro q; simp only [inI, ne_eq, hsk]; tauto
  set K := (Finset.univ.filter (fun q => inI s g q ∧ g.cur q = x0)).card with hK
  have eI : Isize s g = Isize s' g + K := by
    unfold Isize
    rw [card_filter_split Finset.univ (inI s g) (fun q => g.cur q = x0)]
    congr 2; ext q; simp [hinI]
  have uniq : ∀ a b : P, g.cur a = x0 → g.cur b = x0 → a = b := by
    intro a b ha hb
    have e1 := hI.own_cur a (by omega); have e2 := hI.own_cur b (by omega)
    rw [ha] at e1; rw [hb, e1] at e2; exact Option.some_injective _ e2
  have hK1 : K ≤ 1 := by
    rw [hK, Finset.card_le_one]
    intro a ha b hb; simp at ha hb; exact uniq a b ha.2 hb.2
  set K2 := (Finset.univ.filter (fun q => (g.cr q = true ∧ s.A (g.cur q) ≠ .skipped) ∧
    g.cur q = x0)).card with hK2
  have eCr : crCount s g = crCount s' g + K2 := by
    unfold crCount
    rw [card_filter_split Finset.univ (fun q => g.cr q = true ∧ s.A (g.cur q) ≠ .skipped)
      (fun q => g.cur q = x0)]
    congr 2; ext q; simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    have := hsk (g.cur q); simp only [ne_eq] at this; rw [this]; tauto
  set L := (g.lost.filter (fun x => s.A x = .empty ∧ x = x0)).card with hL'
  have eLost : lostCount s g = lostCount s' g + L := by
    unfold lostCount
    rw [card_filter_split g.lost (fun x => s.A x = .empty) (fun x => x = x0)]
    congr 2; ext x; simp [hemp]
  have eSk : nSkipped s' = nSkipped s + 1 := by
    unfold nSkipped
    rw [card_filter_split (Finset.range (s'.C + 1)) (fun x => s'.A x = .skipped) (fun x => x = x0)]
    have e1 : (Finset.range (s'.C + 1)).filter (fun x => s'.A x = .skipped ∧ ¬ x = x0) =
        (Finset.range (s.C + 1)).filter (fun x => s.A x = .skipped) := by
      ext x; by_cases e : x = x0
      · subst e; simp [hA]
      · simp [e, hAx x e, hs']
    have e2 : (Finset.range (s'.C + 1)).filter (fun x => s'.A x = .skipped ∧ x = x0) = {x0} := by
      ext x; by_cases e : x = x0
      · subst e; simp [hA0, hs']; omega
      · simp [e]
    rw [e1, e2, Finset.card_singleton]
  have hPhi : Phi s g = Phi s' g + K := by
    simp only [Phi, eI]; push_cast; simp [hs']; ring
  have hPhi' : 0 ≤ Phi s' g := by
    by_cases hK0 : K = 0
    · have := hI.phi_nonneg; rw [hPhi, hK0] at this; simpa using this
    · obtain ⟨o, ho⟩ : ∃ o, inI s g o ∧ g.cur o = x0 := by
        by_contra hno; push Not at hno
        apply hK0; rw [hK, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro q _ hq; exact hno q hq.1 hq.2
      have := h4 ⟨hA, o, ho⟩
      have hK' : K = 1 := by omega
      rw [hPhi, hK'] at this; push_cast at this; linarith
  have hwit : 1 ≤ K + K2 + L := by
    rcases hI.lost_wit x0 (by omega) hx0C hA with hl | ⟨o, -, ho, hpo⟩
    · have : 1 ≤ L := Finset.card_pos.2 ⟨x0, by simp [hl, hA]⟩
      omega
    · rcases hpo with hpo | hpo
      · have : 1 ≤ K := Finset.card_pos.2 ⟨o, Finset.mem_filter.2 ⟨Finset.mem_univ _,
          ⟨by rw [ho]; exact hx00, by rw [ho, hA]; simp, hpo⟩, ho⟩⟩
        omega
      · have : 1 ≤ K2 := Finset.card_pos.2 ⟨o, by simp [ho, hpo, hA, hx00]⟩
        omega
  have hJfalse : ∀ ℓ, ℓ ≤ s.T → JHyp s' g ℓ → False := by
    rintro ℓ hℓ ⟨hj, -⟩
    rw [hemp] at hj
    by_cases e : ℓ = s.T
    · exact hj.2 (by omega)
    · exact hI.A_tok (ℓ + 1) (by omega) (by omega) hj.1
  exact {
    T_le := hI.T_le
    A_ne := fun x hx => by
      by_cases e : x = x0
      · subst e; exact ⟨by omega, hx0C⟩
      · rw [hAx x e] at hx; exact hI.A_ne x hx
    A_tok := fun x hx hxT h => by
      rw [hemp] at h; exact hI.A_tok x hx hxT h.1
    done := fun x q hx h => hI.done x q hx ((hcl x q).1 h)
    grant := fun q hq => by
      obtain ⟨g1, g2⟩ := hI.grant q hq
      rw [hA] at g2; cases g2
    future := fun q x hx hlt => hI.future q x ((hcl x q).1 hx) hlt
    own_claimed := fun x q hx => hI.own_claimed x q ((hcl x q).1 hx)
    own_le := hI.own_le
    own_ex := hI.own_ex
    cur_le := hI.cur_le
    own_cur := hI.own_cur
    W_cur := hI.W_cur
    X_W := hI.X_W
    pend_pc := fun q hq => by
      rcases hI.pend_pc q hq with h | h
      · exact Or.inl h
      · right; by_contra hc; exact ((hsk _).1 hc).1 h
    cr_pc := hI.cr_pc
    l3_cr := hI.l3_cr
    I_cr := fun q hq => hI.I_cr q ((hinI q).1 hq).1
    lost_wit := fun x hx hxC h => hI.lost_wit x hx hxC ((hemp x).1 h).1
    phi_nonneg := hPhi'
    psi_bound := by
      have := hI.psi_bound
      have e3 : nR15 s' = nR15 s := rfl
      simp only [Psi] at this ⊢
      rw [hPhi, eCr, eLost] at this
      rw [eSk, e3]
      push_cast at this ⊢
      have : (1 : ℤ) ≤ K + K2 + L := by exact_mod_cast hwit
      linarith
    loc := fun q => LI_frame (hI.loc q) rfl rfl (Or.inl rfl) le_rfl le_rfl le_rfl hne
      (fun x r h h' => by rw [hcl] at h; rw [h] at h'; cases h') rfl rfl rfl
      (fun ℓ hℓ _ _ hj => (hJfalse ℓ hℓ hj).elim) }

theorem inv_step_m42 {s : Cfg P} {g : Ghost P} {p : P} {r : Ret} {ℓ : ℕ} (hI : Inv s g)
    (hpc : s.pc p = .m42 r ℓ) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, h2, h3, h4⟩ := hL
  simp only [Cfg.step, Ghost.next, hpc]
  by_cases hT : s.T = ℓ
  · subst hT
    rw [if_pos rfl]
    have hG := inv_advance hI (Or.inr ⟨p, h3, h4⟩)
    change Inv (({ s with T := s.T + 1 } : Cfg P).setPc p (.m34 r)) g
    refine inv_quiet hG (by simp [hpc]) (by simp) ?_ ?_ ?_ ?_ ?_
    · simp only [LI, setPc_pc, Function.update_self, RetInv_setPc]
      exact RetInv_frame h1 rfl (Or.inl rfl) (fun _ _ => rfl)
    · intro h; right; exact hG.skipped_of_pend (by simp [hpc, PendPC]) h
    · simp [CrPC]
    · simp
    · intro _ _ _ _ h
      cases r with
      | wr w => simp [OnTrack, hpc] at h
      | ex => simp [OnTrack]
  · rw [if_neg hT]
    refine inv_quiet hI (by simp [hpc]) (by simp) (LI_retpc h1) ?_ ?_ ?_ ?_
    · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
    · simp only [CrPC_retpc]; simp
    · simp
    · intro _ _ _ _ h
      cases r with
      | wr w => simp [OnTrack, hpc] at h
      | ex => simp [OnTrack, hpc] at h; try exact absurd h.symm hT

theorem inv_step_m46 {s : Cfg P} {g : Ghost P} {p : P} {r : Ret} {ℓ : ℕ} (hI : Inv s g)
    (hpc : s.pc p = .m46 r ℓ) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, h2, h3, h4⟩ := hL
  simp only [Cfg.step, Ghost.next, hpc]
  by_cases hA : s.A (ℓ + 1) = .empty
  · have hℓ : ℓ = s.T := by
      by_contra hne; exact hI.A_tok (ℓ + 1) (by omega) (by omega) hA
    subst hℓ
    rw [if_pos hA]
    have hG := inv_skip hI hpc hA
    change Inv (({ s with A := Function.update s.A (s.T + 1) .skipped } : Cfg P).setPc p
      (.m47 r s.T)) g
    refine inv_quiet hG (by simp [hpc]) (by simp) ?_ ?_ ?_ ?_ ?_
    · simp only [LI, setPc_pc, Function.update_self, RetInv_setPc, setPc_T, setPc_A]
      refine ⟨RetInv_frame h1 rfl (Or.inl rfl) ?_, le_rfl, by simp⟩
      intro x hx; by_cases e : x = s.T + 1
      · subst e; exact absurd hA hx
      · simp [Function.update_of_ne e]
    · intro h; right; exact hG.skipped_of_pend (by simp [hpc, PendPC]) h
    · simp [CrPC]
    · simp
    · intro _ _ _ _ h; cases r <;> simp [OnTrack, hpc] at h
  · rw [if_neg hA]
    change Inv (s.setPc p (.m47 r ℓ)) g
    refine inv_quiet hI (by simp [hpc]) (by simp) ?_ ?_ ?_ ?_ ?_
    · simp only [LI, setPc_pc, Function.update_self, RetInv_setPc, setPc_T, setPc_A]
      exact ⟨h1, h2, hA⟩
    · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
    · simp [CrPC]
    · simp
    · intro _ _ _ _ h; cases r <;> simp [OnTrack, hpc] at h

theorem inv_step_m48 {s : Cfg P} {g : Ghost P} {p : P} {r : Ret} {ℓ : ℕ} (hI : Inv s g)
    (hpc : s.pc p = .m48 r ℓ) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, h2, h3⟩ := hL
  simp only [Cfg.step, Ghost.next, hpc]
  by_cases hT : s.T = ℓ
  · subst hT
    rw [if_pos rfl]
    have hG := inv_advance hI (Or.inl h3)
    change Inv (({ s with T := s.T + 1 } : Cfg P).setPc p (.m34 r)) g
    refine inv_quiet hG (by simp [hpc]) (by simp) ?_ ?_ ?_ ?_ ?_
    · simp only [LI, setPc_pc, Function.update_self, RetInv_setPc]
      exact RetInv_frame h1 rfl (Or.inl rfl) (fun _ _ => rfl)
    · intro h; right; exact hG.skipped_of_pend (by simp [hpc, PendPC]) h
    · simp [CrPC]
    · simp
    · intro _ _ _ _ h
      cases r with
      | wr w => simp [OnTrack, hpc] at h
      | ex => simp [OnTrack]
  · rw [if_neg hT]
    refine inv_quiet hI (by simp [hpc]) (by simp) (LI_retpc h1) ?_ ?_ ?_ ?_
    · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
    · simp only [CrPC_retpc]; simp
    · simp
    · intro _ _ _ _ h
      cases r with
      | wr w => simp [OnTrack, hpc] at h
      | ex => simp [OnTrack, hpc] at h; try exact absurd h.symm hT

end Podc.RecoverableMutexRMR
