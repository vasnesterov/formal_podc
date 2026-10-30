import Papers.PODC2020.RecoverableMutexRMR.InvBasic

/-!
# Preservation of the invariant by steps that only read shared memory
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

/-- `W[p] ≠ (0,false)` implies a nonzero ticket. -/
lemma Inv.W_fst_ne_zero {s : Cfg P} {g : Ghost P} (hI : Inv s g) {p : P}
    (h : s.W p ≠ (0, false)) : (s.W p).1 ≠ 0 := by
  intro h0
  cases hb : (s.W p).2
  · exact h (Prod.ext h0 hb)
  · have := (hI.grant p hb).1; omega

lemma Inv.A_zero {s : Cfg P} {g : Ghost P} (hI : Inv s g) : s.A 0 = .empty := by
  by_contra h; exact (hI.A_ne 0 h).1 rfl

theorem inv_step_rem {s : Cfg P} {g : Ghost P} {p : P} (hI : Inv s g) (hpc : s.pc p = .rem) :
    Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_quiet hI (by simp [hpc]) (by simp) ?_ ?_ ?_ ?_ ?_
  · simp [LI, hL.2]
  · intro h; have := hI.pend_pc p h; simpa [hpc, PendPC] using this
  · simp [CrPC]
  · intro _; exact Or.inr (Or.inr hL.1)
  · intro _ _ _ _ h; simp [OnTrack, hpc] at h

theorem inv_step_l3 {s : Cfg P} {g : Ghost P} {p : P} (hI : Inv s g) (hpc : s.pc p = .l3) :
    Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_quiet hI (by simp [hpc]) (by split_ifs <;> simp) ?_ ?_ ?_ ?_ ?_
  · split_ifs with hW
    · simp [LI, hL, hW]
    · simp [LI, hL, hI.W_fst_ne_zero hW]
  · intro h; have := hI.pend_pc p h; simp [hpc, PendPC] at this; exact Or.inr this
  · split_ifs with hW
    · simp [CrPC]
    · intro _
      rcases hI.l3_cr p hpc with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hW
  · split_ifs <;> simp
  · intro _ _ _ _ h; simp [OnTrack, hpc] at h

lemma one_le_Isize {s : Cfg P} {g : Ghost P} {o : P} (h : inI s g o) : 1 ≤ Isize s g := by
  unfold Isize
  exact Finset.card_pos.2 ⟨o, by simp [h]⟩

lemma LI_retpc {s : Cfg P} {g : Ghost P} {p : P} {r : Ret} (h : RetInv s p r) :
    LI (s.setPc p r.pc) g p := by
  cases r with
  | wr w => simpa [LI, Ret.pc] using h
  | ex => simpa [LI, Ret.pc, RetInv] using h

@[simp] lemma PendPC_retpc (r : Ret) : PendPC (r.pc : PC P) ↔ False := by
  cases r <;> simp [PendPC, Ret.pc]

@[simp] lemma CrPC_retpc (r : Ret) : CrPC (r.pc : PC P) ↔ False := by
  cases r <;> simp [CrPC, Ret.pc]

@[simp] lemma retpc_ne_r15 (r : Ret) : (r.pc : PC P) ≠ .r15 := by
  cases r <;> simp [Ret.pc]

@[simp] lemma retpc_ne_l3 (r : Ret) : (r.pc : PC P) ≠ .l3 := by
  cases r <;> simp [Ret.pc]

/-- From `pend_pc` at a program counter that is not in `PendPC`. -/
lemma Inv.skipped_of_pend {s : Cfg P} {g : Ghost P} (hI : Inv s g) {p : P}
    (hk : ¬ PendPC (s.pc p)) : g.pend p = true → s.A (g.cur p) = .skipped := fun h =>
  (hI.pend_pc p h).resolve_left hk

theorem inv_step_w23 {s : Cfg P} {g : Ghost P} {p : P} (hI : Inv s g) (hpc : s.pc p = .w23) :
    Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_quiet hI (by simp [hpc]) (by simp) ?_ ?_ ?_ ?_ ?_
  · simp [LI, hL]
  · intro h; simp [PendPC]
  · intro _; simpa [hpc, CrPC] using hI.cr_pc p
  · simp
  · intro _ _ _ _ h; simp [OnTrack, hpc] at h

theorem inv_step_w25 {s : Cfg P} {g : Ghost P} {p : P} {w : ℕ} (hI : Inv s g)
    (hpc : s.pc p = .w25 w) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, h2, h3, h4⟩ := hL
  simp only [Cfg.step, Ghost.next, hpc]
  have hcur : g.cur p = w := by rw [← hI.W_cur p (by omega), h2]
  refine inv_quiet hI (by simp [hpc]) (by split_ifs <;> simp) ?_ ?_ ?_ ?_ ?_
  · split_ifs with hA
    · simp [LI, RetInv, h1, h2, h3, hA]
    · simp only [LI, setPc_pc, Function.update_self, setPc_X, setPc_W, setPc_A]
      refine ⟨h1, by rw [h2, hcur], by omega, ?_⟩
      rw [hcur]
      cases ha : s.A w with
      | empty => exact absurd ha h4
      | skipped => rfl
      | claimed r =>
        have e1 := hI.own_claimed _ _ ha
        have e2 := hI.own_cur p (by omega)
        rw [hcur, e1] at e2
        cases e2; exact absurd ha hA
  · intro h
    split_ifs with hA
    · simp [PendPC]
    · right
      rw [hcur]
      cases ha : s.A w with
      | empty => exact absurd ha h4
      | skipped => rfl
      | claimed r =>
        have e1 := hI.own_claimed _ _ ha
        have e2 := hI.own_cur p (by omega)
        rw [hcur, e1] at e2
        cases e2; exact absurd ha hA
  · intro _; simpa [hpc, CrPC] using hI.cr_pc p
  · split_ifs <;> simp
  · intro _ _ _ _ h; simp [OnTrack, hpc] at h

theorem inv_step_w31 {s : Cfg P} {g : Ghost P} {p : P} {w : ℕ} (hI : Inv s g)
    (hpc : s.pc p = .w31 w) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_quiet hI (by simp [hpc]) (by split_ifs <;> simp) ?_ ?_ ?_ ?_ ?_
  · split_ifs with hW
    · simp [LI, RetInv] at hL ⊢; simp [hL.1, hW]
    · simpa [LI] using hL
  · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
  · split_ifs <;> simp [CrPC]
  · split_ifs <;> simp
  · intro _ _ _ _ h; simp [OnTrack, hpc] at h

theorem inv_step_cs {s : Cfg P} {g : Ghost P} {p : P} (hI : Inv s g)
    (hpc : s.pc p = .cs) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_quiet hI (by simp [hpc]) (by simp) ?_ ?_ ?_ ?_ ?_
  · simp [LI, hL.2]
  · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
  · simp [CrPC]
  · simp
  · intro _ _ _ _ h; simp [OnTrack, hpc] at h

theorem inv_step_r16 {s : Cfg P} {g : Ghost P} {p : P} (hI : Inv s g)
    (hpc : s.pc p = .r16) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_quiet hI (by simp [hpc]) (by split_ifs <;> simp) ?_ ?_ ?_ ?_ ?_
  · split_ifs with hX
    · simp only [LI, setPc_pc, Function.update_self, setPc_W, setPc_X]
      rcases hI.X_W p hX with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hX⟩
    · simp [LI, hL]; simpa using hX
  · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
  · split_ifs <;> simp [CrPC, hL]
  · split_ifs <;> simp
  · intro _ _ _ hX _
    simp [hX, OnTrack]

theorem inv_step_r18 {s : Cfg P} {g : Ghost P} {p : P} (hI : Inv s g)
    (hpc : s.pc p = .r18) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_quiet hI (by simp [hpc]) (by split_ifs <;> simp) ?_ ?_ ?_ ?_ ?_
  · split_ifs with hW
    · simp [LI, hL.1, hW]
    · simp [LI, hL.1]
  · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
  · split_ifs <;> simp [CrPC]
  · intro _; exact Or.inr (Or.inl hL.2)
  · intro _ _ _ _ h; simp [OnTrack, hpc] at h

theorem inv_step_m34 {s : Cfg P} {g : Ghost P} {p : P} {r : Ret} (hI : Inv s g)
    (hpc : s.pc p = .m34 r) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_quiet hI (by simp [hpc]) (by simp) ?_ ?_ ?_ ?_ ?_
  · simp only [LI, setPc_pc, Function.update_self]
    exact ⟨RetInv_frame hL rfl (Or.inl rfl) (fun _ _ => rfl), le_rfl⟩
  · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
  · simp [CrPC]
  · simp
  · intro _ _ _ _ h
    cases r <;> simp [OnTrack, hpc] at h ⊢

theorem inv_step_m35 {s : Cfg P} {g : Ghost P} {p : P} {r : Ret} {ℓ : ℕ} (hI : Inv s g)
    (hpc : s.pc p = .m35 r ℓ) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_quiet hI (by simp [hpc]) (by simp) ?_ ?_ ?_ ?_ ?_
  · simp only [LI, setPc_pc, Function.update_self, setPc_T, setPc_D]
    exact ⟨RetInv_frame hL.1 rfl (Or.inl rfl) (fun _ _ => rfl), hL.2, le_rfl⟩
  · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
  · simp [CrPC]
  · simp
  · intro _ _ _ _ h
    cases r <;> simp [OnTrack, hpc] at h ⊢; exact h

theorem inv_step_m36 {s : Cfg P} {g : Ghost P} {p : P} {r : Ret} {ℓ d : ℕ} (hI : Inv s g)
    (hpc : s.pc p = .m36 r ℓ d) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, h2, h3⟩ := hL
  have h1' : RetInv (s.setPc p (PC.m38 r ℓ s.C d)) p r := RetInv_frame h1 rfl (Or.inl rfl) (fun _ _ => rfl)
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_quiet hI (by simp [hpc]) (by split_ifs <;> simp) ?_ ?_ ?_ ?_ ?_
  · split_ifs with hc
    · simp only [LI, setPc_pc, Function.update_self, setPc_T, setPc_D, setPc_C]
      refine ⟨h1', h2, hc, le_rfl, h3, fun hcd hJ => ?_⟩
      obtain ⟨-, o, ho, -⟩ := hJ
      have := one_le_Isize ho
      show 1 ≤ Phi (s.setPc p _) g
      simp only [Phi, setPc_D, setPc_C]
      have : Isize (s.setPc p (PC.m38 r ℓ s.C d)) g = Isize s g := rfl
      push_cast; omega
    · exact LI_retpc h1
  · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
  · split_ifs <;> first | (simp only [CrPC_retpc]; simp) | simp [CrPC]
  · split_ifs <;> simp
  · intro hA _ _ _ h
    cases r with
    | wr w => simp [OnTrack, hpc] at h
    | ex =>
      simp [OnTrack, hpc] at h
      have := (hI.A_ne (s.T + 1) (by simp [hA])).2
      have hc : s.T < s.C := by omega
      subst h
      simp [hc, OnTrack]

theorem inv_step_m38 {s : Cfg P} {g : Ghost P} {p : P} {r : Ret} {ℓ c d : ℕ} (hI : Inv s g)
    (hpc : s.pc p = .m38 r ℓ c d) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_quiet hI (by simp [hpc]) (by split <;> (try split_ifs) <;> simp) ?_ ?_ ?_ ?_ ?_
  · split
    · rename_i q hq
      simp only [LI, setPc_pc, Function.update_self, setPc_T, setPc_A]
      exact ⟨RetInv_frame h1 rfl (Or.inl rfl) (fun _ _ => rfl), h2, hq⟩
    · split_ifs with hcd
      · simp only [LI, setPc_pc, Function.update_self, setPc_T, setPc_C]
        exact ⟨RetInv_frame h1 rfl (Or.inl rfl) (fun _ _ => rfl), h2, by omega, h6 hcd⟩
      · exact LI_retpc h1
  · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
  · split <;> (try split_ifs) <;> first | (simp only [CrPC_retpc]; simp) | simp [CrPC]
  · split <;> (try split_ifs) <;> simp
  · intro hA _ _ _ h
    cases r with
    | wr w => simp [OnTrack, hpc] at h
    | ex =>
      simp [OnTrack, hpc] at h
      subst h
      simp [hA, OnTrack]

theorem inv_step_m41 {s : Cfg P} {g : Ghost P} {p : P} {r : Ret} {ℓ : ℕ} {q : P} (hI : Inv s g)
    (hpc : s.pc p = .m41 r ℓ q) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, h2, h3, h4⟩ := hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_quiet hI (by simp [hpc]) (by split_ifs <;> simp) ?_ ?_ ?_ ?_ ?_
  · split_ifs with hc
    · obtain ⟨hW, rfl⟩ := hc
      simp only [LI, setPc_pc, Function.update_self, setPc_T, setPc_A, setPc_W]
      refine ⟨RetInv_frame h1 rfl (Or.inl rfl) (fun _ _ => rfl), h2, h3, fun e => ?_⟩
      cases hb : (s.W p).2
      · exact h4 rfl (Prod.ext e hb)
      · exact hW (Prod.ext e hb)
    · exact LI_retpc h1
  · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
  · split_ifs <;> first | (simp only [CrPC_retpc]; simp) | simp [CrPC]
  · split_ifs <;> simp
  · intro hA _ hW0 _ h
    cases r with
    | wr w => simp [OnTrack, hpc] at h
    | ex =>
      simp [OnTrack, hpc] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hW0, OnTrack]

theorem inv_step_m47 {s : Cfg P} {g : Ghost P} {p : P} {r : Ret} {ℓ : ℕ} (hI : Inv s g)
    (hpc : s.pc p = .m47 r ℓ) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, h2, h3⟩ := hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_quiet hI (by simp [hpc]) (by split_ifs <;> simp) ?_ ?_ ?_ ?_ ?_
  · split_ifs with hc
    · simp only [LI, setPc_pc, Function.update_self, setPc_T, setPc_A]
      exact ⟨RetInv_frame h1 rfl (Or.inl rfl) (fun _ _ => rfl), h2, hc⟩
    · exact LI_retpc h1
  · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
  · split_ifs <;> first | (simp only [CrPC_retpc]; simp) | simp [CrPC]
  · split_ifs <;> simp
  · intro _ _ _ _ h
    cases r <;> simp [OnTrack, hpc] at h

end Podc.RecoverableMutexRMR
