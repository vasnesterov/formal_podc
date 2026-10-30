import Papers.PODC2020.RecoverableMutexRMR.InvQuiet

/-!
# Preservation of the invariant by writes of W and Exit (lines 5, 24, 26, 9, 10, 12, 40)
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

/-- Steps that change only the local state of `p` and its own entries `W[p]`, `Exit[p]`. -/
theorem inv_local {s s' : Cfg P} {g : Ghost P} {p : P} (hI : Inv s g)
    (hC : s'.C = s.C) (hD : s'.D = s.D) (hT : s'.T = s.T) (hA : s'.A = s.A)
    (hW : ∀ q, q ≠ p → s'.W q = s.W q) (hX : ∀ q, q ≠ p → s'.X q = s.X q)
    (hpc : ∀ q, q ≠ p → s'.pc q = s.pc q)
    (hR : s.pc p ≠ .r15) (hR' : s'.pc p ≠ .r15)
    (done_p : ∀ x, x ≤ s.T → s.A x = .claimed p → (s'.W p).1 ≠ x)
    (grant_p : (s'.W p).2 = true → (s'.W p).1 = s.T + 1 ∧ s.A (s.T + 1) = .claimed p)
    (future_p : Future s' p)
    (W_cur_p : (s'.W p).1 ≠ 0 → (s'.W p).1 = g.cur p)
    (X_W_p : s'.X p = true → (s'.W p).2 = true ∨ s'.W p = (0, false))
    (pend_p : g.pend p = true → PendPC (s'.pc p) ∨ s.A (g.cur p) = .skipped)
    (cr_p : CrPC (s'.pc p) → g.pend p = true ∨ g.cr p = true)
    (l3_p : s'.pc p = .l3 → g.pend p = true ∨ g.cr p = true ∨ s'.W p = (0, false))
    (LI_p : LI s' g p) :
    Inv s' g where
  T_le := by rw [hT, hC]; exact hI.T_le
  A_ne := by rw [hA, hC]; exact hI.A_ne
  A_tok := by rw [hA, hT]; exact hI.A_tok
  done x q := by
    rw [hT, hA]
    by_cases hq : q = p
    · subst hq; exact done_p x
    · rw [hW q hq]; exact hI.done x q
  grant q := by
    rw [hT, hA]
    by_cases hq : q = p
    · subst hq; exact grant_p
    · rw [hW q hq]; exact hI.grant q
  future q := by
    by_cases hq : q = p
    · subst hq; exact future_p
    · intro x hx hlt
      rw [hA] at hx; rw [hT] at hlt ⊢
      rw [hW q hq, hX q hq]
      rcases hI.future q x hx hlt with h | ⟨h1, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2, h3, (OnTrack_congr (hpc q hq) hT).2 h4⟩
  own_claimed := by rw [hA]; exact hI.own_claimed
  own_le := by rw [hC]; exact hI.own_le
  own_ex := by rw [hC]; exact hI.own_ex
  cur_le := by rw [hC]; exact hI.cur_le
  own_cur := hI.own_cur
  W_cur q := by
    by_cases hq : q = p
    · subst hq; exact W_cur_p
    · rw [hW q hq]; exact hI.W_cur q
  X_W q := by
    by_cases hq : q = p
    · subst hq; exact X_W_p
    · rw [hW q hq, hX q hq]; exact hI.X_W q
  pend_pc q := by
    rw [hA]
    by_cases hq : q = p
    · subst hq; exact pend_p
    · rw [hpc q hq]; exact hI.pend_pc q
  cr_pc q := by
    by_cases hq : q = p
    · subst hq; exact cr_p
    · rw [hpc q hq]; exact hI.cr_pc q
  l3_cr q := by
    by_cases hq : q = p
    · subst hq; exact l3_p
    · rw [hpc q hq, hW q hq]; exact hI.l3_cr q
  I_cr q := by
    have : inI s' g q ↔ inI s g q := by simp [inI, hA]
    rw [this]; exact hI.I_cr q
  lost_wit := by rw [hC, hA]; exact hI.lost_wit
  phi_nonneg := by
    rw [Phi_congr hA hC hD]; exact hI.phi_nonneg
  psi_bound := by
    have h1 : Psi s' g = Psi s g := Psi_congr hA hC hD
    have h2 : nR15 s' = nR15 s := by
      unfold nR15; congr 1; apply Finset.filter_congr; intro q _
      by_cases hq : q = p
      · subst hq; simp [hR, hR']
      · rw [hpc q hq]
    have h3 : nSkipped s' = nSkipped s := by simp [nSkipped, hA, hC]
    rw [h1, h2, h3]; exact hI.psi_bound
  loc q := by
    by_cases hq : q = p
    · subst hq; exact LI_p
    · have hJ : ∀ ℓ, ℓ ≤ s.T → ℓ + 1 ≤ s.C → (JHyp s g ℓ → 1 ≤ Phi s g) →
          JHyp s' g ℓ → 1 ≤ Phi s' g := by
        intro ℓ _ _ h hj
        have e1 : Phi s' g = Phi s g := Phi_congr hA hC hD
        have e2 : JHyp s' g ℓ ↔ JHyp s g ℓ := by simp [JHyp, inI, hA]
        rw [e1]; exact h (e2.1 hj)
      exact LI_frame (hI.loc q) (hpc q hq) (hX q hq) (by rw [hW q hq]; exact Or.inl rfl)
        (by rw [hT]) (by rw [hC]) (by rw [hD]) (fun _ _ => by rw [hA])
        (fun x r h h' => by rw [hA] at h; simp [h'] at h) rfl rfl rfl hJ

/-- The effect of a successful CAS of line 40 (performed by anybody) on the invariant. -/
theorem inv_grant {s : Cfg P} {g : Ghost P} {q : P} (hI : Inv s g)
    (hW : s.W q = (s.T + 1, false)) (hA : s.A (s.T + 1) = .claimed q) :
    Inv { s with W := Function.update s.W q (s.T + 1, true) } g := by
  set s' : Cfg P := { s with W := Function.update s.W q (s.T + 1, true) } with hs'
  have hWf : ∀ r, WFrame (s.W r) (s'.W r) := by
    intro r
    by_cases hr : r = q
    · subst hr; right; exact ⟨s.T + 1, by omega, hW, by simp [hs']⟩
    · left; simp [hs', Function.update_of_ne hr]
  have hfst : ∀ r, (s'.W r).1 = (s.W r).1 := fun r => (hWf r).fst
  exact {
    T_le := hI.T_le
    A_ne := hI.A_ne
    A_tok := hI.A_tok
    done := fun x r hx h => by rw [hfst]; exact hI.done x r hx h
    grant := fun r hr => by
      by_cases h : r = q
      · subst h; simp [hs', hA]
      · have : s'.W r = s.W r := by simp [hs', Function.update_of_ne h]
        rw [this] at hr ⊢; exact hI.grant r hr
    future := fun r x hx hlt => by
      rcases hI.future r x hx hlt with h | ⟨h1, h2, h3, h4⟩
      · exact Or.inl (by rw [hfst]; exact h)
      · exact Or.inr ⟨h1, (hWf r).zero.2 h2, h3, h4⟩
    own_claimed := hI.own_claimed
    own_le := hI.own_le
    own_ex := hI.own_ex
    cur_le := hI.cur_le
    own_cur := hI.own_cur
    W_cur := fun r => by rw [hfst]; exact hI.W_cur r
    X_W := fun r hr => by
      rcases hI.X_W r hr with h | h
      · exact Or.inl ((hWf r).snd h)
      · exact Or.inr ((hWf r).zero.2 h)
    pend_pc := hI.pend_pc
    cr_pc := hI.cr_pc
    l3_cr := fun r hr => by rw [(hWf r).zero]; exact hI.l3_cr r hr
    I_cr := hI.I_cr
    lost_wit := hI.lost_wit
    phi_nonneg := hI.phi_nonneg
    psi_bound := hI.psi_bound
    loc := fun r => LI_frame (hI.loc r) rfl rfl (hWf r) le_rfl le_rfl le_rfl (fun _ _ => rfl)
      (fun x r' h h' => by simp [hs', h'] at h) rfl rfl rfl (fun _ _ _ h => h) }

/-- The effect of a successful CAS of line 24 by `p` (at line 24 with ticket `w`). -/
theorem inv_claim {s : Cfg P} {g : Ghost P} {p : P} {w : ℕ} (hI : Inv s g)
    (hpc : s.pc p = .w24 w) (hA : s.A w = .empty) :
    Inv { s with A := Function.update s.A w (.claimed p) } g := by
  set s' : Cfg P := { s with A := Function.update s.A w (.claimed p) } with hs'
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, h2, h3⟩ := hL
  have hcur : g.cur p = w := by rw [← hI.W_cur p (by omega), h2]
  have hown : g.own w = some p := hcur ▸ hI.own_cur p (by omega)
  have hwC : w ≤ s.C := hcur ▸ hI.cur_le p
  have hwT : s.T < w := by
    by_contra h; exact hI.A_tok w h3 (by omega) hA
  have hAx : ∀ x, x ≠ w → s'.A x = s.A x := fun x hx => by simp [hs', Function.update_of_ne hx]
  have hAw : s'.A w = .claimed p := by simp [hs']
  have hsk : ∀ x, s'.A x = .skipped ↔ s.A x = .skipped := by
    intro x; by_cases hx : x = w
    · subst hx; simp [hAw, hA]
    · rw [hAx x hx]
  have hne : ∀ x, s.A x ≠ .empty → s'.A x = s.A x := by
    intro x hx; exact hAx x (by rintro rfl; exact hx hA)
  have hT' : s'.T = s.T := rfl
  have hPhi : Phi s' g = Phi s g := by unfold Phi; rw [Isize_congr' hsk]
  have hJ : ∀ ℓ, (JHyp s g ℓ → 1 ≤ Phi s g) → JHyp s' g ℓ → 1 ≤ Phi s' g := by
    intro ℓ h ⟨hj1, o, ho, hoc⟩
    rw [hPhi]; refine h ⟨?_, o, ?_, hoc⟩
    · by_cases hx : ℓ + 1 = w
      · rw [hx] at hj1 ⊢; rw [hAw] at hj1; cases hj1
      · rwa [hAx _ hx] at hj1
    · simpa [inI, hsk] using ho
  exact {
    T_le := hI.T_le
    A_ne := fun x hx => by
      by_cases h : x = w
      · subst h; exact ⟨h3, hwC⟩
      · rw [hAx x h] at hx; exact hI.A_ne x hx
    A_tok := fun x hx hxT h => by
      rw [hT'] at hxT
      by_cases hxw : x = w
      · omega
      · rw [hAx x hxw] at h; exact hI.A_tok x hx hxT h
    done := fun x q hx h => by
      rw [hT'] at hx
      by_cases hxw : x = w
      · omega
      · rw [hAx x hxw] at h; exact hI.done x q hx h
    grant := fun q hq => by
      obtain ⟨g1, g2⟩ := hI.grant q hq
      refine ⟨g1, ?_⟩
      rw [hT', hne _ (by simp [g2])]; exact g2
    future := fun q x hx hlt => by
      by_cases hxw : x = w
      · subst hxw; rw [hAw] at hx; cases hx; exact Or.inl h2
      · rw [hAx x hxw] at hx
        rcases hI.future q x hx hlt with h | ⟨k1, k2, k3, k4⟩
        · exact Or.inl h
        · exact Or.inr ⟨k1, k2, k3, (OnTrack_congr rfl rfl).2 k4⟩
    own_claimed := fun x q hx => by
      by_cases hxw : x = w
      · subst hxw; rw [hAw] at hx; cases hx; exact hown
      · rw [hAx x hxw] at hx; exact hI.own_claimed x q hx
    own_le := hI.own_le
    own_ex := hI.own_ex
    cur_le := hI.cur_le
    own_cur := hI.own_cur
    W_cur := hI.W_cur
    X_W := hI.X_W
    pend_pc := fun q hq => by
      rcases hI.pend_pc q hq with h | h
      · exact Or.inl h
      · exact Or.inr ((hsk _).2 h)
    cr_pc := hI.cr_pc
    l3_cr := hI.l3_cr
    I_cr := fun q hq => hI.I_cr q (by simpa [inI, hsk] using hq)
    lost_wit := fun x hx hxC h => by
      by_cases hxw : x = w
      · subst hxw; rw [hAw] at h; cases h
      · rw [hAx x hxw] at h; exact hI.lost_wit x hx hxC h
    phi_nonneg := by rw [hPhi]; exact hI.phi_nonneg
    psi_bound := by
      have e1 : Psi s' g ≤ Psi s g := by
        simp only [Psi, hPhi, crCount_congr' hsk]
        have : lostCount s' g ≤ lostCount s g := by
          unfold lostCount
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          refine ⟨hx.1, ?_⟩
          by_cases hxw : x = w
          · subst hxw; exact hA
          · rw [← hAx x hxw]; exact hx.2
        push_cast; omega
      have e2 : nSkipped s' = nSkipped s := by
        unfold nSkipped; congr 1; apply Finset.filter_congr; intro x _; exact hsk x
      have e3 : nR15 s' = nR15 s := rfl
      have := hI.psi_bound
      rw [e2, e3]; linarith
    loc := fun q => by
      by_cases hq : q = p
      · subst hq; simp only [LI, hs', hpc]; exact ⟨h1, h2, h3⟩
      · exact LI_frame (hI.loc q) rfl rfl (Or.inl rfl) le_rfl le_rfl le_rfl hne
          (fun x r h h' => by
            by_cases hxw : x = w
            · subst hxw
              intro e
              have := hI.own_cur q (by rw [← e]; exact h3)
              rw [← e, hown] at this; cases this; exact hq rfl
            · rw [hAx x hxw] at h; rw [h] at h'; cases h')
          rfl rfl rfl (fun ℓ _ _ h => hJ ℓ h) }

theorem inv_step_l5 {s : Cfg P} {g : Ghost P} {p : P} {c : ℕ} (hI : Inv s g)
    (hpc : s.pc p = .l5 c) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL
  simp only [Cfg.step, Ghost.next, hpc, h2, if_true]
  have hcA : ∀ q, s.A c ≠ .claimed q := by
    intro q hq; rcases h5 with h5 | h5 <;> rw [h5] at hq <;> cases hq
  refine inv_local (p := p) hI rfl rfl rfl rfl (fun q hq => by simp [Function.update_of_ne hq])
    (fun _ _ => rfl) (fun q hq => by simp [Function.update_of_ne hq])
    (by simp [hpc]) (by simp) ?_ (by simp) ?_ (by intro _; simp [h3]) (by simp [h1]) ?_ ?_ ?_ ?_
  · intro x hx hA; simp
    intro e; subst e; exact hcA p hA
  · intro x hx hlt
    rcases hI.future p x hx hlt with h | ⟨h1', h2', h3', h4'⟩
    · rw [h2] at h; simp at h; subst h
      exact absurd hx (by simp [hI.A_zero])
    · rw [h1] at h3'; cases h3'
  · intro _; simp [PendPC]
  · intro _; exact Or.inl h6
  · simp
  · simp [LI, h1]; exact h4

theorem inv_step_w24 {s : Cfg P} {g : Ghost P} {p : P} {w : ℕ} (hI : Inv s g)
    (hpc : s.pc p = .w24 w) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, h2, h3⟩ := hL
  simp only [Cfg.step, Ghost.next, hpc]
  have key : ∀ s' : Cfg P, Inv s' g → s'.pc = s.pc → s'.X = s.X → s'.W = s.W →
      s'.A w ≠ .empty → Inv (s'.setPc p (.w25 w)) g := by
    intro s' hI' hpc' hX' hW' hAw
    refine inv_quiet hI' (by simp [hpc', hpc]) (by simp) ?_ ?_ ?_ ?_ ?_
    · simp only [LI, setPc_pc, Function.update_self, setPc_X, setPc_W, setPc_A]
      exact ⟨hX' ▸ h1, hW' ▸ h2, h3, hAw⟩
    · intro _; simp [PendPC]
    · intro _; simpa [hpc', hpc, CrPC] using hI'.cr_pc p
    · simp
    · intro _ _ _ _ h; simp [OnTrack, hpc', hpc] at h
  by_cases hA : s.A w = .empty
  · rw [if_pos hA]
    exact key _ (inv_claim hI hpc hA) rfl rfl rfl (by simp)
  · rw [if_neg hA]
    exact key s hI rfl rfl rfl hA

theorem inv_step_w26 {s : Cfg P} {g : Ghost P} {p : P}  (hI : Inv s g)
    (hpc : s.pc p = .w26) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, h2, h3, h4⟩ := hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_local (p := p) hI rfl rfl rfl rfl (fun q hq => by simp [Function.update_of_ne hq])
    (fun _ _ => rfl) (fun q hq => by simp [Function.update_of_ne hq])
    (by simp [hpc]) (by simp) ?_ (by simp) ?_ (by simp) (by simp [h1]) ?_ ?_ ?_ ?_
  · intro x hx hA; simp
    intro h0; subst h0; rw [hI.A_zero] at hA; cases hA
  · intro x hx hlt
    rcases hI.future p x hx hlt with h | ⟨h1', h2', h3', h4'⟩
    · rw [h2] at h; subst h; rw [h4] at hx; cases hx
    · rw [h1] at h3'; cases h3'
  · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
  · simp [CrPC]
  · simp
  · simp [LI, h1]

theorem inv_step_x9 {s : Cfg P} {g : Ghost P} {p : P}  (hI : Inv s g)
    (hpc : s.pc p = .x9) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_local (p := p) hI rfl rfl rfl rfl (fun _ _ => rfl)
    (fun q hq => by simp [Function.update_of_ne hq]) (fun q hq => by simp [Function.update_of_ne hq])
    (by simp [hpc]) (by simp) (hI.done · p) (hI.grant p) ?_ (hI.W_cur p) ?_ ?_ ?_ ?_ ?_
  · intro x hx hlt
    rcases hI.future p x hx hlt with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, by simp, by simp [OnTrack]⟩
  · intro _
    rcases hL with h | ⟨h1, _⟩
    · exact Or.inl h
    · exact Or.inr h1
  · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
  · simp [CrPC]
  · simp
  · simp [LI]

theorem inv_step_x10 {s : Cfg P} {g : Ghost P} {p : P}  (hI : Inv s g)
    (hpc : s.pc p = .x10) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  simp only [Cfg.step, Ghost.next, hpc]
  have hXW := hI.X_W p hL
  refine inv_local (p := p) hI rfl rfl rfl rfl (fun q hq => by simp [Function.update_of_ne hq])
    (fun _ _ => rfl) (fun q hq => by simp [Function.update_of_ne hq])
    (by simp [hpc]) (by simp) ?_ (by simp) ?_ (by simp) (by simp) ?_ ?_ ?_ ?_
  · intro x hx hA; simp
    intro h0; subst h0; rw [hI.A_zero] at hA; cases hA
  · intro x hx hlt
    simp only [Function.update_self]
    rcases hI.future p x hx hlt with h | ⟨h1, h2, h3, h4⟩
    · -- `W[p]` held `x > T`; by `grant` / `W = (0,false)` this is `T + 1`
      rcases hXW with h' | h'
      · have := (hI.grant p h').1
        right; refine ⟨by omega, by simp, by simp [hL], by simp [OnTrack]⟩
      · rw [h'] at h; simp at h; subst h
        exact absurd hx (by simp [hI.A_zero])
    · exact Or.inr ⟨h1, by simp, by simp [hL], by simp [OnTrack]⟩
  · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
  · simp [CrPC]
  · simp
  · simp [LI, RetInv, hL]

theorem inv_step_x12 {s : Cfg P} {g : Ghost P} {p : P}  (hI : Inv s g)
    (hpc : s.pc p = .x12) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  simp only [Cfg.step, Ghost.next, hpc]
  refine inv_local (p := p) hI rfl rfl rfl rfl (fun _ _ => rfl)
    (fun q hq => by simp [Function.update_of_ne hq]) (fun q hq => by simp [Function.update_of_ne hq])
    (by simp [hpc]) (by simp) (hI.done · p) (hI.grant p) ?_ (hI.W_cur p) ?_ ?_ ?_ ?_ ?_
  · intro x hx hlt
    rcases hI.future p x hx hlt with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · simp [OnTrack, hpc] at h4
  · simp
  · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
  · simp [CrPC]
  · simp
  · simp [LI, hL.2]

theorem inv_step_m40 {s : Cfg P} {g : Ghost P} {p : P} {r : Ret} {ℓ : ℕ} {q : P} (hI : Inv s g)
    (hpc : s.pc p = .m40 r ℓ q) : Inv (s.step p) (g.next s (.step p)) := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, h2, h3⟩ := hL
  simp only [Cfg.step, Ghost.next, hpc]
  by_cases hW : s.W q = (ℓ + 1, false)
  · -- successful grant: necessarily `ℓ = T`
    have hℓ : ℓ = s.T := by
      by_contra hne
      exact hI.done (ℓ + 1) q (by omega) h3 (by rw [hW])
    subst hℓ
    have hG := inv_grant hI hW h3
    rw [if_pos hW]
    change Inv (({ s with W := Function.update s.W q (s.T + 1, true) } : Cfg P).setPc p
      (.m41 r s.T q)) g
    have hpc' : ({ s with W := Function.update s.W q (s.T + 1, true) } : Cfg P).pc p
        = .m40 r s.T q := hpc
    refine inv_quiet hG (by simp [hpc]) (by simp) ?_ ?_ ?_ ?_ ?_
    · simp only [LI, setPc_pc, Function.update_self, setPc_T, setPc_A, setPc_W, RetInv_setPc]
      refine ⟨RetInv_frame h1 rfl ?_ (fun _ _ => rfl), le_rfl, h3, ?_⟩
      · by_cases hq : p = q
        · subst hq; right; exact ⟨s.T + 1, by omega, hW, by simp⟩
        · left; simp [Function.update_of_ne hq]
      · intro e; subst e; simp
    · intro h; right; exact hG.skipped_of_pend (by simp [hpc, PendPC]) h
    · simp [CrPC]
    · simp
    · intro _ _ _ _ h
      cases r with
      | wr w => simp [OnTrack, hpc] at h
      | ex => simp [OnTrack, hpc] at h ⊢; exact h
  · rw [if_neg hW]
    change Inv (s.setPc p (.m41 r ℓ q)) g
    refine inv_quiet hI (by simp [hpc]) (by simp) ?_ ?_ ?_ ?_ ?_
    · simp only [LI, setPc_pc, Function.update_self, setPc_T, setPc_A, setPc_W, RetInv_setPc]
      exact ⟨h1, h2, h3, fun e => by subst e; exact hW⟩
    · intro h; right; exact hI.skipped_of_pend (by simp [hpc, PendPC]) h
    · simp [CrPC]
    · simp
    · intro _ _ _ _ h
      cases r with
      | wr w => simp [OnTrack, hpc] at h
      | ex => simp [OnTrack, hpc] at h ⊢; exact h

end Podc.RecoverableMutexRMR
