import Papers.PODC2020.RecoverableMutexRMR.InvDefs

/-!
# Basic lemmas for the invariant: initial state, frame lemmas
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

@[simp] lemma setPc_C (s : Cfg P) (p : P) (k : PC P) : (s.setPc p k).C = s.C := rfl
@[simp] lemma setPc_D (s : Cfg P) (p : P) (k : PC P) : (s.setPc p k).D = s.D := rfl
@[simp] lemma setPc_T (s : Cfg P) (p : P) (k : PC P) : (s.setPc p k).T = s.T := rfl
@[simp] lemma setPc_A (s : Cfg P) (p : P) (k : PC P) : (s.setPc p k).A = s.A := rfl
@[simp] lemma setPc_W (s : Cfg P) (p : P) (k : PC P) : (s.setPc p k).W = s.W := rfl
@[simp] lemma setPc_X (s : Cfg P) (p : P) (k : PC P) : (s.setPc p k).X = s.X := rfl
@[simp] lemma setPc_pc (s : Cfg P) (p : P) (k : PC P) :
    (s.setPc p k).pc = Function.update s.pc p k := rfl

@[simp] lemma RetInv_setPc (s : Cfg P) (p q : P) (k : PC P) (r : Ret) :
    RetInv (s.setPc p k) q r ↔ RetInv s q r := by
  cases r <;> rfl

lemma Isize_congr {s s' : Cfg P} {g : Ghost P} (hA : s'.A = s.A) : Isize s' g = Isize s g := by
  unfold Isize; congr 1; apply Finset.filter_congr; intro q _; simp [inI, hA]

lemma crCount_congr {s s' : Cfg P} {g : Ghost P} (hA : s'.A = s.A) :
    crCount s' g = crCount s g := by
  unfold crCount; congr 1; apply Finset.filter_congr; intro q _; simp [hA]

lemma lostCount_congr {s s' : Cfg P} {g : Ghost P} (hA : s'.A = s.A) :
    lostCount s' g = lostCount s g := by
  unfold lostCount; congr 1; apply Finset.filter_congr; intro q _; simp [hA]

lemma Phi_congr {s s' : Cfg P} {g : Ghost P} (hA : s'.A = s.A) (hC : s'.C = s.C)
    (hD : s'.D = s.D) : Phi s' g = Phi s g := by
  simp [Phi, Isize_congr hA, hC, hD]

lemma Psi_congr {s s' : Cfg P} {g : Ghost P} (hA : s'.A = s.A) (hC : s'.C = s.C)
    (hD : s'.D = s.D) : Psi s' g = Psi s g := by
  simp [Psi, Phi_congr hA hC hD, crCount_congr hA, lostCount_congr hA]

lemma Isize_congr' {s s' : Cfg P} {g : Ghost P} (hA : ∀ x, s'.A x = .skipped ↔ s.A x = .skipped) :
    Isize s' g = Isize s g := by
  unfold Isize; congr 1; apply Finset.filter_congr; intro q _; simp [inI, hA]

lemma crCount_congr' {s s' : Cfg P} {g : Ghost P}
    (hA : ∀ x, s'.A x = .skipped ↔ s.A x = .skipped) : crCount s' g = crCount s g := by
  unfold crCount; congr 1; apply Finset.filter_congr; intro q _; simp [hA]

lemma card_filter_split {α : Type*} (S : Finset α) (P Q : α → Prop) [DecidablePred P]
    [DecidablePred Q] : (S.filter P).card =
      (S.filter (fun x => P x ∧ ¬ Q x)).card + (S.filter (fun x => P x ∧ Q x)).card := by
  rw [← Finset.card_filter_add_card_filter_not (s := S.filter P) Q,
    Finset.filter_filter, Finset.filter_filter, add_comm]

/-- Counting processes satisfying predicates that agree except at `p`. -/
lemma card_filter_update (f h : P → Prop) [DecidablePred f] [DecidablePred h] (p : P)
    (hfh : ∀ q, q ≠ p → (f q ↔ h q)) :
    (Finset.univ.filter f).card + (if h p then 1 else 0) =
      (Finset.univ.filter h).card + (if f p then 1 else 0) := by
  rw [card_filter_split Finset.univ f (· = p), card_filter_split Finset.univ h (· = p)]
  have e1 : Finset.univ.filter (fun x => f x ∧ ¬ x = p) =
      Finset.univ.filter (fun x => h x ∧ ¬ x = p) := by
    ext q; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, b⟩; exact ⟨(hfh q b).1 a, b⟩
    · rintro ⟨a, b⟩; exact ⟨(hfh q b).2 a, b⟩
  have e2 : ∀ (k : P → Prop) [DecidablePred k],
      (Finset.univ.filter (fun x => k x ∧ x = p)).card = if k p then 1 else 0 := by
    intro k _
    split_ifs with hk
    · rw [Finset.card_eq_one]; exact ⟨p, by ext q; simp; rintro rfl; exact hk⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; rintro q - ⟨a, rfl⟩; exact hk a
  rw [e1, e2 f, e2 h]; omega

/-! ### The initial state -/

lemma Isize_init : Isize (Cfg.init : Cfg P) Ghost.init = 0 := by
  unfold Isize; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro p _; simp [inI, Ghost.init]

theorem inv_init : Inv (Cfg.init : Cfg P) Ghost.init where
  T_le := by simp [Cfg.init]
  A_ne := by simp [Cfg.init]
  A_tok := by intro x hx h; simp [Cfg.init] at h; omega
  done := by simp [Cfg.init]
  grant := by simp [Cfg.init]
  future := by intro q x; simp [Cfg.init]
  own_claimed := by simp [Cfg.init]
  own_le := by simp [Ghost.init]
  own_ex := by intro x hx h; simp [Cfg.init] at h; omega
  cur_le := by simp [Ghost.init]
  own_cur := by simp [Ghost.init]
  W_cur := by simp [Cfg.init]
  X_W := by simp [Cfg.init]
  pend_pc := by simp [Ghost.init]
  cr_pc := by simp [Cfg.init, CrPC]
  l3_cr := by simp [Cfg.init]
  I_cr := by simp [inI, Ghost.init]
  lost_wit := by intro x hx h; simp [Cfg.init] at h; omega
  phi_nonneg := by simp only [Phi, Isize_init]; simp [Cfg.init]
  psi_bound := by
    simp only [Psi, Phi, Isize_init]
    simp [crCount, lostCount, nR15, nSkipped, Cfg.init, Ghost.init]
  loc := by intro p; simp [LI, Cfg.init]

/-! ### Frame lemmas -/

/-- How the `W` entry of a process may change under a step of another process: unchanged, or
granted by line 40. -/
def WFrame (v v' : ℕ × Bool) : Prop := v' = v ∨ ∃ w, w ≠ 0 ∧ v = (w, false) ∧ v' = (w, true)

lemma WFrame.fst {v v' : ℕ × Bool} (h : WFrame v v') : v'.1 = v.1 := by
  rcases h with rfl | ⟨w, -, rfl, rfl⟩ <;> rfl

lemma WFrame.snd {v v' : ℕ × Bool} (h : WFrame v v') (hv : v.2 = true) : v'.2 = true := by
  rcases h with rfl | ⟨w, -, rfl, rfl⟩
  · exact hv
  · rfl

lemma WFrame.zero {v v' : ℕ × Bool} (h : WFrame v v') : v' = (0, false) ↔ v = (0, false) := by
  rcases h with rfl | ⟨w, hw, rfl, rfl⟩
  · rfl
  · simp [hw]

lemma WFrame.ne_false {v v' : ℕ × Bool} (h : WFrame v v') (a : ℕ) (hv : v ≠ (a, false)) :
    v' ≠ (a, false) := by
  rcases h with rfl | ⟨w, hw, rfl, rfl⟩
  · exact hv
  · simp

lemma RetInv_frame {s s' : Cfg P} {q : P} {r : Ret} (h : RetInv s q r)
    (hX : s'.X q = s.X q) (hW : WFrame (s.W q) (s'.W q))
    (hA : ∀ x, s.A x ≠ .empty → s'.A x = s.A x) : RetInv s' q r := by
  cases r with
  | wr w =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨hX ▸ h1, hW.fst ▸ h2, h3, by rw [hA _ (by simp [h4])]; exact h4⟩
  | ex =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨hX ▸ h1, hW.zero.2 h2⟩

/-- Local invariants of a process are preserved by steps of other processes. -/
theorem LI_frame {s s' : Cfg P} {g g' : Ghost P} {q : P}
    (h : LI s g q)
    (hpc : s'.pc q = s.pc q) (hX : s'.X q = s.X q) (hW : WFrame (s.W q) (s'.W q))
    (hT : s.T ≤ s'.T) (hC : s.C ≤ s'.C) (hD : s.D ≤ s'.D)
    (hA : ∀ x, s.A x ≠ .empty → s'.A x = s.A x)
    (hAq : ∀ x r, s'.A x = .claimed r → s.A x = .empty → x ≠ g.cur q)
    (hcur : g'.cur q = g.cur q) (hcr : g'.cr q = g.cr q) (hpend : g'.pend q = g.pend q)
    (hJ : ∀ ℓ, ℓ ≤ s.T → ℓ + 1 ≤ s.C → (JHyp s g ℓ → 1 ≤ Phi s g) →
      JHyp s' g' ℓ → 1 ≤ Phi s' g') :
    LI s' g' q := by
  have hR : ∀ r, RetInv s q r → RetInv s' q r := fun r hr => RetInv_frame hr hX hW hA
  unfold LI at h ⊢
  rw [hpc]
  cases hk : s.pc q with
  | rem => rw [hk] at h; exact ⟨hW.zero.2 h.1, hX ▸ h.2⟩
  | l3 => rw [hk] at h; exact hX ▸ h
  | l4 => rw [hk] at h; exact ⟨hX ▸ h.1, hW.zero.2 h.2⟩
  | l5 c =>
    rw [hk] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨hX ▸ h1, hW.zero.2 h2, hcur ▸ h3, h4, ?_, hpend ▸ h6⟩
    rcases h5 with h5 | h5
    · cases ha : s'.A c with
      | empty => exact Or.inl rfl
      | skipped => exact Or.inr rfl
      | claimed r => exact absurd h3 (hAq c r ha h5)
    · exact Or.inr (by rw [hA _ (by simp [h5])]; exact h5)
  | w23 => rw [hk] at h; exact ⟨hX ▸ h.1, hW.fst ▸ h.2⟩
  | w24 w => rw [hk] at h; exact ⟨hX ▸ h.1, hW.fst ▸ h.2.1, h.2.2⟩
  | w25 w =>
    rw [hk] at h
    exact ⟨hX ▸ h.1, hW.fst ▸ h.2.1, h.2.2.1, by rw [hA _ h.2.2.2]; exact h.2.2.2⟩
  | w26 =>
    rw [hk] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨hX ▸ h1, by rw [hW.fst, hcur]; exact h2, hcur ▸ h3, ?_⟩
    rw [hcur, hA _ (by simp [h4])]; exact h4
  | w28 w => rw [hk] at h; exact hR _ h
  | w31 w => rw [hk] at h; exact hR _ h
  | cs => rw [hk] at h; exact ⟨hX ▸ h.1, hW.snd h.2⟩
  | x9 =>
    rw [hk] at h
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (hW.snd h)
    · exact Or.inr ⟨hW.zero.2 h1, hX ▸ h2⟩
  | x10 => rw [hk] at h; exact hX ▸ h
  | x12 => rw [hk] at h; exact ⟨hX ▸ h.1, hW.zero.2 h.2⟩
  | r15 => trivial
  | r16 => rw [hk] at h; exact hcr ▸ h
  | r18 => rw [hk] at h; exact ⟨hX ▸ h.1, hcr ▸ h.2⟩
  | m34 r => rw [hk] at h; exact hR _ h
  | m35 r ℓ => rw [hk] at h; exact ⟨hR _ h.1, h.2.trans hT⟩
  | m36 r ℓ d => rw [hk] at h; exact ⟨hR _ h.1, h.2.1.trans hT, h.2.2.trans hD⟩
  | m38 r ℓ c d =>
    rw [hk] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨hR _ h1, h2.trans hT, h3, h4.trans hC, h5.trans hD,
      fun hcd => hJ ℓ h2 (by omega) (h6 hcd)⟩
  | m40 r ℓ q' =>
    rw [hk] at h
    exact ⟨hR _ h.1, h.2.1.trans hT, by rw [hA _ (by simp [h.2.2])]; exact h.2.2⟩
  | m41 r ℓ q' =>
    rw [hk] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨hR _ h1, h2.trans hT, by rw [hA _ (by simp [h3])]; exact h3,
      fun e => hW.ne_false _ (h4 e)⟩
  | m42 r ℓ =>
    rw [hk] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨hR _ h1, h2.trans hT, by rw [hA _ (by simp [h3])]; exact h3, hW.fst ▸ h4⟩
  | m46 r ℓ =>
    rw [hk] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨hR _ h1, h2.trans hT, h3.trans (by omega), hJ ℓ h2 h3 h4⟩
  | m47 r ℓ =>
    rw [hk] at h
    exact ⟨hR _ h.1, h.2.1.trans hT, by rw [hA _ h.2.2]; exact h.2.2⟩
  | m48 r ℓ =>
    rw [hk] at h
    exact ⟨hR _ h.1, h.2.1.trans hT, by rw [hA _ (by simp [h.2.2])]; exact h.2.2⟩

lemma OnTrack_congr {s s' : Cfg P} {q : P} (hpc : s'.pc q = s.pc q) (hT : s'.T = s.T) :
    OnTrack s' q ↔ OnTrack s q := by
  unfold OnTrack; rw [hpc, hT]

lemma nR15_setPc {s : Cfg P} {p : P} {k : PC P} (hold : s.pc p ≠ .r15) (hk : k ≠ .r15) :
    nR15 (s.setPc p k) = nR15 s := by
  unfold nR15
  congr 1
  apply Finset.filter_congr
  intro q _
  by_cases hq : q = p
  · subst hq; simp [hold, hk]
  · simp [Function.update_of_ne hq]

/-- Steps that only change the program counter of `p` (reads and local steps). -/
theorem inv_setPc {s : Cfg P} {g : Ghost P} {p : P} {k : PC P} (hI : Inv s g)
    (hold : s.pc p ≠ .r15) (hk : k ≠ .r15)
    (hLI : LI (s.setPc p k) g p)
    (hpend : g.pend p = true → PendPC k ∨ s.A (g.cur p) = .skipped)
    (hcr : CrPC k → g.pend p = true ∨ g.cr p = true)
    (hl3 : k = .l3 → g.pend p = true ∨ g.cr p = true ∨ s.W p = (0, false))
    (hfut : Future (s.setPc p k) p) :
    Inv (s.setPc p k) g where
  T_le := hI.T_le
  A_ne := hI.A_ne
  A_tok := hI.A_tok
  done := hI.done
  grant := hI.grant
  future q := by
    by_cases hq : q = p
    · subst hq; exact hfut
    · intro x hx hT
      rcases hI.future q x hx hT with h | ⟨h1, h2, h3, h4⟩
      · exact Or.inl h
      · refine Or.inr ⟨h1, h2, h3, ?_⟩
        exact (OnTrack_congr (s := s) (s' := s.setPc p k)
          (by simp [Function.update_of_ne hq]) rfl).2 h4
  own_claimed := hI.own_claimed
  own_le := hI.own_le
  own_ex := hI.own_ex
  cur_le := hI.cur_le
  own_cur := hI.own_cur
  W_cur := hI.W_cur
  X_W := hI.X_W
  pend_pc q := by
    by_cases hq : q = p
    · subst hq; simpa using hpend
    · simpa [Function.update_of_ne hq] using hI.pend_pc q
  cr_pc q := by
    by_cases hq : q = p
    · subst hq; simpa using hcr
    · simpa [Function.update_of_ne hq] using hI.cr_pc q
  l3_cr q := by
    by_cases hq : q = p
    · subst hq; simpa using hl3
    · simpa [Function.update_of_ne hq] using hI.l3_cr q
  I_cr := hI.I_cr
  lost_wit := hI.lost_wit
  phi_nonneg := hI.phi_nonneg
  psi_bound := by
    have := hI.psi_bound
    rw [nR15_setPc hold hk]
    exact this
  loc q := by
    by_cases hq : q = p
    · subst hq; exact hLI
    · exact LI_frame (hI.loc q) (by simp [Function.update_of_ne hq]) rfl (Or.inl rfl) le_rfl le_rfl
        le_rfl (fun _ _ => rfl) (fun x r h h' => by simp [h'] at h) rfl rfl rfl
        (fun _ _ _ h => h)

/-- Variant of `inv_setPc` with the `Future` obligation reduced to `OnTrack`. -/
theorem inv_quiet {s : Cfg P} {g : Ghost P} {p : P} {k : PC P} (hI : Inv s g)
    (hold : s.pc p ≠ .r15) (hk : k ≠ .r15)
    (hLI : LI (s.setPc p k) g p)
    (hpend : g.pend p = true → PendPC k ∨ s.A (g.cur p) = .skipped)
    (hcr : CrPC k → g.pend p = true ∨ g.cr p = true)
    (hl3 : k = .l3 → g.pend p = true ∨ g.cr p = true ∨ s.W p = (0, false))
    (hOT : s.A (s.T + 1) = .claimed p → (s.W p).1 ≠ s.T + 1 → s.W p = (0, false) →
      s.X p = true → OnTrack s p → OnTrack (s.setPc p k) p) :
    Inv (s.setPc p k) g := by
  refine inv_setPc hI hold hk hLI hpend hcr hl3 ?_
  intro x hx hT
  rcases hI.future p x hx hT with h | ⟨h1, h2, h3, h4⟩
  · exact Or.inl h
  · subst h1
    exact Or.inr ⟨rfl, h2, h3, hOT hx (by simp [h2]) h2 h3 h4⟩

lemma onTrack_iff (s : Cfg P) (q : P) : OnTrack s q ↔ OnTrack s q := Iff.rfl

end Podc.RecoverableMutexRMR
