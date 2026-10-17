import Papers.PODC2021.ScannableBinaryObjects.Impl1Frame

/-!
# Implementation 1: preservation of the linearizability invariant

`inv_step`: every step preserves `Inv` (for a suitably extended linearization).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Scannable

namespace Impl1

open List

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P]
  {R : ∀ i, (O i).Readable} {Sc Up : Finset P} {h₀ : Sc → Bool}
  {α : List (Label P (scannable O))} {C C' : Config (scannable O) (Obj O Sc) P (Loc O Sc)}
  {L : List (OpId P × ScanOp O)}

lemma not_completed_curOp_tau (q p : P) : ¬ Completed (α ++ [.tau q]) (curOp α p) := by
  rw [← curOp_append_tau α q p]; exact not_completed_curOp _ _

lemma loc_other {ℓ : Label P (scannable O)}
    (h : (impl1 R Sc Up h₀).step C ℓ = some C') : ∀ r : P, r ≠ ℓ.proc → C'.loc r = C.loc r :=
  fun _ hr => (Impl.step_other h (Ne.symm hr)).1

lemma pend_other {ℓ : Label P (scannable O)}
    (h : (impl1 R Sc Up h₀).step C ℓ = some C') : ∀ r : P, r ≠ ℓ.proc → C'.pend r = C.pend r :=
  fun _ hr => (Impl.step_other h (Ne.symm hr)).2

/-- Invocation steps. -/
lemma inv_step_inv (hrun : (impl1 R Sc Up h₀).run α = some C) (hI : Inv Sc Up α C L) {q : P}
    {o : ScanOp O} (h : (impl1 R Sc Up h₀).step C (.inv q o) = some C') :
    Inv Sc Up (α ++ [.inv q o]) C' L := by
  obtain ⟨h0, hall, hpend, hloc, hmem⟩ := Impl.step_inv h
  have hlen : (opsOf α q).length = (respsOf α q).length := by
    rcases (impl1 R Sc Up h₀).run_counts hrun q with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h0 h1
  have hnotin : curOp α q ∉ L.map Prod.fst := by
    intro hm
    have := hI.lin.invoked_of_mem hm
    simp [Invoked] at this; omega
  have hop : opOf (α ++ [.inv q o]) (curOp (α ++ [.inv q o]) q) = some o := by
    simp [opOf, opsOf_append, respsOf_append, ← hlen]
  refine ⟨hI.lin.append_inv q o, fun i => by rw [hmem]; exact hI.mem i, fun p => ?_⟩
  by_cases hpq : p = q
  · subst hpq
    rw [hloc, Function.update_self]
    cases o with
    | scan =>
      simp only [impl1, PInvL]
      exact ⟨by rw [hpend, Function.update_self], by simpa [impl1] using hall,
        by rw [curOp_append_inv]; exact hnotin, hop⟩
    | update i o =>
      simp only [impl1, PInvL]
      exact ⟨by rw [hpend, Function.update_self], by simpa [impl1] using hall,
        by rw [curOp_append_inv]; exact hnotin, hop⟩
  · refine pinv_frame_same (by simpa [Label.proc] using Ne.symm hpq)
      (by rw [hloc, Function.update_of_ne hpq]) (by rw [hpend, Function.update_of_ne hpq])
      (fun hp hR => ⟨by rw [hmem] at hR; exact hR, numDanger_le (loc_other h) ?_⟩) (hI.proc p)
    simp only [Label.proc]; rw [hloc, Function.update_self]
    cases o with
    | scan => simp [impl1, dang]
    | update i o =>
      intro hd
      simp only [impl1, dang, List.all_eq_true, Finset.mem_toList, Finset.mem_univ,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, true_implies] at hd
      exact absurd rfl (hd ⟨p, hp⟩)

/-- Response steps. -/
lemma inv_step_ret (hI : Inv Sc Up α C L) {q : P} {r : ScanResp O}
    (h : (impl1 R Sc Up h₀).step C (.ret q r) = some C') :
    Inv Sc Up (α ++ [.ret q r]) C' L := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  have hq := hI.proc q
  cases hl : C.loc q with
  | idle => simp only [PInvL, hl] at hq; exact absurd hq h0
  | upd i o rest =>
    cases rest <;> simp [impl1, act, hl] at hact
  | scan1 m b =>
    simp only [PInvL, hl] at hq
    by_cases hm : m < k <;> simp [impl1, act, hl, hm, hq.2.1] at hact
  | scan2 c m b =>
    simp only [PInvL, hl] at hq
    by_cases hm : m < k <;> simp [impl1, act, hl, hm, hq.1.2.1] at hact
  | done r' =>
    simp only [impl1, act, hl, Action.ret.injEq] at hact
    obtain ⟨rfl, rfl⟩ := hact
    simp only [PInvL, hl] at hq
    obtain ⟨-, L₁, L₂, o, hs, hr⟩ := hq
    refine ⟨hI.lin.append_ret L₁ L₂ o hs hr, fun i => by rw [hmem]; exact hI.mem i,
      fun p => ?_⟩
    by_cases hpq : p = q
    · subst hpq
      rw [hloc, Function.update_self]
      simp only [PInvL]; rw [hpend, Function.update_self]
    · refine pinv_frame_same (by simpa [Label.proc] using Ne.symm hpq)
        (by rw [hloc, Function.update_of_ne hpq]) (by rw [hpend, Function.update_of_ne hpq])
        (fun hp hR => ⟨by rw [hmem] at hR; exact hR, numDanger_le (loc_other h) ?_⟩)
        (hI.proc p)
      simp only [Label.proc]; rw [hloc, Function.update_self]; simp [dang]

/-- Internal steps that do not change the linearization. -/
lemma inv_tau_same (hI : Inv Sc Up α C L) {q : P}
    (h : (impl1 R Sc Up h₀).step C (.tau q) = some C')
    (hmemB : ∀ i, C'.mem (.inl i) = C.mem (.inl i))
    (hR : ∀ p, p ≠ q → ∀ hp : p ∈ Sc, C'.mem (.inr ⟨p, hp⟩) = false →
      C.mem (.inr ⟨p, hp⟩) = false ∧ (dang p (C'.loc q) = true → dang p (C.loc q) = true))
    (hq : PInvL Sc Up (α ++ [.tau q]) C' L q (C'.loc q)) :
    Inv Sc Up (α ++ [.tau q]) C' L := by
  refine ⟨hI.lin.append_tau q, fun i => by rw [hmemB]; exact hI.mem i, fun p => ?_⟩
  by_cases hpq : p = q
  · subst hpq; exact hq
  · have hpq' : (Label.tau q : Label P (scannable O)).proc ≠ p := by
      simpa [Label.proc] using Ne.symm hpq
    exact pinv_frame_same hpq' (loc_other h p hpq) (pend_other h p hpq)
      (fun hp hR' => ⟨(hR p hpq hp hR').1, numDanger_le (loc_other h) (hR p hpq hp hR').2⟩)
      (hI.proc p)

lemma inv_step_upd_cons (hI : Inv Sc Up α C L) {q : P} {i : Fin k} {o : (O i).Op} {j : Sc}
    {rest : List Sc} (hl : C.loc q = .upd i o (j :: rest))
    (h : (impl1 R Sc Up h₀).step C (.tau q) = some C') :
    Inv Sc Up (α ++ [.tau q]) C' L := by
  obtain ⟨hpend, hmem, hloc⟩ := step_upd_cons hl h
  have hq := hI.proc q
  rw [hl] at hq
  refine inv_tau_same hI h (fun i' => by rw [hmem]; simp) (fun p hpq hp hR => ?_) ?_
  · have hj : j ≠ ⟨p, hp⟩ := by
      rintro rfl; rw [hmem, Function.update_self] at hR; cases hR
    rw [hmem, Function.update_of_ne (by simpa using hj.symm)] at hR
    refine ⟨hR, ?_⟩
    rw [hloc, Function.update_self, hl]
    simp only [dang, List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not]
    refine fun hd => ⟨fun he => hj (Subtype.ext he), hd⟩
  · rw [hloc, Function.update_self]
    simp only [PInvL] at hq ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hq
    exact ⟨by rw [hpend]; exact h1, h2, by rw [curOp_append_tau]; exact h3,
      by rw [curOp_append_tau]; exact opOf_append_of_eq_some h4 _⟩

/-- The linearization point of an update: its access to `B i`. -/
lemma inv_step_upd_nil (hI : Inv Sc Up α C L) {q : P} {i : Fin k} {o : (O i).Op}
    (hl : C.loc q = .upd i o []) (h : (impl1 R Sc Up h₀).step C (.tau q) = some C') :
    Inv Sc Up (α ++ [.tau q]) C' (L ++ [(curOp α q, .update i o)]) := by
  obtain ⟨hpend, hmem, hloc⟩ := step_upd_nil hl h
  have hq := hI.proc q
  rw [hl] at hq
  simp only [PInvL] at hq
  obtain ⟨h1, hqU, h3, h4⟩ := hq
  refine ⟨(hI.lin.push h4 h3 (not_completed_curOp _ q)).append_tau q, fun i' => ?_, fun p => ?_⟩
  · rw [linState_push_update, hmem, ← hI.mem i]
    by_cases hi : i' = i
    · subst hi; simp only [Function.update_self]
    · rw [Function.update_of_ne hi, Function.update_of_ne (by simpa using hi), hI.mem]
  · by_cases hpq : p = q
    · subst hpq
      rw [hloc, Function.update_self]
      simp only [PInvL]
      refine ⟨by rw [hpend, h1]; simp, L, [], .update i o, by rw [curOp_append_tau], ?_⟩
      rw [hI.mem i]
    · have hpq' : (Label.tau q : Label P (scannable O)).proc ≠ p := by
        simpa [Label.proc] using Ne.symm hpq
      refine pinv_frame_push hpq' (loc_other h p hpq) (pend_other h p hpq)
        (fun hp => by rw [hmem]; simp) ?_ rfl rfl (not_completed_curOp_tau q q) (hI.proc p)
      refine numDanger_lt (loc_other h) ?_ ?_ hqU
      · simp only [Label.proc]; rw [hloc, Function.update_self]; rfl
      · simp only [Label.proc]; rw [hl]; rfl

lemma inv_step_scan1_lt (hI : Inv Sc Up α C L) {q : P} {m : ℕ} {b : Fin k → Bool}
    (hm : m < k) (hl : C.loc q = .scan1 m b) (h : (impl1 R Sc Up h₀).step C (.tau q) = some C') :
    Inv Sc Up (α ++ [.tau q]) C' L := by
  obtain ⟨hpend, hmem, hloc⟩ := step_scan1_lt hm hl h
  have hq := hI.proc q
  rw [hl] at hq
  refine inv_tau_same hI h (fun i' => by rw [hmem]) (fun p hpq hp hR => ?_) ?_
  · rw [hmem] at hR
    refine ⟨hR, ?_⟩
    rw [hloc, Function.update_self]; simp [dang]
  · rw [hloc, Function.update_self]
    simp only [PInvL] at hq ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hq
    exact ⟨by rw [hpend]; exact h1, h2, by rw [curOp_append_tau]; exact h3,
      by rw [curOp_append_tau]; exact opOf_append_of_eq_some h4 _⟩

lemma inv_step_scan1_ge (hI : Inv Sc Up α C L) {q : P} {m : ℕ} {b : Fin k → Bool}
    (hm : ¬ m < k) (hl : C.loc q = .scan1 m b)
    (h : (impl1 R Sc Up h₀).step C (.tau q) = some C') :
    Inv Sc Up (α ++ [.tau q]) C' L := by
  obtain ⟨hqS, hpend, hmem, hloc⟩ := step_scan1_ge hm hl h
  have hq := hI.proc q
  rw [hl] at hq
  refine inv_tau_same hI h (fun i' => by rw [hmem]; simp) (fun p hpq hp hR => ?_) ?_
  · have hne : (Sum.inr ⟨p, hp⟩ : Fin k ⊕ Sc) ≠ Sum.inr ⟨q, hqS⟩ := by
      simpa using hpq
    rw [hmem, Function.update_of_ne hne] at hR
    refine ⟨hR, ?_⟩
    rw [hloc, Function.update_self]; simp [dang]
  · rw [hloc, Function.update_self]
    simp only [PInvL] at hq ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hq
    refine ⟨⟨by rw [hpend]; exact h1, h2, by rw [curOp_append_tau]; exact h3,
      by rw [curOp_append_tau]; exact opOf_append_of_eq_some h4 _⟩, fun hp _ => ?_⟩
    refine ⟨L, [], 0, ⟨by simp, by simp⟩, fun _ i hi => absurd hi (by omega),
      by simpa using numDanger_le_card C', Or.inr ⟨le_refl _, by simp⟩⟩

lemma inv_step_scan2_lt (hI : Inv Sc Up α C L) {q : P} {c m : ℕ} {b : Fin k → Bool}
    (hm : m < k) (hl : C.loc q = .scan2 c m b)
    (h : (impl1 R Sc Up h₀).step C (.tau q) = some C') :
    Inv Sc Up (α ++ [.tau q]) C' L := by
  obtain ⟨hpend, hmem, hloc⟩ := step_scan2_lt hm hl h
  have hq := hI.proc q
  rw [hl] at hq
  simp only [PInvL] at hq
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hq
  have hbasic : C'.pend q = some .scan ∧ q ∈ Sc ∧ curOp (α ++ [.tau q]) q ∉ L.map Prod.fst ∧
      opOf (α ++ [.tau q]) (curOp (α ++ [.tau q]) q) = some (ScanOp.scan : ScanOp O) :=
    ⟨by rw [hpend]; exact h1, h2, by rw [curOp_append_tau]; exact h3,
      by rw [curOp_append_tau]; exact opOf_append_of_eq_some h4 _⟩
  have hD : numDanger Up C' q ≤ numDanger Up C q := by
    refine numDanger_le (loc_other h) ?_
    simp only [Label.proc]; rw [hloc, Function.update_self]; split <;> simp [dang]
  refine inv_tau_same hI h (fun i' => by rw [hmem]) (fun p hpq hp hR => ?_) ?_
  · rw [hmem] at hR
    refine ⟨hR, ?_⟩
    rw [hloc, Function.update_self]; split <;> simp [dang]
  · rw [hloc, Function.update_self]
    split
    · rename_i heq
      simp only [PInvL]
      refine ⟨hbasic, fun hp hR => ?_⟩
      rw [hmem] at hR
      obtain ⟨S₁, S₂, d, hcut, hclean, hN, hW⟩ := h5 hp hR
      refine ⟨S₁, S₂, d, by rw [curOp_append_tau]; exact hcut.append h4, fun hall i hi => ?_,
        by omega, ?_⟩
      · by_cases him : i.val < m
        · exact hclean hall i him
        · have hi' : i = ⟨m, hm⟩ := Fin.ext (by show i.val = m; omega)
          subst hi'
          rw [← linState_append_scans S₁ S₂ hall, ← hcut.1, ← hI.mem, heq]
      · rcases hW with ⟨W₁, W₂, hc, hb⟩ | hW
        · exact Or.inl ⟨W₁, W₂, by rw [curOp_append_tau]; exact hc.append h4, hb⟩
        · exact Or.inr hW
    · simp only [PInvL]; exact hbasic

/-- The end of a collect of the validation phase (read of `R q`); if the scan returns, it is
linearized retroactively at a clean collect. -/
lemma inv_step_scan2_ge (hI : Inv Sc Up α C L) {q : P} {c m : ℕ} {b : Fin k → Bool}
    (hm : ¬ m < k) (hl : C.loc q = .scan2 c m b)
    (h : (impl1 R Sc Up h₀).step C (.tau q) = some C') :
    ∃ L', Inv Sc Up (α ++ [.tau q]) C' L' := by
  obtain ⟨hqS, hpend, hmem, hloc⟩ := step_scan2_ge hm hl h
  have hq := hI.proc q
  rw [hl] at hq
  simp only [PInvL] at hq
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hq
  have hbasic : C'.pend q = some .scan ∧ q ∈ Sc ∧ curOp (α ++ [.tau q]) q ∉ L.map Prod.fst ∧
      opOf (α ++ [.tau q]) (curOp (α ++ [.tau q]) q) = some (ScanOp.scan : ScanOp O) :=
    ⟨by rw [hpend]; exact h1, h2, by rw [curOp_append_tau]; exact h3,
      by rw [curOp_append_tau]; exact opOf_append_of_eq_some h4 _⟩
  have hdq : ∀ p, dang p (C'.loc q) = false := by
    intro p; rw [hloc, Function.update_self]; split
    · rfl
    · split <;> rfl
  have hD : ∀ p, numDanger Up C' p ≤ numDanger Up C p := fun p =>
    numDanger_le (loc_other h) (by simp only [Label.proc]; rw [hdq p]; simp)
  have hsame : PInvL Sc Up (α ++ [.tau q]) C' L q (C'.loc q) →
      Inv Sc Up (α ++ [.tau q]) C' L := fun hq' =>
    inv_tau_same hI h (fun i' => by rw [hmem])
      (fun p hpq hp hR => ⟨by rw [hmem] at hR; exact hR, by rw [hdq p]; simp⟩) hq'
  by_cases hR : C.mem (.inr ⟨q, hqS⟩) = true
  · refine ⟨L, hsame ?_⟩
    rw [hloc, Function.update_self]; simp only [hR, ↓reduceIte]
    exact hbasic
  have hRf : C.mem (.inr ⟨q, hqS⟩) = false := by simpa using hR
  obtain ⟨S₁, S₂, d, hcut, hclean, hN, hW⟩ := h5 hqS hRf
  have hclean' : (∀ y ∈ S₂, y.2.isScan = true) → linSt S₁ = b :=
    fun hall => funext fun i => hclean hall i (by omega)
  by_cases hc : c < Up.card
  · refine ⟨L, hsame ?_⟩
    rw [hloc, Function.update_self]; simp only [hR, hc, ↓reduceIte]
    simp only [PInvL]
    refine ⟨hbasic, fun hp _ => ⟨L, [], d, ⟨by simp, by simp⟩, fun _ i hi => absurd hi (by omega),
      by have := hD q; omega, ?_⟩⟩
    rcases hW with ⟨W₁, W₂, hc', hb⟩ | ⟨hcd, hdirty⟩
    · exact Or.inl ⟨W₁, W₂, by rw [curOp_append_tau]; exact hc'.append h4, hb⟩
    · by_cases hall : ∀ y ∈ S₂, y.2.isScan = true
      · exact Or.inl ⟨S₁, S₂, by rw [curOp_append_tau]; exact hcut.append h4, hclean' hall⟩
      · simp only [not_forall, Bool.not_eq_true] at hall
        obtain ⟨y, hy, hys⟩ := hall
        exact Or.inr ⟨hdirty ⟨y, hy, hys⟩, by simp⟩
  · -- the scan returns: find the clean collect
    have hwit : ∃ W₁ W₂, Cut α L (curOp α q) W₁ W₂ ∧ linSt W₁ = b := by
      rcases hW with hw | ⟨hcd, hdirty⟩
      · exact hw
      · by_cases hall : ∀ y ∈ S₂, y.2.isScan = true
        · exact ⟨S₁, S₂, hcut, hclean' hall⟩
        · exfalso
          simp only [not_forall, Bool.not_eq_true] at hall
          obtain ⟨y, hy, hys⟩ := hall
          have := hdirty ⟨y, hy, hys⟩
          omega
    obtain ⟨W₁, W₂, ⟨hWL, hW2⟩, hWb⟩ := hwit
    refine ⟨W₁ ++ (curOp α q, .scan) :: W₂, ⟨?_, fun i => ?_, fun p => ?_⟩⟩
    · have hlin := hI.lin
      rw [hWL] at hlin
      exact (hlin.insert h4 (hWL ▸ h3) (not_completed_curOp _ q) rfl hW2).append_tau q
    · rw [linState_insert_scan, ← hWL, hmem]; exact hI.mem i
    · by_cases hpq : p = q
      · subst hpq
        rw [hloc, Function.update_self]; simp only [hR, hc, ↓reduceIte]
        simp only [PInvL]
        refine ⟨by rw [hpend, h1]; simp, W₁, W₂, .scan, by rw [curOp_append_tau], ?_⟩
        show ScanResp.view (linSt W₁) = _; rw [hWb]
      · have hpq' : (Label.tau q : Label P (scannable O)).proc ≠ p := by
          simpa [Label.proc] using Ne.symm hpq
        exact pinv_frame_insert hpq' (loc_other h p hpq) (pend_other h p hpq)
          (fun hp => by rw [hmem]) (hD p) rfl (not_completed_curOp_tau q q) hWL (hI.proc p)

/-- Every step preserves the invariant. -/
theorem inv_step (hrun : (impl1 R Sc Up h₀).run α = some C) (hI : Inv Sc Up α C L)
    {ℓ : Label P (scannable O)} (h : (impl1 R Sc Up h₀).step C ℓ = some C') :
    ∃ L', Inv Sc Up (α ++ [ℓ]) C' L' := by
  cases ℓ with
  | inv q o => exact ⟨L, inv_step_inv hrun hI h⟩
  | ret q r => exact ⟨L, inv_step_ret hI h⟩
  | tau q =>
    cases hl : C.loc q with
    | idle => rw [step_tau_idle hl] at h; cases h
    | done r => rw [step_tau_done hl] at h; cases h
    | upd i o rest =>
      cases rest with
      | nil => exact ⟨_, inv_step_upd_nil hI hl h⟩
      | cons j rest => exact ⟨L, inv_step_upd_cons hI hl h⟩
    | scan1 m b =>
      by_cases hm : m < k
      · exact ⟨L, inv_step_scan1_lt hI hm hl h⟩
      · exact ⟨L, inv_step_scan1_ge hI hm hl h⟩
    | scan2 c m b =>
      by_cases hm : m < k
      · exact ⟨L, inv_step_scan2_lt hI hm hl h⟩
      · exact inv_step_scan2_ge hI hm hl h

theorem inv_of_run {α : List (Label P (scannable O))}
    {C : Config (scannable O) (Obj O Sc) P (Loc O Sc)}
    (h : (impl1 R Sc Up h₀).run α = some C) : ∃ L, Inv Sc Up α C L :=
  Impl.run_induction (Q := fun α C => ∃ L, Inv Sc Up α C L)
    ⟨[], isLinearization_nil, fun _ => rfl, fun _ => by simp [Impl.initCfg, impl1, PInvL]⟩
    (fun _ _ _ _ hα ⟨_, hI⟩ hs => inv_step hα hI hs) h

end Impl1

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P]

open Impl1 in
/-- **Theorem 2 of Ovens (PODC 2021), linearizability**: Implementation 1 is linearizable
(for any scanners `Sc`, updaters `Up`, readable components and initial handshaking bits). -/
theorem impl1_linearizable (R : ∀ i, (O i).Readable) (Sc Up : Finset P) (h₀ : Sc → Bool) :
    (impl1 R Sc Up h₀).Linearizable :=
  Impl.linearizable_of_run fun _ _ hα =>
    let ⟨L, hL⟩ := inv_of_run hα
    ⟨L, hL.lin⟩

end Cslib.SharedMemory.Scannable
