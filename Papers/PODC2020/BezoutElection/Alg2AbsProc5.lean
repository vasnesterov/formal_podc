import Papers.PODC2020.BezoutElection.Alg2AbsProc4

/-!
# Algorithm 2, per-register abstraction: processing a copy (part 5) and the main theorem

A loser acknowledges (line 17); every abstract step preserves the invariant (`ainv_step`).
-/

set_option linter.unusedSectionVars false

namespace BezoutElection.Alg2

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

/-- A loser writes `⟨⊥, discarded ∪ {id}, phase⟩` (lines 15–17). -/
theorem ainv_line17 (hid : Function.Injective ids)
    {A : AState Id P} {p : P} {v : Reg Id}
    (hI : AInv n U ids A) (hp : (A.loc p).st = .copy v) (hact : (A.loc p).lv = A.reg.level)
    (h1 : v.level = (A.loc p).lv) (h1' : v.level < U)
    (hc : v.disc.card ≠ n - 1) (hid1 : v.id ≠ none) (hid2 : v.id ≠ some (ids p))
    (hme : ids p ∉ v.disc) :
    AInv n U ids (A.upd p
      { A.loc p with ca := false, lo := true, D := insert (ids p) v.disc,
                     st := .pend ⟨none, insert (ids p) v.disc, (A.loc p).ph, v.level,
                       v.leaders⟩ }) := by
  obtain ⟨B, hL⟩ := hI
  have hvV := val_copy hp h1 hact
  have hvL : v.level = A.reg.level := h1.trans hact
  set w : Reg Id := ⟨none, insert (ids p) v.disc, (A.loc p).ph, v.level, v.leaders⟩ with hw
  set l : ALoc Id := { A.loc p with ca := false, lo := true, D := insert (ids p) v.disc,
                                    st := .pend w } with hl
  have hlst : l.st = .pend w := rfl
  have hnc : ∀ v, l.st ≠ .copy v := by intro v h; cases h
  have hcopy : ∀ j v', ((A.upd p l).loc j).st = .copy v' → j ≠ p ∧ (A.loc j).st = .copy v' :=
    fun j v' h => upd_copy hnc h
  have hloc : ∀ j, j ≠ p → (A.upd p l).loc j = A.loc j := fun j hj => upd_loc_ne _ _ hj
  have hAL : ∀ a, A.ActLoser ids a → (A.upd p l).ActLoser ids a :=
    fun a h => actLoser_upd h (fun h1 _ => ⟨h1, rfl⟩)
  have hALp : (A.upd p l).ActLoser ids (ids p) := ⟨p, rfl, by simpa [hl] using hact, by simp [hl]⟩
  have hwAL : ∀ a ∈ insert (ids p) v.disc, (A.upd p l).ActLoser ids a := by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | h
    · exact hALp
    · exact hAL a (B.disc v hvV a h)
  have hthrp : A.Threat ids p := ⟨v, hp, hvL, hact, hid1, hid2, hme⟩
  have hthr : ∀ j, (A.upd p l).Threat ids j → A.Threat ids j := by
    rintro j ⟨v', h1, h2, h3, h4⟩
    obtain ⟨hj, h1⟩ := hcopy j v' h1
    exact ⟨v', h1, h2, by rwa [hloc j hj] at h3, h4⟩
  have BB : Basic n U ids (A.upd p l) := by
    refine ⟨B.lvU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j; by_cases hj : j = p
      · subst hj; simpa [hl] using B.lvLe j
      · rw [hloc j hj]; exact B.lvLe j
    · intro j v' h; obtain ⟨hj, h⟩ := hcopy j v' h; rw [hloc j hj]; exact B.copyLv j v' h
    · intro j w' h
      rcases upd_pend' hlst h with ⟨hj, h⟩ | ⟨rfl, rfl⟩
      · rw [hloc j hj]; exact B.pendLv j w' h
      · simp only [upd_loc_self, upd_reg, hl]
        exact ⟨hact, by omega, Or.inl ⟨hvL, B.copyLead j v hp hvL⟩⟩
    · intro j v' h; exact B.copyLead j v' (hcopy j v' h).2
    · intro j v' h; obtain ⟨hj, h⟩ := hcopy j v' h; rw [hloc j hj]; exact B.dead j v' h
    · intro j hj'; by_cases hj : j = p
      · subst hj; simp [hl]
      · rw [hloc j hj] at hj' ⊢; exact B.lagCa j hj'
    · intro u hu a ha
      rcases upd_val' hlst hu with h | ⟨rfl, -⟩
      · exact hAL a (B.disc u h a ha)
      · exact hwAL a ha
    · intro j hj' a ha
      by_cases hj : j = p
      · subst hj; simp only [upd_loc_self, hl] at ha; exact hwAL a ha
      · rw [hloc j hj] at hj' ha; exact hAL a (B.discLoc j hj' a ha)
    · intro j w' h h2 h3
      rcases upd_pend' hlst h with ⟨hj, h⟩ | ⟨rfl, rfl⟩
      · rw [hloc j hj]; exact B.pendId j w' h h2 h3
      · simp [hw] at h3
    · obtain ⟨j0, hj0⟩ := B.nonloser
      have hj0p : j0 ≠ p := by
        rintro rfl
        rcases hj0 with h | ⟨-, h⟩
        · omega
        · exact h hthrp
      refine ⟨j0, ?_⟩
      rw [hloc j0 hj0p]; rcases hj0 with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, fun h => h2 (hthr j0 h)⟩
    · intro a ha
      obtain ⟨c, hc1, hc2, hc3⟩ := B.regId a ha
      have hcp : c ≠ p := by
        rintro rfl
        subst hc1
        have hv := B.copyOwn c v hp ha
        apply hid2; rw [hv]; exact ha
      exact ⟨c, hc1, by rw [hloc c hcp]; exact ⟨hc2, hc3⟩⟩
    · intro j h; by_cases hj : j = p
      · subst hj; simp [hl] at h
      · rw [hloc j hj] at h ⊢; exact B.caAct j h
    · intro j v' h hr; obtain ⟨hj, h⟩ := hcopy j v' h; exact B.copyOwn j v' h hr
    · intro j h; by_cases hj : j = p
      · subst hj; simp [hl] at h
      · rw [hloc j hj] at h; exact B.caU j h
    · intro a ha
      obtain ⟨c, hc1, h2⟩ := B.regCa a ha
      have hcp : c ≠ p := by
        rintro rfl
        subst hc1
        have hv := B.copyOwn c v hp ha
        apply hid2; rw [hv]; exact ha
      exact ⟨c, hc1, by rw [hloc c hcp]; exact h2⟩
    · rcases B.wit with hP | ⟨c, hc, hT⟩ | ⟨c, w', hw', hl'⟩
      · exfalso; exact hid1 (hP.2.2.2 p v hp hvL hact)
      · have hcp : c ≠ p := by rintro rfl; exact hT hthrp
        exact Or.inr (Or.inl ⟨c, by rw [hloc c hcp]; exact hc, by rw [threat_upd hcp]; exact hT⟩)
      · have hcp : c ≠ p := by rintro rfl; rw [hp] at hw'; cases hw'
        exact Or.inr (Or.inr ⟨c, w', by rw [hloc c hcp]; exact hw', hl'⟩)
  refine ⟨BB, ?_⟩
  rcases hL with N | ⟨ℓ, E⟩
  · left
    have hph : (A.loc p).ph = .electing := N.phEl p hact
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u hu
      rcases upd_val' hlst hu with h | ⟨rfl, -⟩
      · exact N.valsEl u h
      · exact ⟨hph, fun h => absurd rfl h⟩
    · intro j hj'
      by_cases hj : j = p
      · subst hj; simpa [hl] using hph
      · rw [hloc j hj] at hj' ⊢; exact N.phEl j hj'
    · intro j w' h
      rcases upd_pend' hlst h with ⟨-, h⟩ | ⟨-, rfl⟩
      · exact N.noN11 j w' h
      · exact hvL
    · intro c h1 h2 h3
      by_cases hcp : c = p
      · rw [hcp] at h3; simp [hl] at h3
      · rw [hloc c hcp] at h1 h2 h3 ⊢; exact N.strict c h1 h2 h3
  · right
    have hpℓ : p ≠ ℓ := by
      rintro rfl
      exact (E.copyOther p v hp hvL hact hid1 hid2).1 rfl
    have hℓ : (A.upd p l).loc ℓ = A.loc ℓ := hloc ℓ (Ne.symm hpℓ)
    -- a committing acknowledgement only acknowledges the leader's committing value
    have hphE : (A.loc p).ph = .committing → v.id = some (ids ℓ) ∧ v.phase = .committing := by
      intro hC
      by_cases hvℓ : v.id = some (ids ℓ)
      · refine ⟨hvℓ, ?_⟩
        rcases hvp : v.phase with _ | _
        · have := E.copyLE p v hp hvL hact hvℓ hvp hc; rw [hC] at this; cases this
        · rfl
      · have := (E.copyOther p v hp hvL hact hid1 hvℓ).2.1; rw [hC] at this; cases this
    refine ⟨ℓ, ⟨by rw [hℓ]; exact E.act, fun j hj => ?_, ?_, ?_, ?_, ?_⟩⟩
    · by_cases hjp : j = p
      · subst hjp; simp [hl, hact]
      · rw [hloc j hjp]; exact E.others j hj
    · intro j v' h h2 h3 h4 h5
      obtain ⟨hj, h⟩ := hcopy j v' h
      rw [hloc j hj] at h3 ⊢
      exact E.copyOther j v' h h2 h3 h4 h5
    · intro j v' h h2 h3 h4 h5 h6
      obtain ⟨hj, h⟩ := hcopy j v' h
      rw [hloc j hj] at h3 ⊢
      exact E.copyLE j v' h h2 h3 h4 h5 h6
    · intro hph
      rw [hℓ] at hph
      have El := E.el hph
      refine ⟨by rw [hℓ]; exact El.card, by rw [hℓ]; exact El.ca, El.regL, ?_, ?_, ?_⟩
      · intro j v' h h2 h3 h4
        obtain ⟨hj, h⟩ := hcopy j v' h
        rw [hloc j hj] at h3
        exact El.copyL j v' h h2 h3 h4
      · intro u hu hC
        rcases upd_val' hlst hu with h | ⟨rfl, -⟩
        · exact El.coVals u h hC
        · obtain ⟨h1, h2⟩ := hphE hC
          rw [El.copyL p v hp hvL hact h1] at h2; cases h2
      · intro j w' h
        rcases upd_pend' hlst h with ⟨-, h⟩ | ⟨-, rfl⟩
        · exact El.noN11 j w' h
        · exact hvL
    · intro hph
      rw [hℓ] at hph
      have Co := E.co hph
      have hnq : ¬A.Quiet ids ℓ p := by
        intro hq
        rcases hq.2.2.1 v hp hvL with h | ⟨-, h⟩
        · exact hid1 h
        · exact hme h
      have hQ : ∀ j, (ids j ∈ (A.loc ℓ).D ∨ A.Quiet ids ℓ j) →
          ids j ∈ ((A.upd p l).loc ℓ).D ∨ (A.upd p l).Quiet ids ℓ j := by
        intro j hj
        rw [hℓ]
        rcases hj with hj | hj
        · exact Or.inl hj
        · have hjp : j ≠ p := by rintro rfl; exact hnq hj
          exact Or.inr ((quiet_upd hjp).2 hj)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro w' h; rw [hℓ] at h ⊢; exact Co.closing w' h
      · intro h; rw [hℓ] at h ⊢; exact Co.ca h
      · rw [hℓ]; exact Co.regL
      · intro j v' h h2 h3 h4
        obtain ⟨hj, h⟩ := hcopy j v' h
        rw [hloc j hj] at h3; rw [hℓ]
        exact Co.copyL j v' h h2 h3 h4
      · intro h1 h2 j hj; exact hQ j (Co.regBot h1 h2 j hj)
      · intro v' h h1 h2 h3 j hj
        rw [hℓ] at h
        exact hQ j (Co.copyBot v' h h1 h2 h3 j hj)
      · intro v' h; rw [hℓ] at h; exact Co.copyBotReg v' h
      · intro k w' h h1 h2 h3 j hj
        rcases upd_pend' hlst h with ⟨hk, h⟩ | ⟨rfl, rfl⟩
        · rw [hℓ, hloc k hk]
          exact Co.pendBot k w' h h1 h2 h3 j hj
        · rw [hℓ]
          simp only [hw] at h3 hj
          rcases Finset.mem_insert.1 hj with h | h
          · exact Or.inr ⟨hid h, by simpa [hl] using h3⟩
          · obtain ⟨h4, h5⟩ := hphE h3
            exact Or.inl ((Co.copyL k v hp hvL hact h4).2 h5 h)
      · intro j hj
        rw [hℓ] at hj
        have hq := Co.quiet j hj
        have hjp : j ≠ p := by rintro rfl; exact hnq hq
        exact (quiet_upd hjp).2 hq
      · intro j w' h h1
        rcases upd_pend' hlst h with ⟨-, h⟩ | ⟨-, rfl⟩
        · exact Co.n11 j w' h h1
        · simp [hw] at h1; omega

/-- Processing a copy preserves the invariant. -/
theorem ainv_proc (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {A : AState Id P} {p : P} {v : Reg Id} (ok fin : Bool)
    (hI : AInv n U ids A) (hp : (A.loc p).st = .copy v) :
    AInv n U ids (A.upd p (procL n U (ids p) (A.loc p) v ok fin)) := by
  -- a writing step is taken at the current level
  have hW : ∀ l' w, procX n U (ids p) (A.loc p) v ok fin = (l', some w) →
      v.level = (A.loc p).lv → (A.loc p).lv = A.reg.level := by
    intro l' w h h1
    rcases (hI.1.lvLe p).lt_or_eq with hlt | heq
    · have := hI.1.dead p v hp h1 hlt ok fin; rw [h] at this; cases this
    · exact heq
  rcases procX_cases n U (ids p) (A.loc p) v ok fin with
    ⟨h1, h2, h⟩ | h | ⟨h1, h1', h2, h3, h⟩ | ⟨h1, h1', h2, h3, h4, h5, h⟩ |
    ⟨h1, h1', h2, h3, h4, h⟩ | ⟨h1, h1', h2, h3, h4, h⟩ | ⟨h1, h1', h2, h3, h4, h5, h6, h⟩ <;>
    rw [procL_eq _ _ _ _ _ _ _ h] <;> simp only [stOf]
  · exact ainv_lvup hI hp h2
  · exact ainv_consume hI hp
  · exact ainv_line4 hI hp h1 h2 h3
  · refine ainv_win hid hn hI hp (hW _ _ h h1) h1 h1' h2 h3 h4 h5 ?_ ?_ <;> split_ifs <;> simp
  · exact ainv_line8 hI hp (hW _ _ h h1) h1 h1' h2 h3 h4
  · refine ainv_line14 hid hn hI hp (hW _ _ h h1) h1 h1' h2 h3 h4 ?_ ?_ ?_ ?_
    · split_ifs <;> simp
    · split_ifs <;> simp
    · intro h'; simp [h']
    · intro h'; simp [h']
  · exact ainv_line17 hid hI hp (hW _ _ h h1) h1 h1' h3 h4 h5 h6

/-- **Every abstract step preserves the per-register invariant.** -/
theorem ainv_step (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {A A' : AState Id P} (hI : AInv n U ids A) (h : AStep n U ids A A') : AInv n U ids A' := by
  cases h with
  | read j h => exact ainv_read hI h
  | proc j v ok fin h => exact ainv_proc hid hn ok fin hI h
  | write j w h => exact ainv_write hid hn hI h

end BezoutElection.Alg2
