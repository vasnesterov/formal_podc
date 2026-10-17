import Papers.PODC2020.BezoutElection.Alg2AbsProc3

/-!
# Algorithm 2, per-register abstraction: processing a copy (part 4)

Writing steps: a candidate writes its identifier (line 14), a loser acknowledges (line 17).
-/

set_option linter.unusedSectionVars false

namespace BezoutElection.Alg2

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

/-- A candidate writes `⟨id, discarded, phase⟩` (line 14). -/
theorem ainv_line14 (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {A : AState Id P} {p : P} {v : Reg Id} {d : Finset Id}
    (hI : AInv n U ids A) (hp : (A.loc p).st = .copy v) (hact : (A.loc p).lv = A.reg.level)
    (h1 : v.level = (A.loc p).lv) (h1' : v.level < U)
    (hnC : ¬(v.phase = .committing ∧ (A.loc p).ph = .electing))
    (hidn : v.id = none) (hlo : (A.loc p).lo = false)
    (hd1 : (A.loc p).D ⊆ d) (hd2 : d ⊆ (A.loc p).D ∪ v.disc)
    (hd3 : v.phase = (A.loc p).ph → d = (A.loc p).D ∪ v.disc)
    (hd4 : v.phase ≠ (A.loc p).ph → d = (A.loc p).D) :
    AInv n U ids (A.upd p
      { A.loc p with ca := true, D := d,
                     st := .pend ⟨some (ids p), d, (A.loc p).ph, v.level, v.leaders⟩ }) := by
  obtain ⟨B, hL⟩ := hI
  have hvV := val_copy hp h1 hact
  have hvL : v.level = A.reg.level := h1.trans hact
  set w : Reg Id := ⟨some (ids p), d, (A.loc p).ph, v.level, v.leaders⟩ with hw
  set l : ALoc Id := { A.loc p with ca := true, D := d, st := .pend w } with hl
  have hlst : l.st = .pend w := rfl
  have hnc : ∀ v, l.st ≠ .copy v := by intro v h; cases h
  have hcopy : ∀ j v', ((A.upd p l).loc j).st = .copy v' → j ≠ p ∧ (A.loc j).st = .copy v' :=
    fun j v' h => upd_copy hnc h
  have hloc : ∀ j, j ≠ p → (A.upd p l).loc j = A.loc j := fun j hj => upd_loc_ne _ _ hj
  have hAL : ∀ a, A.ActLoser ids a → (A.upd p l).ActLoser ids a :=
    fun a h => actLoser_upd h (fun h1 h2 => ⟨h1, h2⟩)
  have hdAL : ∀ a ∈ d, A.ActLoser ids a := by
    intro a ha
    rcases Finset.mem_union.1 (hd2 ha) with h | h
    · exact B.discLoc p hact a h
    · exact B.disc v hvV a h
  have hpd : ids p ∉ d := by
    intro h; obtain ⟨i, hi, -, h3⟩ := hdAL _ h; rw [hid hi, hlo] at h3; cases h3
  have hregp : A.reg.id ≠ some (ids p) := by
    intro h; rw [← B.copyOwn p v hp h, hidn] at h; cases h
  have BB : Basic n U ids (A.upd p l) := by
    refine ⟨B.lvU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inr (Or.inl ⟨p, by simp [hl], by rintro ⟨v', h1, -⟩; simp [hl] at h1⟩)⟩
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
      · subst hj; simp [hl] at hj'; omega
      · rw [hloc j hj] at hj' ⊢; exact B.lagCa j hj'
    · intro u hu a ha
      rcases upd_val' hlst hu with h | ⟨rfl, -⟩
      · exact hAL a (B.disc u h a ha)
      · exact hAL a (hdAL a ha)
    · intro j hj' a ha
      by_cases hj : j = p
      · subst hj; simp [hl] at ha; exact hAL a (hdAL a ha)
      · rw [hloc j hj] at hj' ha; exact hAL a (B.discLoc j hj' a ha)
    · intro j w' h h2 h3
      rcases upd_pend' hlst h with ⟨hj, h⟩ | ⟨rfl, rfl⟩
      · rw [hloc j hj]; exact B.pendId j w' h h2 h3
      · simp [hl, hw, hlo]
    · refine ⟨p, Or.inr ⟨by simpa [hl] using hlo, ?_⟩⟩
      rintro ⟨v', h1, -⟩; simp [hl] at h1
    · intro a ha
      obtain ⟨c, h1, h2, h3⟩ := B.regId a ha
      refine ⟨c, h1, ?_⟩
      by_cases hc : c = p
      · subst hc; simpa [hl] using ⟨h2, h3⟩
      · rw [hloc c hc]; exact ⟨h2, h3⟩
    · intro j h; by_cases hj : j = p
      · subst hj; simpa [hl] using ⟨hact, hlo⟩
      · rw [hloc j hj] at h ⊢; exact B.caAct j h
    · intro j v' h hr; obtain ⟨hj, h⟩ := hcopy j v' h; exact B.copyOwn j v' h hr
    · intro j h; by_cases hj : j = p
      · simp only [upd_reg]; omega
      · rw [hloc j hj] at h; exact B.caU j h
    · intro a ha
      obtain ⟨c, h1, h2⟩ := B.regCa a ha
      refine ⟨c, h1, ?_⟩
      by_cases hcp : c = p
      · rw [hcp]; exact Or.inl (by simp [hl])
      · rw [hloc c hcp]; exact h2
  refine ⟨BB, ?_⟩
  rcases hL with N | ⟨ℓ, E⟩
  · -- no leader yet: either it stays so, or `p` becomes the leader
    have hph : (A.loc p).ph = .electing := N.phEl p hact
    by_cases hcard : d.card = n - 1
    · right
      have hoth : ∀ j, j ≠ p → (A.loc j).lv = A.reg.level ∧ (A.loc j).lo = true := by
        intro j hj
        have := all_of_card hid hn d (fun i => (A.loc i).lv = A.reg.level ∧ (A.loc i).lo = true) p
          (fun a ha => by obtain ⟨i, h1, h2, h3⟩ := hdAL a ha; exact ⟨i, h1, h2, h3⟩)
          (by rw [hlo]; simp) hcard j hj
        exact this.2
      refine ⟨p, ⟨by simpa [hl] using ⟨hact, hlo⟩, fun j hj => by rw [hloc j hj]; exact hoth j hj,
        ?_, ?_, fun _ => ?_, fun h => by simp [hl, hph] at h⟩⟩
      · intro j v' h h2 h3 h4 h5
        obtain ⟨hj, h⟩ := hcopy j v' h
        rw [hloc j hj] at h3 ⊢
        have hv' : A.Val v' := Or.inr (Or.inr ⟨j, h, h2, h3⟩)
        exact ⟨hj, N.phEl j h3, (N.valsEl v' hv').1, (N.valsEl v' hv').2 h4⟩
      · intro j v' h h2 h3 _ _ _
        obtain ⟨hj, h⟩ := hcopy j v' h
        rw [hloc j hj] at h3 ⊢
        exact N.phEl j h3
      · refine ⟨by simpa [hl] using hcard, by simp [hl], fun h => absurd h hregp, ?_, ?_, ?_⟩
        · intro j v' h h2 h3 _
          obtain ⟨hj, h⟩ := hcopy j v' h
          rw [hloc j hj] at h3
          exact (N.valsEl v' (Or.inr (Or.inr ⟨j, h, h2, h3⟩))).1
        · intro u hu hC
          rcases upd_val' hlst hu with h | ⟨rfl, -⟩
          · rw [(N.valsEl u h).1] at hC; cases hC
          · simp [hw, hph] at hC
        · intro j w' h
          rcases upd_pend' hlst h with ⟨-, h⟩ | ⟨-, rfl⟩
          · exact N.noN11 j w' h
          · exact hvL
    · left
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro u hu
        rcases upd_val' hlst hu with h | ⟨rfl, -⟩
        · exact N.valsEl u h
        · exact ⟨hph, fun _ => hcard⟩
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
        · rw [hcp]; simpa [hl] using hcard
        · rw [hloc c hcp] at h1 h2 h3 ⊢; exact N.strict c h1 h2 h3
  · -- `p` is the leader
    right
    have hpℓ : p = ℓ := by
      by_contra h; have := (E.others p h).2; rw [hlo] at this; cases this
    subst hpℓ
    have hdcard : d.card ≤ n - 1 := card_le_of_ne hn d p (fun a ha => ne_of_actLoser E (hdAL a ha))
    refine ⟨p, ⟨by simpa [hl] using E.act, fun j hj => by rw [hloc j hj]; exact E.others j hj,
      ?_, ?_, fun hph => ?_, fun hph => ?_⟩⟩
    · intro j v' h h2 h3 h4 h5
      obtain ⟨hj, h⟩ := hcopy j v' h
      rw [hloc j hj] at h3 ⊢
      exact E.copyOther j v' h h2 h3 h4 h5
    · intro j v' h h2 h3 h4 h5 h6
      obtain ⟨hj, h⟩ := hcopy j v' h
      rw [hloc j hj] at h3 ⊢
      exact E.copyLE j v' h h2 h3 h4 h5 h6
    · -- electing leader
      simp only [upd_loc_self, hl] at hph
      have El := E.el hph
      have hvE : v.phase = .electing := by
        rcases hvp : v.phase with _ | _
        · rfl
        · exact absurd ⟨hvp, hph⟩ hnC
      have hdD : d = (A.loc p).D ∪ v.disc := hd3 (by rw [hvE, hph])
      refine ⟨?_, by simp [hl], El.regL, ?_, ?_, ?_⟩
      · simp only [upd_loc_self, hl]
        have := Finset.card_le_card hd1; rw [El.card] at this; omega
      · intro j v' h h2 h3 h4
        obtain ⟨hj, h⟩ := hcopy j v' h
        rw [hloc j hj] at h3
        exact El.copyL j v' h h2 h3 h4
      · intro u hu hC
        rcases upd_val' hlst hu with h | ⟨rfl, -⟩
        · exact El.coVals u h hC
        · simp [hw, hph] at hC
      · intro j w' h
        rcases upd_pend' hlst h with ⟨-, h⟩ | ⟨-, rfl⟩
        · exact El.noN11 j w' h
        · exact hvL
    · -- committing leader
      simp only [upd_loc_self, hl] at hph
      have Co := E.co hph
      have hnotin : ∀ u, A.Val u → ids p ∉ u.disc :=
        fun u hu h => E.not_actLoser hid (B.disc u hu _ h)
      have hQ : ∀ j, A.Quiet ids p j → j ≠ p → (A.upd p l).Quiet ids p j :=
        fun j hq hj => (quiet_upd hj).2 hq
      have hDd : ∀ a, a ∈ (A.loc p).D → a ∈ ((A.upd p l).loc p).D := by
        intro a ha; simp only [upd_loc_self, hl]; exact hd1 ha
      refine ⟨?_, fun _ => by simp [hl], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro w' h h2
        rcases upd_pend' hlst h with ⟨h', -⟩ | ⟨-, rfl⟩
        · exact absurd rfl h'
        · simp [hw] at h2; omega
      · intro h; exact absurd h hregp
      · intro j v' h h2 h3 h4
        obtain ⟨hj, h⟩ := hcopy j v' h
        rw [hloc j hj] at h3
        obtain ⟨c1, c2⟩ := Co.copyL j v' h h2 h3 h4
        exact ⟨fun h' => absurd h' hj, fun h' => (c2 h').trans (fun a ha => hDd a ha)⟩
      · intro h1 h2 j hj
        simp only [upd_reg] at h1 h2 hj
        have hjp : j ≠ p := by rintro rfl; exact hnotin _ (Or.inl rfl) hj
        rcases Co.regBot h1 h2 j hj with h | h
        · exact Or.inl (hDd _ h)
        · exact Or.inr (hQ j h hjp)
      · intro v' h; simp [hl] at h
      · intro v' h; simp [hl] at h
      · intro k w' h h2 h3 h4 j hj
        rcases upd_pend' hlst h with ⟨hk, h⟩ | ⟨rfl, rfl⟩
        · rw [hloc k hk]
          rcases Co.pendBot k w' h h2 h3 h4 j hj with h | h
          · exact Or.inl (hDd _ h)
          · exact Or.inr h
        · simp [hw] at h3
      · intro j hj
        simp only [upd_loc_self, hl] at hj
        have hjp : j ≠ p := by rintro rfl; exact hpd hj
        rcases Finset.mem_union.1 (hd2 hj) with h | h
        · exact hQ j (Co.quiet j h) hjp
        · -- an identifier merged from the copy
          by_cases hvC : v.phase = .committing
          swap
          · have hdD := hd4 (by rw [hph]; exact hvC)
            rw [hdD] at hj
            exact hQ j (Co.quiet j hj) hjp
          rcases Co.copyBot v hp hvL hidn hvC j h with h' | h'
          · exact hQ j (Co.quiet j h') hjp
          · exact hQ j h' hjp
      · intro j w' h h2
        rcases upd_pend' hlst h with ⟨-, h⟩ | ⟨-, rfl⟩
        · exact Co.n11 j w' h h2
        · simp [hw] at h2; omega

end BezoutElection.Alg2
