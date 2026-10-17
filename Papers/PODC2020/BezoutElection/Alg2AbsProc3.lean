import Papers.PODC2020.BezoutElection.Alg2AbsProc2

/-!
# Algorithm 2, per-register abstraction: processing a copy (part 3)

Writing steps: the end of a competition (lines N(8)–N(11)) and the start of the committing phase
(line 8).
-/

set_option linter.unusedSectionVars false

namespace BezoutElection.Alg2

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

lemma upd_pend' {A : AState Id P} {p j : P} {l : ALoc Id} {w w' : Reg Id} (hl : l.st = .pend w)
    (h : ((A.upd p l).loc j).st = .pend w') :
    (j ≠ p ∧ (A.loc j).st = .pend w') ∨ (j = p ∧ w' = w) := by
  rcases upd_pend h with h' | ⟨rfl, h'⟩
  · exact Or.inl h'
  · rw [hl] at h'; cases h'; exact Or.inr ⟨rfl, rfl⟩

lemma upd_val' {A : AState Id P} {p : P} {l : ALoc Id} {w u : Reg Id} (hl : l.st = .pend w)
    (h : (A.upd p l).Val u) : A.Val u ∨ (u = w ∧ w.level = A.reg.level) := by
  rcases upd_val (fun v h' => by rw [hl] at h'; cases h') h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · rw [hl] at h1; cases h1; exact Or.inr ⟨rfl, h2⟩

/-- A copy of the current level held by an active process is a value. -/
lemma val_copy {A : AState Id P} {p : P} {v : Reg Id} (hp : (A.loc p).st = .copy v)
    (h1 : v.level = (A.loc p).lv) (hact : (A.loc p).lv = A.reg.level) : A.Val v :=
  Or.inr (Or.inr ⟨p, hp, h1.trans hact, hact⟩)

/-- Processes in a `discarded` set of the current competition are not the leader. -/
lemma ne_of_actLoser {A : AState Id P} {ℓ : P} (E : Lead n ids A ℓ) {a : Id}
    (h : A.ActLoser ids a) : ∃ j, ids j = a ∧ j ≠ ℓ := by
  obtain ⟨i, h1, -, h3⟩ := h
  exact ⟨i, h1, by rintro rfl; rw [E.act.2] at h3; cases h3⟩

/-- The end of a competition: the winner `p` writes the next level (lines N(8)–N(11)). -/
theorem ainv_win (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {A : AState Id P} {p : P} {v : Reg Id} {lead : Finset Id}
    (hI : AInv n U ids A) (hp : (A.loc p).st = .copy v) (hact : (A.loc p).lv = A.reg.level)
    (h1 : v.level = (A.loc p).lv) (h1' : v.level < U) (hc : v.disc.card = n - 1)
    (hid' : v.id ≠ none) (hC : v.phase = .committing) (hme : ids p ∉ v.disc)
    (hl1 : v.leaders ⊆ lead) (hl2 : lead ⊆ insert (ids p) v.leaders) :
    AInv n U ids (A.upd p
      { A.loc p with ca := false, st := .pend ⟨none, ∅, .electing, v.level + 1, lead⟩ }) := by
  obtain ⟨B, hL⟩ := hI
  have hvV := val_copy hp h1 hact
  have hvL : v.level = A.reg.level := h1.trans hact
  set w : Reg Id := ⟨none, ∅, .electing, v.level + 1, lead⟩ with hw
  set l : ALoc Id := { A.loc p with ca := false, st := .pend w } with hl
  have hlst : l.st = .pend w := rfl
  have hnc : ∀ v, l.st ≠ .copy v := by intro v h; cases h
  have hcopy : ∀ j v', ((A.upd p l).loc j).st = .copy v' → j ≠ p ∧ (A.loc j).st = .copy v' :=
    fun j v' h => upd_copy hnc h
  have hloc : ∀ j, j ≠ p → (A.upd p l).loc j = A.loc j := fun j hj => upd_loc_ne _ _ hj
  have hval : ∀ u, (A.upd p l).Val u → A.Val u := by
    intro u hu
    rcases upd_val' hlst hu with h | ⟨-, h⟩
    · exact h
    · simp [hw] at h; omega
  have hAL : ∀ a, A.ActLoser ids a → (A.upd p l).ActLoser ids a :=
    fun a h => actLoser_upd h (fun h1 h2 => ⟨h1, h2⟩)
  -- we are in the committing phase of the leader `p`
  obtain ⟨ℓ, E⟩ : ∃ ℓ, Lead n ids A ℓ := by
    rcases hL with N | h
    · exact absurd hc ((N.valsEl v hvV).2 hid')
    · exact h
  have hvℓ : v.id = some (ids ℓ) := by
    by_contra h
    exact (E.copyOther p v hp hvL hact hid' h).2.2.2 hc
  have hpℓ : p = ℓ := by
    by_contra h
    exact hme (mem_of_card_eq_of_ne hid hn _ ℓ (fun a ha => ne_of_actLoser E (B.disc v hvV a ha))
      hc p h)
  subst hpℓ
  have hphp : (A.loc p).ph = .committing := by
    rcases hph : (A.loc p).ph with _ | _
    · have := (E.el hph).copyL p v hp hvL hact hvℓ; rw [hC] at this; cases this
    · rfl
  have Co := E.co hphp
  have hcard : (A.loc p).D.card = n - 1 := by
    have hsub := (Co.copyL p v hp hvL hact hvℓ).2 hC
    have h1 := Finset.card_le_card hsub
    have h2 := card_le_of_ne hn (A.loc p).D p
      (fun a ha => ne_of_actLoser E (B.discLoc p hact a ha))
    omega
  have hQ : ∀ j, A.Quiet ids p j → j ≠ p → (A.upd p l).Quiet ids p j :=
    fun j hq hj => (quiet_upd hj).2 hq
  have hnotin : ∀ u, A.Val u → ids p ∉ u.disc := fun u hu h => E.not_actLoser hid (B.disc u hu _ h)
  refine ⟨⟨B.lvU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    Or.inr (Or.inr ⟨p, w, by simp [hl], by simp [hw, hvL]⟩)⟩, Or.inr ⟨p, ?_⟩⟩
  · intro j; by_cases hj : j = p
    · subst hj; simpa [hl] using B.lvLe j
    · rw [hloc j hj]; exact B.lvLe j
  · intro j v' h; obtain ⟨hj, h⟩ := hcopy j v' h; rw [hloc j hj]; exact B.copyLv j v' h
  · intro j w' h
    rcases upd_pend' hlst h with ⟨hj, h⟩ | ⟨rfl, rfl⟩
    · rw [hloc j hj]; exact B.pendLv j w' h
    · simp only [upd_loc_self, upd_reg, hl]
      refine ⟨hact, by omega, Or.inr ⟨by simp [hw, hvL], rfl, rfl, rfl, ?_, ?_⟩⟩
      · simp only [upd_reg]; rw [← B.copyLead j v hp hvL]; exact hl1
      · simp only [upd_reg]; rw [← B.copyLead j v hp hvL]; exact hl2
  · intro j v' h; exact B.copyLead j v' (hcopy j v' h).2
  · intro j v' h; obtain ⟨hj, h⟩ := hcopy j v' h; rw [hloc j hj]; exact B.dead j v' h
  · intro j hj'; by_cases hj : j = p
    · subst hj; simp [hl]
    · rw [hloc j hj] at hj' ⊢; exact B.lagCa j hj'
  · intro u hu a ha; exact hAL a (B.disc u (hval u hu) a ha)
  · intro j hj' a ha
    by_cases hj : j = p
    · subst hj; simp [hl] at hj' ha; exact hAL a (B.discLoc j hj' a ha)
    · rw [hloc j hj] at hj' ha; exact hAL a (B.discLoc j hj' a ha)
  · intro j w' h h2
    rcases upd_pend' hlst h with ⟨hj, h⟩ | ⟨rfl, rfl⟩
    · rw [hloc j hj]; exact B.pendId j w' h h2
    · simp [hw] at h2; omega
  · refine ⟨p, Or.inr ⟨by simpa [hl] using E.act.2, ?_⟩⟩
    rintro ⟨v', h1, -⟩; simp [hl] at h1
  · intro a ha
    obtain ⟨c, h1, h2, h3⟩ := B.regId a ha
    refine ⟨c, h1, ?_⟩
    by_cases hc : c = p
    · subst hc; simpa [hl] using ⟨h2, h3⟩
    · rw [hloc c hc]; exact ⟨h2, h3⟩
  · intro j h; by_cases hj : j = p
    · subst hj; simp [hl] at h
    · rw [hloc j hj] at h ⊢; exact B.caAct j h
  · intro j v' h hr; obtain ⟨hj, h⟩ := hcopy j v' h; exact B.copyOwn j v' h hr
  · intro j h; by_cases hj : j = p
    · subst hj; simp [hl] at h
    · rw [hloc j hj] at h; exact B.caU j h
  · intro a ha
    obtain ⟨c, h1, h2⟩ := B.regCa a ha
    refine ⟨c, h1, ?_⟩
    by_cases hcp : c = p
    · rw [hcp]; exact Or.inr ⟨w, by simp [hl], by simp [hw, hvL]⟩
    · rw [hloc c hcp]; exact h2
  · refine ⟨by simpa [hl] using E.act, fun j hj => by rw [hloc j hj]; exact E.others j hj, ?_, ?_,
      fun h => by simp [hl, hphp] at h, fun _ => ?_⟩
    · intro j v' h h2 h3 h4 h5
      obtain ⟨hj, h⟩ := hcopy j v' h
      rw [hloc j hj] at h3 ⊢
      exact E.copyOther j v' h h2 h3 h4 h5
    · intro j v' h h2 h3 h4 h5 h6
      obtain ⟨hj, h⟩ := hcopy j v' h
      rw [hloc j hj] at h3 ⊢
      exact E.copyLE j v' h h2 h3 h4 h5 h6
    · refine ⟨?_, ?_, by simpa [hl] using Co.regL, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro w' _ _; simp [hl, hcard]
      · intro h
        have := h w (by simp [hl]); simp [hw] at this; omega
      · intro j v' h h2 h3 h4
        obtain ⟨hj, h⟩ := hcopy j v' h
        rw [hloc j hj] at h3
        simpa [hl] using Co.copyL j v' h h2 h3 h4
      · intro h1 h2 j hj
        simp only [upd_reg] at h1 h2 hj
        have hjp : j ≠ p := by rintro rfl; exact hnotin _ (Or.inl rfl) hj
        rcases Co.regBot h1 h2 j hj with h | h
        · exact Or.inl (by simpa [hl] using h)
        · exact Or.inr (hQ j h hjp)
      · intro v' h; simp [hl] at h
      · intro v' h; simp [hl] at h
      · intro k w' h h2 h3 h4 j hj
        rcases upd_pend' hlst h with ⟨hk, h⟩ | ⟨rfl, rfl⟩
        · rw [hloc k hk]; simpa [hl] using Co.pendBot k w' h h2 h3 h4 j hj
        · simp [hw] at h2; omega
      · intro j hj
        simp only [upd_loc_self, hl] at hj
        have hjp : j ≠ p := by
          rintro rfl; exact E.not_actLoser hid (B.discLoc j hact _ hj)
        exact hQ j (Co.quiet j hj) hjp
      · intro j w' h h2
        rcases upd_pend' hlst h with ⟨hj, h⟩ | ⟨rfl, -⟩
        · exact Co.n11 j w' h h2
        · rfl

/-- The start of the committing phase (line 8): the value `⟨⊥, ∅, committing⟩` is written. -/
theorem ainv_line8 {A : AState Id P} {p : P} {v : Reg Id}
    (hI : AInv n U ids A) (hp : (A.loc p).st = .copy v) (hact : (A.loc p).lv = A.reg.level)
    (h1 : v.level = (A.loc p).lv) (h1' : v.level < U) (hc : v.disc.card = n - 1)
    (hid' : v.id ≠ none) (hE : v.phase = .electing) :
    AInv n U ids (A.upd p
      { A.loc p with st := .pend ⟨none, ∅, .committing, v.level, v.leaders⟩ }) := by
  obtain ⟨B, hL⟩ := hI
  have hvV := val_copy hp h1 hact
  have hvL : v.level = A.reg.level := h1.trans hact
  set w : Reg Id := ⟨none, ∅, .committing, v.level, v.leaders⟩ with hw
  set l : ALoc Id := { A.loc p with st := .pend w } with hl
  have hlst : l.st = .pend w := rfl
  have hnc : ∀ v, l.st ≠ .copy v := by intro v h; cases h
  have hcopy : ∀ j v', ((A.upd p l).loc j).st = .copy v' → j ≠ p ∧ (A.loc j).st = .copy v' :=
    fun j v' h => upd_copy hnc h
  have hloc : ∀ j, j ≠ p → (A.upd p l).loc j = A.loc j := fun j hj => upd_loc_ne _ _ hj
  have hAL : ∀ a, A.ActLoser ids a → (A.upd p l).ActLoser ids a :=
    fun a h => actLoser_upd h (fun h1 h2 => ⟨h1, h2⟩)
  have hthr : ∀ j, (A.upd p l).Threat ids j → A.Threat ids j := by
    rintro j ⟨v', h1, h2, h3, h4⟩
    obtain ⟨hj, h1⟩ := hcopy j v' h1
    exact ⟨v', h1, h2, by rwa [hloc j hj] at h3, h4⟩
  obtain ⟨ℓ, E⟩ : ∃ ℓ, Lead n ids A ℓ := by
    rcases hL with N | h
    · exact absurd hc ((N.valsEl v hvV).2 hid')
    · exact h
  have hvℓ : v.id = some (ids ℓ) := by
    by_contra h
    exact (E.copyOther p v hp hvL hact hid' h).2.2.2 hc
  refine ⟨⟨B.lvU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inr ⟨ℓ, ?_⟩⟩
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
    · simp [hw] at ha
  · intro j hj' a ha
    by_cases hj : j = p
    · subst hj; simp [hl] at hj' ha; exact hAL a (B.discLoc j hj' a ha)
    · rw [hloc j hj] at hj' ha; exact hAL a (B.discLoc j hj' a ha)
  · intro j w' h h2 h3
    rcases upd_pend' hlst h with ⟨hj, h⟩ | ⟨rfl, rfl⟩
    · rw [hloc j hj]; exact B.pendId j w' h h2 h3
    · simp [hw] at h3
  · obtain ⟨j0, hj0⟩ := B.nonloser
    refine ⟨j0, ?_⟩
    by_cases hj : j0 = p
    · subst hj
      rcases hj0 with h | ⟨h, -⟩
      · left; simpa [hl] using h
      · right; refine ⟨by simpa [hl] using h, ?_⟩
        rintro ⟨v', h1, -⟩; simp [hl] at h1
    · rw [hloc j0 hj]; rcases hj0 with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, fun h => h2 (hthr j0 h)⟩
  · intro a ha
    obtain ⟨c, h1, h2, h3⟩ := B.regId a ha
    refine ⟨c, h1, ?_⟩
    by_cases hc : c = p
    · subst hc; simpa [hl] using ⟨h2, h3⟩
    · rw [hloc c hc]; exact ⟨h2, h3⟩
  · intro j h; by_cases hj : j = p
    · subst hj; simpa [hl] using B.caAct j (by simpa [hl] using h)
    · rw [hloc j hj] at h ⊢; exact B.caAct j h
  · intro j v' h hr; obtain ⟨hj, h⟩ := hcopy j v' h; exact B.copyOwn j v' h hr
  · intro j h; by_cases hj : j = p
    · subst hj; exact B.caU j (by simpa [hl] using h)
    · rw [hloc j hj] at h; exact B.caU j h
  · intro a ha
    obtain ⟨c, h1, h2⟩ := B.regCa a ha
    refine ⟨c, h1, ?_⟩
    by_cases hcp : c = p
    · rw [hcp] at h2 ⊢
      rcases h2 with h2 | ⟨w', hw', -⟩
      · exact Or.inl (by simpa [hl] using h2)
      · rw [hp] at hw'; cases hw'
    · rw [hloc c hcp]; exact h2
  · rcases B.wit with hP | ⟨c, hc, hT⟩ | ⟨c, w', hw', hl'⟩
    · exfalso; exact hid' (hP.2.2.2 p v hp hvL hact)
    · by_cases hcp : c = p
      · rw [hcp] at hc
        refine Or.inr (Or.inl ⟨p, by simpa [hl] using hc, ?_⟩)
        rintro ⟨v', h1, -⟩; simp [hl] at h1
      · exact Or.inr (Or.inl ⟨c, by rw [hloc c hcp]; exact hc, by rw [threat_upd hcp]; exact hT⟩)
    · have hcp : c ≠ p := by rintro rfl; rw [hp] at hw'; cases hw'
      exact Or.inr (Or.inr ⟨c, w', by rw [hloc c hcp]; exact hw', hl'⟩)
  · have hℓloc : ((A.upd p l).loc ℓ).ph = (A.loc ℓ).ph ∧ ((A.upd p l).loc ℓ).D = (A.loc ℓ).D ∧
        ((A.upd p l).loc ℓ).ca = (A.loc ℓ).ca := by
      by_cases hℓ : ℓ = p
      · subst hℓ; simp [hl]
      · rw [hloc ℓ hℓ]; exact ⟨rfl, rfl, rfl⟩
    refine ⟨?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
    · by_cases hℓ : ℓ = p
      · subst hℓ; simpa [hl] using E.act
      · rw [hloc ℓ hℓ]; exact E.act
    · by_cases hjp : j = p
      · subst hjp; simpa [hl] using E.others j hj
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
      rw [hℓloc.1] at hph
      have El := E.el hph
      refine ⟨by rw [hℓloc.2.1]; exact El.card, by rw [hℓloc.2.2]; exact El.ca, El.regL, ?_, ?_, ?_⟩
      · intro j v' h h2 h3 h4
        obtain ⟨hj, h⟩ := hcopy j v' h
        rw [hloc j hj] at h3
        exact El.copyL j v' h h2 h3 h4
      · intro u hu hC
        rcases upd_val' hlst hu with h | ⟨rfl, -⟩
        · exact El.coVals u h hC
        · exact ⟨rfl, rfl⟩
      · intro j w' h
        rcases upd_pend' hlst h with ⟨-, h⟩ | ⟨-, rfl⟩
        · exact El.noN11 j w' h
        · exact hvL
    · intro hph
      rw [hℓloc.1] at hph
      have Co := E.co hph
      have hpℓ : p ≠ ℓ := by
        rintro rfl
        have := (Co.copyL p v hp hvL hact hvℓ).1 rfl; rw [hE] at this; cases this
      have hℓ : (A.upd p l).loc ℓ = A.loc ℓ := hloc ℓ (Ne.symm hpℓ)
      have hnq : ¬A.Quiet ids ℓ p := by
        intro hq
        rcases hq.2.2.1 v hp hvL with h | ⟨h, -⟩
        · exact hid' h
        · rw [hE] at h; cases h
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
        · simp [hw] at hj
      · intro j hj
        rw [hℓ] at hj
        have hq := Co.quiet j hj
        have hjp : j ≠ p := by rintro rfl; exact hnq hq
        exact (quiet_upd hjp).2 hq
      · intro j w' h h1
        rcases upd_pend' hlst h with ⟨-, h⟩ | ⟨-, rfl⟩
        · exact Co.n11 j w' h h1
        · simp [hw] at h1; omega

end BezoutElection.Alg2
