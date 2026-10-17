import Papers.PODC2020.BezoutElection.Alg2AbsRead

/-!
# Algorithm 2, per-register abstraction: the invariant is preserved by writes
-/

set_option linter.unusedSectionVars false

namespace BezoutElection.Alg2

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

namespace AState

/-- The state after `p` wrote `w`. -/
def wr (A : AState Id P) (p : P) (w : Reg Id) : AState Id P := ⟨w, (A.setSt p .fresh).loc⟩

@[simp] lemma wr_reg (A : AState Id P) (p : P) (w : Reg Id) : (A.wr p w).reg = w := rfl
@[simp] lemma wr_ph (A : AState Id P) (p j : P) (w : Reg Id) :
    ((A.wr p w).loc j).ph = (A.loc j).ph := setSt_ph A p j _
@[simp] lemma wr_D (A : AState Id P) (p j : P) (w : Reg Id) :
    ((A.wr p w).loc j).D = (A.loc j).D := setSt_D A p j _
@[simp] lemma wr_lo (A : AState Id P) (p j : P) (w : Reg Id) :
    ((A.wr p w).loc j).lo = (A.loc j).lo := setSt_lo A p j _
@[simp] lemma wr_lv (A : AState Id P) (p j : P) (w : Reg Id) :
    ((A.wr p w).loc j).lv = (A.loc j).lv := setSt_lv A p j _
@[simp] lemma wr_ca (A : AState Id P) (p j : P) (w : Reg Id) :
    ((A.wr p w).loc j).ca = (A.loc j).ca := setSt_ca A p j _
@[simp] lemma wr_st_self (A : AState Id P) (p : P) (w : Reg Id) :
    ((A.wr p w).loc p).st = .fresh := setSt_st_self A p _
lemma wr_st_ne (A : AState Id P) {p j : P} (w : Reg Id) (h : j ≠ p) :
    ((A.wr p w).loc j).st = (A.loc j).st := setSt_st_ne A _ h

end AState

lemma wr_copy {A : AState Id P} {p j : P} {w v : Reg Id} (h : ((A.wr p w).loc j).st = .copy v) :
    j ≠ p ∧ (A.loc j).st = .copy v := by
  by_cases hj : j = p
  · subst hj; simp at h
  · exact ⟨hj, by rwa [wr_st_ne _ _ hj] at h⟩

lemma wr_pend {A : AState Id P} {p j : P} {w w' : Reg Id} (h : ((A.wr p w).loc j).st = .pend w') :
    j ≠ p ∧ (A.loc j).st = .pend w' := by
  by_cases hj : j = p
  · subst hj; simp at h
  · exact ⟨hj, by rwa [wr_st_ne _ _ hj] at h⟩

/-- A quiet process (committing loser whose copy contains it or has no identifier) does not
write when it processes its copy. -/
lemma procX_quiet {me : Id} {l : ALoc Id} {r : Reg Id} {ok fin : Bool}
    (_hph : l.ph = .committing) (hlo : l.lo = true)
    (hr : r.id = none ∨ (r.phase = .committing ∧ me ∈ r.disc)) :
    (procX n U me l r ok fin).2 = none := by
  unfold procX
  split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> try rfl
  · rcases hr with hr | hr
    · exact absurd hr h3.2
    · exact absurd hr.2 h5
  · rcases hr with hr | hr
    · exact absurd hr h3.2
    · exact absurd hr.1 h4
  · rw [hlo] at h6; exact absurd h6.2.1 (by simp)
  · rcases hr with hr | hr
    · exact absurd hr h7.1
    · exact absurd hr.2 h7.2.2

/-- Writing a value of the current level. -/
theorem ainv_write_cur (hid : Function.Injective ids) {A : AState Id P} {p : P} {w : Reg Id}
    (hI : AInv n U ids A) (hp : (A.loc p).st = .pend w) (hw : w.level = A.reg.level)
    (hwl : w.leaders = A.reg.leaders) : AInv n U ids (A.wr p w) := by
  obtain ⟨B, hL⟩ := hI
  have hval : ∀ u, (A.wr p w).Val u → A.Val u := by
    rintro u (rfl | ⟨j, h1, h2⟩ | ⟨j, h1, h2, h3⟩)
    · exact Or.inr (Or.inl ⟨p, hp, hw⟩)
    · exact Or.inr (Or.inl ⟨j, (wr_pend h1).2, by simpa [hw] using h2⟩)
    · exact Or.inr (Or.inr ⟨j, (wr_copy h1).2, by simpa [hw] using h2, by simpa [hw] using h3⟩)
  have hAL : ∀ a, A.ActLoser ids a → (A.wr p w).ActLoser ids a := by
    rintro a ⟨i, h1, h2, h3⟩; exact ⟨i, h1, by simpa [hw] using h2, by simpa using h3⟩
  have hthr : ∀ j, (A.wr p w).Threat ids j → A.Threat ids j := by
    rintro j ⟨v, h1, h2, h3, h4⟩
    exact ⟨v, (wr_copy h1).2, by simpa [hw] using h2, by simpa [hw] using h3, h4⟩
  -- the identifier written is the writer's
  have hwid : ∀ a, w.id = some a → a = ids p ∧ w.disc = (A.loc p).D ∧ w.phase = (A.loc p).ph ∧
      (A.loc p).lo = false ∧ (A.loc p).ca = true := by
    intro a ha
    obtain ⟨h1, h2⟩ := B.pendId p w hp hw (by simp [ha])
    rw [ha] at h1; exact ⟨Option.some.inj h1, h2⟩
  have hlvp := (B.pendLv p w hp).1
  refine ⟨⟨by simpa [hw] using B.lvU, by simpa [hw] using B.lvLe, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, fun j h => by simpa [hw] using B.caU j (by simpa using h), ?_, ?_⟩, ?_⟩
  · intro j v h; simpa [hw] using B.copyLv j v (wr_copy h).2
  · intro j w' h
    obtain ⟨-, h⟩ := wr_pend h
    simpa [hw, hwl, IsN11] using B.pendLv j w' h
  · intro j v h; simpa [hw, hwl] using B.copyLead j v (wr_copy h).2
  · intro j v h h1 h2
    obtain ⟨hj, h⟩ := wr_copy h
    simp only [wr, setSt, upd_loc_ne _ _ hj] at h1 h2 ⊢
    exact B.dead j v h h1 (by rw [hw] at h2; exact h2)
  · intro j h; simpa using B.lagCa j (by simpa [hw] using h)
  · intro u hu a ha; exact hAL a (B.disc u (hval u hu) a ha)
  · intro j hj a ha; exact hAL a (B.discLoc j (by simpa [hw] using hj) a (by simpa using ha))
  · intro j w' h h1 h2
    simpa using B.pendId j w' (wr_pend h).2 (by simpa [hw] using h1) h2
  · obtain ⟨j0, hj0⟩ := B.nonloser
    refine ⟨j0, ?_⟩
    rcases hj0 with h | ⟨h1, h2⟩
    · exact Or.inl (by simpa [hw] using h)
    · exact Or.inr ⟨by simpa using h1, fun h => h2 (hthr j0 h)⟩
  · intro a ha
    obtain ⟨rfl, -, -, h1, -⟩ := hwid a ha
    exact ⟨p, rfl, by simpa [hw] using hlvp, by simpa using h1⟩
  · intro j h; simpa [hw] using B.caAct j (by simpa using h)
  · intro j v h ha
    obtain ⟨hj, -⟩ := wr_copy h
    exact absurd (hid (hwid _ ha).1) hj
  · intro a ha
    obtain ⟨rfl, -, -, -, h1⟩ := hwid a ha
    exact ⟨p, rfl, Or.inl (by simpa using h1)⟩
  · rcases B.wit with hP | ⟨c, hc, hT⟩ | ⟨c, w', hw', hl⟩
    · left
      obtain ⟨h1, h2, h3, h4⟩ := hP
      refine ⟨fun j hj => by simpa using h1 j (by simpa [hw] using hj), by simpa using h3 p w hp hw,
        fun j w' h hl => h3 j w' (wr_pend h).2 (by simpa [hw] using hl),
        fun j v h hl hj => h4 j v (wr_copy h).2 (by simpa [hw] using hl) (by simpa [hw] using hj)⟩
    · exact Or.inr (Or.inl ⟨c, by simpa using hc, fun h => hT (hthr c h)⟩)
    · have hcp : c ≠ p := by rintro rfl; rw [hp] at hw'; cases hw'; omega
      exact Or.inr (Or.inr ⟨c, w', by rw [wr_st_ne _ _ hcp]; exact hw', by simpa [hw] using hl⟩)
  · rcases hL with N | ⟨ℓ, E⟩
    · left
      exact ⟨fun u hu => N.valsEl u (hval u hu), fun j hj => by simpa using N.phEl j (by simpa [hw] using hj),
        fun j w' h => by simpa [hw] using N.noN11 j w' (wr_pend h).2,
        fun c h1 h2 h3 => by
          simpa using N.strict c (by simpa [hw] using h1) (by simpa using h2) (by simpa using h3)⟩
    · right
      -- writes with an identifier are the leader's
      have hwℓ : ∀ a, w.id = some a → p = ℓ := by
        intro a ha
        obtain ⟨-, -, -, h1, -⟩ := hwid a ha
        by_contra hne
        have := (E.others p hne).2; rw [h1] at this; cases this
      refine ⟨ℓ, ⟨by simpa [hw] using E.act, fun j hj => by simpa [hw] using E.others j hj, ?_, ?_, ?_, ?_⟩⟩
      · intro j v h h1 h2 h3 h4
        simpa using E.copyOther j v (wr_copy h).2 (by simpa [hw] using h1) (by simpa [hw] using h2) h3 h4
      · intro j v h h1 h2 h3 h4 h5
        simpa using E.copyLE j v (wr_copy h).2 (by simpa [hw] using h1) (by simpa [hw] using h2) h3 h4 h5
      · intro hph
        have El := E.el (by simpa using hph)
        refine ⟨by simpa using El.card, by simpa using El.ca, ?_, ?_, fun u hu => El.coVals u (hval u hu),
          fun j w' h => by simpa [hw] using El.noN11 j w' (wr_pend h).2⟩
        · intro ha
          have hpl := hwℓ _ ha; subst hpl
          obtain ⟨-, h2, h3, -⟩ := hwid _ ha
          simp only [wr_reg]; rw [h2, h3]; exact ⟨by simpa using hph, El.card⟩
        · intro j v h h1 h2 h3
          exact El.copyL j v (wr_copy h).2 (by simpa [hw] using h1) (by simpa [hw] using h2) h3
      · intro hph
        have Co := E.co (by simpa using hph)
        have hQ : ∀ j, j ≠ p → A.Quiet ids ℓ j → (w.id = some (ids ℓ) → ids j ∈ w.disc) →
            (A.wr p w).Quiet ids ℓ j := by
          intro j hj ⟨q1, q2, q3, _⟩ q4
          refine ⟨by simpa using q1, fun w' h => q2 w' (by rwa [wr_st_ne _ _ hj] at h), ?_, q4⟩
          intro v h h1
          rw [wr_st_ne _ _ hj] at h
          exact q3 v h (by simpa [hw] using h1)
        -- `p` itself is not quiet before the write
        have hnq : ¬A.Quiet ids ℓ p := fun h => h.2.1 w hp
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro w' h h1
          simpa using Co.closing w' (wr_pend h).2 (by simpa [hw] using h1)
        · intro hall
          by_cases hℓ : ℓ = p
          · subst hℓ
            simpa using Co.ca (fun w' h => by rw [hp] at h; cases h; exact hw)
          · simpa using Co.ca (fun w' h => by
              have := hall w' (by rwa [wr_st_ne _ _ hℓ]); simpa [hw] using this)
        · intro ha
          have hpl := hwℓ _ ha; subst hpl
          obtain ⟨-, h2, h3, -⟩ := hwid _ ha
          simp only [wr_reg]; rw [h2, h3]
          exact ⟨by simpa using hph, by simp⟩
        · intro j v h h1 h2 h3
          simpa using Co.copyL j v (wr_copy h).2 (by simpa [hw] using h1) (by simpa [hw] using h2) h3
        · intro h1 h2 j hj
          simp only [wr_reg] at h1 h2 hj
          rcases Co.pendBot p w hp hw h1 h2 j hj with h | ⟨rfl, h⟩
          · exact Or.inl (by simpa using h)
          · refine Or.inr ⟨by simpa using h, fun w' h' => by simp at h', fun v h' => by simp at h', ?_⟩
            intro h'; simp only [wr_reg] at h'; rw [h1] at h'; cases h'
        · intro v h h1 h2 h3 j hj
          obtain ⟨hℓp, h⟩ := wr_copy h
          rcases Co.copyBot v h (by simpa [hw] using h1) h2 h3 j hj with hq | hq
          · exact Or.inl (by simpa using hq)
          · have hjp : j ≠ p := by rintro rfl; exact hnq hq
            exact Or.inr (hQ j hjp hq (fun ha => absurd (hwℓ _ ha).symm hℓp))
        · intro v h h1 h2
          obtain ⟨hℓp, h⟩ := wr_copy h
          simp only [wr_reg]
          cases hwi : w.id with
          | none => rfl
          | some a => exact absurd (hwℓ a hwi).symm hℓp
        · intro k w' h h1 h2 h3 j hj
          obtain ⟨-, h⟩ := wr_pend h
          simpa using Co.pendBot k w' h (by simpa [hw] using h1) h2 h3 j hj
        · intro j hj
          have hq := Co.quiet j (by simpa using hj)
          have hjp : j ≠ p := by rintro rfl; exact hnq hq
          refine hQ j hjp hq (fun ha => ?_)
          have hpl := hwℓ _ ha; subst hpl
          rw [(hwid _ ha).2.1]; simpa using hj
        · intro k w' h h1
          exact Co.n11 k w' (wr_pend h).2 (by simpa [hw] using h1)

/-- Writing the value of line N(11): the competition is over, a new one starts. -/
theorem ainv_write_n11 (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {A : AState Id P} {p : P} {w : Reg Id}
    (hI : AInv n U ids A) (hp : (A.loc p).st = .pend w) (hN : A.IsN11 ids p w) :
    AInv n U ids (A.wr p w) := by
  obtain ⟨B, hL⟩ := hI
  obtain ⟨hw1, hw2, hw3, hw4, -, -⟩ := hN
  -- we are in the committing phase of the leader `p`
  obtain ⟨ℓ, E⟩ : ∃ ℓ, Lead n ids A ℓ := by
    rcases hL with N | h
    · have := N.noN11 p w hp; omega
    · exact h
  have hphℓ : (A.loc ℓ).ph = .committing := by
    rcases hph : (A.loc ℓ).ph with _ | _
    · have := (E.el hph).noN11 p w hp; omega
    · rfl
  have Co := E.co hphℓ
  have hpℓ := Co.n11 p w hp hw1; subst hpℓ
  obtain ⟨hcard, hca⟩ := Co.closing w hp hw1
  have hall : ∀ j, j ≠ p → A.Quiet ids p j := by
    intro j hj
    refine Co.quiet j (mem_of_card_eq_of_ne hid hn _ p (fun a ha => ?_) hcard j hj)
    obtain ⟨i, rfl, -, hi⟩ := B.discLoc p E.act.1 a ha
    exact ⟨i, rfl, by rintro rfl; rw [E.act.2] at hi; cases hi⟩
  have hnopend : ∀ j w', ((A.wr p w).loc j).st = .pend w' → False := by
    intro j w' h
    obtain ⟨hj, h⟩ := wr_pend h
    exact (hall j hj).2.1 w' h
  have hcaf : ∀ j, (A.loc j).ca = false := by
    intro j
    by_cases hj : j = p
    · subst hj; exact hca
    · cases hc : (A.loc j).ca
      · rfl
      · have := (B.caAct j hc).2; rw [(E.others j hj).2] at this; cases this
  have hcopy : ∀ j v, ((A.wr p w).loc j).st = .copy v → v.level < w.level := by
    intro j v h
    have := (B.copyLv j v (wr_copy h).2).2; omega
  have hlvle : ∀ j, (A.loc j).lv < w.level := by intro j; have := B.lvLe j; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨p, Or.inl (by simpa using hlvle p)⟩, ?_, ?_, ?_,
    fun j h => (by simp [hcaf j] at h), fun a ha => (by simp only [wr_reg, hw2] at ha; cases ha),
    Or.inl ⟨fun j hj => absurd hj (by simpa using (hlvle j).ne), by simpa using hw2,
      fun j w' h _ => (hnopend j w' h).elim, fun j v h hl _ => absurd hl (hcopy j v h).ne⟩⟩,
    Or.inl ⟨?_, ?_, ?_, fun c hc => absurd hc (by simpa using (hlvle c).ne)⟩⟩
  · have := (B.pendLv p w hp).2.1; simp only [wr_reg]; omega
  · intro j; simpa using (hlvle j).le
  · intro j v h
    obtain ⟨-, h'⟩ := wr_copy h
    have := B.copyLv j v h'
    simp only [wr_lv, wr_reg]; omega
  · intro j w' h; exact (hnopend j w' h).elim
  · intro j v h h1; exact absurd h1 (by simp only [wr_reg]; exact (hcopy j v h).ne)
  · intro j v h h1 h2 ok fin
    obtain ⟨hj, h'⟩ := wr_copy h
    simp only [wr, setSt, upd_loc_ne _ _ hj, upd_reg] at h1 h2 ⊢
    rcases (B.lvLe j).lt_or_eq with hlt | heq
    · exact B.dead j v h' h1 hlt ok fin
    · have hq := hall j hj
      exact procX_quiet hq.1 (E.others j hj).2 (hq.2.2.1 v h' (by rw [h1, heq]))
  · intro j _; simpa using hcaf j
  · rintro u (rfl | ⟨j, h1, -⟩ | ⟨j, h1, h2, -⟩)
    · simp [hw3]
    · exact (hnopend j u h1).elim
    · exact absurd h2 (hcopy j u h1).ne
  · intro j hj; exact absurd hj (by simpa using (hlvle j).ne)
  · intro j w' h; exact (hnopend j w' h).elim
  · intro a ha; simp only [wr_reg, hw2] at ha; cases ha
  · intro j h; simp [hcaf j] at h
  · intro j v _ ha; simp only [wr_reg, hw2] at ha; cases ha
  · rintro u (rfl | ⟨j, h1, -⟩ | ⟨j, h1, h2, -⟩)
    · simp [hw4, hw2]
    · exact (hnopend j u h1).elim
    · exact absurd h2 (hcopy j u h1).ne
  · intro j hj; exact absurd hj (by simpa using (hlvle j).ne)
  · intro j w' h; exact (hnopend j w' h).elim

/-- Writes preserve the invariant. -/
theorem ainv_write (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {A : AState Id P} {p : P} {w : Reg Id}
    (hI : AInv n U ids A) (hp : (A.loc p).st = .pend w) : AInv n U ids (A.wr p w) := by
  rcases (hI.1.pendLv p w hp).2.2 with ⟨h1, h2⟩ | h
  · exact ainv_write_cur hid hI hp h1 h2
  · exact ainv_write_n11 hid hn hI hp h

end BezoutElection.Alg2
