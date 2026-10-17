import Papers.PODC2020.BezoutElection.Alg2AbsProc5

/-!
# Algorithm 2, per-register abstraction: initial state and consequences of the invariant
-/

set_option linter.unusedSectionVars false

namespace BezoutElection.Alg2

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

/-- The initial abstract state satisfies the invariant. -/
theorem ainv_init [Nonempty P] :
    AInv n U ids (⟨Reg.init, fun _ => ⟨.electing, ∅, false, 0, false, .fresh⟩⟩ : AState Id P) := by
  obtain ⟨q⟩ := ‹Nonempty P›
  refine ⟨⟨by simp [Reg.init], fun _ => by simp [Reg.init], fun j v h => by simp at h,
    fun j w h => by simp at h, fun j v h => by simp at h, fun j v h => by simp at h,
    fun _ _ => rfl, ?_, fun j _ a ha => by simp at ha, fun j w h => by simp at h,
    ⟨q, Or.inr ⟨rfl, fun ⟨v, h, _⟩ => by simp at h⟩⟩, fun a h => by simp [Reg.init] at h,
    fun j h => by simp at h, fun j v h => by simp at h, fun j h => by simp at h,
    fun a h => by simp [Reg.init] at h,
    Or.inl ⟨fun _ _ => rfl, rfl, fun j w h => by simp at h, fun j v h => by simp at h⟩⟩,
    Or.inl ⟨?_, fun _ _ => rfl, fun j w h => by simp at h, fun c _ _ h => by simp at h⟩⟩
  · rintro u (rfl | ⟨j, h, -⟩ | ⟨j, h, -⟩) a ha
    · simp [Reg.init] at ha
    · simp at h
    · simp at h
  · rintro u (rfl | ⟨j, h, -⟩ | ⟨j, h, -⟩)
    · simp [Reg.init]
    · simp at h
    · simp at h

/-- A write decided when processing a copy: the copy is of the current level, and the written
level is either the current one or (end of the competition, by a candidate) the next one. -/
theorem write_facts (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {A : AState Id P} {p : P} {v w : Reg Id} {ok fin : Bool}
    (hI : AInv n U ids A) (hp : (A.loc p).st = .copy v)
    (hw : (procX n U (ids p) (A.loc p) v ok fin).2 = some w) :
    v.level = A.reg.level ∧ (A.loc p).lv = A.reg.level ∧
      (w.level = v.level ∨ (w.level = v.level + 1 ∧ (A.loc p).ca = true ∧
        w.leaders = if fin then insert (ids p) v.leaders else v.leaders)) := by
  obtain ⟨B, hL⟩ := hI
  have hact : ∀ l', procX n U (ids p) (A.loc p) v ok fin = (l', some w) →
      v.level = (A.loc p).lv → (A.loc p).lv = A.reg.level := by
    intro l' h h1
    rcases (B.lvLe p).lt_or_eq with hlt | heq
    · have := B.dead p v hp h1 hlt ok fin; rw [h] at this; cases this
    · exact heq
  rcases procX_cases n U (ids p) (A.loc p) v ok fin with
    ⟨h1, h2, h⟩ | h | ⟨h1, h1', h2, h3, h⟩ | ⟨h1, h1', h2, h3, h4, h5, h⟩ |
    ⟨h1, h1', h2, h3, h4, h⟩ | ⟨h1, h1', h2, h3, h4, h⟩ | ⟨h1, h1', h2, h3, h4, h5, h6, h⟩ <;>
    rw [h] at hw <;> simp only [Option.some.injEq, reduceCtorEq] at hw
  · -- the end of a competition
    subst hw
    have ha := hact _ h h1
    refine ⟨h1.trans ha, ha, Or.inr ⟨rfl, ?_, rfl⟩⟩
    have hvV := val_copy hp h1 ha
    have hvL : v.level = A.reg.level := h1.trans ha
    obtain ⟨ℓ, E⟩ : ∃ ℓ, Lead n ids A ℓ := by
      rcases hL with N | h
      · exact absurd h2 ((N.valsEl v hvV).2 h3)
      · exact h
    have hvℓ : v.id = some (ids ℓ) := by
      by_contra h
      exact (E.copyOther p v hp hvL ha h3 h).2.2.2 h2
    have hpℓ : p = ℓ := by
      by_contra h
      exact h5 (mem_of_card_eq_of_ne hid hn _ ℓ (fun a ha => ne_of_actLoser E (B.disc v hvV a ha))
        h2 p h)
    subst hpℓ
    have hphp : (A.loc p).ph = .committing := by
      rcases hph : (A.loc p).ph with _ | _
      · have := (E.el hph).copyL p v hp hvL ha hvℓ; rw [h4] at this; cases this
      · rfl
    exact (E.co hphp).ca (fun w' h' => by rw [hp] at h'; cases h')
  · subst hw; have ha := hact _ h h1; exact ⟨h1.trans ha, ha, Or.inl rfl⟩
  · subst hw; have ha := hact _ h h1; exact ⟨h1.trans ha, ha, Or.inl rfl⟩
  · subst hw; have ha := hact _ h h1; exact ⟨h1.trans ha, ha, Or.inl rfl⟩

end BezoutElection.Alg2
