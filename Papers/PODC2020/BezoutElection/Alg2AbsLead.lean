import Papers.PODC2020.BezoutElection.Alg2AbsFacts

/-!
# Algorithm 2, per-register abstraction: the leader of a competition stays the leader

Within a competition (the level of the register does not change), once `ℓ` is the leader it
stays the leader (`lead_step`). The leader is recognised by a *mark*: it is an active non-loser
that is committing, or an electing candidate with `n - 1` discarded identifiers.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace BezoutElection.Alg2

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

/-- The mark of the leader. -/
def Marked (n : ℕ) (A : AState Id P) (ℓ : P) : Prop :=
  (A.loc ℓ).lv = A.reg.level ∧ (A.loc ℓ).lo = false ∧
    ((A.loc ℓ).ph = .committing ∨ ((A.loc ℓ).ca = true ∧ (A.loc ℓ).D.card = n - 1))

lemma Lead.marked {A : AState Id P} {ℓ : P} (E : Lead n ids A ℓ) : Marked n A ℓ := by
  refine ⟨E.act.1, E.act.2, ?_⟩
  rcases hph : (A.loc ℓ).ph with _ | _
  · exact Or.inr ⟨(E.el hph).ca, (E.el hph).card⟩
  · exact Or.inl rfl

lemma marked_upd_self {A : AState Id P} {j : P} {l : ALoc Id} :
    Marked n (A.upd j l) j ↔ l.lv = A.reg.level ∧ l.lo = false ∧
      (l.ph = .committing ∨ (l.ca = true ∧ l.D.card = n - 1)) := by
  simp [Marked]

/-- A marked process is the leader. -/
lemma lead_of_marked {A : AState Id P} {ℓ : P} (hI : AInv n U ids A) (hM : Marked n A ℓ) :
    Lead n ids A ℓ := by
  obtain ⟨hact, hlo, hm⟩ := hM
  rcases hI.2 with N | ⟨ℓ', E⟩
  · exfalso
    rcases hm with h | ⟨h1, h2⟩
    · rw [N.phEl ℓ hact] at h; cases h
    · exact N.strict ℓ hact hlo h1 h2
  · have : ℓ' = ℓ := by
      by_contra hne
      have := (E.others ℓ (Ne.symm hne)).2; rw [hlo] at this; cases this
    subst this; exact E

/-- The mark survives the steps of a competition. -/
lemma marked_step (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {A A' : AState Id P} {ℓ : P} (hI : AInv n U ids A) (hM : Marked n A ℓ)
    (h : AStep n U ids A A') (hlev : A'.reg.level = A.reg.level) : Marked n A' ℓ := by
  have E := lead_of_marked hI hM
  obtain ⟨hact, hlo, hm⟩ := hM
  cases h with
  | read j hj =>
    change Marked n (A.setSt j (.copy A.reg)) ℓ
    exact ⟨by simpa using hact, by simpa using hlo, by simpa using hm⟩
  | write j w hj =>
    change (A.wr j w).reg.level = A.reg.level at hlev
    change Marked n (A.wr j w) ℓ
    simp only [AState.wr_reg] at hlev
    exact ⟨by simp only [wr_lv, wr_reg]; omega, by simpa using hlo, by simpa using hm⟩
  | proc j v ok fin hj =>
    change Marked n (A.upd j (procL n U (ids j) (A.loc j) v ok fin)) ℓ
    by_cases hjℓ : j ≠ ℓ
    · simp only [Marked, upd_loc_ne _ _ (Ne.symm hjℓ), upd_reg]; exact ⟨hact, hlo, hm⟩
    push Not at hjℓ
    subst hjℓ
    have hv := (hI.1.copyLv j v hj)
    rcases procX_cases n U (ids j) (A.loc j) v ok fin with
      ⟨h1, h2, e⟩ | e | ⟨h1, h1', h2, h3, e⟩ | ⟨h1, h1', h2, h3, h4, h5, e⟩ |
      ⟨h1, h1', h2, h3, h4, e⟩ | ⟨h1, h1', h2, h3, h4, e⟩ | ⟨h1, h1', h2, h3, h4, h5, h6, e⟩ <;>
      refine marked_upd_self.2 ?_ <;> simp only [procL, e, stOf]
    · exfalso; omega
    · exact ⟨hact, hlo, hm⟩
    · exact ⟨hact, hlo, Or.inl trivial⟩
    · refine ⟨hact, hlo, Or.inl ?_⟩
      rcases hph : (A.loc j).ph with _ | _
      · exfalso
        have h' : procX n U (ids j) (A.loc j) v ok fin =
            ({ A.loc j with ph := .committing, D := ∅ }, none) := by
          unfold procX; rw [if_pos ⟨h1, h1'⟩, if_pos ⟨h4, hph⟩]
        rw [e] at h'; simp at h'
      · rfl
    · exact ⟨hact, hlo, hm⟩
    · -- line 14: the discarded set can only grow, and has at most `n - 1` elements
      refine ⟨hact, hlo, ?_⟩
      rcases hm with hm | ⟨-, hm⟩
      · exact Or.inl hm
      · right
        refine ⟨trivial, ?_⟩
        show (if v.phase = (A.loc j).ph then (A.loc j).D ∪ v.disc else (A.loc j).D).card = n - 1
        have hvL : v.level = A.reg.level := h1.trans hact
        have hvV : A.Val v := Or.inr (Or.inr ⟨j, hj, hvL, hact⟩)
        have hsub : ∀ a ∈ (if v.phase = (A.loc j).ph then (A.loc j).D ∪ v.disc else (A.loc j).D),
            ∃ i, ids i = a ∧ i ≠ j := by
          intro a ha
          have hAL : A.ActLoser ids a := by
            split_ifs at ha
            · rcases Finset.mem_union.1 ha with h | h
              · exact hI.1.discLoc j hact a h
              · exact hI.1.disc v hvV a h
            · exact hI.1.discLoc j hact a ha
          exact ne_of_actLoser E hAL
        have hle := card_le_of_ne hn _ j hsub
        have hge : (A.loc j).D.card ≤
            (if v.phase = (A.loc j).ph then (A.loc j).D ∪ v.disc else (A.loc j).D).card := by
          split_ifs
          · exact Finset.card_le_card Finset.subset_union_left
          · exact le_rfl
        omega
    · exfalso
      by_cases hvℓ : v.id = some (ids j)
      · exact h5 hvℓ
      · have hvL : v.level = A.reg.level := h1.trans hact
        exact (E.copyOther j v hj hvL hact h4 hvℓ).1 rfl

/-- **The leader stays the leader** as long as the competition is not over. -/
theorem lead_step (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {A A' : AState Id P} {ℓ : P} (hI : AInv n U ids A) (E : Lead n ids A ℓ)
    (h : AStep n U ids A A') (hlev : A'.reg.level = A.reg.level) : Lead n ids A' ℓ :=
  lead_of_marked (ainv_step hid hn hI h) (marked_step hid hn hI E.marked h hlev)

end BezoutElection.Alg2
