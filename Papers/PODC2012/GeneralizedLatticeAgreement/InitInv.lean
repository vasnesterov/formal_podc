import Papers.PODC2012.GeneralizedLatticeAgreement.InvStep
import Papers.PODC2012.GeneralizedLatticeAgreement.Safety

/-!
# Every value in the system is a join of initiated values

Used by Lemma 5.11 ("each proposed value can be expressed as the join of some subset of values
in `All`", which the paper says "follows similar to Theorem 5.1").
-/

namespace Podc.GeneralizedLatticeAgreement

variable {P A Ln L : Type}

/-- Is `m` a proposal made by a `Propose` step (according to the ghost set `I`)? -/
def Msg.isInit [DecidableEq P] (I : Finset (P × ℕ)) : Msg P A L → Bool
  | .proposal p n _ => decide ((p, n) ∈ I)
  | _ => false

variable [SemilatticeSup L] [OrderBot L] [DecidableEq P] [DecidableEq A] [DecidableEq Ln]
  [DecidableEq L] [DecidableLE L] [Fintype P] [Fintype A]

/-- The initiated values (values proposed by `Propose` steps). -/
def initVals (s : State P A Ln L) : Finset L :=
  (s.sent.filter fun m => m.isInit s.initiated).image Msg.val

lemma mem_initVals {s : State P A Ln L} {v : L} :
    v ∈ initVals s ↔ ∃ p n, (p, n) ∈ s.initiated ∧ Msg.proposal p n v ∈ s.sent := by
  simp only [initVals, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨m, ⟨hm, hi⟩, rfl⟩
    cases m <;> simp only [Msg.isInit, Msg.val, decide_eq_true_eq, Bool.false_eq_true] at hi ⊢
    exact ⟨_, _, hi, hm⟩
  · rintro ⟨p, n, hi, hm⟩
    exact ⟨_, ⟨hm, by simpa [Msg.isInit] using hi⟩, rfl⟩

lemma initVals_mono {s s' : State P A Ln L} (h1 : s.sent ⊆ s'.sent)
    (h2 : s.initiated ⊆ s'.initiated) : initVals s ⊆ initVals s' := by
  intro v hv
  obtain ⟨p, n, hi, hm⟩ := mem_initVals.1 hv
  exact mem_initVals.2 ⟨p, n, h2 hi, h1 hm⟩

/-- The invariant. -/
structure InitInv (s : State P A Ln L) : Prop where
  prop : ∀ {p n v}, Msg.proposal p n v ∈ s.sent → IsJoinOf (↑(initVals s) : Set L) v ∧ ⊥ < v
  nack : ∀ {a p n ρ}, Msg.nack a p n ρ ∈ s.sent → IsJoinOf (↑(initVals s) : Set L) ρ
  acc : ∀ a, IsJoinOf (↑(initVals s) : Set L) (s.acc a)
  proposed : ∀ p, IsJoinOf (↑(initVals s) : Set L) (s.prop p).proposed

lemma initInv_init (b : P → L) : InitInv (initState (A := A) (Ln := Ln) b) where
  prop h := by simp [initState] at h
  nack h := by simp [initState] at h
  acc _ := IsJoinOf.bot
  proposed _ := IsJoinOf.bot

lemma InitInv.step {s : State P A Ln L} (hi : InitInv s) (h : Inv s) {act : Action P A Ln L}
    (he : Enabled s act) : InitInv (apply s act) := by
  have hI0 : (↑(initVals s) : Set L) ⊆ ↑(initVals (apply s act)) := by
    exact_mod_cast initVals_mono (sent_subset_apply s act) (initiated_subset_apply s act)
  obtain ⟨I, hId⟩ : ∃ I, I = (↑(initVals (apply s act)) : Set L) := ⟨_, rfl⟩
  have hI : (↑(initVals s) : Set L) ⊆ I := hId ▸ hI0
  have hpr : ∀ {p n v}, Msg.proposal p n v ∈ s.sent → IsJoinOf I v ∧ ⊥ < v :=
    fun hm => ⟨(hi.prop hm).1.mono hI, (hi.prop hm).2⟩
  have hnk : ∀ {a p n ρ}, Msg.nack a p n ρ ∈ s.sent → IsJoinOf I ρ :=
    fun hm => (hi.nack hm).mono hI
  have hac : ∀ a, IsJoinOf I (s.acc a) := fun a => (hi.acc a).mono hI
  have hpp : ∀ p, IsJoinOf I (s.prop p).proposed := fun p => (hi.proposed p).mono hI
  suffices H : (∀ {p n v}, Msg.proposal p n v ∈ (apply s act).sent → IsJoinOf I v ∧ ⊥ < v) ∧
      (∀ {a p n ρ}, Msg.nack a p n ρ ∈ (apply s act).sent → IsJoinOf I ρ) ∧
      (∀ a, IsJoinOf I ((apply s act).acc a)) ∧
      (∀ p, IsJoinOf I ((apply s act).prop p).proposed) by
    subst hId; exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2⟩
  cases act with
  | receive q v =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p n v hm; simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm
      exact hpr hm
    · intro a p n ρ hm; simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm
      exact hnk hm
    · exact hac
    · intro p; simp only [apply, State.updP_prop]; split_ifs with hpq
      · subst p; exact hpp q
      · exact hpp p
  | buffer q q' v =>
    refine ⟨fun hm => hpr hm, fun hm => hnk hm, hac, ?_⟩
    intro p; simp only [apply, State.updP_prop]; split_ifs with hpq
    · subst p; exact hpp q
    · exact hpp p
  | propose q =>
    obtain ⟨-, hgt⟩ := he
    have hw : IsJoinOf I ((s.prop q).proposed ⊔ (s.prop q).buffered) := by
      refine IsJoinOf.of_mem ?_
      rw [hId]
      exact mem_initVals.2 ⟨q, (s.prop q).apn + 1, by simp [apply], by simp [apply]⟩
    have hpos : ⊥ < (s.prop q).proposed ⊔ (s.prop q).buffered :=
      lt_of_le_of_lt bot_le (lt_of_le_not_ge le_sup_left hgt)
    refine ⟨?_, ?_, hac, ?_⟩
    · intro p n v hm
      simp only [apply, Finset.mem_insert, Msg.proposal.injEq] at hm
      rcases hm with ⟨rfl, rfl, rfl⟩ | hm
      · exact ⟨hw, hpos⟩
      · exact hpr hm
    · intro a p n ρ hm; simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm
      exact hnk hm
    · intro p; simp only [apply, State.updP_prop]; split_ifs with hpq
      · exact hw
      · exact hpp p
  | processAck q a n v =>
    refine ⟨fun hm => hpr hm, fun hm => hnk hm, hac, ?_⟩
    intro p; simp only [apply, State.updP_prop]; split_ifs with hpq
    · subst p; exact hpp q
    · exact hpp p
  | processNack q a n v =>
    refine ⟨fun hm => hpr hm, fun hm => hnk hm, hac, ?_⟩
    intro p; simp only [apply, State.updP_prop]; split_ifs with hpq
    · subst p; exact (hpp q).sup (hnk he.1)
    · exact hpp p
  | refine q =>
    obtain ⟨hpos, -, -⟩ := he
    obtain ⟨a₀, ha₀⟩ := Finset.card_pos.1 hpos
    obtain ⟨ρ₀, hρ₀, hρ₀le⟩ := h.nacks_sent ha₀
    obtain ⟨v₀, hv₀, hv₀lt⟩ := h.nack_prop hρ₀
    have hpos' : ⊥ < (s.prop q).proposed :=
      lt_of_lt_of_le (hpr hv₀).2 (h.prop_le hv₀)
    refine ⟨?_, ?_, hac, ?_⟩
    · intro p n v hm
      simp only [apply, Finset.mem_insert, Msg.proposal.injEq] at hm
      rcases hm with ⟨rfl, rfl, rfl⟩ | hm
      · exact ⟨hpp p, hpos'⟩
      · exact hpr hm
    · intro a p n ρ hm; simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm
      exact hnk hm
    · intro p; simp only [apply, State.updP_prop]; split_ifs with hpq
      · subst p; exact hpp q
      · exact hpp p
  | decide q =>
    refine ⟨fun hm => hpr hm, fun hm => hnk hm, hac, ?_⟩
    intro p; simp only [apply, State.updP_prop]; split_ifs with hpq
    · subst p; exact hpp q
    · exact hpp p
  | accept a₀ q n v =>
    refine ⟨?_, ?_, ?_, hpp⟩
    · intro p n v hm; simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm
      exact hpr hm
    · intro a p n ρ hm; simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm
      exact hnk hm
    · intro a; simp only [apply, Function.update_apply]; split_ifs
      · exact (hpr he.1).1
      · exact hac a
  | reject a₀ q n v =>
    refine ⟨?_, ?_, ?_, hpp⟩
    · intro p n v hm; simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm
      exact hpr hm
    · intro a p n ρ hm
      simp only [apply, Finset.mem_insert, Msg.nack.injEq] at hm
      rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | hm
      · exact (hac a).sup (hpr he.1).1
      · exact hnk hm
    · intro a; simp only [apply, Function.update_apply]; split_ifs with ha
      · subst ha; exact (hac a).sup (hpr he.1).1
      · exact hac a
  | learn l a q n v =>
    exact ⟨fun hm => hpr hm, fun hm => hnk hm, hac, hpp⟩

lemma Reachable.initInv {b : P → L} {s : State P A Ln L} (h : Reachable b s) : InitInv s := by
  induction h with
  | init => exact initInv_init b
  | step act hr he ih => exact ih.step hr.inv he

end Podc.GeneralizedLatticeAgreement
