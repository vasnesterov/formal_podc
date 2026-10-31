import Papers.PODC2012.GeneralizedLatticeAgreement.Model

/-!
# Basic facts: monotonicity of the state, joins, quorums
-/

namespace Podc.GeneralizedLatticeAgreement

variable {P A Ln L : Type}

/-- `x` is the join of a finite subset of `S` (Theorem 5.1's "can be expressed as the join of
some subset of ..."; the empty join is `⊥`). -/
def IsJoinOf [SemilatticeSup L] [OrderBot L] (S : Set L) (x : L) : Prop :=
  ∃ T : Finset L, ↑T ⊆ S ∧ x = T.sup id

namespace IsJoinOf

variable [SemilatticeSup L] [OrderBot L] {S S' : Set L} {x y : L}

lemma bot : IsJoinOf S (⊥ : L) := ⟨∅, by simp, by simp⟩

lemma of_mem [DecidableEq L] (h : x ∈ S) : IsJoinOf S x :=
  ⟨{x}, by simpa using h, by simp⟩

lemma sup [DecidableEq L] (hx : IsJoinOf S x) (hy : IsJoinOf S y) : IsJoinOf S (x ⊔ y) := by
  obtain ⟨T, hT, rfl⟩ := hx
  obtain ⟨U, hU, rfl⟩ := hy
  exact ⟨T ∪ U, by simp [hT, hU], by simp [Finset.sup_union]⟩

lemma mono (hS : S ⊆ S') (h : IsJoinOf S x) : IsJoinOf S' x := by
  obtain ⟨T, hT, rfl⟩ := h
  exact ⟨T, hT.trans hS, rfl⟩

/-- A join of elements of a finite set `I` is the join of all elements of `I` below it. -/
lemma eq_sup_filter [DecidableLE L] {I : Finset L} (h : IsJoinOf (↑I : Set L) x) :
    x = ({u ∈ I | u ≤ x} : Finset L).sup id := by
  obtain ⟨T, hT, rfl⟩ := h
  apply le_antisymm
  · refine Finset.sup_le fun u hu => ?_
    refine Finset.le_sup (f := id) ?_
    simp only [Finset.mem_filter]
    exact ⟨hT hu, Finset.le_sup (f := id) hu⟩
  · refine Finset.sup_le fun u hu => ?_
    simp only [Finset.mem_filter] at hu
    exact hu.2

end IsJoinOf

/-- Two quorums intersect. -/
lemma quorum_inter [Fintype A] [DecidableEq A] {S T : Finset A} (hS : quorum A ≤ S.card)
    (hT : quorum A ≤ T.card) : (S ∩ T).Nonempty := by
  apply Finset.inter_nonempty_of_card_lt_card_add_card (Finset.subset_univ _)
    (Finset.subset_univ _)
  rw [Finset.card_univ]
  unfold quorum at hS hT
  omega

section

variable [SemilatticeSup L] [OrderBot L] [DecidableEq P] [DecidableEq A] [DecidableEq Ln]
  [DecidableEq L] [DecidableLE L] [Fintype P] [Fintype A]

@[simp] lemma State.updP_prop (s : State P A Ln L) (p : P) (f) (q : P) :
    (s.updP p f).prop q = if q = p then f (s.prop p) else s.prop q := by
  simp [State.updP, Function.update_apply]

@[simp] lemma State.updP_sent (s : State P A Ln L) (p : P) (f) : (s.updP p f).sent = s.sent := rfl
@[simp] lemma State.updP_acc (s : State P A Ln L) (p : P) (f) : (s.updP p f).acc = s.acc := rfl
@[simp] lemma State.updP_adone (s : State P A Ln L) (p : P) (f) :
    (s.updP p f).adone = s.adone := rfl
@[simp] lemma State.updP_learnt (s : State P A Ln L) (p : P) (f) :
    (s.updP p f).learnt = s.learnt := rfl
@[simp] lemma State.updP_lacks (s : State P A Ln L) (p : P) (f) :
    (s.updP p f).lacks = s.lacks := rfl
@[simp] lemma State.updP_received (s : State P A Ln L) (p : P) (f) :
    (s.updP p f).received = s.received := rfl
@[simp] lemma State.updP_initiated (s : State P A Ln L) (p : P) (f) :
    (s.updP p f).initiated = s.initiated := rfl
@[simp] lemma State.updP_decisions (s : State P A Ln L) (p : P) (f) :
    (s.updP p f).decisions = s.decisions := rfl

variable (s : State P A Ln L) (act : Action P A Ln L)

lemma sent_subset_apply : s.sent ⊆ (apply s act).sent := by
  cases act <;> simp [apply, Finset.subset_insert]

lemma received_subset_apply : s.received ⊆ (apply s act).received := by
  cases act <;> simp [apply, Finset.subset_insert]

lemma initiated_subset_apply : s.initiated ⊆ (apply s act).initiated := by
  cases act <;> simp [apply, Finset.subset_insert]

lemma decisions_subset_apply : s.decisions ⊆ (apply s act).decisions := by
  cases act <;> simp [apply, Finset.subset_insert]

lemma apn_le_apply (p : P) : (s.prop p).apn ≤ ((apply s act).prop p).apn := by
  cases act <;> simp only [apply, State.updP_prop] <;> (try split_ifs) <;> simp_all

lemma proposed_le_apply (p : P) : (s.prop p).proposed ≤ ((apply s act).prop p).proposed := by
  cases act <;> simp only [apply, State.updP_prop] <;> (try split_ifs) <;> simp_all

lemma acc_le_apply (he : Enabled s act) (a : A) : s.acc a ≤ (apply s act).acc a := by
  cases act with
  | accept a' p n v =>
    simp only [apply]
    by_cases h : a = a'
    · subst h; simpa using he.2.2
    · simp [Function.update_of_ne h]
  | reject a' p n v =>
    simp only [apply]
    by_cases h : a = a' <;> simp_all [Function.update_apply]
  | _ => simp [apply]

end

end Podc.GeneralizedLatticeAgreement
