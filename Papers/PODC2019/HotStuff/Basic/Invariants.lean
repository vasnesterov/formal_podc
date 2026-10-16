import Papers.PODC2019.HotStuff.Basic.Defs

/-!
# Basic HotStuff: quorum counting and basic invariants

Local invariants of correct replicas (votes are cast in the current view, at most once per phase
and view, the lock and `prepareQC` are valid and monotone, ...), and the consequences used by the
safety and liveness proofs: every valid QC is backed by a valid `prepareQC` of the same view and
node, and **two valid QCs of the same view are on the same node** (a strengthening of Lemma 1).
-/

namespace HotStuff.Basic

open Classical

variable {P C : Type*} [Fintype P] [DecidableEq P] {f : ℕ} {F : Finset P}

/-! ### Signers and validity -/

theorem mem_signers {V : Set (P × QC C)} {q : QC C} {i : P} :
    i ∈ signers F V q ↔ i ∈ F ∨ (i, q) ∈ V := by
  simp [signers]

theorem signers_mono {V V' : Set (P × QC C)} (h : V ⊆ V') (q : QC C) :
    signers F V q ⊆ signers F V' q := by
  intro i hi
  rw [mem_signers] at hi ⊢
  exact hi.imp_right (fun h' => h h')

theorem Valid.mono {V V' : Set (P × QC C)} (h : V ⊆ V') {q : QC C} (hq : Valid f F V q) :
    Valid f F V' q :=
  hq.imp_right fun h' => h'.trans (Finset.card_le_card (signers_mono h q))

/-- Signers of `q` are Byzantine or correct voters. -/
theorem card_signers_le {V : Set (P × QC C)} (q : QC C) :
    (signers F V q).card ≤ F.card + (Finset.univ.filter fun i => i ∉ F ∧ (i, q) ∈ V).card := by
  calc (signers F V q).card ≤ (F ∪ Finset.univ.filter fun i => i ∉ F ∧ (i, q) ∈ V).card := by
        apply Finset.card_le_card
        intro i hi
        rw [mem_signers] at hi
        by_cases hiF : i ∈ F
        · exact Finset.mem_union_left _ hiF
        · exact Finset.mem_union_right _ (by simp [hiF, hi.resolve_left hiF])
    _ ≤ _ := Finset.card_union_le _ _

/-- A quorum of size `n − f` with `2f < n` contains a correct voter. -/
theorem exists_correct_of_quorum (hF : F.card ≤ f) (h2 : 2 * f < Fintype.card P)
    {V : Set (P × QC C)} {q : QC C} (hq : Fintype.card P - f ≤ (signers F V q).card) :
    ∃ r ∉ F, (r, q) ∈ V := by
  by_contra hne
  push Not at hne
  have : (signers F V q) ⊆ F := by
    intro i hi
    rw [mem_signers] at hi
    rcases hi with hi | hi
    · exact hi
    · by_contra hiF; exact hne i hiF hi
  have := Finset.card_le_card this
  omega

/-- Two quorums of size `n − f` with `3f < n` intersect in a correct replica. -/
theorem quorum_inter (hF : F.card ≤ f) (h3 : 3 * f < Fintype.card P) {S₁ S₂ : Finset P}
    (h₁ : Fintype.card P - f ≤ S₁.card) (h₂ : Fintype.card P - f ≤ S₂.card) :
    ∃ r ∉ F, r ∈ S₁ ∧ r ∈ S₂ := by
  have hu := Finset.card_union_add_card_inter S₁ S₂
  have hun : (S₁ ∪ S₂).card ≤ Fintype.card P := Finset.card_le_univ _
  have hsd := Finset.le_card_sdiff F (S₁ ∩ S₂)
  obtain ⟨r, hr⟩ : ((S₁ ∩ S₂) \ F).Nonempty := by
    rw [← Finset.card_pos]; omega
  simp only [Finset.mem_sdiff, Finset.mem_inter] at hr
  exact ⟨r, hr.2, hr.1.1, hr.1.2⟩

theorem quorum_inter_signers (hF : F.card ≤ f) (h3 : 3 * f < Fintype.card P)
    {V : Set (P × QC C)} {q₁ q₂ : QC C}
    (h₁ : Fintype.card P - f ≤ (signers F V q₁).card)
    (h₂ : Fintype.card P - f ≤ (signers F V q₂).card) :
    ∃ r ∉ F, (r, q₁) ∈ V ∧ (r, q₂) ∈ V := by
  obtain ⟨r, hr, h₁', h₂'⟩ := quorum_inter hF h3 h₁ h₂
  rw [mem_signers] at h₁' h₂'
  exact ⟨r, hr, h₁'.resolve_left hr, h₂'.resolve_left hr⟩

/-! ### Local invariant of a correct replica -/

/-- The local invariant of a correct replica with local state `l` and own votes `mine`, given the
global votes `V`. -/
structure LocInv (f : ℕ) (F : Finset P) (V : Set (P × QC C)) (l : Loc C) (mine : QC C → Prop) :
    Prop where
  view_pos : 1 ≤ l.view
  vote : ∀ q, mine q → 1 ≤ q.view ∧ q.view ≤ l.view ∧ (q.view = l.view → q.ty.rank < l.phase)
  uniq : ∀ q₁ q₂, mine q₁ → mine q₂ → q₁.ty = q₂.ty → q₁.view = q₂.view → q₁ = q₂
  just : ∀ q, mine q → (q.ty = .precommit → Valid f F V ⟨.prepare, q.view, q.node⟩) ∧
    (q.ty = .commit → Valid f F V ⟨.precommit, q.view, q.node⟩)
  lock_valid : Valid f F V l.lock ∧ (l.lock.IsGen ∨ l.lock.ty = .precommit)
  lock_view : l.lock.view ≤ l.view ∧ (l.lock.view = l.view → 3 ≤ l.phase)
  lock_ge : ∀ q, mine q → q.ty = .commit → q.view ≤ l.lock.view
  prep_valid : Valid f F V l.prepQC ∧ (l.prepQC.IsGen ∨ l.prepQC.ty = .prepare)
  prep_view : l.prepQC.view ≤ l.view ∧ (l.prepQC.view = l.view → 2 ≤ l.phase)
  prep_ge : ∀ q, mine q → q.ty = .precommit → q.view ≤ l.prepQC.view
  committed : ∀ x ∈ l.committed, ∃ v, Valid f F V ⟨.commit, v, x⟩

theorem LocInv.mono {V V' : Set (P × QC C)} (h : V ⊆ V') {l : Loc C} {mine : QC C → Prop}
    (hI : LocInv f F V l mine) : LocInv f F V' l mine where
  view_pos := hI.view_pos
  vote := hI.vote
  uniq := hI.uniq
  just q hq := ⟨fun h' => ((hI.just q hq).1 h').mono h, fun h' => ((hI.just q hq).2 h').mono h⟩
  lock_valid := ⟨hI.lock_valid.1.mono h, hI.lock_valid.2⟩
  lock_view := hI.lock_view
  lock_ge := hI.lock_ge
  prep_valid := ⟨hI.prep_valid.1.mono h, hI.prep_valid.2⟩
  prep_view := hI.prep_view
  prep_ge := hI.prep_ge
  committed x hx := let ⟨v, hv⟩ := hI.committed x hx; ⟨v, hv.mono h⟩

theorem LocInv.init (V : Set (P × QC C)) : LocInv f F V Loc.init (fun _ => False) where
  view_pos := le_rfl
  vote := by simp
  uniq := by simp
  just := by simp
  lock_valid := ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  lock_view := by simp [Loc.init, QC.genesis]
  lock_ge := by simp
  prep_valid := ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  prep_view := by simp [Loc.init, QC.genesis]
  prep_ge := by simp
  committed := by simp [Loc.init]

/-- A local step preserves the local invariant (the new vote `o` is added to `mine`, and the
global votes grow from `V` to `V'`, which contains the new vote). -/
theorem LocInv.step {V V' : Set (P × QC C)} (hV : V ⊆ V') {l l' : Loc C} {o : Option (QC C)}
    {mine : QC C → Prop} (hI : LocInv f F V l mine) (hs : LStep f F V l l' o) :
    LocInv f F V' l' (fun q => mine q ∨ o = some q) := by
  have hI' := hI.mono hV
  cases hs with
  | prepVote x j h0 hj hx hsafe =>
    refine ⟨hI.view_pos, ?_, ?_, ?_, hI'.lock_valid, ?_, ?_, hI'.prep_valid, ?_, ?_,
      hI'.committed⟩
    · rintro q (hq | ⟨⟨⟩⟩)
      · have := hI.vote q hq
        exact ⟨this.1, this.2.1, fun h => by have := this.2.2 h; simp; omega⟩
      · exact ⟨hI.view_pos, le_rfl, fun _ => by simp [Phase.rank]⟩
    · rintro q₁ q₂ (h₁ | ⟨⟨⟩⟩) (h₂ | ⟨⟨⟩⟩) ht hv
      · exact hI.uniq q₁ q₂ h₁ h₂ ht hv
      · have := (hI.vote q₁ h₁).2.2 hv; rw [ht] at this; simp [Phase.rank] at this; omega
      · have := (hI.vote q₂ h₂).2.2 hv.symm; rw [← ht] at this; simp [Phase.rank] at this; omega
      · rfl
    · rintro q (hq | ⟨⟨⟩⟩)
      · exact hI'.just q hq
      · simp
    · exact ⟨hI.lock_view.1, fun h => by have := hI.lock_view.2 h; simp at this ⊢ <;> omega⟩
    · rintro q (hq | ⟨⟨⟩⟩) ht
      · exact hI.lock_ge q hq ht
      · cases ht
    · exact ⟨hI.prep_view.1, fun h => by have := hI.prep_view.2 h; simp at this ⊢ <;> omega⟩
    · rintro q (hq | ⟨⟨⟩⟩) ht
      · exact hI.prep_ge q hq ht
      · cases ht
  | prepSkip h0 =>
    refine ⟨hI.view_pos, ?_, ?_, ?_, hI'.lock_valid, ?_, ?_, hI'.prep_valid, ?_, ?_,
      hI'.committed⟩
    · rintro q (hq | ⟨⟨⟩⟩)
      have := hI.vote q hq
      exact ⟨this.1, this.2.1, fun h => by have := this.2.2 h; simp; omega⟩
    · rintro q₁ q₂ (h₁ | ⟨⟨⟩⟩) (h₂ | ⟨⟨⟩⟩) ht hv
      exact hI.uniq q₁ q₂ h₁ h₂ ht hv
    · rintro q (hq | ⟨⟨⟩⟩); exact hI'.just q hq
    · exact ⟨hI.lock_view.1, fun h => by have := hI.lock_view.2 h; simp at this ⊢ <;> omega⟩
    · rintro q (hq | ⟨⟨⟩⟩) ht; exact hI.lock_ge q hq ht
    · exact ⟨hI.prep_view.1, fun h => by have := hI.prep_view.2 h; simp at this ⊢ <;> omega⟩
    · rintro q (hq | ⟨⟨⟩⟩) ht; exact hI.prep_ge q hq ht
  | precommitVote q h1 hq hty hv =>
    refine ⟨hI.view_pos, ?_, ?_, ?_, hI'.lock_valid, ?_, ?_, ⟨hq.mono hV, Or.inr hty⟩, ?_, ?_,
      hI'.committed⟩
    · rintro q' (hq' | ⟨⟨⟩⟩)
      · have := hI.vote q' hq'
        exact ⟨this.1, this.2.1, fun h => by have := this.2.2 h; simp; omega⟩
      · exact ⟨hI.view_pos, le_rfl, fun _ => by simp [Phase.rank]⟩
    · rintro q₁ q₂ (h₁ | ⟨⟨⟩⟩) (h₂ | ⟨⟨⟩⟩) ht hv
      · exact hI.uniq q₁ q₂ h₁ h₂ ht hv
      · have := (hI.vote q₁ h₁).2.2 hv; rw [ht] at this; simp [Phase.rank] at this; omega
      · have := (hI.vote q₂ h₂).2.2 hv.symm; rw [← ht] at this; simp [Phase.rank] at this; omega
      · rfl
    · rintro q' (hq' | ⟨⟨⟩⟩)
      · exact hI'.just q' hq'
      · refine ⟨fun _ => ?_, fun h => by cases h⟩
        have : q = ⟨.prepare, l.view, q.node⟩ := by cases q; simp_all
        rw [← this]; exact hq.mono hV
    · exact ⟨hI.lock_view.1, fun h => by have := hI.lock_view.2 h; simp at this ⊢ <;> omega⟩
    · rintro q' (hq' | ⟨⟨⟩⟩) ht
      · exact hI.lock_ge q' hq' ht
      · cases ht
    · exact ⟨by simp [hv], fun _ => by simp⟩
    · rintro q' (hq' | ⟨⟨⟩⟩) ht
      · have := (hI.vote q' hq').2.1; simp [hv]; omega
      · simp [hv]
  | commitVote q h2 hq hty hv =>
    refine ⟨hI.view_pos, ?_, ?_, ?_, ⟨hq.mono hV, Or.inr hty⟩, ?_, ?_, hI'.prep_valid, ?_, ?_,
      hI'.committed⟩
    · rintro q' (hq' | ⟨⟨⟩⟩)
      · have := hI.vote q' hq'
        exact ⟨this.1, this.2.1, fun h => by have := this.2.2 h; simp; omega⟩
      · exact ⟨hI.view_pos, le_rfl, fun _ => by simp [Phase.rank]⟩
    · rintro q₁ q₂ (h₁ | ⟨⟨⟩⟩) (h₂ | ⟨⟨⟩⟩) ht hv
      · exact hI.uniq q₁ q₂ h₁ h₂ ht hv
      · have := (hI.vote q₁ h₁).2.2 hv; rw [ht] at this; simp [Phase.rank] at this; omega
      · have := (hI.vote q₂ h₂).2.2 hv.symm; rw [← ht] at this; simp [Phase.rank] at this; omega
      · rfl
    · rintro q' (hq' | ⟨⟨⟩⟩)
      · exact hI'.just q' hq'
      · refine ⟨fun h => (by cases h), fun _ => ?_⟩
        have : q = ⟨.precommit, l.view, q.node⟩ := by cases q; simp_all
        rw [← this]; exact hq.mono hV
    · exact ⟨by simp [hv], fun _ => by simp⟩
    · rintro q' (hq' | ⟨⟨⟩⟩) ht
      · have := (hI.vote q' hq').2.1; simp [hv]; omega
      · simp [hv]
    · exact ⟨hI.prep_view.1, fun h => by have := hI.prep_view.2 h; simp at this ⊢ <;> omega⟩
    · rintro q' (hq' | ⟨⟨⟩⟩) ht
      · exact hI.prep_ge q' hq' ht
      · cases ht
  | decide q h3 hq hty hv =>
    refine ⟨hI.view_pos, ?_, ?_, ?_, hI'.lock_valid, ?_, ?_, hI'.prep_valid, ?_, ?_, ?_⟩
    · rintro q' (hq' | ⟨⟨⟩⟩)
      have := hI.vote q' hq'
      exact ⟨this.1, this.2.1, fun h => by have := this.2.2 h; simp; omega⟩
    · rintro q₁ q₂ (h₁ | ⟨⟨⟩⟩) (h₂ | ⟨⟨⟩⟩) ht hv
      exact hI.uniq q₁ q₂ h₁ h₂ ht hv
    · rintro q' (hq' | ⟨⟨⟩⟩); exact hI'.just q' hq'
    · exact ⟨hI.lock_view.1, fun h => by have := hI.lock_view.2 h; simp at this ⊢ <;> omega⟩
    · rintro q' (hq' | ⟨⟨⟩⟩) ht; exact hI.lock_ge q' hq' ht
    · exact ⟨hI.prep_view.1, fun h => by have := hI.prep_view.2 h; simp at this ⊢ <;> omega⟩
    · rintro q' (hq' | ⟨⟨⟩⟩) ht; exact hI.prep_ge q' hq' ht
    · intro x hx
      rcases (Set.mem_insert_iff.mp hx) with rfl | hx
      · refine ⟨q.view, ?_⟩
        have : q = ⟨.commit, q.view, q.node⟩ := by cases q; simp_all
        rw [← this]; exact hq.mono hV
      · exact hI'.committed x hx
  | newView v hlt =>
    refine ⟨by simp; have := hI.view_pos; omega, ?_, ?_, ?_, hI'.lock_valid, ?_, ?_,
      hI'.prep_valid, ?_, ?_, hI'.committed⟩
    · rintro q' (hq' | ⟨⟨⟩⟩)
      have := hI.vote q' hq'
      exact ⟨this.1, by simp; omega, fun h => by simp at h; omega⟩
    · rintro q₁ q₂ (h₁ | ⟨⟨⟩⟩) (h₂ | ⟨⟨⟩⟩) ht hv
      exact hI.uniq q₁ q₂ h₁ h₂ ht hv
    · rintro q (hq | ⟨⟨⟩⟩); exact hI'.just q hq
    · exact ⟨by simp; have := hI.lock_view.1; omega, fun h => by
        simp at h; have := hI.lock_view.1; omega⟩
    · rintro q' (hq' | ⟨⟨⟩⟩) ht; exact hI.lock_ge q' hq' ht
    · exact ⟨by simp; have := hI.prep_view.1; omega, fun h => by
        simp at h; have := hI.prep_view.1; omega⟩
    · rintro q' (hq' | ⟨⟨⟩⟩) ht; exact hI.prep_ge q' hq' ht

/-! ### The global invariant -/

/-- The global invariant: only correct replicas appear in `votes`, and every correct replica
satisfies the local invariant. -/
structure Inv (f : ℕ) (F : Finset P) (s : St P C) : Prop where
  correct : ∀ r q, (r, q) ∈ s.votes → r ∉ F
  loc : ∀ r ∉ F, LocInv f F s.votes (s.loc r) (fun q => (r, q) ∈ s.votes)

theorem mem_newVotes {r r' : P} {o : Option (QC C)} {q : QC C} :
    (r', q) ∈ newVotes r o ↔ r' = r ∧ o = some q := by
  simp [newVotes, and_comm, eq_comm]

theorem Inv.init : Inv f F (St.init : St P C) where
  correct := by simp [St.init]
  loc r _ := by simpa [St.init] using LocInv.init (f := f) (F := F) (C := C) ∅

theorem Inv.step {s s' : St P C} (hI : Inv f F s) (hs : Step f F s s') : Inv f F s' := by
  cases hs with
  | mk r l' o hr hl =>
    have hV : s.votes ⊆ s.votes ∪ newVotes r o := Set.subset_union_left
    refine ⟨?_, ?_⟩
    · rintro r' q (hq | hq)
      · exact hI.correct r' q hq
      · rw [mem_newVotes] at hq; exact hq.1 ▸ hr
    · intro r' hr'
      by_cases h : r' = r
      · subst h
        have := (hI.loc r' hr').step hV hl
        simp only [Function.update_self]
        convert this using 2 with q
        simp [mem_newVotes]
      · simp only [Function.update_of_ne h]
        convert (hI.loc r' hr').mono hV using 2 with q
        simp [mem_newVotes, h]

theorem Reach.inv {s : St P C} (h : Reach f F s) : Inv f F s := by
  induction h with
  | refl => exact Inv.init
  | tail _ hs ih => exact ih.step hs

/-! ### Consequences -/

variable {s : St P C}

/-- A valid QC with view `0` is the genesis QC. -/
theorem Inv.node_of_view_zero (hI : Inv f F s) (hF : F.card ≤ f) (h2 : 2 * f < Fintype.card P)
    {q : QC C} (hq : Valid f F s.votes q) (h0 : q.view = 0) : q.node = [] := by
  rcases hq with hq | hq
  · exact hq.2
  · obtain ⟨r, hr, hv⟩ := exists_correct_of_quorum hF h2 hq
    have := ((hI.loc r hr).vote q hv).1
    omega

/-- Every valid QC is backed by a valid `prepareQC` with the same view and node. -/
theorem Inv.valid_prepare (hI : Inv f F s) (hF : F.card ≤ f) (h2 : 2 * f < Fintype.card P)
    {q : QC C} (hq : Valid f F s.votes q) : Valid f F s.votes ⟨.prepare, q.view, q.node⟩ := by
  rcases hq with hq | hq
  · exact Or.inl hq
  obtain ⟨r, hr, hv⟩ := exists_correct_of_quorum hF h2 hq
  obtain ⟨ty, v, x⟩ := q
  cases ty with
  | prepare => exact Or.inr hq
  | precommit => exact ((hI.loc r hr).just _ hv).1 rfl
  | commit =>
    have h' := ((hI.loc r hr).just _ hv).2 rfl
    rcases h' with h' | h'
    · exact Or.inl h'
    obtain ⟨r', hr', hv'⟩ := exists_correct_of_quorum hF h2 h'
    exact ((hI.loc r' hr').just _ hv').1 rfl

/-- **Lemma 1 (strengthened).** Two valid QCs of the same view (of any types) are on the same
node. The paper states: valid QCs of the same type on conflicting nodes have different views. -/
theorem Inv.node_eq (hI : Inv f F s) (hF : F.card ≤ f) (h3 : 3 * f < Fintype.card P)
    {q₁ q₂ : QC C} (h₁ : Valid f F s.votes q₁) (h₂ : Valid f F s.votes q₂)
    (hv : q₁.view = q₂.view) : q₁.node = q₂.node := by
  have h2 : 2 * f < Fintype.card P := by omega
  by_cases h0 : q₁.view = 0
  · rw [hI.node_of_view_zero hF h2 h₁ h0, hI.node_of_view_zero hF h2 h₂ (hv ▸ h0)]
  have p₁ := hI.valid_prepare hF h2 h₁
  have p₂ := hI.valid_prepare hF h2 h₂
  rcases p₁ with p₁ | p₁
  · exact absurd p₁.1 h0
  rcases p₂ with p₂ | p₂
  · exact absurd (hv ▸ p₂.1) h0
  obtain ⟨r, hr, v₁, v₂⟩ := quorum_inter_signers hF h3 p₁ p₂
  have := (hI.loc r hr).uniq _ _ v₁ v₂ rfl hv
  simp at this
  exact this.2

/-- **Lemma 1** of the paper. -/
theorem lemma_1 (hF : F.card ≤ f) (h3 : 3 * f < Fintype.card P) (hs : Reach f F s)
    {q₁ q₂ : QC C} (h₁ : Valid f F s.votes q₁) (h₂ : Valid f F s.votes q₂)
    (_ht : q₁.ty = q₂.ty) (hc : Conflict q₁.node q₂.node) : q₁.view ≠ q₂.view := by
  intro hv
  have := hs.inv.node_eq hF h3 h₁ h₂ hv
  exact hc.1 (this ▸ List.suffix_refl _)

end HotStuff.Basic
