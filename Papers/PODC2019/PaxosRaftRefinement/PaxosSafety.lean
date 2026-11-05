import Papers.PODC2019.PaxosRaftRefinement.Paxos

/-!
# Safety of MultiPaxos (Figure 1 of [paper], repaired)

The paper takes the safety of MultiPaxos for granted ("we assume that all three protocols ... have
been proven correct", Section 4.1) and states it as `theorem Invariance` of its TLA+ spec (B.1).
We prove it for the model of `Paxos.lean`.

The proof is Lamport-style: votes are the `acceptOK` messages `m2b`; `SafeAt i b v` says that no
value other than `v` can have been or can still be chosen in instance `i` at a ballot below `b`;
the inductive invariant `Inv` says that every proposal is safe, that a ballot has at most one
proposal per instance and at most one leader, and relates logs and `prepareOK` reports to votes.
-/

namespace Podc.PaxosRaftRefinement.Paxos

variable {N V : Type*} [DecidableEq N] {Q : QuorumSystem N} {p p' : State N V}

/-! ### Auxiliary notions -/

/-- `v` is safe at instance `i` and ballot `b` (TLA+ `SafeAt`): for every lower ballot `c` some
quorum either voted `v` at `c` or has moved past `c` without voting there. -/
def SafeAt (Q : QuorumSystem N) (p : State N V) (i b : ℕ) (v : V) : Prop :=
  ∀ c < b, ∃ A, Q.IsQuorum A ∧ ∀ a ∈ A,
    (a, i, c, v) ∈ p.m2b ∨ (c < p.ballot a ∧ ∀ w, (a, i, c, w) ∉ p.m2b)

/-- Server `r` collected `prepareOK`s for ballot `b` from a quorum. -/
def HasQuorum (Q : QuorumSystem N) (p : State N V) (r : N) (b : ℕ) : Prop :=
  ∃ A, Q.IsQuorum A ∧ ∀ a ∈ A, ∃ L, (⟨a, r, b, L⟩ : Msg1b N V) ∈ p.m1b

omit [DecidableEq N] in
theorem QuorumSystem.nonempty {A : Finset N} (hA : Q.IsQuorum A) : ∃ a, a ∈ A := by
  obtain ⟨a, ha, -⟩ := Q.inter A A hA hA
  exact ⟨a, ha⟩

omit [DecidableEq N] in
theorem SafeAt.mono {i b : ℕ} {v : V} (h : SafeAt Q p i b v) (hm : p.m2b ⊆ p'.m2b)
    (hb : ∀ a, p.ballot a ≤ p'.ballot a)
    (hnew : ∀ a i c w, (a, i, c, w) ∈ p'.m2b → (a, i, c, w) ∉ p.m2b → p.ballot a ≤ c) :
    SafeAt Q p' i b v := by
  intro c hc
  obtain ⟨A, hA, hA'⟩ := h c hc
  refine ⟨A, hA, fun a ha => ?_⟩
  rcases hA' a ha with h1 | ⟨h1, h2⟩
  · exact Or.inl (hm h1)
  · refine Or.inr ⟨lt_of_lt_of_le h1 (hb a), fun w hw => ?_⟩
    by_cases hw' : (a, i, c, w) ∈ p.m2b
    · exact h2 w hw'
    · exact absurd (hnew a i c w hw hw') (not_le.2 h1)

omit [DecidableEq N] in
theorem HasQuorum.mono {r : N} {b : ℕ} (h : HasQuorum Q p r b) (hm : p.m1b ⊆ p'.m1b) :
    HasQuorum Q p' r b := by
  obtain ⟨A, hA, hA'⟩ := h
  exact ⟨A, hA, fun a ha => (hA' a ha).imp fun _ hL => hm hL⟩

omit [DecidableEq N] in
theorem ChosenAt.mono {i b : ℕ} {v : V} (h : ChosenAt Q p i b v) (hm : p.m2b ⊆ p'.m2b) :
    ChosenAt Q p' i b v := by
  obtain ⟨A, hA, hA'⟩ := h
  exact ⟨A, hA, fun a ha => hm (hA' a ha)⟩

/-! ### Frame properties of a step -/

theorem Step.m2b_sub (hs : Step Q p p') : p.m2b ⊆ p'.m2b := by
  cases hs <;> first | exact subset_rfl | exact Set.subset_insert _ _

theorem Step.m1b_sub (hs : Step Q p p') : p.m1b ⊆ p'.m1b := by
  cases hs <;> first | exact subset_rfl | exact Set.subset_insert _ _

theorem Step.m2a_sub (hs : Step Q p p') : p.m2a ⊆ p'.m2a := by
  cases hs <;> first | exact subset_rfl | exact Set.subset_insert _ _

theorem Step.ballot_le (hs : Step Q p p') (a : N) : p.ballot a ≤ p'.ballot a := by
  cases hs with
  | phase1a s =>
    show p.ballot a ≤ Function.update p.ballot s _ a
    rw [Function.update_apply]; split_ifs with h
    · subst h; omega
    · exact le_rfl
  | phase1b s r b hm hb =>
    show p.ballot a ≤ Function.update p.ballot s _ a
    rw [Function.update_apply]; split_ifs with h
    · subst h; omega
    · exact le_rfl
  | phase2b s i b v hm hb =>
    show p.ballot a ≤ Function.update p.ballot s _ a
    rw [Function.update_apply]; split_ifs with h
    · subst h; omega
    · exact le_rfl
  | _ => exact le_rfl

theorem Step.new_vote (hs : Step Q p p') {a : N} {i c : ℕ} {w : V} (h1 : (a, i, c, w) ∈ p'.m2b)
    (h2 : (a, i, c, w) ∉ p.m2b) : p.ballot a ≤ c := by
  cases hs with
  | phase2b s i' b v hm hb =>
    rcases Set.mem_insert_iff.1 h1 with h1 | h1
    · simp only [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
      exact hb
    · exact absurd h1 h2
  | _ => exact absurd h1 h2

theorem Step.safeAt (hs : Step Q p p') {i b : ℕ} {v : V} (h : SafeAt Q p i b v) :
    SafeAt Q p' i b v :=
  h.mono hs.m2b_sub hs.ballot_le fun _ _ _ _ h1 h2 => hs.new_vote h1 h2

/-- A server keeps its leadership while its ballot does not change. -/
theorem Step.leader_keep (hs : Step Q p p') (a : N) (hb : p'.ballot a = p.ballot a)
    (hl : p.leader a = true) : p'.leader a = true := by
  cases hs with
  | phase1a s =>
    change Function.update p.ballot s _ a = _ at hb
    show Function.update p.leader s false a = true
    rw [Function.update_apply] at hb ⊢; split_ifs at hb ⊢ with h
    · subst h; omega
    · exact hl
  | phase1b s r b hm hb' =>
    change Function.update p.ballot s _ a = _ at hb
    show Function.update p.leader s false a = true
    rw [Function.update_apply] at hb ⊢; split_ifs at hb ⊢ with h
    · subst h; omega
    · exact hl
  | phase1Succeed s S newInst hl' hS hQ hself hsafe =>
    show Function.update p.leader s true a = true
    rw [Function.update_apply]; split_ifs <;> simp [hl]
  | phase2b s i b v hm hb' =>
    change Function.update p.ballot s _ a = _ at hb
    show Function.update p.leader s _ a = true
    rw [Function.update_apply] at hb ⊢; split_ifs at hb ⊢ with h h'
    · subst h; omega
    · subst h; exact hl
    · exact hl
  | _ => exact hl

/-! ### The inductive invariant -/

/-- The inductive invariant of MultiPaxos. -/
structure Inv (Q : QuorumSystem N) (p : State N V) : Prop where
  /-- An acceptor votes only at ballots up to its own. -/
  vote_bal : ∀ a i c v, (a, i, c, v) ∈ p.m2b → c ≤ p.ballot a
  /-- Votes are for proposals. -/
  vote_prop : ∀ a i c v, (a, i, c, v) ∈ p.m2b → (i, c, v) ∈ p.m2a
  /-- One proposal per instance and ballot. -/
  prop_uniq : ∀ i c v w, (i, c, v) ∈ p.m2a → (i, c, w) ∈ p.m2a → v = w
  /-- Proposals are safe. -/
  prop_safe : ∀ i c v, (i, c, v) ∈ p.m2a → SafeAt Q p i c v
  /-- A proposal of ballot `c` comes from a server that collected a quorum for `c` and is still
  leader while at ballot `c`. -/
  prop_leader : ∀ i c v, (i, c, v) ∈ p.m2a →
    ∃ r, HasQuorum Q p r c ∧ c ≤ p.ballot r ∧ (p.ballot r = c → p.leader r = true)
  /-- A leader collected a quorum for its ballot. -/
  leader_quorum : ∀ s, p.leader s = true → HasQuorum Q p s (p.ballot s)
  /-- The entries of a leader's log are safe at its ballot. -/
  leader_some : ∀ s i c v, p.leader s = true → p.inst s i = some (c, v) →
    SafeAt Q p i (p.ballot s) v
  /-- Every value is safe at an empty instance of a leader's log. -/
  leader_none : ∀ s i, p.leader s = true → p.inst s i = none → ∀ v, SafeAt Q p i (p.ballot s) v
  /-- Log entries are proposals. -/
  inst_prop : ∀ s i c v, p.inst s i = some (c, v) → (i, c, v) ∈ p.m2a
  /-- Log entries have ballots up to the server's own. -/
  inst_bal : ∀ s i c v, p.inst s i = some (c, v) → c ≤ p.ballot s
  /-- The log records (at least) the highest vote. -/
  inst_vote : ∀ a i d w, (a, i, d, w) ∈ p.m2b → ∃ c v, p.inst a i = some (c, v) ∧ d ≤ c
  /-- Reported entries are proposals. -/
  rep_prop : ∀ m ∈ p.m1b, ∀ i c v, m.log i = some (c, v) → (i, c, v) ∈ p.m2a
  /-- The sender of a `prepareOK` has moved to its ballot. -/
  rep_bal : ∀ m ∈ p.m1b, m.bal ≤ p.ballot m.src
  /-- Reported entries have lower ballots. -/
  rep_log_bal : ∀ m ∈ p.m1b, ∀ i c v, m.log i = some (c, v) → c < m.bal
  /-- A report covers all votes of its sender below its ballot. -/
  rep_vote : ∀ m ∈ p.m1b, ∀ i d w, (m.src, i, d, w) ∈ p.m2b → d < m.bal →
    ∃ c v, m.log i = some (c, v) ∧ d ≤ c
  /-- A server answers at most one `prepare` per ballot. -/
  rep_uniq : ∀ m ∈ p.m1b, ∀ m' ∈ p.m1b, m.src = m'.src → m.bal = m'.bal → m.dst = m'.dst
  /-- Learned values were chosen. -/
  chosen : ∀ s i v, (i, v) ∈ p.chosen s → ∃ b, ChosenAt Q p i b v

omit [DecidableEq N] in
theorem inv_init : Inv Q (init : State N V) where
  vote_bal := fun _ _ _ _ h => h.elim
  vote_prop := fun _ _ _ _ h => h.elim
  prop_uniq := fun _ _ _ _ h => h.elim
  prop_safe := fun _ _ _ h => h.elim
  prop_leader := fun _ _ _ h => h.elim
  leader_quorum := fun _ h => by simp [init] at h
  leader_some := fun _ _ _ _ h => by simp [init] at h
  leader_none := fun _ _ h => by simp [init] at h
  inst_prop := fun _ _ _ _ h => by simp [init] at h
  inst_bal := fun _ _ _ _ h => by simp [init] at h
  inst_vote := fun _ _ _ _ h => h.elim
  rep_prop := fun _ h => h.elim
  rep_bal := fun _ h => h.elim
  rep_log_bal := fun _ h => h.elim
  rep_vote := fun _ h => h.elim
  rep_uniq := fun _ h => h.elim
  chosen := fun _ _ _ h => h.elim

omit [DecidableEq N] in
/-- Two servers collecting a quorum for the same ballot are equal. -/
theorem Inv.hasQuorum_unique (h : Inv Q p) {r r' : N} {b : ℕ} (h₁ : HasQuorum Q p r b)
    (h₂ : HasQuorum Q p r' b) : r = r' := by
  obtain ⟨A, hA, hA'⟩ := h₁
  obtain ⟨A', hA₂, hA₂'⟩ := h₂
  obtain ⟨a, ha, ha'⟩ := Q.inter A A' hA hA₂
  obtain ⟨L, hL⟩ := hA' a ha
  obtain ⟨L', hL'⟩ := hA₂' a ha'
  exact h.rep_uniq _ hL _ hL' rfl rfl

/-- The `Phase1Succeed` lemma, nonempty case: the highest reported entry of a quorum of
`prepareOK`s for ballot `b` is safe at `b`. -/
theorem Inv.safeAt_of_safeEntry_some (h : Inv Q p) {S : Finset (Msg1b N V)} {b : ℕ}
    (hS : ∀ m ∈ S, m ∈ p.m1b ∧ m.bal = b) (hQ : Q.IsQuorum (S.image Msg1b.src)) {i c : ℕ} {v : V}
    (he : IsSafeEntry S i (some (c, v))) : SafeAt Q p i b v := by
  obtain ⟨⟨m₀, hm₀, hlog₀⟩, hmax⟩ := he
  have hprop : (i, c, v) ∈ p.m2a := h.rep_prop m₀ (hS m₀ hm₀).1 i c v hlog₀
  intro d hd
  by_cases hdc : d < c
  · exact h.prop_safe i c v hprop d hdc
  refine ⟨_, hQ, fun a ha => ?_⟩
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨hm1, hmb⟩ := hS m hm
  by_cases hv : ∃ w, (m.src, i, d, w) ∈ p.m2b
  · obtain ⟨w, hw⟩ := hv
    obtain ⟨c', v', hlog, hdc'⟩ := h.rep_vote m hm1 i d w hw (hmb ▸ hd)
    have hc' := hmax m hm c' v' hlog
    have hdc : d = c := by omega
    subst hdc
    have := h.prop_uniq _ _ _ _ hprop (h.vote_prop _ _ _ _ hw)
    subst this
    exact Or.inl hw
  · push Not at hv
    exact Or.inr ⟨lt_of_lt_of_le hd (hmb ▸ h.rep_bal m hm1), hv⟩

/-- The `Phase1Succeed` lemma, empty case: if no `prepareOK` of a quorum for ballot `b` reports an
entry, every value is safe at `b`. -/
theorem Inv.safeAt_of_safeEntry_none (h : Inv Q p) {S : Finset (Msg1b N V)} {b : ℕ}
    (hS : ∀ m ∈ S, m ∈ p.m1b ∧ m.bal = b) (hQ : Q.IsQuorum (S.image Msg1b.src)) {i : ℕ}
    (he : IsSafeEntry S i none) (v : V) : SafeAt Q p i b v := by
  intro d hd
  refine ⟨_, hQ, fun a ha => ?_⟩
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨hm1, hmb⟩ := hS m hm
  refine Or.inr ⟨lt_of_lt_of_le hd (hmb ▸ h.rep_bal m hm1), fun w hw => ?_⟩
  obtain ⟨c', v', hlog, -⟩ := h.rep_vote m hm1 i d w hw (hmb ▸ hd)
  have : m.log i = none := he m hm
  rw [this] at hlog
  cases hlog

/-- `s` collected a quorum of `prepareOK`s `S` for its ballot. -/
theorem hasQuorum_of_reports {s : N} {S : Finset (Msg1b N V)}
    (hS : ∀ m ∈ S, m ∈ p.m1b ∧ m.dst = s ∧ m.bal = p.ballot s)
    (hQ : Q.IsQuorum (S.image Msg1b.src)) : HasQuorum Q p s (p.ballot s) := by
  refine ⟨_, hQ, fun x hx => ?_⟩
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨h1, h2, h3⟩ := hS m hm
  have e : m = ⟨m.src, s, p.ballot s, m.log⟩ := Msg1b.ext rfl h2 h3 rfl
  exact ⟨m.log, e ▸ h1⟩

/-- The invariant is preserved by every step. -/
theorem Inv.step (h : Inv Q p) (hs : Step Q p p') : Inv Q p' := by
  have hsafe : ∀ {i b v}, SafeAt Q p i b v → SafeAt Q p' i b v := fun hh => hs.safeAt hh
  have hbal := hs.ballot_le
  have hm1b := hs.m1b_sub
  have hm2b := hs.m2b_sub
  have hm2a := hs.m2a_sub
  have hpl : ∀ i c v, (i, c, v) ∈ p.m2a →
      ∃ r, HasQuorum Q p' r c ∧ c ≤ p'.ballot r ∧ (p'.ballot r = c → p'.leader r = true) := by
    intro i c v hv
    obtain ⟨r, hq, hle, hl⟩ := h.prop_leader i c v hv
    have := hbal r
    exact ⟨r, hq.mono hm1b, hle.trans this, fun he => hs.leader_keep r (by omega) (hl (by omega))⟩
  have hch : ∀ s i v, (i, v) ∈ p.chosen s → ∃ b, ChosenAt Q p' i b v :=
    fun s i v hc => (h.chosen s i v hc).imp fun _ hb => hb.mono hm2b
  cases hs with
  | phase1a s =>
    have hL : ∀ a, Function.update p.leader s false a = true →
        a ≠ s ∧ p.leader a = true ∧ Function.update p.ballot s (p.ballot s + 1) a = p.ballot a := by
      intro a ha
      have hne : a ≠ s := by rintro rfl; simp at ha
      rw [Function.update_of_ne hne] at ha
      exact ⟨hne, ha, Function.update_of_ne hne _ _⟩
    refine
      { vote_bal := fun a i c v hv => (h.vote_bal a i c v hv).trans (hbal a)
        vote_prop := h.vote_prop
        prop_uniq := h.prop_uniq
        prop_safe := fun i c v hv => hsafe (h.prop_safe i c v hv)
        prop_leader := hpl
        leader_quorum := fun a ha => ?_
        leader_some := fun a i c v ha hi => ?_
        leader_none := fun a i ha hi w => ?_
        inst_prop := h.inst_prop
        inst_bal := fun a i c v hv => (h.inst_bal a i c v hv).trans (hbal a)
        inst_vote := h.inst_vote
        rep_prop := fun m hm i c v hl => ?_
        rep_bal := fun m hm => ?_
        rep_log_bal := fun m hm i c v hl => ?_
        rep_vote := fun m hm i d w hv hd => ?_
        rep_uniq := fun m hm m' hm' e1 e2 => ?_
        chosen := hch }
    · obtain ⟨-, ha, hb⟩ := hL a ha
      dsimp only; rw [hb]; exact (h.leader_quorum a ha).mono hm1b
    · obtain ⟨-, ha, hb⟩ := hL a ha
      dsimp only; rw [hb]; exact hsafe (h.leader_some a i c v ha hi)
    · obtain ⟨-, ha, hb⟩ := hL a ha
      dsimp only; rw [hb]; exact hsafe (h.leader_none a i ha hi w)
    · rcases Set.mem_insert_iff.1 hm with rfl | hm
      · exact h.inst_prop s i c v hl
      · exact h.rep_prop m hm i c v hl
    · rcases Set.mem_insert_iff.1 hm with rfl | hm
      · simp
      · exact (h.rep_bal m hm).trans (hbal _)
    · rcases Set.mem_insert_iff.1 hm with rfl | hm
      · exact Nat.lt_succ_of_le (h.inst_bal s i c v hl)
      · exact h.rep_log_bal m hm i c v hl
    · rcases Set.mem_insert_iff.1 hm with rfl | hm
      · exact h.inst_vote s i d w hv
      · exact h.rep_vote m hm i d w hv hd
    · rcases Set.mem_insert_iff.1 hm with rfl | hm <;>
        rcases Set.mem_insert_iff.1 hm' with rfl | hm'
      · rfl
      · have := h.rep_bal m' hm'; dsimp only at e1 e2 this; rw [← e1] at this; omega
      · have := h.rep_bal m hm; dsimp only at e1 e2 this; rw [e1] at this; omega
      · exact h.rep_uniq m hm m' hm' e1 e2
  | phase1b s r b hmr hb =>
    have hL : ∀ a, Function.update p.leader s false a = true →
        a ≠ s ∧ p.leader a = true ∧ Function.update p.ballot s b a = p.ballot a := by
      intro a ha
      have hne : a ≠ s := by rintro rfl; simp at ha
      rw [Function.update_of_ne hne] at ha
      exact ⟨hne, ha, Function.update_of_ne hne _ _⟩
    refine
      { vote_bal := fun a i c v hv => (h.vote_bal a i c v hv).trans (hbal a)
        vote_prop := h.vote_prop
        prop_uniq := h.prop_uniq
        prop_safe := fun i c v hv => hsafe (h.prop_safe i c v hv)
        prop_leader := hpl
        leader_quorum := fun a ha => ?_
        leader_some := fun a i c v ha hi => ?_
        leader_none := fun a i ha hi w => ?_
        inst_prop := h.inst_prop
        inst_bal := fun a i c v hv => (h.inst_bal a i c v hv).trans (hbal a)
        inst_vote := h.inst_vote
        rep_prop := fun m hm i c v hl => ?_
        rep_bal := fun m hm => ?_
        rep_log_bal := fun m hm i c v hl => ?_
        rep_vote := fun m hm i d w hv hd => ?_
        rep_uniq := fun m hm m' hm' e1 e2 => ?_
        chosen := hch }
    · obtain ⟨-, ha, hb⟩ := hL a ha
      dsimp only; rw [hb]; exact (h.leader_quorum a ha).mono hm1b
    · obtain ⟨-, ha, hb⟩ := hL a ha
      dsimp only; rw [hb]; exact hsafe (h.leader_some a i c v ha hi)
    · obtain ⟨-, ha, hb⟩ := hL a ha
      dsimp only; rw [hb]; exact hsafe (h.leader_none a i ha hi w)
    · rcases Set.mem_insert_iff.1 hm with rfl | hm
      · exact h.inst_prop s i c v hl
      · exact h.rep_prop m hm i c v hl
    · rcases Set.mem_insert_iff.1 hm with rfl | hm
      · simp
      · exact (h.rep_bal m hm).trans (hbal _)
    · rcases Set.mem_insert_iff.1 hm with rfl | hm
      · exact lt_of_le_of_lt (h.inst_bal s i c v hl) hb
      · exact h.rep_log_bal m hm i c v hl
    · rcases Set.mem_insert_iff.1 hm with rfl | hm
      · exact h.inst_vote s i d w hv
      · exact h.rep_vote m hm i d w hv hd
    · rcases Set.mem_insert_iff.1 hm with rfl | hm <;>
        rcases Set.mem_insert_iff.1 hm' with rfl | hm'
      · rfl
      · have := h.rep_bal m' hm'; dsimp only at e1 e2 this; rw [← e1] at this; omega
      · have := h.rep_bal m hm; dsimp only at e1 e2 this; rw [e1] at this; omega
      · exact h.rep_uniq m hm m' hm' e1 e2
  | phase1Succeed s S newInst hl hS hQ hself hse =>
    have hS' : ∀ m ∈ S, m ∈ p.m1b ∧ m.bal = p.ballot s := fun m hm => ⟨(hS m hm).1, (hS m hm).2.2⟩
    have hQs : HasQuorum Q p s (p.ballot s) := hasQuorum_of_reports hS hQ
    refine
      { vote_bal := h.vote_bal
        vote_prop := h.vote_prop
        prop_uniq := h.prop_uniq
        prop_safe := h.prop_safe
        prop_leader := hpl
        leader_quorum := fun a ha => ?_
        leader_some := fun a i c v ha hi => ?_
        leader_none := fun a i ha hi w => ?_
        inst_prop := fun a i c v hi => ?_
        inst_bal := fun a i c v hi => ?_
        inst_vote := fun a i d w hv => ?_
        rep_prop := h.rep_prop
        rep_bal := h.rep_bal
        rep_log_bal := h.rep_log_bal
        rep_vote := h.rep_vote
        rep_uniq := h.rep_uniq
        chosen := hch }
    · rcases eq_or_ne a s with rfl | hne
      · exact hQs
      · change Function.update p.leader s true a = true at ha
        rw [Function.update_of_ne hne] at ha
        exact h.leader_quorum a ha
    · change Function.update p.inst s newInst a i = some (c, v) at hi
      rcases eq_or_ne a s with rfl | hne
      · rw [Function.update_self] at hi
        have := hse i
        rw [hi] at this
        exact h.safeAt_of_safeEntry_some hS' hQ this
      · change Function.update p.leader s true a = true at ha
        rw [Function.update_of_ne hne] at ha hi
        exact h.leader_some a i c v ha hi
    · change Function.update p.inst s newInst a i = none at hi
      rcases eq_or_ne a s with rfl | hne
      · rw [Function.update_self] at hi
        have := hse i
        rw [hi] at this
        exact h.safeAt_of_safeEntry_none hS' hQ this w
      · change Function.update p.leader s true a = true at ha
        rw [Function.update_of_ne hne] at ha hi
        exact h.leader_none a i ha hi w
    · change Function.update p.inst s newInst a i = some (c, v) at hi
      rcases eq_or_ne a s with rfl | hne
      · rw [Function.update_self] at hi
        have := hse i
        rw [hi] at this
        obtain ⟨⟨m, hm, hlog⟩, -⟩ := this
        exact h.rep_prop m (hS m hm).1 i c v hlog
      · rw [Function.update_of_ne hne] at hi
        exact h.inst_prop a i c v hi
    · change Function.update p.inst s newInst a i = some (c, v) at hi
      rcases eq_or_ne a s with rfl | hne
      · rw [Function.update_self] at hi
        have := hse i
        rw [hi] at this
        obtain ⟨⟨m, hm, hlog⟩, -⟩ := this
        have := h.rep_log_bal m (hS m hm).1 i c v hlog
        rw [(hS m hm).2.2] at this
        exact this.le
      · rw [Function.update_of_ne hne] at hi
        exact h.inst_bal a i c v hi
    · show ∃ c v, Function.update p.inst s newInst a i = some (c, v) ∧ d ≤ c
      rcases eq_or_ne a s with rfl | hne
      · rw [Function.update_self]
        -- the new leader has not voted in its own ballot yet
        have hd : d < p.ballot a := by
          refine lt_of_le_of_ne (h.vote_bal a i d w hv) fun hda => ?_
          obtain ⟨r, hq, -, hlr⟩ := h.prop_leader i d w (h.vote_prop a i d w hv)
          rw [hda] at hq
          have hra := h.hasQuorum_unique hq hQs
          subst hra
          have := hlr hda.symm
          rw [hl] at this
          exact Bool.noConfusion this
        obtain ⟨m, hm, hms⟩ := hself
        obtain ⟨hm1, -, hmb⟩ := hS m hm
        rw [← hms] at hv
        obtain ⟨c', v', hlog, hdc'⟩ := h.rep_vote m hm1 i d w hv (hmb ▸ hd)
        have he := hse i
        cases hni : newInst i with
        | none =>
          rw [hni] at he
          rw [he m hm] at hlog
          cases hlog
        | some e =>
          obtain ⟨c, v⟩ := e
          rw [hni] at he
          exact ⟨c, v, rfl, hdc'.trans (he.2 m hm c' v' hlog)⟩
      · rw [Function.update_of_ne hne]
        exact h.inst_vote a i d w hv
  | phase2a s i v hl hv huniq =>
    refine
      { vote_bal := h.vote_bal
        vote_prop := fun a i c v hv => hm2a (h.vote_prop a i c v hv)
        prop_uniq := fun i' c v1 v2 h1 h2 => ?_
        prop_safe := fun i' c w hw => ?_
        prop_leader := fun i' c w hw => ?_
        leader_quorum := fun a ha => (h.leader_quorum a ha).mono hm1b
        leader_some := fun a i c v ha hi => hsafe (h.leader_some a i c v ha hi)
        leader_none := fun a i ha hi w => hsafe (h.leader_none a i ha hi w)
        inst_prop := fun a i c v hi => hm2a (h.inst_prop a i c v hi)
        inst_bal := h.inst_bal
        inst_vote := h.inst_vote
        rep_prop := fun m hm i c v hl => hm2a (h.rep_prop m hm i c v hl)
        rep_bal := h.rep_bal
        rep_log_bal := h.rep_log_bal
        rep_vote := h.rep_vote
        rep_uniq := h.rep_uniq
        chosen := hch }
    · rcases Set.mem_insert_iff.1 h1 with e1 | h1' <;> rcases Set.mem_insert_iff.1 h2 with e2 | h2'
      · simp only [Prod.mk.injEq] at e1 e2
        rw [e1.2.2, e2.2.2]
      · simp only [Prod.mk.injEq] at e1
        obtain ⟨rfl, rfl, rfl⟩ := e1
        exact (huniq v2 h2').symm
      · simp only [Prod.mk.injEq] at e2
        obtain ⟨rfl, rfl, rfl⟩ := e2
        exact huniq v1 h1'
      · exact h.prop_uniq i' c v1 v2 h1' h2'
    · rcases Set.mem_insert_iff.1 hw with e | hw
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        rcases hv with hn | ⟨c, hc⟩
        · exact hsafe (h.leader_none s i' hl hn w)
        · exact hsafe (h.leader_some s i' c w hl hc)
      · exact hsafe (h.prop_safe i' c w hw)
    · rcases Set.mem_insert_iff.1 hw with e | hw
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        exact ⟨s, (h.leader_quorum s hl).mono hm1b, le_rfl, fun _ => hl⟩
      · exact hpl i' c w hw
  | phase2b s i b v hm hb =>
    have hL : ∀ a, Function.update p.leader s (if p.ballot s < b then false else p.leader s) a = true →
        p.leader a = true ∧ Function.update p.ballot s b a = p.ballot a := by
      intro a ha
      rcases eq_or_ne a s with rfl | hne
      · rw [Function.update_self] at ha
        split_ifs at ha with hlt
        · exact ⟨ha, by rw [Function.update_self]; omega⟩
      · rw [Function.update_of_ne hne] at ha
        exact ⟨ha, Function.update_of_ne hne _ _⟩
    refine
      { vote_bal := fun a i' c w hv => ?_
        vote_prop := fun a i' c w hv => ?_
        prop_uniq := h.prop_uniq
        prop_safe := fun i c v hv => hsafe (h.prop_safe i c v hv)
        prop_leader := hpl
        leader_quorum := fun a ha => ?_
        leader_some := fun a i' c w ha hi => ?_
        leader_none := fun a i' ha hi w => ?_
        inst_prop := fun a i' c w hi => ?_
        inst_bal := fun a i' c w hi => ?_
        inst_vote := fun a i' d w hv => ?_
        rep_prop := h.rep_prop
        rep_bal := fun m hm => (h.rep_bal m hm).trans (hbal _)
        rep_log_bal := h.rep_log_bal
        rep_vote := fun m hm i' d w hv hd => ?_
        rep_uniq := h.rep_uniq
        chosen := hch }
    · rcases Set.mem_insert_iff.1 hv with e | hv
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, rfl, rfl⟩ := e
        simp
      · exact (h.vote_bal a i' c w hv).trans (hbal a)
    · rcases Set.mem_insert_iff.1 hv with e | hv
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, rfl, rfl⟩ := e
        exact hm
      · exact h.vote_prop a i' c w hv
    · obtain ⟨ha, hb'⟩ := hL a ha
      dsimp only; rw [hb']; exact (h.leader_quorum a ha).mono hm1b
    · obtain ⟨ha', hb'⟩ := hL a ha
      dsimp only; rw [hb']
      change Function.update p.inst s _ a i' = some (c, w) at hi
      rcases eq_or_ne a s with rfl | hne
      · rw [Function.update_self, Function.update_apply] at hi
        rw [Function.update_self] at hb'
        split_ifs at hi with hii
        · subst hii
          simp only [Option.some.injEq, Prod.mk.injEq] at hi
          obtain ⟨rfl, rfl⟩ := hi
          rw [← hb']
          exact hsafe (h.prop_safe _ _ _ hm)
        · exact hsafe (h.leader_some a i' c w ha' hi)
      · rw [Function.update_of_ne hne] at hi
        exact hsafe (h.leader_some a i' c w ha' hi)
    · obtain ⟨ha', hb'⟩ := hL a ha
      dsimp only; rw [hb']
      change Function.update p.inst s _ a i' = none at hi
      rcases eq_or_ne a s with rfl | hne
      · rw [Function.update_self, Function.update_apply] at hi
        split_ifs at hi with hii
        exact hsafe (h.leader_none a i' ha' hi w)
      · rw [Function.update_of_ne hne] at hi
        exact hsafe (h.leader_none a i' ha' hi w)
    · change Function.update p.inst s _ a i' = some (c, w) at hi
      rcases eq_or_ne a s with rfl | hne
      · rw [Function.update_self, Function.update_apply] at hi
        split_ifs at hi with hii
        · subst hii
          simp only [Option.some.injEq, Prod.mk.injEq] at hi
          obtain ⟨rfl, rfl⟩ := hi
          exact hm
        · exact h.inst_prop a i' c w hi
      · rw [Function.update_of_ne hne] at hi
        exact h.inst_prop a i' c w hi
    · change Function.update p.inst s _ a i' = some (c, w) at hi
      show c ≤ Function.update p.ballot s b a
      rcases eq_or_ne a s with rfl | hne
      · rw [Function.update_self, Function.update_apply] at hi
        rw [Function.update_self]
        split_ifs at hi with hii
        · simp only [Option.some.injEq, Prod.mk.injEq] at hi
          omega
        · exact (h.inst_bal a i' c w hi).trans hb
      · rw [Function.update_of_ne hne] at hi ⊢
        exact h.inst_bal a i' c w hi
    · show ∃ c v', Function.update p.inst s (Function.update (p.inst s) i (some (b, v))) a i' =
          some (c, v') ∧ d ≤ c
      rcases Set.mem_insert_iff.1 hv with e | hv'
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, rfl, rfl⟩ := e
        exact ⟨d, w, by simp, le_rfl⟩
      · rcases eq_or_ne a s with rfl | hne
        · rw [Function.update_self, Function.update_apply]
          split_ifs with hii
          · exact ⟨b, v, rfl, (h.vote_bal a i' d w hv').trans hb⟩
          · exact h.inst_vote a i' d w hv'
        · rw [Function.update_of_ne hne]
          exact h.inst_vote a i' d w hv'
    · rcases Set.mem_insert_iff.1 hv with e | hv
      · simp only [Prod.mk.injEq] at e
        obtain ⟨e1, rfl, rfl, rfl⟩ := e
        have := h.rep_bal m hm
        rw [e1] at this
        omega
      · exact h.rep_vote m hm i' d w hv hd
  | learn s i b v A hA hacc =>
    refine
      { vote_bal := h.vote_bal
        vote_prop := h.vote_prop
        prop_uniq := h.prop_uniq
        prop_safe := h.prop_safe
        prop_leader := h.prop_leader
        leader_quorum := h.leader_quorum
        leader_some := h.leader_some
        leader_none := h.leader_none
        inst_prop := h.inst_prop
        inst_bal := h.inst_bal
        inst_vote := h.inst_vote
        rep_prop := h.rep_prop
        rep_bal := h.rep_bal
        rep_log_bal := h.rep_log_bal
        rep_vote := h.rep_vote
        rep_uniq := h.rep_uniq
        chosen := fun a i' w hc => ?_ }
    change (i', w) ∈ Function.update p.chosen s _ a at hc
    rcases eq_or_ne a s with rfl | hne
    · rw [Function.update_self] at hc
      rcases Set.mem_insert_iff.1 hc with e | hc
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact ⟨b, A, hA, hacc⟩
      · exact h.chosen a i' w hc
    · rw [Function.update_of_ne hne] at hc
      exact h.chosen a i' w hc

/-- The invariant holds in every reachable state. -/
theorem Reachable.inv (hp : Reachable Q p) : Inv Q p := by
  induction hp with
  | refl => exact inv_init
  | tail _ hs ih => exact ih.step hs

/-! ### Safety -/

/-- Every entry of a `chosenSet` was chosen by a quorum. -/
theorem chosen_chosenAt (hp : Reachable Q p) {s : N} {i : ℕ} {v : V} (h : (i, v) ∈ p.chosen s) :
    ∃ b, ChosenAt Q p i b v := by
  exact hp.inv.chosen s i v h

/-- The key Paxos lemma: once `v` is chosen in ballot `b`, every proposal for the same instance in
a ballot `b' ≥ b` proposes `v`. -/
theorem proposal_eq_of_chosenAt (hp : Reachable Q p) {i b b' : ℕ} {v w : V}
    (hc : ChosenAt Q p i b v) (hw : (i, b', w) ∈ p.m2a) (hbb : b ≤ b') : w = v := by
  have h := hp.inv
  obtain ⟨A, hA, hacc⟩ := hc
  rcases eq_or_lt_of_le hbb with rfl | hlt
  · obtain ⟨a, ha⟩ := QuorumSystem.nonempty hA
    exact h.prop_uniq i b w v hw (h.vote_prop a i b v (hacc a ha))
  · obtain ⟨A', hA', hsafe⟩ := h.prop_safe i b' w hw b hlt
    obtain ⟨a, ha, ha'⟩ := Q.inter A A' hA hA'
    rcases hsafe a ha' with hv | ⟨-, hno⟩
    · exact h.prop_uniq i b w v (h.vote_prop a i b w hv) (h.vote_prop a i b v (hacc a ha))
    · exact absurd (hacc a ha) (hno v)

/-- At most one value is chosen per instance (TLA+ `chosen` has at most one element). -/
theorem chosenAt_agree (hp : Reachable Q p) {i b b' : ℕ} {v w : V}
    (h₁ : ChosenAt Q p i b v) (h₂ : ChosenAt Q p i b' w) : v = w := by
  have h := hp.inv
  rcases le_total b b' with hbb | hbb
  · obtain ⟨A, hA, hacc⟩ := h₂
    obtain ⟨a, ha⟩ := QuorumSystem.nonempty hA
    exact (proposal_eq_of_chosenAt hp h₁ (h.vote_prop a i b' w (hacc a ha)) hbb).symm
  · obtain ⟨A, hA, hacc⟩ := h₁
    obtain ⟨a, ha⟩ := QuorumSystem.nonempty hA
    exact proposal_eq_of_chosenAt hp h₂ (h.vote_prop a i b v (hacc a ha)) hbb

/-- **Safety of MultiPaxos**: two servers never put different values for the same instance in
their `chosenSet`. -/
theorem safety (hp : Reachable Q p) {s s' : N} {i : ℕ} {v w : V}
    (h₁ : (i, v) ∈ p.chosen s) (h₂ : (i, w) ∈ p.chosen s') : v = w := by
  obtain ⟨b, hb⟩ := chosen_chosenAt hp h₁
  obtain ⟨b', hb'⟩ := chosen_chosenAt hp h₂
  exact chosenAt_agree hp hb hb'

/-! ### Non-vacuity -/

/-- Non-vacuity: with three servers and majority quorums, server `0` can become leader of ballot `1`
with the help of server `1`, propose `7` for instance `0`, get it accepted by `{0, 1}` and learn
it. -/
theorem exists_reachable_chosen :
    ∃ p : State (Fin 3) ℕ, Reachable (QuorumSystem.majority (Fin 3)) p ∧ (0, 7) ∈ p.chosen 0 := by
  classical
  let Q := QuorumSystem.majority (Fin 3)
  let S : Finset (Msg1b (Fin 3) ℕ) := {⟨0, 0, 1, fun _ => none⟩, ⟨1, 0, 1, fun _ => none⟩}
  have r1 : Reachable Q _ := Relation.ReflTransGen.single (Step.phase1a (V := ℕ) init 0)
  have r2 := r1.tail (Step.phase1b _ 1 0 1 (by simp [init]) (by simp [init]))
  have r3 := r2.tail (Step.phase1Succeed _ 0 S (fun _ => none) (by simp [init])
    (by
      intro m hm
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl <;> simp [init])
    (by simp [S, Q, QuorumSystem.majority])
    ⟨⟨0, 0, 1, fun _ => none⟩, by simp [S], rfl⟩
    (fun i m hm => by
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl <;> rfl))
  have r4 := r3.tail (Step.phase2a _ 0 0 7 (by simp) (by simp [init]) (by simp [init]))
  have r5 := r4.tail (Step.phase2b _ 0 0 1 7 (by simp [init]) (by simp [init]))
  have r6 := r5.tail (Step.phase2b _ 1 0 1 7 (by simp [init]) (by simp [init]))
  have r7 := r6.tail (Step.learn _ 0 0 1 7 {0, 1} (by simp [Q, QuorumSystem.majority])
    (by intro a ha; simp at ha; rcases ha with rfl | rfl <;> simp))
  exact ⟨_, r7, by simp⟩

end Podc.PaxosRaftRefinement.Paxos
