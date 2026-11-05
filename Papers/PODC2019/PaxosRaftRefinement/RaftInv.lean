import Papers.PODC2019.PaxosRaftRefinement.RaftStar

/-!
# Invariants of (repaired) Raft*

The inductive invariant `Inv` of Raft* under any rules whose vote rule only lets a server vote for
a candidate whose last term is at least its own (`VoteMono`) and without heartbeats. These are
the facts the refinement proof of Appendix C silently relies on ("`s.instances[0, s.lastIndex]` is
already the safeEntries of Paxos algorithm", step 2.3/4.2): log matching, at most one leader per
term, a candidate's log is its own vote, every log entry is a proposal of its term, and every log
has been accepted in the ballot of its last term.

Preservation for `receiveAppend` uses one Paxos fact on the ghost variables (`PropSafe`): a
proposal in a ballot at least that of a quorum's acceptance carries the accepted value. It is
supplied by the safety of MultiPaxos through the refinement (`Refinement.lean`).
-/

namespace Podc.PaxosRaftRefinement.Raft

variable {N V : Type*} [DecidableEq N]

/-- `L` is one of the logs present in the system: a server's log, or a log carried by a vote or
an `append` message. -/
def InLogs (r : State N V) (L : List (ℕ × V)) : Prop :=
  (∃ s, L = r.log s) ∨ (∃ m ∈ r.rvok, L = m.log) ∨ (∃ m ∈ r.ae, L = m.full)

/-- `c` received votes of a quorum for term `t`. -/
def Cand (Q : QuorumSystem N) (r : State N V) (c : N) (t : ℕ) : Prop :=
  ∃ S : Finset (RVOKMsg N V), (∀ m ∈ S, m ∈ r.rvok ∧ m.dst = c ∧ m.term = t) ∧
    Q.IsQuorum (S.image RVOKMsg.src)

/-- `v` was accepted for index `i` by a quorum in one ballot `b ≤ t` (ghost `acks`). -/
def CommittedAt (Q : QuorumSystem N) (r : State N V) (i t : ℕ) (v : V) : Prop :=
  ∃ b ≤ t, ∃ A, Q.IsQuorum A ∧ ∀ a ∈ A, (a, i, b, v) ∈ r.acks

/-- The Paxos fact used to show that committed entries are never overwritten. -/
def PropSafe (Q : QuorumSystem N) (r : State N V) : Prop :=
  ∀ i b b' (v w : V), (∃ A, Q.IsQuorum A ∧ ∀ a ∈ A, (a, i, b, v) ∈ r.acks) →
    (i, b', w) ∈ r.props → b ≤ b' → w = v

/-- The vote rule never lets a server vote for a candidate with a smaller last term. -/
def VoteMono (R : Rules V) : Prop := ∀ L n t, R.voteOK L n t → lastTerm L ≤ t

/-- The inductive invariant of Raft*. -/
structure Inv (Q : QuorumSystem N) (r : State N V) : Prop where
  entry_props : ∀ L, InLogs r L → ∀ i (h : i < L.length), (i, L[i].1, L[i].2) ∈ r.props
  last_props : ∀ L, InLogs r L → ∀ i (h : i < L.length), (i, lastTerm L, L[i].2) ∈ r.props
  props_unique : ∀ i t (v w : V), (i, t, v) ∈ r.props → (i, t, w) ∈ r.props → v = w
  props_leader : ∀ i t (v : V), (i, t, v) ∈ r.props → ∃ c, Cand Q r c t ∧ t ≤ r.term c ∧
    (r.term c = t → r.leader c = true ∧ lastTerm (r.log c) = t ∧
      ∃ h : i < (r.log c).length, (r.log c)[i].2 = v)
  rvok_unique : ∀ m ∈ r.rvok, ∀ m' ∈ r.rvok, m.src = m'.src → m.term = m'.term →
    m.dst = m'.dst ∧ m.log = m'.log
  rvok_term : ∀ m ∈ r.rvok, m.term ≤ r.term m.src
  rvok_vote : ∀ m ∈ r.rvok, ∃ L, ⟨m.dst, m.dst, m.term, L⟩ ∈ r.rvok ∧ lastTerm m.log ≤ lastTerm L
  rv_ok : ∀ m ∈ r.rv, ∃ L, ⟨m.cand, m.cand, m.term, L⟩ ∈ r.rvok ∧ m.len = L.length ∧
    m.lterm = lastTerm L
  leader_cand : ∀ c, r.leader c = true → Cand Q r c (r.term c)
  cand_log : ∀ c L, ⟨c, c, r.term c, L⟩ ∈ r.rvok → r.leader c = false → r.log c ≠ L →
    ∃ c', c' ≠ c ∧ Cand Q r c' (r.term c)
  ae_ok : ∀ m ∈ r.ae, Cand Q r m.src m.term ∧ m.term ≤ r.term m.src ∧ m.full ≠ [] ∧
    lastTerm m.full = m.term ∧ m.prevLen ≤ m.full.length ∧ m.commit ≤ m.full.length ∧
    ∀ i (_ : i < m.commit) (h : i < m.full.length), CommittedAt Q r i m.term m.full[i].2
  commit_le : ∀ s, r.commit s ≤ (r.log s).length
  commit_ok : ∀ s i (_ : i < r.commit s) (h : i < (r.log s).length),
    CommittedAt Q r i (r.term s) (r.log s)[i].2
  acks_props : ∀ a i t (v : V), (a, i, t, v) ∈ r.acks → (i, t, v) ∈ r.props ∧ t ≤ r.term a
  self_acks : ∀ s i (h : i < (r.log s).length), (s, i, lastTerm (r.log s), (r.log s)[i].2) ∈ r.acks
  aeok_ok : ∀ m ∈ r.aeok, ∀ i < m.len, ∃ v, (m.src, i, m.term, v) ∈ r.acks
  lastTerm_le : ∀ s, lastTerm (r.log s) ≤ r.term s
  log_matching : ∀ L₁ L₂, InLogs r L₁ → InLogs r L₂ → ∀ i (h₁ : i < L₁.length)
    (h₂ : i < L₂.length), L₁[i].1 = L₂[i].1 → L₁.take (i + 1) = L₂.take (i + 1)


/-! ### Basic lemmas -/

theorem lastTerm_nil : lastTerm ([] : List (ℕ × V)) = 0 := rfl

theorem lastTerm_append_map {L : List (ℕ × V)} {vals : List V} (t : ℕ) (h : vals ≠ []) :
    lastTerm (L ++ vals.map (fun v => (t, v))) = t := by
  unfold lastTerm
  rw [List.getLast?_append]
  obtain ⟨w, ws, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [List.getLast?_map, List.getLast?_cons]

theorem lastTerm_append_nil {L : List (ℕ × V)} (t : ℕ) :
    lastTerm (L ++ ([] : List V).map (fun v => (t, v))) = lastTerm L := by simp

variable {Q : QuorumSystem N} {r r' : State N V}

theorem Cand.mono {c : N} {t : ℕ} (h : Cand Q r c t) (hs : r.rvok ⊆ r'.rvok) : Cand Q r' c t := by
  obtain ⟨S, hS, hQ⟩ := h
  exact ⟨S, fun m hm => ⟨hs (hS m hm).1, (hS m hm).2⟩, hQ⟩

theorem CommittedAt.mono {i t t' : ℕ} {v : V} (h : CommittedAt Q r i t v) (hs : r.acks ⊆ r'.acks)
    (ht : t ≤ t') : CommittedAt Q r' i t' v := by
  obtain ⟨b, hb, A, hA, hA'⟩ := h
  exact ⟨b, hb.trans ht, A, hA, fun a ha => hs (hA' a ha)⟩

theorem Inv.cand_unique (I : Inv Q r) {c c' : N} {t : ℕ} (h : Cand Q r c t) (h' : Cand Q r c' t) :
    c = c' := by
  obtain ⟨S, hS, hQ⟩ := h
  obtain ⟨S', hS', hQ'⟩ := h'
  obtain ⟨a, ha, ha'⟩ := Q.inter _ _ hQ hQ'
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨m', hm', hmm⟩ := Finset.mem_image.1 ha'
  have := I.rvok_unique m (hS m hm).1 m' (hS' m' hm').1 hmm.symm
    ((hS m hm).2.2.trans (hS' m' hm').2.2.symm)
  rw [← (hS m hm).2.1, ← (hS' m' hm').2.1, this.1]

/-- A proposal of the term of a candidate that is not (yet) leader does not exist. -/
theorem Inv.no_props_of_cand (I : Inv Q r) {c : N} (hc : Cand Q r c (r.term c))
    (hl : r.leader c = false) {i : ℕ} {v : V} : (i, r.term c, v) ∉ r.props := by
  intro hp
  obtain ⟨c', hc', hle, himp⟩ := I.props_leader _ _ _ hp
  have := I.cand_unique hc hc'
  subst this
  simp [(himp rfl).1] at hl

/-- Proposals of a leader's term are entries of its log. -/
theorem Inv.props_of_leader (I : Inv Q r) {c : N} (hl : r.leader c = true) {i : ℕ} {v : V}
    (hp : (i, r.term c, v) ∈ r.props) :
    lastTerm (r.log c) = r.term c ∧ ∃ h : i < (r.log c).length, (r.log c)[i].2 = v := by
  obtain ⟨c', hc', hle, himp⟩ := I.props_leader _ _ _ hp
  have := I.cand_unique (I.leader_cand c hl) hc'
  subst this
  exact (himp rfl).2

/-! ### The initial state -/

theorem inv_init : Inv Q (init : State N V) where
  entry_props L hL := by
    rcases hL with ⟨s, rfl⟩ | ⟨m, hm, -⟩ | ⟨m, hm, -⟩
    · simp [init]
    · simp [init] at hm
    · simp [init] at hm
  last_props L hL := by
    rcases hL with ⟨s, rfl⟩ | ⟨m, hm, -⟩ | ⟨m, hm, -⟩
    · simp [init]
    · simp [init] at hm
    · simp [init] at hm
  props_unique := by simp [init]
  props_leader := by simp [init]
  rvok_unique := by simp [init]
  rvok_term := by simp [init]
  rvok_vote := by simp [init]
  rv_ok := by simp [init]
  leader_cand := by simp [init]
  cand_log := by simp [init]
  ae_ok := by simp [init]
  commit_le := by simp [init]
  commit_ok := by simp [init]
  acks_props := by simp [init]
  self_acks := by simp [init]
  aeok_ok := by simp [init]
  lastTerm_le := by simp [init, lastTerm]
  log_matching L₁ L₂ h₁ h₂ := by
    rcases h₁ with ⟨s, rfl⟩ | ⟨m, hm, -⟩ | ⟨m, hm, -⟩
    · simp [init]
    · simp [init] at hm
    · simp [init] at hm


/-! ### `RequestVote` -/

theorem Inv.requestVote (I : Inv Q r) (s : N) :
    Inv Q { r with
        term := Function.update r.term s (r.term s + 1)
        leader := Function.update r.leader s false
        rv := insert ⟨s, r.term s + 1, (r.log s).length, lastTerm (r.log s)⟩ r.rv
        rvok := insert ⟨s, s, r.term s + 1, r.log s⟩ r.rvok } := by
  set r' : State N V := { r with
        term := Function.update r.term s (r.term s + 1)
        leader := Function.update r.leader s false
        rv := insert ⟨s, r.term s + 1, (r.log s).length, lastTerm (r.log s)⟩ r.rv
        rvok := insert ⟨s, s, r.term s + 1, r.log s⟩ r.rvok } with hr'
  have hlogs : ∀ L, InLogs r' L → InLogs r L := by
    rintro L (⟨a, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · rcases Set.mem_insert_iff.1 hm with rfl | hm
      · exact Or.inl ⟨s, rfl⟩
      · exact Or.inr (Or.inl ⟨m, hm, rfl⟩)
    · exact Or.inr (Or.inr ⟨m, hm, rfl⟩)
  have hsub : r.rvok ⊆ r'.rvok := Set.subset_insert _ _
  have hterm : ∀ a, r.term a ≤ r'.term a := by
    intro a; by_cases h : a = s
    · subst h; simp [hr']
    · simp [hr', Function.update_of_ne h]
  -- a new vote of `s` only for its new term; old votes have smaller terms
  have hold : ∀ m ∈ r.rvok, m.src = s → m.term < r.term s + 1 := fun m hm h =>
    Nat.lt_succ_of_le (h ▸ I.rvok_term m hm)
  have hcand : ∀ c t, c ≠ s → Cand Q r' c t → Cand Q r c t := by
    rintro c t hc ⟨S, hS, hQ⟩
    refine ⟨S, fun m hm => ⟨?_, (hS m hm).2⟩, hQ⟩
    rcases Set.mem_insert_iff.1 (hS m hm).1 with h | h
    · exact absurd ((hS m hm).2.1.symm.trans (by rw [h])) hc
    · exact h
  refine
    { entry_props := fun L hL => I.entry_props L (hlogs L hL)
      last_props := fun L hL => I.last_props L (hlogs L hL)
      props_unique := I.props_unique
      props_leader := ?_
      rvok_unique := ?_
      rvok_term := ?_
      rvok_vote := ?_
      rv_ok := ?_
      leader_cand := ?_
      cand_log := ?_
      ae_ok := ?_
      commit_le := I.commit_le
      commit_ok := ?_
      acks_props := ?_
      self_acks := I.self_acks
      aeok_ok := I.aeok_ok
      lastTerm_le := fun a => (I.lastTerm_le a).trans (hterm a)
      log_matching := fun L₁ L₂ h₁ h₂ => I.log_matching L₁ L₂ (hlogs L₁ h₁) (hlogs L₂ h₂) }
  · intro i t v hp
    obtain ⟨c, hc, hle, himp⟩ := I.props_leader i t v hp
    refine ⟨c, hc.mono hsub, hle.trans (hterm c), fun he => ?_⟩
    by_cases hcs : c = s
    · subst hcs; simp [hr'] at he; omega
    · simp only [hr', Function.update_of_ne hcs] at he ⊢
      exact himp he
  · intro m hm m' hm' hsrc hterm'
    rcases Set.mem_insert_iff.1 hm with rfl | hm <;>
      rcases Set.mem_insert_iff.1 hm' with rfl | hm'
    · exact ⟨rfl, rfl⟩
    · have := hold m' hm' hsrc.symm; simp at hterm'; omega
    · have := hold m hm hsrc; simp at hterm'; omega
    · exact I.rvok_unique m hm m' hm' hsrc hterm'
  · intro m hm
    rcases Set.mem_insert_iff.1 hm with rfl | hm
    · simp [hr']
    · exact (I.rvok_term m hm).trans (hterm _)
  · intro m hm
    rcases Set.mem_insert_iff.1 hm with rfl | hm
    · exact ⟨r.log s, Set.mem_insert _ _, le_rfl⟩
    · obtain ⟨L, hL, hle⟩ := I.rvok_vote m hm
      exact ⟨L, hsub hL, hle⟩
  · intro m hm
    rcases Set.mem_insert_iff.1 hm with rfl | hm
    · exact ⟨r.log s, Set.mem_insert _ _, rfl, rfl⟩
    · obtain ⟨L, hL, h1, h2⟩ := I.rv_ok m hm
      exact ⟨L, hsub hL, h1, h2⟩
  · intro c hc
    by_cases hcs : c = s
    · subst hcs; simp [hr'] at hc
    · simp only [hr', Function.update_of_ne hcs] at hc ⊢
      exact (I.leader_cand c hc).mono hsub
  · intro c L hL hl hne
    by_cases hcs : c = s
    · subst hcs
      simp only [hr', Function.update_self] at hL hne
      rcases Set.mem_insert_iff.1 hL with h | h
      · simp only [RVOKMsg.mk.injEq] at h; exact absurd h.2.2.2.symm hne
      · have := hold _ h rfl; simp at this
    · simp only [hr', Function.update_of_ne hcs] at hL hl hne ⊢
      rcases Set.mem_insert_iff.1 hL with h | h
      · simp only [RVOKMsg.mk.injEq] at h; exact absurd h.1 hcs
      · obtain ⟨c', hc', hcand'⟩ := I.cand_log c L h hl hne
        exact ⟨c', hc', hcand'.mono hsub⟩
  · intro m hm
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := I.ae_ok m hm
    exact ⟨h1.mono hsub, h2.trans (hterm _), h3, h4, h5, h6, h7⟩
  · intro a i hi h
    exact (I.commit_ok a i hi h).mono subset_rfl (hterm a)
  · intro a i t v h
    exact ⟨(I.acks_props a i t v h).1, (I.acks_props a i t v h).2.trans (hterm a)⟩


/-! ### `ReceiveVote` -/

theorem Inv.receiveVote (I : Inv Q r) (s : N) (m : RVMsg N) (hm : m ∈ r.rv)
    (ht : r.term s < m.term) (hv : lastTerm (r.log s) ≤ m.lterm) :
    Inv Q { r with
        term := Function.update r.term s m.term
        leader := Function.update r.leader s false
        rvok := insert ⟨s, m.cand, m.term, r.log s⟩ r.rvok } := by
  set r' : State N V := { r with
        term := Function.update r.term s m.term
        leader := Function.update r.leader s false
        rvok := insert ⟨s, m.cand, m.term, r.log s⟩ r.rvok } with hr'
  have hlogs : ∀ L, InLogs r' L → InLogs r L := by
    rintro L (⟨a, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · rcases Set.mem_insert_iff.1 hm with rfl | hm
      · exact Or.inl ⟨s, rfl⟩
      · exact Or.inr (Or.inl ⟨m, hm, rfl⟩)
    · exact Or.inr (Or.inr ⟨m, hm, rfl⟩)
  have hsub : r.rvok ⊆ r'.rvok := Set.subset_insert _ _
  have hterm : ∀ a, r.term a ≤ r'.term a := by
    intro a; by_cases h : a = s
    · subst h; simp [hr']; omega
    · simp [hr', Function.update_of_ne h]
  obtain ⟨Lc, hLc, hlen, hlt⟩ := I.rv_ok m hm
  have hcs : m.cand ≠ s := by
    rintro h
    have := I.rvok_term _ hLc
    simp only at this; rw [h] at this; omega
  have hold : ∀ m' ∈ r.rvok, m'.src = s → m'.term < m.term := fun m' hm' h =>
    lt_of_le_of_lt (h ▸ I.rvok_term m' hm') ht
  refine
    { entry_props := fun L hL => I.entry_props L (hlogs L hL)
      last_props := fun L hL => I.last_props L (hlogs L hL)
      props_unique := I.props_unique
      props_leader := ?_
      rvok_unique := ?_
      rvok_term := ?_
      rvok_vote := ?_
      rv_ok := ?_
      leader_cand := ?_
      cand_log := ?_
      ae_ok := ?_
      commit_le := I.commit_le
      commit_ok := ?_
      acks_props := ?_
      self_acks := I.self_acks
      aeok_ok := I.aeok_ok
      lastTerm_le := fun a => (I.lastTerm_le a).trans (hterm a)
      log_matching := fun L₁ L₂ h₁ h₂ => I.log_matching L₁ L₂ (hlogs L₁ h₁) (hlogs L₂ h₂) }
  · intro i t v hp
    obtain ⟨c, hc, hle, himp⟩ := I.props_leader i t v hp
    refine ⟨c, hc.mono hsub, hle.trans (hterm c), fun he => ?_⟩
    by_cases hc' : c = s
    · subst hc'; simp [hr'] at he; omega
    · simp only [hr', Function.update_of_ne hc'] at he ⊢
      exact himp he
  · intro m₁ hm₁ m₂ hm₂ hsrc hterm'
    rcases Set.mem_insert_iff.1 hm₁ with rfl | hm₁ <;>
      rcases Set.mem_insert_iff.1 hm₂ with rfl | hm₂
    · exact ⟨rfl, rfl⟩
    · have := hold m₂ hm₂ hsrc.symm; simp at hterm'; omega
    · have := hold m₁ hm₁ hsrc; simp at hterm'; omega
    · exact I.rvok_unique m₁ hm₁ m₂ hm₂ hsrc hterm'
  · intro m₁ hm₁
    rcases Set.mem_insert_iff.1 hm₁ with rfl | hm₁
    · simp [hr']
    · exact (I.rvok_term m₁ hm₁).trans (hterm _)
  · intro m₁ hm₁
    rcases Set.mem_insert_iff.1 hm₁ with rfl | hm₁
    · exact ⟨Lc, hsub hLc, hlt ▸ hv⟩
    · obtain ⟨L, hL, hle⟩ := I.rvok_vote m₁ hm₁
      exact ⟨L, hsub hL, hle⟩
  · intro m₁ hm₁
    obtain ⟨L, hL, h1, h2⟩ := I.rv_ok m₁ hm₁
    exact ⟨L, hsub hL, h1, h2⟩
  · intro c hc
    by_cases hc' : c = s
    · subst hc'; simp [hr'] at hc
    · simp only [hr', Function.update_of_ne hc'] at hc ⊢
      exact (I.leader_cand c hc).mono hsub
  · intro c L hL hl hne
    by_cases hc' : c = s
    · subst hc'
      simp only [hr', Function.update_self] at hL
      rcases Set.mem_insert_iff.1 hL with h | h
      · simp only [RVOKMsg.mk.injEq] at h; exact absurd h.2.1.symm hcs
      · have := hold _ h rfl; simp at this
    · simp only [hr', Function.update_of_ne hc'] at hL hl hne ⊢
      rcases Set.mem_insert_iff.1 hL with h | h
      · simp only [RVOKMsg.mk.injEq] at h; exact absurd h.1 hc'
      · obtain ⟨c', hc'', hcand'⟩ := I.cand_log c L h hl hne
        exact ⟨c', hc'', hcand'.mono hsub⟩
  · intro m₁ hm₁
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := I.ae_ok m₁ hm₁
    exact ⟨h1.mono hsub, h2.trans (hterm _), h3, h4, h5, h6, h7⟩
  · intro a i hi h
    exact (I.commit_ok a i hi h).mono subset_rfl (hterm a)
  · intro a i t v h
    exact ⟨(I.acks_props a i t v h).1, (I.acks_props a i t v h).2.trans (hterm a)⟩


/-! ### `BecomeLeader` -/

theorem Inv.cand_of_votes (S : Finset (RVOKMsg N V)) {s : N}
    (hS : ∀ m ∈ S, m ∈ r.rvok ∧ m.dst = s ∧ m.term = r.term s)
    (hQ : Q.IsQuorum (S.image RVOKMsg.src)) : Cand Q r s (r.term s) := ⟨S, hS, hQ⟩

theorem Inv.becomeLeader_nil (I : Inv Q r) (s : N) (hl : r.leader s = false)
    (hc : Cand Q r s (r.term s)) :
    Inv Q { r with leader := Function.update r.leader s true } := by
  set r' : State N V := { r with leader := Function.update r.leader s true } with hr'
  have hlogs : ∀ L, InLogs r' L → InLogs r L := fun L h => h
  refine
    { entry_props := I.entry_props
      last_props := I.last_props
      props_unique := I.props_unique
      props_leader := ?_
      rvok_unique := I.rvok_unique
      rvok_term := I.rvok_term
      rvok_vote := I.rvok_vote
      rv_ok := I.rv_ok
      leader_cand := ?_
      cand_log := ?_
      ae_ok := I.ae_ok
      commit_le := I.commit_le
      commit_ok := I.commit_ok
      acks_props := I.acks_props
      self_acks := I.self_acks
      aeok_ok := I.aeok_ok
      lastTerm_le := I.lastTerm_le
      log_matching := I.log_matching }
  · intro i t v hp
    obtain ⟨c, hc', hle, himp⟩ := I.props_leader i t v hp
    refine ⟨c, hc', hle, fun he => ?_⟩
    by_cases hcs : c = s
    · subst hcs; simp [(himp he).1] at hl
    · simp only [hr', Function.update_of_ne hcs]; exact himp he
  · intro c hc'
    by_cases hcs : c = s
    · subst hcs; exact hc
    · simp only [hr', Function.update_of_ne hcs] at hc'; exact I.leader_cand c hc'
  · intro c L hL hl' hne
    by_cases hcs : c = s
    · subst hcs; simp [hr'] at hl'
    · simp only [hr', Function.update_of_ne hcs] at hl'; exact I.cand_log c L hL hl' hne

theorem Inv.becomeLeader_cons (I : Inv Q r) (s : N) (ext : List V) (he : ext ≠ [])
    (hl : r.leader s = false) (hc : Cand Q r s (r.term s)) :
    Inv Q { r with
        leader := Function.update r.leader s true
        log := Function.update r.log s (r.log s ++ ext.map (fun v => (r.term s, v)))
        props := r.props ∪ propsOf (r.log s ++ ext.map (fun v => (r.term s, v))) (r.term s)
        acks := r.acks ∪ acksOf s (r.log s ++ ext.map (fun v => (r.term s, v))) (r.term s) } := by
  set t := r.term s with ht
  set L' := r.log s ++ ext.map (fun v => (t, v)) with hL'
  set r' : State N V := { r with
        leader := Function.update r.leader s true
        log := Function.update r.log s L'
        props := r.props ∪ propsOf L' t
        acks := r.acks ∪ acksOf s L' t } with hr'
  have hnp : ∀ i (v : V), (i, t, v) ∉ r.props := fun i v => I.no_props_of_cand hc hl
  have hLt : lastTerm L' = t := lastTerm_append_map t he
  have hlen : (r.log s).length ≤ L'.length := by simp [hL']
  have hfst : ∀ i (h : i < L'.length), (r.log s).length ≤ i → L'[i].1 = t := by
    intro i h hi
    simp only [hL', List.getElem_append_right hi, List.getElem_map]
  have hleft : ∀ i (h : i < (r.log s).length), L'[i]'(lt_of_lt_of_le h hlen) = (r.log s)[i] := by
    intro i h; simp only [hL', List.getElem_append_left h]
  have hlogs : ∀ L, InLogs r' L → InLogs r L ∨ L = L' := by
    rintro L (⟨a, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
    · by_cases has : a = s
      · subst has; right; simp [hr']
      · left; exact Or.inl ⟨a, by simp [hr', Function.update_of_ne has]⟩
    · exact Or.inl (Or.inr (Or.inl ⟨m, hm, rfl⟩))
    · exact Or.inl (Or.inr (Or.inr ⟨m, hm, rfl⟩))
  have hps : r.props ⊆ r'.props := Set.subset_union_left
  have has : r.acks ⊆ r'.acks := Set.subset_union_left
  have hnew : ∀ i (h : i < L'.length), (i, t, L'[i].2) ∈ r'.props :=
    fun i h => Or.inr ⟨i, h, rfl⟩
  have hLM : ∀ L₂, InLogs r L₂ → ∀ i (h₁ : i < L'.length) (h₂ : i < L₂.length),
      L'[i].1 = L₂[i].1 → L'.take (i + 1) = L₂.take (i + 1) := by
    intro L₂ hL₂ i h₁ h₂ heq
    by_cases hi : i < (r.log s).length
    · rw [hleft i hi] at heq
      rw [hL', List.take_append_of_le_length (by omega)]
      exact I.log_matching _ _ (Or.inl ⟨s, rfl⟩) hL₂ i hi h₂ heq
    · rw [hfst i h₁ (by omega)] at heq
      have := I.entry_props L₂ hL₂ i h₂
      rw [← heq] at this
      exact absurd this (hnp _ _)
  refine
    { entry_props := ?_
      last_props := ?_
      props_unique := ?_
      props_leader := ?_
      rvok_unique := I.rvok_unique
      rvok_term := I.rvok_term
      rvok_vote := I.rvok_vote
      rv_ok := I.rv_ok
      leader_cand := ?_
      cand_log := ?_
      ae_ok := ?_
      commit_le := ?_
      commit_ok := ?_
      acks_props := ?_
      self_acks := ?_
      aeok_ok := ?_
      lastTerm_le := ?_
      log_matching := ?_ }
  · intro L hL i h
    rcases hlogs L hL with hL | rfl
    · exact hps (I.entry_props L hL i h)
    · by_cases hi : i < (r.log s).length
      · have := I.entry_props _ (Or.inl ⟨s, rfl⟩) i hi
        rw [← hleft i hi] at this; exact hps this
      · rw [hfst i h (by omega)]; exact hnew i h
  · intro L hL i h
    rcases hlogs L hL with hL | rfl
    · exact hps (I.last_props L hL i h)
    · rw [hLt]; exact hnew i h
  · intro i t₀ v w hv hw
    rcases hv with hv | ⟨j, hj, hjv⟩ <;> rcases hw with hw | ⟨k, hk, hkw⟩
    · exact I.props_unique i t₀ v w hv hw
    · simp only [Prod.mk.injEq] at hkw; obtain ⟨rfl, rfl, rfl⟩ := hkw; exact absurd hv (hnp _ _)
    · simp only [Prod.mk.injEq] at hjv; obtain ⟨rfl, rfl, rfl⟩ := hjv; exact absurd hw (hnp _ _)
    · simp only [Prod.mk.injEq] at hjv hkw
      obtain ⟨rfl, rfl, rfl⟩ := hjv; obtain ⟨rfl, -, rfl⟩ := hkw; rfl
  · intro i t₀ v hp
    rcases hp with hp | ⟨j, hj, hjv⟩
    · obtain ⟨c, hc', hle, himp⟩ := I.props_leader i t₀ v hp
      refine ⟨c, hc', hle, fun he' => ?_⟩
      by_cases hcs : c = s
      · subst hcs; simp [(himp he').1] at hl
      · simp only [hr', Function.update_of_ne hcs]; exact himp he'
    · simp only [Prod.mk.injEq] at hjv; obtain ⟨rfl, rfl, rfl⟩ := hjv
      refine ⟨s, hc, le_rfl, fun _ => ⟨by simp [hr'], by simp [hr', hLt], ?_⟩⟩
      simp only [hr', Function.update_self]
      exact ⟨hj, trivial⟩
  · intro c hc'
    by_cases hcs : c = s
    · subst hcs; exact hc
    · simp only [hr', Function.update_of_ne hcs] at hc'; exact I.leader_cand c hc'
  · intro c L hL hl' hne
    by_cases hcs : c = s
    · subst hcs; simp [hr'] at hl'
    · simp only [hr', Function.update_of_ne hcs] at hl' hne; exact I.cand_log c L hL hl' hne
  · intro m hm
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := I.ae_ok m hm
    exact ⟨h1, h2, h3, h4, h5, h6, fun i hi h => (h7 i hi h).mono has le_rfl⟩
  · intro a
    by_cases has : a = s
    · subst has; simp only [hr', Function.update_self]; exact (I.commit_le a).trans hlen
    · simp only [hr', Function.update_of_ne has]; exact I.commit_le a
  · intro a i hi h
    by_cases has' : a = s
    · subst has'
      simp only [hr', Function.update_self] at h ⊢
      have hi' : i < (r.log a).length := lt_of_lt_of_le hi (I.commit_le a)
      rw [hleft i hi']
      exact (I.commit_ok a i hi hi').mono has le_rfl
    · simp only [hr', Function.update_of_ne has'] at h ⊢
      exact (I.commit_ok a i hi h).mono has le_rfl
  · intro a i t₀ v h
    rcases h with h | ⟨j, hj, hjv⟩
    · exact ⟨hps (I.acks_props a i t₀ v h).1, (I.acks_props a i t₀ v h).2⟩
    · simp only [Prod.mk.injEq] at hjv; obtain ⟨rfl, rfl, rfl, rfl⟩ := hjv
      exact ⟨hnew _ hj, le_rfl⟩
  · intro a i h
    by_cases has' : a = s
    · subst has'
      simp only [hr', Function.update_self] at h ⊢
      rw [hLt]; exact Or.inr ⟨i, h, rfl⟩
    · simp only [hr', Function.update_of_ne has'] at h ⊢
      exact has (I.self_acks a i h)
  · intro m hm i hi
    obtain ⟨v, hv⟩ := I.aeok_ok m hm i hi
    exact ⟨v, has hv⟩
  · intro a
    by_cases has' : a = s
    · subst has'; simp only [hr', Function.update_self]; rw [hLt]
    · simp only [hr', Function.update_of_ne has']; exact I.lastTerm_le a
  · intro L₁ L₂ h₁ h₂ i hi₁ hi₂ heq
    rcases hlogs L₁ h₁ with h₁ | rfl <;> rcases hlogs L₂ h₂ with h₂ | rfl
    · exact I.log_matching L₁ L₂ h₁ h₂ i hi₁ hi₂ heq
    · exact (hLM L₁ h₁ i hi₂ hi₁ heq.symm).symm
    · exact hLM L₂ h₂ i hi₁ hi₂ heq
    · rfl


/-! ### `AppendEntries` -/

theorem Inv.appendEntries (I : Inv Q r) (s : N) (vals : List V) (prevLen : ℕ)
    (hl : r.leader s = true) (hvals : vals ≠ []) (hprev : prevLen ≤ (r.log s).length) :
    Inv Q { r with
        log := Function.update r.log s (r.log s ++ vals.map (fun v => (r.term s, v)))
        ae := insert ⟨s, r.term s, prevLen, r.log s ++ vals.map (fun v => (r.term s, v)),
          r.commit s⟩ r.ae
        props := r.props ∪ propsOf (r.log s ++ vals.map (fun v => (r.term s, v))) (r.term s)
        acks := r.acks ∪ acksOf s (r.log s ++ vals.map (fun v => (r.term s, v))) (r.term s) } := by
  set t := r.term s with ht
  set L' := r.log s ++ vals.map (fun v => (t, v)) with hL'
  set r' : State N V := { r with
        log := Function.update r.log s L'
        ae := insert ⟨s, t, prevLen, L', r.commit s⟩ r.ae
        props := r.props ∪ propsOf L' t
        acks := r.acks ∪ acksOf s L' t } with hr'
  have hc : Cand Q r s t := I.leader_cand s hl
  have hpl : ∀ i (w : V), (i, t, w) ∈ r.props →
      lastTerm (r.log s) = t ∧ ∃ h : i < (r.log s).length, (r.log s)[i].2 = w :=
    fun i w hp => I.props_of_leader hl hp
  have hLt : lastTerm L' = t := lastTerm_append_map t hvals
  have hlen : (r.log s).length ≤ L'.length := by simp [hL']
  have hfst : ∀ i (h : i < L'.length), (r.log s).length ≤ i → L'[i].1 = t := by
    intro i h hi
    simp only [hL', List.getElem_append_right hi, List.getElem_map]
  have hleft : ∀ i (h : i < (r.log s).length), L'[i]'(lt_of_lt_of_le h hlen) = (r.log s)[i] := by
    intro i h; simp only [hL', List.getElem_append_left h]
  have hlogs : ∀ L, InLogs r' L → InLogs r L ∨ L = L' := by
    rintro L (⟨a, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
    · by_cases has : a = s
      · subst has; right; simp [hr']
      · left; exact Or.inl ⟨a, by simp [hr', Function.update_of_ne has]⟩
    · exact Or.inl (Or.inr (Or.inl ⟨m, hm, rfl⟩))
    · rcases Set.mem_insert_iff.1 hm with rfl | hm
      · exact Or.inr rfl
      · exact Or.inl (Or.inr (Or.inr ⟨m, hm, rfl⟩))
  have hps : r.props ⊆ r'.props := Set.subset_union_left
  have has : r.acks ⊆ r'.acks := Set.subset_union_left
  have hnew : ∀ i (h : i < L'.length), (i, t, L'[i].2) ∈ r'.props :=
    fun i h => Or.inr ⟨i, h, rfl⟩
  have hLM : ∀ L₂, InLogs r L₂ → ∀ i (h₁ : i < L'.length) (h₂ : i < L₂.length),
      L'[i].1 = L₂[i].1 → L'.take (i + 1) = L₂.take (i + 1) := by
    intro L₂ hL₂ i h₁ h₂ heq
    by_cases hi : i < (r.log s).length
    · rw [hleft i hi] at heq
      rw [hL', List.take_append_of_le_length (by omega)]
      exact I.log_matching _ _ (Or.inl ⟨s, rfl⟩) hL₂ i hi h₂ heq
    · rw [hfst i h₁ (by omega)] at heq
      have := I.entry_props L₂ hL₂ i h₂
      rw [← heq] at this
      obtain ⟨-, hi', -⟩ := hpl _ _ this
      exact absurd hi' hi
  refine
    { entry_props := ?_
      last_props := ?_
      props_unique := ?_
      props_leader := ?_
      rvok_unique := I.rvok_unique
      rvok_term := I.rvok_term
      rvok_vote := I.rvok_vote
      rv_ok := I.rv_ok
      leader_cand := I.leader_cand
      cand_log := ?_
      ae_ok := ?_
      commit_le := ?_
      commit_ok := ?_
      acks_props := ?_
      self_acks := ?_
      aeok_ok := ?_
      lastTerm_le := ?_
      log_matching := ?_ }
  · intro L hL i h
    rcases hlogs L hL with hL | rfl
    · exact hps (I.entry_props L hL i h)
    · by_cases hi : i < (r.log s).length
      · have := I.entry_props _ (Or.inl ⟨s, rfl⟩) i hi
        rw [← hleft i hi] at this; exact hps this
      · rw [hfst i h (by omega)]; exact hnew i h
  · intro L hL i h
    rcases hlogs L hL with hL | rfl
    · exact hps (I.last_props L hL i h)
    · rw [hLt]; exact hnew i h
  · intro i t₀ v w hv hw
    rcases hv with hv | ⟨j, hj, hjv⟩ <;> rcases hw with hw | ⟨k, hk, hkw⟩
    · exact I.props_unique i t₀ v w hv hw
    · simp only [Prod.mk.injEq] at hkw; obtain ⟨rfl, rfl, rfl⟩ := hkw
      obtain ⟨-, hi, hiv⟩ := hpl _ _ hv
      rw [← hiv, ← hleft _ hi]
    · simp only [Prod.mk.injEq] at hjv; obtain ⟨rfl, rfl, rfl⟩ := hjv
      obtain ⟨-, hi, hiv⟩ := hpl _ _ hw
      rw [← hiv, ← hleft _ hi]
    · simp only [Prod.mk.injEq] at hjv hkw
      obtain ⟨rfl, rfl, rfl⟩ := hjv; obtain ⟨rfl, -, rfl⟩ := hkw; rfl
  · intro i t₀ v hp
    rcases hp with hp | ⟨j, hj, hjv⟩
    · obtain ⟨c, hc', hle, himp⟩ := I.props_leader i t₀ v hp
      refine ⟨c, hc', hle, fun he' => ?_⟩
      by_cases hcs : c = s
      · subst hcs
        obtain ⟨h1, h2, hi, hiv⟩ := himp he'
        simp only [hr', Function.update_self]
        refine ⟨h1, hLt.trans he', lt_of_lt_of_le hi hlen, ?_⟩
        rw [hleft i hi]; exact hiv
      · simp only [hr', Function.update_of_ne hcs]; exact himp he'
    · simp only [Prod.mk.injEq] at hjv; obtain ⟨rfl, rfl, rfl⟩ := hjv
      refine ⟨s, hc, le_rfl, fun _ => ⟨hl, by simp [hr', hLt], ?_⟩⟩
      simp only [hr', Function.update_self]
      exact ⟨hj, trivial⟩
  · intro c L hL hl' hne
    by_cases hcs : c = s
    · subst hcs; exact absurd (hl.symm.trans hl') (by decide)
    · simp only [hr', Function.update_of_ne hcs] at hne; exact I.cand_log c L hL hl' hne
  · intro m hm
    rcases Set.mem_insert_iff.1 hm with rfl | hm
    · refine ⟨hc, le_rfl, ?_, hLt, hprev.trans hlen, (I.commit_le s).trans hlen, ?_⟩
      · simp [hL', hvals]
      · intro i hi h
        have hi' : i < (r.log s).length := lt_of_lt_of_le hi (I.commit_le s)
        simp only
        rw [hleft i hi']
        exact (I.commit_ok s i hi hi').mono has le_rfl
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := I.ae_ok m hm
      exact ⟨h1, h2, h3, h4, h5, h6, fun i hi h => (h7 i hi h).mono has le_rfl⟩
  · intro a
    by_cases has' : a = s
    · subst has'; simp only [hr', Function.update_self]; exact (I.commit_le a).trans hlen
    · simp only [hr', Function.update_of_ne has']; exact I.commit_le a
  · intro a i hi h
    by_cases has' : a = s
    · subst has'
      simp only [hr', Function.update_self] at h ⊢
      have hi' : i < (r.log a).length := lt_of_lt_of_le hi (I.commit_le a)
      rw [hleft i hi']
      exact (I.commit_ok a i hi hi').mono has le_rfl
    · simp only [hr', Function.update_of_ne has'] at h ⊢
      exact (I.commit_ok a i hi h).mono has le_rfl
  · intro a i t₀ v h
    rcases h with h | ⟨j, hj, hjv⟩
    · exact ⟨hps (I.acks_props a i t₀ v h).1, (I.acks_props a i t₀ v h).2⟩
    · simp only [Prod.mk.injEq] at hjv; obtain ⟨rfl, rfl, rfl, rfl⟩ := hjv
      exact ⟨hnew _ hj, le_rfl⟩
  · intro a i h
    by_cases has' : a = s
    · subst has'
      simp only [hr', Function.update_self] at h ⊢
      rw [hLt]; exact Or.inr ⟨i, h, rfl⟩
    · simp only [hr', Function.update_of_ne has'] at h ⊢
      exact has (I.self_acks a i h)
  · intro m hm i hi
    obtain ⟨v, hv⟩ := I.aeok_ok m hm i hi
    exact ⟨v, has hv⟩
  · intro a
    by_cases has' : a = s
    · subst has'; simp only [hr', Function.update_self]; rw [hLt]
    · simp only [hr', Function.update_of_ne has']; exact I.lastTerm_le a
  · intro L₁ L₂ h₁ h₂ i hi₁ hi₂ heq
    rcases hlogs L₁ h₁ with h₁ | rfl <;> rcases hlogs L₂ h₂ with h₂ | rfl
    · exact I.log_matching L₁ L₂ h₁ h₂ i hi₁ hi₂ heq
    · exact (hLM L₁ h₁ i hi₂ hi₁ heq.symm).symm
    · exact hLM L₂ h₂ i hi₁ hi₂ heq
    · rfl


/-! ### `ReceiveAppend` -/

/-- By log matching, the follower's new log is exactly the leader's log carried by the message. -/
theorem Inv.receiveAppend_log (I : Inv Q r) (s : N) (m : AEMsg N V) (hm : m ∈ r.ae)
    (hprev : m.prevLen ≤ (r.log s).length) (hmatch : PrevMatch (r.log s) m) :
    (r.log s).take m.prevLen ++ m.full.drop m.prevLen = m.full := by
  by_cases h0 : m.prevLen = 0
  · simp [h0]
  rcases hmatch with h0' | ⟨e, he, e', he', heq⟩
  · exact absurd h0' h0
  · have hp1 : m.prevLen - 1 < (r.log s).length := by omega
    have hp2 : m.prevLen - 1 < m.full.length := by
      rcases Nat.lt_or_ge (m.prevLen - 1) m.full.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at he'
    rw [List.getElem?_eq_getElem hp1, Option.mem_def, Option.some_inj] at he
    rw [List.getElem?_eq_getElem hp2, Option.mem_def, Option.some_inj] at he'
    subst he he'
    have := I.log_matching _ _ (Or.inl ⟨s, rfl⟩) (Or.inr (Or.inr ⟨m, hm, rfl⟩)) _ hp1 hp2 heq
    rw [Nat.sub_add_cancel (by omega)] at this
    rw [this, List.take_append_drop]

theorem Inv.receiveAppend' (I : Inv Q r) (hsafe : PropSafe Q r) (s : N) (m : AEMsg N V)
    (hm : m ∈ r.ae) (ht : r.term s ≤ m.term) (hlen : (r.log s).length ≤ m.full.length) :
    Inv Q { r with
        term := Function.update r.term s m.term
        leader := Function.update r.leader s (if r.term s < m.term then false else r.leader s)
        log := Function.update r.log s m.full
        commit := Function.update r.commit s (max m.commit (r.commit s))
        aeok := insert ⟨s, m.src, m.term, m.full.length⟩ r.aeok
        acks := r.acks ∪ acksOf s m.full m.term } := by
  set t := m.term with ht'
  set F := m.full with hF
  set r' : State N V := { r with
        term := Function.update r.term s t
        leader := Function.update r.leader s (if r.term s < t then false else r.leader s)
        log := Function.update r.log s F
        commit := Function.update r.commit s (max m.commit (r.commit s))
        aeok := insert ⟨s, m.src, t, F.length⟩ r.aeok
        acks := r.acks ∪ acksOf s F t } with hr'
  obtain ⟨hcand, hsrc, hFne, hFt, hpF, hcF, hcm⟩ := I.ae_ok m hm
  have hFin : InLogs r F := Or.inr (Or.inr ⟨m, hm, rfl⟩)
  have hlogs : ∀ L, InLogs r' L → InLogs r L := by
    rintro L (⟨a, rfl⟩ | ⟨m', hm', rfl⟩ | ⟨m', hm', rfl⟩)
    · by_cases has : a = s
      · subst has; simpa [hr'] using hFin
      · exact Or.inl ⟨a, by simp [hr', Function.update_of_ne has]⟩
    · exact Or.inr (Or.inl ⟨m', hm', rfl⟩)
    · exact Or.inr (Or.inr ⟨m', hm', rfl⟩)
  have has : r.acks ⊆ r'.acks := Set.subset_union_left
  have hterm : ∀ a, r.term a ≤ r'.term a := by
    intro a; by_cases h : a = s
    · subst h; simp [hr']; omega
    · simp [hr', Function.update_of_ne h]
  have hFp : ∀ i (h : i < F.length), (i, t, F[i].2) ∈ r.props := fun i h => by
    have := I.last_props F hFin i h; rwa [hFt] at this
  refine
    { entry_props := fun L hL => I.entry_props L (hlogs L hL)
      last_props := fun L hL => I.last_props L (hlogs L hL)
      props_unique := I.props_unique
      props_leader := ?_
      rvok_unique := I.rvok_unique
      rvok_term := fun m' hm' => (I.rvok_term m' hm').trans (hterm _)
      rvok_vote := I.rvok_vote
      rv_ok := I.rv_ok
      leader_cand := ?_
      cand_log := ?_
      ae_ok := ?_
      commit_le := ?_
      commit_ok := ?_
      acks_props := ?_
      self_acks := ?_
      aeok_ok := ?_
      lastTerm_le := ?_
      log_matching := fun L₁ L₂ h₁ h₂ => I.log_matching L₁ L₂ (hlogs L₁ h₁) (hlogs L₂ h₂) }
  · intro i t₀ v hp
    obtain ⟨c, hc, hle, himp⟩ := I.props_leader i t₀ v hp
    refine ⟨c, hc, hle.trans (hterm c), fun he => ?_⟩
    by_cases hcs : c = s
    · subst hcs
      simp only [hr', Function.update_self] at he ⊢
      have hts : r.term c = t := by omega
      obtain ⟨h1, -, hi, hiv⟩ := himp (hts.trans he)
      refine ⟨by simp [hts, h1], hFt.trans he, lt_of_lt_of_le hi hlen, ?_⟩
      exact I.props_unique _ _ _ _ (hFp i _) (he ▸ hp)
    · simp only [hr', Function.update_of_ne hcs] at he ⊢; exact himp he
  · intro c hc
    by_cases hcs : c = s
    · subst hcs
      simp only [hr', Function.update_self] at hc ⊢
      split_ifs at hc with h
      have hts : r.term c = t := by omega
      rw [← hts]; exact I.leader_cand c hc
    · simp only [hr', Function.update_of_ne hcs] at hc ⊢; exact I.leader_cand c hc
  · intro c L hL hl' hne
    by_cases hcs : c = s
    · subst hcs
      simp only [hr', Function.update_self] at hL hl' hne ⊢
      have hts : r.term c = t := by
        have := I.rvok_term _ hL; simp only at this; omega
      rw [if_neg (by omega)] at hl'
      refine ⟨m.src, ?_, hcand⟩
      rintro hsc
      have h0 : 0 < F.length := List.length_pos_of_ne_nil hFne
      obtain ⟨c'', hc'', -, himp⟩ := I.props_leader _ _ _ (hFp 0 h0)
      have := I.cand_unique hcand hc''
      rw [hsc] at this; subst this
      have := (himp hts).1
      simp [this] at hl'
    · simp only [hr', Function.update_of_ne hcs] at hL hl' hne ⊢
      exact I.cand_log c L hL hl' hne
  · intro m' hm'
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := I.ae_ok m' hm'
    exact ⟨h1, h2.trans (hterm _), h3, h4, h5, h6, fun i hi h => (h7 i hi h).mono has le_rfl⟩
  · intro a
    by_cases has' : a = s
    · subst has'; simp only [hr', Function.update_self]
      exact max_le hcF ((I.commit_le a).trans hlen)
    · simp only [hr', Function.update_of_ne has']; exact I.commit_le a
  · intro a i hi h
    by_cases has' : a = s
    · subst has'
      simp only [hr', Function.update_self] at hi h ⊢
      rcases lt_max_iff.1 hi with hi | hi
      · exact (hcm i hi h).mono has le_rfl
      · have hi' : i < (r.log a).length := lt_of_lt_of_le hi (I.commit_le a)
        obtain ⟨b, hb, A, hA, hA'⟩ := I.commit_ok a i hi hi'
        have heq := hsafe i b t _ _ ⟨A, hA, hA'⟩ (hFp i h) (hb.trans ht)
        rw [heq]
        exact (I.commit_ok a i hi hi').mono has ht
    · simp only [hr', Function.update_of_ne has'] at hi h ⊢
      exact (I.commit_ok a i hi h).mono has le_rfl
  · intro a i t₀ v h
    rcases h with h | ⟨j, hj, hjv⟩
    · exact ⟨(I.acks_props a i t₀ v h).1, (I.acks_props a i t₀ v h).2.trans (hterm a)⟩
    · simp only [Prod.mk.injEq] at hjv; obtain ⟨rfl, rfl, rfl, rfl⟩ := hjv
      exact ⟨hFp _ hj, by simp [hr']⟩
  · intro a i h
    by_cases has' : a = s
    · subst has'
      simp only [hr', Function.update_self] at h ⊢
      rw [hFt]; exact Or.inr ⟨i, h, rfl⟩
    · simp only [hr', Function.update_of_ne has'] at h ⊢
      exact has (I.self_acks a i h)
  · intro m' hm' i hi
    rcases Set.mem_insert_iff.1 hm' with rfl | hm'
    · exact ⟨_, Or.inr ⟨i, hi, rfl⟩⟩
    · obtain ⟨v, hv⟩ := I.aeok_ok m' hm' i hi
      exact ⟨v, has hv⟩
  · intro a
    by_cases has' : a = s
    · subst has'; simp only [hr', Function.update_self]; rw [hFt]
    · simp only [hr', Function.update_of_ne has']; exact I.lastTerm_le a


/-! ### `LeaderLearn` -/

/-- The entries below `k` of a leader's log were accepted by the quorum of `LeaderLearn`, in the
ballot of the leader's last term. -/
theorem Inv.leaderLearn_acks (I : Inv Q r) (s : N) (S : Finset (AEOKMsg N)) (k : ℕ)
    (hl : r.leader s = true)
    (hS : ∀ m ∈ S, m ∈ r.aeok ∧ m.dst = s ∧ m.term = r.term s)
    (hk : ∀ m ∈ S, k ≤ m.len) :
    ∀ i (h : i < (r.log s).length), i < k → ∀ a ∈ insert s (S.image AEOKMsg.src),
      (a, i, lastTerm (r.log s), (r.log s)[i].2) ∈ r.acks := by
  intro i h hik a ha
  rcases Finset.mem_insert.1 ha with rfl | ha
  · exact I.self_acks a i h
  · obtain ⟨mm, hmm, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨v, hv⟩ := I.aeok_ok mm (hS mm hmm).1 i (lt_of_lt_of_le hik (hk mm hmm))
    rw [(hS mm hmm).2.2] at hv
    obtain ⟨hlt, _, hiv⟩ := I.props_of_leader hl (I.acks_props _ _ _ _ hv).1
    rw [hlt, hiv]; exact hv

theorem Inv.leaderLearn (I : Inv Q r) (s : N) (S : Finset (AEOKMsg N)) (k : ℕ)
    (hl : r.leader s = true)
    (hS : ∀ m ∈ S, m ∈ r.aeok ∧ m.dst = s ∧ m.term = r.term s)
    (hQ : Q.IsQuorum (insert s (S.image AEOKMsg.src)))
    (hk : ∀ m ∈ S, k ≤ m.len) (hkl : k ≤ (r.log s).length) :
    Inv Q { r with commit := Function.update r.commit s (max (r.commit s) k) } := by
  set r' : State N V := { r with commit := Function.update r.commit s (max (r.commit s) k) }
    with hr'
  have hacks := I.leaderLearn_acks s S k hl hS hk
  refine
    { entry_props := I.entry_props
      last_props := I.last_props
      props_unique := I.props_unique
      props_leader := I.props_leader
      rvok_unique := I.rvok_unique
      rvok_term := I.rvok_term
      rvok_vote := I.rvok_vote
      rv_ok := I.rv_ok
      leader_cand := I.leader_cand
      cand_log := I.cand_log
      ae_ok := I.ae_ok
      commit_le := ?_
      commit_ok := ?_
      acks_props := I.acks_props
      self_acks := I.self_acks
      aeok_ok := I.aeok_ok
      lastTerm_le := I.lastTerm_le
      log_matching := I.log_matching }
  · intro a
    by_cases has : a = s
    · subst has; simp only [hr', Function.update_self]; exact max_le (I.commit_le a) hkl
    · simp only [hr', Function.update_of_ne has]; exact I.commit_le a
  · intro a i hi h
    by_cases has : a = s
    · subst has
      simp only [hr', Function.update_self] at hi h ⊢
      rcases lt_max_iff.1 hi with hi | hi
      · exact I.commit_ok a i hi h
      · exact ⟨_, I.lastTerm_le a, _, hQ, hacks i h hi⟩
    · simp only [hr', Function.update_of_ne has] at hi h ⊢
      exact I.commit_ok a i hi h

/-! ### All steps -/

/-- `Inv` is preserved by every step of Raft* under rules with a monotone vote rule and without
heartbeats, provided the Paxos fact `PropSafe` holds (it is supplied by MultiPaxos safety). -/
theorem Inv.step {R : Rules V} (hR : VoteMono R) (hhb : ¬ R.heartbeat) (I : Inv Q r)
    (hsafe : PropSafe Q r) (h : Step Q R r r') : Inv Q r' := by
  cases h with
  | requestVote s => exact I.requestVote s
  | receiveVote s m hm ht hv => exact I.receiveVote s m hm ht (hR _ _ _ hv)
  | becomeLeader s S ext hl hS hself hQ hext =>
    rcases eq_or_ne ext [] with rfl | he
    · simpa using I.becomeLeader_nil s hl ⟨S, hS, hQ⟩
    · simp only [if_neg he]
      exact I.becomeLeader_cons s ext he hl ⟨S, hS, hQ⟩
  | appendEntries s vals prevLen hl hvals hprev =>
    exact I.appendEntries s vals prevLen hl (hvals.resolve_right hhb) hprev
  | receiveAppend s m hm ht hprev hmatch hlen =>
    rw [I.receiveAppend_log s m hm hprev hmatch]
    exact I.receiveAppend' hsafe s m hm ht hlen
  | leaderLearn s S k hl hS hQ hk hkl => exact I.leaderLearn s S k hl hS hQ hk hkl

end Podc.PaxosRaftRefinement.Raft
