import Papers.PODC2019.PaxosRaftRefinement.RaftInv
import Papers.PODC2019.PaxosRaftRefinement.PaxosBatch
import Papers.PODC2019.PaxosRaftRefinement.PaxosSafety

/-!
# Raft* refines MultiPaxos (Appendix C of [paper])

The refinement mapping of Appendix C:

| Paxos | Raft* |
|---|---|
| `ballot` | `currentTerm` |
| `phase1Succeeded` | `isLeader` |
| `instance i` = `(accBallot, value)` | `(lastLogEntry.term, log[i].value)` |
| `chosenSet` | `log[0, commitIndex]` |
| `prepare` / `prepareOK` | `requestVote` / `requestVoteOK` |
| `accept` / `acceptOK` | (implicit and explicit) `append` / `appendOK` (ghosts `props`, `acks`) |

Every step of (repaired) Raft* maps to a finite sequence of MultiPaxos steps
(`RequestVote` ↦ `Phase1a`, `ReceiveVote` ↦ `Phase1b`, `BecomeLeader` ↦ `Phase1Succeed` followed,
if new entries are adopted, by `Phase2a` and `Phase2b` for every entry; `AppendEntries` ↦
`Phase2a` + `Phase2b` for every entry; `ReceiveAppend` ↦ `Phase2b` for every entry + `Learn` for
the committed ones; `LeaderLearn` ↦ `Learn`), so the image of every reachable Raft* state is a
reachable MultiPaxos state (`refinement`), and Raft*'s state machine safety follows from MultiPaxos
safety (`raftStar_commitSafe`).

The accepted ballot of *every* entry is the term of the *last* entry (as in Appendix C), not the
per-entry `bal` field of Figure 2/Figure 3.
-/

namespace Podc.PaxosRaftRefinement

open Raft

variable {N V : Type*} [DecidableEq N] {Q : QuorumSystem N}

/-- Paxos view of a Raft* log: every entry carries the last term as its accepted ballot. -/
def absLog (L : List (ℕ × V)) : ℕ → Option (ℕ × V) :=
  fun i => L[i]?.map fun e => (lastTerm L, e.2)

/-- Paxos view of a committed prefix: `chosenSet = log[0, commitIndex]`. -/
def chosenOf (L : List (ℕ × V)) (c : ℕ) : Set (ℕ × V) :=
  {x | ∃ h : x.1 < L.length, x.1 < c ∧ L[x.1].2 = x.2}

/-- A `requestVoteOK` seen as a `prepareOK`. -/
def absVote (m : RVOKMsg N V) : Paxos.Msg1b N V := ⟨m.src, m.dst, m.term, absLog m.log⟩

/-- The refinement mapping from Raft* states to MultiPaxos states (Appendix C). -/
def abs (r : Raft.State N V) : Paxos.State N V where
  ballot := r.term
  leader := r.leader
  inst s := absLog (r.log s)
  chosen s := chosenOf (r.log s) (r.commit s)
  m1a := (fun m : RVMsg N => (m.cand, m.term)) '' r.rv
  m1b := absVote '' r.rvok
  m2a := r.props
  m2b := r.acks

theorem absLog_lt {L : List (ℕ × V)} {i : ℕ} (h : i < L.length) :
    absLog L i = some (lastTerm L, L[i].2) := by
  simp [absLog, List.getElem?_eq_getElem h]

theorem absLog_ge {L : List (ℕ × V)} {i : ℕ} (h : L.length ≤ i) : absLog L i = none := by
  simp [absLog, List.getElem?_eq_none h]

theorem chosenOf_append {L : List (ℕ × V)} (X : List (ℕ × V)) {c : ℕ} (hc : c ≤ L.length) :
    chosenOf (L ++ X) c = chosenOf L c := by
  ext ⟨i, v⟩
  simp only [chosenOf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, hi, hv⟩
    exact ⟨by omega, hi, by rwa [List.getElem_append_left (by omega)] at hv⟩
  · rintro ⟨h, hi, hv⟩
    exact ⟨by simp; omega, hi, by rwa [List.getElem_append_left h]⟩

theorem propsOf_eq (L : List (ℕ × V)) (t : ℕ) :
    propsOf L t = {x | ∃ i, ∃ h : i < (L.map Prod.snd).length, x = (i, t, (L.map Prod.snd)[i])} := by
  ext x; simp [propsOf]

theorem acksOf_eq (s : N) (L : List (ℕ × V)) (t : ℕ) :
    acksOf s L t =
      {x | ∃ i, ∃ h : i < (L.map Prod.snd).length, x = (s, i, t, (L.map Prod.snd)[i])} := by
  ext x; simp [acksOf]

theorem abs_init : abs (Raft.init : Raft.State N V) = Paxos.init := by
  ext <;> simp [abs, Raft.init, Paxos.init, absLog, chosenOf]

/-! ### Simulation of the individual steps -/

/-- `RequestVote(s)` implies `Phase1a(s)` (Appendix C, step 2.1). -/
theorem sim_requestVote (r : Raft.State N V) (s : N) :
    Relation.ReflTransGen (Paxos.Step Q) (abs r) (abs { r with
        term := Function.update r.term s (r.term s + 1)
        leader := Function.update r.leader s false
        rv := insert ⟨s, r.term s + 1, (r.log s).length, lastTerm (r.log s)⟩ r.rv
        rvok := insert ⟨s, s, r.term s + 1, r.log s⟩ r.rvok }) := by
  refine Relation.ReflTransGen.single ?_
  convert Paxos.Step.phase1a (Q := Q) (abs r) s using 1
  apply Paxos.State.ext <;> (try rfl) <;> simp [abs, Set.image_insert_eq, absVote]

/-- `ReceiveVote(s)` implies `Phase1b(s)` (Appendix C, step 2.2). -/
theorem sim_receiveVote (r : Raft.State N V) (s : N) (m : RVMsg N) (hm : m ∈ r.rv)
    (ht : r.term s < m.term) :
    Relation.ReflTransGen (Paxos.Step Q) (abs r) (abs { r with
        term := Function.update r.term s m.term
        leader := Function.update r.leader s false
        rvok := insert ⟨s, m.cand, m.term, r.log s⟩ r.rvok }) := by
  refine Relation.ReflTransGen.single ?_
  convert Paxos.Step.phase1b (Q := Q) (abs r) s m.cand m.term ⟨m, hm, rfl⟩ ht using 1
  apply Paxos.State.ext <;> (try rfl) <;> simp [abs, Set.image_insert_eq, absVote]

/-- `LeaderLearn(s)` implies `Learn(s)` for each newly committed entry (Appendix C, step 2.6). -/
theorem sim_leaderLearn {r : Raft.State N V} (I : Inv Q r) (s : N) (S : Finset (AEOKMsg N))
    (k : ℕ) (hl : r.leader s = true)
    (hS : ∀ m ∈ S, m ∈ r.aeok ∧ m.dst = s ∧ m.term = r.term s)
    (hQ : Q.IsQuorum (insert s (S.image AEOKMsg.src)))
    (hk : ∀ m ∈ S, k ≤ m.len) (hkl : k ≤ (r.log s).length) :
    Relation.ReflTransGen (Paxos.Step Q) (abs r)
      (abs { r with commit := Function.update r.commit s (max (r.commit s) k) }) := by
  have hacks := I.leaderLearn_acks s S k hl hS hk
  set C := ((r.log s).take k).map Prod.snd with hC
  have hCl : C.length = k := by simp [hC]; omega
  have hCget : ∀ i (h : i < C.length), C[i] = ((r.log s)[i]'(by omega)).2 := by
    intro i h; simp only [hC, List.getElem_map, List.getElem_take]
  have := Paxos.learn_batch (Q := Q) (abs r) s C (fun i h => ⟨_, _, hQ, fun a ha => by
    rw [hCget]; exact hacks i _ (by omega) a ha⟩)
  convert this using 1
  apply Paxos.State.ext <;> (try rfl)
  funext a
  by_cases ha : a = s
  · subst ha
    simp only [abs, Function.update_self]
    ext ⟨i, v⟩
    simp only [chosenOf, Set.mem_setOf_eq, Set.mem_union, Prod.mk.injEq]
    constructor
    · rintro ⟨h, hi, hv⟩
      rcases lt_max_iff.1 hi with hi | hi
      · exact Or.inl ⟨h, hi, hv⟩
      · exact Or.inr ⟨i, by omega, rfl, by rw [hCget, hv]⟩
    · rintro (⟨h, hi, hv⟩ | ⟨j, hj, hij, hjv⟩)
      · exact ⟨h, lt_max_of_lt_left hi, hv⟩
      · subst hij hjv
        exact ⟨by omega, lt_max_of_lt_right (by omega), (hCget _ hj).symm⟩
  · simp [abs, Function.update_of_ne ha]


/-- `abs` of a state whose log at `s` is `L'` has the expected `inst` after a batch of
`Phase2b` steps accepting all of `L'` in ballot `lastTerm L'`. -/
theorem absLog_eq_batch (L L' : List (ℕ × V)) (t : ℕ) (hLt : lastTerm L' = t)
    (hlen : L.length ≤ L'.length) :
    absLog L' = fun i => if h : i < (L'.map Prod.snd).length
      then some (t, (L'.map Prod.snd)[i]) else absLog L i := by
  funext i
  by_cases hi : i < L'.length
  · rw [absLog_lt hi, dif_pos (by simpa using hi), hLt]; simp
  · rw [absLog_ge (by omega), dif_neg (by simpa using hi), absLog_ge (by omega)]

/-- `AppendEntries(s, vals, prev)` implies `Phase2a` and `Phase2b` for every entry of the
leader's log (Appendix C, step 2.4; the leader implicitly accepts its own entries). -/
theorem sim_appendEntries {r : Raft.State N V} (I : Inv Q r) (s : N) (vals : List V)
    (prevLen : ℕ) (hl : r.leader s = true) (hvals : vals ≠ []) :
    Relation.ReflTransGen (Paxos.Step Q) (abs r) (abs { r with
        log := Function.update r.log s (r.log s ++ vals.map (fun v => (r.term s, v)))
        ae := insert ⟨s, r.term s, prevLen, r.log s ++ vals.map (fun v => (r.term s, v)),
          r.commit s⟩ r.ae
        props := r.props ∪ propsOf (r.log s ++ vals.map (fun v => (r.term s, v))) (r.term s)
        acks := r.acks ∪ acksOf s (r.log s ++ vals.map (fun v => (r.term s, v))) (r.term s) }) := by
  set t := r.term s with ht
  set L' := r.log s ++ vals.map (fun v => (t, v)) with hL'
  set W := L'.map Prod.snd with hW
  have hLt : lastTerm L' = t := lastTerm_append_map t hvals
  have hlen : (r.log s).length ≤ L'.length := by simp [hL']
  have hWne : W ≠ [] := by simp [hW, hL', hvals]
  have hWget : ∀ i (h : i < W.length), W[i] = (L'[i]'(by simpa [hW] using h)).2 := by
    intro i h; simp [hW]
  have hleft : ∀ i (h : i < (r.log s).length), L'[i]'(lt_of_lt_of_le h hlen) = (r.log s)[i] := by
    intro i h; simp only [hL', List.getElem_append_left h]
  have h1 := Paxos.phase2a_batch (Q := Q) (abs r) s W hl (by
      intro i h
      by_cases hi : i < (r.log s).length
      · right; refine ⟨lastTerm (r.log s), ?_⟩
        show absLog (r.log s) i = _
        rw [absLog_lt hi, hWget, hleft i hi]
      · left; exact absLog_ge (by omega)) (by
      intro i h w hw
      obtain ⟨-, hi, hiw⟩ := I.props_of_leader hl hw
      rw [hWget, hleft i hi, hiw])
  have h2 := Paxos.phase2b_batch (Q := Q)
    { abs r with m2a := (abs r).m2a ∪ {x | ∃ i, ∃ h : i < W.length, x = (i, (abs r).ballot s, W[i])} }
    s t W hWne le_rfl (fun i h => Or.inr ⟨i, h, rfl⟩)
  refine h1.trans ?_
  convert h2 using 1
  apply Paxos.State.ext <;> (try rfl)
  · simp [abs, ht]
  · simp [abs, ht]
  · funext a
    by_cases ha : a = s
    · subst ha
      simp only [abs, Function.update_self]
      exact absLog_eq_batch _ _ t hLt hlen
    · simp [abs, Function.update_of_ne ha]
  · funext a
    by_cases ha : a = s
    · subst ha
      simp only [abs, Function.update_self]
      exact chosenOf_append _ (I.commit_le a)
    · simp [abs, Function.update_of_ne ha]
  · simp only [abs]; rw [propsOf_eq]
  · simp only [abs]; rw [acksOf_eq]


/-- `ReceiveAppend(s)` (with the follower's new log already identified with the leader's log,
`Inv.receiveAppend_log`) implies `Phase2b` for every entry and `Learn` for the committed ones
(Appendix C, step 2.5). -/
theorem sim_receiveAppend {r : Raft.State N V} (I : Inv Q r) (hsafe : PropSafe Q r) (s : N)
    (m : AEMsg N V) (hm : m ∈ r.ae) (ht : r.term s ≤ m.term)
    (hlen : (r.log s).length ≤ m.full.length) :
    Relation.ReflTransGen (Paxos.Step Q) (abs r) (abs { r with
        term := Function.update r.term s m.term
        leader := Function.update r.leader s (if r.term s < m.term then false else r.leader s)
        log := Function.update r.log s m.full
        commit := Function.update r.commit s (max m.commit (r.commit s))
        aeok := insert ⟨s, m.src, m.term, m.full.length⟩ r.aeok
        acks := r.acks ∪ acksOf s m.full m.term }) := by
  obtain ⟨hcand, hsrc, hFne, hFt, hpF, hcF, hcm⟩ := I.ae_ok m hm
  set t := m.term with ht'
  set F := m.full with hF
  have hFin : InLogs r F := Or.inr (Or.inr ⟨m, hm, rfl⟩)
  have hFp : ∀ i (h : i < F.length), (i, t, F[i].2) ∈ r.props := fun i h => by
    have := I.last_props F hFin i h; rwa [hFt] at this
  set W := F.map Prod.snd with hW
  have hWne : W ≠ [] := by simp [hW, hFne]
  have hWget : ∀ i (h : i < W.length), W[i] = (F[i]'(by simpa [hW] using h)).2 := by
    intro i h; simp [hW]
  have h1 := Paxos.phase2b_batch (Q := Q) (abs r) s t W hWne ht (fun i h => by
    rw [hWget]; exact hFp i _)
  set C := (F.take m.commit).map Prod.snd with hC
  have hCl : C.length = m.commit := by simp [hC]; omega
  have hCget : ∀ i (h : i < C.length), C[i] = (F[i]'(by rw [hCl] at h; omega)).2 := by
    intro i h; simp only [hC, List.getElem_map, List.getElem_take]
  set P₁ : Paxos.State N V := { abs r with
        ballot := Function.update (abs r).ballot s t
        leader := Function.update (abs r).leader s
          (if (abs r).ballot s < t then false else (abs r).leader s)
        inst := Function.update (abs r).inst s
          (fun i => if h : i < W.length then some (t, W[i]) else (abs r).inst s i)
        m2b := (abs r).m2b ∪ {x | ∃ i, ∃ h : i < W.length, x = (s, i, t, W[i])} } with hP₁
  have h2 := Paxos.learn_batch (Q := Q) P₁ s C (fun i h => by
    obtain ⟨b, -, A, hA, hA'⟩ := hcm i (by omega) (by omega)
    exact ⟨b, A, hA, fun a ha => by rw [hCget]; exact Or.inl (hA' a ha)⟩)
  refine h1.trans ?_
  convert h2 using 1
  apply Paxos.State.ext <;> (try rfl)
  · funext a
    by_cases ha : a = s
    · subst ha
      simp only [abs, hP₁, Function.update_self]
      exact absLog_eq_batch _ _ t hFt hlen
    · simp [abs, hP₁, Function.update_of_ne ha]
  · funext a
    by_cases ha : a = s
    · subst ha
      simp only [abs, hP₁, Function.update_self]
      ext ⟨i, v⟩
      simp only [chosenOf, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro ⟨h, hi, hv⟩
        rcases lt_max_iff.1 hi with hi | hi
        · exact Or.inr ⟨i, by omega, by rw [hCget, hv]⟩
        · have hi' : i < (r.log a).length := lt_of_lt_of_le hi (I.commit_le a)
          refine Or.inl ⟨hi', hi, ?_⟩
          obtain ⟨b, hb, A, hA, hA'⟩ := I.commit_ok a i hi hi'
          rw [← hv]
          exact (hsafe i b t _ _ ⟨A, hA, hA'⟩ (hFp i h) (hb.trans ht)).symm
      · rintro (⟨h, hi, hv⟩ | ⟨j, hj, hjv⟩)
        · have hi' : i < F.length := by omega
          refine ⟨hi', lt_max_of_lt_right hi, ?_⟩
          obtain ⟨b, hb, A, hA, hA'⟩ := I.commit_ok a i hi h
          rw [← hv]
          exact hsafe i b t _ _ ⟨A, hA, hA'⟩ (hFp i hi') (hb.trans ht)
        · simp only [Prod.mk.injEq] at hjv
          obtain ⟨rfl, rfl⟩ := hjv
          exact ⟨by omega, lt_max_of_lt_left (by omega), (hCget _ hj).symm⟩
    · simp [abs, hP₁, Function.update_of_ne ha]
  · simp only [abs, hP₁]; rw [acksOf_eq]


/-- `BecomeLeader(s)` implies `Phase1Succeed(s)` (Appendix C, step 2.3), followed — when the new
leader adopts entries from the votes — by `Phase2a` and `Phase2b` for every entry. The heart of the
proof (step 4.2 of Appendix C): the candidate's own entries are safe entries of the votes, because
its own vote carries its current log and every voter's last term is at most the candidate's. -/
theorem sim_becomeLeader {r : Raft.State N V} (I : Inv Q r) (s : N) (S : Finset (RVOKMsg N V))
    (ext : List V) (hl : r.leader s = false)
    (hS : ∀ m ∈ S, m ∈ r.rvok ∧ m.dst = s ∧ m.term = r.term s)
    (hself : ∃ m ∈ S, m.src = s) (hQ : Q.IsQuorum (S.image RVOKMsg.src))
    (hext : ExtOK S (r.log s).length ext) :
    Relation.ReflTransGen (Paxos.Step Q) (abs r) (abs { r with
        leader := Function.update r.leader s true
        log := Function.update r.log s (r.log s ++ ext.map (fun v => (r.term s, v)))
        props := if ext = [] then r.props else
          r.props ∪ propsOf (r.log s ++ ext.map (fun v => (r.term s, v))) (r.term s)
        acks := if ext = [] then r.acks else
          r.acks ∪ acksOf s (r.log s ++ ext.map (fun v => (r.term s, v))) (r.term s) }) := by
  classical
  set t := r.term s with ht
  set n := (r.log s).length with hn
  set T := lastTerm (r.log s) with hT
  have hc : Cand Q r s t := ⟨S, hS, hQ⟩
  obtain ⟨m₀, hm₀S, hm₀src⟩ := hself
  have hm₀ : m₀ = ⟨s, s, t, m₀.log⟩ := by
    obtain ⟨-, h2, h3⟩ := hS m₀ hm₀S
    ext <;> simp [hm₀src, h2, h3]
  have hm₀log : m₀.log = r.log s := by
    by_contra hne
    have hmem := (hS m₀ hm₀S).1
    rw [hm₀] at hmem
    obtain ⟨c', hc'ne, hc'⟩ := I.cand_log s m₀.log hmem hl (Ne.symm hne)
    exact hc'ne (I.cand_unique hc hc').symm
  have hvote : ∀ m ∈ S, lastTerm m.log ≤ T := by
    intro m hm
    obtain ⟨L, hL, hle⟩ := I.rvok_vote m (hS m hm).1
    rw [(hS m hm).2.1, (hS m hm).2.2] at hL
    have := I.rvok_unique _ hL _ (hS m₀ hm₀S).1 hm₀src.symm (hS m₀ hm₀S).2.2.symm
    simp only at this
    rw [this.2, hm₀log] at hle
    exact hle
  obtain ⟨hextlen, hext2⟩ := hext
  choose mf hmfS c hc' hmax using hext2
  let newInst : ℕ → Option (ℕ × V) := fun i =>
    if i < n then absLog (r.log s) i else
      if h : i - n < ext.length then some (lastTerm (mf (i - n) h).log, ext[i - n]) else none
  have hsafe : ∀ i, Paxos.IsSafeEntry (S.image absVote) i (newInst i) := by
    intro i
    by_cases hi : i < n
    · simp only [newInst, if_pos hi, absLog_lt hi]
      refine ⟨⟨absVote m₀, Finset.mem_image_of_mem _ hm₀S, ?_⟩, ?_⟩
      · simp only [absVote, hm₀log, absLog_lt hi]
      · intro m' hm' c' v' hcv
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hm'
        simp only [absVote, absLog, Option.map_eq_some_iff] at hcv
        obtain ⟨_, _, hcv⟩ := hcv
        simp only [Prod.mk.injEq] at hcv
        rw [← hcv.1]; exact hvote m hm
    · by_cases hj : i - n < ext.length
      · simp only [newInst, if_neg hi, dif_pos hj]
        have hi' : i = n + (i - n) := by omega
        refine ⟨⟨absVote (mf _ hj), Finset.mem_image_of_mem _ (hmfS _ hj), ?_⟩, ?_⟩
        · have := hc' _ hj
          rw [show n + (i - n) = i by omega] at this
          simp only [absVote, absLog, this]; rfl
        · intro m' hm' c'' v' hcv
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hm'
          simp only [absVote, absLog, Option.map_eq_some_iff] at hcv
          obtain ⟨e, he, hcv⟩ := hcv
          simp only [Prod.mk.injEq] at hcv
          rw [← hcv.1]
          have hlt : i < m.log.length := (List.getElem?_eq_some_iff.1 he).1
          exact hmax _ hj m hm (by omega)
      · simp only [newInst, if_neg hi, dif_neg hj]
        intro m' hm'
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hm'
        simp only [absVote]
        exact absLog_ge (by have := hextlen m hm; omega)
  have hstep := Paxos.Step.phase1Succeed (Q := Q) (abs r) s (S.image absVote) newInst hl
    (by
      intro m' hm'
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hm'
      exact ⟨⟨m, (hS m hm).1, rfl⟩, (hS m hm).2.1, (hS m hm).2.2⟩)
    (by rw [Finset.image_image]; exact hQ)
    ⟨absVote m₀, Finset.mem_image_of_mem _ hm₀S, hm₀src⟩ hsafe
  refine (Relation.ReflTransGen.single hstep).trans ?_
  rcases eq_or_ne ext [] with rfl | he
  · have : newInst = absLog (r.log s) := by
      funext i
      by_cases hi : i < n
      · simp only [newInst, if_pos hi]
      · simp only [newInst, if_neg hi, List.length_nil, Nat.not_lt_zero, dif_neg, not_false_eq_true]
        exact (absLog_ge (by omega)).symm
    convert Relation.ReflTransGen.refl using 1
    apply Paxos.State.ext <;> (try rfl)
    · funext a
      by_cases ha : a = s
      · subst ha; simp [abs, this]
      · simp [abs, Function.update_of_ne ha]
    · funext a
      by_cases ha : a = s
      · subst ha; simp [abs]
      · simp [abs, Function.update_of_ne ha]
  · set L' := r.log s ++ ext.map (fun v => (t, v)) with hL'
    set W := L'.map Prod.snd with hW
    have hLt : lastTerm L' = t := lastTerm_append_map t he
    have hlen : n ≤ L'.length := by simp [hL', hn]
    have hWne : W ≠ [] := by simp [hW, hL', he]
    have hWget : ∀ i (h : i < W.length), W[i] = (L'[i]'(by simpa [hW] using h)).2 := by
      intro i h; simp [hW]
    have hL'l : L'.length = n + ext.length := by simp [hL', hn]
    have hL'get : ∀ i (h : i < L'.length) (hi : n ≤ i),
        L'[i] = (t, ext[i - n]'(by rw [hL'l] at h; omega)) := by
      intro i h hi
      simp only [hL', List.getElem_append_right (show (r.log s).length ≤ i from hi),
        List.getElem_map]
      rfl
    have hleft : ∀ i (h : i < n), L'[i]'(lt_of_lt_of_le h hlen) = (r.log s)[i] := by
      intro i h; simp only [hL', List.getElem_append_left h]
    set P₁ : Paxos.State N V := { abs r with
      inst := Function.update (abs r).inst s newInst
      leader := Function.update (abs r).leader s true } with hP₁
    have h1 := Paxos.phase2a_batch (Q := Q) P₁ s W (by simp [hP₁]) (by
        intro i h
        right
        simp only [hP₁, Function.update_self, newInst]
        by_cases hi : i < n
        · refine ⟨T, ?_⟩
          rw [if_pos hi, absLog_lt hi, hWget, hleft i hi]
        · have hj : i - n < ext.length := by simp [hW] at h; omega
          refine ⟨lastTerm (mf (i - n) hj).log, ?_⟩
          rw [if_neg hi, dif_pos hj, hWget, hL'get i _ (by omega)]) (by
        intro i h w hw
        exact absurd hw (I.no_props_of_cand hc hl))
    have h2 := Paxos.phase2b_batch (Q := Q)
      { P₁ with m2a := P₁.m2a ∪ {x | ∃ i, ∃ h : i < W.length, x = (i, P₁.ballot s, W[i])} }
      s t W hWne le_rfl (fun i h => Or.inr ⟨i, h, rfl⟩)
    refine h1.trans ?_
    convert h2 using 1
    apply Paxos.State.ext <;> (try rfl)
    · simp [abs, hP₁, ht]
    · simp [abs, hP₁, ht]
    · funext a
      by_cases ha : a = s
      · subst ha
        simp only [abs, hP₁, Function.update_self]
        funext i
        by_cases hi : i < L'.length
        · rw [absLog_lt hi, dif_pos (by simpa [hW] using hi), hLt, hWget]
        · rw [absLog_ge (by omega), dif_neg (by simpa [hW] using hi)]
          simp only [newInst]
          rw [if_neg (by omega), dif_neg (by omega)]
      · simp [abs, hP₁, Function.update_of_ne ha]
    · funext a
      by_cases ha : a = s
      · subst ha
        simp only [abs, hP₁, Function.update_self]
        exact chosenOf_append _ (I.commit_le a)
      · simp [abs, hP₁, Function.update_of_ne ha]
    · simp only [abs, hP₁, if_neg he]; rw [propsOf_eq]
    · simp only [abs, hP₁, if_neg he]; rw [acksOf_eq]


/-! ### The refinement theorem -/

/-- MultiPaxos safety, read back on the ghost variables of Raft*. -/
theorem propSafe_of_reachable {r : Raft.State N V} (hP : Paxos.Reachable Q (abs r)) :
    PropSafe Q r :=
  fun _ _ _ _ _ hc hw hbb => Paxos.proposal_eq_of_chosenAt hP hc hw hbb

/-- **Appendix C, step 2**: every step of Raft* implies a (possibly empty) sequence of MultiPaxos
steps under the refinement mapping `abs`, from any state satisfying the invariant. -/
theorem refinement_step {R : Rules V} (hhb : ¬ R.heartbeat) {r r' : Raft.State N V}
    (I : Inv Q r) (hsafe : PropSafe Q r) (h : Raft.Step Q R r r') :
    Relation.ReflTransGen (Paxos.Step Q) (abs r) (abs r') := by
  cases h with
  | requestVote s => exact sim_requestVote r s
  | receiveVote s m hm ht hv => exact sim_receiveVote r s m hm ht
  | becomeLeader s S ext hl hS hself hQ hext => exact sim_becomeLeader I s S ext hl hS hself hQ hext
  | appendEntries s vals prevLen hl hvals hprev =>
    exact sim_appendEntries I s vals prevLen hl (hvals.resolve_right hhb)
  | receiveAppend s m hm ht hprev hmatch hlen =>
    rw [I.receiveAppend_log s m hm hprev hmatch]
    exact sim_receiveAppend I hsafe s m hm ht hlen
  | leaderLearn s S k hl hS hQ hk hkl => exact sim_leaderLearn I s S k hl hS hQ hk hkl

/-- The invariant holds and the image is a reachable MultiPaxos state, for every reachable state of
Raft* whose vote rule never favours a candidate with a smaller last term and that has no
heartbeats. -/
theorem inv_and_reachable {R : Rules V} (hR : VoteMono R) (hhb : ¬ R.heartbeat)
    {r : Raft.State N V} (hr : Raft.Reachable Q R r) :
    Inv Q r ∧ Paxos.Reachable Q (abs r) := by
  induction hr with
  | refl => exact ⟨inv_init, by rw [abs_init]; exact Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
    obtain ⟨I, hP⟩ := ih
    have hsafe := propSafe_of_reachable hP
    exact ⟨I.step hR hhb hsafe hstep, hP.trans (refinement_step hhb I hsafe hstep)⟩

/-- **Appendix C ("Raft* is a refinement of Paxos")**: under the refinement mapping of Appendix C,
the image of every reachable state of (repaired) Raft* is a reachable state of MultiPaxos. -/
theorem refinement {R : Rules V} (hR : VoteMono R) (hhb : ¬ R.heartbeat)
    {r : Raft.State N V} (hr : Raft.Reachable Q R r) : Paxos.Reachable Q (abs r) :=
  (inv_and_reachable hR hhb hr).2

/-- **State machine safety of Raft*** (Section 3: Raft* is correct because it refines Paxos):
committed entries of any two servers agree. -/
theorem raftStar_commitSafe {R : Rules V} (hR : VoteMono R) (hhb : ¬ R.heartbeat)
    {r : Raft.State N V} (hr : Raft.Reachable Q R r) : CommitSafe r := by
  intro s s' i h h' hc hc'
  have hP := refinement hR hhb hr
  exact Paxos.safety hP (s := s) (s' := s') (i := i)
    (show (i, (r.log s)[i].2) ∈ chosenOf (r.log s) (r.commit s) from ⟨h, hc, rfl⟩)
    (show (i, (r.log s')[i].2) ∈ chosenOf (r.log s') (r.commit s') from ⟨h', hc', rfl⟩)

theorem voteMono_repaired : VoteMono (Rules.repaired : Rules V) := fun _ _ _ h => h

theorem voteMono_raft : VoteMono (⟨raftVoteOK, False⟩ : Rules V) := by
  rintro L n t (h | ⟨h, -⟩) <;> omega

theorem voteMono_fig2Fixed : VoteMono (⟨fig2FixedVoteOK, False⟩ : Rules V) := by
  rintro L n t (h | ⟨h, -⟩) <;> omega

/-- Repaired Raft* (any log lengths in the vote, every append carries a new value) refines
MultiPaxos. -/
theorem refinement_repaired {r : Raft.State N V} (hr : Raft.Reachable Q Rules.repaired r) :
    Paxos.Reachable Q (abs r) :=
  refinement voteMono_repaired (fun h => h) hr

/-- Raft* with Raft's own vote rule (TLA+ spec B.2) and no heartbeats is safe. -/
theorem raftStar_commitSafe_raftVote {r : Raft.State N V}
    (hr : Raft.Reachable Q ⟨raftVoteOK, False⟩ r) : CommitSafe r :=
  raftStar_commitSafe voteMono_raft (fun h => h) hr

/-- Raft* with Figure 2's vote rule read at the voter's *last* index, and no heartbeats, is safe. -/
theorem raftStar_commitSafe_fig2Fixed {r : Raft.State N V}
    (hr : Raft.Reachable Q ⟨fig2FixedVoteOK, False⟩ r) : CommitSafe r :=
  raftStar_commitSafe voteMono_fig2Fixed (fun h => h) hr

end Podc.PaxosRaftRefinement
