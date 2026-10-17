import Papers.PODC2021.FastByzantineConsensus.ProtocolSafety
import Papers.PODC2021.FastByzantineConsensus.TwoStep
import Cslib.Computability.Distributed.Byzantine.PartialSync.Gossip

/-!
# A concrete implementation of the protocol in the partially synchronous model

We implement the generalized protocol of Kuznetsov–Tonkikh–Zhang (Section 3 + Appendix A) as an
`Algorithm` of the shared model `Cslib.Byzantine.PartialSync`, with ideal signatures:

* messages are tokens `Tok P V` (signed statements); `auth`: the signer of a message is
  `Tok.signer`, and a message carries exactly itself as signature token;
* every process keeps the finite set `known` of all tokens it has received or emitted and
  **gossips** it to everybody at every time step (so certificates travel with the votes/requests
  that need them, and a forwarded vote carries its evidence);
* views are driven by the (perfectly synchronized) local clock: view `v` is the time interval
  `[vL, (v+1)L)` (the paper's unspecified view synchronizer; `L` is a parameter, `6δ + 12`
  suffices); the leader of view `v` is `pr.leader v`;
* at every step, after adding the received tokens, a process performs in order: vote when
  entering a new view (`actVote`); as leader of view `v > 0`, sign `CertAck` for its own selection
  (`actLeaderCA`, which plays the role of `CertReq`); as verifier, sign `CertAck(x, v)` for a value
  the leader certified on a valid vote set (`actVerify`); as leader, propose a certified value
  (`actPropose`; the leader of view `0` proposes its input in its initial state); acknowledge the
  first valid proposal of the view (`actAck`); send `Commit` on a commit certificate of the view
  (`actCommit`). A process decides `x` as soon as its `known` contains a fast (`n − t` acks) or
  slow (`⌈(n+f+1)/2⌉` commits) quorum for `x`.

Main results: `algo_gossips` (with `Cslib.Computability.Distributed.Byzantine.PartialSync.Gossip`), `algo_unforging`, `algo_agreement` (via the refinement `reachable_absState` into the
transition system of `Protocol.lean` and `Protocol.consistency`), `algo_validity` (weak validity),
`algo_twoStep` (for `δ ≥ 2`), `algo_termination`, hence `algo_fastConsensus`: the protocol is an
`f`-resilient `t`-two-step consensus protocol for `n ≥ 3f + 2t − 1`; with `LowerBound.lean` this
gives the tight bound `tight_bound`.
-/

set_option linter.unusedSectionVars false

namespace FastByzantineConsensus.Impl

open Cslib.Byzantine.PartialSync FastByzantineConsensus.Protocol Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- Local state of a process. -/
structure LState (P V : Type*) where
  /-- Local clock (= current time). -/
  clock : ℕ
  /-- The input. -/
  input : V
  /-- All tokens received or emitted so far. -/
  known : Finset (Tok P V)
  /-- `vote_q`: latest acknowledged proposal `(x, u)`. -/
  ballot : Option (V × ℕ)
  /-- Latest collected commit certificate `(x, u)`. -/
  cc : Option (V × ℕ)

/-- Ideal signatures: a message is a token, signed by `Tok.signer`, carrying itself. -/
def auth : Auth P (Tok P V) (Tok P V) where
  signer := Tok.signer
  tokens m := {m}

section Defs

variable (pr : Params P) (L : ℕ)

open Classical in
/-- `x` is a possible outcome of the selection algorithm on a valid vote set for view `v` whose
votes (and their certificates) are in `K`. -/
def Sel (K : Finset (Tok P V)) (v : ℕ) (x : V) : Prop :=
  ∃ S bal cc, ValidVotes pr (↑K : Set (Tok P V)) v S bal cc ∧ Selects pr v S bal cc x

open Classical in
/-- The value the leader selects: its input if allowed, otherwise some allowed value. -/
noncomputable def leaderChoice (K : Finset (Tok P V)) (v : ℕ) (inp : V) : V :=
  if Sel pr K v inp then inp else if h : ∃ x, Sel pr K v x then Classical.choose h else inp

/-- Entering a new view `v` (`old`: the state before the step): send the vote. -/
def actVote (p : P) (old : LState P V) (v : ℕ) (s : LState P V) : LState P V :=
  if v ≠ old.clock / L then { s with known := insert (Tok.vote p v s.ballot s.cc) s.known } else s

open Classical in
/-- The leader of view `v > 0` signs `CertAck` for its selection (once per view). -/
noncomputable def actLeaderCA (p : P) (v : ℕ) (s : LState P V) : LState P V :=
  if pr.leader v = p ∧ v ≠ 0 ∧ (∀ x, Tok.certAck p x v ∉ s.known) ∧ ∃ x, Sel pr s.known v x then
    { s with known := insert (Tok.certAck p (leaderChoice pr s.known v s.input) v) s.known }
  else s

open Classical in
/-- A verifier signs `CertAck(x, v)` for a value `x` certified by the leader of `v` on a valid
vote set (one value per step). -/
noncomputable def actVerify (p : P) (v : ℕ) (s : LState P V) : LState P V :=
  if h : ∃ x, Tok.certAck (pr.leader v) x v ∈ s.known ∧ Tok.certAck p x v ∉ s.known ∧
      Sel pr s.known v x then
    { s with known := insert (Tok.certAck p (Classical.choose h) v) s.known }
  else s

open Classical in
/-- The leader of view `v > 0` proposes a value with a progress certificate (once per view). -/
noncomputable def actPropose (p : P) (v : ℕ) (s : LState P V) : LState P V :=
  if h : pr.leader v = p ∧ v ≠ 0 ∧ (∀ y, Tok.propose p y v ∉ s.known) ∧
      ∃ x, Certified pr (↑s.known : Set (Tok P V)) x v then
    { s with known := insert (Tok.propose p (Classical.choose h.2.2.2) v) s.known }
  else s

open Classical in
/-- Acknowledge the first valid proposal of view `v` and adopt it as the vote. -/
noncomputable def actAck (p : P) (v : ℕ) (s : LState P V) : LState P V :=
  if h : (∀ y, Tok.ack p y v ∉ s.known) ∧ ∃ x, Tok.propose (pr.leader v) x v ∈ s.known ∧
      (v = 0 ∨ Certified pr (↑s.known : Set (Tok P V)) x v) then
    { s with known := insert (Tok.ack p (Classical.choose h.2) v) s.known,
             ballot := some (Classical.choose h.2, v) }
  else s

open Classical in
/-- On a commit certificate for the current view, send `Commit` and record the certificate. -/
noncomputable def actCommit (p : P) (v : ℕ) (s : LState P V) : LState P V :=
  if h : ∃ x, HasCC pr (↑s.known : Set (Tok P V)) x v ∧ Tok.commit p x v ∉ s.known then
    { s with known := insert (Tok.commit p (Classical.choose h) v) s.known,
             cc := some (Classical.choose h, v) }
  else s

/-- The local step: receive (add all received tokens), advance the clock, then perform the
actions for the view `v = (clock + 1) / L` of the new time. -/
noncomputable def stepFn (p : P) (s : LState P V) (ib : P → List (Tok P V)) : LState P V :=
  let v := (s.clock + 1) / L
  let s1 : LState P V :=
    { s with clock := s.clock + 1, known := s.known ∪ univ.biUnion fun q => (ib q).toFinset }
  actCommit pr p v (actAck pr p v (actPropose pr p v (actVerify pr p v
    (actLeaderCA pr p v (actVote L p s v s1)))))

open Classical in
/-- **The protocol** as an algorithm of the partially synchronous model. -/
noncomputable def algo : Algorithm P (Tok P V) (LState P V) V V where
  init p x := ⟨0, x, if pr.leader 0 = p then {Tok.propose p x 0} else ∅, none, none⟩
  step := stepFn pr L
  send _ s _ := s.known.toList
  decide _ s := if h : ∃ x, Decided pr (↑s.known : Set (Tok P V)) x then some (Classical.choose h)
    else none

/-- The abstract state (in the transition system of `Protocol.lean`) corresponding to time `τ`
of a run: all tokens known to correct processes, and the local states of correct processes. -/
noncomputable def absState (R : Run P (Tok P V) V) (τ : ℕ) : State P V where
  E := {k | ∃ q ∉ R.faulty, k ∈ (R.st (algo pr L) τ q).known}
  loc q := if q ∈ R.faulty then ⟨0, none, none⟩ else
    ⟨τ / L, (R.st (algo pr L) τ q).ballot, (R.st (algo pr L) τ q).cc⟩

end Defs

variable {pr : Params P} {L : ℕ}

/-! ### Basic properties of the local step -/

section Basic

variable (pr L) in
/-- Every action keeps the known tokens and only adds tokens signed by the acting process. -/
def Grows (p : P) (f : LState P V → LState P V) : Prop :=
  ∀ s, s.known ⊆ (f s).known ∧ (f s).clock = s.clock ∧ (f s).input = s.input ∧
    ∀ k ∈ (f s).known, k ∈ s.known ∨ k.signer = p

theorem grows_comp {p : P} {f g : LState P V → LState P V} (hf : Grows p f) (hg : Grows p g) :
    Grows p (f ∘ g) := by
  intro s
  obtain ⟨g1, g2, g3, g4⟩ := hg s
  obtain ⟨f1, f2, f3, f4⟩ := hf (g s)
  refine ⟨g1.trans f1, by simp [f2, g2], by simp [f3, g3], fun k hk => ?_⟩
  rcases f4 k hk with h | h
  · exact g4 k h
  · exact Or.inr h

theorem grows_vote (p : P) (old : LState P V) (v : ℕ) : Grows p (actVote L p old v) := by
  intro s
  unfold actVote
  split_ifs
  · refine ⟨subset_insert _ _, rfl, rfl, fun k hk => ?_⟩
    rcases mem_insert.mp hk with h | h
    · exact Or.inr (by rw [h]; rfl)
    · exact Or.inl h
  · exact ⟨subset_rfl, rfl, rfl, fun k hk => Or.inl hk⟩

theorem grows_leaderCA (p : P) (v : ℕ) : Grows p (actLeaderCA (V := V) pr p v) := by
  intro s
  unfold actLeaderCA
  split_ifs
  · refine ⟨subset_insert _ _, rfl, rfl, fun k hk => ?_⟩
    rcases mem_insert.mp hk with h | h
    · exact Or.inr (by rw [h]; rfl)
    · exact Or.inl h
  · exact ⟨subset_rfl, rfl, rfl, fun k hk => Or.inl hk⟩

theorem grows_verify (p : P) (v : ℕ) : Grows p (actVerify (V := V) pr p v) := by
  intro s
  unfold actVerify
  split_ifs
  · refine ⟨subset_insert _ _, rfl, rfl, fun k hk => ?_⟩
    rcases mem_insert.mp hk with h | h
    · exact Or.inr (by rw [h]; rfl)
    · exact Or.inl h
  · exact ⟨subset_rfl, rfl, rfl, fun k hk => Or.inl hk⟩

theorem grows_propose (p : P) (v : ℕ) : Grows p (actPropose (V := V) pr p v) := by
  intro s
  unfold actPropose
  split_ifs
  · refine ⟨subset_insert _ _, rfl, rfl, fun k hk => ?_⟩
    rcases mem_insert.mp hk with h | h
    · exact Or.inr (by rw [h]; rfl)
    · exact Or.inl h
  · exact ⟨subset_rfl, rfl, rfl, fun k hk => Or.inl hk⟩

theorem grows_ack (p : P) (v : ℕ) : Grows p (actAck (V := V) pr p v) := by
  intro s
  unfold actAck
  split_ifs
  · refine ⟨subset_insert _ _, rfl, rfl, fun k hk => ?_⟩
    rcases mem_insert.mp hk with h | h
    · exact Or.inr (by rw [h]; rfl)
    · exact Or.inl h
  · exact ⟨subset_rfl, rfl, rfl, fun k hk => Or.inl hk⟩

theorem grows_commit (p : P) (v : ℕ) : Grows p (actCommit (V := V) pr p v) := by
  intro s
  unfold actCommit
  split_ifs
  · refine ⟨subset_insert _ _, rfl, rfl, fun k hk => ?_⟩
    rcases mem_insert.mp hk with h | h
    · exact Or.inr (by rw [h]; rfl)
    · exact Or.inl h
  · exact ⟨subset_rfl, rfl, rfl, fun k hk => Or.inl hk⟩

/-- The six actions of a step, after reception. -/
theorem grows_actions (p : P) (old : LState P V) (v : ℕ) :
    Grows p (actCommit pr p v ∘ actAck pr p v ∘ actPropose pr p v ∘ actVerify pr p v ∘
      actLeaderCA pr p v ∘ actVote L p old v) :=
  grows_comp (grows_commit p v) (grows_comp (grows_ack p v) (grows_comp (grows_propose p v)
    (grows_comp (grows_verify p v) (grows_comp (grows_leaderCA p v) (grows_vote p old v)))))

theorem stepFn_eq (p : P) (s : LState P V) (ib : P → List (Tok P V)) :
    stepFn pr L p s ib = (actCommit pr p ((s.clock + 1) / L) ∘ actAck pr p ((s.clock + 1) / L) ∘
      actPropose pr p ((s.clock + 1) / L) ∘ actVerify pr p ((s.clock + 1) / L) ∘
      actLeaderCA pr p ((s.clock + 1) / L) ∘ actVote L p s ((s.clock + 1) / L))
      { s with clock := s.clock + 1, known := s.known ∪ univ.biUnion fun q => (ib q).toFinset } :=
  rfl

/-- A step: the clock advances, all known and received tokens are kept, and every new token is
signed by the process itself. -/
theorem stepFn_spec (p : P) (s : LState P V) (ib : P → List (Tok P V)) :
    (stepFn pr L p s ib).clock = s.clock + 1 ∧ (stepFn pr L p s ib).input = s.input ∧
    s.known ⊆ (stepFn pr L p s ib).known ∧
    (∀ q, ∀ k ∈ ib q, k ∈ (stepFn pr L p s ib).known) ∧
    ∀ k ∈ (stepFn pr L p s ib).known, k ∈ s.known ∨ (∃ q, k ∈ ib q) ∨ k.signer = p := by
  rw [stepFn_eq]
  obtain ⟨h1, h2, h3, h4⟩ := grows_actions (pr := pr) (L := L) p s ((s.clock + 1) / L)
    { s with clock := s.clock + 1, known := s.known ∪ univ.biUnion fun q => (ib q).toFinset }
  refine ⟨h2, h3, fun k hk => h1 (mem_union_left _ hk), fun q k hk => h1 (mem_union_right _
    (mem_biUnion.mpr ⟨q, mem_univ _, List.mem_toFinset.mpr hk⟩)), fun k hk => ?_⟩
  rcases h4 k hk with h | h
  · rcases mem_union.mp h with h | h
    · exact Or.inl h
    · obtain ⟨q, -, hq⟩ := mem_biUnion.mp h
      exact Or.inr (Or.inl ⟨q, List.mem_toFinset.mp hq⟩)
  · exact Or.inr (Or.inr h)

/-- The protocol **gossips** its known tokens (`Algorithm.Gossips`): knowledge only grows, every
known token is sent to everybody at every step, and received tokens are learnt. -/
theorem algo_gossips : (algo (V := V) pr L).Gossips auth fun s => ↑s.known where
  subset_step p s ib := coe_subset.2 (stepFn_spec p s ib).2.2.1
  tokens_subset p s q m hm := by
    simpa [auth] using (mem_toList.1 hm : m ∈ s.known)
  exists_mem_send p s q k hk := ⟨k, mem_toList.2 hk, rfl⟩
  tokens_subset_step p s ib q m hm :=
    Set.singleton_subset_iff.2 (mem_coe.2 ((stepFn_spec p s ib).2.2.2.1 q m hm))

/-- The protocol only emits its own signatures and relays received ones. -/
theorem algo_unforging : (algo (V := V) pr L).Unforging auth := by
  refine algo_gossips.toSharesKnowledge.unforging (fun p x k hk => ?_) fun p s ib k hk => ?_
  · have hk' : k ∈ (if pr.leader 0 = p then {Tok.propose p x 0} else ∅ : Finset (Tok P V)) := hk
    split_ifs at hk'
    · rw [mem_singleton.1 hk']; rfl
    · simp at hk'
  · rcases (stepFn_spec p s ib).2.2.2.2 k hk with h | ⟨q, h⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨q, k, h, rfl⟩)
    · exact Or.inr (Or.inr h)

variable (R : Run P (Tok P V) V)

theorem st_succ_eq (τ : ℕ) (q : P) :
    R.st (algo pr L) (τ + 1) q = stepFn pr L q (R.st (algo pr L) τ q) (R.inbox (algo pr L) q τ) :=
  R.st_succ _ τ q

@[simp] theorem st_clock (τ : ℕ) (q : P) : (R.st (algo pr L) τ q).clock = τ := by
  induction τ with
  | zero => rfl
  | succ τ ih => rw [st_succ_eq, (stepFn_spec q _ _).1, ih]

@[simp] theorem st_input (τ : ℕ) (q : P) : (R.st (algo pr L) τ q).input = R.inp q := by
  induction τ with
  | zero => rfl
  | succ τ ih => rw [st_succ_eq, (stepFn_spec q _ _).2.1, ih]

theorem known_mono {τ τ' : ℕ} (h : τ ≤ τ') (q : P) :
    (R.st (algo pr L) τ q).known ⊆ (R.st (algo pr L) τ' q).known :=
  coe_subset.1 (algo_gossips.mono R h q)

/-- Received tokens are known after the step. -/
theorem mem_known_of_inbox {τ : ℕ} {q r : P} {k : Tok P V} (hk : k ∈ R.inbox (algo pr L) q τ r) :
    k ∈ (R.st (algo pr L) (τ + 1) q).known := by
  rw [st_succ_eq]; exact (stepFn_spec q _ _).2.2.2.1 r k hk

/-- New tokens are received or signed by the process. -/
theorem mem_known_succ {τ : ℕ} {q : P} {k : Tok P V}
    (hk : k ∈ (R.st (algo pr L) (τ + 1) q).known) :
    k ∈ (R.st (algo pr L) τ q).known ∨ (∃ r, k ∈ R.inbox (algo pr L) q τ r) ∨ k.signer = q := by
  rw [st_succ_eq] at hk; exact (stepFn_spec q _ _).2.2.2.2 k hk

variable {R} in
/-- Tokens signed by a correct process `q` that some correct process knows are known to `q`
(only `q` creates them; unforgeability of the adversary). -/
theorem known_signed (hRa : R.AuthValid auth (algo pr L)) {q c : P}
    (hq : q ∉ R.faulty) (hc : c ∉ R.faulty) {τ : ℕ} {k : Tok P V}
    (hk : k ∈ (R.st (algo pr L) τ c).known) (hs : k.signer = q) :
    k ∈ (R.st (algo pr L) τ q).known :=
  algo_gossips.mem_of_mem algo_unforging hRa hc hq hk hs

variable {R} in
/-- A token received by a correct process at time `τ` is signed by a Byzantine process or known
to some correct process (its signer) at time `τ`. -/
theorem recv_origin (hRa : R.AuthValid auth (algo pr L)) {c r : P}
    (hc : c ∉ R.faulty) {τ : ℕ} {k : Tok P V} (hk : k ∈ R.inbox (algo pr L) c τ r) :
    k.signer ∈ R.faulty ∨ ∃ c' ∉ R.faulty, k ∈ (R.st (algo pr L) τ c').known := by
  by_cases hs : k.signer ∈ R.faulty
  · exact Or.inl hs
  · exact Or.inr ⟨_, hs, algo_gossips.mem_of_mem_inbox algo_unforging hRa hc hs hk rfl rfl⟩

/-- What a correct process sends at time `τ` is its knowledge at `τ`. -/
theorem out_correct {q : P} (hq : q ∉ R.faulty) (τ : ℕ) (r : P) :
    R.out (algo pr L) q τ r = (R.st (algo pr L) τ q).known.toList :=
  R.out_of_correct _ hq τ r

end Basic

end FastByzantineConsensus.Impl
