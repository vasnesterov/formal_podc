import Papers.PODC2024.TetraBFT.ProtocolLiveness

/-!
# Liveness within a synchronized view (Lemma 5 and the timing of a view)

If, after GST, all correct nodes are in the same view `v` with a correct leader during
`K = 6(δ + 1)` time units, then every correct node decides by the end of that interval
(`decides_of_synchronized_view`), and all decide the same value.

This is the paper's Lemma 5 combined with Lemmas 2 and 4 and the timing budget of a view: the
proof/suggest messages (sent when the nodes entered `v`, before `t0`), the proposal, and
vote-1, vote-2, vote-3, vote-4: six hops, each costing one message delay `δ` plus one tick of
processing in this discrete-time model (the paper's "6Δ").
It does *not* establish that such a synchronized interval ever occurs; for the view-change rule
of the paper it need not (`Counterexample.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace TetraBFT

open Finset Cslib.Byzantine.PartialSync

variable {n : ℕ} {V : Type} [DecidableEq V]

/-! ### Proposals in an outbox -/

/-- The proposals in a list of messages. -/
def props (l : List (Msg V)) : List (ℕ × V) :=
  l.filterMap fun m => match m with
    | .proposal w x => some (w, x)
    | _ => none

theorem mem_props {l : List (Msg V)} {w : ℕ} {x : V} :
    (w, x) ∈ props l ↔ Msg.proposal w x ∈ l := by
  simp only [props, List.mem_filterMap]
  constructor
  · rintro ⟨m, hm, he⟩
    cases m <;> simp_all
  · intro h; exact ⟨_, h, rfl⟩

theorem props_append (l l' : List (Msg V)) : props (l ++ l') = props l ++ props l' := by
  simp [props, List.filterMap_append]

section Stages

variable (prm : Params n)

/-- The stages after the view change. -/
noncomputable def post (p : Fin n) (s : St n V) : St n V :=
  decideSt prm (voteKSt prm 4 (voteKSt prm 3 (voteKSt prm 2 (vote1St prm (proposeSt prm p s)))))

theorem step_eq_post (p : Fin n) (s : St n V) (ib : Fin n → List (Msg V)) :
    step prm p s ib = post prm p (preVote prm s ib) := rfl

/-- Stages that only append votes (and their messages) to the outbox. -/
structure OutExt (s s' : St n V) : Prop where
  out : ∃ l, s'.out = s.out ++ l
  votes : ∀ w ∈ s'.votes, w ∈ s.votes ∨ Msg.vote w.phase w.view w.val ∈ s'.out
  props : props s'.out = props s.out
  propView : s'.propView = s.propView

theorem OutExt.refl (s : St n V) : OutExt s s :=
  ⟨⟨[], by simp⟩, fun w hw => Or.inl hw, rfl, rfl⟩

theorem OutExt.trans {s s' s'' : St n V} (h : OutExt s s') (h' : OutExt s' s'') :
    OutExt s s'' := by
  obtain ⟨l, hl⟩ := h.out
  obtain ⟨l', hl'⟩ := h'.out
  refine ⟨⟨l ++ l', by rw [hl', hl, List.append_assoc]⟩, fun w hw => ?_, h'.props.trans h.props,
    h'.propView.trans h.propView⟩
  rcases h'.votes w hw with hw | hw
  · rcases h.votes w hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr (by rw [hl']; exact List.mem_append_left _ hw)
  · exact Or.inr hw

theorem OutExt.castVote (s : St n V) (k : ℕ) (x : V) : OutExt s (castVote s k x) := by
  refine ⟨⟨_, rfl⟩, fun w hw => ?_, by simp [TetraBFT.castVote, TetraBFT.props], rfl⟩
  simp only [TetraBFT.castVote, List.mem_append, List.mem_singleton] at hw ⊢
  rcases hw with hw | rfl
  · exact Or.inl hw
  · exact Or.inr (Or.inr rfl)

theorem OutExt.vote1St (s : St n V) : OutExt s (vote1St prm s) := by
  unfold TetraBFT.vote1St
  split
  · exact .refl s
  · split
    · exact .refl s
    · split
      · exact .castVote s _ _
      · split
        · exact .castVote s _ _
        · exact .refl s

theorem OutExt.voteKSt (k : ℕ) (s : St n V) : OutExt s (voteKSt prm k s) := by
  unfold TetraBFT.voteKSt
  split
  · exact .refl s
  · split
    · exact .refl s
    · exact .castVote s _ _

theorem OutExt.decideSt (s : St n V) : OutExt s (decideSt prm s) := by
  unfold TetraBFT.decideSt
  split
  · exact .refl s
  · split
    · exact .refl s
    · exact ⟨⟨[], by simp⟩, fun w hw => Or.inl hw, rfl, rfl⟩

theorem proposeSt_shape (p : Fin n) (s : St n V) :
    proposeSt prm p s = s ∨ ∃ x, proposeSt prm p s =
      { s with propView := some s.view, out := s.out ++ [.proposal s.view x] } ∧
      s.propView ≠ some s.view := by
  unfold TetraBFT.proposeSt
  split
  · split
    · exact Or.inl rfl
    · rename_i h
      split
      · rename_i x _
        exact Or.inr ⟨x, rfl, h⟩
      · exact Or.inl rfl
  · exact Or.inl rfl

/-- The part of `post` after the proposal. -/
noncomputable def postVote (s : St n V) : St n V :=
  decideSt prm (voteKSt prm 4 (voteKSt prm 3 (voteKSt prm 2 (vote1St prm s))))

theorem OutExt.postVote (s : St n V) : OutExt s (postVote prm s) :=
  ((((OutExt.vote1St prm s).trans (.voteKSt prm 2 _)).trans (.voteKSt prm 3 _)).trans
    (.voteKSt prm 4 _)).trans (.decideSt prm _)

theorem VoteExt.postVote (s : St n V) : VoteExt s (postVote prm s) :=
  ((((VoteExt.vote1St prm s).trans (.voteKSt prm 2 _)).trans (.voteKSt prm 3 _)).trans
    (.voteKSt prm 4 _)).trans (.decideSt prm _)

theorem post_eq (p : Fin n) (s : St n V) : post prm p s = postVote prm (proposeSt prm p s) := rfl

/-- Shape of the proposals sent in a step after the view change. -/
theorem post_props (p : Fin n) (s : St n V) (h0 : props s.out = []) :
    (props (post prm p s).out = [] ∧ (post prm p s).propView = s.propView) ∨
    ∃ x, props (post prm p s).out = [(s.view, x)] ∧ (post prm p s).propView = some s.view ∧
      s.propView ≠ some s.view := by
  have hE := OutExt.postVote prm (proposeSt prm p s)
  rw [post_eq]
  rcases proposeSt_shape prm p s with h | ⟨x, h, hne⟩
  · rw [h] at hE ⊢
    exact Or.inl ⟨hE.props.trans h0, hE.propView⟩
  · rw [h] at hE ⊢
    refine Or.inr ⟨x, ?_, hE.propView, hne⟩
    rw [hE.props, props_append, h0]
    simp [props]

theorem post_votes (p : Fin n) (s : St n V) :
    ∀ w ∈ (post prm p s).votes, w ∈ s.votes ∨ Msg.vote w.phase w.view w.val ∈ (post prm p s).out := by
  intro w hw
  have hE := OutExt.postVote prm (proposeSt prm p s)
  rw [post_eq] at hw ⊢
  rcases proposeSt_shape prm p s with h | ⟨x, h, -⟩ <;> rw [h] at hE hw ⊢ <;> exact hE.votes w hw

theorem post_out (p : Fin n) (s : St n V) : ∃ l, (post prm p s).out = s.out ++ l := by
  rw [post_eq]
  rcases proposeSt_shape prm p s with h | ⟨x, h, -⟩
  · rw [h]; exact (OutExt.postVote prm s).out
  · rw [h]
    obtain ⟨l, hl⟩ := (OutExt.postVote prm
      { s with propView := some s.view, out := s.out ++ [.proposal s.view x] }).out
    exact ⟨[Msg.proposal s.view x] ++ l, by rw [hl]; simp⟩

theorem post_voteExt (p : Fin n) (s : St n V) : VoteExt s (post prm p s) :=
  (VoteExt.proposeSt prm p s).trans (VoteExt.postVote prm _)

/-! ### Enabling lemmas -/

theorem proposeVal_isSome' {s : St n V} (h : s.view = 0 ∨ ∃ x, leaderSafe prm s x) :
    (proposeVal prm s).isSome := by
  rcases h with h | h
  · simp [proposeVal, h]
  · exact proposeVal_isSome h

theorem post_propose {p : Fin n} {s : St n V} (hp : p = prm.leader s.view)
    (h : s.view = 0 ∨ ∃ x, leaderSafe prm s x) : (post prm p s).propView = some s.view := by
  have hE := OutExt.postVote prm (proposeSt prm p s)
  rw [post_eq, hE.propView]
  unfold TetraBFT.proposeSt
  rw [if_pos hp]
  split
  · assumption
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (proposeVal_isSome' prm h)
    rw [hx]

theorem vote1St_votes {s : St n V} {x : V}
    (hprop : firstFrom s.rcv (prm.leader s.view) (getProposal s.view) = some x)
    (hsafe : s.view = 0 ∨ nodeSafe prm s x) :
    ∃ y, (⟨1, s.view, y⟩ : Vote V) ∈ (vote1St prm s).votes := by
  unfold TetraBFT.vote1St
  split
  · rename_i h
    obtain ⟨w, hw, hw'⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw'
    exact ⟨w.val, by rw [← hw'.1, ← hw'.2]; exact hw⟩
  · rw [hprop]
    simp only
    split
    · exact ⟨x, by simp [TetraBFT.castVote]⟩
    · rename_i h0
      rcases hsafe with h | h
      · exact absurd h h0
      · rw [if_pos h]; exact ⟨x, by simp [TetraBFT.castVote]⟩

theorem voteKSt_votes {k : ℕ} {s : St n V}
    (hq : (quorumVal prm.f s.rcv (k - 1) s.view).isSome) :
    ∃ y, (⟨k, s.view, y⟩ : Vote V) ∈ (voteKSt prm k s).votes := by
  unfold TetraBFT.voteKSt
  split
  · rename_i h
    obtain ⟨w, hw, hw'⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw'
    exact ⟨w.val, by rw [← hw'.1, ← hw'.2]; exact hw⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hq
    rw [hx]
    exact ⟨x, by simp [TetraBFT.castVote]⟩

theorem decideSt_dec {s : St n V} (hq : (quorumVal prm.f s.rcv 4 s.view).isSome) :
    (decideSt prm s).dec ≠ none := by
  unfold TetraBFT.decideSt
  split
  · simp_all
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hq
    rw [hx]; simp

theorem mem_votes_of_voteExt {s s' : St n V} (h : VoteExt s s') {w : Vote V}
    (hw : w ∈ s.votes) : w ∈ s'.votes := by
  obtain ⟨l, hl, -⟩ := h.votes
  rw [hl]; exact List.mem_append_left _ hw

/-- Vote-1 in `post`. -/
theorem post_vote1 {p : Fin n} {s : St n V} {x : V}
    (hprop : firstFrom s.rcv (prm.leader s.view) (getProposal s.view) = some x)
    (hsafe : s.view = 0 ∨ nodeSafe prm s x) :
    ∃ y, (⟨1, s.view, y⟩ : Vote V) ∈ (post prm p s).votes := by
  have h1 := VoteExt.proposeSt prm p s
  have hrcv := h1.rcv
  have hview := h1.view
  obtain ⟨y, hy⟩ := vote1St_votes prm (s := proposeSt prm p s) (x := x)
    (by rw [hrcv, hview]; exact hprop)
    (by rw [hview]; simpa [nodeSafe, hrcv, hview] using hsafe)
  rw [hview] at hy
  refine ⟨y, mem_votes_of_voteExt ?_ hy⟩
  exact (((VoteExt.voteKSt prm 2 _).trans (.voteKSt prm 3 _)).trans (.voteKSt prm 4 _)).trans
    (.decideSt prm _)

/-- The state before the vote-`k` stage. -/
theorem post_voteK {p : Fin n} {s : St n V} {k : ℕ} (hk2 : 2 ≤ k) (hk4 : k ≤ 4)
    (hq : (quorumVal prm.f s.rcv (k - 1) s.view).isSome) :
    ∃ y, (⟨k, s.view, y⟩ : Vote V) ∈ (post prm p s).votes := by
  set s1 := vote1St prm (proposeSt prm p s)
  have h1 : VoteExt s s1 := (VoteExt.proposeSt prm p s).trans (.vote1St prm _)
  have key : ∀ (s' : St n V), VoteExt s s' → ∃ y, (⟨k, s.view, y⟩ : Vote V) ∈ (voteKSt prm k s').votes :=
    fun s' h => by
      obtain ⟨y, hy⟩ := voteKSt_votes prm (s := s') (k := k) (by rw [h.rcv, h.view]; exact hq)
      rw [h.view] at hy
      exact ⟨y, hy⟩
  interval_cases k
  · obtain ⟨y, hy⟩ := key s1 h1
    exact ⟨y, mem_votes_of_voteExt
      (((VoteExt.voteKSt prm 3 _).trans (.voteKSt prm 4 _)).trans (.decideSt prm _)) hy⟩
  · obtain ⟨y, hy⟩ := key _ (h1.trans (.voteKSt prm 2 _))
    exact ⟨y, mem_votes_of_voteExt ((VoteExt.voteKSt prm 4 _).trans (.decideSt prm _)) hy⟩
  · obtain ⟨y, hy⟩ := key _ ((h1.trans (.voteKSt prm 2 _)).trans (.voteKSt prm 3 _))
    exact ⟨y, mem_votes_of_voteExt (.decideSt prm _) hy⟩

theorem post_decide {p : Fin n} {s : St n V} (hq : (quorumVal prm.f s.rcv 4 s.view).isSome) :
    (post prm p s).dec ≠ none := by
  have h : VoteExt s (voteKSt prm 4 (voteKSt prm 3 (voteKSt prm 2 (vote1St prm
      (proposeSt prm p s))))) :=
    ((((VoteExt.proposeSt prm p s).trans (.vote1St prm _)).trans (.voteKSt prm 2 _)).trans
      (.voteKSt prm 3 _)).trans (.voteKSt prm 4 _)
  exact decideSt_dec prm (by rw [h.rcv, h.view]; exact hq)

/-! ### The view-change stages -/

theorem echoSt_out (s : St n V) : props (echoSt prm s).out = props s.out ∧
    (echoSt prm s).propView = s.propView ∧ (echoSt prm s).view = s.view := by
  unfold TetraBFT.echoSt; split
  · simp [props]
  · split <;> simp [props]

theorem viewSt_out (s : St n V) : props (viewSt prm s).out = props s.out ∧
    (viewSt prm s).propView = s.propView := by
  unfold TetraBFT.viewSt
  split
  · simp [props]
  · split <;> simp [props]

theorem viewSt_enter (s : St n V) (h : (viewSt prm s).view ≠ s.view) :
    (∃ rep, Msg.proof (viewSt prm s).view rep ∈ (viewSt prm s).out) ∧
    (∃ rep, Msg.suggest (viewSt prm s).view rep ∈ (viewSt prm s).out) := by
  revert h
  unfold TetraBFT.viewSt
  split
  · intro _; simp
  · split <;> simp

theorem preVote_props (s : St n V) (ib : Fin n → List (Msg V)) :
    props (preVote prm s ib).out = [] ∧ (preVote prm s ib).propView = s.propView := by
  have h1 := viewSt_out prm (echoSt prm (recvSt s ib))
  have h2 := echoSt_out prm (recvSt s ib)
  refine ⟨?_, ?_⟩
  · simp only [preVote, h1.1, h2.1]; simp [recvSt, props]
  · simp only [preVote, h1.2, h2.2.1]; rfl

theorem preVote_enter (s : St n V) (ib : Fin n → List (Msg V))
    (h : (preVote prm s ib).view ≠ s.view) :
    (∃ rep, Msg.proof (preVote prm s ib).view rep ∈ (preVote prm s ib).out) ∧
    (∃ rep, Msg.suggest (preVote prm s ib).view rep ∈ (preVote prm s ib).out) := by
  have h2 := (echoSt_out prm (recvSt s ib)).2.2
  apply viewSt_enter
  simp only [preVote] at h
  rw [h2]; exact h

end Stages

/-! ### Run-level facts -/

theorem firstFrom_isSome {α : Type} {rcv : List (Fin n × Msg V)} {q : Fin n}
    {g : Msg V → Option α} {m : Msg V} {a : α} (hm : (q, m) ∈ rcv) (hg : g m = some a) :
    (firstFrom rcv q g).isSome := by
  induction rcv with
  | nil => simp at hm
  | cons e l ih =>
    simp only [firstFrom, List.findSome?_cons]
    split
    · simp
    · rename_i h
      rcases List.mem_cons.1 hm with rfl | hm
      · simp [hg] at h
      · exact ih hm

theorem quorumVal_isSome {f : ℕ} {rcv : List (Fin n × Msg V)} {k v : ℕ} {x : V} (hf : f < n)
    (h : n - f ≤ (senders rcv (.vote k v x)).card) : (quorumVal f rcv k v).isSome := by
  obtain ⟨q, hq⟩ : (senders rcv (.vote k v x)).Nonempty := card_pos.1 (by omega)
  simp only [senders, mem_filter, mem_univ, true_and] at hq
  unfold quorumVal
  rw [List.find?_isSome]
  refine ⟨x, List.mem_filterMap.2 ⟨(q, .vote k v x), hq, by simp [getVote]⟩, ?_⟩
  simpa using h

section Run

variable {prm : Params n} (R : Run (Fin n) (Msg V) V)

local notation "A" => tetra (V := V) prm

/-- The working state of node `p` in the step at time `τ` (after receiving and view change). -/
noncomputable def work (prm : Params n) (R : Run (Fin n) (Msg V) V) (τ : ℕ) (p : Fin n) :
    St n V :=
  preVote prm (R.st (tetra prm) τ p) (R.inbox (tetra prm) p τ)

theorem st_step (τ : ℕ) (p : Fin n) : R.st A (τ + 1) p = post prm p (work prm R τ p) :=
  st_succ' R τ p

theorem work_rcv (τ : ℕ) (p : Fin n) : (work prm R τ p).rcv = (R.st A (τ + 1) p).rcv := by
  rw [st_step, (post_voteExt prm p _).rcv]

theorem work_view (τ : ℕ) (p : Fin n) : (work prm R τ p).view = (R.st A (τ + 1) p).view := by
  rw [st_step, (post_voteExt prm p _).view]

/-- **Delivery.** A message in the outbox of a correct node at time `τc` is in the received
messages of every correct node from time `max τc GST + δ + 1` on. -/
theorem deliver {t δ : ℕ} (hR : R.Valid t δ) {q j : Fin n} (hq : q ∉ R.faulty)
    (hj : j ∉ R.faulty) {τc : ℕ} {m : Msg V} (hm : m ∈ (R.st A τc q).out) {τ : ℕ}
    (hτ : max τc R.gst + δ ≤ τ) : (q, m) ∈ (R.st A (τ + 1) j).rcv :=
  tetra_logs.mem_log_of_valid R hR hq hj hm (by omega)

/-- A node in a view `v ≠ 0` has sent proof and suggest messages for `v` when entering it. -/
theorem entered {v : ℕ} (hv : v ≠ 0) {j : Fin n} :
    ∀ τ, (R.st A τ j).view = v → ∃ τe, τe + 1 ≤ τ ∧
      (∃ rep, Msg.proof v rep ∈ (R.st A (τe + 1) j).out) ∧
      (∃ rep, Msg.suggest v rep ∈ (R.st A (τe + 1) j).out) := by
  intro τ
  induction τ with
  | zero => intro h; exact absurd h.symm (by simpa [tetra] using hv)
  | succ τ ih =>
    intro h
    by_cases h' : (R.st A τ j).view = v
    · obtain ⟨τe, hle, h1, h2⟩ := ih h'
      exact ⟨τe, by omega, h1, h2⟩
    · have hw : (work prm R τ j).view = v := by rw [work_view, h]
      have hne : (work prm R τ j).view ≠ (R.st A τ j).view := by rw [hw]; exact Ne.symm h'
      obtain ⟨⟨r1, h1⟩, ⟨r2, h2⟩⟩ := preVote_enter prm _ _ hne
      obtain ⟨l, hl⟩ := post_out prm j (work prm R τ j)
      refine ⟨τ, le_rfl, ⟨r1, ?_⟩, ⟨r2, ?_⟩⟩
      · rw [st_step, hl, ← hw]; exact List.mem_append_left _ h1
      · rw [st_step, hl, ← hw]; exact List.mem_append_left _ h2

theorem step_props (τ : ℕ) (p : Fin n) :
    (props (R.st A (τ + 1) p).out = [] ∧ (R.st A (τ + 1) p).propView = (R.st A τ p).propView) ∨
    ∃ x, props (R.st A (τ + 1) p).out = [((work prm R τ p).view, x)] ∧
      (R.st A (τ + 1) p).propView = some (work prm R τ p).view ∧
      (R.st A τ p).propView ≠ some (work prm R τ p).view := by
  have hp := preVote_props prm (R.st A τ p) (R.inbox A p τ)
  rw [st_step]
  rcases post_props prm p (work prm R τ p) hp.1 with ⟨h1, h2⟩ | ⟨x, h1, h2, h3⟩
  · exact Or.inl ⟨h1, h2.trans hp.2⟩
  · refine Or.inr ⟨x, h1, h2, ?_⟩
    rw [← hp.2]; exact h3

theorem propView_le (p : Fin n) : ∀ τ a, (R.st A τ p).propView = some a →
    a ≤ (R.st A τ p).view := by
  intro τ
  induction τ with
  | zero => intro a h; simp [tetra] at h
  | succ τ ih =>
    intro a h
    rcases step_props R τ p with ⟨-, h2⟩ | ⟨x, -, h2, -⟩
    · rw [h2] at h
      exact le_trans (ih a h) (st_view_mono R (Nat.le_succ τ) p)
    · rw [h2] at h
      obtain rfl := Option.some.inj h
      rw [work_view]

theorem propView_mono (p : Fin n) {τ τ' : ℕ} (hle : τ ≤ τ') {a : ℕ}
    (h : (R.st A τ p).propView = some a) : ∃ b, (R.st A τ' p).propView = some b ∧ a ≤ b := by
  induction hle with
  | refl => exact ⟨a, h, le_rfl⟩
  | step hle ih =>
    obtain ⟨b, hb, hab⟩ := ih
    rcases step_props R _ p with ⟨-, h2⟩ | ⟨x, -, h2, -⟩
    · exact ⟨b, by rw [h2, hb], hab⟩
    · refine ⟨_, h2, le_trans hab (le_trans (propView_le R p _ b hb) ?_)⟩
      rw [work_view]
      exact st_view_mono R (Nat.le_succ _) p

theorem prop_out {p : Fin n} {τ w : ℕ} {x : V} (h : Msg.proposal w x ∈ (R.st A τ p).out) :
    ∃ τ', τ = τ' + 1 ∧ props (R.st A τ p).out = [(w, x)] ∧
      (R.st A τ p).propView = some w ∧ (R.st A τ' p).propView ≠ some w ∧
      (R.st A τ p).view = w := by
  rcases τ with _ | τ
  · simp [tetra] at h
  · rcases step_props R τ p with ⟨h1, -⟩ | ⟨x', h1, h2, h3⟩
    · have := mem_props.2 h; rw [h1] at this; simp at this
    · have hm := mem_props.2 h
      rw [h1, List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨τ, rfl, h1, h2, h3, (work_view R τ p).symm⟩

/-- A correct leader proposes at most one value per view. -/
theorem proposal_unique {p : Fin n} {τ₁ τ₂ w : ℕ} {x y : V}
    (h₁ : Msg.proposal w x ∈ (R.st A τ₁ p).out) (h₂ : Msg.proposal w y ∈ (R.st A τ₂ p).out) :
    x = y := by
  obtain ⟨a, rfl, hp₁, hv₁, hn₁, hw₁⟩ := prop_out R h₁
  obtain ⟨b, rfl, hp₂, hv₂, hn₂, hw₂⟩ := prop_out R h₂
  have aux : ∀ a b, a < b → (R.st A (a + 1) p).propView = some w →
      (R.st A b p).propView ≠ some w → (R.st A (b + 1) p).view = w → False := by
    intro a b hab hva hnb hwb
    obtain ⟨c, hc, hwc⟩ := propView_mono R p (show a + 1 ≤ b by omega) hva
    have h1 := propView_le R p b c hc
    have h2 := st_view_mono (prm := prm) R (Nat.le_succ b) p
    rw [hwb] at h2
    have : c = w := by omega
    exact hnb (this ▸ hc)
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact (aux a b hab hv₁ hn₂ hw₂).elim
  · rw [hp₁] at hp₂
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hp₂
    exact hp₂.2
  · exact (aux b a hab hv₂ hn₁ hw₁).elim

theorem proposal_exists {p : Fin n} {w : ℕ} : ∀ τ, (R.st A τ p).propView = some w →
    ∃ τ' ≤ τ, ∃ x, Msg.proposal w x ∈ (R.st A τ' p).out := by
  intro τ
  induction τ with
  | zero => intro h; simp [tetra] at h
  | succ τ ih =>
    intro h
    rcases step_props R τ p with ⟨-, h2⟩ | ⟨x, h1, h2, -⟩
    · obtain ⟨τ', hle, x, hx⟩ := ih (by rw [← h2]; exact h)
      exact ⟨τ', by omega, x, hx⟩
    · rw [h2] at h
      obtain rfl := Option.some.inj h
      refine ⟨τ + 1, le_rfl, x, mem_props.1 ?_⟩
      rw [h1]; simp

/-- Every cast vote was sent. -/
theorem vote_sent {p : Fin n} : ∀ τ, ∀ w ∈ (R.st A τ p).votes,
    ∃ τc ≤ τ, Msg.vote w.phase w.view w.val ∈ (R.st A τc p).out := by
  intro τ
  induction τ with
  | zero => intro w hw; simp [tetra] at hw
  | succ τ ih =>
    intro w hw
    rw [st_step] at hw
    rcases post_votes prm p _ w hw with hw' | hw'
    · rw [show (work prm R τ p).votes = (R.st A τ p).votes from preVote_votes prm _ _] at hw'
      obtain ⟨τc, hle, h⟩ := ih w hw'
      exact ⟨τc, by omega, h⟩
    · exact ⟨τ + 1, le_rfl, by rw [st_step]; exact hw'⟩

end Run

/-! ### The synchronized view -/

/-- After GST, all correct nodes are in view `v` (with a correct leader) during
`[t0, t0 + 6(δ + 1)]`. -/
structure SyncView (prm : Params n) (R : Run (Fin n) (Msg V) V) (δ v t0 : ℕ) : Prop where
  hn : 3 * prm.f < n
  valid : R.Valid prm.f δ
  leader : prm.leader v ∉ R.faulty
  gst : R.gst ≤ t0
  view : ∀ p ∉ R.faulty, ∀ τ, t0 ≤ τ → τ ≤ t0 + 6 * (δ + 1) → (R.st (tetra prm) τ p).view = v

namespace SyncView

variable {prm : Params n} {R : Run (Fin n) (Msg V) V} {δ v t0 : ℕ} (H : SyncView prm R δ v t0)
include H

local notation "A" => tetra (V := V) prm

theorem card_faulty : R.faulty.card ≤ prm.f := H.valid.card_faulty

theorem work_view' {τ : ℕ} (h1 : t0 ≤ τ + 1) (h2 : τ + 1 ≤ t0 + 6 * (δ + 1)) {p : Fin n}
    (hp : p ∉ R.faulty) : (work prm R τ p).view = v := by
  rw [work_view, H.view p hp _ h1 h2]

/-- From time `t0 + δ + 1` on, every correct node has the proof and suggest messages for `v` of
all correct nodes. -/
theorem have_reports (hv : v ≠ 0) {q j : Fin n} (hq : q ∉ R.faulty) (hj : j ∉ R.faulty)
    {τ : ℕ} (hτ : t0 + δ ≤ τ) :
    q ∈ repSenders (R.st A (τ + 1) j).rcv (getProof v) ∧
    q ∈ repSenders (R.st A (τ + 1) j).rcv (getSuggest v) := by
  obtain ⟨τe, hle, ⟨r1, h1⟩, ⟨r2, h2⟩⟩ :=
    entered R hv t0 (H.view q hq t0 le_rfl (by omega))
  have hd : max (τe + 1) R.gst + δ ≤ τ := by have := H.gst; omega
  have m1 := deliver R H.valid hq hj h1 hd
  have m2 := deliver R H.valid hq hj h2 hd
  simp only [repSenders, mem_filter, mem_univ, true_and]
  exact ⟨firstFrom_isSome m1 (a := r1) (by simp [getProof]),
    firstFrom_isSome m2 (a := r2) (by simp [getSuggest])⟩

/-- The correct leader proposes by time `t0 + δ + 1`. -/
theorem leader_proposes : ∃ τp ≤ t0 + δ + 1, ∃ x,
    Msg.proposal v x ∈ (R.st A τp (prm.leader v)).out := by
  set ℓ := prm.leader v
  have hw := H.work_view' (τ := t0 + δ) (by omega) (by omega) H.leader
  have hpv : (R.st A (t0 + δ + 1) ℓ).propView = some v := by
    rw [st_step, ← hw]
    refine post_propose prm (by rw [hw]) ?_
    by_cases hv : v = 0
    · exact Or.inl (hw.trans hv)
    · refine Or.inr ?_
      have hview := H.view ℓ H.leader (t0 + δ + 1) (by omega) (by omega)
      obtain ⟨x, hx⟩ := leader_determines_safe R H.hn H.card_faulty (R.inp ℓ)
        (τ := t0 + δ + 1) (p := ℓ)
        (fun q hq => by rw [hview]; exact (H.have_reports hv hq H.leader le_rfl).2)
      refine ⟨x, ?_⟩
      unfold leaderSafe at hx ⊢
      rw [work_rcv, work_view]
      exact hx
  exact proposal_exists R _ hpv

/-- The leader's value. -/
noncomputable def val : V := Classical.choose (Classical.choose_spec H.leader_proposes).2

theorem val_spec : ∃ τp ≤ t0 + δ + 1, Msg.proposal v H.val ∈ (R.st A τp (prm.leader v)).out := by
  obtain ⟨hle, h⟩ := Classical.choose_spec H.leader_proposes
  exact ⟨_, hle, Classical.choose_spec h⟩

/-- All correct votes in view `v` carry the leader's value. -/
theorem vote_val {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) {j : Fin n} (hj : j ∉ R.faulty) {τ : ℕ}
    {y : V} (h : (⟨k, v, y⟩ : Vote V) ∈ (R.st A τ j).votes) : y = H.val := by
  obtain ⟨q, hq, τ', h'⟩ := Execution.exists_vote1 (E := toExec (prm := prm) R)
    (by simpa using H.hn) (toExec_safetyHyp R H.card_faulty) k hk1 hk4 hj ⟨τ, h⟩
  obtain ⟨-, -, -, -, hpr⟩ := (st_inv (prm := prm) R τ' q).just _ h'
  obtain ⟨τ'', -, hm⟩ := rcv_authentic R H.leader (hpr rfl)
  obtain ⟨τp, -, hp⟩ := H.val_spec
  exact proposal_unique R hm hp

/-- Every correct node casts vote-1 by time `t0 + 2δ + 2`. -/
theorem vote1 {j : Fin n} (hj : j ∉ R.faulty) :
    ∃ y, (⟨1, v, y⟩ : Vote V) ∈ (R.st A (t0 + 2 * δ + 2) j).votes := by
  set ℓ := prm.leader v
  set S2 := t0 + 2 * δ + 1
  have hw := H.work_view' (τ := S2) (by omega) (by omega) hj
  have hview := H.view j hj (S2 + 1) (by omega) (by omega)
  obtain ⟨τp, hτp, hp⟩ := H.val_spec
  have hm : (ℓ, Msg.proposal v H.val) ∈ (R.st A (S2 + 1) j).rcv :=
    deliver R H.valid H.leader hj hp (by have := H.gst; omega)
  obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.1
    (firstFrom_isSome (g := getProposal v) (a := H.val) hm (by simp [getProposal]))
  have hx'eq : x' = H.val := by
    obtain ⟨τ', -, h'⟩ := rcv_authentic R H.leader (mem_of_firstFrom_proposal hx')
    exact proposal_unique R h' hp
  subst hx'eq
  rw [show S2 + 1 = t0 + 2 * δ + 2 by omega] at hview hm
  rw [show t0 + 2 * δ + 2 = S2 + 1 by omega, st_step]
  rw [← hw]
  refine post_vote1 prm (x := H.val) ?_ ?_
  · rw [work_rcv, hw, show S2 + 1 = t0 + 2 * δ + 2 by omega]; exact hx'
  · by_cases hv : v = 0
    · exact Or.inl (hw.trans hv)
    · refine Or.inr ?_
      have hsafe := follower_determines_safe R H.hn H.card_faulty (τ := S2 + 1) (j := j)
        (x := H.val) (by rw [show S2 + 1 = t0 + 2 * δ + 2 by omega, hview]; exact hv)
        (by rw [show S2 + 1 = t0 + 2 * δ + 2 by omega, hview]; exact H.leader)
        (by rw [show S2 + 1 = t0 + 2 * δ + 2 by omega, hview]; exact hm)
        (fun q hq => by
          rw [show S2 + 1 = t0 + 2 * δ + 2 by omega, hview]
          exact (H.have_reports hv hq hj (τ := S2) (by omega)).1)
      unfold nodeSafe at hsafe ⊢
      rw [work_rcv, work_view]
      exact hsafe

/-- The votes of phase `k` of all correct nodes are in every correct node's received messages
`δ + 1` time units later. -/
theorem quorum_after {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) {τ : ℕ} (hτ : t0 ≤ τ)
    (hall : ∀ q ∉ R.faulty, ∃ y, (⟨k, v, y⟩ : Vote V) ∈ (R.st A τ q).votes) {j : Fin n}
    (hj : j ∉ R.faulty) :
    (quorumVal prm.f (R.st A (τ + δ + 1) j).rcv k v).isSome := by
  refine quorumVal_isSome (x := H.val) (by have := H.hn; omega) ?_
  have hC := Execution.card_correct (toExec_safetyHyp (prm := prm) R H.card_faulty)
  simp only [Fintype.card_fin] at hC
  refine le_trans hC (card_le_card fun q hq => ?_)
  have hqF : q ∉ R.faulty := (mem_filter.1 hq).2
  obtain ⟨y, hy⟩ := hall q hqF
  have hyv := H.vote_val hk1 hk4 hqF hy
  subst hyv
  obtain ⟨τc, hτc, hm⟩ := vote_sent R τ _ hy
  simp only [senders, mem_filter, mem_univ, true_and]
  exact deliver R H.valid hqF hj hm (by have := H.gst; omega)

/-- One voting phase takes `δ + 1` time units. -/
theorem hop {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) {τ : ℕ} (hτ : t0 ≤ τ)
    (hτK : τ + δ + 1 ≤ t0 + 6 * (δ + 1))
    (hall : ∀ q ∉ R.faulty, ∃ y, (⟨k, v, y⟩ : Vote V) ∈ (R.st A τ q).votes) :
    ∀ j ∉ R.faulty, ∃ y, (⟨k + 1, v, y⟩ : Vote V) ∈ (R.st A (τ + δ + 1) j).votes := by
  intro j hj
  have hw := H.work_view' (τ := τ + δ) (by omega) (by omega) hj
  rw [st_step, ← hw]
  refine post_voteK prm (by omega) (by omega) ?_
  rw [work_rcv, hw, show k + 1 - 1 = k by omega]
  exact H.quorum_after hk1 (by omega) hτ hall hj

/-- **Lemma 5 with timing.** Every correct node has decided by time `t0 + 6(δ + 1)`. -/
theorem decided {j : Fin n} (hj : j ∉ R.faulty) :
    (R.st A (t0 + 6 * (δ + 1)) j).dec ≠ none := by
  have h1 : ∀ q ∉ R.faulty, ∃ y, (⟨1, v, y⟩ : Vote V) ∈ (R.st A (t0 + 2 * δ + 2) q).votes :=
    fun q hq => H.vote1 hq
  have h2 := H.hop le_rfl (by omega) (by omega) (by omega) h1
  have h3 := H.hop (k := 2) (by omega) (by omega) (by omega) (by omega) h2
  have h4 := H.hop (k := 3) (by omega) (by omega) (by omega) (by omega) h3
  set τ := t0 + 2 * δ + 2 + δ + 1 + δ + 1 + δ + 1
  have hw := H.work_view' (τ := τ + δ) (by omega) (by omega) hj
  rw [show t0 + 6 * (δ + 1) = τ + δ + 1 by omega, st_step]
  refine post_decide prm ?_
  rw [work_rcv, hw]
  exact H.quorum_after (k := 4) (by omega) le_rfl (by omega) h4 hj

end SyncView

/-- **Liveness within a synchronized view** (Lemmas 2, 4, 5 and the timing of a view). Let
`3f < n`, let the run be valid with delay bound `δ`, and suppose that after GST, during
`[t0, t0 + 6(δ + 1)]`, all correct nodes are in the same view `v`, whose leader is correct. Then
every correct node has decided by time `t0 + 6(δ + 1)`. -/
theorem decides_of_synchronized_view {prm : Params n} {R : Run (Fin n) (Msg V) V} {δ v t0 : ℕ}
    (hn : 3 * prm.f < n) (hR : R.Valid prm.f δ) (hℓ : prm.leader v ∉ R.faulty)
    (hgst : R.gst ≤ t0)
    (hview : ∀ p ∉ R.faulty, ∀ τ, t0 ≤ τ → τ ≤ t0 + 6 * (δ + 1) →
      (R.st (tetra prm) τ p).view = v) :
    ∀ p ∉ R.faulty, (R.st (tetra prm) (t0 + 6 * (δ + 1)) p).dec ≠ none ∧
      ∃ x, R.Decides (tetra prm) p x := by
  intro p hp
  have hd := (SyncView.mk hn hR hℓ hgst hview).decided hp
  refine ⟨hd, ?_⟩
  obtain ⟨⟨x, w⟩, hx⟩ := Option.ne_none_iff_exists'.1 hd
  exact ⟨x, t0 + 6 * (δ + 1), by change Option.map Prod.fst _ = _; rw [hx]; rfl⟩

/-- Under the same hypotheses all correct nodes decide, and on the same value. -/
theorem decide_same_of_synchronized_view {prm : Params n} {R : Run (Fin n) (Msg V) V}
    {δ v t0 : ℕ} (hn : 3 * prm.f < n) (hR : R.Valid prm.f δ) (hℓ : prm.leader v ∉ R.faulty)
    (hgst : R.gst ≤ t0)
    (hview : ∀ p ∉ R.faulty, ∀ τ, t0 ≤ τ → τ ≤ t0 + 6 * (δ + 1) →
      (R.st (tetra prm) τ p).view = v) :
    ∃ x, ∀ p ∉ R.faulty, R.Decides (tetra prm) p x ∧ ∀ y, R.Decides (tetra prm) p y → y = x := by
  have hC := Execution.card_correct (toExec_safetyHyp (prm := prm) R hR.card_faulty)
  simp only [Fintype.card_fin] at hC
  obtain ⟨p₀, hp₀⟩ : (univ.filter (· ∉ (toExec (prm := prm) R).faulty)).Nonempty :=
    card_pos.1 (by omega)
  replace hp₀ : p₀ ∉ R.faulty := (mem_filter.1 hp₀).2
  · obtain ⟨x, hx⟩ := (decides_of_synchronized_view hn hR hℓ hgst hview p₀ hp₀).2
    refine ⟨x, fun p hp => ?_⟩
    obtain ⟨y, hy⟩ := (decides_of_synchronized_view hn hR hℓ hgst hview p hp).2
    have hxy := tetra_agreement R hn hR.card_faulty hp₀ hp hx hy
    subst hxy
    exact ⟨hy, fun z hz => (tetra_agreement R hn hR.card_faulty hp₀ hp hx hz).symm⟩

end TetraBFT
