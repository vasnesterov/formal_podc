import Papers.PODC2021.GoodCaseLatencyBB.Basic

/-!
# The 2-round-BRB protocol (Figure 1, Theorem 5)

Abraham, Nayak, Ren, Xiang, *Good-case Latency of Byzantine Broadcast: a Complete
Categorization*, PODC 2021, Section 3.

The protocol (`n ≥ 3f + 1`, asynchronous, authenticated):
1. *Propose.* The broadcaster `s` with input `v` sends `⟨propose, v⟩_s` to all parties.
2. *Vote.* On the first proposal of `s`, send `⟨vote, v⟩_i` to all parties.
3. *Commit.* On `n − f` signed votes for `v`, forward them, commit `v` (and terminate).

## Implementation in `Cslib.Byzantine.PartialSync`

* Tokens `Tok P V`: proposals `prop p v` and votes `vote p v`, both signed by `p`.
* Messages are finite sets of tokens (`auth.tokens m = ↑m`). Every process keeps the set `known`
  of all tokens it has received or created and **gossips** it to everybody at every time step
  (this subsumes "send the proposal / vote to all" and "forward the `n − f` votes").
* At each step, after adding the received tokens, a process that has not voted yet and knows a
  proposal of `s` votes for it ("first proposal": if several proposals of `s` arrive at the same
  step, a classical choice breaks the tie). The broadcaster starts knowing its own proposal.
* A process has committed `v` as soon as its `known` contains `n − f` votes for `v`
  (`decide` is read off the state; termination of sending is irrelevant for the properties).

## Main results

* `algo_unforging`: correct processes only emit their own tokens and relay received ones.
* `theorem_5_brb`: Byzantine reliable broadcast in all asynchronous runs (`asyncRuns f`).
* `theorem_5_latency`: good-case latency `2Δ` in synchronous runs with delay bound `Δ`.

The generic `Run.honestTokens_origin` (a token emitted by a correct process and signed by a
correct process `q` was emitted by `q` itself, at the same time or earlier) is a CSLib candidate.
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset

/-! ### Token origin (generic) -/

section Origin

variable {P M S VI VO K : Type*} [DecidableEq P]

-- CSLib candidate
/-- **Token origin.** In a run respecting unforgeability of an unforging algorithm, a token
emitted by a correct process by time `τ` is signed by a Byzantine process, or was emitted by its
(correct) signer itself by time `τ`. -/
theorem Run.honestTokens_origin {Au : Auth P M K} {A : Algorithm P M S VI VO}
    (hU : A.Unforging Au) {R : Run P M VI} (hR : R.AuthValid Au A) {τ : ℕ} {x : K}
    (hx : x ∈ R.honestTokens Au A τ) :
    Au.signer x ∈ R.faulty ∨ ∃ τ' ≤ τ, ∃ r, ∃ m ∈ R.out A (Au.signer x) τ' r, x ∈ Au.tokens m := by
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    obtain ⟨τ₁, hτ₁, q, hq, r, m, hm, hxm⟩ := hx
    have hm' := hm
    rw [Run.out_of_correct A R hq] at hm'
    rcases hU R q τ₁ r m hm' x hxm with hs | ⟨τ₂, hτ₂, q', m', hm₂, hx₂⟩
    · exact Or.inr ⟨τ₁, hτ₁, r, m, hs ▸ hm, hxm⟩
    · obtain ⟨σ, hσ, -, hm₃⟩ := Run.mem_inbox.mp hm₂
      have hh : Au.signer x ∈ R.faulty ∨ x ∈ R.honestTokens Au A σ := by
        by_cases hq' : q' ∈ R.faulty
        · rw [Run.out_of_faulty A R hq'] at hm₃
          exact hR q' hq' σ q hq m' hm₃ x hx₂
        · exact Or.inr ⟨σ, le_rfl, q', hq', q, m', hm₃, hx₂⟩
      rcases hh with h | h
      · exact Or.inl h
      · rcases ih σ (by omega) h with h' | ⟨τ', hτ', r', m'', hm'', hx''⟩
        · exact Or.inl h'
        · exact Or.inr ⟨τ', by omega, r', m'', hm'', hx''⟩

end Origin

namespace BRB

/-! ### The protocol -/

/-- Signed statements: `prop p v` (a proposal of `v`) and `vote p v`, both signed by `p`. -/
inductive Tok (P V : Type*) where
  | prop (p : P) (v : V)
  | vote (p : P) (v : V)
  deriving DecidableEq

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- The signer of a token. -/
def Tok.signer : Tok P V → P
  | .prop p _ => p
  | .vote p _ => p

/-- Ideal signatures: a message is a finite set of tokens and carries exactly these tokens. -/
def auth : Auth P (Finset (Tok P V)) (Tok P V) where
  signer := Tok.signer
  tokens m := ↑m

section Defs

variable (s : P) (f : ℕ)

open Classical in
/-- **Vote** (step 2): if `p` has not voted yet and knows a proposal of `s`, it votes for it
(ties between several proposals learnt at the same step are broken by a fixed choice). -/
noncomputable def voteAct (p : P) (K : Finset (Tok P V)) : Finset (Tok P V) :=
  if h : (∀ v, Tok.vote p v ∉ K) ∧ ∃ v, Tok.prop s v ∈ K then insert (Tok.vote p h.2.choose) K
  else K

/-- All tokens of all received messages. -/
def received (ib : P → List (Finset (Tok P V))) : Finset (Tok P V) :=
  univ.biUnion fun q => (ib q).toFinset.biUnion id

/-- `K` contains `n − f` votes for `v`. -/
def Quorum (K : Finset (Tok P V)) (v : V) : Prop :=
  Fintype.card P - f ≤ (univ.filter fun q => Tok.vote q v ∈ K).card

open Classical in
/-- **The 2-round-BRB protocol** (Figure 1) with broadcaster `s`, for at most `f` faults. The
state is the set of known tokens; it is gossiped to everybody at every step. -/
noncomputable def algo : Algorithm P (Finset (Tok P V)) (Finset (Tok P V)) V V where
  init p x := if p = s then {Tok.prop s x} else ∅
  step p K ib := voteAct s p (K ∪ received ib)
  send _ K _ := [K]
  decide _ K := if h : ∃ v, Quorum f K v then some h.choose else none

end Defs

variable {s : P} {f : ℕ}

/-! ### The local step -/

theorem subset_voteAct (p : P) (K : Finset (Tok P V)) : K ⊆ voteAct s p K := by
  unfold voteAct; split_ifs
  · exact subset_insert _ _
  · exact subset_rfl

theorem mem_voteAct {p : P} {K : Finset (Tok P V)} {k : Tok P V} (hk : k ∈ voteAct s p K) :
    k ∈ K ∨ ∃ u, k = Tok.vote p u ∧ Tok.prop s u ∈ K ∧ ∀ v, Tok.vote p v ∉ K := by
  unfold voteAct at hk; split_ifs at hk with h
  · rcases mem_insert.mp hk with hk | hk
    · exact Or.inr ⟨_, hk, h.2.choose_spec, h.1⟩
    · exact Or.inl hk
  · exact Or.inl hk

theorem voteAct_vote {p : P} {K : Finset (Tok P V)} (h : ∃ v, Tok.prop s v ∈ K) :
    ∃ u, Tok.vote p u ∈ voteAct s p K := by
  by_cases h' : ∃ u, Tok.vote p u ∈ K
  · obtain ⟨u, hu⟩ := h'; exact ⟨u, subset_voteAct p K hu⟩
  · simp only [not_exists] at h'
    unfold voteAct
    split_ifs with hh
    · exact ⟨_, mem_insert_self _ _⟩
    · exact absurd ⟨h', h⟩ hh

theorem voteAct_unique {p : P} {K : Finset (Tok P V)}
    (hK : ∀ v w, Tok.vote p v ∈ K → Tok.vote p w ∈ K → v = w) :
    ∀ v w, Tok.vote p v ∈ voteAct s p K → Tok.vote p w ∈ voteAct s p K → v = w := by
  intro v w hv hw
  unfold voteAct at hv hw
  split_ifs at hv hw with h
  · rcases mem_insert.mp hv with hv | hv <;> rcases mem_insert.mp hw with hw | hw
    · cases hv; cases hw; rfl
    · exact absurd hw (h.1 w)
    · exact absurd hv (h.1 v)
    · exact hK v w hv hw
  · exact hK v w hv hw

theorem mem_received {ib : P → List (Finset (Tok P V))} {k : Tok P V} :
    k ∈ received ib ↔ ∃ r, ∃ m ∈ ib r, k ∈ m := by
  simp [received]

variable (R : Run P (Finset (Tok P V)) V)

theorem st_succ_eq (τ : ℕ) (q : P) :
    R.st (algo s f) (τ + 1) q =
      voteAct s q (R.st (algo s f) τ q ∪ received (R.inbox (algo s f) q τ)) :=
  R.st_succ _ τ q

theorem st_zero_eq (q : P) :
    R.st (algo s f) 0 q = if q = s then {Tok.prop s (R.inp q)} else ∅ := rfl

theorem known_mono {τ τ' : ℕ} (h : τ ≤ τ') (q : P) :
    R.st (algo s f) τ q ⊆ R.st (algo s f) τ' q := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih =>
    refine ih.trans ?_
    rw [st_succ_eq]
    exact subset_union_left.trans (subset_voteAct _ _)

theorem mem_known_of_inbox {τ : ℕ} {q r : P} {m : Finset (Tok P V)}
    (hm : m ∈ R.inbox (algo s f) q τ r) {k : Tok P V} (hk : k ∈ m) :
    k ∈ R.st (algo s f) (τ + 1) q := by
  rw [st_succ_eq]
  exact subset_voteAct _ _ (mem_union_right _ (mem_received.mpr ⟨r, m, hm, hk⟩))

theorem out_correct {q : P} (hq : q ∉ R.faulty) (τ : ℕ) (r : P) :
    R.out (algo s f) q τ r = [R.st (algo s f) τ q] :=
  R.out_of_correct _ hq τ r

/-! ### Unforgeability and the origin of tokens -/

/-- Correct processes only emit their own tokens and relay received ones. -/
theorem algo_unforging : (algo (V := V) s f).Unforging auth := by
  intro R p τ q m hm x hx
  have hm' : m = R.st (algo s f) τ p := by simpa [algo] using hm
  subst hm'
  change x ∈ R.st (algo s f) τ p at hx
  clear hm
  induction τ generalizing x with
  | zero =>
    left
    rw [st_zero_eq] at hx
    split_ifs at hx with h
    · rw [mem_singleton] at hx; subst hx; exact h.symm
    · simp at hx
  | succ τ ih =>
    rw [st_succ_eq] at hx
    rcases mem_voteAct hx with hx | ⟨u, rfl, -, -⟩
    · rcases mem_union.mp hx with hx | hx
      · rcases ih x hx with h | ⟨τ', hτ', r', m', hm', hx'⟩
        · exact Or.inl h
        · exact Or.inr ⟨τ', by omega, r', m', hm', hx'⟩
      · obtain ⟨r, m, hm, hk⟩ := mem_received.mp hx
        exact Or.inr ⟨τ, by omega, r, m, hm, hk⟩
    · exact Or.inl rfl

variable {R}

/-- What a correct process knows, it has emitted. -/
theorem known_honest {q : P} (hq : q ∉ R.faulty) {τ : ℕ} {x : Tok P V}
    (hx : x ∈ R.st (algo s f) τ q) : x ∈ R.honestTokens auth (algo s f) τ :=
  ⟨τ, le_rfl, q, hq, q, _, by rw [out_correct R hq]; exact List.mem_singleton_self _, hx⟩

/-- A token emitted by correct processes and signed by a correct `q` is known to `q`. -/
theorem honest_known (hR : R.AuthValid auth (algo s f)) {q : P} (hq : q ∉ R.faulty) {τ : ℕ}
    {x : Tok P V} (hx : x ∈ R.honestTokens auth (algo s f) τ) (hs : x.signer = q) :
    x ∈ R.st (algo s f) τ q := by
  rcases Run.honestTokens_origin algo_unforging hR hx with h | ⟨τ', hτ', r, m, hm, hxm⟩
  · exact absurd (hs ▸ h) hq
  · have hs' : auth.signer x = q := hs
    rw [hs', out_correct R hq] at hm
    rw [List.mem_singleton.mp hm] at hxm
    exact known_mono R hτ' q hxm

/-- A token known to a correct process and signed by a correct `q` is known to `q`. -/
theorem known_signed (hR : R.AuthValid auth (algo s f)) {c q : P} (hc : c ∉ R.faulty)
    (hq : q ∉ R.faulty) {τ : ℕ} {x : Tok P V} (hx : x ∈ R.st (algo s f) τ c)
    (hs : x.signer = q) : x ∈ R.st (algo s f) τ q :=
  honest_known hR hq (known_honest hc hx) hs

/-- A token received by a correct process at `τ` and signed by a correct `q` is known to `q`
at `τ`. -/
theorem recv_signed (hR : R.AuthValid auth (algo s f)) {c q : P} (hc : c ∉ R.faulty)
    (hq : q ∉ R.faulty) {τ : ℕ} {x : Tok P V}
    (hx : x ∈ received (R.inbox (algo s f) c τ)) (hs : x.signer = q) :
    x ∈ R.st (algo s f) τ q := by
  obtain ⟨r, m, hm, hxm⟩ := mem_received.mp hx
  obtain ⟨σ, hσ, -, hm'⟩ := Run.mem_inbox.mp hm
  refine known_mono R hσ q (honest_known hR hq ?_ hs)
  by_cases hr : r ∈ R.faulty
  · rw [Run.out_of_faulty _ _ hr] at hm'
    rcases hR r hr σ c hc m hm' x hxm with h | h
    · exact absurd (hs ▸ h) hq
    · exact h
  · rw [out_correct R hr] at hm'
    rw [List.mem_singleton.mp hm'] at hxm
    exact known_honest hr hxm

/-- An own token of a correct process present before its vote action is already known to it. -/
theorem own_of_union (hR : R.AuthValid auth (algo s f)) {c : P} (hc : c ∉ R.faulty) {τ : ℕ}
    {x : Tok P V}
    (hx : x ∈ R.st (algo s f) τ c ∪ received (R.inbox (algo s f) c τ)) (hs : x.signer = c) :
    x ∈ R.st (algo s f) τ c := by
  rcases mem_union.mp hx with hx | hx
  · exact hx
  · exact recv_signed hR hc hc hx hs

/-! ### Invariants of correct processes -/

/-- A correct process votes at most once. -/
theorem vote_unique (hR : R.AuthValid auth (algo s f)) {c : P} (hc : c ∉ R.faulty) (τ : ℕ) :
    ∀ v w, Tok.vote c v ∈ R.st (algo s f) τ c → Tok.vote c w ∈ R.st (algo s f) τ c → v = w := by
  induction τ with
  | zero =>
    intro v w hv _
    rw [st_zero_eq] at hv
    split_ifs at hv <;> simp at hv
  | succ τ ih =>
    rw [st_succ_eq]
    exact voteAct_unique fun v w hv hw =>
      ih v w (own_of_union hR hc hv rfl) (own_of_union hR hc hw rfl)

/-- A correct process only votes for a proposal of `s` it knows. -/
theorem vote_prop (hR : R.AuthValid auth (algo s f)) {c : P} (hc : c ∉ R.faulty) {τ : ℕ}
    {w : V} (h : Tok.vote c w ∈ R.st (algo s f) τ c) : Tok.prop s w ∈ R.st (algo s f) τ c := by
  induction τ with
  | zero =>
    rw [st_zero_eq] at h
    split_ifs at h <;> simp at h
  | succ τ ih =>
    have h' := h
    rw [st_succ_eq] at h'
    rcases mem_voteAct h' with h' | ⟨u, hu, hp, -⟩
    · exact known_mono R (Nat.le_succ τ) c (ih (own_of_union hR hc h' rfl))
    · cases hu
      rw [st_succ_eq]; exact subset_voteAct _ _ hp

/-- A correct broadcaster only proposes its input. -/
theorem prop_input (hR : R.AuthValid auth (algo s f)) (hs : s ∉ R.faulty) {τ : ℕ} {w : V}
    (h : Tok.prop s w ∈ R.st (algo s f) τ s) : w = R.inp s := by
  induction τ with
  | zero =>
    rw [st_zero_eq] at h
    simp only [ite_true, mem_singleton] at h
    cases h; rfl
  | succ τ ih =>
    rw [st_succ_eq] at h
    rcases mem_voteAct h with h | ⟨u, hu, -, -⟩
    · exact ih (own_of_union hR hs h rfl)
    · cases hu

/-- From time `1` on, a process that knows a proposal of `s` has voted. -/
theorem vote_of_prop {r : P} {τ : ℕ} {w : V} (h : Tok.prop s w ∈ R.st (algo s f) (τ + 1) r) :
    ∃ u, Tok.vote r u ∈ R.st (algo s f) (τ + 1) r := by
  rw [st_succ_eq] at h ⊢
  rcases mem_voteAct h with h | ⟨u, hu, -, -⟩
  · exact voteAct_vote ⟨w, h⟩
  · cases hu

/-- With an honest broadcaster, correct processes only vote for its input. -/
theorem vote_input (hR : R.AuthValid auth (algo s f)) (hs : s ∉ R.faulty) {c : P}
    (hc : c ∉ R.faulty) {τ : ℕ} {w : V} (h : Tok.vote c w ∈ R.st (algo s f) τ c) :
    w = R.inp s :=
  prop_input hR hs (known_signed hR hc hs (vote_prop hR hc h) rfl)

/-! ### Quorums -/

theorem Quorum.mono {K K' : Finset (Tok P V)} (h : K ⊆ K') {v : V} (hq : Quorum f K v) :
    Quorum f K' v :=
  hq.trans (card_le_card fun c hc => by
    simp only [mem_filter] at hc ⊢; exact ⟨hc.1, h hc.2⟩)

theorem quorum_of_correct {K : Finset (Tok P V)} {v : V} (hcard : R.faulty.card ≤ f)
    (h : ∀ c ∉ R.faulty, Tok.vote c v ∈ K) : Quorum f K v := by
  have hsub : R.faultyᶜ ⊆ univ.filter fun q => Tok.vote q v ∈ K := fun c hc =>
    mem_filter.mpr ⟨mem_univ _, h c (mem_compl.mp hc)⟩
  have := card_le_card hsub
  rw [card_compl] at this
  unfold Quorum; omega

/-- A quorum contains the vote of a correct process (`n − f > f`). -/
theorem Quorum.exists_correct {K : Finset (Tok P V)} {v : V} (hq : Quorum f K v)
    (hcard : R.faulty.card ≤ f) (hn : 2 * f < Fintype.card P) :
    ∃ c ∉ R.faulty, Tok.vote c v ∈ K := by
  obtain ⟨c, hc, hcf⟩ := exists_mem_notMem_of_card_lt_card (t := univ.filter
    fun q => Tok.vote q v ∈ K) (s := R.faulty) (by unfold Quorum at hq; omega)
  exact ⟨c, hcf, (mem_filter.mp hc).2⟩

/-- **Quorum intersection**: two quorums share the vote of a correct process (`n ≥ 3f + 1`). -/
theorem Quorum.inter_correct {K K' : Finset (Tok P V)} {v w : V} (hq : Quorum f K v)
    (hq' : Quorum f K' w) (hcard : R.faulty.card ≤ f) (hn : 3 * f + 1 ≤ Fintype.card P) :
    ∃ c ∉ R.faulty, Tok.vote c v ∈ K ∧ Tok.vote c w ∈ K' := by
  unfold Quorum at hq hq'
  set Q := univ.filter fun q => Tok.vote q v ∈ K
  set Q' := univ.filter fun q => Tok.vote q w ∈ K'
  have h1 := card_inter_add_card_union Q Q'
  have h2 : (Q ∪ Q').card ≤ Fintype.card P := card_le_univ _
  obtain ⟨c, hc, hcf⟩ := exists_mem_notMem_of_card_lt_card (t := Q ∩ Q') (s := R.faulty)
    (by omega)
  rw [mem_inter] at hc
  exact ⟨c, hcf, (mem_filter.mp hc.1).2, (mem_filter.mp hc.2).2⟩

theorem decide_spec {p : P} {K : Finset (Tok P V)} {v : V}
    (h : (algo s f).decide p K = some v) : Quorum f K v := by
  simp only [algo] at h
  split_ifs at h with hq
  · cases h; exact hq.choose_spec

theorem decide_of_quorum (p : P) {K : Finset (Tok P V)} {v : V} (h : Quorum f K v) :
    ∃ w, (algo s f).decide p K = some w := by
  simp only [algo]
  split_ifs with hh
  · exact ⟨_, rfl⟩
  · exact absurd ⟨v, h⟩ hh

/-- With an honest broadcaster, a correct process only commits the broadcaster's input. -/
theorem decide_input (hR : R.AuthValid auth (algo s f)) (hs : s ∉ R.faulty)
    (hcard : R.faulty.card ≤ f) (hn : 2 * f < Fintype.card P) {p : P} (hp : p ∉ R.faulty)
    {τ : ℕ} {w : V} (h : (algo s f).decide p (R.st (algo s f) τ p) = some w) : w = R.inp s := by
  obtain ⟨c, hc, hcv⟩ := (decide_spec h).exists_correct hcard hn
  exact vote_input hR hs hc (known_signed hR hp hc hcv rfl)

/-! ### Gossip -/

/-- A correct process learns everything a correct process knew when the batch is delivered. -/
theorem gossip {q r : P} (hq : q ∉ R.faulty) {τ : ℕ} (hdl : τ ≤ R.dl q τ r) :
    R.st (algo s f) τ q ⊆ R.st (algo s f) (R.dl q τ r + 1) r := by
  intro k hk
  refine mem_known_of_inbox R (r := q) (m := R.st (algo s f) τ q) ?_ hk
  exact Run.mem_inbox.mpr ⟨τ, hdl, rfl, by rw [out_correct R hq]; exact List.mem_singleton_self _⟩

theorem gossip_valid {D : ℕ} (hV : R.Valid f D) {q r : P} (hq : q ∉ R.faulty)
    (hr : r ∉ R.faulty) (τ : ℕ) :
    R.st (algo s f) τ q ⊆ R.st (algo s f) (max τ R.gst + D + 1) r :=
  (gossip hq (hV.dl_ge q τ r hq hr)).trans
    (known_mono R (by have := hV.dl_le q τ r hq hr; omega) r)

theorem gossip_sync {Δ : ℕ} (hV : SyncValid f Δ R) {q r : P} (hq : q ∉ R.faulty)
    (hr : r ∉ R.faulty) (τ : ℕ) : R.st (algo s f) τ q ⊆ R.st (algo s f) (τ + Δ) r :=
  (gossip hq (hV.dl_ge q τ r hq hr)).trans
    (known_mono R (by have := hV.dl_lt q τ r hq hr; omega) r)

/-! ### Theorem 5 -/

/-- Agreement (quorum intersection). -/
theorem agreement (hR : R.AuthValid auth (algo s f)) (hcard : R.faulty.card ≤ f)
    (hn : 3 * f + 1 ≤ Fintype.card P) {p q : P} (hp : p ∉ R.faulty) (hq : q ∉ R.faulty)
    {v w : V} (hv : R.Decides (algo s f) p v) (hw : R.Decides (algo s f) q w) : v = w := by
  obtain ⟨τ, hτ⟩ := hv
  obtain ⟨τ', hτ'⟩ := hw
  obtain ⟨c, hc, h1, h2⟩ := (decide_spec hτ).inter_correct (decide_spec hτ') hcard hn
  exact vote_unique hR hc (max τ τ') v w
    (known_mono R (le_max_left _ _) c (known_signed hR hp hc h1 rfl))
    (known_mono R (le_max_right _ _) c (known_signed hR hq hc h2 rfl))

/-- With an honest broadcaster, once every correct process knows the proposal (at some time
`τ + 1`), all correct processes have voted for the input. -/
theorem all_vote (hR : R.AuthValid auth (algo s f)) (hs : s ∉ R.faulty) {τ : ℕ}
    (h : ∀ c ∉ R.faulty, Tok.prop s (R.inp s) ∈ R.st (algo s f) (τ + 1) c) :
    ∀ c ∉ R.faulty, Tok.vote c (R.inp s) ∈ R.st (algo s f) (τ + 1) c := by
  intro c hc
  obtain ⟨u, hu⟩ := vote_of_prop (h c hc)
  rwa [← vote_input hR hs hc hu]

theorem prop_init : Tok.prop s (R.inp s) ∈ R.st (algo s f) 0 s := by
  rw [st_zero_eq]; simp

/-- **Theorem 5 (BRB).** For `n ≥ 3f + 1`, the 2-round-BRB protocol solves Byzantine reliable
broadcast in the asynchronous authenticated setting (all runs of the model, in which messages
between correct processes are eventually delivered). -/
theorem theorem_5_brb (hn : 3 * f + 1 ≤ Fintype.card P) :
    IsBRB auth (algo s f) s (asyncRuns (P := P) (V := V) f) where
  agreement := by
    rintro R ⟨D, hV⟩ hR p hp q hq v w hv hw
    exact agreement hR hV.card_faulty hn hp hq hv hw
  validity := by
    rintro R ⟨D, hV⟩ hR hs p hp
    have h1 : ∀ c ∉ R.faulty, Tok.prop s (R.inp s) ∈ R.st (algo s f) (max 0 R.gst + D + 1) c :=
      fun c hc => gossip_valid hV hs hc 0 prop_init
    have h2 := all_vote hR hs h1
    set T := max (max 0 R.gst + D + 1) R.gst + D + 1
    obtain ⟨w, hw⟩ := decide_of_quorum (s := s) p (quorum_of_correct (K :=
      R.st (algo s f) T p) (v := R.inp s) hV.card_faulty
      fun c hc => gossip_valid hV hc hp _ (h2 c hc))
    exact ⟨T, (decide_input hR hs hV.card_faulty (by omega) hp hw) ▸ hw⟩
  termination := by
    rintro R ⟨D, hV⟩ hR ⟨p, hp, v, τ, hτ⟩ r hr
    obtain ⟨w, hw⟩ := decide_of_quorum (s := s) r
      ((decide_spec hτ).mono (gossip_valid hV hp hr τ))
    exact ⟨w, _, hw⟩

/-- **Theorem 5 (good-case latency).** With an honest broadcaster and synchronous delays
`≤ Δ` (effective-delay convention of `SyncValid`), every correct process commits by time `2Δ`
(two rounds: proposal, votes). This part does not need `n ≥ 3f + 1`. -/
theorem theorem_5_latency :
    ∀ Δ ≥ 1, LatencyWithin auth (algo s f) s (syncRuns (P := P) (V := V) f Δ) (2 * Δ) := by
  intro Δ hΔ R hV hR hs p hp
  have hV : SyncValid f Δ R := hV
  obtain ⟨d, rfl⟩ : ∃ d, Δ = d + 1 := ⟨Δ - 1, by omega⟩
  have h1 : ∀ c ∉ R.faulty, Tok.prop s (R.inp s) ∈ R.st (algo s f) (d + 1) c := fun c hc => by
    simpa using gossip_sync hV hs hc 0 prop_init
  have h2 := all_vote hR hs h1
  obtain ⟨w, hw⟩ := decide_of_quorum (s := s) p (quorum_of_correct (K :=
    R.st (algo s f) (2 * (d + 1)) p) (v := R.inp s) hV.card_faulty
    fun c hc => by
      have := gossip_sync hV hc hp (d + 1) (h2 c hc)
      rwa [show d + 1 + (d + 1) = 2 * (d + 1) by omega] at this)
  exact ⟨w, 2 * (d + 1), le_rfl, hw⟩

end BRB

end GoodCaseLatencyBB
