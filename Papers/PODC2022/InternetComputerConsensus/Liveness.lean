import Papers.PODC2022.InternetComputerConsensus.Run

/-!
# Liveness of ICC0 under partial synchrony (Lemma "Liveness assuming partial synchrony", P3)

Paper statement [ICC, Section 4]. Assume that
(i) there are at most `t < n/3` corrupt parties, signatures are secure, and hash functions are
    collision resistant;
(ii) `k > 1`, the first honest party `P` to enter round `k` does so at time `T`, and all honest
    parties have been initiated at time `T`;
(iii) the leader `Q` of round `k` is honest;
(iv) the communication network is `δ`-synchronous at times `T` and `T + δ + Δprop(0)`;
(v) `2δ + Δprop(0) ≤ Δntry(1)`.
Then when all round-`k` messages from honest parties have been delivered to all honest parties,
each honest party will have `Q`'s round-`k` proposed block in its pool as a finalized block.

*Definition.* The network is `δ`-synchronous at time `T` if all messages that have been sent by
honest parties by time `T` arrive at their destinations before time `T + δ`.

We prove it for runs with the "wait for" semantics (`IsRun`), discrete time, `δ ≥ 1`, any
`k ≥ 1`, and the conclusion "every honest party has `Q`'s block `B_Q` valid in its pool together
with a full set of `n - t` finalization shares for it, has `kmax ≥ k`, and has committed `B_Q`
(the chain of `B_Q` is a prefix of its output)". The literal conclusion "a finalization of `B_Q`
is in every honest pool" can fail: a party whose `kmax` already passed `k` (because it saw the
round-`k+1` finalization shares first) never combines the round-`k` shares (see
`differencies.md`).
-/

namespace Podc.InternetComputerConsensus

open Finset Cslib.Byzantine

set_option linter.unusedSectionVars false

variable {P V : Type*} [Fintype P] [DecidableEq P] {π : Params P} {F : Finset P}

/-- The network is `δ`-synchronous at time `T₀` in the run `σ`: every message sent by an honest
party by time `T₀` is in every honest pool at every state of time `≥ T₀ + δ`. -/
def SyncAt (F : Finset P) (σ : ℕ → GState P V) (δ T₀ : ℕ) : Prop :=
  ∀ i i', (σ i).now ≤ T₀ → T₀ + δ ≤ (σ i').now → ∀ m ∈ (σ i).sent, ∀ q ∉ F,
    m ∈ ((σ i').loc q).pool

/-- Counting signers: if `s₁`-signers outside `F` are `s₂`-signers, a `Q`-certificate for `s₁`
gives a `(Q - f)`-certificate for `s₂`. -/
theorem certified_transfer {s₁ : P → α → Prop} {s₂ : P → β → Prop} {x : α} {y : β} {Q f : ℕ}
    (h : Certified s₁ Q x) (hF : #F ≤ f) (h12 : ∀ q ∉ F, s₁ q x → s₂ q y) :
    Certified s₂ (Q - f) y := by
  classical
  unfold Certified at *
  have : signers s₁ x ⊆ F ∪ signers s₂ y := by
    intro q hq
    by_cases hqF : q ∈ F
    · exact mem_union_left _ hqF
    · exact mem_union_right _ (mem_signers.2 (h12 q hqF (mem_signers.1 hq)))
  have := (card_le_card this).trans (card_union_le _ _)
  omega

/-- If an honest party has entered round `k`, every round `r ≤ k` has `t + 1` honest beacon
shares. -/
theorem Inv.beacon_cert {s : GState P V} (hI : Inv π F s) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {P₀ : P} (hP₀ : P₀ ∉ F) {k : ℕ} (hk : Entered s P₀ k)
    {r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ k) :
    Certified (fun q r => Msg.beacon r q ∈ s.sent) (π.t + 1) r := by
  rcases Nat.lt_or_ge 1 k with hk1 | hk1
  · -- the notarized round-`(k-1)` block has `n - 2t ≥ t + 1` honest signers
    have hround : k - 1 < (s.loc P₀).round := by
      unfold Entered at hk; rcases hk with h | ⟨h, -⟩ <;> omega
    obtain ⟨B, hBr, hBn⟩ := hI.finished P₀ hP₀ (k - 1) (by omega) hround
    have hcert := (hI.sent_notar B hBn).resolve_left (Block.ne_root_of_round (by omega))
    refine Certified.mono (certified_transfer (s₂ := fun q r => Msg.beacon r q ∈ s.sent) (y := r)
      hcert hF (fun q hq hs => ?_)) (fun _ h => h) (by omega)
    have hs := hs.resolve_left hq
    obtain ⟨-, -, -, h4, -⟩ := hI.share B q hs
    rw [hBr] at h4
    rcases h4 with h4 | ⟨h4, h4', -⟩
    · exact hI.beacon_sent q hq r hr1 (by omega)
    · rcases Nat.lt_or_ge r k with h5 | h5
      · exact hI.beacon_sent q hq r hr1 (by omega)
      · have : r = (s.loc q).round + 1 := by omega
        rw [this]; exact hI.beacon_active q hq h4'
  · have : r = 1 := by omega
    subst this
    exact (certified_of_forall_notMem (signed := fun q r => Msg.beacon r q ∈ s.sent) hF
      (fun q hq => hI.beacon_sent q hq 1 le_rfl (hI.round_pos q hq))).mono (fun _ h => h)
      (by omega)

/-- **Catching up.** If an honest party `P₀` has entered round `k` in `s₀`, and the honest party
`q` has received everything broadcast by honest parties in `s₀` and has no enabled Tree Building
clause, then `q` has entered round `k` too. -/
theorem Inv.advance {s₀ s : GState P V} (hI₀ : Inv π F s₀) (hI : Inv π F s) (hF : #F ≤ π.t)
    (hn : 3 * π.t < Fintype.card P) {P₀ : P} (hP₀ : P₀ ∉ F) {k : ℕ} (hk : Entered s₀ P₀ k)
    {q : P} (hq : q ∉ F) (hdel : ∀ m ∈ s₀.sent, m ∈ (s.loc q).pool) (hset : TBSettled π s q) :
    Entered s q k := by
  by_contra hcon
  unfold Entered at hcon
  push Not at hcon
  have hpos := hI.round_pos q hq
  cases ha : (s.loc q).active with
  | false =>
    have hrk : (s.loc q).round ≤ k := by
      by_contra h; exact absurd (hcon.1) (by omega)
    have hready : BeaconReady π (s.loc q).pool (s.loc q).round :=
      (hI₀.beacon_cert hF hn hP₀ hk hpos hrk).mono (fun q' h => hdel _ h) le_rfl
    have := hset _ _ (LStep.beacon _ ha hready)
    simp [LState.start] at this
  | true =>
    have hrk : (s.loc q).round < k := by
      rcases Nat.lt_or_ge (s.loc q).round k with h | h
      · exact h
      · exfalso
        rcases Nat.lt_or_eq_of_le h with h | h
        · exact absurd hcon.1 (by omega)
        · exact absurd ha (hcon.2 h.symm)
    have hround : (s.loc q).round < (s₀.loc P₀).round := by
      unfold Entered at hk; rcases hk with h | ⟨h, -⟩ <;> omega
    obtain ⟨B, hBr, hBn⟩ := hI₀.finished P₀ hP₀ _ hpos hround
    have hBnot := hI₀.notarized_of_sent hF hn (K := B.round) (fun m hm _ => hdel m hm) le_rfl hBn
    have := hset _ _ (LStep.finish _ B ha hBr hBnot.1 (Or.inl (hdel _ hBn)))
    simp at this

/-- The hypotheses of the liveness lemma, for a run `σ`, round `k`, time `T`, delay `δ` and
leader `Q`. -/
structure LiveHyp (π : Params P) (F : Finset P) (σ : ℕ → GState P V) (k T δ : ℕ) (Q : P) :
    Prop where
  run : IsRun π F σ
  inj : ∀ k, Function.Injective (π.rank k)
  hF : #F ≤ π.t
  hn : 3 * π.t < Fintype.card P
  k1 : 1 ≤ k
  /-- (ii) no honest party enters round `k` before time `T` -/
  before : ∀ i, (σ i).now < T → ∀ q ∉ F, ¬ Entered (σ i) q k
  /-- (ii) some honest party has entered round `k` at time `T` -/
  first : ∃ i, (σ i).now = T ∧ ∃ q ∉ F, Entered (σ i) q k
  /-- (iii) the leader of round `k` is honest -/
  leader : Q ∉ F
  leader_rank : π.rank k Q = 0
  /-- (iv) -/
  sync₁ : SyncAt F σ δ T
  sync₂ : SyncAt F σ δ (T + δ + π.Δprop 0)
  /-- (v) -/
  delays : 2 * δ + π.Δprop 0 ≤ π.Δntry 1
  /-- `Δntry` is non-decreasing (Section 3.5) -/
  mono : Monotone π.Δntry
  /-- a delay bound is at least one time unit (discrete time) -/
  δpos : 1 ≤ δ

theorem settled_tb {s : GState P V} {q : P} (h : Settled π s q) : TBSettled π s q :=
  fun l M hl => absurd hl (h l M)

theorem Entered.t0_le {s : GState P V} (hI : Inv π F s) {q : P} (hq : q ∉ F) {k : ℕ}
    (h : Entered s q k) : (s.loc q).t0 k ≤ s.now :=
  hI.t0_le q hq k (h.imp id (fun h => ⟨h.1.symm, h.2⟩))

namespace LiveHyp

variable {σ : ℕ → GState P V} {k T δ : ℕ} {Q : P} (L : LiveHyp π F σ k T δ Q)
include L

theorem inv (i : ℕ) : Inv π F (σ i) :=
  inv_of_reachable L.inj L.hF L.hn (L.run.reachable i)

theorem not_entered_zero (q : P) : ¬ Entered (σ 0) q k := by
  rw [L.run.init]; unfold Entered; simp [GState.init, LState.init]; have := L.k1; omega

/-- The index at which an honest party entered round `k`; the start time of round `k` is the time
of that step. -/
theorem enter_index {j : ℕ} {q : P} (h : Entered (σ j) q k) :
    ∃ e < j, ¬ Entered (σ e) q k ∧ Entered (σ (e + 1)) q k ∧
      ((σ j).loc q).t0 k = (σ e).now := by
  induction j with
  | zero => exact absurd h (L.not_entered_zero q)
  | succ j ih =>
    by_cases hj : Entered (σ j) q k
    · obtain ⟨e, he, h1, h2, h3⟩ := ih hj
      exact ⟨e, by omega, h1, h2, by rw [(L.run.step j).step'.t0_stable hj, h3]⟩
    · exact ⟨j, by omega, hj, h, (L.run.step j).step'.t0_of_enter hj h⟩

/-- Steps that change a local state do not change the time. -/
theorem now_eq_of_entered {e : ℕ} {q : P} (h1 : ¬ Entered (σ e) q k)
    (h2 : Entered (σ (e + 1)) q k) : (σ (e + 1)).now = (σ e).now := by
  rcases (L.run.step e).cases' with h | ⟨-, h⟩
  · exact h
  · rw [h] at h2; exact absurd h2 h1

/-- Every honest party starts round `k` at time `≥ T`. -/
theorem t0_ge {j : ℕ} {q : P} (hq : q ∉ F) (h : Entered (σ j) q k) :
    T ≤ ((σ j).loc q).t0 k := by
  obtain ⟨e, -, h1, h2, h3⟩ := L.enter_index h
  rw [h3, ← L.now_eq_of_entered h1 h2]
  by_contra hlt
  push Not at hlt
  exact L.before _ hlt q hq h2

/-- At the last tick before time `T + δ`, every honest party has entered round `k`. -/
theorem entered_at_tick {i : ℕ} (hi : (σ i).now + 1 = T + δ)
    (hset : ∀ p ∉ F, Settled π (σ i) p) (htick : σ (i + 1) = { σ i with now := (σ i).now + 1 })
    {q : P} (hq : q ∉ F) : Entered (σ i) q k := by
  obtain ⟨i₀, hi₀, P₀, hP₀, hent⟩ := L.first
  have hle : i₀ ≤ i := by
    by_contra h
    have := L.run.now_mono (show i + 1 ≤ i₀ by omega)
    rw [htick] at this; simp only at this; have := L.δpos; omega
  refine (L.inv i₀).advance (L.inv i) L.hF L.hn hP₀ hent hq (fun m hm => ?_)
    (settled_tb (hset q hq))
  have := L.sync₁ i₀ (i + 1) (by omega) (by rw [htick]; simp only; omega) m hm q hq
  rwa [htick] at this

/-- **Catching up**: from time `T + δ` on, every honest party has entered round `k`. -/
theorem entered_of_ge {j : ℕ} (hj : T + δ ≤ (σ j).now) {q : P} (hq : q ∉ F) :
    Entered (σ j) q k := by
  obtain ⟨i, hij, h1, hset, htick⟩ := L.run.exists_tick (by have := L.δpos; omega) j hj
  exact L.run.entered_mono hij.le (L.entered_at_tick h1 hset htick hq)

/-- Every honest party starts round `k` before time `T + δ`. -/
theorem t0_lt {j : ℕ} {q : P} (hq : q ∉ F) (h : Entered (σ j) q k) :
    ((σ j).loc q).t0 k < T + δ := by
  by_cases hj : (σ j).now < T + δ
  · exact lt_of_le_of_lt (h.t0_le (L.inv j) hq) hj
  · push Not at hj
    obtain ⟨i, hij, h1, hset, htick⟩ := L.run.exists_tick (by have := L.δpos; omega) j hj
    have hi := L.entered_at_tick h1 hset htick hq
    rw [L.run.t0_stable hij.le hi]
    have := hi.t0_le (L.inv i) hq
    omega

/-- Honest notarization shares for round-`k` blocks of rank `≥ 1` are cast at time
`≥ T + Δntry(1) ≥ T + 2δ + Δprop(0)`. -/
theorem share_late {i : ℕ} {q : P} {B : Block P V} (h : Msg.notarShare B q ∈ (σ i).sent)
    (hBr : B.round = k) (hrk : 1 ≤ B.rk π.rank) : T + 2 * δ + π.Δprop 0 ≤ (σ i).now := by
  obtain ⟨hq, -, -, h4, h5⟩ := (L.inv i).share B q h
  rw [hBr] at h4 h5
  have hent : Entered (σ i) q k := h4.imp id (fun h => ⟨h.1.symm, h.2.1⟩)
  have := L.t0_ge hq hent
  have := L.mono hrk
  have := L.delays
  omega

/-- A round-`k` block of rank `0` is proposed by the leader `Q`. -/
theorem eq_leader {B : Block P V} (hBr : B.round = k) (hrk : B.rk π.rank = 0) :
    ∃ par pl, B = .mk k Q par pl := by
  cases B with
  | root => simp at hBr; have := L.k1; omega
  | mk k' α par pl =>
    simp only [Block.round_mk] at hBr; subst hBr
    simp only [Block.rk_mk] at hrk
    exact ⟨par, pl, by rw [L.inj _ (hrk.trans L.leader_rank.symm)]⟩

/-- **The leader proposes in time**: its round-`k` block is authenticated before time
`T + δ + Δprop(0)`. -/
theorem proposal [Nonempty V] {j : ℕ} (hj : T + δ + π.Δprop 0 ≤ (σ j).now) :
    ∃ i ≤ j, (σ i).now < T + δ + π.Δprop 0 ∧
      ∃ par pl, Msg.auth (.mk k Q par pl) ∈ (σ i).sent := by
  have hQ := L.entered_of_ge (j := j) (by omega) L.leader
  obtain ⟨e, hej, he1, he2, he3⟩ := L.enter_index hQ
  have hte := L.t0_lt L.leader hQ
  rw [he3] at hte
  obtain ⟨i, hij, h1, hset, htick⟩ :=
    L.run.exists_tick (X := (σ e).now + π.Δprop 0 + 1) (by omega) j (by omega)
  have hei : e + 1 ≤ i := by
    by_contra h
    have h2 := L.run.now_mono (show i + 1 ≤ e + 1 by omega)
    rw [L.now_eq_of_entered he1 he2, htick] at h2
    simp only at h2
    omega
  have hQi : Entered (σ i) Q k := L.run.entered_mono hei he2
  have ht0 : ((σ i).loc Q).t0 k = (σ e).now := by
    rw [← he3, L.run.t0_stable hij.le hQi]
  refine ⟨i, hij.le, by omega, ?_⟩
  have hI := L.inv i
  rcases hQi with hlt | ⟨hr, ha⟩
  · obtain ⟨B, hBr, hBn⟩ := hI.finished Q L.leader k L.k1 hlt
    have hcert := (hI.sent_notar B hBn).resolve_left (Block.ne_root_of_round (by
      have := L.k1; omega))
    obtain ⟨q, hqF, hq⟩ := hcert.exists_correct_signer L.hF (by have := L.hn; omega)
    have hs := hq.resolve_left hqF
    have hauth := (hI.share B q hs).2.1
    rcases Nat.eq_zero_or_pos (B.rk π.rank) with h0 | h0
    · obtain ⟨par, pl, rfl⟩ := L.eq_leader hBr h0
      exact ⟨par, pl, hauth⟩
    · have := L.share_late hs hBr h0
      omega
  · cases hp : ((σ i).loc Q).proposed with
    | true =>
      obtain ⟨par, pl, h⟩ := hI.proposed_auth Q L.leader ha hp
      rw [hr] at h
      exact ⟨par, pl, h⟩
    | false =>
      exfalso
      obtain ⟨Bp, hBp1, hBp2⟩ := hI.parent_ok Q L.leader
      refine hset Q L.leader _ _ (LStep.propose _ Bp (Classical.arbitrary V) ha hp ?_ hBp1 hBp2)
      rw [hr, ht0, L.leader_rank]
      omega

/-- From time `T + 2δ + Δprop(0)` on, the leader's block is valid for every honest party. -/
theorem valid_leader {i₀ : ℕ} {par : Block P V} {pl : V}
    (hauth : Msg.auth (.mk k Q par pl) ∈ (σ i₀).sent) (hi₀ : (σ i₀).now ≤ T + δ + π.Δprop 0)
    {i : ℕ} (hi : T + 2 * δ + π.Δprop 0 ≤ (σ i).now) {q : P} (hq : q ∉ F) :
    Valid ((σ i).loc q).pool (.mk k Q par pl) :=
  (L.inv i₀).valid_of_auth L.hF L.hn (K := k)
    (fun m hm _ => L.sync₂ i₀ i hi₀ (by omega) m hm q hq) le_rfl hauth

/-- The first index at which a message is broadcast. -/
theorem first_sent {m : Msg P V} (h0 : m ∉ (σ 0).sent) {i : ℕ} (hi : m ∈ (σ i).sent) :
    ∃ e < i, m ∉ (σ e).sent ∧ m ∈ (σ (e + 1)).sent := by
  induction i with
  | zero => exact absurd hi h0
  | succ i ih =>
    by_cases h : m ∈ (σ i).sent
    · obtain ⟨e, he, h1, h2⟩ := ih h; exact ⟨e, by omega, h1, h2⟩
    · exact ⟨i, by omega, h, hi⟩

/-- **Only the leader's block gets honest notarization shares in round `k`.** -/
theorem share_eq_leader {i₀ : ℕ} {par : Block P V} {pl : V}
    (hauth : Msg.auth (.mk k Q par pl) ∈ (σ i₀).sent) (hi₀ : (σ i₀).now ≤ T + δ + π.Δprop 0)
    {i : ℕ} {q : P} {B : Block P V} (h : Msg.notarShare B q ∈ (σ i).sent) (hBr : B.round = k) :
    B = .mk k Q par pl := by
  have hI := L.inv i
  obtain ⟨hq, hauthB, -, -, -⟩ := hI.share B q h
  rcases Nat.eq_zero_or_pos (B.rk π.rank) with h0 | h0
  · obtain ⟨par', pl', rfl⟩ := L.eq_leader hBr h0
    have e1 := L.run.sent_mono (show i ≤ max i i₀ by omega) hauthB
    have e2 := L.run.sent_mono (show i₀ ≤ max i i₀ by omega) hauth
    obtain ⟨rfl, rfl⟩ := (L.inv (max i i₀)).auth_unique k Q par' pl' par pl L.leader e1 e2
    rfl
  · exfalso
    have h0' : Msg.notarShare B q ∉ (σ 0).sent := by
      rw [L.run.init]; simp [GState.init]
    obtain ⟨e, -, he1, he2⟩ := L.first_sent h0' h
    obtain ⟨-, ha, hr, -, -, ht, hbetter⟩ := (L.run.step e).step'.new_share he2 he1
    rw [hBr] at hr
    have hent : Entered (σ e) q k := Or.inr ⟨hr.symm, ha⟩
    have := L.t0_ge hq hent
    have := L.mono (show 1 ≤ B.rk π.rank from h0)
    have := L.delays
    rw [← hr] at ht
    have hv := L.valid_leader hauth hi₀ (i := e) (by omega) hq
    have hD := hbetter _ hv (by simp [hr]) (by simp [L.leader_rank]; omega)
    simp only [Block.rk_mk, L.leader_rank] at hD
    obtain ⟨α, hα, hαr⟩ := (L.inv e).D_corrupt L.inj hq ha hD
    rw [← hr, ← L.leader_rank] at hαr
    exact L.leader (L.inj _ hαr ▸ hα)

/-- **Every honest party that finished round `k` cast a finalization share for the leader's
block.** -/
theorem fshare_leader {i₀ : ℕ} {par : Block P V} {pl : V}
    (hauth : Msg.auth (.mk k Q par pl) ∈ (σ i₀).sent) (hi₀ : (σ i₀).now ≤ T + δ + π.Δprop 0) :
    ∀ i, ∀ R ∉ F, k < ((σ i).loc R).round → Msg.finalShare (.mk k Q par pl) R ∈ (σ i).sent := by
  intro i
  induction i with
  | zero =>
    intro R _ h
    rw [L.run.init] at h; simp [GState.init, LState.init] at h; have := L.k1; omega
  | succ i ih =>
    intro R hR h
    have hstep := (L.run.step i).step'
    by_cases hi : k < ((σ i).loc R).round
    · exact hstep.sent_mono (ih R hR hi)
    · have hlt : ((σ i).loc R).round < ((σ (i + 1)).loc R).round := by omega
      obtain ⟨-, hr1, ha, B, hBr, hBv, hBn, hfs⟩ := hstep.finish_of_round_lt hlt
      have hrk : ((σ i).loc R).round = k := by omega
      have hI := L.inv i
      have hpos := hI.round_pos R hR
      have hcert := notarCert_of_pool (hI.pool_avail R hR) (Block.ne_root_of_round (by omega)) hBn
      obtain ⟨q, hqF, hq⟩ := hcert.exists_correct_signer L.hF (by have := L.hn; omega)
      have hB := L.share_eq_leader hauth hi₀ (hq.resolve_left hqF) (hBr.trans hrk)
      subst hB
      apply hfs
      intro B' hB'
      obtain ⟨h1, h2⟩ := hI.N_share R hR ha B' hB'
      exact L.share_eq_leader hauth hi₀ h1 (h2.trans hrk)

end LiveHyp

/-- **Lemma (Liveness assuming partial synchrony)** of [ICC, Section 4] (Property P3).

Consider a run with the "wait for" semantics and assume (i) at most `t < n/3` corrupt parties;
(ii) the first honest party to enter round `k ≥ 1` does so at time `T`; (iii) the leader `Q` of
round `k` (rank `0`) is honest; (iv) the network is `δ`-synchronous at times `T` and
`T + δ + Δprop(0)`; (v) `2δ + Δprop(0) ≤ Δntry(1)` (`Δntry` non-decreasing, `δ ≥ 1`).

Then `Q` proposes a round-`k` block `B_Q` such that, at any time `≥ T + 2δ + Δprop(0)` and
`≥ T + δ + Δntry(0)` at which all round-`k` messages of honest parties have been delivered to all
honest parties and no honest party has an enabled clause, every honest party has `B_Q` valid in
its pool together with a full set of `n - t` finalization shares for it, has `kmax ≥ k`, and has
committed `B_Q` (the chain ending at `B_Q` is a prefix of its output). -/
theorem liveness [Nonempty V] {σ : ℕ → GState P V} {k T δ : ℕ} {Q : P}
    (L : LiveHyp π F σ k T δ Q) {j : ℕ} (hj₁ : T + 2 * δ + π.Δprop 0 ≤ (σ j).now)
    (hj₂ : T + δ + π.Δntry 0 ≤ (σ j).now)
    (hdel : ∀ m ∈ (σ j).sent, m.round = k → ∀ q ∉ F, m ∈ ((σ j).loc q).pool)
    (hset : ∀ q ∉ F, Settled π (σ j) q) :
    ∃ par pl, ∀ R ∉ F,
      Valid ((σ j).loc R).pool (.mk k Q par pl) ∧
      FinalShares π ((σ j).loc R).pool (.mk k Q par pl) ∧
      k ≤ ((σ j).loc R).kmax ∧
      (Block.mk k Q par pl).chain <+: ((σ j).loc R).out := by
  obtain ⟨i₀, hi₀j, hi₀, par, pl, hauth⟩ := L.proposal (j := j) (by omega)
  set BQ : Block P V := .mk k Q par pl with hBQ
  have hI := L.inv j
  have hk1 := L.k1
  have hvalid : ∀ R ∉ F, Valid ((σ j).loc R).pool BQ := fun R hR =>
    L.valid_leader hauth hi₀.le hj₁ hR
  have hauthj : Msg.auth BQ ∈ (σ j).sent := L.run.sent_mono hi₀j hauth
  -- every honest party in round `k` has cast its notarization share for `BQ`
  have hN : ∀ R ∉ F, ((σ j).loc R).round = k → BQ ∈ ((σ j).loc R).N := by
    intro R hR hr
    have hent := L.entered_of_ge (j := j) (by omega) hR
    have ha : ((σ j).loc R).active = true := by
      rcases hent with h | h
      · omega
      · exact h.2
    by_contra hBN
    have hD : BQ.rk π.rank ∉ ((σ j).loc R).D := by
      intro hD
      obtain ⟨α, hα, hαr⟩ := hI.D_corrupt L.inj hR ha hD
      simp only [hBQ, Block.rk_mk, hr] at hαr
      exact L.leader (L.inj _ hαr ▸ hα)
    have ht := L.t0_lt hR hent
    have htime : ((σ j).loc R).t0 ((σ j).loc R).round + π.Δntry (BQ.rk π.rank) ≤ (σ j).now := by
      simp only [hBQ, Block.rk_mk, hr, L.leader_rank]; omega
    have hbetter : ∀ B', Valid ((σ j).loc R).pool B' → B'.round = ((σ j).loc R).round →
        B'.rk π.rank < BQ.rk π.rank → B'.rk π.rank ∈ ((σ j).loc R).D := by
      intro B' _ _ h; simp [hBQ, L.leader_rank] at h
    by_cases hex : ∃ B' ∈ ((σ j).loc R).N, B'.rk π.rank = BQ.rk π.rank
    · exact hset R hR _ _ (LStep.echoDisq _ BQ ha (by simp [hBQ, hr]) (hvalid R hR) hBN hD
        htime hbetter hex)
    · exact hset R hR _ _ (LStep.echoShare _ BQ ha (by simp [hBQ, hr]) (hvalid R hR) hBN hD
        htime hbetter hex)
  -- every honest party has finished round `k`
  have hdone : ∀ R ∉ F, k < ((σ j).loc R).round := by
    intro R hR
    have hent := L.entered_of_ge (j := j) (by omega) hR
    rcases hent with h | ⟨hr, ha⟩
    · exact h
    exfalso
    by_cases hB : ∃ R' ∉ F, k < ((σ j).loc R').round
    · obtain ⟨R', hR', hR'k⟩ := hB
      obtain ⟨B, hBr, hBn⟩ := hI.finished R' hR' k hk1 hR'k
      have hcert := (hI.sent_notar B hBn).resolve_left (Block.ne_root_of_round (by omega))
      obtain ⟨q, hqF, hq⟩ := hcert.exists_correct_signer L.hF (by have := L.hn; omega)
      have e := L.share_eq_leader hauth hi₀.le (hq.resolve_left hqF) hBr
      rw [e] at hBn
      exact hset R hR _ _ (LStep.finish _ BQ ha (by simp [hBQ, hr]) (hvalid R hR)
        (Or.inl (hdel _ hBn (by simp [Msg.round]) R hR)))
    · push Not at hB
      have hall : ∀ q ∉ F, Msg.notarShare BQ q ∈ (σ j).sent := by
        intro q hq
        have hent := L.entered_of_ge (j := j) (by omega) hq
        have hqr : ((σ j).loc q).round = k := by
          rcases hent with h | h
          · exact absurd (hB q hq) (by omega)
          · exact h.1
        have hqa : ((σ j).loc q).active = true := by
          rcases hent with h | h
          · omega
          · exact h.2
        exact (hI.N_share q hq hqa BQ (hN q hq hqr)).1
      exact hset R hR _ _ (LStep.finish _ BQ ha (by simp [hBQ, hr]) (hvalid R hR)
        (Or.inr (notarShares_of_forall L.hF (fun q hq =>
          hdel _ (hall q hq) (by simp [Msg.round, hBQ]) R hR))))
  -- the finalization shares
  have hfs : ∀ R ∉ F, FinalShares π ((σ j).loc R).pool BQ := fun R hR =>
    finalShares_of_forall L.hF (fun q hq =>
      hdel _ (L.fshare_leader hauth hi₀.le j q hq (hdone q hq)) (by simp [Msg.round]) R hR)
  refine ⟨par, pl, fun R hR => ⟨hvalid R hR, hfs R hR, ?_, ?_⟩⟩
  · by_contra hk
    push Not at hk
    exact hset R hR _ _ (LStep.final _ BQ (hvalid R hR) (by simpa [hBQ] using hk)
      (Or.inr (hfs R hR)))
  · have hkmax : k ≤ ((σ j).loc R).kmax := by
      by_contra hk
      push Not at hk
      exact hset R hR _ _ (LStep.final _ BQ (hvalid R hR) (by simpa [hBQ] using hk)
        (Or.inr (hfs R hR)))
    rcases hI.out_ok R hR with ⟨h0, -⟩ | ⟨B, hBr, hBv, hBf, hout⟩
    · omega
    rw [hout]
    have hBQf : FinalCert π F (σ j).sent BQ := finalCert_of_pool (hI.pool_avail R hR) (Or.inr (hfs R hR))
    exact chain_prefix_of_final hI L.hF L.hn hR (hvalid R hR) hBQf hBv hBf (by simp; omega)

end Podc.InternetComputerConsensus
