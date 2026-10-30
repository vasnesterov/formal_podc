import Mathlib

/-!
# Theorem 3.3: an `Ω(t²)` message lower bound for asynchronous Byzantine agreement

Constantinescu, Dufay, Paramonov, Wattenhofer, *From Few to Many Faults: Optimal Adaptive
Byzantine Agreement*, PODC 2026 (arXiv:2505.19989), Theorem 3.3 / Appendix A.

## Model

Message-driven asynchronous message passing among the parties `Fin n`.

* **Randomness and setup.** Everything that is fixed before the inputs are known — shared
  randomness, private coins, a PKI, the outcome of an arbitrary setup phase — is encoded in one
  random element `ω : Ω` drawn from a measure `μ`. No measurability assumption is made on the
  protocol (all statements use `∀ᵐ`, which only needs a null set containing the bad event).
* **Protocol** (`Protocol`). Party `p` with input `b` starts in state `(init p b ω).1` and sends
  the messages `(init p b ω).2` (pairs destination / payload). Upon receipt of a message `m` from
  `q` it moves to `(recv p ω s q m).1` and sends `(recv p ω s q m).2`. Asynchronous parties have
  no clocks, so all local computation between two receipts is folded into the receipt step.
  Self-addressed messages are discarded (a party can simulate them locally). `decision s` is the
  output of the party in state `s` (`none` = undecided); the *first* decision is recorded in the
  configuration (`Config.dec`) and never changes afterwards (irrevocable decisions).
* **Configurations** (`Config`): local states, the global log of all sent messages in sending
  order, the set of delivered log indices and the recorded decisions.
* **Scheduler** (`Scheduler`). The message scheduler is a function of the *metadata* of the
  current configuration only (`Obs`: source/destination of every sent message, which ones were
  delivered, who has decided — no payloads, no states, no `ω`). At every step it either delivers
  one pending message or does nothing. A scheduler that sees `ω` would defeat every protocol
  (FLP), so this restriction is essential; restricting the scheduler (memoryless, metadata only)
  weakens the requirement `Solves` on the protocol and hence strengthens the lower bound, and the
  scheduler built in the proof is of this restricted kind anyway.
* **Faults** (`Fair`, `Solves`). A static set `F` of at most `t` faulty parties. Faulty parties
  run the protocol code, but messages from or to them need not ever be delivered: these are
  Byzantine behaviours (follow the code, omit/ignore messages), so every protocol that is
  resilient to `t` Byzantine parties satisfies `Solves`. A run is `F`-fair if every message
  between two parties outside `F` is eventually delivered.
* **Correctness** (`Solves A μ t`): for every scheduler, input vector and fault set of size
  `≤ t`, for `μ`-almost every `ω`, if the run is `F`-fair then (termination) every party outside
  `F` decides, (agreement) any two decisions of parties outside `F` coincide and (strong unanimity
  validity) if all parties outside `F` have input `v` then they can only decide `v`.
* **Message complexity**: `msgsAtDecision` = the number of messages sent until the first moment
  at which all parties have decided (`⊤` if never); `totalMsgs` = all messages ever sent.

## Main results

* `lower_bound_general`: for `n ≥ 2`, a set `C` of `c` parties and `d` with `c ≤ t` and
  `c - 1 + d ≤ t`, the scheduler `mainSched C d` (execution `Main` of the paper, with `t/2`
  replaced by `c` and `d`) is such that with all inputs `false`, almost surely the run is
  fault-free fair, everybody decides `false`, and at least `c * (d + 1)` messages are sent before
  everybody has decided.
* `theorem_3_3`: with `c = t/2 + 1`, `d = (t+1)/2` (for `1 ≤ t < n`): almost surely
  `M ≥ (t/2 + 1) * ((t+1)/2 + 1) ≥ t²/4`, hence also `E[M] ≥ t²/4`.

## Proof structure (differences from the paper)

The bound holds *almost surely*, not only in expectation: the paper's Markov/union-bound step is
replaced by a pointwise argument on the intersection of finitely many full-measure events:
* setup `Final` (`no_init_decision`): a.s. no party with input `false` decides without having
  received a message (i.e. at initialization; in this message-driven model this replaces the
  paper's "within time `T`"), since otherwise agreement fails with positive probability;
* setups `S_B` and `S_Q` (`main_fair_C`, `main_fair_Q`): a.s. everybody decides in `Main`;
* counting (`main_count`): hence every `p ∈ C` decides only after receiving a non-held message,
  i.e. after at least `d + 1` messages were sent to it.
(The paper's inclusion `⋂ E_pᶜ ⊆ {M ≥ t²/2}` should read `{M > t²/4}`; this is harmless there.)

Non-vacuity: `Solves A μ t` is satisfiable for `n > 3t` by known randomized asynchronous BA
protocols with a trusted setup (e.g. Cachin–Kursawe–Shoup), since our faults are a special case
of Byzantine faults; no such protocol is formalized here. The hypothesis `n ≥ 2` of
`lower_bound_general` cannot be dropped: for `n = 1`, "decide your own input at initialization"
satisfies `Solves` for every `t`.
-/

namespace Podc.FewToManyFaultsBA.Async

open MeasureTheory

variable {n : ℕ} {σ Msg Ω : Type*}

/-! ## The model -/

-- CSLib candidate: randomized message-driven asynchronous model with a metadata scheduler.

/-- A randomized asynchronous protocol for `n` parties with local states `σ`, payloads `Msg` and
randomness/setup outcome `ω : Ω`. -/
structure Protocol (n : ℕ) (σ Msg Ω : Type*) where
  /-- Initial state and initial messages `(destination, payload)` of a party from its input. -/
  init : Fin n → Bool → Ω → σ × List (Fin n × Msg)
  /-- `recv p ω s q m`: party `p` in state `s` receives `m` from `q`; new state and messages. -/
  recv : Fin n → Ω → σ → Fin n → Msg → σ × List (Fin n × Msg)
  /-- The output of a party in a given state (`none`: not decided). -/
  decision : σ → Option Bool

/-- A sent message. -/
structure Envelope (n : ℕ) (Msg : Type*) where
  /-- Sender. -/
  src : Fin n
  /-- Destination. -/
  dst : Fin n
  /-- Payload. -/
  msg : Msg

/-- A global configuration. -/
structure Config (n : ℕ) (σ Msg : Type*) where
  /-- Local states. -/
  state : Fin n → σ
  /-- All messages sent so far, in sending order. -/
  sent : List (Envelope n Msg)
  /-- Indices (into `sent`) of the delivered messages. -/
  delivered : Finset ℕ
  /-- The first decision of each party (irrevocable). -/
  dec : Fin n → Option Bool

/-- What the scheduler sees: the metadata of a configuration (no payloads, states or
randomness). -/
structure Obs (n : ℕ) where
  /-- `(source, destination)` of every sent message, in sending order. -/
  links : List (Fin n × Fin n)
  /-- Delivered indices. -/
  delivered : Finset ℕ
  /-- Who has decided. -/
  decided : Fin n → Bool

/-- The metadata of a configuration. -/
def Config.obs (c : Config n σ Msg) : Obs n :=
  ⟨c.sent.map (fun e => (e.src, e.dst)), c.delivered, fun p => (c.dec p).isSome⟩

/-- A (deterministic, memoryless, metadata-only) scheduler: `some i` delivers message `i` (if it
is pending; otherwise nothing happens), `none` does nothing. -/
abbrev Scheduler (n : ℕ) := Obs n → Option ℕ

/-- Messages sent by `p`, self-addressed ones discarded. -/
def wrap (p : Fin n) (out : List (Fin n × Msg)) : List (Envelope n Msg) :=
  (out.filter (fun m => m.1 ≠ p)).map (fun m => ⟨p, m.1, m.2⟩)

/-- The initial configuration: every party initializes (in the order of `Fin n`). -/
def initConfig (A : Protocol n σ Msg Ω) (inp : Fin n → Bool) (ω : Ω) : Config n σ Msg where
  state p := (A.init p (inp p) ω).1
  sent := (List.finRange n).flatMap (fun p => wrap p (A.init p (inp p) ω).2)
  delivered := ∅
  dec p := A.decision (A.init p (inp p) ω).1

/-- One step: deliver message `i` if `a = some i` and `i` is pending. -/
def step (A : Protocol n σ Msg Ω) (ω : Ω) (c : Config n σ Msg) : Option ℕ → Config n σ Msg
  | none => c
  | some i =>
    if h : i < c.sent.length ∧ i ∉ c.delivered then
      let e := c.sent[i]'h.1
      let r := A.recv e.dst ω (c.state e.dst) e.src e.msg
      { state := Function.update c.state e.dst r.1
        sent := c.sent ++ wrap e.dst r.2
        delivered := insert i c.delivered
        dec := Function.update c.dec e.dst ((c.dec e.dst).or (A.decision r.1)) }
    else c

/-- The run of protocol `A` under scheduler `sched` with inputs `inp` and randomness `ω`. -/
def run (A : Protocol n σ Msg Ω) (sched : Scheduler n) (inp : Fin n → Bool) (ω : Ω) :
    ℕ → Config n σ Msg
  | 0 => initConfig A inp ω
  | k + 1 => step A ω (run A sched inp ω k) (sched (run A sched inp ω k).obs)

/-- A run is `F`-fair if every message between two parties outside `F` is eventually
delivered. -/
def Fair (F : Finset (Fin n)) (r : ℕ → Config n σ Msg) : Prop :=
  ∀ k i e, (r k).sent[i]? = some e → e.src ∉ F → e.dst ∉ F → ∃ k', i ∈ (r k').delivered

/-- Correctness of a run for the non-faulty parties (outside `F`): termination, agreement and
strong unanimity validity. -/
def Correct (F : Finset (Fin n)) (inp : Fin n → Bool) (r : ℕ → Config n σ Msg) : Prop :=
  (∀ p ∉ F, ∃ k, (r k).dec p ≠ none) ∧
  (∀ p ∉ F, ∀ q ∉ F, ∀ k k' v w, (r k).dec p = some v → (r k').dec q = some w → v = w) ∧
  (∀ v, (∀ p ∉ F, inp p = v) → ∀ p ∉ F, ∀ k w, (r k).dec p = some w → w = v)

/-- `A` solves asynchronous binary Byzantine agreement against `t` static faults with
almost-sure termination: for every scheduler, input vector and fault set of size `≤ t`, almost
every `F`-fair run is correct. -/
def Solves [MeasurableSpace Ω] (A : Protocol n σ Msg Ω) (μ : Measure Ω) (t : ℕ) : Prop :=
  ∀ (sched : Scheduler n) (inp : Fin n → Bool) (F : Finset (Fin n)), F.card ≤ t →
    ∀ᵐ ω ∂μ, Fair F (run A sched inp ω) → Correct F inp (run A sched inp ω)

open Classical in
/-- Number of messages sent until all parties have decided (`⊤` if this never happens). -/
noncomputable def msgsAtDecision (r : ℕ → Config n σ Msg) : ℕ∞ :=
  if h : ∃ k, ∀ q, (r k).dec q ≠ none then ((r (Nat.find h)).sent.length : ℕ∞) else ⊤

/-- Total number of messages ever sent. -/
noncomputable def totalMsgs (r : ℕ → Config n σ Msg) : ℕ∞ :=
  ⨆ k, ((r k).sent.length : ℕ∞)

/-! ## Basic properties of runs -/

section Basic

variable (A : Protocol n σ Msg Ω) (ω : Ω)

lemma wrap_noself (p : Fin n) (out : List (Fin n × Msg)) :
    ∀ e ∈ wrap p out, e.src = p ∧ e.dst ≠ p := by
  intro e he
  simp only [wrap, List.mem_map, List.mem_filter] at he
  obtain ⟨m, ⟨-, hm⟩, rfl⟩ := he
  simpa using hm

lemma step_sent_prefix (c : Config n σ Msg) (a : Option ℕ) : c.sent <+: (step A ω c a).sent := by
  cases a with
  | none => exact List.prefix_refl _
  | some i =>
    simp only [step]; split_ifs
    · exact List.prefix_append _ _
    · exact List.prefix_refl _

lemma step_delivered_subset (c : Config n σ Msg) (a : Option ℕ) :
    c.delivered ⊆ (step A ω c a).delivered := by
  cases a with
  | none => exact subset_rfl
  | some i =>
    simp only [step]; split_ifs
    · exact Finset.subset_insert _ _
    · exact subset_rfl

lemma step_dec (c : Config n σ Msg) (a : Option ℕ) (p : Fin n) (v : Bool)
    (h : c.dec p = some v) : (step A ω c a).dec p = some v := by
  cases a with
  | none => exact h
  | some i =>
    simp only [step]; split_ifs
    · simp only [Function.update_apply]
      split_ifs with hp
      · subst hp; simp [h]
      · exact h
    · exact h

lemma step_delivered_eq (c : Config n σ Msg) (i : ℕ) (h : i < c.sent.length)
    (h' : i ∉ c.delivered) : (step A ω c (some i)).delivered = insert i c.delivered := by
  simp [step, h, h']

lemma step_valid (c : Config n σ Msg) (a : Option ℕ)
    (hc : ∀ i ∈ c.delivered, i < c.sent.length) :
    ∀ i ∈ (step A ω c a).delivered, i < (step A ω c a).sent.length := by
  cases a with
  | none => exact hc
  | some j =>
    simp only [step]; split_ifs with h
    · intro i hi
      simp only [Finset.mem_insert, List.length_append] at hi ⊢
      rcases hi with rfl | hi
      · omega
      · have := hc i hi; omega
    · exact hc

lemma step_noself (c : Config n σ Msg) (a : Option ℕ) (hc : ∀ e ∈ c.sent, e.src ≠ e.dst) :
    ∀ e ∈ (step A ω c a).sent, e.src ≠ e.dst := by
  cases a with
  | none => exact hc
  | some j =>
    simp only [step]; split_ifs with h
    · intro e he
      simp only [List.mem_append] at he
      rcases he with he | he
      · exact hc e he
      · obtain ⟨h1, h2⟩ := wrap_noself _ _ e he
        rw [h1]; exact fun h => h2 h.symm
    · exact hc

/-- A party's recorded decision can only appear when it receives a message. -/
lemma step_dec_change (c : Config n σ Msg) (a : Option ℕ) (p : Fin n) (h0 : c.dec p = none)
    (h1 : (step A ω c a).dec p ≠ none) :
    ∃ i, a = some i ∧ i ∉ c.delivered ∧ ∃ e, c.sent[i]? = some e ∧ e.dst = p := by
  cases a with
  | none => exact absurd h0 h1
  | some i =>
    simp only [step] at h1; split_ifs at h1 with h
    · refine ⟨i, rfl, h.2, c.sent[i]'h.1, List.getElem?_eq_getElem h.1, ?_⟩
      by_contra hne
      simp only [Function.update_apply] at h1
      simp [Ne.symm hne, h0] at h1
    · exact absurd h0 h1

variable (sched : Scheduler n) (inp : Fin n → Bool)

lemma run_succ (k : ℕ) :
    run A sched inp ω (k + 1) = step A ω (run A sched inp ω k) (sched (run A sched inp ω k).obs) :=
  rfl

lemma sent_prefix {k k' : ℕ} (hk : k ≤ k') :
    (run A sched inp ω k).sent <+: (run A sched inp ω k').sent := by
  induction k', hk using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k' _ ih => exact ih.trans (step_sent_prefix A ω _ _)

lemma delivered_mono {k k' : ℕ} (hk : k ≤ k') :
    (run A sched inp ω k).delivered ⊆ (run A sched inp ω k').delivered := by
  induction k', hk using Nat.le_induction with
  | base => exact subset_rfl
  | succ k' _ ih => exact ih.trans (step_delivered_subset A ω _ _)

lemma dec_stable {k k' : ℕ} (hk : k ≤ k') {p : Fin n} {v : Bool}
    (h : (run A sched inp ω k).dec p = some v) : (run A sched inp ω k').dec p = some v := by
  induction k', hk using Nat.le_induction with
  | base => exact h
  | succ k' _ ih => exact step_dec A ω _ _ _ _ ih

lemma dec_isSome_stable {k k' : ℕ} (hk : k ≤ k') {p : Fin n}
    (h : (run A sched inp ω k).dec p ≠ none) : (run A sched inp ω k').dec p ≠ none := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h
  rw [dec_stable A ω sched inp hk hv]; simp

lemma delivered_lt (k : ℕ) :
    ∀ i ∈ (run A sched inp ω k).delivered, i < (run A sched inp ω k).sent.length := by
  induction k with
  | zero => simp [run, initConfig]
  | succ k ih => exact step_valid A ω _ _ ih

lemma noself (k : ℕ) : ∀ e ∈ (run A sched inp ω k).sent, e.src ≠ e.dst := by
  induction k with
  | zero =>
    intro e he
    simp only [run, initConfig, List.mem_flatMap] at he
    obtain ⟨p, -, he⟩ := he
    obtain ⟨h1, h2⟩ := wrap_noself _ _ e he
    rw [h1]; exact fun h => h2 h.symm
  | succ k ih => exact step_noself A ω _ _ ih

lemma dec_zero (p : Fin n) :
    (run A sched inp ω 0).dec p = A.decision (A.init p (inp p) ω).1 := rfl

lemma getElem?_of_prefix {k k' : ℕ} (hk : k ≤ k') {i : ℕ} {e : Envelope n Msg}
    (h : (run A sched inp ω k).sent[i]? = some e) : (run A sched inp ω k').sent[i]? = some e := by
  obtain ⟨u, hu⟩ := sent_prefix A ω sched inp hk
  rw [← hu, List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1, h]

end Basic

/-! ## Schedulers delivering the oldest pending allowed message -/

open Classical in
/-- The scheduler that delivers the oldest pending message satisfying `allowed` (and does nothing
if there is none). -/
noncomputable def oldestSched (allowed : Obs n → ℕ → Prop) : Scheduler n := fun o =>
  if h : ∃ i, i < o.links.length ∧ i ∉ o.delivered ∧ allowed o i then some (Nat.find h) else none

section Oldest

variable (allowed : Obs n → ℕ → Prop)

open Classical in
lemma oldestSched_spec {o : Obs n} {j : ℕ} (h : oldestSched allowed o = some j) :
    j < o.links.length ∧ j ∉ o.delivered ∧ allowed o j := by
  unfold oldestSched at h
  split_ifs at h with hex
  · cases h
    exact Nat.find_spec hex

open Classical in
lemma oldestSched_le {o : Obs n} {i : ℕ} (hi : i < o.links.length) (hd : i ∉ o.delivered)
    (ha : allowed o i) : ∃ j ≤ i, oldestSched allowed o = some j := by
  unfold oldestSched
  split_ifs with hex
  · exact ⟨_, Nat.find_min' hex ⟨hi, hd, ha⟩, rfl⟩
  · exact absurd ⟨i, hi, hd, ha⟩ hex

variable (A : Protocol n σ Msg Ω) (ω : Ω) (inp : Fin n → Bool)

/-- Generic fairness of `oldestSched`: if allowedness of a sent message is never revoked, every
message that is allowed at some point is eventually delivered. -/
theorem oldest_eventually_delivered
    (hmono : ∀ k i, i < (run A (oldestSched allowed) inp ω k).sent.length →
      allowed (run A (oldestSched allowed) inp ω k).obs i →
      allowed (run A (oldestSched allowed) inp ω (k + 1)).obs i)
    {k i : ℕ} (hi : i < (run A (oldestSched allowed) inp ω k).sent.length)
    (ha : allowed (run A (oldestSched allowed) inp ω k).obs i) :
    ∃ k', i ∈ (run A (oldestSched allowed) inp ω k').delivered := by
  set r := run A (oldestSched allowed) inp ω with hr
  by_contra hnd
  push Not at hnd
  have key : ∀ m, i < (r (k + m)).sent.length ∧ allowed (r (k + m)).obs i ∧
      m ≤ ((r (k + m)).delivered.filter (· < i)).card := by
    intro m
    induction m with
    | zero => exact ⟨hi, ha, Nat.zero_le _⟩
    | succ m ih =>
      obtain ⟨hi', ha', hc⟩ := ih
      have hlen : i < (r (k + m)).obs.links.length := by simpa [Config.obs] using hi'
      obtain ⟨j, hji, hj⟩ := oldestSched_le allowed hlen (hnd _) ha'
      obtain ⟨hjl, hjd, -⟩ := oldestSched_spec allowed hj
      simp only [Config.obs, List.length_map] at hjl hjd
      have hstep : r (k + (m + 1)) = step A ω (r (k + m)) (some j) := by
        rw [← add_assoc, hr, run_succ, ← hr, hj]
      have hdel : (r (k + (m + 1))).delivered = insert j (r (k + m)).delivered := by
        rw [hstep]; exact step_delivered_eq A ω _ _ hjl hjd
      have hji' : j ≠ i := by
        rintro rfl; exact hnd (k + (m + 1)) (by rw [hdel]; exact Finset.mem_insert_self _ _)
      refine ⟨lt_of_lt_of_le hi' (sent_prefix A ω _ inp (by omega)).length_le,
        by rw [← add_assoc]; exact hmono _ _ hi' ha', ?_⟩
      rw [hdel, Finset.filter_insert, ite_eq_left_of_eq_true _ _ (eq_true (lt_of_le_of_ne hji hji')),
        Finset.card_insert_of_notMem (fun h => hjd (Finset.mem_filter.1 h).1)]
      omega
  have h1 := (key (i + 1)).2.2
  have h2 : ((r (k + (i + 1))).delivered.filter (· < i)).card ≤ i := by
    calc _ ≤ (Finset.range i).card :=
          Finset.card_le_card fun x hx => Finset.mem_range.2 (Finset.mem_filter.1 hx).2
      _ = i := Finset.card_range i
  omega

end Oldest

/-! ## The schedulers `Main` and `FIFO` -/

section Schedulers

variable (C : Finset (Fin n)) (d : ℕ)

/-- `e` is a message from outside `C` to `p`. -/
def isBto (p : Fin n) (e : Fin n × Fin n) : Bool := decide (e.1 ∉ C ∧ e.2 = p)

/-- Message `i` of the log `l` is *held* by `Main` (paper, Appendix A): it goes from `C` to `C`,
or it goes to some `p ∈ C` and is among the first `d` messages from outside `C` to `p`. -/
def Held (l : List (Fin n × Fin n)) (i : ℕ) : Prop :=
  ∃ s p, l[i]? = some (s, p) ∧ p ∈ C ∧ (s ∈ C ∨ (l.take i).countP (isBto C p) < d)

/-- `Main` may deliver a message if it is not held, or once everybody has decided. -/
def mainAllowed (o : Obs n) (i : ℕ) : Prop :=
  (∀ q, o.decided q = true) ∨ ¬ Held C d o.links i

/-- The scheduler of the execution `Main` (paper, Appendix A): messages inside `C` and the first
`d` messages from outside `C` to each `p ∈ C` are delayed until everybody has decided; all other
messages are delivered (oldest first). It only looks at metadata. -/
noncomputable def mainSched : Scheduler n := oldestSched (mainAllowed C d)

/-- The FIFO scheduler: always deliver the oldest pending message. -/
noncomputable def fifoSched : Scheduler n := oldestSched (fun _ _ => True)

/-- Senders of the held messages from outside `C` to `p` in the log `l`. -/
def heldSrc (p : Fin n) (l : List (Fin n × Fin n)) : Finset (Fin n) :=
  (((l.filter (isBto C p)).take d).map Prod.fst).toFinset

lemma held_append {l : List (Fin n × Fin n)} {i : ℕ} (hi : i < l.length)
    (u : List (Fin n × Fin n)) : Held C d (l ++ u) i ↔ Held C d l i := by
  unfold Held
  rw [List.getElem?_append_left hi, List.take_append_of_le_length hi.le]

lemma heldSrc_card (p : Fin n) (l : List (Fin n × Fin n)) : (heldSrc C d p l).card ≤ d := by
  unfold heldSrc
  refine (List.toFinset_card_le _).trans ?_
  simp

lemma not_mem_of_mem_heldSrc {p s : Fin n} {l : List (Fin n × Fin n)}
    (h : s ∈ heldSrc C d p l) : s ∉ C := by
  unfold heldSrc at h
  simp only [List.mem_toFinset, List.mem_map] at h
  obtain ⟨e, he, rfl⟩ := h
  have := (List.mem_filter.1 (List.mem_of_mem_take he)).2
  simp [isBto] at this
  exact this.1

lemma heldSrc_append (p : Fin n) (l u : List (Fin n × Fin n)) :
    heldSrc C d p l ⊆ heldSrc C d p (l ++ u) := by
  intro s hs
  unfold heldSrc at hs ⊢
  simp only [List.mem_toFinset, List.mem_map] at hs ⊢
  obtain ⟨e, he, rfl⟩ := hs
  refine ⟨e, ?_, rfl⟩
  rw [List.filter_append, List.take_append, List.mem_append]
  rcases Nat.lt_or_ge (l.filter (isBto C p)).length d with h | h
  · left; rw [List.take_of_length_le h.le] at he ⊢; exact he
  · left; exact he

lemma mem_heldSrc {l : List (Fin n × Fin n)} {i : ℕ} {s p : Fin n}
    (hl : l[i]? = some (s, p)) (hs : s ∉ C) (hc : (l.take i).countP (isBto C p) < d) :
    s ∈ heldSrc C d p l := by
  obtain ⟨hi, hle⟩ := List.getElem?_eq_some_iff.1 hl
  have hsplit : l = l.take i ++ (s, p) :: l.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i l]
    rw [List.drop_eq_getElem_cons hi, hle]
  unfold heldSrc
  rw [hsplit, List.filter_append, List.filter_cons_of_pos (by simp [isBto, hs]),
    List.take_append]
  rw [List.countP_eq_length_filter] at hc
  obtain ⟨m, hm⟩ : ∃ m, d - ((l.take i).filter (isBto C p)).length = m + 1 :=
    ⟨d - ((l.take i).filter (isBto C p)).length - 1, by omega⟩
  rw [hm, List.take_succ_cons]
  simp

end Schedulers

section RunSchedulers

variable (A : Protocol n σ Msg Ω) (ω : Ω) (inp : Fin n → Bool) (C : Finset (Fin n)) (d : ℕ)

lemma links_append (sched : Scheduler n) (k : ℕ) :
    ∃ u, (run A sched inp ω (k + 1)).obs.links = (run A sched inp ω k).obs.links ++ u := by
  obtain ⟨u, hu⟩ := sent_prefix A ω sched inp (Nat.le_succ k)
  exact ⟨u.map (fun e => (e.src, e.dst)), by simp [Config.obs, ← hu]⟩

lemma links_getElem? (sched : Scheduler n) {k i : ℕ} {e : Envelope n Msg}
    (h : (run A sched inp ω k).sent[i]? = some e) :
    (run A sched inp ω k).obs.links[i]? = some (e.src, e.dst) := by
  simp [Config.obs, h]

lemma mainAllowed_mono (k i : ℕ) (hi : i < (run A (mainSched C d) inp ω k).sent.length)
    (ha : mainAllowed C d (run A (mainSched C d) inp ω k).obs i) :
    mainAllowed C d (run A (mainSched C d) inp ω (k + 1)).obs i := by
  rcases ha with ha | ha
  · left
    intro q
    have hq := ha q
    simp only [Config.obs, Option.isSome_iff_ne_none] at hq ⊢
    exact dec_isSome_stable A ω _ inp (Nat.le_succ k) hq
  · right
    obtain ⟨u, hu⟩ := links_append A ω inp (mainSched C d) k
    rw [hu, held_append C d (by simpa [Config.obs] using hi)]
    exact ha

/-- Under `Main`, a message that is not held is eventually delivered. -/
lemma main_delivered_of_not_held {k i : ℕ} (hi : i < (run A (mainSched C d) inp ω k).sent.length)
    (hh : ¬ Held C d (run A (mainSched C d) inp ω k).obs.links i) :
    ∃ k', i ∈ (run A (mainSched C d) inp ω k').delivered :=
  oldest_eventually_delivered (mainAllowed C d) A ω inp (mainAllowed_mono A ω inp C d) hi
    (Or.inr hh)

/-- The FIFO scheduler is fair (every message is eventually delivered). -/
lemma fifo_fair (F : Finset (Fin n)) : Fair F (run A fifoSched inp ω) := by
  intro k i e he _ _
  exact oldest_eventually_delivered (fun _ _ => True) A ω inp (fun _ _ _ _ => trivial)
    (List.getElem?_eq_some_iff.1 he).1 trivial

/-- In `Main`, the faulty set `C` (setup `S_B` of the paper): the run is `C`-fair. -/
lemma main_fair_C : Fair C (run A (mainSched C d) inp ω) := by
  intro k i e he _ hdst
  refine main_delivered_of_not_held A ω inp C d (List.getElem?_eq_some_iff.1 he).1 ?_
  rintro ⟨s, p, hl, hp, -⟩
  rw [links_getElem? A ω inp _ he] at hl
  cases hl
  exact hdst hp

/-- In `Main`, the faulty set `(C \ {p}) ∪ Q` (setup `S_Q` of the paper): the run is fair as soon
as `Q` contains all senders of held messages from outside `C` to `p`. -/
lemma main_fair_Q {p : Fin n} (Q : Finset (Fin n))
    (hQ : ∀ k, heldSrc C d p (run A (mainSched C d) inp ω k).obs.links ⊆ Q) :
    Fair (C.erase p ∪ Q) (run A (mainSched C d) inp ω) := by
  intro k i e he hsrc hdst
  refine main_delivered_of_not_held A ω inp C d (List.getElem?_eq_some_iff.1 he).1 ?_
  rintro ⟨s, q, hl, hq, hsC⟩
  have hl' := hl
  rw [links_getElem? A ω inp _ he] at hl
  cases hl
  simp only [Finset.mem_union, Finset.mem_erase, not_or, not_and] at hsrc hdst
  have hqp : e.dst = p := by by_contra h; exact hdst.1 h hq
  have hne : e.src ≠ e.dst :=
    noself A ω _ inp k e (List.mem_of_getElem? he)
  have hsC' : e.src ∉ C := fun h => hsrc.1 (hqp ▸ hne) h
  rcases hsC with h | h
  · exact hsC' h
  · rw [hqp] at hl' h
    exact hsrc.2 (hQ k (mem_heldSrc C d hl' hsC' h))

end RunSchedulers

/-! ## Counting messages in `Main` -/

section Counting

variable (A : Protocol n σ Msg Ω) (ω : Ω) (C : Finset (Fin n)) (d : ℕ)

lemma sum_countP_dst_le (C : Finset (Fin n)) (l : List (Fin n × Fin n)) :
    ∑ p ∈ C, l.countP (fun e => decide (e.2 = p)) ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, Finset.sum_add_distrib, decide_eq_true_eq, List.length_cons]
    have : ∑ p ∈ C, (if a.2 = p then 1 else 0) ≤ 1 := by
      rw [Finset.sum_ite_eq]; split_ifs <;> omega
    omega

lemma links_prefix (sched : Scheduler n) (inp : Fin n → Bool) {k k' : ℕ} (hk : k ≤ k') :
    (run A sched inp ω k).obs.links <+: (run A sched inp ω k').obs.links :=
  (sent_prefix A ω sched inp hk).map _

/-- In `Main`, a party `p ∈ C` that does not decide at initialization has, by the time it has
decided, been sent at least `d + 1` messages: it decides only upon receiving a message, and the
only messages it can receive before everybody has decided are those from outside `C` sent after
the first `d` messages from outside `C` to `p`. -/
lemma main_count_to {p : Fin n} (hp : p ∈ C) (hinit : A.decision (A.init p false ω).1 = none)
    {K : ℕ} (hK : (run A (mainSched C d) (fun _ => false) ω K).dec p ≠ none) :
    d + 1 ≤ (run A (mainSched C d) (fun _ => false) ω K).obs.links.countP
      (fun e => decide (e.2 = p)) := by
  set r := run A (mainSched C d) (fun _ => false) ω with hr
  have hex : ∃ k, (r k).dec p ≠ none := ⟨K, hK⟩
  classical
  obtain ⟨k, hk1⟩ : ∃ k, Nat.find hex = k + 1 := by
    rcases h : Nat.find hex with _ | k
    · exact absurd (h ▸ Nat.find_spec hex) (by rw [hr, dec_zero]; exact not_not.2 hinit)
    · exact ⟨k, rfl⟩
  have hk0 : (r k).dec p = none := by
    have := Nat.find_min hex (show k < Nat.find hex by omega)
    simpa using this
  have hkK : k + 1 ≤ K := hk1 ▸ Nat.find_min' hex hK
  have hstep : (r (k + 1)).dec p ≠ none := hk1 ▸ Nat.find_spec hex
  rw [hr, run_succ, ← hr] at hstep
  obtain ⟨i, hi, -, e, he, hep⟩ := step_dec_change A ω _ _ p hk0 hstep
  obtain ⟨-, -, hall⟩ := oldestSched_spec (mainAllowed C d) hi
  have hnh : ¬ Held C d (r k).obs.links i := by
    rcases hall with h | h
    · have := h p; simp [Config.obs, hk0] at this
    · exact h
  have hl := links_getElem? A ω (fun _ => false) _ he
  rw [hep] at hl
  have hcnt : d ≤ ((r k).obs.links.take i).countP (isBto C p) := by
    by_contra h
    exact hnh ⟨e.src, p, hl, hp, Or.inr (by omega)⟩
  have hsrc : e.src ∉ C := fun h => hnh ⟨e.src, p, hl, hp, Or.inl h⟩
  calc d + 1 ≤ ((r k).obs.links.take i).countP (fun e => decide (e.2 = p)) + 1 := by
        have := List.countP_mono_left (l := (r k).obs.links.take i) (p := isBto C p)
          (q := fun e => decide (e.2 = p)) (by intro x _ hx; simp [isBto] at hx ⊢; exact hx.2)
        omega
    _ = ((r k).obs.links.take (i + 1)).countP (fun e => decide (e.2 = p)) := by
        rw [List.take_add_one, hl, List.countP_append]; simp
    _ ≤ (r K).obs.links.countP (fun e => decide (e.2 = p)) :=
        ((List.take_prefix _ _).trans (links_prefix A ω _ _ (by omega))).sublist.countP_le

/-- In `Main`, if no party of `C` decides at initialization, then at least `|C| * (d + 1)`
messages have been sent at any time at which every party of `C` has decided. -/
lemma main_count (hinit : ∀ p ∈ C, A.decision (A.init p false ω).1 = none) {K : ℕ}
    (hK : ∀ p ∈ C, (run A (mainSched C d) (fun _ => false) ω K).dec p ≠ none) :
    C.card * (d + 1) ≤ (run A (mainSched C d) (fun _ => false) ω K).sent.length := by
  calc C.card * (d + 1) = ∑ p ∈ C, (d + 1) := by simp
    _ ≤ ∑ p ∈ C, (run A (mainSched C d) (fun _ => false) ω K).obs.links.countP
          (fun e => decide (e.2 = p)) :=
        Finset.sum_le_sum fun p hp => main_count_to A ω C d hp (hinit p hp) (hK p hp)
    _ ≤ (run A (mainSched C d) (fun _ => false) ω K).obs.links.length := sum_countP_dst_le C _
    _ = _ := by simp [Config.obs]

end Counting

/-! ## The lower bound -/

section LowerBound

open scoped ENNReal

variable [MeasurableSpace Ω] (A : Protocol n σ Msg Ω) (μ : Measure Ω) (t : ℕ)

/-- The inputs of the paper's setup `Final`: party `p` has input `0` (`false`), all other
parties have input `!w` (the paper only needs `w = false`, i.e. the others have input `1`; we also
use `w = true` to exclude a decision `1` at initialization). -/
def finalInp (p : Fin n) (w : Bool) : Fin n → Bool := fun q => if q = p then false else !w

/-- Setup `Final` of the paper (with the FIFO scheduler, which is fair): almost surely, a party
with input `false` does not decide at initialization, i.e. without having received any
message. Otherwise, with positive probability, it would decide some `w` while all others, having
input `!w`, decide `!w` (validity with `p` treated as faulty), violating agreement. -/
lemma no_init_decision (hA : Solves A μ t) (ht : 1 ≤ t) (hn : 2 ≤ n) (p : Fin n) :
    ∀ᵐ ω ∂μ, A.decision (A.init p false ω).1 = none := by
  have key : ∀ w : Bool, ∀ᵐ ω ∂μ, A.decision (A.init p false ω).1 ≠ some w := by
    intro w
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
    obtain ⟨q, hq⟩ := exists_ne p
    filter_upwards [hA fifoSched (finalInp p w) {p} (by simpa using ht),
      hA fifoSched (finalInp p w) ∅ (by simp)] with ω h1 h2 hdec
    obtain ⟨hterm, -, hval⟩ := h1 (fifo_fair A ω _ _)
    obtain ⟨-, hagr, -⟩ := h2 (fifo_fair A ω _ _)
    obtain ⟨k, hk⟩ := hterm q (by simpa using hq)
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hk
    have hv' : v = !w := hval (!w) (fun x hx => by
      simp only [Finset.mem_singleton] at hx; simp [finalInp, hx]) q (by simpa using hq) k v hv
    have h0 : (run A fifoSched (finalInp p w) ω 0).dec p = some w := by
      rw [dec_zero]; simpa [finalInp] using hdec
    have := hagr p (by simp) q (by simp) 0 k w v h0 hv
    rw [hv'] at this
    cases w <;> simp at this
  filter_upwards [key true, key false] with ω h1 h2
  cases h : A.decision (A.init p false ω).1 with
  | none => rfl
  | some b => cases b <;> simp_all

/-- **Theorem 3.3, general form.** Let `A` solve asynchronous binary Byzantine agreement against
`t` static faults (`Solves A μ t`), `n ≥ 2`, and let `C` be a set of parties and `d` a number with
`|C| ≤ t` and `|C| - 1 + d ≤ t`. Consider the execution `Main` of the paper: all inputs `false`,
scheduler `mainSched C d`. Then almost surely
* the run is a legitimate fault-free asynchronous execution (every message is eventually
  delivered) in which every party decides `false`, and
* at least `|C| * (d + 1)` messages are sent before all parties have decided (and hence in
  total). -/
theorem lower_bound_general (hA : Solves A μ t) (hn : 2 ≤ n) (C : Finset (Fin n)) (d : ℕ)
    (hCt : C.card ≤ t) (hCd : C.card - 1 + d ≤ t) :
    (∀ᵐ ω ∂μ, Fair ∅ (run A (mainSched C d) (fun _ => false) ω) ∧
      ∀ q, ∃ k, (run A (mainSched C d) (fun _ => false) ω k).dec q = some false) ∧
    (∀ᵐ ω ∂μ, ((C.card * (d + 1) : ℕ) : ℕ∞) ≤
      msgsAtDecision (run A (mainSched C d) (fun _ => false) ω)) ∧
    (∀ᵐ ω ∂μ, ((C.card * (d + 1) : ℕ) : ℕ∞) ≤
      totalMsgs (run A (mainSched C d) (fun _ => false) ω)) := by
  set r := fun ω => run A (mainSched C d) (fun _ => false) ω with hr
  have hG0 := hA (mainSched C d) (fun _ => false) ∅ (by simp)
  -- setup `S_B`: the parties of `C` are faulty
  have hG1 := hA (mainSched C d) (fun _ => false) C hCt
  -- setups `S_Q`: the parties of `C \ {p}` and of `Q` are faulty
  have hG2 : ∀ᵐ ω ∂μ, ∀ p : Fin n, ∀ Q : Finset (Fin n), p ∈ C → p ∉ Q → Q.card ≤ d →
      Fair (C.erase p ∪ Q) (r ω) → Correct (C.erase p ∪ Q) (fun _ => false) (r ω) := by
    refine ae_all_iff.2 fun p => ae_all_iff.2 fun Q => ?_
    by_cases hp : p ∈ C
    · by_cases hQ : Q.card ≤ d
      · have hcard : (C.erase p ∪ Q).card ≤ t := by
          have := Finset.card_union_le (C.erase p) Q
          rw [Finset.card_erase_of_mem hp] at this; omega
        filter_upwards [hA (mainSched C d) (fun _ => false) _ hcard] with ω hω _ _ _ using hω
      · exact Filter.Eventually.of_forall fun ω _ _ h => absurd h hQ
    · exact Filter.Eventually.of_forall fun ω h => absurd h hp
  -- setup `Final`
  have hG3 : ∀ᵐ ω ∂μ, ∀ p ∈ C, A.decision (A.init p false ω).1 = none := by
    refine ae_all_iff.2 fun p => ?_
    by_cases hp : p ∈ C
    · have : 1 ≤ t := (Finset.card_pos.2 ⟨p, hp⟩).trans_le hCt
      filter_upwards [no_init_decision A μ t hA this hn p] with ω h _ using h
    · exact Filter.Eventually.of_forall fun ω h => absurd h hp
  -- every party eventually decides in `Main`
  have hall : ∀ᵐ ω ∂μ, ∀ q, ∃ k, (r ω k).dec q ≠ none := by
    filter_upwards [hG1, hG2] with ω h1 h2 q
    by_cases hq : q ∈ C
    · classical
      let S : Finset (Fin n) :=
        Finset.univ.filter (fun s => ∃ k, s ∈ heldSrc C d q (r ω k).obs.links)
      have hmono : ∀ k k', k ≤ k' →
          heldSrc C d q (r ω k).obs.links ⊆ heldSrc C d q (r ω k').obs.links := by
        intro k k' hk
        obtain ⟨u, hu⟩ := links_prefix A ω _ _ hk
        rw [← hu]; exact heldSrc_append C d q _ _
      obtain ⟨K, hK⟩ : ∃ K, ∀ s ∈ S, s ∈ heldSrc C d q (r ω K).obs.links := by
        have : ∀ᶠ K in Filter.atTop, ∀ s ∈ S, s ∈ heldSrc C d q (r ω K).obs.links := by
          refine (Filter.eventually_all_finset S).2 fun s hs => ?_
          obtain ⟨k, hk⟩ := (Finset.mem_filter.1 hs).2
          exact Filter.eventually_atTop.2 ⟨k, fun K hK => hmono k K hK hk⟩
        exact this.exists
      have hScard : S.card ≤ d := (Finset.card_le_card hK).trans (heldSrc_card C d q _)
      have hqS : q ∉ S := fun h => not_mem_of_mem_heldSrc C d (hK q h) hq
      have hsub : ∀ k, heldSrc C d q (r ω k).obs.links ⊆ S :=
        fun k s hs => Finset.mem_filter.2 ⟨Finset.mem_univ _, k, hs⟩
      exact (h2 q S hq hqS hScard (main_fair_Q A ω _ C d S hsub)).1 q (by simp [hqS])
    · exact (h1 (main_fair_C A ω _ C d)).1 q hq
  have hallK : ∀ᵐ ω ∂μ, ∀ k, ∃ K, k ≤ K ∧ ∀ q, (r ω K).dec q ≠ none := by
    filter_upwards [hall] with ω h k
    have : ∀ᶠ K in Filter.atTop, ∀ q, (r ω K).dec q ≠ none := Filter.eventually_all.2 fun q => by
      obtain ⟨k, hk⟩ := h q
      exact Filter.eventually_atTop.2 ⟨k, fun K hK => dec_isSome_stable A ω _ _ hK hk⟩
    obtain ⟨K, h1, h2⟩ := (this.and (Filter.eventually_ge_atTop k)).exists
    exact ⟨K, h2, h1⟩
  -- once everybody has decided, the held messages are released: `Main` is fault-free fair
  have hfair : ∀ᵐ ω ∂μ, Fair ∅ (r ω) := by
    filter_upwards [hallK] with ω h
    intro k i e he _ _
    obtain ⟨K, hkK, hK⟩ := h k
    have hi : i < (r ω K).sent.length :=
      (List.getElem?_eq_some_iff.1 (getElem?_of_prefix A ω _ _ hkK he)).1
    exact oldest_eventually_delivered (mainAllowed C d) A ω _ (mainAllowed_mono A ω _ C d) hi
      (Or.inl fun q => Option.isSome_iff_ne_none.2 (hK q))
  -- the message count
  have hcount : ∀ᵐ ω ∂μ, ∃ K, (∀ q, (r ω K).dec q ≠ none) ∧
      ((C.card * (d + 1) : ℕ) : ℕ∞) ≤ msgsAtDecision (r ω) ∧
      ((C.card * (d + 1) : ℕ) : ℕ∞) ≤ (r ω K).sent.length := by
    filter_upwards [hallK, hG3] with ω h h3
    classical
    have hex : ∃ k, ∀ q, (r ω k).dec q ≠ none := let ⟨K, _, hK⟩ := h 0; ⟨K, hK⟩
    have hc := main_count A ω C d h3 fun p _ => Nat.find_spec hex p
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_, by exact_mod_cast hc⟩
    unfold msgsAtDecision
    split_ifs
    exact_mod_cast hc
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hfair, hG0, hall] with ω hf h0 hd
    refine ⟨hf, fun q => ?_⟩
    obtain ⟨-, -, hval⟩ := h0 hf
    obtain ⟨k, hk⟩ := hd q
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hk
    exact ⟨k, by rw [hv, hval false (fun _ _ => rfl) q (by simp) k v hv]⟩
  · filter_upwards [hcount] with ω ⟨_, _, h, _⟩ using h
  · filter_upwards [hcount] with ω ⟨K, _, _, h⟩
    exact h.trans (le_iSup (fun k => ((r ω k).sent.length : ℕ∞)) K)

/-- Arithmetic: the bound of `theorem_3_3` is at least `t² / 4`. -/
lemma sq_le_four_mul_bound (t : ℕ) : t ^ 2 ≤ 4 * ((t / 2 + 1) * ((t + 1) / 2 + 1)) := by
  have h1 : t + 1 ≤ 2 * (t / 2 + 1) := by omega
  have h2 : t + 2 ≤ 2 * ((t + 1) / 2 + 1) := by omega
  nlinarith [Nat.mul_le_mul h1 h2]

/-- **Theorem 3.3** of [Constantinescu–Dufay–Paramonov–Wattenhofer, PODC 2026]. Let `A` solve
asynchronous binary Byzantine agreement (agreement, strong unanimity validity, almost-sure
termination) against `t ≥ 1` static faults out of `n > t` parties, with arbitrary setup, PKI and
shared randomness encoded in `ω ∼ μ`. Then there is an input configuration (all `false`) and a
message scheduler (which only looks at message metadata) such that, with no faulty party:
* almost surely the execution is a legitimate asynchronous execution (every message is
  eventually delivered) in which all parties decide `false`;
* almost surely, at least `(t/2 + 1) * ((t+1)/2 + 1) ≥ t²/4` messages are sent before all parties
  have decided;
* consequently `E[M] ≥ t²/4`, both for `M` = messages sent until everybody has decided and for
  `M` = messages ever sent. -/
theorem theorem_3_3 [IsProbabilityMeasure μ] (hA : Solves A μ t) (ht : 1 ≤ t) (htn : t < n) :
    ∃ sched : Scheduler n,
      (∀ᵐ ω ∂μ, Fair ∅ (run A sched (fun _ => false) ω) ∧
        ∀ q, ∃ k, (run A sched (fun _ => false) ω k).dec q = some false) ∧
      (∀ᵐ ω ∂μ, (((t / 2 + 1) * ((t + 1) / 2 + 1) : ℕ) : ℕ∞) ≤
        msgsAtDecision (run A sched (fun _ => false) ω)) ∧
      (t : ℝ≥0∞) ^ 2 / 4 ≤ ∫⁻ ω, (msgsAtDecision (run A sched (fun _ => false) ω) : ℝ≥0∞) ∂μ ∧
      (t : ℝ≥0∞) ^ 2 / 4 ≤ ∫⁻ ω, (totalMsgs (run A sched (fun _ => false) ω) : ℝ≥0∞) ∂μ := by
  obtain ⟨C, -, hC⟩ := Finset.exists_subset_card_eq
    (show t / 2 + 1 ≤ (Finset.univ : Finset (Fin n)).card by simp; omega)
  obtain ⟨h1, h2, h3⟩ := lower_bound_general A μ t hA (by omega) C ((t + 1) / 2)
    (by omega) (by omega)
  rw [hC] at h2 h3
  set B := (t / 2 + 1) * ((t + 1) / 2 + 1) with hB
  have key : ∀ M : Ω → ℕ∞, (∀ᵐ ω ∂μ, (B : ℕ∞) ≤ M ω) →
      (t : ℝ≥0∞) ^ 2 / 4 ≤ ∫⁻ ω, (M ω : ℝ≥0∞) ∂μ := by
    intro M hM
    refine ENNReal.div_le_of_le_mul ?_
    calc (t : ℝ≥0∞) ^ 2 ≤ (B : ℝ≥0∞) * 4 := by
          have := sq_le_four_mul_bound t
          rw [← hB] at this
          exact_mod_cast (by omega : t ^ 2 ≤ B * 4)
      _ = (∫⁻ _, (B : ℝ≥0∞) ∂μ) * 4 := by simp [lintegral_const]
      _ ≤ (∫⁻ ω, (M ω : ℝ≥0∞) ∂μ) * 4 := by
          refine mul_le_mul_left (lintegral_mono_ae (hM.mono fun ω hω => ?_)) 4
          have := ENat.toENNReal_le.2 hω
          simpa using this
  exact ⟨mainSched C ((t + 1) / 2), h1, h2, key _ h2, key _ h3⟩

end LowerBound

end Podc.FewToManyFaultsBA.Async
