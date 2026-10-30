import Papers.PODC2025.AsymmetricDAGConsensus.RoundGather

/-!
# Algorithm 3: constant-round asymmetric gather — model and safety

Amores-Sesar, Cachin, Villacis, Zanolini, *DAG-based Consensus with Asymmetric Trust*, PODC 2025.

Algorithm 3 in the asynchronous interleaving model `Cslib.Byzantine.AsyncBroadcast` (Byzantine
faults, adaptive corruption, authenticated channels). Each handler of the pseudocode is a
disjunct of the send guard:

* line 43: arb-broadcast the input (`GMsg.val`);
* line 46: once the arb-delivered pairs `S` cover a quorum, send `DISTRIBUTES S` (once);
* line 48: on `DISTRIBUTES S` from `j` with `S ⊆ Sᵢ` and before sending `DISTRIBUTET`,
  acknowledge (`GMsg.ack j S`, addressed to `j`; `Tᵢ` is the union of the acknowledged sets);
* line 51: `READY` after acknowledgements of the own `DISTRIBUTES` from a quorum;
* lines 53/55: `CONFIRM` after `READY` from a quorum or `CONFIRM` from a kernel;
* line 57: `DISTRIBUTET Tᵢ` (once) after `CONFIRM` from a quorum, `Tᵢ` = union of the
  acknowledged sets; afterwards no more acknowledgements (`sentT`);
* lines 60/62: ag-deliver `U` once `DISTRIBUTET` messages `T_q` with `T_q ⊆ Sᵢ` were received
  from all `q` of a quorum; `U` contains these `T_q` and only received `DISTRIBUTET` sets
  with `T ⊆ Sᵢ`.

The asymmetric reliable broadcast of the inputs is the `val` message; its guarantees for the
guild that are not automatic in the model (consistency and totality for Byzantine senders) are
hypotheses on the execution (`RBC`), exactly the properties of the primitive of Alpos et al.

This file: the protocol, invariants of reachable states, and the safety lemmas
(Lemma 3.4, Lemma 3.5, Lemma 3.7 = common core, Lemma 3.8 validity and agreement) for any
guild `G` of the execution. Liveness (Lemmas 3.3, 3.6, termination) is in `Gather3Liveness`.
-/

namespace Podc.AsymmetricDAGConsensus

open Cslib.Byzantine.AsyncBroadcast Cslib.AsymmetricQuorum

variable {P V : Type*}

/-! ### Generic step lemma -/

section Generic

variable {M I O : Type*} [DecidableEq P] {A : Protocol P M I O} {x : P → I} {k : FaultKind}
  {t : ℕ}

-- CSLib candidate (AsyncBroadcast).
/-- A message that is broadcast after a step was broadcast before, or the step was its
broadcast (by an uncorrupted party whose guard held). -/
theorem step_sent_new {σ σ' : State P M O} (h : Step A x k t σ σ') {p : P} {m : M}
    (hm : (p, m) ∈ σ'.sent) :
    (p, m) ∈ σ.sent ∨ (p ∉ σ.bad ∧ A.send p (x p) (σ.inbox p) (σ.out p) m) := by
  cases h with
  | send p' m' hb hg =>
    rcases Set.mem_insert_iff.1 hm with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inr ⟨hb, hg⟩
    · exact Or.inl hm
  | _ => exact Or.inl hm

-- CSLib candidate (AsyncBroadcast).
/-- In an execution, a broadcast present at time `i + 1` was present at time `i` or was made by
the step `i → i + 1` (with the guard holding at time `i`). -/
theorem exec_sent_succ (E : Exec A x k t) (i : ℕ) {p : P} {m : M}
    (hm : (p, m) ∈ (E.σ (i + 1)).sent) :
    (p, m) ∈ (E.σ i).sent ∨
      (p ∉ (E.σ i).bad ∧ A.send p (x p) ((E.σ i).inbox p) ((E.σ i).out p) m) := by
  rcases E.step i with h | h
  · exact step_sent_new h hm
  · rw [h] at hm; exact Or.inl hm

end Generic

/-! ### The protocol -/

/-- Messages of Algorithm 3. `ack j S` is the acknowledgement addressed to `j` for its
`DISTRIBUTES S` (point-to-point messages are modelled as broadcasts carrying the addressee). -/
inductive GMsg (P V : Type*)
  | val (v : V)
  | distS (S : Set (P × V))
  | ack (j : P) (S : Set (P × V))
  | ready
  | confirm
  | distT (T : Set (P × V))

namespace Gather3

/-- `Sᵢ`: the arb-delivered pairs. -/
def delivered (ib : P → Set (GMsg P V)) : Set (P × V) := {sv | GMsg.val sv.2 ∈ ib sv.1}

/-- `Tᵢ`: the union of the acknowledged `DISTRIBUTES` sets. -/
def acked (out : Set (GMsg P V)) : Set (P × V) := {sv | ∃ j S, GMsg.ack j S ∈ out ∧ sv ∈ S}

/-- `φ` holds for all members of some quorum of `p`. -/
def QSays (Qs : P → Set (Finset P)) (p : P) (φ : P → Prop) : Prop := ∃ Q ∈ Qs p, ∀ q ∈ Q, φ q

/-- `φ` holds for all members of some kernel of `p`. -/
def KSays (Qs : P → Set (Finset P)) (p : P) (φ : P → Prop) : Prop :=
  ∃ K : Set P, IsKernel Qs p K ∧ ∀ q ∈ K, φ q

/-- A received `DISTRIBUTET T` from `q` whose pairs are all arb-delivered (line 60). -/
def QualT (ib : P → Set (GMsg P V)) (q : P) (T : Set (P × V)) : Prop :=
  GMsg.distT T ∈ ib q ∧ T ⊆ delivered ib

/-- Algorithm 3 for the asymmetric quorum system `Qs`. -/
def protocol (Qs : P → Set (Finset P)) : Protocol P (GMsg P V) V (Set (P × V)) where
  send p x ib out m :=
    m = .val x ∨
    (m = .distS (delivered ib) ∧ QSays Qs p (fun q => ∃ v, (q, v) ∈ delivered ib) ∧
      ∀ S, GMsg.distS S ∉ out) ∨
    (∃ j S, m = .ack j S ∧ GMsg.distS S ∈ ib j ∧ S ⊆ delivered ib ∧ ∀ T, GMsg.distT T ∉ out) ∨
    (m = .ready ∧ QSays Qs p (fun q => ∃ S, GMsg.ack p S ∈ ib q)) ∨
    (m = .confirm ∧ (QSays Qs p (fun q => GMsg.ready ∈ ib q) ∨
      KSays Qs p (fun q => GMsg.confirm ∈ ib q))) ∨
    (m = .distT (acked out) ∧ QSays Qs p (fun q => GMsg.confirm ∈ ib q) ∧
      ∀ T, GMsg.distT T ∉ out)
  decide p _ ib _ U := ∃ Q ∈ Qs p, ∃ Tq : P → Set (P × V),
    (∀ q ∈ Q, QualT ib q (Tq q) ∧ Tq q ⊆ U) ∧ U ⊆ {sv | ∃ q T, QualT ib q T ∧ sv ∈ T}

theorem delivered_mono {ib ib' : P → Set (GMsg P V)} (h : ∀ s, ib s ⊆ ib' s) :
    delivered ib ⊆ delivered ib' := fun _ hm => h _ hm

theorem acked_mono {out out' : Set (GMsg P V)} (h : out ⊆ out') : acked out ⊆ acked out' := by
  rintro sv ⟨j, S, hm, hs⟩; exact ⟨j, S, h hm, hs⟩

theorem QSays.mono {Qs : P → Set (Finset P)} {p : P} {φ ψ : P → Prop} (h : ∀ q, φ q → ψ q) :
    QSays Qs p φ → QSays Qs p ψ := by
  rintro ⟨Q, hQ, hφ⟩; exact ⟨Q, hQ, fun q hq => h q (hφ q hq)⟩

theorem KSays.mono {Qs : P → Set (Finset P)} {p : P} {φ ψ : P → Prop} (h : ∀ q, φ q → ψ q) :
    KSays Qs p φ → KSays Qs p ψ := by
  rintro ⟨K, hK, hφ⟩; exact ⟨K, hK, fun q hq => h q (hφ q hq)⟩

theorem QualT.mono {ib ib' : P → Set (GMsg P V)} (h : ∀ s, ib s ⊆ ib' s) {q : P}
    {T : Set (P × V)} (hT : QualT ib q T) : QualT ib' q T :=
  ⟨h q hT.1, hT.2.trans (delivered_mono h)⟩

/-- The common-core property of Definition 3.1 for executions: one set `S`, covering a quorum
of a guild member, is contained in every set ag-delivered (at any time) by a guild member. -/
def ExecCommonCore [DecidableEq P] {x : P → V} {Qs : P → Set (Finset P)} {fk : FaultKind}
    {t : ℕ} (G : Set P) (E : Exec (protocol Qs) x fk t) : Prop :=
  ∃ i ∈ G, ∃ Q ∈ Qs i, ∃ S : Set (P × V), (∀ s ∈ Q, ∃ v, (s, v) ∈ S) ∧
    ∀ k ∈ G, ∀ n U, (E.σ n).dec k = some U → S ⊆ U

/-! ### Invariants of reachable states -/

section Invariants

variable [DecidableEq P] {Qs : P → Set (Finset P)} {x : P → V} {fk : FaultKind} {t : ℕ}
  {σ : State P (GMsg P V) (Set (P × V))} (hσ : Reachable (protocol Qs) x fk t σ)
include hσ

theorem sent_val {p : P} {v : V} (h : (p, GMsg.val v) ∈ σ.sent) : v = x p := by
  have := hσ.sent_just (fun p m _ _ => ∀ v, m = GMsg.val v → v = x p)
    (fun _ _ _ _ _ _ _ _ h => h) ?_ h v rfl
  · exact this
  · intro p ib out m hg v hv
    subst hv
    rcases hg with h | ⟨h, -⟩ | ⟨j, S, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact (GMsg.val.inj h)
    all_goals cases h

theorem sent_distS {p : P} {S : Set (P × V)} (h : (p, GMsg.distS S) ∈ σ.sent) :
    S ⊆ delivered (σ.inbox p) ∧ QSays Qs p (fun q => ∃ v, (q, v) ∈ S) := by
  refine hσ.sent_just (fun p m ib _ => ∀ S, m = GMsg.distS S →
      S ⊆ delivered ib ∧ QSays Qs p (fun q => ∃ v, (q, v) ∈ S))
    (fun _ _ _ _ _ _ hib _ h S hS => ⟨(h S hS).1.trans (delivered_mono hib), (h S hS).2⟩)
    ?_ h S rfl
  intro p ib out m hg S hS
  subst hS
  rcases hg with h | ⟨h, hq, -⟩ | ⟨j, S', h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · cases h
  · cases h; exact ⟨subset_rfl, hq⟩
  all_goals cases h

theorem sent_ack {q j : P} {S : Set (P × V)} (h : (q, GMsg.ack j S) ∈ σ.sent) :
    GMsg.distS S ∈ σ.inbox q j ∧ S ⊆ delivered (σ.inbox q) := by
  refine hσ.sent_just (fun _ m ib _ => ∀ j S, m = GMsg.ack j S →
      GMsg.distS S ∈ ib j ∧ S ⊆ delivered ib)
    (fun _ _ _ _ _ _ hib _ h j S hS =>
      ⟨hib _ (h j S hS).1, (h j S hS).2.trans (delivered_mono hib)⟩) ?_ h j S rfl
  intro p ib out m hg j S hS
  subst hS
  rcases hg with h | ⟨h, -⟩ | ⟨j', S', h, h1, h2, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · cases h
  · cases h
  · cases h; exact ⟨h1, h2⟩
  all_goals cases h

theorem sent_ready {p : P} (h : (p, GMsg.ready) ∈ σ.sent) :
    QSays Qs p (fun q => ∃ S, GMsg.ack p S ∈ σ.inbox p q) := by
  refine hσ.sent_just (fun p m ib _ => m = GMsg.ready →
      QSays Qs p (fun q => ∃ S, GMsg.ack p S ∈ ib q))
    (fun _ _ _ _ _ _ hib _ h hm => (h hm).mono fun q ⟨S, hS⟩ => ⟨S, hib q hS⟩) ?_ h rfl
  intro p ib out m hg hm
  subst hm
  rcases hg with h | ⟨h, -⟩ | ⟨j', S', h, -⟩ | ⟨-, hq⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · cases h
  · cases h
  · cases h
  · exact hq
  all_goals cases h

theorem sent_distT {p : P} {T : Set (P × V)} (h : (p, GMsg.distT T) ∈ σ.sent) :
    QSays Qs p (fun q => GMsg.confirm ∈ σ.inbox p q) ∧ T ⊆ acked (σ.out p) := by
  refine hσ.sent_just (fun p m ib out => ∀ T, m = GMsg.distT T →
      QSays Qs p (fun q => GMsg.confirm ∈ ib q) ∧ T ⊆ acked out)
    (fun _ _ _ _ _ _ hib hout h T hT =>
      ⟨(h T hT).1.mono fun q hq => hib q hq, (h T hT).2.trans (acked_mono hout)⟩) ?_ h T rfl
  intro p ib out m hg T hT
  subst hT
  rcases hg with h | ⟨h, -⟩ | ⟨j', S', h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, hq, -⟩
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h; exact ⟨hq, subset_rfl⟩

theorem acked_sub_delivered (p : P) : acked (σ.out p) ⊆ delivered (σ.inbox p) := by
  rintro sv ⟨j, S, hm, hs⟩
  exact (sent_ack hσ hm).2 hs

theorem distT_sub_delivered {p : P} {T : Set (P × V)} (h : (p, GMsg.distT T) ∈ σ.sent) :
    T ⊆ delivered (σ.inbox p) :=
  (sent_distT hσ h).2.trans (acked_sub_delivered hσ p)

omit hσ in
/-- The `DISTRIBUTET` set of a process contains every set it acknowledged. -/
theorem ack_sub_distT (hσ : Reachable (protocol Qs) x fk t σ) {p j : P} {S T : Set (P × V)}
    (hT : (p, GMsg.distT T) ∈ σ.sent) (hS : (p, GMsg.ack j S) ∈ σ.sent) : S ⊆ T := by
  revert p j S T
  refine Reachable.induction (Inv := fun σ => ∀ {p j : P} {S T : Set (P × V)},
    (p, GMsg.distT T) ∈ σ.sent → (p, GMsg.ack j S) ∈ σ.sent → S ⊆ T)
    (by simp [State.init]) ?_ hσ
  intro σ σ' _ ih hst p j S T hT hS
  cases hst with
  | send p' m' _ hg =>
    rcases Set.mem_insert_iff.1 hT with he | hT' <;> rcases Set.mem_insert_iff.1 hS with he' | hS'
    · simp only [Prod.mk.injEq] at he he'
      obtain ⟨rfl, rfl⟩ := he
      cases he'.2
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rcases hg with h | ⟨h, -⟩ | ⟨j', S', h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩
      · cases h
      · cases h
      · cases h
      · cases h
      · cases h
      · cases h; exact fun sv hsv => ⟨j, S, hS', hsv⟩
    · simp only [Prod.mk.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      rcases hg with h | ⟨h, -⟩ | ⟨j', S', h, -, -, hno⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · cases h
      · cases h
      · exact absurd hT' (hno T)
      · cases h
      · cases h
      · cases h
    · exact ih hT' hS'
  | _ => exact ih hT hS

theorem distS_unique {p : P} {S S' : Set (P × V)} (h : (p, GMsg.distS S) ∈ σ.sent)
    (h' : (p, GMsg.distS S') ∈ σ.sent) : S = S' := by
  have := hσ.sent_excl (fun m => ∃ S, m = GMsg.distS S) ?_ h h' ⟨S, rfl⟩ ⟨S', rfl⟩
  · cases this; rfl
  · rintro p ib out m hg ⟨S, rfl⟩ m' hm' ⟨S', rfl⟩
    rcases hg with h | ⟨-, -, hno⟩ | ⟨j', S'', h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · cases h
    · exact hno S' hm'
    all_goals cases h

theorem dec_guard {p : P} {U : Set (P × V)} (h : σ.dec p = some U) :
    (protocol Qs).decide p (x p) (σ.inbox p) (σ.out p) U := by
  refine hσ.dec_just (fun p U ib out => (protocol Qs).decide p (x p) ib out U) ?_
    (fun _ _ _ _ h => h) h
  rintro p U ib ib' out out' hib - ⟨Q, hQ, Tq, hT, hU⟩
  refine ⟨Q, hQ, Tq, fun q hq => ⟨(hT q hq).1.mono hib, (hT q hq).2⟩, ?_⟩
  rintro sv hsv
  obtain ⟨q, T, hqT, hsvT⟩ := hU hsv
  exact ⟨q, T, hqT.mono hib, hsvT⟩

theorem dec_sub_delivered {p : P} {U : Set (P × V)} (h : σ.dec p = some U) :
    U ⊆ delivered (σ.inbox p) := by
  obtain ⟨-, -, -, -, hU⟩ := dec_guard hσ h
  intro sv hsv
  obtain ⟨q, T, hqT, hsvT⟩ := hU hsv
  exact hqT.2 hsvT

end Invariants

/-! ### Safety in executions with a guild -/

/-- The guarantees of the asymmetric reliable broadcast of the inputs for the guild `G` that
the model does not give for free (Alpos et al., asymmetric reliable broadcast): *consistency*
(guild members deliver the same value from a sender, and at most one) and *totality* (a value
delivered by one guild member is delivered by all). Validity and integrity for correct senders
follow from the model and fairness. -/
structure RBC [DecidableEq P] {Qs : P → Set (Finset P)} {x : P → V} {fk : FaultKind} {t : ℕ}
    (E : Exec (protocol Qs) x fk t) (G : Set P) : Prop where
  agree : ∀ q ∈ G, ∀ q' ∈ G, ∀ s v v' i j, GMsg.val v ∈ (E.σ i).inbox q s →
    GMsg.val v' ∈ (E.σ j).inbox q' s → v = v'
  total : ∀ q ∈ G, ∀ q' ∈ G, ∀ s v i, GMsg.val v ∈ (E.σ i).inbox q s →
    ∃ j, GMsg.val v ∈ (E.σ j).inbox q' s

variable [DecidableEq P] {Fs Qs : P → Set (Finset P)} {x : P → V} {fk : FaultKind} {t : ℕ}
  (E : Exec (protocol Qs) x fk t) {G : Set P}

/-- The faulty processes of an execution: those corrupted at some time. -/
def Faulty : Set P := {p | ¬ E.Correct p}

theorem correct_of_guild (hG : IsGuild Fs Qs (Faulty E) G) {g : P} (hg : g ∈ G) :
    E.Correct g := by
  have := hG.notMem_fault hg
  simpa [Faulty] using this

theorem genuine_of_correct {g q : P} (hg : E.Correct g) {i : ℕ} {m : GMsg P V}
    (hm : m ∈ (E.σ i).inbox q g) : (g, m) ∈ (E.σ i).sent :=
  (E.reachable i).genuine hm (hg i)

/-- **Lemma 3.4.** If a guild member has sent `CONFIRM` by time `i`, then some guild member has
received `READY` from all members of one of its quorums by time `i`. -/
theorem lemma_3_4 (hG : IsGuild Fs Qs (Faulty E) G) :
    ∀ i, ∀ g ∈ G, (g, GMsg.confirm) ∈ (E.σ i).sent →
      ∃ m ∈ G, QSays Qs m (fun q => GMsg.ready ∈ (E.σ i).inbox m q) := by
  intro i
  induction i with
  | zero => intro g _ h; rw [E.zero] at h; exact absurd h (by simp [State.init])
  | succ i ih =>
    intro g hg h
    have mono : ∀ m, QSays Qs m (fun q => GMsg.ready ∈ (E.σ i).inbox m q) →
        QSays Qs m (fun q => GMsg.ready ∈ (E.σ (i + 1)).inbox m q) :=
      fun m => QSays.mono fun q hq => E.inbox_mono (Nat.le_succ i) m q hq
    rcases exec_sent_succ E i h with h | ⟨-, hgd⟩
    · obtain ⟨m, hm, hq⟩ := ih g hg h
      exact ⟨m, hm, mono m hq⟩
    · rcases hgd with h | ⟨h, -⟩ | ⟨j', S', h, -⟩ | ⟨h, -⟩ | ⟨-, hc | hc⟩ | ⟨h, -⟩
      · cases h
      · cases h
      · cases h
      · cases h
      · exact ⟨g, hg, mono g hc⟩
      · -- a kernel of `g` sent `CONFIRM`; it contains a guild member
        obtain ⟨K, hK, hKc⟩ := hc
        obtain ⟨Qg, hQg, hQgG⟩ := hG.2 g hg
        obtain ⟨y, hyQ, hyK⟩ := hK Qg hQg
        have hyG : y ∈ G := hQgG hyQ
        have := genuine_of_correct E (correct_of_guild E hG hyG) (hKc y hyK)
        obtain ⟨m, hm, hq⟩ := ih y hyG this
        exact ⟨m, hm, mono m hq⟩
      · cases h

/-- The common-core candidate: a guild member `pᵢ` with its `DISTRIBUTES` set `S`, which covers
a quorum of `pᵢ`, and a quorum `Q` of `pᵢ` whose correct members all acknowledged `S` by time
`i₀`. This is what the proof of Lemma 3.5 constructs. -/
structure Candidate (G : Set P) (i₀ : ℕ) (pi : P) (S : Set (P × V)) (Q : Finset P) : Prop where
  mem : pi ∈ G
  distS : (pi, GMsg.distS S) ∈ (E.σ i₀).sent
  cover : QSays Qs pi (fun q => ∃ v, (q, v) ∈ S)
  quorum : Q ∈ Qs pi
  acks : ∀ q ∈ Q, E.Correct q → (q, GMsg.ack pi S) ∈ (E.σ i₀).sent

/-- If some guild member has sent `DISTRIBUTET`, a common-core candidate exists. -/
theorem exists_candidate (hG : IsGuild Fs Qs (Faulty E) G) (hQ : IsQuorumSystem Fs Qs)
    {g₀ : P} (hg₀ : g₀ ∈ G) {i₀ : ℕ} {T₀ : Set (P × V)}
    (hT₀ : (g₀, GMsg.distT T₀) ∈ (E.σ i₀).sent) : ∃ pi S Q, Candidate E G i₀ pi S Q := by
  have hr := E.reachable i₀
  -- a guild member of the CONFIRM quorum of `g₀` sent CONFIRM
  obtain ⟨Q₀, hQ₀, hc⟩ := (sent_distT hr hT₀).1
  obtain ⟨y, hyQ, hyG⟩ := hG.exists_mem_guild_of_quorum hQ hg₀ hQ₀
  have hyc : (y, GMsg.confirm) ∈ (E.σ i₀).sent :=
    genuine_of_correct E (correct_of_guild E hG hyG) (hc y hyQ)
  -- Lemma 3.4: a guild member received READY from a quorum
  obtain ⟨m, hmG, Qm, hQm, hr'⟩ := lemma_3_4 E hG i₀ y hyG hyc
  obtain ⟨pi, hpiQ, hpiG⟩ := hG.exists_mem_guild_of_quorum hQ hmG hQm
  have hpic := correct_of_guild E hG hpiG
  have hready : (pi, GMsg.ready) ∈ (E.σ i₀).sent := genuine_of_correct E hpic (hr' pi hpiQ)
  -- `pi` received acknowledgements from a quorum `Q`
  obtain ⟨Q, hQQ, hacks⟩ := sent_ready hr hready
  -- a correct member of `Q` acknowledged the (unique) DISTRIBUTES set of `pi`
  have hw := hG.1 pi hpiG
  obtain ⟨z, hzQ, -, hzF⟩ := hQ.exists_mem_inter_notMem hw hw hQQ hQQ
  have hzc : E.Correct z := by simpa [Faulty] using hzF
  obtain ⟨S, hS⟩ := hacks z hzQ
  have hzack := genuine_of_correct E hzc hS
  have hdS := genuine_of_correct E hpic (sent_ack hr hzack).1
  refine ⟨pi, S, Q, hpiG, hdS, (sent_distS hr hdS).2, hQQ, fun q hq hqc => ?_⟩
  obtain ⟨S', hS'⟩ := hacks q hq
  have hqack := genuine_of_correct E hqc hS'
  have hdS' := genuine_of_correct E hpic (sent_ack hr hqack).1
  rwa [← distS_unique hr hdS hdS'] at hqack

/-- **Lemma 3.5.** If some guild member sends `DISTRIBUTET`, then there are a guild member `pᵢ`,
its `DISTRIBUTES` set `S` (covering a quorum of `pᵢ`) and a quorum `Q` of `pᵢ` such that every
correct member of `Q` received `DISTRIBUTES S` from `pᵢ` and acknowledged it, and every
`DISTRIBUTET` set it ever sends contains `S`. -/
theorem lemma_3_5 (hG : IsGuild Fs Qs (Faulty E) G) (hQ : IsQuorumSystem Fs Qs)
    (h : ∃ g ∈ G, ∃ i T, (g, GMsg.distT T) ∈ (E.σ i).sent) :
    ∃ pi ∈ G, ∃ S, (∃ i, (pi, GMsg.distS S) ∈ (E.σ i).sent) ∧
      QSays Qs pi (fun q => ∃ v, (q, v) ∈ S) ∧
      ∃ Q ∈ Qs pi, ∀ q ∈ Q, E.Correct q →
        (∃ i, GMsg.distS S ∈ (E.σ i).inbox q pi ∧ (q, GMsg.ack pi S) ∈ (E.σ i).sent) ∧
        ∀ i T, (q, GMsg.distT T) ∈ (E.σ i).sent → S ⊆ T := by
  obtain ⟨g₀, hg₀, i₀, T₀, hT₀⟩ := h
  obtain ⟨pi, S, Q, hc⟩ := exists_candidate E hG hQ hg₀ hT₀
  refine ⟨pi, hc.mem, S, ⟨i₀, hc.distS⟩, hc.cover, Q, hc.quorum, fun q hq hqc => ⟨⟨i₀,
    (sent_ack (E.reachable i₀) (hc.acks q hq hqc)).1, hc.acks q hq hqc⟩, fun i T hT => ?_⟩⟩
  exact ack_sub_distT (E.reachable (max i i₀)) (E.sent_mono (le_max_left _ _) hT)
    (E.sent_mono (le_max_right _ _) (hc.acks q hq hqc))

/-- **Lemma 3.7 (common core), safety part.** If some guild member sends `DISTRIBUTET`, the
`DISTRIBUTES` set of a guild member, which covers one of its quorums, is contained in every set
ag-delivered by a guild member. -/
theorem lemma_3_7 (hG : IsGuild Fs Qs (Faulty E) G) (hQ : IsQuorumSystem Fs Qs)
    (h : ∃ g ∈ G, ∃ i T, (g, GMsg.distT T) ∈ (E.σ i).sent) : ExecCommonCore G E := by
  obtain ⟨g₀, hg₀, i₀, T₀, hT₀⟩ := h
  obtain ⟨pi, S, Q, hc⟩ := exists_candidate E hG hQ hg₀ hT₀
  obtain ⟨QS, hQS, hcov⟩ := hc.cover
  refine ⟨pi, hc.mem, QS, hQS, S, hcov, fun k hk n U hU => ?_⟩
  obtain ⟨Qk, hQk, Tq, hT, -⟩ := dec_guard (E.reachable n) hU
  obtain ⟨q, hqQ, hqQk, hqF⟩ :=
    hQ.exists_mem_inter_notMem (hG.1 pi hc.mem) (hG.1 k hk) hc.quorum hQk
  have hqc : E.Correct q := by simpa [Faulty] using hqF
  have hdT := genuine_of_correct E hqc (hT q hqQk).1.1
  have := ack_sub_distT (E.reachable (max n i₀)) (E.sent_mono (le_max_left _ _) hdT)
    (E.sent_mono (le_max_right _ _) (hc.acks q hqQ hqc))
  exact this.trans (hT q hqQk).2

/-- **Lemma 3.8, validity.** If a guild member ag-delivers a set containing `(s, v)` and `s` is
wise, then `v` is the input of `s`. -/
theorem validity {k s : P} (hs : Wise Fs (Faulty E) s) {n : ℕ} {U : Set (P × V)}
    (hU : (E.σ n).dec k = some U) {v : V} (hv : (s, v) ∈ U) : v = x s := by
  have hr := E.reachable n
  have h1 := dec_sub_delivered hr hU hv
  have hsc : E.Correct s := by simpa [Faulty] using hs.1
  exact sent_val hr (genuine_of_correct E hsc h1)

/-- **Lemma 3.8, agreement.** Two guild members never ag-deliver different values of the same
sender. -/
theorem agreement (hrbc : RBC E G) {k k' s : P} (hk : k ∈ G) (hk' : k' ∈ G) {n n' : ℕ}
    {U U' : Set (P × V)} (hU : (E.σ n).dec k = some U) (hU' : (E.σ n').dec k' = some U')
    {v v' : V} (hv : (s, v) ∈ U) (hv' : (s, v') ∈ U') : v = v' :=
  hrbc.agree k hk k' hk' s v v' n n' (dec_sub_delivered (E.reachable n) hU hv)
    (dec_sub_delivered (E.reachable n') hU' hv')

end Gather3

end Podc.AsymmetricDAGConsensus
