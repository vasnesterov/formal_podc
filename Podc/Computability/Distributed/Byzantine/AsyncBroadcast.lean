import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/Byzantine/AsyncBroadcast.lean

/-!
# Asynchronous broadcast protocols with adaptive crash or Byzantine corruption

A small interleaving model for *threshold broadcast protocols* ("upon receiving `⟨echo, v⟩` from
`t + 1` parties, send `⟨echo, v⟩` to all") in the fully asynchronous message-passing model.

* A `Protocol P M I O` is given by two guards: `send p x ib out m` (party `p` with input `x`,
  inbox `ib s` = messages received from `s`, own broadcasts `out`, may broadcast `m`) and
  `decide p x ib out o`. Guards are arbitrary predicates, so "upon"/"wait until" clauses that
  look at *some* `n − t` received messages are modelled liberally ("there are `n − t` senders
  such that …"); this is a superset of the behaviours of the deterministic code, since the
  asynchronous adversary controls the order of receptions.
* A `State` records the broadcasts `sent` (pairs `(p, m)`, only made by uncorrupted parties),
  the receptions `rcv` (triples `(q, s, m)`: `q` received `m` from `s`), the decisions `dec`
  (made at most once, by uncorrupted parties; they persist if the party is corrupted later) and
  the corrupted set `bad`.
* `Step`: an uncorrupted party broadcasts or decides when its guard holds; any broadcast
  message is delivered to any party at any time (asynchrony, no loss of information about the
  sender: channels are authenticated); a corrupted party can, in the `byzantine` fault kind,
  make anybody receive anything from it (equivocation); the adversary corrupts parties
  **adaptively** (`corrupt`), at most `t` in total. A corrupted party takes no more protocol
  steps (crash), its earlier broadcasts may still be delivered (or not: a crash in the middle
  of a broadcast).
* `Exec` (infinite executions with stuttering) and `Exec.Fair`: messages between parties that
  are never corrupted are eventually delivered, and a never-corrupted party whose guard holds
  forever eventually acts (weak fairness). `exists_fair`: fair executions exist (round robin
  over all events), so liveness results are not vacuous.

## Main lemmas

* `Reachable.bad_ncard_le`, `Reachable.genuine` (a message received from a currently
  uncorrupted party was broadcast by it), `Reachable.sent_just`/`Reachable.dec_just`
  (a monotone justification of a broadcast/decision persists), `Reachable.sent_excl`
  (exclusive message classes are broadcast at most once).
* Quorum counting: `exists_mem_not_mem_of_ncard_lt`, `exists_mem_inter_not_mem`.
* Liveness helpers: `Exec.ncard_not_correct_le`, `Exec.eventually_sent`, `Exec.eventually_dec`,
  `Exec.eventually_rcv_all`, `exists_forall_of_mono`.
-/

namespace Cslib.Byzantine.AsyncBroadcast

/-- The kind of faults: crash (corrupted parties stop) or Byzantine (corrupted parties stop
following the protocol and may send arbitrary messages to anybody). -/
inductive FaultKind
  | crash
  | byzantine
  deriving DecidableEq

/-- A broadcast protocol, given by its guards. `send p x ib out m`: party `p` with input `x`,
inbox `ib` (`ib s` = messages received from `s`) and own broadcasts `out` may broadcast `m`.
`decide p x ib out o`: it may decide `o`. -/
structure Protocol (P M I O : Type*) where
  /-- Guard of broadcasting a message. -/
  send : P → I → (P → Set M) → Set M → M → Prop
  /-- Guard of deciding an output. -/
  decide : P → I → (P → Set M) → Set M → O → Prop

/-- A global state. -/
structure State (P M O : Type*) where
  /-- `(p, m)`: `p` broadcast `m` (while uncorrupted). -/
  sent : Set (P × M)
  /-- `(q, s, m)`: `q` received `m` from `s`. -/
  rcv : Set (P × P × M)
  /-- Decisions (made while uncorrupted). -/
  dec : P → Option O
  /-- The corrupted parties. -/
  bad : Set P

variable {P M I O : Type*}

namespace State

/-- The inbox of `q`: `σ.inbox q s` = the messages `q` received from `s`. -/
def inbox (σ : State P M O) (q : P) : P → Set M := fun s => {m | (q, s, m) ∈ σ.rcv}

/-- The broadcasts of `p`. -/
def out (σ : State P M O) (p : P) : Set M := {m | (p, m) ∈ σ.sent}

/-- The initial state. -/
def init : State P M O := ⟨∅, ∅, fun _ => none, ∅⟩

@[simp] theorem mem_inbox {σ : State P M O} {q s : P} {m : M} :
    m ∈ σ.inbox q s ↔ (q, s, m) ∈ σ.rcv := Iff.rfl

@[simp] theorem mem_out {σ : State P M O} {p : P} {m : M} : m ∈ σ.out p ↔ (p, m) ∈ σ.sent :=
  Iff.rfl

end State

variable [DecidableEq P]

/-- One step of the asynchronous system with inputs `x`, fault kind `k` and at most `t`
corruptions. -/
inductive Step (A : Protocol P M I O) (x : P → I) (k : FaultKind) (t : ℕ) :
    State P M O → State P M O → Prop
  /-- An uncorrupted party broadcasts a message allowed by its guard. -/
  | send (σ : State P M O) (p : P) (m : M) :
      p ∉ σ.bad → A.send p (x p) (σ.inbox p) (σ.out p) m →
      Step A x k t σ { σ with sent := insert (p, m) σ.sent }
  /-- A broadcast message is delivered to some party. -/
  | deliver (σ : State P M O) (q s : P) (m : M) :
      (s, m) ∈ σ.sent → Step A x k t σ { σ with rcv := insert (q, s, m) σ.rcv }
  /-- A Byzantine party makes `q` receive an arbitrary message. -/
  | inject (σ : State P M O) (q s : P) (m : M) :
      k = .byzantine → s ∈ σ.bad → Step A x k t σ { σ with rcv := insert (q, s, m) σ.rcv }
  /-- An uncorrupted party that has not decided yet decides. -/
  | decide (σ : State P M O) (p : P) (o : O) :
      p ∉ σ.bad → σ.dec p = none → A.decide p (x p) (σ.inbox p) (σ.out p) o →
      Step A x k t σ { σ with dec := Function.update σ.dec p (some o) }
  /-- The adaptive adversary corrupts a party (at most `t` in total). -/
  | corrupt (σ : State P M O) (p : P) :
      (insert p σ.bad).ncard ≤ t → Step A x k t σ { σ with bad := insert p σ.bad }

/-- `σ'` is reachable from `σ`. -/
abbrev Reach (A : Protocol P M I O) (x : P → I) (k : FaultKind) (t : ℕ) :
    State P M O → State P M O → Prop :=
  Relation.ReflTransGen (Step A x k t)

/-- `σ` is reachable from the initial state. -/
def Reachable (A : Protocol P M I O) (x : P → I) (k : FaultKind) (t : ℕ)
    (σ : State P M O) : Prop :=
  Reach A x k t State.init σ

variable {A : Protocol P M I O} {x : P → I} {k : FaultKind} {t : ℕ}

/-! ### Monotonicity -/

namespace Step

variable {σ σ' : State P M O}

theorem sent_subset (h : Step A x k t σ σ') : σ.sent ⊆ σ'.sent := by
  cases h <;> first | exact Set.subset_insert _ _ | exact le_rfl

theorem rcv_subset (h : Step A x k t σ σ') : σ.rcv ⊆ σ'.rcv := by
  cases h <;> first | exact Set.subset_insert _ _ | exact le_rfl

theorem bad_subset (h : Step A x k t σ σ') : σ.bad ⊆ σ'.bad := by
  cases h <;> first | exact Set.subset_insert _ _ | exact le_rfl

theorem dec_mono (h : Step A x k t σ σ') {p : P} {o : O} (hp : σ.dec p = some o) :
    σ'.dec p = some o := by
  cases h with
  | decide q _ _ _ hq =>
    by_cases hpq : p = q
    · subst hpq; simp_all
    · simp [Function.update_of_ne hpq, hp]
  | _ => exact hp

end Step

namespace Reach

variable {σ σ' : State P M O}

theorem sent_subset (h : Reach A x k t σ σ') : σ.sent ⊆ σ'.sent := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact ih.trans hs.sent_subset

theorem rcv_subset (h : Reach A x k t σ σ') : σ.rcv ⊆ σ'.rcv := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact ih.trans hs.rcv_subset

theorem bad_subset (h : Reach A x k t σ σ') : σ.bad ⊆ σ'.bad := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact ih.trans hs.bad_subset

theorem dec_mono (h : Reach A x k t σ σ') {p : P} {o : O} (hp : σ.dec p = some o) :
    σ'.dec p = some o := by
  induction h with
  | refl => exact hp
  | tail _ hs ih => exact hs.dec_mono ih

end Reach

theorem Reachable.reach {σ σ' : State P M O} (h : Reachable A x k t σ)
    (h' : Reach A x k t σ σ') : Reachable A x k t σ' :=
  Relation.ReflTransGen.trans h h'

theorem Reachable.step {σ σ' : State P M O} (h : Reachable A x k t σ)
    (h' : Step A x k t σ σ') : Reachable A x k t σ' :=
  Relation.ReflTransGen.tail h h'

/-- Proving an invariant by induction on reachability. -/
theorem Reachable.induction {Inv : State P M O → Prop} (h0 : Inv State.init)
    (hs : ∀ σ σ', Reachable A x k t σ → Inv σ → Step A x k t σ σ' → Inv σ')
    {σ : State P M O} (h : Reachable A x k t σ) : Inv σ := by
  unfold Reachable at h
  induction h with
  | refl => exact h0
  | tail hr hst ih => exact hs _ _ hr ih hst

/-! ### Basic invariants -/

/-- At most `t` parties are corrupted. -/
theorem Reachable.bad_ncard_le {σ : State P M O} [Finite P] (h : Reachable A x k t σ) :
    σ.bad.ncard ≤ t := by
  refine Reachable.induction (Inv := fun σ => σ.bad.ncard ≤ t) (by simp [State.init]) ?_ h
  intro σ σ' _ ih hst
  cases hst with
  | corrupt _ hc => exact hc
  | _ => exact ih

/-- Received messages were broadcast, unless the sender is a corrupted Byzantine party. -/
theorem Reachable.rcv_origin {σ : State P M O} (h : Reachable A x k t σ) {q s : P} {m : M}
    (hm : (q, s, m) ∈ σ.rcv) : (s, m) ∈ σ.sent ∨ (k = .byzantine ∧ s ∈ σ.bad) := by
  revert q s m
  refine Reachable.induction
    (Inv := fun σ => ∀ {q s : P} {m : M}, (q, s, m) ∈ σ.rcv →
      (s, m) ∈ σ.sent ∨ (k = .byzantine ∧ s ∈ σ.bad)) (by simp [State.init]) ?_ h
  intro σ σ' _ ih hst q s m hm
  cases hst with
  | send p m' _ _ =>
    rcases ih hm with h1 | h1
    · exact Or.inl (Set.mem_insert_of_mem _ h1)
    · exact Or.inr h1
  | deliver q' s' m' hs =>
    rcases Set.mem_insert_iff.1 hm with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inl hs
    · exact ih hm
  | inject q' s' m' hk hb =>
    rcases Set.mem_insert_iff.1 hm with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inr ⟨hk, hb⟩
    · exact ih hm
  | decide => exact ih hm
  | corrupt p _ =>
    rcases ih hm with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, Set.mem_insert_of_mem _ h2⟩

/-- A message received from a currently uncorrupted party was broadcast by it. -/
theorem Reachable.genuine {σ : State P M O} (h : Reachable A x k t σ) {q s : P} {m : M}
    (hm : m ∈ σ.inbox q s) (hs : s ∉ σ.bad) : (s, m) ∈ σ.sent := by
  rcases h.rcv_origin hm with h1 | ⟨_, h2⟩
  · exact h1
  · exact absurd h2 hs

/-- With crash faults every received message was broadcast. -/
theorem Reachable.genuine_crash {σ : State P M O} (h : Reachable A x .crash t σ) {q s : P}
    {m : M} (hm : m ∈ σ.inbox q s) : (s, m) ∈ σ.sent := by
  rcases h.rcv_origin hm with h1 | ⟨h2, _⟩
  · exact h1
  · cases h2

/-- A justification of broadcasts that is monotone in the inbox and the own broadcasts holds
for every broadcast message, with respect to the current inbox. -/
theorem Reachable.sent_just (J : P → M → (P → Set M) → Set M → Prop)
    (hmono : ∀ p m ib ib' out out', (∀ s, ib s ⊆ ib' s) → out ⊆ out' → J p m ib out →
      J p m ib' out')
    (hJ : ∀ p ib out m, A.send p (x p) ib out m → J p m ib out)
    {σ : State P M O} (h : Reachable A x k t σ) {p : P} {m : M} (hm : (p, m) ∈ σ.sent) :
    J p m (σ.inbox p) (σ.out p) := by
  revert p m
  refine Reachable.induction (Inv := fun σ => ∀ {p : P} {m : M}, (p, m) ∈ σ.sent →
      J p m (σ.inbox p) (σ.out p)) (by simp [State.init]) ?_ h
  intro σ σ' _ ih hst p m hm
  have hsub := hst.sent_subset
  have hrsub := hst.rcv_subset
  have mono : ∀ {p m}, J p m (σ.inbox p) (σ.out p) → J p m (σ'.inbox p) (σ'.out p) :=
    fun hj => hmono _ _ _ _ _ _ (fun s _ hm => hrsub hm) (fun _ hm => hsub hm) hj
  cases hst with
  | send p' m' _ hg =>
    rcases Set.mem_insert_iff.1 hm with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact mono (hJ _ _ _ _ hg)
    · exact mono (ih hm)
  | _ => exact mono (ih hm)

/-- A justification of decisions that is monotone in the inbox and the own broadcasts holds for
every decision, with respect to the current inbox. -/
theorem Reachable.dec_just (J : P → O → (P → Set M) → Set M → Prop)
    (hmono : ∀ p o ib ib' out out', (∀ s, ib s ⊆ ib' s) → out ⊆ out' → J p o ib out →
      J p o ib' out')
    (hJ : ∀ p ib out o, A.decide p (x p) ib out o → J p o ib out)
    {σ : State P M O} (h : Reachable A x k t σ) {p : P} {o : O} (ho : σ.dec p = some o) :
    J p o (σ.inbox p) (σ.out p) := by
  revert p o
  refine Reachable.induction (Inv := fun σ => ∀ {p : P} {o : O}, σ.dec p = some o →
      J p o (σ.inbox p) (σ.out p)) (by simp [State.init]) ?_ h
  intro σ σ' _ ih hst p o ho
  have hsub := hst.sent_subset
  have hrsub := hst.rcv_subset
  have mono : ∀ {p o}, J p o (σ.inbox p) (σ.out p) → J p o (σ'.inbox p) (σ'.out p) :=
    fun hj => hmono _ _ _ _ _ _ (fun s _ hm => hrsub hm) (fun _ hm => hsub hm) hj
  cases hst with
  | decide p' o' _ _ hg =>
    by_cases hpp : p = p'
    · subst hpp
      simp only [Function.update_self, Option.some.injEq] at ho
      subst ho
      exact mono (hJ _ _ _ _ hg)
    · simp only [Function.update_of_ne hpp] at ho
      exact mono (ih ho)
  | _ => exact mono (ih ho)

/-- If the guard of a message of class `φ` requires that no message of class `φ` was broadcast
before, every party broadcasts at most one message of class `φ`. -/
theorem Reachable.sent_excl (φ : M → Prop)
    (hφ : ∀ p ib out m, A.send p (x p) ib out m → φ m → ∀ m' ∈ out, ¬ φ m')
    {σ : State P M O} (h : Reachable A x k t σ) {p : P} {m m' : M} (hm : (p, m) ∈ σ.sent)
    (hm' : (p, m') ∈ σ.sent) (h1 : φ m) (h2 : φ m') : m = m' := by
  revert p m m'
  refine Reachable.induction (Inv := fun σ => ∀ {p : P} {m m' : M}, (p, m) ∈ σ.sent →
      (p, m') ∈ σ.sent → φ m → φ m' → m = m') (by simp [State.init]) ?_ h
  intro σ σ' _ ih hst p m m' hm hm' h1 h2
  cases hst with
  | send p' m'' _ hg =>
    rcases Set.mem_insert_iff.1 hm with he | ho <;>
      rcases Set.mem_insert_iff.1 hm' with he' | ho'
    · simp only [Prod.mk.injEq] at he he'
      rw [he.2, he'.2]
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact absurd h2 (hφ _ _ _ _ hg h1 m' ho')
    · simp only [Prod.mk.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      exact absurd h1 (hφ _ _ _ _ hg h2 m ho)
    · exact ih ho ho' h1 h2
  | _ => exact ih hm hm' h1 h2

/-! ### Counting senders -/

/-- The number of parties from which `m` was received. -/
noncomputable def cnt (ib : P → Set M) (m : M) : ℕ := {s | m ∈ ib s}.ncard

/-- The number of parties from which some message satisfying `φ` was received. -/
noncomputable def cntP (ib : P → Set M) (φ : M → Prop) : ℕ := {s | ∃ m ∈ ib s, φ m}.ncard

omit [DecidableEq P] in
theorem cnt_mono [Finite P] {ib ib' : P → Set M} (h : ∀ s, ib s ⊆ ib' s) (m : M) :
    cnt ib m ≤ cnt ib' m :=
  Set.ncard_le_ncard fun s hs => h s hs

omit [DecidableEq P] in
theorem cntP_mono [Finite P] {ib ib' : P → Set M} (h : ∀ s, ib s ⊆ ib' s) (φ : M → Prop) :
    cntP ib φ ≤ cntP ib' φ :=
  Set.ncard_le_ncard fun _ ⟨m, hm, hφ⟩ => ⟨m, h _ hm, hφ⟩

omit [DecidableEq P] in
theorem le_cnt [Finite P] {ib : P → Set M} {m : M} {S : Set P} (h : ∀ s ∈ S, m ∈ ib s) :
    S.ncard ≤ cnt ib m :=
  Set.ncard_le_ncard fun s hs => h s hs

omit [DecidableEq P] in
theorem le_cntP [Finite P] {ib : P → Set M} {φ : M → Prop} {S : Set P}
    (h : ∀ s ∈ S, ∃ m ∈ ib s, φ m) : S.ncard ≤ cntP ib φ :=
  Set.ncard_le_ncard fun s hs => h s hs

omit [DecidableEq P] in
theorem cnt_le_cntP [Finite P] {ib : P → Set M} {m : M} {φ : M → Prop} (h : φ m) :
    cnt ib m ≤ cntP ib φ :=
  Set.ncard_le_ncard fun _ hs => ⟨m, hs, h⟩

omit [DecidableEq P] in
/-- If more parties than `|B|` belong to `S`, one of them is outside `B`. -/
theorem exists_mem_not_mem_of_ncard_lt [Finite P] {S B : Set P} (h : B.ncard < S.ncard) :
    ∃ s ∈ S, s ∉ B :=
  Set.exists_mem_notMem_of_ncard_lt_ncard h

omit [DecidableEq P] in
/-- Quorum intersection: if `|S₁| + |S₂| > n + |B|`, some party of `S₁ ∩ S₂` is outside `B`. -/
theorem exists_mem_inter_not_mem [Fintype P] {S₁ S₂ B : Set P}
    (h : Fintype.card P + B.ncard < S₁.ncard + S₂.ncard) : ∃ s ∈ S₁, s ∈ S₂ ∧ s ∉ B := by
  have h1 := Set.ncard_inter_add_ncard_union S₁ S₂
  have h2 : (S₁ ∪ S₂).ncard ≤ Fintype.card P := by
    rw [← Nat.card_eq_fintype_card]; exact Set.ncard_le_card _
  obtain ⟨s, hs, hsB⟩ := exists_mem_not_mem_of_ncard_lt (S := S₁ ∩ S₂) (B := B) (by omega)
  exact ⟨s, hs.1, hs.2, hsB⟩

/-- `n − t` senders of a message include a currently uncorrupted one (if `t < n − t`). -/
theorem Reachable.exists_good [Fintype P] {σ : State P M O} (h : Reachable A x k t σ)
    {S : Set P} (hS : t < S.ncard) : ∃ s ∈ S, s ∉ σ.bad :=
  exists_mem_not_mem_of_ncard_lt (lt_of_le_of_lt h.bad_ncard_le hS)

/-! ### Executions and fairness -/

/-- An infinite execution (with stuttering steps). -/
structure Exec (A : Protocol P M I O) (x : P → I) (k : FaultKind) (t : ℕ) where
  /-- The states. -/
  σ : ℕ → State P M O
  zero : σ 0 = State.init
  step : ∀ i, Step A x k t (σ i) (σ (i + 1)) ∨ σ (i + 1) = σ i

namespace Exec

variable (E : Exec A x k t)

/-- A party is correct in the execution if it is never corrupted. -/
def Correct (p : P) : Prop := ∀ i, p ∉ (E.σ i).bad

/-- Weak fairness: messages from correct to correct parties are delivered, and a correct party
whose guard holds forever eventually broadcasts / decides. Corrupted parties' messages and the
adversary's injections are not constrained. -/
structure Fair : Prop where
  deliver : ∀ q s m i, E.Correct q → E.Correct s → (s, m) ∈ (E.σ i).sent →
    ∃ j, (q, s, m) ∈ (E.σ j).rcv
  send : ∀ p m i, E.Correct p →
    (∀ j, i ≤ j → A.send p (x p) ((E.σ j).inbox p) ((E.σ j).out p) m) →
    ∃ j, (p, m) ∈ (E.σ j).sent
  decide : ∀ p o i, E.Correct p →
    (∀ j, i ≤ j → A.decide p (x p) ((E.σ j).inbox p) ((E.σ j).out p) o) →
    ∃ j, (E.σ j).dec p ≠ none

theorem reach_le {i j : ℕ} (hij : i ≤ j) : Reach A x k t (E.σ i) (E.σ j) := by
  induction hij with
  | refl => exact Relation.ReflTransGen.refl
  | step _ ih =>
    rcases E.step _ with h | h
    · exact ih.tail h
    · rw [h]; exact ih

theorem reachable (i : ℕ) : Reachable A x k t (E.σ i) := by
  have := E.reach_le (Nat.zero_le i)
  rwa [E.zero] at this

theorem sent_mono {i j : ℕ} (hij : i ≤ j) {p : P} {m : M} (h : (p, m) ∈ (E.σ i).sent) :
    (p, m) ∈ (E.σ j).sent :=
  (E.reach_le hij).sent_subset h

theorem rcv_mono {i j : ℕ} (hij : i ≤ j) {q s : P} {m : M} (h : (q, s, m) ∈ (E.σ i).rcv) :
    (q, s, m) ∈ (E.σ j).rcv :=
  (E.reach_le hij).rcv_subset h

theorem inbox_mono {i j : ℕ} (hij : i ≤ j) (q s : P) :
    (E.σ i).inbox q s ⊆ (E.σ j).inbox q s :=
  fun _ h => E.rcv_mono hij h

theorem dec_mono {i j : ℕ} (hij : i ≤ j) {p : P} {o : O} (h : (E.σ i).dec p = some o) :
    (E.σ j).dec p = some o :=
  (E.reach_le hij).dec_mono h

theorem bad_mono {i j : ℕ} (hij : i ≤ j) : (E.σ i).bad ⊆ (E.σ j).bad :=
  (E.reach_le hij).bad_subset

/-- At most `t` parties are not correct. -/
theorem ncard_not_correct_le [Fintype P] : {p | ¬ E.Correct p}.ncard ≤ t := by
  classical
  have hp : ∀ p, ¬ E.Correct p → ∃ i, p ∈ (E.σ i).bad := by
    intro p hp; simpa [Correct] using hp
  let idx : P → ℕ := fun p => if h : ¬ E.Correct p then (hp p h).choose else 0
  let N := Finset.univ.sup idx
  have hsub : {p | ¬ E.Correct p} ⊆ (E.σ N).bad := by
    intro p hpc
    have h1 : p ∈ (E.σ (idx p)).bad := by
      simp only [idx, dite_eq_left_of_eq_true (eq_true (show ¬ E.Correct p from hpc))]
      exact (hp p hpc).choose_spec
    exact E.bad_mono (Finset.le_sup (f := idx) (Finset.mem_univ p)) h1
  exact (Set.ncard_le_ncard hsub).trans (E.reachable N).bad_ncard_le

/-- At least `n − t` parties are correct. -/
theorem card_sub_le_ncard_correct [Fintype P] :
    Fintype.card P - t ≤ {p | E.Correct p}.ncard := by
  have h1 := E.ncard_not_correct_le
  have h2 := Set.ncard_add_ncard_compl {p | E.Correct p}
  rw [Nat.card_eq_fintype_card] at h2
  have : {p | E.Correct p}ᶜ = {p | ¬ E.Correct p} := rfl
  rw [this] at h2
  omega

/-- All but at most `t` members of a set are correct. -/
theorem ncard_le_ncard_inter_correct_add [Fintype P] (S : Set P) :
    S.ncard ≤ (S ∩ {p | E.Correct p}).ncard + t := by
  have h1 : S ⊆ (S ∩ {p | E.Correct p}) ∪ {p | ¬ E.Correct p} := fun s hs => by
    by_cases hc : E.Correct s
    · exact Or.inl ⟨hs, hc⟩
    · exact Or.inr hc
  have h2 := (Set.ncard_le_ncard h1).trans (Set.ncard_union_le _ _)
  have h3 := E.ncard_not_correct_le
  omega

/-- A correct party that keeps a guard for a message of class `φ` enabled as long as it has not
broadcast a message of class `φ` eventually broadcasts one. -/
theorem eventually_sent (hF : E.Fair) {p : P} (hp : E.Correct p) {φ : M → Prop} {m : M}
    (hm : φ m) {i : ℕ}
    (hg : ∀ j, i ≤ j → (∀ m', φ m' → (p, m') ∉ (E.σ j).sent) →
      A.send p (x p) ((E.σ j).inbox p) ((E.σ j).out p) m) :
    ∃ j m', φ m' ∧ (p, m') ∈ (E.σ j).sent := by
  by_contra hne
  push Not at hne
  obtain ⟨j, hj⟩ := hF.send p m i hp fun j hij => hg j hij fun m' hm' => hne j m' hm'
  exact hne j m hm hj

/-- A correct party whose decision guard holds as long as it has not decided eventually
decides. -/
theorem eventually_dec (hF : E.Fair) {p : P} (hp : E.Correct p) {o : O} {i : ℕ}
    (hg : ∀ j, i ≤ j → (E.σ j).dec p = none →
      A.decide p (x p) ((E.σ j).inbox p) ((E.σ j).out p) o) :
    ∃ j, (E.σ j).dec p ≠ none := by
  by_contra hne
  push Not at hne
  obtain ⟨j, hj⟩ := hF.decide p o i hp fun j hij => hg j hij (hne j)
  exact hj (hne j)

end Exec

/-- A monotone family of eventual facts over a finite index type holds simultaneously. -/
theorem exists_forall_of_mono {ι : Type*} [Finite ι] (φ : ι → ℕ → Prop)
    (hmono : ∀ a i j, i ≤ j → φ a i → φ a j) (h : ∀ a, ∃ i, φ a i) : ∃ j, ∀ a, φ a j := by
  classical
  have := Fintype.ofFinite ι
  choose f hf using h
  exact ⟨Finset.univ.sup f, fun a => hmono a _ _ (Finset.le_sup (Finset.mem_univ a)) (hf a)⟩

namespace Exec

variable (E : Exec A x k t)

/-- If every party of `S` (all correct) eventually broadcasts `m s`, a correct `q` eventually
has received `m s` from every `s ∈ S`. -/
theorem eventually_rcv_all [Finite P] (hF : E.Fair) {S : Set P} (hS : ∀ s ∈ S, E.Correct s)
    {m : P → M} (hsent : ∀ s ∈ S, ∃ i, (s, m s) ∈ (E.σ i).sent) {q : P} (hq : E.Correct q) :
    ∃ j, ∀ s ∈ S, (q, s, m s) ∈ (E.σ j).rcv := by
  have h : ∀ s : S, ∃ j, (q, (s : P), m s) ∈ (E.σ j).rcv := by
    rintro ⟨s, hs⟩
    obtain ⟨i, hi⟩ := hsent s hs
    exact hF.deliver q s _ i hq (hS s hs) hi
  obtain ⟨j, hj⟩ := exists_forall_of_mono (fun (s : S) j => (q, (s : P), m s) ∈ (E.σ j).rcv)
    (fun _ _ _ hij h => E.rcv_mono hij h) h
  exact ⟨j, fun s hs => hj ⟨s, hs⟩⟩

/-- Variant of `eventually_rcv_all` where every `s ∈ S` broadcasts *some* message of class
`φ`. -/
theorem eventually_rcv_all' [Finite P] (hF : E.Fair) {S : Set P} (hS : ∀ s ∈ S, E.Correct s)
    {φ : M → Prop} (hsent : ∀ s ∈ S, ∃ i m, φ m ∧ (s, m) ∈ (E.σ i).sent) {q : P}
    (hq : E.Correct q) : ∃ j, ∀ s ∈ S, ∃ m, φ m ∧ (q, s, m) ∈ (E.σ j).rcv := by
  have h : ∀ s : S, ∃ j, ∃ m, φ m ∧ (q, (s : P), m) ∈ (E.σ j).rcv := by
    rintro ⟨s, hs⟩
    obtain ⟨i, m, hm, hi⟩ := hsent s hs
    obtain ⟨j, hj⟩ := hF.deliver q s _ i hq (hS s hs) hi
    exact ⟨j, m, hm, hj⟩
  obtain ⟨j, hj⟩ := exists_forall_of_mono
    (fun (s : S) j => ∃ m, φ m ∧ (q, (s : P), m) ∈ (E.σ j).rcv)
    (fun _ _ _ hij ⟨m, hm, h⟩ => ⟨m, hm, E.rcv_mono hij h⟩) h
  exact ⟨j, fun s hs => hj ⟨s, hs⟩⟩

end Exec

/-! ### Fair executions exist -/

section RoundRobin

variable [Encodable P] [Encodable M] [Encodable O]

/-- The events scheduled by the round robin: broadcasts, deliveries and decisions. -/
private abbrev Ev (P M O : Type*) := (P × M) ⊕ (P × P × M) ⊕ (P × O)

open Classical in
/-- Apply an event if it is enabled (no corruptions). -/
private noncomputable def apply (A : Protocol P M I O) (x : P → I) :
    Option (Ev P M O) → State P M O → State P M O
  | some (.inl (p, m)), σ =>
    if p ∉ σ.bad ∧ A.send p (x p) (σ.inbox p) (σ.out p) m
    then { σ with sent := insert (p, m) σ.sent } else σ
  | some (.inr (.inl (q, s, m))), σ =>
    if (s, m) ∈ σ.sent then { σ with rcv := insert (q, s, m) σ.rcv } else σ
  | some (.inr (.inr (p, o))), σ =>
    if p ∉ σ.bad ∧ σ.dec p = none ∧ A.decide p (x p) (σ.inbox p) (σ.out p) o
    then { σ with dec := Function.update σ.dec p (some o) } else σ
  | none, σ => σ

/-- The schedule: every event occurs at arbitrarily late positions. -/
private def sched (i : ℕ) : Option (Ev P M O) := Encodable.decode (Nat.unpair i).1

omit [DecidableEq P] in
private theorem sched_hits (e : Ev P M O) (i : ℕ) : ∃ j, i ≤ j ∧ sched j = some e :=
  ⟨Nat.pair (Encodable.encode e) i, Nat.right_le_pair _ _, by simp [sched, Nat.unpair_pair]⟩

private noncomputable def rrσ (A : Protocol P M I O) (x : P → I) : ℕ → State P M O
  | 0 => State.init
  | i + 1 => apply A x (sched i) (rrσ A x i)

private theorem rr_step (A : Protocol P M I O) (x : P → I) (k : FaultKind) (t : ℕ) (i : ℕ) :
    Step A x k t (rrσ A x i) (rrσ A x (i + 1)) ∨ rrσ A x (i + 1) = rrσ A x i := by
  simp only [rrσ]
  rcases sched (P := P) (M := M) (O := O) i with _ | ((⟨p, m⟩) | (⟨q, s, m⟩) | (⟨p, o⟩))
  · exact Or.inr rfl
  · simp only [apply]
    split_ifs with h
    · exact Or.inl (Step.send _ _ _ h.1 h.2)
    · exact Or.inr rfl
  · simp only [apply]
    split_ifs with h
    · exact Or.inl (Step.deliver _ _ _ _ h)
    · exact Or.inr rfl
  · simp only [apply]
    split_ifs with h
    · exact Or.inl (Step.decide _ _ _ h.1 h.2.1 h.2.2)
    · exact Or.inr rfl

private theorem rr_bad (A : Protocol P M I O) (x : P → I) (i : ℕ) : (rrσ A x i).bad = ∅ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [rrσ]
    rcases sched (P := P) (M := M) (O := O) i with _ | ((⟨p, m⟩) | (⟨q, s, m⟩) | (⟨p, o⟩)) <;>
      simp only [apply] <;> (try split_ifs) <;> exact ih

/-- Fair executions without corruptions exist (round robin over all broadcast, delivery and
decision events), for encodable parties, messages and outputs. -/
theorem exists_fair_enc (A : Protocol P M I O) (x : P → I) (k : FaultKind) (t : ℕ) :
    ∃ E : Exec A x k t, E.Fair ∧ ∀ i, (E.σ i).bad = ∅ := by
  classical
  let E : Exec A x k t := ⟨rrσ A x, rfl, rr_step A x k t⟩
  refine ⟨E, ⟨?_, ?_, ?_⟩, rr_bad A x⟩
  · intro q s m i _ _ hm
    obtain ⟨j, hij, hj⟩ := sched_hits (P := P) (M := M) (O := O) (.inr (.inl (q, s, m))) i
    refine ⟨j + 1, ?_⟩
    have hm' : (s, m) ∈ (rrσ A x j).sent := E.sent_mono hij hm
    show (q, s, m) ∈ (rrσ A x (j + 1)).rcv
    simp only [rrσ, hj, apply, ite_eq_left_of_eq_true _ _ (eq_true hm')]
    exact Set.mem_insert _ _
  · intro p m i _ hg
    obtain ⟨j, hij, hj⟩ := sched_hits (P := P) (M := M) (O := O) (.inl (p, m)) i
    refine ⟨j + 1, ?_⟩
    have hb : p ∉ (rrσ A x j).bad := by rw [rr_bad]; exact Set.notMem_empty p
    show (p, m) ∈ (rrσ A x (j + 1)).sent
    simp only [rrσ, hj, apply]
    split_ifs with hc
    · exact Set.mem_insert _ _
    · exact absurd ⟨hb, hg j hij⟩ hc
  · intro p o i _ hg
    obtain ⟨j, hij, hj⟩ := sched_hits (P := P) (M := M) (O := O) (.inr (.inr (p, o))) i
    by_cases hd : (rrσ A x j).dec p = none
    · refine ⟨j + 1, ?_⟩
      have hb : p ∉ (rrσ A x j).bad := by rw [rr_bad]; exact Set.notMem_empty p
      show (rrσ A x (j + 1)).dec p ≠ none
      simp only [rrσ, hj, apply]
      split_ifs with hc
      · simp
      · exact absurd ⟨hb, hd, hg j hij⟩ hc
    · exact ⟨j, hd⟩

end RoundRobin

/-- Fair executions without corruptions exist (for countable parties, messages and outputs), so
liveness statements about fair executions are not vacuous. -/
theorem exists_fair [Countable P] [Countable M] [Countable O] (A : Protocol P M I O)
    (x : P → I) (k : FaultKind) (t : ℕ) : ∃ E : Exec A x k t, E.Fair ∧ ∀ i, (E.σ i).bad = ∅ := by
  have := Encodable.ofCountable P
  have := Encodable.ofCountable M
  have := Encodable.ofCountable O
  exact exists_fair_enc A x k t

/-- In an execution without corruptions every party is correct. -/
theorem Exec.correct_of_bad_empty (E : Exec A x k t) (h : ∀ i, (E.σ i).bad = ∅) (p : P) :
    E.Correct p := fun i => by rw [h i]; exact Set.notMem_empty p

end Cslib.Byzantine.AsyncBroadcast
