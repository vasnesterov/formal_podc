import Cslib.Computability.Distributed.Byzantine.LockStep.Basic
import Mathlib

/-!
# Synchronous message passing with per-round fault onset (Dolev–Lenzen, PODC 2013, Section 2)

The model of *Early-Deciding Consensus is Expensive* (Dolev, Lenzen, PODC 2013):

* `n` nodes `V` on a complete network, synchronous rounds `1, 2, …`, authenticated links
  (the receiver knows the sender), unbounded messages and local computation.
* A deterministic algorithm is a CSLib lock-step protocol (`Cslib.Byzantine.LockStep.Protocol`):
  the message `p` sends to `q` in round `k` and the decision status of `p` are functions of the
  input of `p` and of its history (the inboxes of rounds `1, …, k - 1`). Decisions are *first*
  decisions (`DecidesAt`): later changes of the status are ignored, so a decision is final.
* An execution (`Execution`) fixes the binary inputs, the set `F` of faulty nodes, for each
  faulty node the round `fr p` from which on it is faulty (the paper's sets
  `F_k = {p ∈ F | fr p ≤ k}`, `FaultyAt`), and the messages faulty nodes send (`adv`).
  Before its fault round a faulty node follows the algorithm. The number of faults is `F.card`
  (the paper's `f^E = max_k |F_k|`).
* Fault classes are predicates on executions: Byzantine (`byzAdm t`: at most `t` faulty nodes),
  crash (`crashAdm`: in its fault round a node sends a subset of its algorithm messages, then
  nothing, Definition 4.1) and orderly crash (`orderlyAdm`: the subset is a prefix of an order
  fixed by the algorithm, Definition 4.4).
* `Correct A Adm`: termination, agreement and validity in every admissible execution, for the
  nodes that are never faulty. `DecidingAt A Adm f D`: in admissible executions with exactly `f`
  faulty nodes, every never-faulty node decides within `D` rounds (Definition 3.1 with
  `d(f) = D`).
* Message counts: `msgCount A E R` counts the messages sent in rounds `1, …, R` by nodes that
  are not faulty in the round of sending (the paper's convention: nodes of `F_k` are "faulty" only
  from round `k` on).

The construction `addFaults E S k₀ γ` turns the (honest) nodes of `S` faulty from round `k₀` on,
sending `γ`; it does not change anything before round `k₀` (`hist_addFaults_of_lt`). All
executions of the lower-bound proofs are built with it.

The model is a re-indexing of CSLib's lock-step model: `hist_toScenario` shows that our histories
are those of the CSLib scenario in which `F` is the (static) Byzantine set and faulty nodes send
the messages they send here.
-/

namespace Podc.EarlyDecidingExpensive

open Finset

/-- A deterministic binary consensus algorithm on the nodes `V` with messages `M`: a CSLib
lock-step protocol with binary inputs and outputs. -/
abbrev Algorithm (V M : Type*) := Cslib.Byzantine.LockStep.Protocol V Bool M Bool

/-- Local histories: the inboxes of the rounds so far, oldest first. -/
abbrev History (V M : Type*) := Cslib.Byzantine.LockStep.History V M

-- CSLib candidate (synchronous executions with per-round fault onset, `addFaults`, counts)
/-- An execution: inputs, faulty nodes `F`, the round `fr p` from which on `p ∈ F` is faulty,
and the messages `adv k p q` that a faulty `p` sends to `q` in round `k`. -/
structure Execution (V M : Type*) where
  /-- The binary inputs. -/
  input : V → Bool
  /-- The nodes that are faulty at some point. -/
  F : Finset V
  /-- The round from which on a node of `F` is faulty (irrelevant outside `F`). -/
  fr : V → ℕ
  /-- The message a faulty `p` sends to `q` in round `k`. -/
  adv : ℕ → V → V → Option M

variable {V M : Type*}

namespace Execution

/-- `p ∈ F_k`: node `p` is faulty in round `k`. -/
def FaultyAt (E : Execution V M) (k : ℕ) (p : V) : Prop := p ∈ E.F ∧ E.fr p ≤ k

instance [DecidableEq V] (E : Execution V M) (k : ℕ) (p : V) : Decidable (E.FaultyAt k p) := by
  unfold FaultyAt; infer_instance

lemma FaultyAt.mono {E : Execution V M} {k k' : ℕ} {p : V} (h : E.FaultyAt k p) (hk : k ≤ k') :
    E.FaultyAt k' p := ⟨h.1, h.2.trans hk⟩

lemma not_faultyAt_of_not_mem {E : Execution V M} {k : ℕ} {p : V} (h : p ∉ E.F) :
    ¬ E.FaultyAt k p := fun h' => h h'.1

end Execution

variable [DecidableEq V] (A : Algorithm V M)

/-- The message `p` sends to `q` in round `k`, given the histories `h` after round `k - 1`. -/
def step (E : Execution V M) (k : ℕ) (h : V → History V M) (p q : V) : Option M :=
  if p = q then none else if E.FaultyAt k p then E.adv k p q else A.send p (E.input p) (h p) q

/-- `hist A E k q`: the history of `q` after `k` rounds (the inboxes of rounds `1, …, k`). -/
def hist (E : Execution V M) : ℕ → V → History V M
  | 0, _ => []
  | k + 1, q => hist E k q ++ [fun p => step A E (k + 1) (hist E k) p q]

/-- The message `p` sends to `q` in round `k ≥ 1` of `E`. -/
def msg (E : Execution V M) (k : ℕ) (p q : V) : Option M := step A E k (hist A E (k - 1)) p q

/-- The message the algorithm would make `p` send to `q` in round `k` of `E`. -/
def hmsg (E : Execution V M) (k : ℕ) (p q : V) : Option M :=
  if p = q then none else A.send p (E.input p) (hist A E (k - 1) p) q

/-- The decision status of `q` after `k` rounds. -/
def status (E : Execution V M) (k : ℕ) (q : V) : Option Bool :=
  A.decide q (E.input q) (hist A E k q)

/-- `q` decides `b` after exactly `k` rounds (its first decision). -/
def DecidesAt (E : Execution V M) (q : V) (k : ℕ) (b : Bool) : Prop :=
  status A E k q = some b ∧ ∀ j < k, status A E j q = none

/-- `q` decides `b` within the first `K` rounds. -/
def DecidedBy (E : Execution V M) (q : V) (K : ℕ) (b : Bool) : Prop :=
  ∃ k ≤ K, DecidesAt A E q k b

/-- `q` decides `b` (eventually). -/
def Decides (E : Execution V M) (q : V) (b : Bool) : Prop :=
  ∃ k, DecidesAt A E q k b

/-! ### Specifications -/

/-- Binary consensus (Section 2) in every execution of the class `Adm`: termination, agreement
and validity for the nodes that are never faulty. -/
structure Correct (Adm : Execution V M → Prop) : Prop where
  termination : ∀ E, Adm E → ∀ p ∉ E.F, ∃ b, Decides A E p b
  agreement : ∀ E, Adm E → ∀ p ∉ E.F, ∀ q ∉ E.F, ∀ b c,
    Decides A E p b → Decides A E q c → b = c
  validity : ∀ E, Adm E → ∀ p ∉ E.F, ∀ b, Decides A E p b → ∃ v, E.input v = b

/-- In every execution of `Adm` with exactly `f` faulty nodes, every never-faulty node has decided
within `D` rounds. -/
def DecidingAt (Adm : Execution V M → Prop) (f D : ℕ) : Prop :=
  ∀ E, Adm E → E.F.card = f → ∀ q ∉ E.F, ∃ b, DecidedBy A E q D b

/-- Definition 3.1: `A` is `d`-deciding on `Adm`. (The paper also constrains nodes that become
faulty after round `d(f)`; as a hypothesis this weaker version makes the lower bounds stronger.) -/
def Deciding (Adm : Execution V M → Prop) (d : ℕ → ℕ) : Prop :=
  ∀ f, DecidingAt A Adm f (d f)

/-- Byzantine executions: at most `t` faulty nodes, arbitrary faulty behaviour. -/
def byzAdm (t : ℕ) (E : Execution V M) : Prop := E.F.card ≤ t

/-- Definition 4.1 (crash faults): in its fault round a faulty node sends, to each node, either
its algorithm message or nothing; afterwards it sends nothing. -/
def CrashBehaved (E : Execution V M) : Prop :=
  ∀ p ∈ E.F, ∀ k q, (E.fr p < k → msg A E k p q = none) ∧
    (k = E.fr p → msg A E k p q = none ∨ msg A E k p q = hmsg A E k p q)

/-- Crash executions with at most `t` faults. -/
def crashAdm (t : ℕ) (E : Execution V M) : Prop := E.F.card ≤ t ∧ CrashBehaved A E

/-- Definition 4.4 (orderly crashes): `rank p k q` is the position of `q` in the order in which
`p` sends its messages in round `k`; a crashing node delivers exactly its messages to a prefix of
this order. -/
def OrderlyBehaved (rank : V → ℕ → V → ℕ) (E : Execution V M) : Prop :=
  ∀ p ∈ E.F, (∀ k q, E.fr p < k → msg A E k p q = none) ∧
    ∃ m, ∀ q, msg A E (E.fr p) p q = if rank p (E.fr p) q < m then hmsg A E (E.fr p) p q else none

/-- Orderly-crash executions with at most `t` faults. -/
def orderlyAdm (rank : V → ℕ → V → ℕ) (t : ℕ) (E : Execution V M) : Prop :=
  E.F.card ≤ t ∧ OrderlyBehaved A rank E

/-! ### Message counts -/

section Count

variable [Fintype V]

/-- The nodes to which `p` sends a message in round `k`. -/
def sentTo (E : Execution V M) (k : ℕ) (p : V) : Finset V :=
  univ.filter fun q => (msg A E k p q).isSome

/-- The number of messages sent in round `k` by the nodes of `X`. -/
def roundCount (E : Execution V M) (k : ℕ) (X : Finset V) : ℕ :=
  ∑ p ∈ X, (sentTo A E k p).card

/-- The nodes that are not faulty in round `k`. -/
def nonfaulty (E : Execution V M) (k : ℕ) : Finset V :=
  univ.filter fun p => ¬ E.FaultyAt k p

/-- The number of messages sent by non-faulty nodes in rounds `1, …, R`. -/
def msgCount (E : Execution V M) (R : ℕ) : ℕ :=
  ∑ k ∈ Icc 1 R, roundCount A E k (nonfaulty E k)

/-- The number of messages sent by all nodes in rounds `1, …, R`. -/
def totalCount (E : Execution V M) (R : ℕ) : ℕ :=
  ∑ k ∈ Icc 1 R, roundCount A E k univ

end Count

/-! ### Basic API -/

variable {A}

@[simp] lemma hist_zero (E : Execution V M) (q : V) : hist A E 0 q = [] := rfl

lemma hist_succ (E : Execution V M) (k : ℕ) (q : V) :
    hist A E (k + 1) q = hist A E k q ++ [fun p => msg A E (k + 1) p q] := rfl

@[simp] lemma length_hist (E : Execution V M) (k : ℕ) (q : V) : (hist A E k q).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [hist_succ, ih]

lemma msg_self (E : Execution V M) (k : ℕ) (p : V) : msg A E k p p = none := by
  simp [msg, step]

lemma msg_of_faultyAt {E : Execution V M} {k : ℕ} {p q : V} (h : E.FaultyAt k p) (hpq : p ≠ q) :
    msg A E k p q = E.adv k p q := by
  simp [msg, step, h, hpq]

lemma msg_of_not_faultyAt {E : Execution V M} {k : ℕ} {p : V} (h : ¬ E.FaultyAt k p) (q : V) :
    msg A E k p q = hmsg A E k p q := by
  by_cases hpq : p = q
  · subst hpq; simp [msg, step, hmsg]
  · simp [msg, step, hmsg, h, hpq]

/-- Histories are prefixes of each other. -/
lemma hist_take (E : Execution V M) {j k : ℕ} (hjk : j ≤ k) (q : V) :
    (hist A E k q).take j = hist A E j q := by
  induction k with
  | zero => obtain rfl : j = 0 := by omega
            rfl
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · rw [hist_succ, List.take_append_of_le_length (by simp; omega), ih (by omega)]
    · obtain rfl : j = k + 1 := by omega
      simp

/-- Two histories after `K` rounds agree iff the messages received in rounds `1, …, K` agree. -/
lemma hist_eq_iff {E E' : Execution V M} {K : ℕ} {q : V} :
    hist A E K q = hist A E' K q ↔ ∀ k, 1 ≤ k → k ≤ K → ∀ p, msg A E k p q = msg A E' k p q := by
  induction K with
  | zero => simp only [hist_zero, true_iff]; intro k h1 h2; omega
  | succ K ih =>
    rw [hist_succ, hist_succ]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
      intro k hk1 hk2 p
      rcases Nat.lt_or_ge k (K + 1) with hk | hk
      · exact ih.1 h1 k hk1 (by omega) p
      · obtain rfl : k = K + 1 := by omega
        have := congrFun (List.singleton_inj.1 h2) p
        exact this
    · intro h
      rw [ih.2 fun k hk1 hk2 p => h k hk1 (by omega) p]
      congr 2
      funext p
      exact h (K + 1) (by omega) le_rfl p

lemma hist_eq_of_le {E E' : Execution V M} {j K : ℕ} {q : V} (hjK : j ≤ K)
    (h : hist A E K q = hist A E' K q) : hist A E j q = hist A E' j q := by
  rw [← hist_take E hjK, ← hist_take E' hjK, h]

/-- The algorithm messages of a node only depend on its input and history. -/
lemma hmsg_congr {E E' : Execution V M} {k : ℕ} {p : V} (hx : E.input p = E'.input p)
    (hh : hist A E (k - 1) p = hist A E' (k - 1) p) (q : V) :
    hmsg A E k p q = hmsg A E' k p q := by
  simp [hmsg, hx, hh]

/-- A node that is non-faulty in round `k` of two executions, with the same input and history,
sends the same messages in round `k`. -/
lemma msg_congr {E E' : Execution V M} {k : ℕ} {p : V} (hf : ¬ E.FaultyAt k p)
    (hf' : ¬ E'.FaultyAt k p) (hx : E.input p = E'.input p)
    (hh : hist A E (k - 1) p = hist A E' (k - 1) p) (q : V) :
    msg A E k p q = msg A E' k p q := by
  rw [msg_of_not_faultyAt hf, msg_of_not_faultyAt hf', hmsg_congr hx hh]

/-! ### Decisions -/

lemma DecidesAt.unique {E : Execution V M} {q : V} {k k' : ℕ} {b b' : Bool}
    (h : DecidesAt A E q k b) (h' : DecidesAt A E q k' b') : k = k' ∧ b = b' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  rcases lt_trichotomy k k' with hk | rfl | hk
  · simp [h2' k hk] at h1
  · exact ⟨rfl, Option.some_injective _ (h1.symm.trans h1')⟩
  · simp [h2 k' hk] at h1'

lemma Decides.unique {E : Execution V M} {q : V} {b b' : Bool} (h : Decides A E q b)
    (h' : Decides A E q b') : b = b' := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := h'
  exact (hk.unique hk').2

lemma DecidedBy.decides {E : Execution V M} {q : V} {K : ℕ} {b : Bool}
    (h : DecidedBy A E q K b) : Decides A E q b := by
  obtain ⟨k, -, hk⟩ := h; exact ⟨k, hk⟩

lemma DecidedBy.mono {E : Execution V M} {q : V} {K K' : ℕ} {b : Bool}
    (h : DecidedBy A E q K b) (hK : K ≤ K') : DecidedBy A E q K' b := by
  obtain ⟨k, hk, h⟩ := h; exact ⟨k, hk.trans hK, h⟩

/-- Indistinguishability: a node with the same input and history after `K` rounds in two
executions makes the same decisions within `K` rounds. -/
lemma DecidedBy.transfer {E E' : Execution V M} {q : V} {K : ℕ} {b : Bool}
    (h : DecidedBy A E q K b) (hx : E.input q = E'.input q)
    (hh : hist A E K q = hist A E' K q) : DecidedBy A E' q K b := by
  obtain ⟨k, hk, h1, h2⟩ := h
  have hst : ∀ j ≤ K, status A E j q = status A E' j q := by
    intro j hj
    simp only [status, hx, hist_eq_of_le hj hh]
  refine ⟨k, hk, ?_, fun j hj => ?_⟩
  · rw [← hst k hk]; exact h1
  · rw [← hst j (by omega)]; exact h2 j hj

/-- In a correct algorithm, a never-faulty node decides, so "not deciding `b`" means deciding
`!b`. -/
lemma Correct.decides_not {Adm : Execution V M → Prop} (hA : Correct A Adm) {E : Execution V M}
    (hE : Adm E) {q : V} (hq : q ∉ E.F) {b : Bool} (h : ¬ Decides A E q b) :
    Decides A E q (!b) := by
  obtain ⟨c, hc⟩ := hA.termination E hE q hq
  cases b <;> cases c <;> simp_all

/-- Agreement in the form used below: if one never-faulty node decides `b`, every never-faulty
node decides `b`. -/
lemma Correct.decides_of_decides {Adm : Execution V M → Prop} (hA : Correct A Adm)
    {E : Execution V M} (hE : Adm E) {p q : V} (hp : p ∉ E.F) (hq : q ∉ E.F) {b : Bool}
    (h : Decides A E p b) : Decides A E q b := by
  obtain ⟨c, hc⟩ := hA.termination E hE q hq
  rwa [hA.agreement E hE p hp q hq b c h hc]

/-! ### Adding faults -/

/-- Make the nodes of `S` faulty from round `k₀` on, sending `γ k p q` in rounds `k ≥ k₀`. -/
def addFaults (E : Execution V M) (S : Finset V) (k₀ : ℕ) (γ : ℕ → V → V → Option M) :
    Execution V M where
  input := E.input
  F := E.F ∪ S
  fr p := if p ∈ S then k₀ else E.fr p
  adv k p q := if p ∈ S then γ k p q else E.adv k p q

section AddFaults

variable {E : Execution V M} {S : Finset V} {k₀ : ℕ} {γ : ℕ → V → V → Option M}

@[simp] lemma addFaults_input : (addFaults E S k₀ γ).input = E.input := rfl
@[simp] lemma addFaults_F : (addFaults E S k₀ γ).F = E.F ∪ S := rfl

lemma card_addFaults (hS : Disjoint E.F S) : (addFaults E S k₀ γ).F.card = E.F.card + S.card :=
  card_union_of_disjoint hS

lemma faultyAt_addFaults_of_mem {k : ℕ} {p : V} (hp : p ∈ S) :
    (addFaults E S k₀ γ).FaultyAt k p ↔ k₀ ≤ k := by
  simp [Execution.FaultyAt, addFaults, hp]

lemma faultyAt_addFaults_of_not_mem {k : ℕ} {p : V} (hp : p ∉ S) :
    (addFaults E S k₀ γ).FaultyAt k p ↔ E.FaultyAt k p := by
  simp [Execution.FaultyAt, addFaults, hp]

/-- Adding faults from round `k₀` on changes nothing before round `k₀`. -/
lemma hist_addFaults_of_lt (hS : Disjoint E.F S) {k : ℕ} (hk : k < k₀) (q : V) :
    hist A (addFaults E S k₀ γ) k q = hist A E k q := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
    rw [hist_succ, hist_succ, ih (by omega)]
    congr 2
    funext p
    by_cases hp : p ∈ S
    · have hpE : p ∉ E.F := fun h => Finset.disjoint_left.1 hS h hp
      apply msg_congr
      · rw [faultyAt_addFaults_of_mem hp]; omega
      · exact Execution.not_faultyAt_of_not_mem hpE
      · rfl
      · exact ih (by omega) p
    · by_cases hf : E.FaultyAt (k + 1) p
      · by_cases hpq : p = q
        · subst hpq; simp [msg_self]
        rw [msg_of_faultyAt ((faultyAt_addFaults_of_not_mem hp).2 hf) hpq, msg_of_faultyAt hf hpq]
        simp [addFaults, hp]
      · apply msg_congr ((faultyAt_addFaults_of_not_mem hp).not.2 hf) hf rfl (ih (by omega) p)

lemma hist_addFaults_of_le (hS : Disjoint E.F S) {k : ℕ} (hk : k ≤ k₀ - 1) (q : V) :
    hist A (addFaults E S k₀ γ) k q = hist A E k q := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rfl
  · exact hist_addFaults_of_lt hS (by omega) q

lemma msg_addFaults_of_not_mem (hS : Disjoint E.F S) {k : ℕ} (hk : k ≤ k₀) {p : V} (hp : p ∉ S)
    (q : V) : msg A (addFaults E S k₀ γ) k p q = msg A E k p q := by
  by_cases hpq : p = q
  · subst hpq; simp [msg_self]
  by_cases hf : E.FaultyAt k p
  · rw [msg_of_faultyAt ((faultyAt_addFaults_of_not_mem hp).2 hf) hpq, msg_of_faultyAt hf hpq]
    simp [addFaults, hp]
  · exact msg_congr ((faultyAt_addFaults_of_not_mem hp).not.2 hf) hf rfl
      (hist_addFaults_of_le hS (by omega) p) q

lemma msg_addFaults_of_mem {k : ℕ} (hk : k₀ ≤ k) {p q : V} (hp : p ∈ S) (hpq : p ≠ q) :
    msg A (addFaults E S k₀ γ) k p q = γ k p q := by
  rw [msg_of_faultyAt ((faultyAt_addFaults_of_mem hp).2 hk) hpq]
  simp [addFaults, hp]

lemma msg_addFaults_of_lt (hS : Disjoint E.F S) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < k₀) (p q : V) :
    msg A (addFaults E S k₀ γ) k p q = msg A E k p q :=
  (hist_eq_iff (A := A)).1 (hist_addFaults_of_lt (A := A) (γ := γ) hS hk q) k hk1 le_rfl p

end AddFaults

/-! ### Bridge to CSLib's lock-step model -/

/-- The CSLib lock-step scenario of an execution: the faulty nodes are the (static) Byzantine
set and send what they send in `E` (round `r` there is round `r + 1` here). -/
def toScenario (A : Algorithm V M) (E : Execution V M) : Cslib.Byzantine.LockStep.Scenario V Bool M where
  byz := ↑E.F
  input := E.input
  adv r p q := msg A E (r + 1) p q

/-- Our histories are the histories of CSLib's lock-step model on the complete network. -/
theorem hist_toScenario (A : Algorithm V M) (E : Execution V M) (k : ℕ) (q : V) :
    Cslib.Byzantine.LockStep.hist ⊤ A (toScenario A E) k q = hist A E k q := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
    rw [Cslib.Byzantine.LockStep.hist_succ, hist_succ, ih]
    congr 2
    funext p
    have hih := ih p
    simp only [Cslib.Byzantine.LockStep.deliver, SimpleGraph.top_adj]
    by_cases hpq : p = q
    · subst hpq; simp [msg_self]
    · have hdrop : ¬ (toScenario A E).drop k p q := id
      simp only [hpq, ne_eq, not_false_eq_true, if_true, hdrop, if_false, hih]
      by_cases hF : p ∈ E.F
      · simp [toScenario, hF]
      · rw [if_neg (by simpa [toScenario] using hF), msg_of_not_faultyAt (fun h => hF h.1)]
        simp [hmsg, hpq, toScenario]

end Podc.EarlyDecidingExpensive
