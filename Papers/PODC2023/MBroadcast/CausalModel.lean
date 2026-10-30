import Papers.PODC2023.MBroadcast.Spec
import Mathlib.Data.Fintype.Card

/-!
# Algorithm 2 (MBroadcast on top of causal message delivery): the model

Model `CAMP_{n,t}[t < n/2]` enriched with causal message delivery, running Algorithm 2 of
Déprés, Mostéfaoui, Perrin, Raynal, *Brief Announcement: The MBroadcast Abstraction*, PODC 2023:

```
operation mbroadcast(m):
 (1) causal_broadcast init(m);
 (2) wait (ack(m) received from at least n − t − 1 processes);
 (3) mdelivery of m from p_i
when init(m) is causally-delivered from p_j do
 (4) if i ≠ j then (5) causal_send ack(m) to p_j; (6) mdelivery of m from p_j end if
```

## Model choices

* Processes `P` (`[Fintype P]`, `n = Fintype.card P`), protocol parameter `t : ℕ` (the waiting
  threshold of line 2 is `n - t - 1`, natural subtraction), messages `M`.
* **One global, append-only event log** `Cfg.log : List (GEv P M)`, in real-time order; "before"
  is comparison of positions. It contains the events of the MBroadcast abstraction (`GEv.mb`), the
  network sends (`GEv.snd`) and the network receptions (`GEv.rcv`). The *id* of a network message
  is the log position of its `snd` event. The MBroadcast trace is the projection
  `Cfg.trace = log.filterMap mbOf`; all correctness theorems are stated about it, with the
  definitions of `Papers.PODC2023.MBroadcast.Spec`.
* A network message record (`Rec`) has a sender, a set of destinations (a causal broadcast is one
  network message with destinations `univ.erase sender`, a causal send has one destination), a
  body (`init m` or `ack m`) and a ghost field `dep`: the ids of all messages that causally precede
  this send. `dep` is the sender's causal past `Cfg.past src` at sending time; `past p` contains
  the ids of `p`'s own sends, of the messages `p` received, and their `dep`s (this is the
  transitive closure of the paper's relations (i) and (ii)).
* **Causal delivery** (`CausalReady`): a process `p` may receive message `x` only if it has
  already received every message `y ∈ dep x` of which it is a destination. This is exactly the
  paper's causal delivery guarantee ("if send(m1) causally precedes send(m2) and both have the
  same destination, m1 is delivered there before m2"), for causal broadcasts and causal sends
  alike. Channels are otherwise unordered (not FIFO).
* **Self-delivery.** The causal broadcast of line 1 does not include the sender in its
  destinations: in Algorithm 2 the handler of a self-delivered `init(m)` does nothing (test of
  line 4), so this is a no-op; it does not affect causality either, since every own send is in
  the sender's causal past anyway.
* **Atomicity.** Each step executes a block of code between two `wait`s atomically: an
  invocation (line 1: the whole causal broadcast is one step), the end of the wait of line 2
  (line 3, `Action.own`), the reception of a message together with its handler (lines 4–6 for
  `init`; for `ack(m)`, the receiver records the sender in its set of acknowledgers if it is
  currently waiting for acknowledgements of `m`).
* **Local state**: `Phase.idle` or `Phase.wait m acks` (inside `mbroadcast(m)`, waiting at
  line 2, `acks` = the processes from which `ack(m)` was received); crashed processes `crashed`.
* **All mbroadcast messages are different** (the paper's assumption, per sender): `invoke p m`
  is enabled only if `p` never invoked `mbroadcast(m)` before. A process invokes a new
  `mbroadcast` only when the previous one returned (processes are sequential).
* **Crashes and reliability.** A crash is a step (`Action.crash`); crashed processes take no
  further steps. Messages are never lost: the messages of a crashed sender stay in transit and
  may still be received (reliable channels). Since a whole broadcast is one atomic step, the
  paper's possibility "a process crashes in the middle of a broadcast and only some destinations
  ever receive the message" is covered for safety: every finite behaviour of that model is a
  finite behaviour of ours in which the remaining receptions simply have not happened yet, and
  the safety properties are properties of finite traces. For liveness (`Exec.Fair`), a message
  to a correct process whose causal predecessors (with the same destination) have been received
  is eventually received, also when its sender has crashed. The liveness proofs use this only
  for messages of correct senders and for messages in the causal past of a message sent by a
  correct process (a process that has delivered or sent them); this is what an implementation
  of causal delivery on top of reliable channels provides (by piggybacking the causal past), and
  it is needed anyway for causal delivery to be live in the presence of crashes.
* `Action.skip` (stuttering) makes infinite executions always possible.
-/

set_option linter.unusedSectionVars false

namespace Podc.MBroadcast.Causal

open Finset

/-- Bodies of the implementation messages. -/
inductive Body (M : Type) where
  | init (m : M)
  | ack (m : M)
  deriving DecidableEq

/-- A network message: sender, destinations, body, and (ghost) the ids of the messages that
causally precede it. -/
structure Rec (P M : Type) where
  src : P
  dst : Finset P
  body : Body M
  dep : Finset ℕ
  deriving DecidableEq

/-- Events of the global log. -/
inductive GEv (P M : Type) where
  /-- An event of the MBroadcast abstraction. -/
  | mb (e : Ev P M)
  /-- A network message is sent; its id is the log position of this event. -/
  | snd (r : Rec P M)
  /-- Process `p` (causally) receives the network message with id `id`. -/
  | rcv (p : P) (id : ℕ)
  deriving DecidableEq

/-- Control state of a process. -/
inductive Phase (P M : Type) where
  | idle
  /-- Inside `mbroadcast(m)`, waiting at line 2; `acks` = senders of the received `ack(m)`. -/
  | wait (m : M) (acks : Finset P)
  deriving DecidableEq

/-- Configurations. -/
structure Cfg (P M : Type) where
  /-- The global event log (append-only). -/
  log : List (GEv P M)
  /-- Control states. -/
  phase : P → Phase P M
  /-- Ghost: causal past of each process (ids of network messages). -/
  past : P → Finset ℕ
  /-- Crashed processes. -/
  crashed : Finset P

/-- Actions (scheduler choices). -/
inductive Action (P M : Type) where
  /-- `p` invokes `mbroadcast(m)`. -/
  | invoke (p : P) (m : M)
  /-- `p` receives network message `id` and runs the handler. -/
  | recv (p : P) (id : ℕ)
  /-- `p` ends the wait of line 2 and mdelivers its own message (line 3). -/
  | own (p : P)
  /-- `p` crashes. -/
  | crash (p : P)
  /-- Stuttering. -/
  | skip

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]

/-- Projection of the global log to MBroadcast events. -/
def mbOf : GEv P M → Option (Ev P M)
  | .mb e => some e
  | _ => none

/-- The MBroadcast trace of a configuration. -/
def Cfg.trace (C : Cfg P M) : List (Ev P M) := C.log.filterMap mbOf

/-- `p` is a destination of the network message with id `y`. -/
def needs (L : List (GEv P M)) (p : P) (y : ℕ) : Bool :=
  match L[y]? with
  | some (.snd r) => decide (p ∈ r.dst)
  | _ => false

/-- Causal delivery guard: `p` has received every message causally preceding `r` of which it is
a destination. -/
def CausalReady (L : List (GEv P M)) (p : P) (r : Rec P M) : Prop :=
  ∀ y ∈ r.dep, needs L p y = true → GEv.rcv p y ∈ L

instance (L : List (GEv P M)) (p : P) (r : Rec P M) : Decidable (CausalReady L p r) := by
  unfold CausalReady; infer_instance

/-- The initial configuration. -/
def initCfg : Cfg P M := ⟨[], fun _ => .idle, fun _ => ∅, ∅⟩

/-- Effect of the reception by `p` of the network message `x` (record `r`), with its handler. -/
def deliver (C : Cfg P M) (p : P) (x : ℕ) (r : Rec P M) : Cfg P M :=
  let past' := C.past p ∪ r.dep ∪ {x}
  match r.body with
  | .init m =>
    if r.src ≠ p then
      -- lines 5–6: causal_send ack(m) to the sender, then mdeliver m from the sender
      { C with
        log := C.log ++ [.rcv p x, .snd ⟨p, {r.src}, .ack m, past'⟩, .mb (.dl p r.src m)]
        past := Function.update C.past p (insert (C.log.length + 1) past') }
    else
      { C with log := C.log ++ [.rcv p x], past := Function.update C.past p past' }
  | .ack m =>
    { C with
      log := C.log ++ [.rcv p x]
      past := Function.update C.past p past'
      phase := match C.phase p with
        | .wait m' A => if m' = m then Function.update C.phase p (.wait m (insert r.src A))
            else C.phase
        | .idle => C.phase }

/-- The transition function (`none` = action not enabled). `t` is the protocol parameter. -/
def step (t : ℕ) (C : Cfg P M) : Action P M → Option (Cfg P M)
  | .invoke p m =>
    if p ∉ C.crashed ∧ C.phase p = .idle ∧ GEv.mb (.bc p m) ∉ C.log then
      some { C with
        log := C.log ++ [.mb (.bc p m), .snd ⟨p, univ.erase p, .init m, C.past p⟩]
        past := Function.update C.past p (insert (C.log.length + 1) (C.past p))
        phase := Function.update C.phase p (.wait m ∅) }
    else none
  | .recv p x =>
    match C.log[x]? with
    | some (.snd r) =>
      if p ∉ C.crashed ∧ p ∈ r.dst ∧ GEv.rcv p x ∉ C.log ∧ CausalReady C.log p r then
        some (deliver C p x r)
      else none
    | _ => none
  | .own p =>
    match C.phase p with
    | .wait m A =>
      if p ∉ C.crashed ∧ Fintype.card P - t - 1 ≤ A.card then
        some { C with
          log := C.log ++ [.mb (.dl p p m)]
          phase := Function.update C.phase p .idle }
      else none
    | .idle => none
  | .crash p => some { C with crashed := insert p C.crashed }
  | .skip => some C

/-- Reachable configurations. -/
inductive Reachable (t : ℕ) : Cfg P M → Prop
  | init : Reachable t initCfg
  | step {C C' : Cfg P M} (a : Action P M) : Reachable t C → step t C a = some C' →
      Reachable t C'

/-! ## Step inversion lemmas -/

section Inversion

variable {t : ℕ} {C C' : Cfg P M}

lemma step_invoke {p : P} {m : M} (h : step t C (.invoke p m) = some C') :
    p ∉ C.crashed ∧ C.phase p = .idle ∧ GEv.mb (.bc p m) ∉ C.log ∧
    C' = { C with
        log := C.log ++ [.mb (.bc p m), .snd ⟨p, univ.erase p, .init m, C.past p⟩]
        past := Function.update C.past p (insert (C.log.length + 1) (C.past p))
        phase := Function.update C.phase p (.wait m ∅) } := by
  simp only [step] at h
  split_ifs at h with hg
  exact ⟨hg.1, hg.2.1, hg.2.2, (Option.some.inj h).symm⟩

lemma step_recv {p : P} {x : ℕ} (h : step t C (.recv p x) = some C') :
    ∃ r, C.log[x]? = some (.snd r) ∧ p ∉ C.crashed ∧ p ∈ r.dst ∧ GEv.rcv p x ∉ C.log ∧
      CausalReady C.log p r ∧ C' = deliver C p x r := by
  simp only [step] at h
  split at h
  · rename_i r hr
    split_ifs at h with hg
    exact ⟨r, hr, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2, (Option.some.inj h).symm⟩
  · cases h

lemma step_own {p : P} (h : step t C (.own p) = some C') :
    ∃ m A, C.phase p = .wait m A ∧ p ∉ C.crashed ∧ Fintype.card P - t - 1 ≤ A.card ∧
      C' = { C with
          log := C.log ++ [.mb (.dl p p m)]
          phase := Function.update C.phase p .idle } := by
  simp only [step] at h
  split at h
  · rename_i m A hph
    split_ifs at h with hg
    exact ⟨m, A, hph, hg.1, hg.2, (Option.some.inj h).symm⟩
  · cases h

lemma step_crash {p : P} (h : step t C (.crash p) = some C') :
    C' = { C with crashed := insert p C.crashed } := by
  simp only [step, Option.some.injEq] at h; exact h.symm

lemma step_skip (h : step t C .skip = some C') : C' = C := by
  simp only [step, Option.some.injEq] at h; exact h.symm

/-- Every step appends to the log. -/
lemma step_log_prefix {a : Action P M} (h : step t C a = some C') : ∃ l, C'.log = C.log ++ l := by
  cases a with
  | invoke p m => obtain ⟨-, -, -, rfl⟩ := step_invoke h; exact ⟨_, rfl⟩
  | recv p x =>
    obtain ⟨r, -, -, -, -, -, rfl⟩ := step_recv h
    unfold deliver
    split
    · split_ifs
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  | own p => obtain ⟨m, A, -, -, -, rfl⟩ := step_own h; exact ⟨_, rfl⟩
  | crash p => rw [step_crash h]; exact ⟨[], by simp⟩
  | skip => rw [step_skip h]; exact ⟨[], by simp⟩

/-- Crashed processes stay crashed. -/
lemma step_crashed_mono {a : Action P M} (h : step t C a = some C') : C.crashed ⊆ C'.crashed := by
  cases a with
  | invoke p m => obtain ⟨-, -, -, rfl⟩ := step_invoke h; exact subset_rfl
  | recv p x =>
    obtain ⟨r, -, -, -, -, -, rfl⟩ := step_recv h
    unfold deliver
    split
    · split_ifs
      · exact subset_rfl
      · exact subset_rfl
    · exact subset_rfl
  | own p => obtain ⟨m, A, -, -, -, rfl⟩ := step_own h; exact subset_rfl
  | crash p => rw [step_crash h]; exact subset_insert _ _
  | skip => rw [step_skip h]

end Inversion

/-! ## List lemmas -/

section ListLemmas

variable {α : Type}

lemma lt_of_getElem?_eq_some {L : List α} {i : ℕ} {a : α} (h : L[i]? = some a) : i < L.length := by
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h

lemma getElem?_append_of_some {L l : List α} {i : ℕ} {a : α} (h : L[i]? = some a) :
    (L ++ l)[i]? = some a := by
  rw [List.getElem?_append_left (lt_of_getElem?_eq_some h)]; exact h

lemma getElem?_append_cases {L l : List α} {i : ℕ} {a : α} (h : (L ++ l)[i]? = some a) :
    L[i]? = some a ∨ (L.length ≤ i ∧ l[i - L.length]? = some a) := by
  by_cases hi : i < L.length
  · left; rwa [List.getElem?_append_left hi] at h
  · right; rw [List.getElem?_append_right (by omega)] at h; exact ⟨by omega, h⟩

lemma getElem?_append_one {L : List α} {b : α} {i : ℕ} {a : α} (h : (L ++ [b])[i]? = some a) :
    L[i]? = some a ∨ (i = L.length ∧ b = a) := by
  rcases getElem?_append_cases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · right
    obtain ⟨k, hk⟩ : ∃ k, i = L.length + k := ⟨i - L.length, by omega⟩
    subst hk
    rcases k with _ | k <;> simp at h2 ⊢; exact h2

lemma getElem?_append_two {L : List α} {b c : α} {i : ℕ} {a : α}
    (h : (L ++ [b, c])[i]? = some a) :
    L[i]? = some a ∨ (i = L.length ∧ b = a) ∨ (i = L.length + 1 ∧ c = a) := by
  rcases getElem?_append_cases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · right
    obtain ⟨k, hk⟩ : ∃ k, i = L.length + k := ⟨i - L.length, by omega⟩
    subst hk
    rcases k with _ | _ | k <;> simp at h2 ⊢
    · exact h2
    · exact h2

lemma getElem?_append_three {L : List α} {b c d : α} {i : ℕ} {a : α}
    (h : (L ++ [b, c, d])[i]? = some a) :
    L[i]? = some a ∨ (i = L.length ∧ b = a) ∨ (i = L.length + 1 ∧ c = a) ∨
      (i = L.length + 2 ∧ d = a) := by
  rcases getElem?_append_cases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · right
    obtain ⟨k, hk⟩ : ∃ k, i = L.length + k := ⟨i - L.length, by omega⟩
    subst hk
    rcases k with _ | _ | _ | k <;> simp at h2 ⊢
    · exact h2
    · exact h2
    · exact h2

lemma mem_iff_getElem?' {L : List α} {a : α} : a ∈ L ↔ ∃ i : ℕ, L[i]? = some a := by
  constructor
  · intro h; obtain ⟨i, hi, he⟩ := List.getElem_of_mem h; exact ⟨i, by simp [hi, he]⟩
  · rintro ⟨i, hi⟩; exact List.mem_of_getElem? hi

-- CSLib candidate
/-- A position in a `filterMap` comes from a position of the original list, with the same
prefix. -/
lemma exists_of_getElem?_filterMap {β : Type} (f : α → Option β) :
    ∀ (l : List α) (i : ℕ) (b : β), (l.filterMap f)[i]? = some b →
      ∃ j a, l[j]? = some a ∧ f a = some b ∧ (l.take j).filterMap f = (l.filterMap f).take i
  | [], i, b, h => by simp at h
  | a :: l, i, b, h => by
    cases hfa : f a with
    | none =>
      rw [List.filterMap_cons_none hfa] at h
      obtain ⟨j, a', h1, h2, h3⟩ := exists_of_getElem?_filterMap f l i b h
      refine ⟨j + 1, a', by simpa using h1, h2, ?_⟩
      rw [List.take_succ_cons, List.filterMap_cons_none hfa, List.filterMap_cons_none hfa, h3]
    | some b' =>
      rw [List.filterMap_cons_some hfa] at h
      cases i with
      | zero =>
        simp at h; subst h
        exact ⟨0, a, rfl, hfa, by simp⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨j, a', h1, h2, h3⟩ := exists_of_getElem?_filterMap f l i b h
        refine ⟨j + 1, a', by simpa using h1, h2, ?_⟩
        rw [List.take_succ_cons, List.filterMap_cons_some hfa, List.filterMap_cons_some hfa,
          List.take_succ_cons, h3]

end ListLemmas

lemma mbOf_eq_some {a : GEv P M} {e : Ev P M} : mbOf a = some e ↔ a = .mb e := by
  cases a <;> simp [mbOf]

lemma mem_filterMap_mbOf {L : List (GEv P M)} {e : Ev P M} :
    e ∈ L.filterMap mbOf ↔ GEv.mb e ∈ L := by
  simp [List.mem_filterMap, mbOf_eq_some]

lemma count_filterMap_mbOf (L : List (GEv P M)) (e : Ev P M) :
    (L.filterMap mbOf).count e = L.count (.mb e) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    cases a with
    | mb e' =>
      rw [List.filterMap_cons_some (by rfl), List.count_cons, List.count_cons, ih]
      simp
    | snd r => rw [List.filterMap_cons_none (by rfl), List.count_cons, ih]; simp
    | rcv p y => rw [List.filterMap_cons_none (by rfl), List.count_cons, ih]; simp

lemma needs_iff {L : List (GEv P M)} {p : P} {y : ℕ} :
    needs L p y = true ↔ ∃ r, L[y]? = some (.snd r) ∧ p ∈ r.dst := by
  unfold needs
  split
  · rename_i r hr; simp [hr]
  · rename_i hr
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro r h; exact absurd h (hr r)

end Podc.MBroadcast.Causal
