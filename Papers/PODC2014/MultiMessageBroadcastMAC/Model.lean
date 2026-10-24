import Mathlib

/-!
# BMMB composed with a standard abstract MAC layer with unreliable links

Model for Ghaffari, Kantor, Lynch, Newport, *Multi-Message Broadcast with Abstract MAC Layers and
Unreliable Links* (PODC 2014, arXiv:1405.1671), Section 2 and §3.2.1–3.2.2.

The network is a pair of graphs `G ≤ G'` on the nodes `V` (reliable and unreliable links). We model
the system "BMMB protocol + abstract MAC layer" directly, as an event-driven transition system:

* A node's BMMB state is its `log` (the messages it got, in order: this is the paper's `rcvd` set,
  and the order in which they were appended to `bcastq`) and its number `acks` of acknowledged
  broadcasts. The FIFO queue `bcastq` is `log.drop acks`; its head is the message currently being
  broadcast (BMMB broadcasts the head immediately, with no delay, whenever it is idle).
  The paper's sets are `R_i = log` and `C_i = log.take acks` (the "sent" set).
* `heard v` records the receive events at `v`: `(u, m) ∈ heard v` iff `v` received `u`'s broadcast
  of `m`. A node broadcasts each message at most once, so `(u, m)` identifies a *message instance*.
* Events (`Event`): `arrive i m` (the environment injects `m` at `i`; BMMB delivers it and appends it
  to its queue unless it already has it), `rcv u v` (`v` receives `u`'s current broadcast; only over
  `G'` edges, at most once per instance: *receive correctness*), `ack u` (only after every
  `G`-neighbour received the instance: *acknowledgment correctness*). A disabled event is a no-op.
* An execution (`Exec`) is a sequence of events `ev` with times: event `n` happens at time
  `T (n + 1)`, configuration `n` exists from time `T n` on, `T 0 = 0`, `T` is monotone and diverges
  (admissibility). The *final state at time `t`* is configuration `last t`, the last one with
  `T n ≤ t`.
* Time bounds: `AckBound F_ack` (every broadcast is acknowledged within `F_ack` of its start) and
  `ProgBound F_prog` (the progress bound of §3.2.1 for the closed fragments between the final
  states at two times; `connect` and `contend` are the paper's sets of message instances).
-/

namespace Podc.MultiMessageBroadcastMAC

open Filter

variable {V M : Type*}

/-- Events of the composed system. -/
inductive Event (V M : Type*)
  /-- The environment injects message `m` at node `i` (`arrive(m)_i`). -/
  | arrive (i : V) (m : M)
  /-- Node `v` receives the current broadcast of node `u` (`rcv(m)_v`). -/
  | rcv (u v : V)
  /-- Node `u` receives the acknowledgment of its current broadcast (`ack(m)_u`). -/
  | ack (u : V)
  /-- No event (time passage only). -/
  | skip

/-- A configuration of the composed system. -/
@[ext] structure Config (V M : Type*) where
  /-- The messages node `i` got, in order (`rcvd`, in `bcastq` order). -/
  log : V → List M
  /-- The number of acknowledged broadcasts of node `i`. -/
  acks : V → ℕ
  /-- `(u, m) ∈ heard v`: node `v` received `u`'s broadcast of `m`. -/
  heard : V → Set (V × M)

namespace Config

variable (c : Config V M)

/-- The BMMB queue `bcastq`. -/
def queue (i : V) : List M := (c.log i).drop (c.acks i)

/-- The message node `i` is currently broadcasting (the head of `bcastq`). -/
def head (i : V) : Option M := (c.log i)[c.acks i]?

/-- Node `i` is broadcasting (its queue is nonempty). -/
def Busy (i : V) : Prop := c.acks i < (c.log i).length

/-- The instance `(i, m)` has been started (`bcast(m)_i` occurred). -/
def Started (i : V) (m : M) : Prop := m ∈ (c.log i).take (c.acks i + 1)

/-- The instance `(i, m)` has been terminated (`ack(m)_i` occurred): `m ∈ C_i`. -/
def Acked (i : V) (m : M) : Prop := m ∈ (c.log i).take (c.acks i)

/-- The initial configuration. -/
def init : Config V M := ⟨fun _ => [], fun _ => 0, fun _ => ∅⟩

end Config

section Step

variable [DecidableEq V] (G G' : SimpleGraph V)

open Classical in
/-- The effect of an event; disabled events are no-ops. -/
noncomputable def step (c : Config V M) : Event V M → Config V M
  | .arrive i m =>
    if m ∈ c.log i then c else { c with log := Function.update c.log i (c.log i ++ [m]) }
  | .rcv u v =>
    match c.head u with
    | some m =>
      if G'.Adj u v ∧ (u, m) ∉ c.heard v then
        { c with
          log := if m ∈ c.log v then c.log else Function.update c.log v (c.log v ++ [m])
          heard := Function.update c.heard v (insert (u, m) (c.heard v)) }
      else c
    | none => c
  | .ack u =>
    match c.head u with
    | some m =>
      if ∀ v, G.Adj u v → (u, m) ∈ c.heard v then
        { c with acks := Function.update c.acks u (c.acks u + 1) }
      else c
    | none => c
  | .skip => c

end Step

/-- A timed execution of BMMB with an abstract MAC layer on the network `(G, G')`: the sequence of
events and their times. Event `n` happens at time `T (n + 1)`. -/
structure Exec (G G' : SimpleGraph V) (M : Type*) where
  /-- The `n`-th event. -/
  ev : ℕ → Event V M
  /-- `T n`: the time at which configuration `n` is reached. -/
  T : ℕ → ℝ
  T_zero : T 0 = 0
  T_mono : Monotone T
  /-- Admissibility: time diverges. -/
  T_tendsto : Tendsto T atTop atTop

namespace Exec

variable {G G' : SimpleGraph V} (α : Exec G G' M)

lemma exists_lt_T (t : ℝ) : ∃ n, t < α.T (n + 1) := by
  obtain ⟨n, hn⟩ := (α.T_tendsto.eventually_gt_atTop t).exists_forall_of_atTop
  exact ⟨n, hn _ (Nat.le_succ n)⟩

open Classical in
/-- The index of the final state at time `t`: the last configuration reached by time `t`. -/
noncomputable def last (t : ℝ) : ℕ := Nat.find (α.exists_lt_T t)

lemma lt_T_last_succ (t : ℝ) : t < α.T (α.last t + 1) := by
  classical exact Nat.find_spec (α.exists_lt_T t)

lemma T_last_le {t : ℝ} (ht : 0 ≤ t) : α.T (α.last t) ≤ t := by
  classical
  rcases h : α.last t with _ | n
  · rw [α.T_zero]; exact ht
  · have := Nat.find_min (α.exists_lt_T t) (m := n) (by unfold last at h; omega)
    exact not_lt.1 this

lemma le_last {t : ℝ} {n : ℕ} (h : α.T n ≤ t) : n ≤ α.last t := by
  by_contra hn
  have := α.T_mono (show α.last t + 1 ≤ n by omega)
  linarith [α.lt_T_last_succ t]

lemma le_last_iff {t : ℝ} (ht : 0 ≤ t) {n : ℕ} : n ≤ α.last t ↔ α.T n ≤ t :=
  ⟨fun h => (α.T_mono h).trans (α.T_last_le ht), α.le_last⟩

lemma last_mono {t t' : ℝ} (ht : 0 ≤ t) (h : t ≤ t') : α.last t ≤ α.last t' :=
  α.le_last ((α.T_last_le ht).trans h)

lemma last_of_neg {t : ℝ} (ht : t < 0) : α.last t = 0 := by
  classical
  refine Nat.eq_zero_of_le_zero (Nat.find_min' (α.exists_lt_T t) ?_)
  have := α.T_mono (Nat.zero_le 1)
  rw [α.T_zero] at this
  simp only [zero_add]; linarith

lemma last_monotone : Monotone α.last := by
  intro t t' h
  rcases lt_or_ge t 0 with ht | ht
  · rw [α.last_of_neg ht]; exact Nat.zero_le _
  · exact α.last_mono ht h

/-- Some time strictly after `t` has the same final state as `t` (the next event happens a
positive amount of time later). -/
lemma exists_gt_last_eq {t : ℝ} (ht : 0 ≤ t) : ∃ t', t < t' ∧ α.last t' = α.last t := by
  refine ⟨(t + α.T (α.last t + 1)) / 2, by linarith [α.lt_T_last_succ t], ?_⟩
  refine le_antisymm ?_ (α.last_mono ht (by linarith [α.lt_T_last_succ t]))
  by_contra h
  have h := not_le.1 h
  have := (α.le_last_iff (n := α.last t + 1) (by linarith [α.lt_T_last_succ t])).1 h
  linarith [α.lt_T_last_succ t]

variable [DecidableEq V]

/-- The configurations of the execution. -/
noncomputable def cfg : ℕ → Config V M
  | 0 => Config.init
  | n + 1 => step G G' (cfg n) (α.ev n)

@[simp] lemma cfg_zero : α.cfg 0 = Config.init := rfl

lemma cfg_succ (n : ℕ) : α.cfg (n + 1) = step G G' (α.cfg n) (α.ev n) := rfl

/-- The final state at time `t`. -/
noncomputable def at_ (t : ℝ) : Config V M := α.cfg (α.last t)

variable [DecidableEq M]

/-- `R_i(t)`: the messages `m'` for which `get(m')_i` occurs by time `t`. -/
noncomputable def R (i : V) (t : ℝ) : Finset M := ((α.at_ t).log i).toFinset

/-- `C_i(t)`: the messages `m'` for which `ack(m')_i` occurs by time `t`. -/
noncomputable def C (i : V) (t : ℝ) : Finset M := (((α.at_ t).log i).take ((α.at_ t).acks i)).toFinset

/-- A broadcast of `i` starts at configuration `n` (the instance pending at `n` was not pending
at `n - 1`). -/
def Fresh (i : V) (n : ℕ) : Prop :=
  (α.cfg n).Busy i ∧ ∀ n', n = n' + 1 → ¬ ((α.cfg n').Busy i ∧ (α.cfg n').acks i = (α.cfg n).acks i)

/-- **Acknowledgment bound** (and termination): every broadcast is acknowledged at most `Fack`
time after its `bcast` event. -/
def AckBound (Fack : ℝ) : Prop :=
  ∀ i n, α.Fresh i n → ∃ n', α.T n' ≤ α.T n + Fack ∧ (α.cfg n).acks i < (α.cfg n').acks i

/-- `connect(α', j)` for the fragment `α'` from configuration `a` to configuration `b`: instances
of `G`-neighbours of `j` whose `bcast` precedes the fragment and whose `ack` follows it. -/
def connect (a b : ℕ) (j : V) : Set (V × M) :=
  {p | G.Adj p.1 j ∧ (α.cfg a).Started p.1 p.2 ∧ ¬ (α.cfg b).Acked p.1 p.2}

/-- `contend(α', j)` for the fragment `α'` starting at configuration `a`: instances of
`G'`-neighbours of `j` not terminated before the fragment starts. -/
def contend (a : ℕ) (j : V) : Set (V × M) :=
  {p | G'.Adj p.1 j ∧ ¬ (α.cfg a).Acked p.1 p.2}

/-- **Progress bound**, for the closed fragments from the final state at time `t` to the final
state at time `t'`: if `t' - t > Fprog` and `connect ≠ ∅`, then some `rcv_j` event of an instance
in `contend` occurs by the end of the fragment. -/
def ProgBound (Fprog : ℝ) : Prop :=
  ∀ t t' j, 0 ≤ t → t + Fprog < t' → (α.connect (α.last t) (α.last t') j).Nonempty →
    ∃ p ∈ α.contend (α.last t) j, p ∈ (α.cfg (α.last t')).heard j

/-- All `arrive` events happen at time `0` (the setting of §3.1 and §3.2.3). -/
def ArrivalsAtZero : Prop := ∀ n i m, α.ev n = .arrive i m → α.T (n + 1) = 0

/-- `m` arrives at `i` in the execution. -/
def Arrives (i : V) (m : M) : Prop := ∃ n, α.ev n = .arrive i m

end Exec

end Podc.MultiMessageBroadcastMAC
