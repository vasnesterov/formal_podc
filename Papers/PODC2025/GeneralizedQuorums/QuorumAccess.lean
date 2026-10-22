import Papers.PODC2025.GeneralizedQuorums.Defs
import Cslib.Computability.Distributed.SharedMemory.History

/-!
# The quorum access functions of Figure 3 and their safety (Lemma 1, Theorem 3)

The protocol of Figure 3, as an algorithm in the model `Cslib.ChannelFailures`, for arbitrary
families of read quorums `RR` and write quorums `WW` (only Consistency is needed for safety).

* The opaque top-level state is represented by the set of identifiers of the update functions
  applied to it: the update of the `quorum_set` invoked by `p` with sequence number `k` is
  `(p, k)` (`k ≥ 1`; the `k`-th operation of `p`, counted from `0` in the history, has sequence
  number `k + 1`). Applying an update inserts its identifier. Hence "`s` has incorporated `u`" is
  `u ∈ s`, and the Validity property says that `s` only contains identifiers of invoked
  `quorum_set`s.
* `quorum_get` returns the list of states collected from a read quorum; `quorum_set` returns `[]`.
* Waits are re-evaluated after every step (`advance`). A process keeps, for every sender, the
  `GET_RESP` with the highest clock received so far (`latest`): the wait at line 8 (resp. 20) is
  for a read quorum all of whose latest clocks are `≥ c_get` (resp. `≥ c_set`).

The safety theorems (`realtime_ordering`, `validity`) are proved in `QuorumAccessProof.lean`.
-/

namespace Podc.GeneralizedQuorums.QA

open Cslib.ChannelFailures Cslib.SharedMemory

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Operations: `quorum_get()` and `quorum_set(u)` (the update is identified by its invocation). -/
inductive QOp where
  | get
  | set
  deriving DecidableEq

/-- The interface of the quorum access functions. -/
abbrev qaObj (P : Type) : ObjSpec where
  State := Unit
  Op := QOp
  Resp := List (Finset (P × ℕ))
  init := ()
  δ _ _ := ((), [])

/-- Messages of Figure 3. -/
inductive QMsg (P : Type) where
  | clockReq (k : ℕ)
  | clockResp (k c : ℕ)
  | getResp (s : Finset (P × ℕ)) (c : ℕ)
  | setReq (k : ℕ)
  | setResp (k c : ℕ)

/-- Phase of the current operation. -/
inductive Phase where
  /-- No operation in progress. -/
  | idle
  /-- `quorum_get`, line 6: waiting for `CLOCK_RESP`s from a write quorum. -/
  | getClk
  /-- `quorum_get`, line 8: waiting for `GET_RESP`s with clock `≥ cget` from a read quorum. -/
  | getWait (cget : ℕ)
  /-- `quorum_set`, line 18: waiting for `SET_RESP`s from a write quorum. -/
  | setAck
  /-- `quorum_set`, line 20: waiting for `GET_RESP`s with clock `≥ cset` from a read quorum. -/
  | setWait (cset : ℕ)
  deriving DecidableEq

/-- Local state of a process. -/
structure QState (P : Type) where
  /-- The opaque state (identifiers of the applied updates). -/
  st : Finset (P × ℕ)
  /-- The logical clock. -/
  clock : ℕ
  /-- The sequence number of the current/last operation. -/
  seq : ℕ
  /-- The phase of the current operation. -/
  phase : Phase
  /-- `CLOCK_RESP(seq, c)` received from each process. -/
  clockResps : P → Option ℕ
  /-- `SET_RESP(seq, c)` received from each process. -/
  setResps : P → Option ℕ
  /-- The `GET_RESP(s, c)` with the highest clock received from each process. -/
  latest : P → Option (Finset (P × ℕ) × ℕ)

variable (RR WW : Set (Set P))

open Classical in
/-- Re-evaluate the waits at lines 8 and 20 (read-quorum waits). -/
noncomputable def advanceRead (l : QState P) : QState P × Option (List (Finset (P × ℕ))) :=
  match l.phase with
  | .getWait c =>
    if h : ∃ R ∈ RR, ∀ j ∈ R, ∃ s c', l.latest j = some (s, c') ∧ c ≤ c' then
      ({ l with phase := .idle },
        some ((Finset.univ.filter (· ∈ h.choose)).toList.filterMap fun j => (l.latest j).map Prod.fst))
    else (l, none)
  | .setWait c =>
    if ∃ R ∈ RR, ∀ j ∈ R, ∃ s c', l.latest j = some (s, c') ∧ c ≤ c' then
      ({ l with phase := .idle }, some [])
    else (l, none)
  | _ => (l, none)

open Classical in
/-- Re-evaluate all waits (lines 6, 8, 18, 20). -/
noncomputable def advance (l : QState P) : QState P × Option (List (Finset (P × ℕ))) :=
  match l.phase with
  | .getClk =>
    if h : ∃ W ∈ WW, ∀ j ∈ W, (l.clockResps j).isSome then
      advanceRead RR
        { l with phase := .getWait ((Finset.univ.filter (· ∈ h.choose)).sup fun j => (l.clockResps j).getD 0) }
    else (l, none)
  | .setAck =>
    if h : ∃ W ∈ WW, ∀ j ∈ W, (l.setResps j).isSome then
      advanceRead RR
        { l with phase := .setWait ((Finset.univ.filter (· ∈ h.choose)).sup fun j => (l.setResps j).getD 0) }
    else (l, none)
  | _ => advanceRead RR l

/-- Send `m` to all processes. -/
noncomputable def bcast (m : QMsg P) : List (P × QMsg P) := Finset.univ.toList.map fun j => (j, m)

/-- Apply `advance` after a local transition. -/
noncomputable def finish (l : QState P) (out : List (P × QMsg P)) :
    QState P × List (P × QMsg P) × Option (List (Finset (P × ℕ))) :=
  ((advance RR WW l).1, out, (advance RR WW l).2)

open Classical in
/-- **Figure 3**: the protocol at a process. -/
noncomputable def qaAlg : Algorithm P (qaObj P) (QMsg P) (QState P) where
  init _ := ⟨∅, 0, 0, .idle, fun _ => none, fun _ => none, fun _ => none⟩
  handle _ i l := match i with
    | .invoke .get =>
      finish RR WW { l with seq := l.seq + 1, phase := .getClk, clockResps := fun _ => none }
        (bcast (.clockReq (l.seq + 1)))
    | .invoke .set =>
      finish RR WW { l with seq := l.seq + 1, phase := .setAck, setResps := fun _ => none }
        (bcast (.setReq (l.seq + 1)))
    | .tick _ =>
      finish RR WW { l with clock := l.clock + 1 } (bcast (.getResp l.st (l.clock + 1)))
    | .recv j (.clockReq k) => finish RR WW l [(j, .clockResp k l.clock)]
    | .recv j (.clockResp k c) =>
      if k = l.seq ∧ l.phase = .getClk then
        finish RR WW { l with clockResps := Function.update l.clockResps j (some c) } []
      else finish RR WW l []
    | .recv j (.getResp s c) =>
      if ∀ s' c', l.latest j = some (s', c') → c' ≤ c then
        finish RR WW { l with latest := Function.update l.latest j (some (s, c)) } []
      else finish RR WW l []
    | .recv j (.setReq k) =>
      finish RR WW { l with st := insert (j, k) l.st, clock := l.clock + 1 }
        [(j, .setResp k (l.clock + 1))]
    | .recv j (.setResp k c) =>
      if k = l.seq ∧ l.phase = .setAck then
        finish RR WW { l with setResps := Function.update l.setResps j (some c) } []
      else finish RR WW l []

end Podc.GeneralizedQuorums.QA
