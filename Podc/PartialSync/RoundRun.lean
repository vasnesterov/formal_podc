import Cslib.Computability.Distributed.Byzantine.PartialSync.RoundAuth
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

-- CSLib candidate: Cslib/Computability/Distributed/Byzantine/PartialSync/Rounds.lean

/-!
# Synchronous round executions and message counts

Complements CSLib's round layer (`RoundAlgorithm`, `RoundRun`):

* `RoundRun.sync RA F inp adv`: the synchronous execution (no message between correct processes
  is lost, `sync_syncFrom`) in which the correct processes follow `RA` and the faulty processes
  of `F` send `adv r s p q` to `p` in round `r`, where `s` are the current states of all processes
  (a full-information adversary). Every adversary yields an execution, so the hypotheses
  "`E : RoundRun RA F inp` with `E.SyncFrom 0`" of round-based correctness theorems are
  satisfiable. `RoundRun.honestAdv RA` lets the faulty processes follow the algorithm too.
* `RoundRun.msgsUpTo E N`: the number of messages that correct processes send to *other*
  processes in rounds `< N`; `RoundRun.procMsgs E N p`: the same for one process
  (`msgsUpTo_eq_sum_procMsgs`).
-/

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P Msg S VI VO K : Type*}

namespace RoundRun

section Sync

variable [DecidableEq P] (RA : RoundAlgorithm P Msg S VI VO) (F : Finset P) (inp : P → VI)
  (adv : ℕ → (P → S) → P → P → Option Msg)

/-- The states of the synchronous execution `sync RA F inp adv`. -/
def syncStates : ℕ → P → S
  | 0 => fun p => RA.init p (inp p)
  | r + 1 => fun p => RA.trans r p (syncStates r p) fun q =>
      if q ∈ F then adv r (syncStates r) p q else RA.send r q (syncStates r q) p

/-- The synchronous execution of `RA` in which the faulty processes of `F` send
`adv r s p q` to `p` in round `r` (`s`: the current states of all processes). -/
def sync : RoundRun RA F inp where
  s := syncStates RA F inp adv
  rcv r p q := if q ∈ F then adv r (syncStates RA F inp adv r) p q
    else RA.send r q (syncStates RA F inp adv r q) p
  s_zero _ := rfl
  s_succ _ _ := rfl
  honest r p q m hq h := by simpa [hq] using h

/-- The adversary under which faulty processes follow the algorithm. -/
def honestAdv : ℕ → (P → S) → P → P → Option Msg := fun r s p q => RA.send r q (s q) p

/-- Under `honestAdv`, every process receives what the algorithm sends it. -/
theorem sync_honestAdv_rcv (r : ℕ) (p q : P) :
    (sync RA F inp (honestAdv RA)).rcv r p q =
      RA.send r q ((sync RA F inp (honestAdv RA)).s r q) p := by
  simp [sync, honestAdv]

theorem sync_syncFrom : (sync RA F inp adv).SyncFrom 0 := by
  intro r _ p q _ hq
  simp [sync, hq]

/-- Without faulty processes, the synchronous execution respects unforgeability. -/
theorem sync_empty_authValid (Au : Auth P Msg K) : (sync RA ∅ inp adv).AuthValid Au := by
  intro r p q m _ hm x hx
  simp only [sync, Finset.notMem_empty, ite_false] at hm
  exact Or.inr ⟨r, le_rfl, q, Finset.notMem_empty q, p, m, hm, hx⟩

end Sync

/-! ### Message counts -/

section Msgs

variable [Fintype P] [DecidableEq P] {RA : RoundAlgorithm P Msg S VI VO} {F : Finset P}
  {inp : P → VI} (E : RoundRun RA F inp)

/-- The number of messages sent by `p` to other processes in rounds `< N`. -/
def procMsgs (N : ℕ) (p : P) : ℕ :=
  ∑ r ∈ range N, (univ.filter fun q => q ≠ p ∧ RA.send r p (E.s r p) q ≠ none).card

/-- The number of messages sent by correct processes to other processes in rounds `< N`. -/
def msgsUpTo (N : ℕ) : ℕ :=
  ∑ r ∈ range N, ∑ p ∈ univ.filter (· ∉ F),
    (univ.filter fun q => q ≠ p ∧ RA.send r p (E.s r p) q ≠ none).card

theorem msgsUpTo_eq_sum_procMsgs (N : ℕ) :
    E.msgsUpTo N = ∑ p ∈ univ.filter (· ∉ F), E.procMsgs N p := by
  unfold msgsUpTo procMsgs; exact Finset.sum_comm

end Msgs

end RoundRun

end Cslib.Byzantine.PartialSync
