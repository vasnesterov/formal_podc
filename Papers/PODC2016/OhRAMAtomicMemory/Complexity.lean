import Papers.PODC2016.OhRAMAtomicMemory.Statements
import Cslib.Computability.Distributed.MessagePassing.FairExec

/-!
# Message complexity of reads (Table 1, Sections 3.2, 4.2, 5.1.2, 5.2.2)

The paper counts the messages of a read operation: `|S|` `readRequest`s, `|S|²` server-to-server
`readRelay`s (`|S|² + |S|` with the relays to the reader in the revised protocol) and `|S|`
`readAck`s, i.e. `|S|² + 2|S|` (OhSam, OhMam) or `|S|² + 3|S|` (OhSam', OhMam').

In the printed code the test of line 53 (`relays[r] = |S|/2 + 1`) is not nested in the `if` of
line 51. A server whose counter for a *newer* read of `r` sits at `|S|/2 + 1` therefore answers
every *stale* `readRelay` of an older read with one more `readAck` for the older read. With
`|S| = 3`: two consecutive reads, each completed with the relays of `s₀, s₁`; the relays of `s₂`
for the first read arrive afterwards and each of the three servers answers with a stale `readAck`.
The first read then has `3 + 9 + 6 = 18 > 15 = |S|² + 2|S|` messages (`ohSam_read_msgs_gt`,
`ohMam_read_msgs_gt`), resp. `3 + 12 + 6 = 21 > 18` in the revised protocol
(`ohSam'_read_msgs_gt`, `ohMam'_read_msgs_gt`).
-/

set_option linter.unusedSectionVars false

namespace Podc.OhRAM

open Cslib.SharedMemory Cslib.AsyncMP

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V]

/-- The message `(src, dst, m)` belongs to the `k`-th read of reader `r` (its `readRequest`, a
`readRelay` for it, or a `readAck` for it). -/
def IsReadMsg (r : R) (k : ℕ) : Node W R S × Node W R S × Msg R T V → Bool
  | (.rd r', _, .readRequest k') => decide (r' = r ∧ k' = k)
  | (_, _, .readRelay _ _ r' k') => decide (r' = r ∧ k' = k)
  | (_, .rd r', .readAck _ _ k') => decide (r' = r ∧ k' = k)
  | _ => false

/-- The number of messages sent so far for the `k`-th read of `r` (`read_op = k`). -/
def readMsgs (C : Config (Node W R S) (Loc W R S T V) (Msg R T V)) (r : R) (k : ℕ) : ℕ :=
  C.sent.countP (fun x => IsReadMsg r k x)

/-! ## The counterexample run -/

section Run

/-- Three servers, one reader, one writer, binary values. -/
abbrev N := Node Unit Unit (Fin 3)

/-- The steps of the run (for any variant; `T` is the tag type, `⊥` the initial tag). -/
def staleRun (T : Type) [Bot T] (fast : Bool) : List (Step N (register Bool false) (Msg Unit T Bool) Empty) :=
  let relay (k : ℕ) (j i : Fin 3) : Step N (register Bool false) (Msg Unit T Bool) Empty :=
    .recv (.sv j) (.sv i) (.readRelay ⊥ false () k)
  let ack (k : ℕ) (j : Fin 3) : Step N (register Bool false) (Msg Unit T Bool) Empty :=
    .recv (.sv j) (.rd ()) (.readAck ⊥ false k)
  let rread (k : ℕ) : List (Step N (register Bool false) (Msg Unit T Bool) Empty) :=
    [.inv (.rd ()) .read,
      .recv (.rd ()) (.sv 0) (.readRequest k), .recv (.rd ()) (.sv 1) (.readRequest k),
      .recv (.rd ()) (.sv 2) (.readRequest k),
      relay k 0 0, relay k 1 0, relay k 0 1, relay k 1 1, relay k 0 2, relay k 1 2] ++
    (if fast then [] else [ack k 0, ack k 1])
  -- in the revised protocol the reader completes with the relays of `s₀, s₁` (same tag `⊥`)
  let frelay (k : ℕ) (j : Fin 3) : Step N (register Bool false) (Msg Unit T Bool) Empty :=
    .recv (.sv j) (.rd ()) (.readRelay ⊥ false () k)
  rread 1 ++ (if fast then [frelay 1 0, frelay 1 1] else []) ++
  rread 2 ++ (if fast then [frelay 2 0, frelay 2 1] else []) ++
  -- the stale relays of `s₂` for the first read
  [relay 1 2 0, relay 1 2 1, relay 1 2 2]

end Run

end Podc.OhRAM

namespace Podc.OhRAM
open Cslib.SharedMemory Cslib.AsyncMP

/-- The paper's per-read message bound `c` holds for `Pr`: in every reachable configuration, at
most `c` messages have been sent for any read operation. -/
def ReadMsgBound {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S]
    [DecidableEq T] [DecidableEq V] {A : ObjSpec}
    (Pr : Protocol (Node W R S) A (Loc W R S T V) (Msg R T V) Empty) (c : ℕ) : Prop :=
  ∀ C h, Pr.Reach C h → ∀ r k, readMsgs C r k ≤ c

lemma not_readMsgBound_of_run {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S]
    [DecidableEq T] [DecidableEq V] {A : ObjSpec}
    {Pr : Protocol (Node W R S) A (Loc W R S T V) (Msg R T V) Empty} {c : ℕ}
    {ss : List (Step (Node W R S) A (Msg R T V) Empty)} {r : R} {k : ℕ}
    (h : ((Pr.runFrom Pr.initCfg ss).map fun x => decide (c < readMsgs x.1 r k)) = some true) :
    ¬ ReadMsgBound Pr c := by
  intro hb
  obtain ⟨⟨C, hC⟩, hrun, hc⟩ := Option.map_eq_some_iff.1 h
  have := hb C hC (by simpa using Protocol.runFrom_reach Protocol.Reach.init hrun) r k
  simp only [decide_eq_true_eq] at hc
  omega

/-- **Table 1 / Section 3.2 is false for the printed code**: OhSam (Algorithm 1) with `|S| = 3`
servers does not satisfy the read message bound `|S|² + 2|S| = 15`: a read can have 18 messages
(stale `readAck`s, line 53). -/
theorem ohSam_read_msgs_gt :
    ¬ ReadMsgBound (ohSam Unit (Fin 3) Bool false) (Fintype.card (Fin 3) ^ 2 + 2 * Fintype.card (Fin 3)) :=
  not_readMsgBound_of_run (ss := staleRun ℕ false) (r := ()) (k := 1) (by decide +kernel)

/-- Same for OhMam (Algorithm 2, Section 4.2), with one writer. -/
theorem ohMam_read_msgs_gt :
    ¬ ReadMsgBound (ohMam Unit Unit (Fin 3) Bool false)
      (Fintype.card (Fin 3) ^ 2 + 2 * Fintype.card (Fin 3)) :=
  not_readMsgBound_of_run (ss := staleRun (Tag Unit) false) (r := ()) (k := 1) (by decide +kernel)

/-- Same for OhSam' (Algorithm 3, Section 5.1.2): 21 messages `> |S|² + 3|S| = 18`. -/
theorem ohSam'_read_msgs_gt :
    ¬ ReadMsgBound (ohSam' Unit (Fin 3) Bool false)
      (Fintype.card (Fin 3) ^ 2 + 3 * Fintype.card (Fin 3)) :=
  not_readMsgBound_of_run (ss := staleRun ℕ true) (r := ()) (k := 1) (by decide +kernel)

/-- Same for OhMam' (Section 5.2.2). -/
theorem ohMam'_read_msgs_gt :
    ¬ ReadMsgBound (ohMam' Unit Unit (Fin 3) Bool false)
      (Fintype.card (Fin 3) ^ 2 + 3 * Fintype.card (Fin 3)) :=
  not_readMsgBound_of_run (ss := staleRun (Tag Unit) true) (r := ()) (k := 1) (by decide +kernel)

/-- The bound fails however the stale `readAck`s are attributed: at the end of the run of
`ohSam_read_msgs_gt`, the two reads together have `18 + 15 = 33 > 2 · 15` messages. -/
theorem ohSam_staleRun_two_reads :
    ((ohSam Unit (Fin 3) Bool false).runFrom (ohSam Unit (Fin 3) Bool false).initCfg
      (staleRun ℕ false)).map (fun x => (readMsgs x.1 () 1, readMsgs x.1 () 2)) = some (18, 15) := by
  decide +kernel

/-- Same for OhSam': `21 + 18 = 39 > 2 · 18`. -/
theorem ohSam'_staleRun_two_reads :
    ((ohSam' Unit (Fin 3) Bool false).runFrom (ohSam' Unit (Fin 3) Bool false).initCfg
      (staleRun ℕ true)).map (fun x => (readMsgs x.1 () 1, readMsgs x.1 () 2)) = some (21, 18) := by
  decide +kernel

end Podc.OhRAM
