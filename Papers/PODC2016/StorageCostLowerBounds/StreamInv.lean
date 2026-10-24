import Papers.PODC2016.StorageCostLowerBounds.Stream
import Papers.PODC2016.StorageCostLowerBounds.RelayInv

/-!
# Safety of the streaming relay: the invariant

`Inv qs C α` is an inductive invariant of the reachable configurations of `alg qs` (with history
`α`). Notation: `S α` is the stream of bits of all invoked writes; `xW C i` is the number of bits
server `i` has received.

* Writer–server tokens (`TokW`): per server at most one bit is outstanding (sent, not yet
  acknowledged), and it is in exactly one place: in transit to the server, at the server (`pa`),
  or as the acknowledgement in transit.
* Forwarded stream (`fstr`): the bits the reader received from server `i`, followed by the bits
  in transit and the pending one, are the first `xW C i` bits of `S α`.
* Reader–server tokens (`TokQ`): per server at most one query is outstanding, in transit, pending
  at the server (`pd`), or answered in transit.
* The current read (`CurOk`), the reads-from data (`RFOk`): as for the relay (`RelayInv.lean`),
  with the answer of a server of `G` preceded by `lb·B` forwarded bits.
-/

namespace Podc.StorageCost.Stream

open Cslib.ChannelFailures Cslib.SharedMemory
open Podc.StorageCost.Relay (OkPair)

variable {n B : ℕ} (qs : ℕ)

abbrev Cfg (n B : ℕ) := Config (Node n) (register (Val B) (fun _ => false)) Msg (LSt n B)
abbrev Hist (n B : ℕ) := List (Label (Node n) (register (Val B) (fun _ => false)))

/-- Bits of an operation (reads have none). -/
def opBits : RWOp (Val B) → List Bool
  | .write v => bits v
  | .read => []

/-- The stream of all written bits. -/
def S (α : Hist n B) : List Bool := (opsOf α .wr).flatMap opBits

/-- Number of invoked writes. -/
abbrev K (α : Hist n B) : ℕ := (opsOf α .wr).length

/-- Value of write `t`. -/
abbrev wv (α : Hist n B) (t : ℕ) : Val B := writeVal (fun _ => false) (opsOf α .wr) t

/-- Bits received by server `i`. -/
abbrev xW (C : Cfg n B) (i : Fin n) : ℕ := C.dlv .wr (.srv i)

/-- Forwarded bits in a list of messages. -/
def Fbits (l : List Msg) : List Bool := l.filterMap fun m => match m with
  | .F b => some b
  | _ => none

/-- Number of answers in a list of messages. -/
def nD (l : List Msg) : ℕ := l.count .D

/-- Writer state, reader state, server state. -/
abbrev ws (C : Cfg n B) : WSt n B := (C.loc .wr).1
abbrev rs (C : Cfg n B) : RSt n B := (C.loc .rd).2.1
abbrev ss (C : Cfg n B) (i : Fin n) : SSt := (C.loc (.srv i)).2.2

/-- The writer–server token of server `i`. -/
def TokW (C : Cfg n B) (α : Hist n B) (i : Fin n) : Prop :=
  let a := (ws C).ackc i
  let sc := (ws C).sentc i
  a ≤ sc ∧ sc ≤ a + 1 ∧ sc ≤ (S α).length ∧ (sc = a → a = (S α).length) ∧
  ((sc = a ∧ xW C i = a ∧ C.chan .wr (.srv i) = [] ∧ (ss C i).1 = none ∧ (ss C i).2.1 = false ∧
      C.chan (.srv i) .wr = []) ∨
   (sc = a + 1 ∧ xW C i = a ∧ C.chan .wr (.srv i) = [.W ((S α).getD a false)] ∧
      (ss C i).1 = none ∧ (ss C i).2.1 = false ∧ C.chan (.srv i) .wr = []) ∨
   (sc = a + 1 ∧ xW C i = a + 1 ∧ C.chan .wr (.srv i) = [] ∧ (ss C i).2.1 = true ∧
      C.chan (.srv i) .wr = []) ∨
   (sc = a + 1 ∧ xW C i = a + 1 ∧ C.chan .wr (.srv i) = [] ∧ (ss C i).1 = none ∧
      (ss C i).2.1 = false ∧ C.chan (.srv i) .wr = [.A]))

/-- The reader–server token of server `i`. -/
def TokQ (C : Cfg n B) (i : Fin n) : Prop :=
  ((rs C).sentAt i = none ∧ C.chan .rd (.srv i) = [] ∧ (ss C i).2.2.1 = false ∧
      nD (C.chan (.srv i) .rd) = 0) ∨
  (∃ j, (rs C).sentAt i = some j ∧ j ≤ (rs C).q ∧
    ((C.chan .rd (.srv i) = [.Q] ∧ (ss C i).2.2.1 = false ∧ nD (C.chan (.srv i) .rd) = 0) ∨
     (C.chan .rd (.srv i) = [] ∧ (ss C i).2.2.1 = true ∧ nD (C.chan (.srv i) .rd) = 0) ∨
     (C.chan .rd (.srv i) = [] ∧ (ss C i).2.2.1 = false ∧ nD (C.chan (.srv i) .rd) = 1)))

/-- In a channel to the reader, every answer is preceded by at least `k - g` forwarded bits. -/
def DAfter (k g : ℕ) (l : List Msg) : Prop :=
  ∀ pos, l[pos]? = some .D → k ≤ g + (Fbits (l.take pos)).length

/-- Reads-from data for the completed reads. -/
def RFOk (C : Cfg n B) (α : Hist n B) (rf : ℕ → ℕ) : Prop :=
  ∀ j < (respsOf α .rd).length,
    respOf α (.rd, j) = some (wv α (rf j)) ∧ rf j ≤ (rs C).best ∧ rf j ≤ K α ∧
    (0 < rf j → ¬ Precedes α (.rd, j) (.wr, rf j - 1)) ∧ ¬ Precedes α (.wr, rf j) (.rd, j) ∧
    ∀ j' < (respsOf α .rd).length, j ≤ j' → rf j ≤ rf j'

/-- The current read: `lb` bounds the writes completed before it was invoked. -/
def CurOk (C : Cfg n B) (α : Hist n B) : Prop :=
  (rs C).resp.card < qs ∧ ∃ lb,
    (∀ m, Precedes α (.wr, m) (.rd, (rs C).q - 1) → m < lb) ∧
    (lb = 0 ∨ ∃ G : Finset (Fin n), qs ≤ G.card ∧ ∀ i ∈ G, lb * B ≤ (ws C).ackc i ∧
      (i ∈ (rs C).resp → lb ≤ (rs C).best) ∧
      ((rs C).sentAt i = some (rs C).q →
        DAfter (lb * B) ((rs C).got i).length (C.chan (.srv i) .rd)))

/-- The invariant. -/
structure Inv (C : Cfg n B) (α : Hist n B) : Prop where
  wops : ∀ o ∈ opsOf α .wr, ∃ v, o = .write v
  wK : (ws C).K = K α
  wS : (ws C).strm = S α
  wbusy : (ws C).busy = true ↔ C.pend .wr ≠ none
  wcur : (ws C).busy = true → (ws C).cur = wv α (K α)
  wresp : ∀ j < (respsOf α .wr).length, respOf α (.wr, j) = some (wv α (j + 1))
  wdone : (ws C).busy = true →
    (Finset.univ.filter fun i => (S α).length ≤ (ws C).ackc i).card < qs
  wq : qs ≤ (Finset.univ.filter fun i => (respsOf α .wr).length * B ≤ (ws C).ackc i).card
  tokW : ∀ i, TokW C α i
  fstr : ∀ i, (rs C).got i ++ Fbits (C.chan (.srv i) .rd) ++ (ss C i).1.toList =
    (S α).take (xW C i)
  chR : ∀ i, ∀ m ∈ C.chan (.srv i) .rd, (∃ b, m = .F b) ∨ m = .D
  rq : (rs C).q = (opsOf α .rd).length
  rbusy : (rs C).busy = true ↔ C.pend .rd ≠ none
  rbest : (rs C).best ≤ K α
  rval : (rs C).val = wv α (rs C).best
  rmax : ∀ i, ((rs C).got i).length / B ≤ (rs C).best
  tokQ : ∀ i, TokQ C i
  rcur : (rs C).busy = true → CurOk qs C α
  rf : ∃ rf, RFOk C α rf
  other : ∀ a b, ¬ OkPair a b → C.chan a b = []

theorem inv_init (hqn : qs ≤ n) :
    Inv qs (alg (n := n) (B := B) qs).initCfg ([] : Hist n B) := by
  refine ⟨by simp, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨id, ?_⟩, ?_⟩
  all_goals simp [Algorithm.initCfg, alg, lInit, RFOk, TokW, TokQ, S, Fbits, nD, ws, rs, ss, xW]
  exact hqn

end Podc.StorageCost.Stream
