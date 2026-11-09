import Cslib.Computability.Distributed.MessagePassing.Async
import Mathlib.Data.List.MinMax
import Mathlib.Data.Fintype.Card
import Mathlib.Order.WithBot
import Mathlib.Order.Prod.Lex.Basic

/-!
# The algorithms OhSam, OhMam, OhSam', OhMam' (Hadjistasi–Nicolaou–Schwarzmann)

Model: CSLib's asynchronous crash-prone message passing `Cslib.AsyncMP` (reliable, *non-FIFO*
point-to-point channels; any process may crash; a message whose sender crashed may be lost).
Processes are writers `W`, readers `R` and replica servers `S` (`Node`); the implemented object is
CSLib's `register V v₀`.

One protocol `proto Vr next` covers the four algorithms of the paper:

* `Vr.mw = false`: the single-writer write protocol of OhSam (Algorithm 1, lines 18–31, 41–44):
  the writer picks the tag `next w tag` (`ts + 1`) and sends `writeRequest` to all servers;
* `Vr.mw = true`: the multi-writer write protocol of OhMam (Algorithm 2, lines 73–94, 118–124):
  a `discover` phase, then the tag `next w maxTag` (`⟨maxTS + 1, w⟩`), then a `writeRequest`
  phase; servers update only if `tg < tg' ∧ write_ops[w] < write_op`;
* `Vr.fast = false`: the read protocol of OhSam/OhMam (three exchanges: `readRequest`,
  server-to-server `readRelay`, `readAck`; the reader returns the value of the *minimum* tag
  among a majority of `readAck`s);
* `Vr.fast = true`: the revised read protocol of OhSam'/OhMam' (Algorithm 3): servers also relay
  to the reader, who may return after a majority of relays carrying the same tag.
* `Vr.fixAck`: `false` is the printed code, where the test of line 53 (`relays[r] = |S|/2 + 1`)
  is *outside* the `if` of line 51, so a stale `readRelay` re-sends a `readAck`; `true` nests it
  (our repair of the message complexity, see `Complexity.lean`).

Tags live in any linear order `T` with bottom `⊥` (the tag of the initial value `v₀`) and are
created by `next : W → T → T`: `fun _ t => t + 1` on `ℕ` for OhSam(') and `nextTag` on
`Tag W = WithBot (ℕ ×ₗ W)` for OhMam(') (`⊥` stands for the initial server tags `⟨0, sᵢ⟩`).

Each block of code between two `wait`s runs atomically. All waits (`wait until |ack| = |S|/2+1`
and the fast-read condition) are evaluated in the message handler right after the reception
that may make them true, so they are exactly the paper's `=` tests. The acknowledgment sets
`rAck`, `rRelay`, `wAck`, `mAck ⊆ S × M` are lists without duplicates (`List.insert`) of triples
`(sender, tag, value)` — the other fields of `m` (operation counter, sender id, message type) are
determined by the filters. The server field `got` is a ghost variable (the senders of the relays
counted by `relays[r]`); it never influences the behaviour.
-/

set_option linter.unusedSectionVars false

namespace Podc.OhRAM

open Cslib.SharedMemory Cslib.AsyncMP

/-- Process identifiers: writers `W`, readers `R`, replica servers `S`. -/
inductive Node (W R S : Type) where
  | wr (w : W)
  | rd (r : R)
  | sv (s : S)
  deriving DecidableEq

/-- Messages. The identity of the sender is known from the channel (`(src, dst, m)`), so the
fields `r` of `readRequest`, `sᵢ` of `readRelay`/`readAck`/`writeAck`/`discoverAck` and `w` of
`writeRequest`/`discover` are omitted. The single-writer protocol has no `write_op`; it sends
`writeRequest t v 0` (the field is ignored). -/
inductive Msg (R T V : Type) where
  /-- `⟨readRequest, r, read_op⟩` (lines 10, 65, 128). -/
  | readRequest (k : ℕ)
  /-- `⟨readRelay, ts, v, r, read_op, sᵢ⟩` (lines 40, 107, 147). -/
  | readRelay (t : T) (v : V) (r : R) (k : ℕ)
  /-- `⟨readAck, ts, v, read_op, sᵢ⟩` (lines 54, 117). -/
  | readAck (t : T) (v : V) (k : ℕ)
  /-- `⟨writeRequest, ts, v, w⟩` (line 26) / `⟨writeRequest, tg, v, write_op, w⟩` (line 89). -/
  | writeRequest (t : T) (v : V) (op : ℕ)
  /-- `⟨writeAck, ts, v, sᵢ⟩` (line 44) / `⟨writeAck, tg, v, write_op, sᵢ⟩` (line 124). -/
  | writeAck (t : T) (v : V) (op : ℕ)
  /-- `⟨discover, write_op, w⟩` (line 83). -/
  | discover (op : ℕ)
  /-- `⟨discoverAck, tg, v, write_op, sᵢ⟩` (line 119). -/
  | discoverAck (t : T) (v : V) (op : ℕ)
  deriving DecidableEq

/-- Which of the four algorithms (and whether line 53 is repaired). -/
structure Variant where
  /-- Multi-writer write protocol (OhMam, OhMam'). -/
  mw : Bool
  /-- Revised read protocol with the two-exchange fast path (OhSam', OhMam'). -/
  fast : Bool
  /-- `true`: the test of line 53 is nested in the `if` of line 51 (our repair). -/
  fixAck : Bool := false

/-- Control position of a writer. -/
inductive WPhase (V : Type) where
  | idle
  /-- MWMR: waiting at line 84 for `discoverAck`s; will write `v`. -/
  | disc (v : V)
  /-- Waiting at line 27 / line 90 for `writeAck`s. -/
  | upd
  deriving DecidableEq

/-- Local state of a writer (lines 19–22, 74–79). -/
structure WLoc (S T V : Type) where
  /-- `ts` (SWMR) / `tg` (MWMR). -/
  tag : T
  /-- `v`. -/
  val : V
  /-- `write_op` (MWMR only). -/
  op : ℕ
  /-- Control position. -/
  phase : WPhase V
  /-- `wAck` / `mAck`. -/
  ack : List (S × T × V)

/-- Local state of a reader (lines 2–6, 56–61, 120–124). -/
structure RLoc (S T V : Type) where
  /-- `read_op`. -/
  op : ℕ
  /-- A read is in progress. -/
  pending : Bool
  /-- `rAck`. -/
  ack : List (S × T × V)
  /-- `rRelay` (revised read protocol). -/
  relay : List (S × T × V)

/-- Local state of a server (lines 33–38, 96–105). -/
structure SLoc (W R S T V : Type) where
  /-- `ts` / `tg`. -/
  tag : T
  /-- `v`. -/
  val : V
  /-- `operations[r]`. -/
  ops : R → ℕ
  /-- `relays[r]`. -/
  relays : R → ℕ
  /-- `write_ops[w]` (MWMR only). -/
  wops : W → ℕ
  /-- Ghost: the senders of the `readRelay`s counted in `relays[r]`. -/
  got : R → Finset S

/-- Local states (each process uses only the component of its kind). -/
structure Loc (W R S T V : Type) where
  /-- Writer variables. -/
  w : WLoc S T V
  /-- Reader variables. -/
  r : RLoc S T V
  /-- Server variables. -/
  s : SLoc W R S T V

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V]

variable (S) in
/-- The quorum size `|S|/2 + 1` (integer division). -/
def maj : ℕ := Fintype.card S / 2 + 1

/-- `broadcast m to S`. -/
def bcast (m : Msg R T V) : Multiset (Node W R S × Msg R T V) :=
  (Finset.univ : Finset S).val.map (fun s => (Node.sv s, m))

/-- The maximum tag in a list of acknowledgments (line 85; `⊥` for the empty list). -/
def maxTag (a : List (S × T × V)) : T := (a.map (·.2.1)).foldr max ⊥

/-- Lines 12–13: the value associated with the minimum tag of `rAck`. -/
def minVal (v₀ : V) (a : List (S × T × V)) : V :=
  ((a.argmin (·.2.1)).map (·.2.2)).getD v₀

/-- Lines 130–131 and 137: the value of a set `Z ⊆ rRelay` of at least `|S|/2 + 1` relays with
the same tag, if there is one. -/
def fastVal (a : List (S × T × V)) : Option V :=
  (a.find? (fun p => decide (maj S ≤ (a.filter (fun q => decide (q.2.1 = p.2.1))).length))).map
    (·.2.2)

section Writer

variable (Vr : Variant) (next : W → T → T)

/-- Invocation of `write(val)` by writer `w` (lines 23–26 / 80–83). -/
def wInvoke (w : W) (val : V) (l : WLoc S T V) :
    Option (WLoc S T V × Multiset (Node W R S × Msg R T V)) :=
  match l.phase with
  | .idle =>
    if Vr.mw then
      some ({ l with op := l.op + 1, ack := [], phase := .disc val }, bcast (.discover (l.op + 1)))
    else
      some ({ l with tag := next w l.tag, val := val, ack := [], phase := .upd },
        bcast (.writeRequest (next w l.tag) val 0))
  | _ => none

/-- Lines 29–31 / 92–94: record an acknowledgment from server `s`. -/
def wRecord (s : S) (m : Msg R T V) (l : WLoc S T V) : WLoc S T V :=
  match m with
  | .writeAck t v k =>
    if (if Vr.mw then k = l.op else t = l.tag) then { l with ack := l.ack.insert (s, t, v) } else l
  | .discoverAck t v k =>
    if Vr.mw ∧ k = l.op then { l with ack := l.ack.insert (s, t, v) } else l
  | _ => l

/-- The waits of the writer (lines 27–28 / 84–91), evaluated after each reception. -/
def wWait (w : W) (l : WLoc S T V) :
    WLoc S T V × Multiset (Node W R S × Msg R T V) × Option V :=
  if l.ack.length = maj S then
    match l.phase with
    | .disc val =>
      ({ l with
          tag := next w (maxTag l.ack), val := val, op := l.op + 1, ack := [], phase := .upd },
        bcast (.writeRequest (next w (maxTag l.ack)) val (l.op + 1)), none)
    | .upd => ({ l with phase := .idle }, 0, some l.val)
    | .idle => (l, 0, none)
  else (l, 0, none)

end Writer

section Reader

variable (Vr : Variant) (v₀ : V)

/-- Invocation of `read()` by reader `r` (lines 7–10 / 62–65 / 125–128). -/
def rInvoke (l : RLoc S T V) : Option (RLoc S T V × Multiset (Node W R S × Msg R T V)) :=
  if l.pending then none else
    some ({ op := l.op + 1, pending := true, ack := [], relay := [] },
      bcast (.readRequest (l.op + 1)))

/-- Lines 15–17 / 70–72 / 139–144: record a fresh `readAck` or (revised protocol) `readRelay`. -/
def rRecord (s : S) (m : Msg R T V) (l : RLoc S T V) : RLoc S T V :=
  match m with
  | .readAck t v k => if k = l.op then { l with ack := l.ack.insert (s, t, v) } else l
  | .readRelay t v _ k =>
    if Vr.fast ∧ k = l.op then { l with relay := l.relay.insert (s, t, v) } else l
  | _ => l

/-- The wait of the reader (lines 11–14 / 66–69 / 129–138), evaluated after each reception. -/
def rWait (l : RLoc S T V) : RLoc S T V × Option V :=
  if l.pending then
    if l.ack.length = maj S then ({ l with pending := false }, some (minVal v₀ l.ack))
    else if Vr.fast then
      match fastVal l.relay with
      | some v => ({ l with pending := false }, some v)
      | none => (l, none)
    else (l, none)
  else (l, none)

end Reader

section Server

variable (Vr : Variant)

/-- Lines 45–54 / 108–117: server `si` receives `⟨readRelay, t, v, r, k⟩` from server `sj`. -/
def sRelay (sj : S) (t : T) (v : V) (r : R) (k : ℕ) (l : SLoc W R S T V) :
    SLoc W R S T V × Multiset (Node W R S × Msg R T V) :=
  let l1 := if l.tag < t then { l with tag := t, val := v } else l
  let l2 := if l1.ops r < k then
      { l1 with
        ops := Function.update l1.ops r k, relays := Function.update l1.relays r 0,
        got := Function.update l1.got r ∅ }
    else l1
  let l3 := if l2.ops r = k then
      { l2 with
        relays := Function.update l2.relays r (l2.relays r + 1),
        got := Function.update l2.got r (insert sj (l2.got r)) }
    else l2
  (l3, if (Vr.fixAck = false ∨ l3.ops r = k) ∧ l3.relays r = maj S then
      {(Node.rd r, Msg.readAck l3.tag l3.val k)} else 0)

/-- Lines 41–44 / 120–124: server receives `writeRequest t v op` from writer `w`. -/
def sWrite (w : W) (t : T) (v : V) (op : ℕ) (l : SLoc W R S T V) :
    SLoc W R S T V × Multiset (Node W R S × Msg R T V) :=
  let l' := if Vr.mw then
      (if l.tag < t ∧ l.wops w < op then
        { l with tag := t, val := v, wops := Function.update l.wops w op } else l)
    else (if l.tag < t then { l with tag := t, val := v } else l)
  (l', {(Node.wr w, Msg.writeAck l'.tag l'.val op)})

/-- The message handlers of a server. -/
def sRecv (src : Node W R S) (m : Msg R T V) (l : SLoc W R S T V) :
    SLoc W R S T V × Multiset (Node W R S × Msg R T V) :=
  match src, m with
  | .rd r, .readRequest k =>
    -- lines 39–40 / 106–107 / 146–147
    (l, bcast (.readRelay l.tag l.val r k) +
      if Vr.fast then {(Node.rd r, Msg.readRelay l.tag l.val r k)} else 0)
  | .sv sj, .readRelay t v r k => sRelay Vr sj t v r k l
  | .wr w, .writeRequest t v op => sWrite Vr w t v op l
  | .wr w, .discover op =>
    -- lines 118–119
    (l, {(Node.wr w, Msg.discoverAck l.tag l.val op)})
  | _, _ => (l, 0)

end Server

variable (Vr : Variant) (next : W → T → T) (v₀ : V)

/-- Initial local state (lines 6, 22, 37–38, 60–61, 78–79, 102–105). -/
def initLoc : Loc W R S T V :=
  ⟨⟨⊥, v₀, 0, .idle, []⟩, ⟨0, false, [], []⟩, ⟨⊥, v₀, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ => ∅⟩⟩

/-- The protocol. Writers only write, readers only read, servers invoke nothing. -/
def proto : Protocol (Node W R S) (register V v₀) (Loc W R S T V) (Msg R T V) Empty where
  init _ := initLoc v₀
  invoke p o L :=
    match p, o with
    | .wr w, .write val => (wInvoke Vr next w val L.w).map fun x => ({ L with w := x.1 }, x.2)
    | .rd _, .read => (rInvoke L.r).map fun x => ({ L with r := x.1 }, x.2)
    | _, _ => none
  internal _ a _ := a.elim
  receive p q m L :=
    match p, q with
    | .wr w, .sv s =>
      let x := wWait (R := R) next w (wRecord Vr s m L.w)
      some ({ L with w := x.1 }, x.2.1, x.2.2)
    | .rd _, .sv s =>
      let x := rWait Vr v₀ (rRecord Vr s m L.r)
      some ({ L with r := x.1 }, 0, x.2)
    | .sv _, _ =>
      let x := sRecv Vr q m L.s
      some ({ L with s := x.1 }, x.2, none)
    | _, _ => some (L, 0, none)

/-! ## The four algorithms -/

/-- MWMR tags `⟨ts, id⟩`, ordered lexicographically; `⊥` is the tag of the initial value. -/
abbrev Tag (W : Type) := WithBot (ℕ ×ₗ W)

/-- Line 86: the tag `⟨maxTS + 1, w⟩` from the maximum tag `t` discovered. -/
def nextTag (w : W) : Tag W → Tag W
  | ⊥ => ((toLex (1, w) : ℕ ×ₗ W) : WithBot _)
  | (x : ℕ ×ₗ W) => ((toLex ((ofLex x).1 + 1, w) : ℕ ×ₗ W) : WithBot _)

variable (W R S V)

/-- **Algorithm 1 (OhSam)**: one writer (`W = Unit`), timestamps in `ℕ`. -/
def ohSam : Protocol (Node Unit R S) (register V v₀) (Loc Unit R S ℕ V) (Msg R ℕ V) Empty :=
  proto ⟨false, false, false⟩ (fun _ t => t + 1) v₀

/-- **Algorithm 2 (OhMam)**: writers `W` (a linear order breaks ties of tags). -/
def ohMam [LinearOrder W] :
    Protocol (Node W R S) (register V v₀) (Loc W R S (Tag W) V) (Msg R (Tag W) V) Empty :=
  proto ⟨true, false, false⟩ nextTag v₀

/-- **Algorithm 3 (OhSam')**: OhSam with the revised read protocol. -/
def ohSam' : Protocol (Node Unit R S) (register V v₀) (Loc Unit R S ℕ V) (Msg R ℕ V) Empty :=
  proto ⟨false, true, false⟩ (fun _ t => t + 1) v₀

/-- **OhMam'** (Section 5.2): OhMam with the revised read protocol. -/
def ohMam' [LinearOrder W] :
    Protocol (Node W R S) (register V v₀) (Loc W R S (Tag W) V) (Msg R (Tag W) V) Empty :=
  proto ⟨true, true, false⟩ nextTag v₀

end Podc.OhRAM
