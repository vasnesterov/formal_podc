import Papers.PODC2016.StorageCostLowerBounds.Model

/-!
# The streaming relay: an I/O-automaton-faithful counterexample

In the paper's I/O-automaton model every send is a separate output action, so a server must keep
in its state the messages it still has to send. `IOASends` formalizes this: a server step that
receives a message (or an invocation) sends nothing, and a spontaneous step sends at most one
message. The relay algorithm of `Relay.lean` does not satisfy it. The **streaming relay** does,
and its servers still have only `36` states, independent of the value set.

Values are bit vectors `V = Fin B → Bool`; the writer streams the bits of its values, in order,
one bit at a time to every server (stop-and-wait per server).
* Writer: keeps the whole stream `strm` (bits of all written values) and, per server, the number
  of bits sent (`sentc`) and acknowledged (`ackc`). A server is sent the next bit `W b` when its
  previous bit is acknowledged. Write `K` returns once `qs` servers acknowledged the whole stream.
* Server, state `(pf, pa, pd, turn)`: receiving `W b` sets `pf := some b`, `pa := true`; receiving
  the query `Q` sets `pd := true`. Spontaneous steps take turns: turn 0 sends `F b` to the reader
  (if `pf = some b`), turn 1 sends the acknowledgement `A` to the writer (if `pa` and the bit was
  forwarded), turn 2 sends the answer `D` to the reader (if `pd`).
* Reader: keeps all bits received from each server (`got`); whenever a server's bits complete a
  block of `B` bits, block number `t`, and `t > best`, it records `best := t` and the decoded value.
  Read `q` sends `Q` to every server without an outstanding query (`sentAt i = none`). An answer
  `D` to a query of the current read counts; an answer to an older query triggers a new `Q`. The
  read returns the recorded value once `qs` servers answered.
-/

namespace Podc.StorageCost.Stream

open Cslib.ChannelFailures Cslib.SharedMemory

variable {n B : ℕ}

/-- Values: bit vectors of length `B`. -/
abbrev Val (B : ℕ) := Fin B → Bool

/-- The bits of a value. -/
def bits (v : Val B) : List Bool := List.ofFn v

/-- Decoding a block of bits. -/
def decode (l : List Bool) : Val B := fun j => l.getD j false

@[simp] lemma length_bits (v : Val B) : (bits v).length = B := by simp [bits]

@[simp] lemma decode_bits (v : Val B) : decode (bits v) = v := by
  funext j; simp [decode, bits]

/-- Writer state. -/
structure WSt (n B : ℕ) where
  /-- Number of writes invoked. -/
  K : ℕ
  /-- A write is pending. -/
  busy : Bool
  /-- Value of the last write. -/
  cur : Val B
  /-- The bits of all written values. -/
  strm : List Bool
  /-- Bits sent to each server. -/
  sentc : Fin n → ℕ
  /-- Bits acknowledged by each server. -/
  ackc : Fin n → ℕ

/-- Reader state. -/
structure RSt (n B : ℕ) where
  /-- Number of reads invoked. -/
  q : ℕ
  /-- A read is pending. -/
  busy : Bool
  /-- Bits received from each server. -/
  got : Fin n → List Bool
  /-- Largest complete block received. -/
  best : ℕ
  /-- Its value. -/
  val : Val B
  /-- The read for which the outstanding query to a server was sent. -/
  sentAt : Fin n → Option ℕ
  /-- Servers that answered the current read. -/
  resp : Finset (Fin n)

/-- Server state: pending forward, pending acknowledgement, pending answer, turn. -/
abbrev SSt := Option Bool × Bool × Bool × Fin 3

/-- Messages. -/
inductive Msg where
  /-- Writer to server: next bit. -/
  | W (b : Bool)
  /-- Server to writer: acknowledgement of the last bit. -/
  | A
  /-- Server to reader: forwarded bit. -/
  | F (b : Bool)
  /-- Reader to server: query. -/
  | Q
  /-- Server to reader: answer. -/
  | D
  deriving DecidableEq

/-- Local states (every node carries all three components, each node uses its own). -/
abbrev LSt (n B : ℕ) := WSt n B × RSt n B × SSt

variable (qs : ℕ)

/-- Writer: invocation of `write v`. -/
def wInvoke (w : WSt n B) (v : Val B) : WSt n B × List (Node n × Msg) :=
  let s := w.strm ++ bits v
  (⟨w.K + 1, true, v, s, fun i => if w.sentc i = w.ackc i then w.sentc i + 1 else w.sentc i,
    w.ackc⟩,
   (List.finRange n).filterMap fun i =>
     if w.sentc i = w.ackc i then some (.srv i, .W (s.getD (w.ackc i) false)) else none)

/-- Writer: acknowledgement from server `i`. -/
def wAck (w : WSt n B) (i : Fin n) : WSt n B × List (Node n × Msg) × Option (Val B) :=
  let a := Function.update w.ackc i (w.ackc i + 1)
  let more := decide (w.ackc i + 1 < w.strm.length)
  let sc := if more then Function.update w.sentc i (w.sentc i + 1) else w.sentc
  let out := if more then [(.srv i, .W (w.strm.getD (w.ackc i + 1) false))] else []
  if w.busy = true ∧ qs ≤ (Finset.univ.filter fun j => w.strm.length ≤ a j).card then
    (⟨w.K, false, w.cur, w.strm, sc, a⟩, out, some w.cur)
  else (⟨w.K, w.busy, w.cur, w.strm, sc, a⟩, out, none)

/-- Reader: invocation of `read`. -/
def rInvoke (r : RSt n B) : RSt n B × List (Node n × Msg) :=
  (⟨r.q + 1, true, r.got, r.best, r.val,
    fun i => if r.sentAt i = none then some (r.q + 1) else r.sentAt i, ∅⟩,
   (List.finRange n).filterMap fun i => if r.sentAt i = none then some (.srv i, .Q) else none)

/-- Reader: forwarded bit `b` from server `i`. -/
def rBit (r : RSt n B) (i : Fin n) (b : Bool) : RSt n B :=
  let l := r.got i ++ [b]
  if l.length % B = 0 ∧ r.best < l.length / B then
    ⟨r.q, r.busy, Function.update r.got i l, l.length / B, decode (l.drop (l.length - B)),
      r.sentAt, r.resp⟩
  else ⟨r.q, r.busy, Function.update r.got i l, r.best, r.val, r.sentAt, r.resp⟩

/-- Reader: answer from server `i`. -/
def rAns (r : RSt n B) (i : Fin n) : RSt n B × List (Node n × Msg) × Option (Val B) :=
  if r.busy = true then
    if r.sentAt i = some r.q then
      if qs ≤ (insert i r.resp).card then
        (⟨r.q, false, r.got, r.best, r.val, Function.update r.sentAt i none, insert i r.resp⟩,
          [], some r.val)
      else (⟨r.q, true, r.got, r.best, r.val, Function.update r.sentAt i none, insert i r.resp⟩,
          [], none)
    else (⟨r.q, true, r.got, r.best, r.val, Function.update r.sentAt i (some r.q), r.resp⟩,
          [(.srv i, .Q)], none)
  else (⟨r.q, false, r.got, r.best, r.val, Function.update r.sentAt i none, r.resp⟩, [], none)

/-- Server: spontaneous step. -/
def sTick : SSt → SSt × List (Node n × Msg)
  | (some b, pa, pd, 0) => ((none, pa, pd, 1), [(.rd, .F b)])
  | (none, pa, pd, 0) => ((none, pa, pd, 1), [])
  | (pf, true, pd, 1) =>
    if pf = none then ((pf, false, pd, 2), [(.wr, .A)]) else ((pf, true, pd, 2), [])
  | (pf, false, pd, 1) => ((pf, false, pd, 2), [])
  | (pf, pa, true, 2) => ((pf, pa, false, 0), [(.rd, .D)])
  | (pf, pa, false, 2) => ((pf, pa, false, 0), [])

/-- The transition function. -/
def handle : Node n → Input (Node n) (RWOp (Val B)) Msg → LSt n B →
    LSt n B × List (Node n × Msg) × Option (Val B)
  | .wr, .invoke (.write v), (w, r, s) => (((wInvoke w v).1, r, s), (wInvoke w v).2, none)
  | .wr, .recv (.srv i) .A, (w, r, s) => (((wAck qs w i).1, r, s), (wAck qs w i).2.1, (wAck qs w i).2.2)
  | .rd, .invoke .read, (w, r, s) => ((w, (rInvoke r).1, s), (rInvoke r).2, none)
  | .rd, .recv (.srv i) (.F b), (w, r, s) => ((w, rBit r i b, s), [], none)
  | .rd, .recv (.srv i) .D, (w, r, s) => ((w, (rAns qs r i).1, s), (rAns qs r i).2.1, (rAns qs r i).2.2)
  | .srv _, .recv .wr (.W b), (w, r, s) => ((w, r, (some b, true, s.2.2)), [], none)
  | .srv _, .recv .rd .Q, (w, r, s) => ((w, r, (s.1, s.2.1, true, s.2.2.2)), [], none)
  | .srv _, .tick _, (w, r, s) => ((w, r, (sTick (n := n) s).1), (sTick (n := n) s).2, none)
  | _, _, l => (l, [], none)

/-- Initial local state. -/
def lInit : LSt n B :=
  (⟨0, false, fun _ => false, [], fun _ => 0, fun _ => 0⟩,
   ⟨0, false, fun _ => [], 0, fun _ => false, fun _ => none, ∅⟩, (none, false, false, 0))

/-- The streaming relay with quorum size `qs`. -/
def alg : Algorithm (Node n) (register (Val B) (fun _ => false)) Msg (LSt n B) where
  init _ := lInit
  handle := handle qs

/-- **The I/O-automaton restriction for servers**: a step processing an input (invocation or
received message) sends nothing; a spontaneous step sends at most one message. (Client states are
not counted, so clients may buffer outputs for free; they are not restricted.) -/
def IOASends {M L : Type} {V : Type} {v₀ : V} (A : Algorithm (Node n) (register V v₀) M L) :
    Prop :=
  ∀ i inp l, ((∀ c, inp ≠ .tick c) → (A.handle (.srv i) inp l).2.1 = []) ∧
    (A.handle (.srv i) inp l).2.1.length ≤ 1

theorem ioaSends : IOASends (alg (n := n) (B := B) qs) := by
  intro i inp l
  obtain ⟨w, r, s⟩ := l
  rcases inp with o | c | ⟨q, m⟩
  · simp [alg, handle]
  · refine ⟨fun h => absurd rfl (h c), ?_⟩
    obtain ⟨pf, pa, pd, t⟩ := s
    simp only [alg, handle]
    rcases pf with _ | b <;> rcases pa <;> rcases pd <;> fin_cases t <;> simp [sTick]
  · rcases q with _ | _ | _ <;> rcases m <;> simp [alg, handle]

/-- The streaming relay does not gossip. -/
theorem noGossip : NoGossip (alg (n := n) (B := B) qs) := by
  intro i inp l x hx j
  obtain ⟨w, r, s⟩ := l
  rcases inp with o | c | ⟨q, m⟩
  · simp [alg, handle] at hx
  · obtain ⟨pf, pa, pd, t⟩ := s
    simp only [alg, handle] at hx
    rcases pf with _ | b <;> rcases pa <;> rcases pd <;> fin_cases t <;>
      simp [sTick] at hx <;> subst hx <;> simp
  · rcases q with _ | _ | _ <;> rcases m <;> simp [alg, handle] at hx

/-- Servers only change their own component. -/
theorem srv_loc (E : List (Event (Node n) (register (Val B) (fun _ => false)))) (i : Fin n) :
    ∃ s : SSt, ((alg qs).run (alg qs).initCfg E).loc (.srv i) = (lInit.1, lInit.2.1, s) := by
  suffices h : ∀ C : Config (Node n) (register (Val B) (fun _ => false)) Msg (LSt n B),
      (∃ s : SSt, C.loc (.srv i) = (lInit.1, lInit.2.1, s)) →
      ∃ s : SSt, ((alg qs).run C E).loc (.srv i) = (lInit.1, lInit.2.1, s) from h _ ⟨_, rfl⟩
  intro C hC
  induction E generalizing C with
  | nil => exact hC
  | cons e E ih =>
    refine ih _ ?_
    by_cases ho : e.owner = .srv i
    · obtain ⟨s, hs⟩ := hC
      have key : ∀ (C' : Config (Node n) (register (Val B) (fun _ => false)) Msg (LSt n B))
          (inp : Input (Node n) (RWOp (Val B)) Msg), C'.loc (.srv i) = (lInit.1, lInit.2.1, s) →
          ∃ s' : SSt, (C'.apply (.srv i) (handle qs (.srv i) inp (C'.loc (.srv i)))).1.loc
            (.srv i) = (lInit.1, lInit.2.1, s') := by
        intro C' inp h
        simp only [Config.apply, Function.update_self]
        rw [h]
        rcases inp with o | c | ⟨q, m⟩
        · exact ⟨s, rfl⟩
        · exact ⟨_, rfl⟩
        · rcases q with _ | _ | _ <;> rcases m <;> exact ⟨_, rfl⟩
      cases e with
      | invoke p o =>
        simp only [Event.owner] at ho; subst ho
        simp only [Algorithm.step]
        split
        · exact ⟨s, hs⟩
        · exact key _ _ hs
      | tick p c =>
        simp only [Event.owner] at ho; subst ho
        exact key _ _ hs
      | deliver a p =>
        simp only [Event.owner] at ho; subst ho
        simp only [Algorithm.step]
        split
        · exact ⟨s, hs⟩
        · exact key _ _ hs
    · rw [loc_step_ne _ _ _ (Ne.symm ho)]; exact hC

/-- The 36 server states. -/
def srvStates : Fin n → Finset (LSt n B) := fun _ =>
  (Finset.univ : Finset SSt).map ⟨fun s => (lInit.1, lInit.2.1, s), fun a b h => by
    simpa using h⟩

theorem card_srvStates (i : Fin n) : (srvStates (n := n) (B := B) i).card = 36 := by
  simp [srvStates]

theorem stateBound : StateBound (alg (n := n) (B := B) qs) srvStates := by
  intro E _ i
  obtain ⟨s, hs⟩ := srv_loc qs E i
  rw [hs]; exact Finset.mem_map_of_mem _ (Finset.mem_univ s)

end Podc.StorageCost.Stream
