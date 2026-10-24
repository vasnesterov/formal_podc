import Papers.PODC2016.StorageCostLowerBounds.Model

/-!
# The relay algorithm: zero bits of server storage

A counterexample to Theorems 4.1, 5.1 and B.1 of the paper in the FIFO-channel model.
Servers are **stateless relays**; the value is kept in the reader's incoming channels.

* Write `t` (the `t`-th write, value `v`): the writer sends `W t v` to every server and returns
  once `qs` servers acknowledged (`A t`).
* A server receiving `W t v` forwards `F t v` to the reader and sends `A t` to the writer; a
  server receiving the query `Q j` from the reader answers `D j`. Its local state never changes.
* The reader records the largest write index `best` it has seen in an `F` message, with its
  value. Read `j` sends `Q j` to every server and returns the recorded value once `qs` servers
  answered `D j`.

With `qs = n - f` and `2 f < n` the algorithm is atomic (`RelayInv.lean`) and live
(`RelayLive.lean`). FIFO is essential: when the reader receives `D j` from a server, it has already
received every `F` that server sent before.
-/

namespace Podc.StorageCost.Relay

open Cslib.ChannelFailures Cslib.SharedMemory

variable {n : ℕ} {V : Type}

/-- Writer state. -/
structure WSt (n : ℕ) (V : Type) where
  /-- Number of writes invoked. -/
  k : ℕ
  /-- A write is pending. -/
  busy : Bool
  /-- Value of the last write. -/
  cur : V
  /-- Servers that acknowledged the pending write. -/
  acked : Finset (Fin n)

/-- Reader state. -/
structure RSt (n : ℕ) (V : Type) where
  /-- Number of reads invoked. -/
  q : ℕ
  /-- A read is pending. -/
  busy : Bool
  /-- Largest write index seen. -/
  best : ℕ
  /-- Its value. -/
  val : V
  /-- Servers that answered the pending read. -/
  resp : Finset (Fin n)

/-- Messages. -/
inductive Msg (V : Type) where
  /-- Writer to server: write `t` has value `v`. -/
  | W (t : ℕ) (v : V)
  /-- Server to writer: acknowledgement of write `t`. -/
  | A (t : ℕ)
  /-- Server to reader: forwarded write `t` with value `v`. -/
  | F (t : ℕ) (v : V)
  /-- Reader to server: query of read `j`. -/
  | Q (j : ℕ)
  /-- Server to reader: answer to query `j`. -/
  | D (j : ℕ)
  deriving DecidableEq

/-- Local states: every node carries a writer and a reader component; the writer uses the first,
the reader the second, servers never change theirs. -/
abbrev LSt (n : ℕ) (V : Type) := WSt n V × RSt n V

/-- Send `m` to every server. -/
def toAll (m : Msg V) : List (Node n × Msg V) := (List.finRange n).map fun i => (Node.srv i, m)

variable (v₀ : V) (qs : ℕ)

/-- The transition function (`qs` is the quorum size `n - f`). -/
def handle : Node n → Input (Node n) (RWOp V) (Msg V) → LSt n V →
    LSt n V × List (Node n × Msg V) × Option V
  | .wr, .invoke (.write v), (w, r) => ((⟨w.k + 1, true, v, ∅⟩, r), toAll (.W (w.k + 1) v), none)
  | .wr, .recv (.srv i) (.A t), (w, r) =>
    if w.busy = true ∧ t = w.k then
      if qs ≤ (insert i w.acked).card then
        ((⟨w.k, false, w.cur, insert i w.acked⟩, r), [], some w.cur)
      else ((⟨w.k, true, w.cur, insert i w.acked⟩, r), [], none)
    else ((w, r), [], none)
  | .rd, .invoke .read, (w, r) =>
    ((w, ⟨r.q + 1, true, r.best, r.val, ∅⟩), toAll (.Q (r.q + 1)), none)
  | .rd, .recv (.srv _) (.F t v), (w, r) =>
    if r.best < t then ((w, ⟨r.q, r.busy, t, v, r.resp⟩), [], none) else ((w, r), [], none)
  | .rd, .recv (.srv i) (.D j), (w, r) =>
    if r.busy = true ∧ j = r.q then
      if qs ≤ (insert i r.resp).card then
        ((w, ⟨r.q, false, r.best, r.val, insert i r.resp⟩), [], some r.val)
      else ((w, ⟨r.q, true, r.best, r.val, insert i r.resp⟩), [], none)
    else ((w, r), [], none)
  | .srv _, .recv .wr (.W t v), l => (l, [(.rd, .F t v), (.wr, .A t)], none)
  | .srv _, .recv .rd (.Q j), l => (l, [(.rd, .D j)], none)
  | _, _, l => (l, [], none)

/-- Initial local state. -/
def lInit : LSt n V := (⟨0, false, v₀, ∅⟩, ⟨0, false, 0, v₀, ∅⟩)

/-- The relay algorithm. -/
def relay : Algorithm (Node n) (register V v₀) (Msg V) (LSt n V) where
  init _ := lInit v₀
  handle := handle qs

/-! ### Basic facts -/

/-- Servers never change their local state. -/
theorem srv_loc (E : List (Event (Node n) (register V v₀))) (i : Fin n) :
    ((relay v₀ qs).run (relay v₀ qs).initCfg E).loc (.srv i) = lInit v₀ := by
  suffices h : ∀ C : Config (Node n) (register V v₀) (Msg V) (LSt n V), C.loc (.srv i) = lInit v₀ →
      ((relay v₀ qs).run C E).loc (.srv i) = lInit v₀ from h _ rfl
  intro C hC
  induction E generalizing C with
  | nil => exact hC
  | cons e E ih =>
    refine ih _ ?_
    by_cases ho : e.owner = .srv i
    · have key : ∀ (C' : Config (Node n) (register V v₀) (Msg V) (LSt n V))
          (inp : Input (Node n) (RWOp V) (Msg V)), C'.loc (.srv i) = lInit v₀ →
          (C'.apply (.srv i) (handle qs (.srv i) inp (C'.loc (.srv i)))).1.loc (.srv i) =
            lInit v₀ := by
        intro C' inp h
        simp only [Config.apply, Function.update_self]
        rw [h]
        rcases inp with o | c | ⟨q, m⟩
        · rfl
        · rfl
        · rcases q with _ | _ | _ <;> rcases m <;> rfl
      cases e with
      | invoke p o =>
        simp only [Event.owner] at ho; subst ho
        simp only [Algorithm.step]
        split
        · exact hC
        · exact key _ _ hC
      | tick p c =>
        simp only [Event.owner] at ho; subst ho
        exact key _ _ hC
      | deliver a p =>
        simp only [Event.owner] at ho; subst ho
        simp only [Algorithm.step]
        split
        · exact hC
        · exact key _ _ hC
    · rw [loc_step_ne _ _ _ (Ne.symm ho)]; exact hC

/-- The relay algorithm does not gossip. -/
theorem noGossip : NoGossip (relay v₀ qs : Algorithm (Node n) (register V v₀) _ _) := by
  intro i inp l x hx j
  rcases inp with o | c | ⟨q, m⟩
  · simp [relay, handle] at hx
  · simp [relay, handle] at hx
  · rcases q with _ | _ | _ <;> rcases m <;> simp [relay, handle] at hx <;>
      rcases hx with rfl | rfl <;> simp

/-- Server state sets of the relay algorithm: a single state. -/
theorem stateBound :
    StateBound (relay v₀ qs : Algorithm (Node n) (register V v₀) _ _) (fun _ => {lInit v₀}) :=
  fun E _ i => by simp [srv_loc]

end Podc.StorageCost.Relay
