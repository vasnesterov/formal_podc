import Mathlib

/-!
# Servers and the `ss-broadcast` abstraction

Bonomi, Dolev, Potop-Butucaru, Raynal. *Stabilizing Server-Based Storage in Byzantine Asynchronous
Message-Passing Systems.* PODC 2015 (full version arXiv:1503.00140v1).

The server code (lines 19–23) is the same in Fig. 2 (regular register) and Fig. 3 (practically atomic
register); only the payload type `D` differs (`D = V` in Fig. 2, `D = seqnum × V` in Fig. 3).

## Model of `ss-broadcast`

Every server `s` has two FIFO links, one from the writer (`wq`) and one from the reader (`rq`). Their
initial contents are arbitrary (transient failures), an `ss_broadcast` appends the message at the end
of the link of every server, and a server step `ss_deliver`s the head of one of its links.
Hence *no duplication*, *validity* (a delivered message was broadcast or was in the initial link) and
*FIFO order* hold by construction. *Synchronized delivery* is a guard of the client step that ends a
broadcast: at least `n - 2t` correct servers have delivered it (their link is empty, since the client
broadcasts one message at a time). *Termination* and *eventual delivery* are fairness properties of
infinite executions.

The paper matches acknowledgments with broadcasts by FIFO order (Remark of Section 3.1). We model this
matching *favourably to the paper*: a server's reply is recorded in a ghost slot (`wack`, `rack`) only
when it answers the client's *current* broadcast (the delivered message is the last one in the link);
the slot is cleared by every new broadcast of that client. Stale replies are thus never used.
-/

namespace Podc.StabilizingByzStorage

/-- Messages `ss-broadcast` by the writer: `WRITE(v)` and `NEW_HELP_VAL(v)`. -/
inductive WMsg (D : Type) where
  | write (d : D)
  | newHelp (d : D)
  deriving DecidableEq, Repr

/-- Local state of a server: `last_val`, `helping_val` (`none` = `⊥`), the two incoming links and the
ghost reply slots for the clients' current broadcasts. -/
structure Server (D : Type) where
  last : D
  help : Option D
  /-- Link from the writer (pending messages, oldest first). -/
  wq : List (WMsg D)
  /-- Link from the reader: pending `READ(new_read)` messages. -/
  rq : List Bool
  /-- `ACK_WRITE(helping_val)` sent in answer to the writer's current broadcast, if any. -/
  wack : Option (Option D)
  /-- `ACK_READ(last_val, helping_val)` sent in answer to the reader's current broadcast, if any. -/
  rack : Option (D × Option D)
  deriving DecidableEq, Repr

namespace Server

variable {D : Type}

/-- Lines 19–21: deliver the oldest pending message of the writer. `WRITE(v)`: `last_val ← v` and
answer `ACK_WRITE(helping_val)`; `NEW_HELP_VAL(v)`: `helping_val ← v`. -/
def deliverW (s : Server D) : Server D :=
  match s.wq with
  | [] => s
  | .write d :: rest =>
    { s with last := d, wq := rest, wack := if rest = [] then some s.help else s.wack }
  | .newHelp d :: rest => { s with help := some d, wq := rest }

/-- Lines 22–23: deliver the oldest pending `READ(new_read)`; reset `helping_val` if `new_read`, and
answer `ACK_READ(last_val, helping_val)`. -/
def deliverR (s : Server D) : Server D :=
  match s.rq with
  | [] => s
  | b :: rest =>
    let h := if b then none else s.help
    { s with help := h, rq := rest, rack := if rest = [] then some (s.last, h) else s.rack }

/-- The writer `ss-broadcast`s `m`: append to the link, clear the reply slot. -/
def bcastW (m : WMsg D) (s : Server D) : Server D := { s with wq := s.wq ++ [m], wack := none }

/-- The reader `ss-broadcast`s `READ(b)`. -/
def bcastR (b : Bool) (s : Server D) : Server D := { s with rq := s.rq ++ [b], rack := none }

end Server

variable {n : ℕ}

/-- Number of members of `Q` whose reply `f` equals `a` (a threshold test of the pseudo-code). -/
def cnt {α : Type} [DecidableEq α] (Q : Finset (Fin n)) (f : Fin n → α) (a : α) : ℕ :=
  (Q.filter fun s => f s = a).card

/-- Number of correct servers that have delivered the writer's current broadcast. -/
def syncW {D : Type} (B : Finset (Fin n)) (srv : Fin n → Server D) : ℕ :=
  (Finset.univ.filter fun s => s ∉ B ∧ (srv s).wq = []).card

/-- Number of correct servers that have delivered the reader's current broadcast. -/
def syncR {D : Type} (B : Finset (Fin n)) (srv : Fin n → Server D) : ℕ :=
  (Finset.univ.filter fun s => s ∉ B ∧ (srv s).rq = []).card

lemma exists_le_cnt_iff {α : Type} [DecidableEq α] (Q : Finset (Fin n)) (f : Fin n → α) {k : ℕ}
    (hk : 1 ≤ k) : (∃ a, k ≤ cnt Q f a) ↔ ∃ s ∈ Q, k ≤ cnt Q f (f s) := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨s, hs⟩ : (Q.filter fun s => f s = a).Nonempty := by
      rw [← Finset.card_pos]; unfold cnt at ha; omega
    rw [Finset.mem_filter] at hs
    exact ⟨s, hs.1, hs.2 ▸ ha⟩
  · rintro ⟨s, -, hs⟩; exact ⟨_, hs⟩

lemma exists_le_cnt_some_iff {α : Type} [DecidableEq α] (Q : Finset (Fin n))
    (f : Fin n → Option α) {k : ℕ} (hk : 1 ≤ k) :
    (∃ a, k ≤ cnt Q f (some a)) ↔ ∃ s ∈ Q, (f s).isSome ∧ k ≤ cnt Q f (f s) := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨s, hs⟩ : (Q.filter fun s => f s = some a).Nonempty := by
      rw [← Finset.card_pos]; unfold cnt at ha; omega
    rw [Finset.mem_filter] at hs
    exact ⟨s, hs.1, by simp [hs.2], hs.2 ▸ ha⟩
  · rintro ⟨s, -, h1, hs⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h1
    exact ⟨a, ha ▸ hs⟩

end Podc.StabilizingByzStorage
