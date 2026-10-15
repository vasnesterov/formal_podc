import Cslib.Computability.Distributed.MessagePassing.Async
import Cslib.Computability.Distributed.SharedMemory.SWMRRegister
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Group.Multiset

/-!
# The algorithm of Figure 1 (Mostéfaoui–Raynal, PODC 2016)

Single-writer multi-reader atomic register in `CAMP_{n,t}[t < n/2]` whose messages carry only a
two-bit type (`WRITE0(v)`, `WRITE1(v)`, `READ()`, `PROCEED()`).

Process `w` is the writer; every other process may read. Local variables of `p_i`:
`history_i` (`hist : ℕ → V`), `w_sync_i[1..n]` (`ws`), `r_sync_i[1..n]` (`rs`); the control
position of the current operation (`phase`: `idle`, waiting at line 3 / 7 / 9); and the pending
`READ()` handlers waiting at line 20 (`tasks`, multiset of `(requester, sn)`, `sn` = the value of
`w_sync_i[i]` saved at line 19).

Atomicity: each block of code between two `wait`s is one atomic transition:
* `invoke (write v)` = lines 1–2, internal action `wret` = lines 3–4;
* `invoke read` = lines 5–6, `r8` = end of the wait of line 7 + line 8, `rret` = lines 9–10;
* receiving `WRITE(b, v)` from `p_j` = lines 11–18 (enabled only when the condition of line 11
  holds; otherwise the message stays in the channel, which is indistinguishable from a handler
  blocked at line 11);
* receiving `READ()` = line 19 (creates a task), internal action `proceed j sn` = lines 20–21;
* receiving `PROCEED()` = line 22.

Bits: `b = wsn mod 2` is `par wsn`.
-/

set_option linter.unusedSectionVars false

namespace Podc.TwoBit

open Cslib.SharedMemory Cslib.AsyncMP

/-- The four message types. `write b v` is `WRITE0(v)` / `WRITE1(v)`. -/
inductive Msg (V : Type) where
  | write (b : Bool) (v : V)
  | read
  | proceed
  deriving DecidableEq

/-- The control information of a message: two bits. -/
def Msg.ctrl {V : Type} : Msg V → Bool × Bool
  | .write b _ => (false, b)
  | .read => (true, false)
  | .proceed => (true, true)

/-- The data carried by a message (only `WRITE` messages carry a value). -/
def Msg.payload {V : Type} : Msg V → Option V
  | .write _ v => some v
  | _ => none

/-- **Theorem 2 (message content).** A message is determined by its two control bits and its data
value: no other control information (sequence numbers, …) is carried. Two of the four message
types carry a value, the other two carry nothing. -/
theorem Msg.ext_ctrl_payload {V : Type} (m m' : Msg V) :
    m = m' ↔ m.ctrl = m'.ctrl ∧ m.payload = m'.payload := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · cases m <;> cases m' <;> simp [Msg.ctrl, Msg.payload]

/-- Control position of the current operation. -/
inductive Phase where
  | idle
  /-- waiting at line 3 (write number `wsn`) -/
  | w3 (wsn : ℕ)
  /-- waiting at line 7 (read request number `rsn`) -/
  | r7 (rsn : ℕ)
  /-- waiting at line 9 (will return `history[sn]`) -/
  | r9 (sn : ℕ)
  deriving DecidableEq

/-- Local state of a process. -/
structure Loc (P V : Type) where
  /-- `history_i` (only indices `0..w_sync_i[i]` are meaningful). -/
  hist : ℕ → V
  /-- `w_sync_i[1..n]`. -/
  ws : P → ℕ
  /-- `r_sync_i[1..n]`. -/
  rs : P → ℕ
  /-- Control position of the current operation. -/
  phase : Phase
  /-- `READ()` handlers waiting at line 20: `(requester, sn)`. -/
  tasks : Multiset (P × ℕ)

/-- Internal actions (continuations after `wait` statements). -/
inductive Act (P : Type) where
  /-- lines 3–4 -/
  | wret
  /-- lines 7–8 -/
  | r8
  /-- lines 9–10 -/
  | rret
  /-- lines 20–21 for the pending `READ()` of `j` with saved `sn` -/
  | proceed (j : P) (sn : ℕ)

/-- The parity bit `wsn mod 2`. -/
def par (k : ℕ) : Bool := decide (k % 2 = 1)

lemma par_eq_iff (a b : ℕ) : par a = par b ↔ a % 2 = b % 2 := by
  simp only [par]
  constructor
  · intro h
    by_cases ha : a % 2 = 1 <;> by_cases hb : b % 2 = 1 <;> simp_all
  · intro h; simp [h]

variable {P V : Type} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- The number of processes `j` satisfying `c j`. -/
def count (c : P → Prop) [DecidablePred c] : ℕ := (Finset.univ.filter c).card

/-- Initial local state. -/
def Loc.init (v₀ : V) : Loc P V := ⟨fun _ => v₀, fun _ => 0, fun _ => 0, .idle, 0⟩

/-- Messages `msg` to all `ℓ` with `c ℓ`. -/
def sendTo (c : P → Prop) [DecidablePred c] (m : Msg V) : Multiset (P × Msg V) :=
  (Finset.univ.filter c).val.map (fun ℓ => (ℓ, m))

/-- Invocations (lines 1–2 and 5–6). -/
def invoke (w : P) (p : P) (o : RWOp V) (l : Loc P V) : Option (Loc P V × Multiset (P × Msg V)) :=
  match o, l.phase with
  | .write v, .idle =>
    if p = w then
      let wsn := l.ws p + 1
      let ws' := Function.update l.ws p wsn
      some ({ l with hist := Function.update l.hist wsn v, ws := ws', phase := .w3 wsn },
        sendTo (fun j => ws' j = wsn - 1) (.write (par wsn) v))
    else none
  | .read, .idle =>
    if p ≠ w then
      let rsn := l.rs p + 1
      some ({ l with rs := Function.update l.rs p rsn, phase := .r7 rsn },
        sendTo (fun j => j ≠ p) .read)
    else none
  | _, _ => none

/-- Internal actions (lines 3–4, 7–8, 9–10, 20–21); `q = n - t` is the quorum size. -/
def internal (q : ℕ) (p : P) (a : Act P) (l : Loc P V) :
    Option (Loc P V × Multiset (P × Msg V) × Option V) :=
  match a, l.phase with
  | .wret, .w3 wsn =>
    if q ≤ count (fun j => l.ws j = wsn) then some ({ l with phase := .idle }, 0, some (l.hist wsn))
    else none
  | .r8, .r7 rsn =>
    if q ≤ count (fun j => l.rs j = rsn) then some ({ l with phase := .r9 (l.ws p) }, 0, none)
    else none
  | .rret, .r9 sn =>
    if q ≤ count (fun j => sn ≤ l.ws j) then some ({ l with phase := .idle }, 0, some (l.hist sn))
    else none
  | .proceed j sn, _ =>
    if (j, sn) ∈ l.tasks ∧ sn ≤ l.ws j then
      some ({ l with tasks := l.tasks.erase (j, sn) }, {(j, .proceed)}, none)
    else none
  | _, _ => none

/-- Message handlers: process `p` receives `m` from `q` (lines 11–18, 19, 22). -/
def receive (p q : P) (m : Msg V) (l : Loc P V) :
    Option (Loc P V × Multiset (P × Msg V) × Option V) :=
  match m with
  | .write b v =>
    if b = par (l.ws q + 1) then
      let wsn := l.ws q + 1
      if wsn = l.ws p + 1 then
        let ws1 := Function.update l.ws p wsn
        some ({ l with hist := Function.update l.hist wsn v, ws := Function.update ws1 q wsn },
          sendTo (fun ℓ => ws1 ℓ = wsn - 1) (.write (par wsn) v), none)
      else if wsn < l.ws p then
        some ({ l with ws := Function.update l.ws q wsn },
          {(q, .write (par (wsn + 1)) (l.hist (wsn + 1)))}, none)
      else some ({ l with ws := Function.update l.ws q wsn }, 0, none)
    else none
  | .read => some ({ l with tasks := l.tasks + {(q, l.ws p)} }, 0, none)
  | .proceed => some ({ l with rs := Function.update l.rs q (l.rs q + 1) }, 0, none)

/-- The algorithm of Figure 1: writer `w`, at most `t` crashes, initial value `v₀`. -/
def alg (w : P) (t : ℕ) (v₀ : V) : Protocol P (register V v₀) (Loc P V) (Msg V) (Act P) where
  init _ := Loc.init v₀
  invoke := invoke w
  internal := internal (Fintype.card P - t)
  receive := receive

end Podc.TwoBit
