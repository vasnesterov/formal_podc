import Mathlib

/-!
# Robust atomic storage: the round model (§2 of Dobre–Guerraoui–Majuntke–Suri–Vukolić)

Asynchronous message passing between clients (one writer `w` and readers `Rd`) and a finite set
`Obj` of storage objects, at most `t` of which are malicious (Byzantine). Objects never talk to
each other; they only reply to clients. Clients never receive messages from other clients (the
paper focuses on such runs "without loss of generality"; our model simply has no client-to-client
channel). No data authentication: a malicious object may send arbitrary replies.

**Rounds (Definition 1).** An operation of client `c` is a sequence of rounds. In round `q` the
client sends one message to every object (the message to `s` may depend on `s` and on the replies
received in the earlier rounds). Objects process the messages of a client in FIFO order: an object
that has not yet processed round `q - 1` of `c` processes it first ("the new invocation awaits the
completion of the pending one"). A round may terminate once objects at least `S - t` (`S` the
number of objects) have replied to it; the scheduler decides when (possibly later). This is the
round model of [1] (Abraham et al.), which the paper says its model is equivalent to.

**Protocols** (`Proto`) are deterministic:
* a correct object `s` replies to message `m` from `c` by `reply s log c m`, where `log` is the list
  of messages (with senders) it processed before; every deterministic object automaton is of
  this form (its state is a function of its log);
* `wMsg v views s` is the message of `write(v)` to `s` in the next round, `views` the replies of
  the earlier rounds (one list per round, in arrival order); `rMsg j views s` the same for a read
  of reader `j`; `rRet j views` the value returned by the read after its last round;
* writes take exactly `K` rounds and reads exactly `N` rounds.

**Runs** (`exec`) are finite sequences of events:
* `invW v` / `invR j`: the writer invokes `write(v)` (`v ≠ ⊥`) / reader `j` invokes `read()`;
  every client invokes at most one operation (one-shot clients; the lower-bound runs of the paper
  have this form, and restricting the runs only strengthens the impossibility results);
* `dlv c s`: object `s` processes the next pending round message of `c` and replies; the reply is
  appended to `c`'s replies for its *current* round (late replies of earlier rounds included);
* `nxt c`: `c` terminates its current round (enabled iff at least `S - t` objects have replied to
  it) and starts the next round, or returns after the last round;
* `forge s L`: a malicious object `s ∈ F` overwrites its state with an arbitrary log `L`.
  Afterwards it again replies by `reply`, so malicious behaviour is "behave correctly from a
  forged state", exactly the behaviour used in the paper's proofs (a special case of Byzantine
  behaviour, hence again only a restriction of the runs).

**Atomicity** (`AtomicHist`) is the paper's definition (properties (1)–(4) of §2.2), specialised
to runs with at most one write. `Proto.Atomic P t ⊥` says that every run with any set `F` of at
most `t` malicious objects has an atomic history.
-/

namespace Podc.RobustAtomicStorage

/-- Clients: the single writer and the readers. -/
inductive Cl (Rd : Type) where
  | w : Cl Rd
  | r : Rd → Cl Rd
  deriving DecidableEq

/-- The replies received by a client in one round, in arrival order. -/
abbrev View (Obj Rep : Type) := List (Obj × Rep)

/-- A deterministic round-based implementation of a SWMR register with values `V`, messages
`Msg` and replies `Rep`: writes take `K` rounds, reads `N` rounds. -/
structure Proto (Obj Rd V Msg Rep : Type) where
  /-- number of rounds of a write -/
  K : ℕ
  /-- number of rounds of a read -/
  N : ℕ
  /-- reply of a correct object `s` with log `log` to message `m` of client `c` -/
  reply : Obj → List (Cl Rd × Msg) → Cl Rd → Msg → Rep
  /-- message of `write(v)` to object `s`, given the replies of the earlier rounds -/
  wMsg : V → List (View Obj Rep) → Obj → Msg
  /-- message of a read of reader `j` to object `s`, given the replies of the earlier rounds -/
  rMsg : Rd → List (View Obj Rep) → Obj → Msg
  /-- value returned by a read of reader `j`, given the replies of all its rounds -/
  rRet : Rd → List (View Obj Rep) → V

/-- Events of a run. `L` is the type of object states (logs) a malicious object may forge. -/
inductive Ev (Obj Rd V L : Type) where
  | invW (v : V)
  | invR (j : Rd)
  | dlv (c : Cl Rd) (s : Obj)
  | nxt (c : Cl Rd)
  | forge (s : Obj) (log : L)

/-- Invocation and response events (the history of a run). -/
inductive HEv (Rd V : Type) where
  | invW (v : V)
  | retW
  | invR (j : Rd)
  | retR (j : Rd) (v : V)
  deriving DecidableEq

/-- Configurations. -/
structure Cfg (Obj Rd V Msg Rep : Type) where
  /-- state of each object: the messages it processed (or a forged log) -/
  log : Obj → List (Cl Rd × Msg)
  /-- current round of each client (`0`: not invoked yet) -/
  rnd : Cl Rd → ℕ
  /-- replies of the terminated rounds of the current operation -/
  past : Cl Rd → List (View Obj Rep)
  /-- replies received in the current round -/
  cur : Cl Rd → View Obj Rep
  /-- number of round messages of client `c` that object `s` processed -/
  prc : Obj → Cl Rd → ℕ
  /-- whether the operation of the client has returned -/
  done : Cl Rd → Bool
  /-- the value being written -/
  wv : V

variable {Obj Rd V Msg Rep : Type}

/-- The initial configuration. -/
def Cfg.init (bot : V) : Cfg Obj Rd V Msg Rep where
  log _ := []
  rnd _ := 0
  past _ := []
  cur _ := []
  prc _ _ := 0
  done _ := false
  wv := bot

namespace Proto

variable (P : Proto Obj Rd V Msg Rep)

/-- Number of rounds of the operations of client `c`. -/
def rounds : Cl Rd → ℕ
  | .w => P.K
  | .r _ => P.N

/-- The message of client `c` (with value `v` if `c` is the writer) to `s`, given the views of
the earlier rounds. -/
def msg (v : V) : Cl Rd → List (View Obj Rep) → Obj → Msg
  | .w => P.wMsg v
  | .r j => P.rMsg j

variable [DecidableEq Obj] [DecidableEq Rd] [Fintype Obj] [DecidableEq V]

/-- Object `s` processes the next pending round message of `c`. -/
def deliver (C : Cfg Obj Rd V Msg Rep) (c : Cl Rd) (s : Obj) : Cfg Obj Rd V Msg Rep :=
  let q := C.prc s c + 1
  let m := P.msg C.wv c ((C.past c).take (q - 1)) s
  { C with
    log := Function.update C.log s (C.log s ++ [(c, m)])
    cur := Function.update C.cur c (C.cur c ++ [(s, P.reply s (C.log s) c m)])
    prc := Function.update C.prc s (Function.update (C.prc s) c q) }

/-- Number of objects that replied to the current round of `c`. -/
def _root_.Podc.RobustAtomicStorage.Cfg.nResp (C : Cfg Obj Rd V Msg Rep) (c : Cl Rd) : ℕ :=
  (Finset.univ.filter fun s => C.prc s c = C.rnd c).card

/-- The response event emitted when `c` returns. -/
def retEv (C : Cfg Obj Rd V Msg Rep) : Cl Rd → HEv Rd V
  | .w => .retW
  | .r j => .retR j (P.rRet j (C.past (.r j) ++ [C.cur (.r j)]))

/-- One step, with malicious set `F`, resilience `t`, initial value `bot`. Returns the new
configuration and the emitted history events, or `none` if the event is not enabled. -/
def step (t : ℕ) (F : Finset Obj) (bot : V) (C : Cfg Obj Rd V Msg Rep) :
    Ev Obj Rd V (List (Cl Rd × Msg)) → Option (Cfg Obj Rd V Msg Rep × List (HEv Rd V))
  | .invW v =>
    if C.rnd .w = 0 ∧ v ≠ bot then
      some ({ C with rnd := Function.update C.rnd .w 1, wv := v }, [.invW v])
    else none
  | .invR j =>
    if C.rnd (.r j) = 0 then
      some ({ C with rnd := Function.update C.rnd (.r j) 1 }, [.invR j])
    else none
  | .dlv c s =>
    if C.prc s c < C.rnd c then some (P.deliver C c s, []) else none
  | .nxt c =>
    if 0 < C.rnd c ∧ C.done c = false ∧ Fintype.card Obj ≤ t + C.nResp c then
      if C.rnd c = P.rounds c then
        some ({ C with
          past := Function.update C.past c (C.past c ++ [C.cur c])
          cur := Function.update C.cur c []
          done := Function.update C.done c true }, [P.retEv C c])
      else
        some ({ C with
          past := Function.update C.past c (C.past c ++ [C.cur c])
          cur := Function.update C.cur c []
          rnd := Function.update C.rnd c (C.rnd c + 1) }, [])
    else none
  | .forge s L =>
    if s ∈ F then some ({ C with log := Function.update C.log s L }, []) else none

/-- Execution of a list of events. -/
def exec (t : ℕ) (F : Finset Obj) (bot : V) (C : Cfg Obj Rd V Msg Rep) :
    List (Ev Obj Rd V (List (Cl Rd × Msg))) → Option (Cfg Obj Rd V Msg Rep × List (HEv Rd V))
  | [] => some (C, [])
  | e :: σ =>
    (P.step t F bot C e).bind fun p =>
      (exec t F bot p.1 σ).map fun q => (q.1, p.2 ++ q.2)

end Proto

/-! ### Atomicity (§2.2), for histories with at most one write -/

/-- `a` occurs before `b` in the history `h` (used with `a` a response and `b` an invocation:
"the operation of `a` precedes the operation of `b`"). -/
def Before {Rd V : Type} (h : List (HEv Rd V)) (a b : HEv Rd V) : Prop :=
  ∃ i j : ℕ, i < j ∧ h[i]? = some a ∧ h[j]? = some b

/-- The paper's atomicity (properties (1)–(4) of §2.2) for a history with at most one write
(`val₀ = bot`, `val₁ = v` if `write(v)` is invoked):
1. a read returns `⊥` or the value of an invoked write;
2. a read that succeeds the (complete) write returns its value;
3. a read returning the written value does not precede the write;
4. a read that succeeds a read returning the written value also returns it. -/
structure AtomicHist {Rd V : Type} (bot : V) (h : List (HEv Rd V)) : Prop where
  ret_val : ∀ j x, HEv.retR j x ∈ h → x = bot ∨ HEv.invW x ∈ h
  after_write : ∀ j x v, HEv.retR j x ∈ h → HEv.invW v ∈ h → Before h .retW (.invR j) → x = v
  not_before_write : ∀ j v, v ≠ bot → HEv.retR j v ∈ h → HEv.invW v ∈ h →
    ¬ Before h (.retR j v) (.invW v)
  after_read : ∀ j j' v x, v ≠ bot → HEv.retR j v ∈ h → HEv.invW v ∈ h →
    Before h (.retR j v) (.invR j') → HEv.retR j' x ∈ h → x = v

/-- A protocol is an atomic register implementation tolerating `t` malicious objects (initial
value `bot`) if every run, for every set of at most `t` malicious objects, has an atomic history.
(Wait-freedom is built into the round model: every round may terminate as soon as `S - t` objects
replied, and operations have a fixed number of rounds.) -/
def Proto.Atomic [DecidableEq Obj] [DecidableEq Rd] [Fintype Obj] [DecidableEq V]
    (P : Proto Obj Rd V Msg Rep) (t : ℕ) (bot : V) : Prop :=
  ∀ F : Finset Obj, F.card ≤ t → ∀ σ C h,
    P.exec t F bot (Cfg.init bot) σ = some (C, h) → AtomicHist bot h

end Podc.RobustAtomicStorage
