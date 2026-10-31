import Papers.PODC2018.JupiterListSpec.Space
import Papers.PODC2018.JupiterListSpec.Spec

/-!
# The client/server system model (Sections 2.1, 3 and 4)

`n` clients `Fin n` and one server; every client is connected to the server by two FIFO
channels (`up c`: client → server, `down c`: server → client). Executions are arbitrary
interleavings of three kinds of events (`Ev`):

* `do c u` — client `c` performs the user operation `u` (local processing: the operation is
  applied locally, gets the identifier `(c, seq)`, and a message is put on `up c`);
* `srv c` — the server takes the first message of `up c`, processes it and puts one message on
  `down j` for every other client `j` (server processing);
* `recv c` — client `c` takes the first message of `down c` and processes it (remote processing).

A protocol (`Proto`) supplies the replica states and the three handlers; Jupiter and CJupiter are
two instances. The configuration also carries ghost state that the replicas never read: the log of
`do` events (`log`), the set of operations known to each client (`know`), and the server order
(`sv`).

Operation identifiers are pairs `(c, seq)`; they double as the list elements (inserted elements
are unique "by attaching replica identifiers and sequence numbers", Section 2.3). The priority of
an insertion is the id of its client (Appendix A).

`genOp` is the client's local generation step. It normalises positions (an out-of-range
`Ins`/`Del` is turned into the equivalent in-range one) before the operation is sent; the
paper's pseudocode sends the user's position unchanged (`genRaw`), which breaks CP1 (see
`cp1_fails` and `Counterexample.lean`).
-/

namespace Podc.JupiterListSpec

/-- Operation identifiers `(cid, seq)`. -/
abbrev Oid (n : ℕ) := Fin n × ℕ

/-- User operations: `Ins(k)` (the element is the fresh identifier), `Del(k)`, `Read`. -/
inductive UOp where
  | ins (k : ℕ)
  | del (k : ℕ)
  | read
  deriving DecidableEq, Repr

variable {n : ℕ}

/-- Local generation with normalised positions: the original operation sent to the server, and
the signature recorded in the `do` event. -/
def genOp (x : Oid n) (u : UOp) (l : List (Oid n)) : LOp (Oid n) × Sig (Oid n) :=
  match u with
  | .ins k => (.ins x (min k l.length) x.1.val, .ins x k)
  | .del k =>
    match l[min k (l.length - 1)]? with
    | some a => (.del a (min k (l.length - 1)), .del (some a) k)
    | none => (.nop, .del none k)
  | .read => (.nop, .read)

/-- Local generation as in the paper's pseudocode: the user's position is sent unchanged. -/
def genRaw (x : Oid n) (u : UOp) (l : List (Oid n)) : LOp (Oid n) × Sig (Oid n) :=
  match u with
  | .ins k => (.ins x k x.1.val, .ins x k)
  | .del k =>
    match l[min k (l.length - 1)]? with
    | some a => (.del a k, .del (some a) k)
    | none => (.nop, .del none k)
  | .read => (.nop, .read)

/-- A client/server replication protocol. -/
structure Proto (n : ℕ) where
  /-- client state -/
  CS : Type
  /-- server state -/
  SS : Type
  /-- messages -/
  Msg : Type
  cinit : CS
  sinit : SS
  /-- the list content of a client -/
  list : CS → List (Oid n)
  /-- the list content of the server -/
  slist : SS → List (Oid n)
  /-- the operation identifier carried by a message -/
  oidOf : Msg → Oid n
  /-- local processing of the original operation `o` with identifier `x` (already applied to the
  list by the system); returns the message for the server -/
  cdo : Fin n → Oid n → LOp (Oid n) → CS → CS × Msg
  /-- remote processing at a client (`none`: the handler gets stuck) -/
  crecv : Fin n → Msg → CS → Option CS
  /-- server processing; returns the message forwarded to the other clients -/
  srecv : Fin n → Msg → SS → Option (SS × Msg)
  oidOf_cdo : ∀ c x o s, oidOf (cdo c x o s).2 = x
  oidOf_srecv : ∀ c m s s' m', srecv c m s = some (s', m') → oidOf m' = oidOf m

/-- Ghost record of a `do` event. -/
structure Rec (n : ℕ) where
  oid : Oid n
  lop : LOp (Oid n)
  ctx : Finset (Oid n)
  sig : Sig (Oid n)
  ret : List (Oid n)

/-- Events of an execution. -/
inductive Ev (n : ℕ) where
  | do (c : Fin n) (u : UOp)
  | srv (c : Fin n)
  | recv (c : Fin n)

/-- Configurations. -/
structure Cfg (P : Proto n) where
  cs : Fin n → P.CS
  ss : P.SS
  up : Fin n → List P.Msg
  down : Fin n → List P.Msg
  seq : Fin n → ℕ
  /-- ghost: the `do` events so far -/
  log : List (Rec n)
  /-- ghost: operations processed by each client -/
  know : Fin n → Finset (Oid n)
  /-- ghost: operations processed by the server, in order -/
  sv : List (Oid n)

namespace Cfg

variable {P : Proto n}

/-- The initial configuration. -/
def init (P : Proto n) : Cfg P where
  cs := fun _ => P.cinit
  ss := P.sinit
  up := fun _ => []
  down := fun _ => []
  seq := fun _ => 0
  log := []
  know := fun _ => ∅
  sv := []

/-- One step; `none` if the event is not enabled or a handler gets stuck. -/
def step (g : Oid n → UOp → List (Oid n) → LOp (Oid n) × Sig (Oid n)) (cfg : Cfg P) :
    Ev n → Option (Cfg P)
  | .do c u =>
    let x : Oid n := (c, cfg.seq c)
    let l := P.list (cfg.cs c)
    let og := g x u l
    let r := P.cdo c x og.1 (cfg.cs c)
    some { cfg with
      cs := Function.update cfg.cs c r.1
      up := Function.update cfg.up c (cfg.up c ++ [r.2])
      seq := Function.update cfg.seq c (cfg.seq c + 1)
      log := cfg.log ++ [⟨x, og.1, cfg.know c, og.2, og.1.apply l⟩]
      know := Function.update cfg.know c (insert x (cfg.know c)) }
  | .srv c =>
    match cfg.up c with
    | [] => none
    | m :: rest =>
      match P.srecv c m cfg.ss with
      | none => none
      | some (s', m') =>
        some { cfg with
          ss := s'
          up := Function.update cfg.up c rest
          down := fun j => if j = c then cfg.down j else cfg.down j ++ [m']
          sv := cfg.sv ++ [P.oidOf m] }
  | .recv c =>
    match cfg.down c with
    | [] => none
    | m :: rest =>
      match P.crecv c m (cfg.cs c) with
      | none => none
      | some s' =>
        some { cfg with
          cs := Function.update cfg.cs c s'
          down := Function.update cfg.down c rest
          know := Function.update cfg.know c (insert (P.oidOf m) (cfg.know c)) }

/-- The configuration reached by a sequence of events (`none` if some event is not enabled). -/
def run (g : Oid n → UOp → List (Oid n) → LOp (Oid n) × Sig (Oid n)) (P : Proto n)
    (es : List (Ev n)) : Option (Cfg P) :=
  es.foldlM (step g) (init P)

/-- The generated operations. -/
def D (cfg : Cfg P) : Finset (Oid n) := (cfg.log.map Rec.oid).toFinset

/-- The abstract execution of a configuration: `H` is the sequence of `do` events, and an event
is visible to a later one iff its operation was known to the later one's replica. -/
def absExec (cfg : Cfg P) : AbsExec (Fin n) (Oid n) where
  H := cfg.log.map fun r => ⟨r.oid.1, r.sig, r.ret⟩
  vis i j := i < j ∧ ∃ ri rj, cfg.log[i]? = some ri ∧ cfg.log[j]? = some rj ∧ ri.oid ∈ rj.ctx

end Cfg

end Podc.JupiterListSpec
