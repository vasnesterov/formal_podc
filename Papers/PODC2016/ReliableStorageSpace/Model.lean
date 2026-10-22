import Mathlib

/-!
# Fault-prone shared memory with black-box coded storage (Sections 2 and 4)

Spiegelman, Cassuto, Chockler, Keidar. *Space Bounds for Reliable Storage: Fundamental Limits of Coding.*
PODC 2016 (arXiv 1507.05169v1).

**System (Section 2.1).** Clients `C` access base objects `N` by arbitrary atomic read-modify-write
operations (RMWs). A client *triggers* an RMW on an object; later the RMW *takes effect* on the object
and its response is delivered to the client (event `exec`). A client may have several pending RMWs.
Clients are deterministic state machines; they only act while they have an outstanding high-level
operation (`read` / `write` of the emulated MWMR register).

**Failures and fairness.** Failures are not events: a failure pattern `(Fc, Fo)` (crashed clients,
crashed objects, `|Fo| ≤ f`) only enters fairness (`Alg.Fair`): crashed clients take finitely many
steps, RMWs on crashed objects take effect finitely often, every correct client is scheduled infinitely
often, and every RMW of a correct client on a correct object eventually takes effect.

**Black-box storage model (the paper's "information-theoretic storage model").** Written values are
opaque: write `w = (c, k)` (the `k`-th operation of client `c`) has value `val w` for a value assignment
`val`, and the algorithm never sees it. What the algorithm stores and moves around are *blocks*
`b = (w, j)`: block `j` of the value of `w`, whose contents is the `sz j`-bit string `enc j (val w)`
(`enc` is the algorithm's code, e.g. an erasure code; replication is a block of `D` bits). All control
flow and all metadata are independent of the values. Blocks only flow: an RMW can store blocks the
client holds, a response can carry blocks the object holds, and a writer may create blocks of its own
current write (`Alg.invoke_blk`, `Alg.act_blk`, `Alg.apply_blk`, `Alg.recv_blk`). A read returns
`rdout c l (contents)` where the output may depend only on the contents of the blocks the reader holds
(`Alg.rdout_congr`). Storage is counted in bits of blocks.

This makes precise the paper's assumption (Section 4, after Theorem 1) that "each stored bit is associated
with a particular write". The paper claims this is without loss of generality via Theorem 1; it is not
(see `Coding.lean` and `differencies.md`), so the lower bound is proved for this class of algorithms.
-/

noncomputable section

namespace Podc.ReliableStorageSpace

open Finset Classical

/-- Operations of the emulated register. Values of writes are given by a value assignment, so a write
carries no value. -/
inductive Op
  | write
  | read
  deriving DecidableEq

/-- Operation identifiers: `(c, k)` is the `k`-th operation of client `c`. -/
abbrev OpId (C : Type) := C × ℕ

/-- Code blocks: `(w, j)` is block `j` of the value written by `w`. -/
abbrev Blk (C J : Type) := OpId C × J

/-- What a client does when scheduled. -/
inductive Act (L N R : Type)
  /-- trigger RMW `r` on object `o`, new local state `l` -/
  | trigger (o : N) (r : R) (l : L)
  /-- return from the current operation, new local state `l` -/
  | ret (l : L)
  /-- wait -/
  | idle

/-- An algorithm emulating an MWMR register over fault-prone base objects, in the black-box storage
model. `invoke c k op l`, `act c k op l`: client `c` executing its `k`-th operation `op`. -/
structure Alg (C N J V : Type) where
  /-- client local states -/
  L : Type
  /-- base object states -/
  O : Type
  /-- RMW descriptors -/
  R : Type
  /-- RMW responses -/
  Res : Type
  linit : C → L
  oinit : N → O
  invoke : C → ℕ → Op → L → L
  act : C → ℕ → Op → L → Act L N R
  /-- the atomic RMW: new object state and response -/
  apply : R → O → O × Res
  recv : C → L → N → Res → L
  /-- size in bits of block `j` -/
  sz : J → ℕ
  /-- the code: contents of block `j` of value `v` -/
  enc : (j : J) → V → Fin (2 ^ sz j)
  /-- the value returned by a read, from the contents of the blocks -/
  rdout : C → L → ((b : Blk C J) → Fin (2 ^ sz b.2)) → V
  /-- blocks held in a local state / object state / carried by an RMW / carried by a response -/
  lblk : L → Finset (Blk C J)
  oblk : O → Finset (Blk C J)
  rblk : R → Finset (Blk C J)
  resblk : Res → Finset (Blk C J)
  /-- blocks are non-empty bit strings -/
  sz_pos : ∀ j, 0 < sz j
  linit_blk : ∀ c, lblk (linit c) = ∅
  oinit_blk : ∀ o, oblk (oinit o) = ∅
  /-- a writer may create blocks of its current write -/
  invoke_blk : ∀ c k op l, ∀ b ∈ lblk (invoke c k op l), b ∈ lblk l ∨ (op = .write ∧ b.1 = (c, k))
  act_trigger_blk : ∀ c k op l o r l', act c k op l = .trigger o r l' →
    ∀ b ∈ rblk r ∪ lblk l', b ∈ lblk l ∨ (op = .write ∧ b.1 = (c, k))
  act_ret_blk : ∀ c k op l l', act c k op l = .ret l' → lblk l' ⊆ lblk l
  apply_blk : ∀ r ob, oblk (apply r ob).1 ∪ resblk (apply r ob).2 ⊆ oblk ob ∪ rblk r
  recv_blk : ∀ c l o res, lblk (recv c l o res) ⊆ lblk l ∪ resblk res
  /-- the output of a read depends only on the contents of the blocks the reader holds -/
  rdout_congr : ∀ c l (g g' : (b : Blk C J) → Fin (2 ^ sz b.2)),
    (∀ b ∈ lblk l, g b = g' b) → rdout c l g = rdout c l g'

/-- History labels: invocation / response of operation `(c, k)`. A read's response records its output
as a function of the block contents. -/
inductive Label (C Out : Type)
  | inv (c : C) (k : ℕ) (op : Op)
  | ret (c : C) (k : ℕ) (out : Option Out)

/-- A pending RMW: the `idx`-th RMW of client `cl`, on object `obj`. -/
structure Pend (C N R : Type) where
  cl : C
  idx : ℕ
  obj : N
  rmw : R

/-- Events (chosen by the environment / adversary). Disabled events are no-ops. -/
inductive Event (C : Type)
  /-- client `c` invokes `op` (no-op if `c` has an outstanding operation) -/
  | inv (c : C) (op : Op)
  /-- client `c` is scheduled (no-op if `c` has no outstanding operation) -/
  | step (c : C)
  /-- the `m`-th RMW of `c` takes effect and its response is delivered (no-op if not pending) -/
  | exec (c : C) (m : ℕ)
  | skip

variable {C N J V : Type}

/-- Blocks of write `w` in a set of blocks. -/
def ofW (w : OpId C) (s : Finset (Blk C J)) : Finset (Blk C J) := s.filter (·.1 = w)

/-- `c` takes a step or receives an invocation at time `t`. -/
def ClientEv (ev : ℕ → Event C) (t : ℕ) (c : C) : Prop := ev t = .step c ∨ ∃ op, ev t = .inv c op

namespace Alg

variable (A : Alg C N J V)

/-- Contents of all blocks. -/
abbrev Content := (b : Blk C J) → Fin (2 ^ A.sz b.2)

/-- Block contents under the value assignment `val`. -/
def contents (val : OpId C → V) : A.Content := fun b => A.enc b.2 (val b.1)

/-- Configurations. `cnt c` = number of completed operations of `c` (so the current one is `(c, cnt c)`),
`nrmw c` = number of RMWs triggered by `c`, `pend` = pending RMWs in trigger order, `tick` = number of
`step` events (used for round robin), `hist` = the history. -/
structure Config where
  loc : C → A.L
  obj : N → A.O
  cur : C → Option Op
  cnt : C → ℕ
  nrmw : C → ℕ
  pend : List (Pend C N A.R)
  tick : ℕ
  hist : List (Label C (A.Content → V))

/-- The initial configuration. -/
def init : A.Config where
  loc := A.linit
  obj := A.oinit
  cur := fun _ => none
  cnt := fun _ => 0
  nrmw := fun _ => 0
  pend := []
  tick := 0
  hist := []

/-- The pending RMW `(c, m)`, if any. -/
def findP (X : A.Config) (c : C) (m : ℕ) : Option (Pend C N A.R) :=
  X.pend.find? (fun p => decide (p.cl = c ∧ p.idx = m))

/-- One event. -/
def step (X : A.Config) : Event C → A.Config
  | .inv c op =>
    if X.cur c = none then
      { X with loc := Function.update X.loc c (A.invoke c (X.cnt c) op (X.loc c))
               cur := Function.update X.cur c (some op)
               hist := X.hist ++ [.inv c (X.cnt c) op] }
    else X
  | .step c =>
    match X.cur c with
    | none => { X with tick := X.tick + 1 }
    | some op =>
      match A.act c (X.cnt c) op (X.loc c) with
      | .trigger o r l =>
        { X with loc := Function.update X.loc c l
                 pend := X.pend ++ [⟨c, X.nrmw c, o, r⟩]
                 nrmw := Function.update X.nrmw c (X.nrmw c + 1)
                 tick := X.tick + 1 }
      | .ret l =>
        { X with loc := Function.update X.loc c l
                 cur := Function.update X.cur c none
                 cnt := Function.update X.cnt c (X.cnt c + 1)
                 tick := X.tick + 1
                 hist := X.hist ++
                   [.ret c (X.cnt c) (if op = .read then some (A.rdout c (X.loc c)) else none)] }
      | .idle => { X with tick := X.tick + 1 }
  | .exec c m =>
    match A.findP X c m with
    | none => X
    | some p =>
      { X with obj := Function.update X.obj p.obj (A.apply p.rmw (X.obj p.obj)).1
               loc := Function.update X.loc c
                 (A.recv c (X.loc c) p.obj (A.apply p.rmw (X.obj p.obj)).2)
               pend := X.pend.filter (fun q => !decide (q.cl = c ∧ q.idx = m)) }
  | .skip => X

/-- The configuration after a finite list of events from `X`. -/
def runFrom (X : A.Config) (evs : List (Event C)) : A.Config := evs.foldl A.step X

/-- Configurations of an infinite event sequence: `cfg ev t` is the configuration after `t` events. -/
def cfg (ev : ℕ → Event C) : ℕ → A.Config
  | 0 => A.init
  | t + 1 => A.step (cfg ev t) (ev t)

/-- Reachable configurations. -/
def Reachable (X : A.Config) : Prop := ∃ evs, X = A.runFrom A.init evs

/-! ### Storage -/

/-- Number of bits of a set of blocks. -/
def bits (s : Finset (Blk C J)) : ℕ := ∑ b ∈ s, A.sz b.2

/-- Blocks carried by the pending RMWs of client `c`. -/
def pendBlk (X : A.Config) (c : C) : Finset (Blk C J) :=
  ((X.pend.filter (fun p => decide (p.cl = c))).map (fun p => A.rblk p.rmw)).foldr (· ∪ ·) ∅

/-- Blocks held by client `c`: in its local state or in its pending RMWs. -/
def held (X : A.Config) (c : C) : Finset (Blk C J) :=
  A.lblk (X.loc c) ∪ A.pendBlk X c


/-- Bits stored in the base objects. -/
def objBits [Fintype N] (X : A.Config) : ℕ := ∑ o, A.bits (A.oblk (X.obj o))

/-- Bits of *other* writes' blocks held by clients (copies of data in client memory). -/
def cliBits [Fintype C] (X : A.Config) : ℕ :=
  ∑ c, A.bits ((A.held X c).filter (·.1.1 ≠ c))

/-- The storage: bits in base objects plus copies of other clients' data held by clients
(Observation 1 of the paper needs the latter; see `differencies.md`). -/
def storage [Fintype C] [Fintype N] (X : A.Config) : ℕ := A.objBits X + A.cliBits X

/-- `D = ⌈log₂ |V|⌉`: the size of a value in bits. -/
def D [Fintype V] : ℕ := Nat.clog 2 (Fintype.card V)

/-- `F(t)`: the base objects that store `D` bits of some single write. -/
def Full [Fintype N] [Fintype V] (X : A.Config) : Finset N :=
  univ.filter (fun o => ∃ w, D (V := V) ≤ A.bits (ofW w (A.oblk (X.obj o))))

/-! ### Fairness and liveness -/

/-- The event at time `t` makes an RMW on object `o` take effect. -/
def ExecOn (ev : ℕ → Event C) (t : ℕ) (o : N) : Prop :=
  ∃ c m p, ev t = .exec c m ∧ A.findP (A.cfg ev t) c m = some p ∧ p.obj = o

/-- Fairness of an infinite run w.r.t. the failure pattern `(Fc, Fo)` with at most `f` crashed base
objects (Section 2.1). -/
structure Fair (f : ℕ) (ev : ℕ → Event C) (Fc : Finset C) (Fo : Finset N) : Prop where
  card_le : Fo.card ≤ f
  obj_crash : ∀ o ∈ Fo, ∃ T, ∀ t ≥ T, ¬ A.ExecOn ev t o
  cl_crash : ∀ c ∈ Fc, ∃ T, ∀ t ≥ T, ¬ ClientEv ev t c
  cl_live : ∀ c ∉ Fc, ∀ T, ∃ t ≥ T, ev t = .step c
  rmw_live : ∀ t, ∀ p ∈ (A.cfg ev t).pend, p.cl ∉ Fc → p.obj ∉ Fo →
    ∃ t' ≥ t, p ∉ (A.cfg ev t').pend

/-- `c` returns from an operation at time `t`. -/
def Returns (ev : ℕ → Event C) (t : ℕ) (c : C) : Prop :=
  (A.cfg ev t).cur c ≠ none ∧ (A.cfg ev (t + 1)).cur c = none

/-- Lock-freedom: in every fair run, if a correct client has an outstanding operation at time `t`, then
some operation completes at a time `≥ t`. -/
def LockFree (f : ℕ) : Prop :=
  ∀ ev Fc Fo, A.Fair f ev Fc Fo → ∀ t c, c ∉ Fc → (A.cfg ev t).cur c ≠ none →
    ∃ t' ≥ t, ∃ c', A.Returns ev t' c'

/-! ### Weak regularity -/

variable {A}

/-- `a` precedes `b` in the history `h` (real-time order). -/
def Precedes {Out : Type} (h : List (Label C Out)) (a b : OpId C) : Prop :=
  ∃ i j : ℕ, i < j ∧ (∃ out, h[i]? = some (Label.ret a.1 a.2 out)) ∧
    (∃ op, h[j]? = some (Label.inv b.1 b.2 op))

/-- `a` is a write of `h`. -/
def IsWrite {Out : Type} (h : List (Label C Out)) (a : OpId C) : Prop := .inv a.1 a.2 .write ∈ h

/-- `a` is completed in `h`. -/
def Completed {Out : Type} (h : List (Label C Out)) (a : OpId C) : Prop :=
  ∃ out, .ret a.1 a.2 out ∈ h

/-- Value of the last write of a list of operations, `v₀` if none. -/
def lastVal (v₀ : V) (val : OpId C → V) (l : List (OpId C)) : V := (l.getLast?.map val).getD v₀

variable (A) in
/-- **Weak regularity** (MWRegWeak of Shao et al., Section 2.2): for every finite run, every value
assignment and every completed read `rd`, there is a linearization of the writes and `rd`: a sequence
`L` containing `rd`, all completed writes and possibly some pending ones, respecting real-time order,
in which `rd` returns the value of the last write before it (`v₀` if none). -/
def WeakRegular (v₀ : V) : Prop :=
  ∀ (evs : List (Event C)) (val : OpId C → V) (rd : OpId C) (out : A.Content → V),
    Label.ret rd.1 rd.2 (some out) ∈ (A.runFrom A.init evs).hist →
    let h := (A.runFrom A.init evs).hist
    ∃ L : List (OpId C), L.Nodup ∧ rd ∈ L ∧ (∀ a ∈ L, a ≠ rd → IsWrite h a) ∧
      (∀ a, IsWrite h a → Completed h a → a ∈ L) ∧
      (∀ a ∈ L, ∀ b ∈ L, Precedes h a b → L.idxOf a < L.idxOf b) ∧
      out (A.contents val) = lastVal v₀ val (L.take (L.idxOf rd))

end Alg

end Podc.ReliableStorageSpace

end
