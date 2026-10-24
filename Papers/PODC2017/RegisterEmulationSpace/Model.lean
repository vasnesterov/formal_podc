import Mathlib
import Cslib.Foundations.Data.Nat.Descent

/-!
# Fault-prone shared memory with servers (Section 2 and Appendix A)

Chockler, Spiegelman. *Space Complexity of Fault-Tolerant Register Emulations.* PODC 2017
(arXiv 1705.07212v1).

**System.** Clients `C` access base read/write registers `B` (values `W`, initially `A.winit`); each
register lives on a server, `δ : B → S`. A client *triggers* a low-level read or write on a register;
the operation stays *pending* until a `resp` event applies it to the register (atomically) and delivers
its response (the value for a read, an acknowledgement for a write) to the client. A client may have
several pending operations (also on the same register). Clients are deterministic state machines
(`Alg`): when scheduled (`step c`) a client triggers an operation, returns from its current high-level
operation, or does nothing, depending only on its local state. High-level invocations `inv c op` are
inputs from the environment and are ignored when the client is busy.

Linearizing each base operation at its response is a restriction of the paper's model (where a
pending write may take effect earlier); it only removes runs, so hypotheses quantified over all runs
become weaker and the lower bounds stronger. The paper itself adopts it in the proof (Assumption 1).

**Failures and fairness.** Failures are not events. A failure pattern `(Fc, Fs)` (crashed clients,
crashed servers) only enters fairness (`Alg.Fair`): crashed clients take finitely many steps,
registers on crashed servers respond finitely often, correct clients are scheduled infinitely often,
and every pending operation of a correct client on a register of a correct server eventually responds.
Pending operations of crashed clients may still take effect (as in the paper).

**Correctness conditions.** `Alg.ObstructionFree δ f Wr`: in every fair run with at most `f` crashed
servers in which only the clients in `Wr` (the writers of the emulated `k`-register) invoke writes, a
high-level operation of a correct client that is not concurrent with operations of other correct
clients returns. `Alg.SeqSafe v₀ Wr`: in a *sequential* run (high-level operations never overlap) a
read returns the value of the last write (`v₀` if none). This is implied by the paper's WS-Safety (in a
sequential history every read is a read not concurrent with any write of a write-sequential history),
so the lower bounds assuming only `SeqSafe` are stronger than the paper's.

Everything here is in the paper namespace; it is a CSLib candidate (fault-prone shared memory with
servers, crash-prone base registers).
-/

namespace Podc.RegisterEmulationSpace

/-- Low-level operations on a base register. -/
inductive LOp (W : Type*) where
  | read
  | write (w : W)

/-- `o` is a low-level write. -/
def LOp.IsWrite {W : Type*} : LOp W → Prop
  | .read => False
  | .write _ => True

instance LOp.decIsWrite {W : Type*} (o : LOp W) : Decidable o.IsWrite :=
  match o with
  | .read => isFalse id
  | .write _ => isTrue trivial

@[simp] lemma LOp.isWrite_write {W : Type*} (w : W) : (LOp.write w).IsWrite := trivial
@[simp] lemma LOp.not_isWrite_read {W : Type*} : ¬ (LOp.read : LOp W).IsWrite := id

/-- High-level operations of the emulated register. -/
inductive HOp (V : Type*) where
  | read
  | write (v : V)

/-- What a scheduled client does. -/
inductive Act (B W V : Type*) where
  /-- trigger a low-level operation on a base register -/
  | trig (b : B) (o : LOp W)
  /-- return from the current high-level operation with value `x` (ignored for writes) -/
  | ret (x : V)
  /-- do nothing -/
  | skip

/-- A pending low-level operation: the `n`-th operation triggered by its client. -/
structure POp (B W : Type*) where
  n : ℕ
  reg : B
  op : LOp W

/-- An emulation algorithm: deterministic clients with local states `L`. -/
structure Alg (C B V W L : Type*) where
  /-- initial local states -/
  init : C → L
  /-- initial values of the base registers -/
  winit : B → W
  /-- high-level invocation -/
  invoke : C → HOp V → L → L
  /-- action and new local state of a scheduled client -/
  act : C → L → Act B W V × L
  /-- delivery of the response of a pending operation: the value read, or `none` (write ack) -/
  recv : C → L → POp B W → Option W → L

/-- High-level history events. -/
inductive HEv (C V : Type*) where
  | inv (c : C) (o : HOp V)
  | ret (c : C) (x : V)

/-- Configurations. `cur c` is the pending high-level operation of `c`; `cnt c` counts the
operations triggered by `c` (identifiers of pending operations); `hist` is the high-level history. -/
structure Cfg (C B V W L : Type*) where
  loc : C → L
  val : B → W
  pend : C → List (POp B W)
  cnt : C → ℕ
  cur : C → Option (HOp V)
  hist : List (HEv C V)

/-- Events (actions) of a run. -/
inductive Ev (C V : Type*) where
  /-- the environment invokes a high-level operation at a client -/
  | inv (c : C) (o : HOp V)
  /-- the client takes a step -/
  | step (c : C)
  /-- the pending operation number `n` of client `c` takes effect and responds -/
  | resp (c : C) (n : ℕ)

/-- The event is a step of client `c` or a response to `c`. -/
def Ev.IsOf {C V : Type*} (c : C) : Ev C V → Prop
  | .inv _ _ => False
  | .step c' => c' = c
  | .resp c' _ => c' = c

variable {C B V W L S : Type*}

section Semantics

variable [DecidableEq C] [DecidableEq B] (A : Alg C B V W L)

namespace Alg

/-- The initial configuration. -/
def initCfg : Cfg C B V W L where
  loc := A.init
  val := A.winit
  pend := fun _ => []
  cnt := fun _ => 0
  cur := fun _ => none
  hist := []

/-- Invocation (ignored if the client is busy). -/
def doInv (X : Cfg C B V W L) (c : C) (o : HOp V) : Cfg C B V W L :=
  if X.cur c = none then
    { X with loc := Function.update X.loc c (A.invoke c o (X.loc c)),
             cur := Function.update X.cur c (some o),
             hist := X.hist ++ [.inv c o] }
  else X

/-- A step of client `c`. -/
def doStep (X : Cfg C B V W L) (c : C) : Cfg C B V W L :=
  let X1 : Cfg C B V W L := { X with loc := Function.update X.loc c (A.act c (X.loc c)).2 }
  match (A.act c (X.loc c)).1 with
  | .trig b o => { X1 with pend := Function.update X.pend c (X.pend c ++ [⟨X.cnt c, b, o⟩]),
                           cnt := Function.update X.cnt c (X.cnt c + 1) }
  | .ret x =>
    match X.cur c with
    | some _ => { X1 with cur := Function.update X.cur c none, hist := X.hist ++ [.ret c x] }
    | none => X1
  | .skip => X1

/-- The pending operation `p` of `c` takes effect and responds. -/
def apply (X : Cfg C B V W L) (c : C) (p : POp B W) : Cfg C B V W L :=
  match p.op with
  | .read => { X with pend := Function.update X.pend c ((X.pend c).filter (fun q => q.n ≠ p.n)),
                      loc := Function.update X.loc c (A.recv c (X.loc c) p (some (X.val p.reg))) }
  | .write w => { X with pend := Function.update X.pend c ((X.pend c).filter (fun q => q.n ≠ p.n)),
                         loc := Function.update X.loc c (A.recv c (X.loc c) p none),
                         val := Function.update X.val p.reg w }

/-- Response to the pending operation number `n` of `c` (ignored if there is none). -/
def doResp (X : Cfg C B V W L) (c : C) (n : ℕ) : Cfg C B V W L :=
  match (X.pend c).find? (fun q => q.n = n) with
  | none => X
  | some p => A.apply X c p

/-- The transition function. -/
def step (X : Cfg C B V W L) : Ev C V → Cfg C B V W L
  | .inv c o => A.doInv X c o
  | .step c => A.doStep X c
  | .resp c n => A.doResp X c n

/-- Execution of a finite list of events. -/
def exec (X : Cfg C B V W L) (E : List (Ev C V)) : Cfg C B V W L := E.foldl A.step X

/-- The configuration after a finite run. -/
def run (E : List (Ev C V)) : Cfg C B V W L := A.exec A.initCfg E

/-- The configurations of an infinite run. -/
def traj (ev : ℕ → Ev C V) : ℕ → Cfg C B V W L
  | 0 => A.initCfg
  | t + 1 => A.step (traj ev t) (ev t)

/-- Fairness of an infinite run for the failure pattern `(Fc, Fs)` (Appendix A.4). -/
structure Fair (δ : B → S) (ev : ℕ → Ev C V) (Fc : Set C) (Fs : Set S) : Prop where
  /-- correct clients are scheduled infinitely often -/
  sched : ∀ c ∉ Fc, ∀ t, ∃ t' ≥ t, ev t' = .step c
  /-- crashed clients take finitely many steps and invoke finitely many operations -/
  crashC : ∀ c ∈ Fc, ∃ T, ∀ t ≥ T, ev t ≠ .step c ∧ ∀ o, ev t ≠ .inv c o
  /-- registers on crashed servers respond finitely often -/
  crashS : ∀ s ∈ Fs, ∃ T, ∀ t ≥ T, ∀ c n p, ev t = .resp c n →
    ((A.traj ev t).pend c).find? (fun q => q.n = n) = some p → δ p.reg ≠ s
  /-- every pending operation of a correct client on a correct server eventually responds -/
  live : ∀ t c p, c ∉ Fc → p ∈ (A.traj ev t).pend c → δ p.reg ∉ Fs →
    ∃ t' ≥ t, p ∉ (A.traj ev t').pend c

/-- Only the clients in `Wr` invoke high-level writes. -/
def WritersOnly (Wr : Set C) (ev : ℕ → Ev C V) : Prop :=
  ∀ t c v, ev t = .inv c (.write v) → c ∈ Wr

/-- `f`-tolerant obstruction freedom (Section 2): in every fair run with at most `f` crashed servers
(and writes invoked only by `Wr`), an operation invoked by a correct client `c` that is not concurrent
with any operation of another correct client returns. -/
def ObstructionFree (δ : B → S) (f : ℕ) (Wr : Set C) : Prop :=
  ∀ (ev : ℕ → Ev C V) (Fc : Set C) (Fs : Finset S), Fs.card ≤ f → A.Fair δ ev Fc ↑Fs →
    WritersOnly Wr ev →
    ∀ t c o, c ∉ Fc → ev t = .inv c o → (A.traj ev t).cur c = none →
      (∀ t' > t, ∀ c' ≠ c, c' ∉ Fc → (A.traj ev t').cur c' = none) →
      ∃ t' > t, (A.traj ev t').cur c = none

end Alg

/-- The high-level history of a sequential run with operations `L` (client, operation, returned
value; the value returned by a write is irrelevant). -/
def seqHist : List (C × HOp V × V) → List (HEv C V) :=
  List.flatMap fun e => [.inv e.1 e.2.1, .ret e.1 e.2.2]

/-- The value of the last write in `L`, or `v₀`. -/
def lastVal (v₀ : V) (L : List (C × HOp V × V)) : V :=
  L.foldl (fun acc e => match e.2.1 with | .write v => v | .read => acc) v₀

namespace Alg

/-- Safety in sequential runs: a read returns the value of the last preceding write (`v₀` if none).
Implied by the paper's WS-Safety (Section 2, Appendix A.3), which constrains every read that is not
concurrent with a write in a write-sequential run. -/
def SeqSafe (v₀ : V) (Wr : Set C) : Prop :=
  ∀ (E : List (Ev C V)) (L : List (C × HOp V × V)) (c : C) (x : V),
    (A.run E).hist = seqHist (L ++ [(c, .read, x)]) →
    (∀ e ∈ L, ∀ v, e.2.1 = .write v → e.1 ∈ Wr) → x = lastVal v₀ L

end Alg

open Classical in
/-- Registers covered by a pending low-level write (`Cov(t)` in Section 3.2). -/
noncomputable def Cov [Fintype B] (X : Cfg C B V W L) : Finset B :=
  Finset.univ.filter fun b => ∃ c, ∃ p ∈ X.pend c, p.reg = b ∧ p.op.IsWrite

end Semantics

end Podc.RegisterEmulationSpace
