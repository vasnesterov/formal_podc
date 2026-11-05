import Mathlib

-- CSLib candidate: nondeterministic read/write shared memory + covering toolkit

/-!
# Nondeterministic read/write shared memory and leader election

The model of Section 5 of Giakkoupis–Woelfel, *On the time and space complexity of randomized
test-and-set* (PODC 2012).

* `P` processes, `Reg` atomic multi-reader multi-writer registers with values in `V` (initial
  values `v₀`).
* A process is a **nondeterministic** automaton with local states `L` (randomized algorithms:
  the coin flips are the nondeterministic choices). Its next action is a function of its local
  state: read a register, write a value to a register, or return (`done true` = it won the
  leader election, `done false` = it lost). After a read of value `v`, the new local state is any
  element of `readNext l v`; after a write, any element of `writeNext l`. Local computation and
  coin flips between two shared-memory steps are folded into these sets; initial local states
  are chosen nondeterministically from `init p` as well.
* An *event* is a pair `(p, l')`: process `p` takes its next step and moves to local state `l'`.
  Executions are lists of events; since an event fixes the nondeterministic choice, the final
  configuration `run C es` of a finite execution is a function. `Valid C es` says that `es` is an
  execution from `C`.
* Every register records its last writer (`Config.wr`), which the processes cannot observe. This
  is the paper's w.l.o.g. assumption "every written value is a pair `(x, ID)`" made ghost: a
  process *sees* `q` when it reads a register whose last writer is `q`.

Leader election (paper, Section 1.1): if some processes call `elect()`, at most one call returns
`True`, and if no process crashes, exactly one call returns `True`. We quantify over the set `S`
of processes that called `elect()`: in every finite execution in which only processes of `S`
take steps, at most one process of `S` has won, and if all of `S` have returned, one of them
has won (`IsLeaderElection`). Nondeterministic solo-termination: from every reachable
configuration every process has a finite solo execution in which it returns (`SoloTerminating`).
-/

namespace Podc.LeaderElectionSpaceLB

/-- The next action of a process. -/
inductive Act (Reg V : Type*) where
  /-- Read register `r`. -/
  | read (r : Reg)
  /-- Write `v` to register `r`. -/
  | write (r : Reg) (v : V)
  /-- Returned from `elect()`: `true` = won, `false` = lost. -/
  | done (win : Bool)

/-- A nondeterministic read/write algorithm for processes `P`, registers `Reg` with values `V`,
and local states `L`. -/
structure Alg (P Reg V L : Type*) where
  /-- Possible initial local states. -/
  init : P → Set L
  init_nonempty : ∀ p, (init p).Nonempty
  /-- Initial register values. -/
  v₀ : Reg → V
  /-- The next action in a local state. -/
  act : L → Act Reg V
  /-- Possible local states after reading value `v`. -/
  readNext : L → V → Set L
  /-- Possible local states after a write. -/
  writeNext : L → Set L

/-- A configuration: local states, register values, and (ghost) last writers. -/
structure Config (P Reg V L : Type*) where
  /-- Local states. -/
  loc : P → L
  /-- Register values. -/
  val : Reg → V
  /-- Last writer of each register (`none`: never written). -/
  wr : Reg → Option P

variable {P Reg V L : Type*} [DecidableEq P] [DecidableEq Reg]

namespace Alg

variable (A : Alg P Reg V L)

/-- `C` is an initial configuration. -/
def IsInit (C : Config P Reg V L) : Prop :=
  (∀ p, C.loc p ∈ A.init p) ∧ (∀ r, C.val r = A.v₀ r) ∧ ∀ r, C.wr r = none

/-- Event `e = (p, l')` is enabled in `C`: `p` has not returned and `l'` is a possible successor
state of its next step. -/
def Enabled (C : Config P Reg V L) (e : P × L) : Prop :=
  match A.act (C.loc e.1) with
  | .read r => e.2 ∈ A.readNext (C.loc e.1) (C.val r)
  | .write _ _ => e.2 ∈ A.writeNext (C.loc e.1)
  | .done _ => False

/-- The configuration after event `e`. -/
def apply (C : Config P Reg V L) (e : P × L) : Config P Reg V L :=
  match A.act (C.loc e.1) with
  | .write r v =>
      { loc := Function.update C.loc e.1 e.2, val := Function.update C.val r v,
        wr := Function.update C.wr r (some e.1) }
  | _ => { C with loc := Function.update C.loc e.1 e.2 }

/-- `es` is an execution from `C`. -/
def Valid : Config P Reg V L → List (P × L) → Prop
  | _, [] => True
  | C, e :: es => A.Enabled C e ∧ Valid (A.apply C e) es

/-- Final configuration of the execution `es` from `C`. -/
def run (C : Config P Reg V L) (es : List (P × L)) : Config P Reg V L :=
  es.foldl A.apply C

/-- `C` is reachable from an initial configuration. -/
def Reachable (C : Config P Reg V L) : Prop :=
  ∃ C₀ es, A.IsInit C₀ ∧ A.Valid C₀ es ∧ A.run C₀ es = C

/-- Process `p` has returned from `elect()` in `C`. -/
def Finished (C : Config P Reg V L) (p : P) : Prop := ∃ b, A.act (C.loc p) = .done b

/-- Process `p` has won the leader election in `C`. -/
def Won (C : Config P Reg V L) (p : P) : Prop := A.act (C.loc p) = .done true

/-- Process `p` covers register `r` in `C`: its next step writes `r`. -/
def Covers (C : Config P Reg V L) (p : P) (r : Reg) : Prop := ∃ v, A.act (C.loc p) = .write r v

/-- In the step `e` from `C`, process `e.1` sees `q`: it reads a register on which `q` is
visible (whose last writer is `q`). -/
def SeesStep (C : Config P Reg V L) (e : P × L) (q : P) : Prop :=
  ∃ r, A.act (C.loc e.1) = .read r ∧ C.wr r = some q

/-- During the execution `es` from `C`, `p` sees `q` (in some step). -/
def SeesIn : Config P Reg V L → List (P × L) → P → P → Prop
  | _, [], _, _ => False
  | C, e :: es, p, q => (e.1 = p ∧ A.SeesStep C e q) ∨ SeesIn (A.apply C e) es p q

/-- The relation `p ↔_E q` of the paper: `p = q`, or during `E` `p` sees `q` or `q` sees `p`. -/
def Aware (C : Config P Reg V L) (es : List (P × L)) (p q : P) : Prop :=
  p = q ∨ A.SeesIn C es p q ∨ A.SeesIn C es q p

/-- `Q` is closed w.r.t. `≡_E`, the transitive closure of `↔_E`: it is a union of
`≡_E`-classes. -/
def Closed (C : Config P Reg V L) (es : List (P × L)) (Q : Set P) : Prop :=
  ∀ p q, Relation.EqvGen (A.Aware C es) p q → (p ∈ Q ↔ q ∈ Q)

/-- During `es` from `C`, some step writes a register in `S`. -/
def WritesIn : Config P Reg V L → List (P × L) → Set Reg → Prop
  | _, [], _ => False
  | C, e :: es, S => (∃ r v, A.act (C.loc e.1) = .write r v ∧ r ∈ S) ∨ WritesIn (A.apply C e) es S

/-- **Leader election** (Section 1.1): for every set `S` of processes that call `elect()` and
every finite execution from an initial configuration in which only processes of `S` take steps,
at most one process of `S` has won, and if no process of `S` crashed (all of them returned), one
of them has won. -/
def IsLeaderElection : Prop :=
  ∀ C₀ es, A.IsInit C₀ → A.Valid C₀ es → ∀ S : Set P, (∀ e ∈ es, e.1 ∈ S) →
    (∀ p ∈ S, ∀ q ∈ S, A.Won (A.run C₀ es) p → A.Won (A.run C₀ es) q → p = q) ∧
    (S.Nonempty → (∀ p ∈ S, A.Finished (A.run C₀ es) p) → ∃ p ∈ S, A.Won (A.run C₀ es) p)

/-- **Nondeterministic solo-termination** [Fich–Herlihy–Shavit]: from every reachable
configuration, every process has a finite solo execution at the end of which it has returned. -/
def SoloTerminating : Prop :=
  ∀ C, A.Reachable C → ∀ p, ∃ es : List (P × L), (∀ e ∈ es, e.1 = p) ∧ A.Valid C es ∧
    A.Finished (A.run C es) p

end Alg

end Podc.LeaderElectionSpaceLB
