import Papers.PODC2019.BayouRevisited.Framework

/-!
# The system model of Section 3: replicas, RB/TOB, fair runs, and the ACT restrictions

* `n` replicas `Fin n`, each a deterministic state machine (`Impl`). A replica reacts to
  *external* events (operation invocations, `RB-deliver`, `TOB-deliver`) and may execute
  *internal* events when they are enabled in its state (Section 3.2.1). Every step receives the
  replica's local clock, which we instantiate by the number of the replica's previous steps
  (a strictly increasing clock; the paper makes no assumption about clocks).
* A step may return values to clients (`Eff.resp`, pairs `(request id, value)`; the request id
  of an invocation is the clock value at the invocation) and `RB-cast`/`TOB-cast` messages.
* A global execution is a sequence of actions `(i, x)`: replica `i` processes the local input `x`.
  Message instances are identified by `(sender, index of the cast at the sender)`; delivering one
  is enabled iff it was cast and not yet delivered by the receiver; `TOB-deliver` additionally
  keeps the `TOB`-delivery sequences of all replicas prefixes of one total order
  (Section 3.2.2).
* Runs (`IsAsyncRun`, `IsStableRun`) are infinite valid executions without crashes satisfying
  fairness and the reliable-delivery properties of Section 3.2.2; these classes are *smaller*
  than the paper's (every one of our runs is a fair run of the paper), which makes the
  impossibility result only stronger.
* `IsACT` collects the implementation restrictions of Section 3.3 that are used:
  invisible reads (1), input-driven processing (2) and op-driven messages (3).
-/

namespace Podc.BayouRevisited

/-- Effects of one atomic step of a replica: responses `(request id, value)` and casts. -/
structure Eff (Msg Val : Type) where
  /-- Responses to clients. -/
  resp : List (ℕ × Val)
  /-- Messages `RB-cast` in this step. -/
  rbCast : List Msg
  /-- Messages `TOB-cast` in this step. -/
  tobCast : List Msg

/-- External events of a replica (Section 3.2.1). The sender of a delivered message is also
passed to the replica (this only enlarges the class of implementations). -/
inductive ExtIn (n : ℕ) (Op Msg : Type)
  | invoke (op : Op) (l : Level)
  | rbDeliver (j : Fin n) (m : Msg)
  | tobDeliver (j : Fin n) (m : Msg)

/-- An implementation: `n` deterministic replicas. Each step gets the replica's id and the
current local clock. Internal events are enabled depending on the state only. -/
structure Impl (n : ℕ) (Op Val : Type) where
  /-- Replica states. -/
  State : Type
  /-- Message payloads. -/
  Msg : Type
  /-- Internal events. -/
  IntEv : Type
  /-- Initial states. -/
  init : Fin n → State
  /-- Reaction to an external event. -/
  ext : Fin n → ℕ → State → ExtIn n Op Msg → State × Eff Msg Val
  /-- Enabledness of internal events. -/
  enabled : Fin n → State → IntEv → Prop
  /-- Effect of an internal event. -/
  int : Fin n → ℕ → State → IntEv → State × Eff Msg Val

/-- The local input processed in one step of a global execution. Deliveries carry the identity
`(sender j, index k)` of the message instance and its payload `m`. -/
inductive LIn (n : ℕ) (Op Msg IntEv : Type)
  | inv (op : Op) (l : Level)
  | rb (j : Fin n) (k : ℕ) (m : Msg)
  | tob (j : Fin n) (k : ℕ) (m : Msg)
  | int (ι : IntEv)

namespace LIn

variable {n : ℕ} {Op Msg IntEv : Type}

/-- The input is an invocation. -/
def IsInv : LIn n Op Msg IntEv → Prop
  | .inv _ _ => True
  | _ => False

/-- The operation of an invocation. -/
def opOf : (x : LIn n Op Msg IntEv) → x.IsInv → Op
  | .inv op _, _ => op

/-- The level of an invocation. -/
def lvlOf : (x : LIn n Op Msg IntEv) → x.IsInv → Level
  | .inv _ l, _ => l

/-- The TOB message identity of a `TOB-deliver` input. -/
def tobId : LIn n Op Msg IntEv → Option (Fin n × ℕ)
  | .tob j k _ => some (j, k)
  | _ => none

end LIn

namespace Impl

variable {n : ℕ} {Op Val : Type} (I : Impl n Op Val)

/-- A state is passive if no internal event is enabled in it (Section 3.3). -/
def Passive (i : Fin n) (σ : I.State) : Prop := ∀ ι, ¬ I.enabled i σ ι

/-- Local inputs of this implementation. -/
abbrev Input := LIn n Op I.Msg I.IntEv

/-- Actions of a global execution. -/
abbrev Act := Fin n × I.Input

/-- One step of replica `i` with clock `c` in state `σ`. -/
def step (i : Fin n) (c : ℕ) (σ : I.State) : I.Input → I.State × Eff I.Msg Val
  | .inv op l => I.ext i c σ (.invoke op l)
  | .rb j _ m => I.ext i c σ (.rbDeliver j m)
  | .tob j _ m => I.ext i c σ (.tobDeliver j m)
  | .int ι => I.int i c σ ι

/-- One step of the local fold: the clock is the number of previous local steps. -/
def lstep (i : Fin n) (p : I.State × List (Eff I.Msg Val)) (x : I.Input) :
    I.State × List (Eff I.Msg Val) :=
  ((I.step i p.2.length p.1 x).1, p.2 ++ [(I.step i p.2.length p.1 x).2])

/-- Running replica `i` on a local input sequence: final state and the effects of every step. -/
def lrun (i : Fin n) (ℓ : List I.Input) : I.State × List (Eff I.Msg Val) :=
  ℓ.foldl (I.lstep i) (I.init i, [])

/-- The state of replica `i` after the local inputs `ℓ`. -/
def lstate (i : Fin n) (ℓ : List I.Input) : I.State := (I.lrun i ℓ).1

/-- The effects of the steps of replica `i` on the local inputs `ℓ`. -/
def leffs (i : Fin n) (ℓ : List I.Input) : List (Eff I.Msg Val) := (I.lrun i ℓ).2

/-- The step of replica `i` on input `x` after the local inputs `ℓ`. -/
def stepAt (i : Fin n) (ℓ : List I.Input) (x : I.Input) : I.State × Eff I.Msg Val :=
  I.step i ℓ.length (I.lstate i ℓ) x

/-- All messages `RB-cast` by `i` (in order) during `ℓ`. -/
def rbCasts (i : Fin n) (ℓ : List I.Input) : List I.Msg := (I.leffs i ℓ).flatMap Eff.rbCast

/-- All messages `TOB-cast` by `i` (in order) during `ℓ`. -/
def tobCasts (i : Fin n) (ℓ : List I.Input) : List I.Msg := (I.leffs i ℓ).flatMap Eff.tobCast

/-- The first response to request `c` given by replica `i` in the steps `c, c+1, …` of `ℓ`. -/
def lresp (i : Fin n) (ℓ : List I.Input) (c : ℕ) : Option Val :=
  ((I.leffs i ℓ).drop c).findSome? fun e => e.resp.lookup c

/-- The local inputs of replica `i` in a global execution. -/
def loc (i : Fin n) (P : List I.Act) : List I.Input :=
  P.filterMap fun a => if a.1 = i then some a.2 else none

/-- The sequence of TOB message identities delivered by `i`. -/
def tobSeq (i : Fin n) (P : List I.Act) : List (Fin n × ℕ) := (I.loc i P).filterMap LIn.tobId

/-- An action is enabled after the finite execution `P` (Section 3.2). -/
def Enabled (S : ACTSpec Op Val) (P : List I.Act) : I.Act → Prop
  | (_, .inv op l) => l ∈ S.lvlmap op
  | (i, .int ι) => I.enabled i (I.lstate i (I.loc i P)) ι
  | (i, .rb j k m) => (I.rbCasts j (I.loc j P))[k]? = some m ∧ ∀ m', LIn.rb j k m' ∉ I.loc i P
  | (i, .tob j k m) => (I.tobCasts j (I.loc j P))[k]? = some m ∧
      (∀ m', LIn.tob j k m' ∉ I.loc i P) ∧
      ∀ i', I.tobSeq i P ++ [(j, k)] <+: I.tobSeq i' P ∨ I.tobSeq i' P <+: I.tobSeq i P ++ [(j, k)]

/-- A valid finite execution: every action is enabled after its prefix. -/
def Valid (S : ACTSpec Op Val) (P : List I.Act) : Prop :=
  ∀ t (h : t < P.length), I.Enabled S (P.take t) P[t]

/-- The prefix of length `t` of an infinite execution. -/
def pre (r : ℕ → I.Act) (t : ℕ) : List I.Act := (List.range t).map r

/-- A valid infinite execution. -/
def ValidRun (S : ACTSpec Op Val) (r : ℕ → I.Act) : Prop := ∀ t, I.Enabled S (I.pre r t) (r t)

/-- Fairness (Section 3.2.3), in a strong form and without crashes: every replica invokes
infinitely many operations and is passive infinitely often (so no internal event stays enabled
forever), and every `RB-cast` message is `RB-delivered` by every replica. -/
structure Fair (r : ℕ → I.Act) : Prop where
  inv_inf : ∀ i N, ∃ t ≥ N, (r t).1 = i ∧ (r t).2.IsInv
  passive_inf : ∀ i N, ∃ t ≥ N, I.Passive i (I.lstate i (I.loc i (I.pre r t)))
  rb_all : ∀ i j k t, k < (I.rbCasts j (I.loc j (I.pre r t))).length →
    ∃ t' m, r t' = (i, .rb j k m)

/-- An asynchronous run: a fair valid infinite execution in which a message `TOB-delivered` by
some replica is `TOB-delivered` by all replicas (Section 3.2.2). -/
def IsAsyncRun (S : ACTSpec Op Val) (r : ℕ → I.Act) : Prop :=
  I.ValidRun S r ∧ I.Fair r ∧
    ∀ i j k m t, r t = (i, .tob j k m) → ∀ i', ∃ t' m', r t' = (i', .tob j k m')

/-- A stable run: an asynchronous run in which, in addition, every `TOB-cast` message is
`TOB-delivered` by every replica (Section 3.2.2). -/
def IsStableRun (S : ACTSpec Op Val) (r : ℕ → I.Act) : Prop :=
  I.IsAsyncRun S r ∧ ∀ i j k t, k < (I.tobCasts j (I.loc j (I.pre r t))).length →
    ∃ t' m, r t' = (i, .tob j k m)

/-- Events of the history of a run: the invocation steps. -/
def Ev (r : ℕ → I.Act) : Type := {t : ℕ // (r t).2.IsInv}

/-- The local index (= clock = request id) of the step `t` at its replica. -/
def lidx (r : ℕ → I.Act) (t : ℕ) : ℕ := (I.loc (r t).1 (I.pre r t)).length

/-- The value returned for the invocation `e` (`none` = pending). -/
noncomputable def rvalOf (r : ℕ → I.Act) (e : I.Ev r) : Option Val :=
  open Classical in
  if h : ∃ T v, I.lresp (r e.1).1 (I.loc (r e.1).1 (I.pre r T)) (I.lidx r e.1) = some v then
    some h.choose_spec.choose
  else none

/-- The history of a run (Section 4.2). Every invocation is its own session (each operation is
issued by a different client; this restricts the runs and only strengthens Theorem 5). -/
noncomputable def history (r : ℕ → I.Act) : History (I.Ev r) Op Val where
  op e := (r e.1).2.opOf e.2
  rval := I.rvalOf r
  rb e₁ e₂ := (I.lresp (r e₁.1).1 (I.loc (r e₁.1).1 (I.pre r e₂.1)) (I.lidx r e₁.1)).isSome
  ss e₁ e₂ := e₁ = e₂
  lvl e := (r e.1).2.lvlOf e.2

/-- The implementation restrictions of Section 3.3 used by Theorem 5.
1. *Invisible reads*: a weak read-only invocation leaves the state unchanged and responds
   immediately (in the invocation step). Whether it may cast messages is left to restriction 3,
   as in the paper.
2. *Input-driven processing*: without external events, a replica executes only finitely many
   internal events (from any reachable state).
3. *Op-driven messages*: a replica casts messages only while it is active since an invocation
   of an operation that is not a weak read-only one. (The paper's literal rule excludes all
   read-only operations; its proof of Theorem 5 lets strong reads cast messages, and so do we:
   this enlarges the class of implementations.)
Restrictions 4 and 5 (highly available weak / non-blocking strong operations) are not needed. -/
structure IsACT (S : ACTSpec Op Val) : Prop where
  invisible_reads : ∀ P, I.Valid S P → ∀ i op, RDT.IsReadOnly S.F op → Level.weak ∈ S.lvlmap op →
    (I.stepAt i (I.loc i P) (.inv op .weak)).1 = I.lstate i (I.loc i P) ∧
    ((I.stepAt i (I.loc i P) (.inv op .weak)).2.resp.lookup (I.loc i P).length).isSome
  input_driven : ∀ P, I.Valid S P → ∀ i (f : ℕ → I.IntEv), ∃ k,
    ¬ I.enabled i (I.lstate i (I.loc i P ++ (List.range k).map fun j => .int (f j))) (f k)
  op_driven : ∀ P, I.Valid S P → ∀ i c e, (I.leffs i (I.loc i P))[c]? = some e →
    (e.rbCast ≠ [] ∨ e.tobCast ≠ []) →
    ∃ s ≤ c, (∃ op l, (I.loc i P)[s]? = some (.inv op l) ∧ ¬ (l = .weak ∧ RDT.IsReadOnly S.F op)) ∧
      ∀ u, s ≤ u → u < c → ¬ I.Passive i (I.lstate i ((I.loc i P).take (u + 1)))

end Impl

end Podc.BayouRevisited
