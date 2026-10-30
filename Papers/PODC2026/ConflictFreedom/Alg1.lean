import Papers.PODC2026.ConflictFreedom.GCA
import Papers.PODC2026.ConflictFreedom.TraceDomain
import Papers.PODC2026.ConflictFreedom.Progress

/-!
# Algorithm 1: the weakly conflict-free universal construction (definitions)

Kuznetsov, Sutra and Toyos-Marfurt, *Conflict-Freedom as a Progress Condition*, PODC 2026,
Section 4.3.

Algorithm 1 is written as a CSLib implementation `Alg1.impl A n : Impl A (Alg1.base A n) (Fin n)
(Alg1.Loc A n)` of an arbitrary sequential object `A` for `n` processes. The GCA objects
`GCA_r` (`r ≥ 1`) are *flattened*: each is Algorithm 2 run on its own pair of atomic snapshot
objects `Obj.A r`, `Obj.B r` (CSLib has no composition theorem, so we inline the
implementation); `Obj.S j` are the atomic registers `S[j]` (initially `(0, ε)`).

* Commands are triples `(op, i, seq)` (`Cmd A n`); two commands conflict iff their operations do
  (`CmdConflict`), which is the conflict relation of the object `A_c` of the paper.
* Traces are Mazurkiewicz traces of duplicate-free command schedules (`Tr A n`), the GCA domain.
* Local state `Loc`: the phase (`idle`; `readS j best` = reading `S[j]` at line 5, `best` being
  the pair with the largest round read so far; `gca g` = executing `GCA_r.propose` with local
  state `g` of Algorithm 2, `r` the current round; `writeS` = line 13; `done` = line 14), the
  local variables `seq`, `cmd`, `r`, `s` of the paper, and *ghost* variables that never influence
  the behaviour: `hist` (the final local GCA states of the rounds the process has completed),
  `cr` (the commit round of each operation).
* Line 5 reads the `n` registers one at a time (a collect, not a snapshot).
* `ret*(cmd, s)` is `retT s cmd`: the response of `cmd` in the execution of a representative of
  `s` from the initial state (well defined by Lemma 4.1).
-/

namespace Podc.ConflictFreedom

open Cslib.SharedMemory Cslib.Mazurkiewicz Classical

namespace Alg1

variable (A : ObjSpec) (n : ℕ)

/-- Commands `(op, i, seq)`. -/
abbrev Cmd : Type := A.Op × Fin n × ℕ

/-- The sequential specification `A_c` on commands: a command executes its operation. -/
def cmdδ (q : A.State) (c : Cmd A n) : A.State × A.Resp := A.δ q c.1

/-- The conflict relation on commands, inherited from the operations. -/
def CmdConflict : Cmd A n → Cmd A n → Prop := Conflict (cmdδ A n)

instance : Std.Symm (CmdConflict A n) := inferInstanceAs (Std.Symm (Conflict (cmdδ A n)))

/-- Traces of duplicate-free command schedules. -/
abbrev Tr : Type := NTrace (CmdConflict A n)

variable {A n}

lemma cmdConflict_iff (c c' : Cmd A n) : CmdConflict A n c c' ↔ A.Conflicting c.1 c'.1 := Iff.rfl

variable (A n)

/-- Operations of an `n`-component atomic snapshot object over `V`. -/
inductive SnapOp (V : Type) where
  | upd (i : Fin n) (v : V)
  | snap

/-- An `n`-component atomic snapshot object over `V` (components initially `⊥ = none`);
`upd i v` writes `v` into component `i`, `snap` returns all components. -/
abbrev snapSpec (V : Type) : ObjSpec where
  State := Fin n → Option V
  Op := SnapOp n V
  Resp := Fin n → Option V
  init := fun _ => none
  δ q o := match o with
    | .upd i v => (Function.update q i (some v), q)
    | .snap => (q, q)

/-- The base objects: the snapshot objects `A`, `B` of `GCA_r` and the registers `S[j]`. -/
inductive Obj where
  | A (r : ℕ)
  | B (r : ℕ)
  | S (j : Fin n)
  deriving DecidableEq

/-- Specifications of the base objects. -/
abbrev base : Obj n → ObjSpec
  | .A _ => snapSpec n (Tr A n)
  | .B _ => snapSpec n (Tr A n × Bool)
  | .S _ => register (ℕ × Tr A n) (0, ⊥)

/-- Phases of a process. -/
inductive Phase where
  /-- No pending operation. -/
  | idle
  /-- Line 5: about to read `S[j]`; `best` is the pair with the largest round read so far. -/
  | readS (j : ℕ) (best : ℕ × Tr A n)
  /-- Line 11: executing `GCA_r.propose` (Algorithm 2) with local state `g`. -/
  | gca (g : GCA.Loc n (Tr A n))
  /-- Line 13: about to write `S[i] ← (r, s)`. -/
  | writeS
  /-- Line 14: about to return `ret*(cmd, s)`. -/
  | done

/-- Local state of a process. -/
structure Loc where
  /-- The phase. -/
  phase : Phase A n
  /-- The local sequence number. -/
  seq : ℕ
  /-- The command of the current (or last) operation. -/
  cmd : Cmd A n
  /-- The current round. -/
  r : ℕ
  /-- The current trace. -/
  s : Tr A n
  /-- Ghost: the final local GCA state of each completed round. -/
  hist : ℕ → Option (GCA.Loc n (Tr A n))
  /-- Ghost: the round at which the operation with each sequence number committed. -/
  cr : ℕ → ℕ

variable {A n}

/-- The pair with the larger round (line 5). -/
def better (best v : ℕ × Tr A n) : ℕ × Tr A n := if best.1 < v.1 then v else best

/-- Lines 7–11: start round `r₀ + 1`, proposing `t · cmd` (or `t` if `cmd ∈ ops(t)`). -/
noncomputable def Loc.startRound (l : Loc A n) (r₀ : ℕ) (t : Tr A n) : Loc A n :=
  { l with r := r₀ + 1, s := t.snoc l.cmd, phase := .gca (GCA.Loc.init (t.snoc l.cmd)) }

/-- After `GCA_r.propose` returned (final local state `g`): exit the loop (line 6) if the output
is committed and contains `cmd`, otherwise start the next round. The ghost history records `g`. -/
noncomputable def Loc.afterGCA (l : Loc A n) (g : GCA.Loc n (Tr A n)) : Loc A n :=
  if g.output.2 = true ∧ l.cmd ∈ g.output.1.supp then
    { l with hist := Function.update l.hist l.r (some g), s := g.output.1, phase := .writeS,
             cr := Function.update l.cr l.seq l.r }
  else { l.startRound l.r g.output.1 with hist := Function.update l.hist l.r (some g) }

variable [Inhabited A.Resp]

/-- `ret*(c, s)`: the response of command `c` when a representative of `s` is executed from the
initial state. -/
noncomputable def retT (s : Tr A n) (c : Cmd A n) : A.Resp :=
  (respFirst (cmdδ A n) A.init s.rep c).getD default

/-- The next action of process `i` (Algorithm 1 with Algorithm 2 inlined). -/
noncomputable def act (i : Fin n) (l : Loc A n) : Action A (base A n) (Loc A n) :=
  match l.phase with
  | .idle => .ret default l
  | .readS j best =>
    if hj : j < n then
      .access (.S ⟨j, hj⟩) RWOp.read fun v =>
        if j + 1 < n then { l with phase := .readS (j + 1) (better best v) }
        else l.startRound (better best v).1 (better best v).2
    else .ret default l
  | .gca g =>
    match g.pc with
    | 0 => .access (.A l.r) (.upd i g.inp) fun _ => { l with phase := .gca { g with pc := 1 } }
    | 1 => .access (.A l.r) .snap fun v => { l with phase := .gca { g with pc := 2, av := v } }
    | 2 => .access (.B l.r) (.upd i (GCA.candidate g.av, GCA.compatFlag g.av)) fun _ =>
        { l with phase := .gca { g with pc := 3 } }
    | _ => .access (.B l.r) .snap fun v => l.afterGCA { g with pc := 4, bv := v }
  | .writeS => .access (.S i) (RWOp.write (l.r, l.s)) fun _ => { l with phase := .done }
  | .done => .ret (retT l.s l.cmd) { l with phase := .idle }

/-- Lines 2–5: invocation of `op` by process `i`. -/
def invoke (i : Fin n) (l : Loc A n) (o : A.Op) : Loc A n :=
  { l with seq := l.seq + 1, cmd := (o, i, l.seq + 1), phase := .readS 0 (0, ⊥) }

variable [Inhabited A.Op] [NeZero n]

/-- Algorithm 1 (with Algorithm 2 for every `GCA_r`) as a CSLib implementation of `A` for the
processes `Fin n`. -/
noncomputable def impl : Impl A (base A n) (Fin n) (Loc A n) where
  memInit o := match o with
    | .A _ => fun _ => none
    | .B _ => fun _ => none
    | .S _ => ((0 : ℕ), (⊥ : Tr A n))
  locInit _ := ⟨.idle, 0, (default, 0, 0), 0, ⊥, fun _ => none, fun _ => 0⟩
  invoke := invoke
  act := act

end Alg1

end Podc.ConflictFreedom
