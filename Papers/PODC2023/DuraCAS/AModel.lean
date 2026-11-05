import Papers.PODC2023.DuraCAS.Spec

/-!
# DuraCAS over atomic durable EC objects (the A-level model)

Appendix A.3 of the full version starts with: "Lines 21 to 24 of `RECOVER()` ensure that
`W.RECOVER()` or `Z.RECOVER()` is executed before any other operation is executed on `W` or `Z`.
Consequently, the durable objects `W` and `Z` behave like atomic EC objects." This file makes the
right-hand side precise, and `Refinement.lean` proves the claim (for the per-process discipline).

An *atomic durable* EC object behaves as follows:
* `ECLL` and `ECSC` are atomic steps; `ECSC(h, s, v)` succeeds iff `seq = s`, and then sets the
  object to `(ŝ, v)` with `ŝ = max(DETECT(h), s) + 1` and `DETECT(h) := ŝ` (this is exactly the
  sequence number DurEC chooses; the abstract `DETECT` value of a handle is `ls h`);
* a call returns in a separate step (`APc.aft`), so the effect of an `ECSC` may precede its return;
* if a process crashes while poised at an `ECSC`, that `ECSC` may stay pending as an *orphan*
  (`Orph`) that may take effect later (`Lbl.orph`) or be dropped (`Lbl.drop`); `RECOVER` of the
  object (lines 22–25) can complete only after the orphan on that object is resolved.
The DuraCAS code is the same as in `Model.lean`; `ECLL` and line-21 steps are as there.
-/

namespace Podc.DuraCAS

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

variable (P K V) in
/-- A pending `ECSC(h, s, v)` on `o` of a crashed process. -/
structure Orph where
  o : Obj K
  h : Hd P
  s : ℕ
  v : V × Bool
  deriving DecidableEq

variable (V) in
/-- A-level program counter: at a line, or just after a call at `pc` returned `r`. -/
inductive APc where
  | at (pc : Pc V)
  | aft (pc : Pc V) (r : Bool)
  deriving DecidableEq

variable (P K V) in
/-- A-level process state. -/
structure APS where
  pc : APc V
  op : Option (OpRec K V)
  orph : Option (Orph P K V)

variable (P K V) in
/-- A-level global state: the EC objects (`Y`), the `DETECT` values of the DurEC handles (`ls`),
the processes, the history. -/
structure AS where
  Y : Obj K → Cell V
  ls : Hd P → ℕ
  ps : P → APS P K V
  hist : List (Ev P K V)
  nid : ℕ

/-- The `ECSC` issued at DuraCAS line `pc` by `p` executing `op` on `k`: object, handle, context,
value (lines 10, 15, 21). -/
def scArgs (p : P) (k : K) (op : Op V) : Pc V → Option (Orph P K V)
  | .cas10 _ z => match op with
    | .cas _ new => some ⟨(k, .Z), (p, .crit), z.1, (new, z.2.2)⟩
    | _ => none
  | .wr15 w => match op with
    | .write v => some ⟨(k, .W), (p, .crit), w.1, (v, !w.2.2)⟩
    | _ => none
  | .tw21 _ zh wh => some ⟨(k, .Z), (p, .cas), zh.1, wh.2⟩
  | _ => none

/-- The object recovered at line `22 + j` of `RECOVER`. -/
def recObj (k : K) (j : Fin 4) : Obj K := (k, if j.val % 2 = 0 then .W else .Z)

/-- An atomic `ECSC(h, s, v)` on `o`: new objects, new `DETECT` values, result. -/
def ecsc (Y : Obj K → Cell V) (ls : Hd P → ℕ) (c : Orph P K V) :
    (Obj K → Cell V) × (Hd P → ℕ) × Bool :=
  if (Y c.o).1 = c.s then
    (Function.update Y c.o (max (ls c.h) c.s + 1, c.v),
     Function.update ls c.h (max (ls c.h) c.s + 1), true)
  else (Y, ls, false)

/-- Apply a continuation to `p`. -/
def AS.next (a : AS P K V) (p : P) (n : Next V) : AS P K V :=
  let st := a.ps p
  match n with
  | .go pc => { a with ps := Function.update a.ps p { st with pc := .at pc } }
  | .ret r =>
    { a with ps := Function.update a.ps p ⟨.at .idle, none, st.orph⟩,
             hist := a.hist ++ [.ret ((st.op.map OpRec.id).getD 0) r (a.ls (p, .crit))] }
  | .rdone =>
    { a with ps := Function.update a.ps p ⟨.at .idle, none, st.orph⟩,
             hist := a.hist ++ [.rdone ((st.op.map OpRec.id).getD 0) (a.ls (p, .crit))] }

/-- Set the A-level program counter of `p`. -/
def AS.setPc (a : AS P K V) (p : P) (pc : APc V) : AS P K V :=
  { a with ps := Function.update a.ps p { a.ps p with pc := pc } }

/-- The next step of a busy process `p` (deterministic). -/
def apstep (a : AS P K V) (p : P) : AS P K V :=
  let st := a.ps p
  match st.op with
  | none => a
  | some r =>
    let k := r.k
    let Wk := a.Y (k, .W)
    let Zk := a.Y (k, .Z)
    match st.pc with
    | .aft pc b => a.next p (afterCall pc b)
    | .at pc =>
      match pc with
      | .idle => a
      | .read => a.next p (.ret (.val Zk.2.1))
      | .cas7 i =>
        match r.op with
        | .cas old new =>
          if Zk.2.1 ≠ old then a.next p (.ret (.ok false))
          else if old = new then a.next p (.ret (.ok true))
          else a.next p (.go (.tw19 (.casT i Zk)))
        | _ => a
      | .wr12 => a.next p (.go (.wr13 Wk))
      | .wr13 w =>
        match r.op with
        | .write v =>
          if Zk.2.1 = v then a.next p (.ret (.ok true))
          else if Zk.2.2 = w.2.2 then a.next p (.go (.wr15 w))
          else a.next p (.go (.tw19 .wr1))
        | _ => a
      | .tw19 ret => a.next p (.go (.tw20 ret Zk))
      | .tw20 ret zh =>
        if zh.2.2 ≠ Wk.2.2 then a.next p (.go (.tw21 ret zh Wk))
        else a.next p (afterTW ret)
      | .recv j => a.next p (afterCall (.recv j) false)
      | c =>
        match scArgs p k r.op c with
        | none => a
        | some x =>
          let e := ecsc a.Y a.ls x
          { a with Y := e.1, ls := e.2.1,
                   ps := Function.update a.ps p { st with pc := .aft c e.2.2 } }

/-- Invocation. -/
def AS.invoke (a : AS P K V) (p : P) (k : K) (op : Op V) : AS P K V :=
  { a with ps := Function.update a.ps p ⟨.at (firstPc op), some ⟨a.nid, k, op, a.ls (p, .crit)⟩,
              (a.ps p).orph⟩,
           hist := a.hist ++ [.inv a.nid p k op (a.ls (p, .crit))],
           nid := a.nid + 1 }

/-- Crash of `p`; if `b` and `p` is poised at an `ECSC`, that `ECSC` becomes an orphan. -/
def AS.crash (a : AS P K V) (p : P) (b : Bool) : AS P K V :=
  let st := a.ps p
  let new : Option (Orph P K V) :=
    match b, st.pc, st.op with
    | true, .at c, some r => scArgs p r.k r.op c
    | _, _, _ => none
  { a with ps := Function.update a.ps p ⟨.at (.recv 0), st.op, new.orElse fun _ => st.orph⟩,
           hist := a.hist ++ [.crash p] }

/-- The orphan of `p` takes effect. -/
def AS.orphEff (a : AS P K V) (p : P) : AS P K V :=
  match (a.ps p).orph with
  | none => a
  | some x =>
    let e := ecsc a.Y a.ls x
    { a with Y := e.1, ls := e.2.1, ps := Function.update a.ps p { a.ps p with orph := none } }

/-- The orphan of `p` is dropped (it never takes effect). -/
def AS.drop (a : AS P K V) (p : P) : AS P K V :=
  { a with ps := Function.update a.ps p { a.ps p with orph := none } }

variable (P K V) in
/-- A-level transition labels. -/
inductive ALbl where
  | step (p : P)
  | invoke (p : P) (k : K) (op : Op V)
  | crash (p : P) (b : Bool)
  | orph (p : P)
  | drop (p : P)

/-- Enabledness of A-level transitions. A `RECOVER` of an object completes only when the orphan of
`p` (if any) is not on that object. An orphan takes effect only if its `ECSC` succeeds. -/
def ALbl.En (a : AS P K V) : ALbl P K V → Prop
  | .step p => ∃ r, (a.ps p).op = some r ∧
      ∀ j, (a.ps p).pc = .at (.recv j) → ∀ x, (a.ps p).orph = some x → x.o ≠ recObj r.k j
  | .invoke p _ _ => (a.ps p).op = none
  | .crash p _ => (a.ps p).op.isSome
  | .orph p => ∃ x, (a.ps p).orph = some x ∧ (a.Y x.o).1 = x.s
  | .drop p => (a.ps p).orph.isSome

/-- Effect of A-level transitions. -/
def ALbl.apply (a : AS P K V) : ALbl P K V → AS P K V
  | .step p => apstep a p
  | .invoke p k op => a.invoke p k op
  | .crash p b => a.crash p b
  | .orph p => a.orphEff p
  | .drop p => a.drop p

/-- A-level initial state. -/
def ainit (init : K → V) : AS P K V where
  Y := fun o => (0, (init o.1, false))
  ls := fun _ => 0
  ps := fun _ => ⟨.at .idle, none, none⟩
  hist := []
  nid := 0

/-- One A-level step. -/
def AStep (a a' : AS P K V) : Prop := ∃ ℓ : ALbl P K V, ℓ.En a ∧ a' = ℓ.apply a

/-- A-level reachable states. -/
def AReach (init : K → V) : AS P K V → Prop := Relation.ReflTransGen AStep (ainit init)

end Podc.DuraCAS
