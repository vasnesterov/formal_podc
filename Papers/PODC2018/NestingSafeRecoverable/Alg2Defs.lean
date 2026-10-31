import Podc.Computability.Distributed.SharedMemory.NRL.Erase
import Podc.Computability.Distributed.SharedMemory.NRL.Model

/-!
# Algorithm 2 of [ABH18]: a nesting-safe recoverable CAS object — definitions

Attiya, Ben-Baruch, Hendler, *Nesting-Safe Recoverable Linearizability*, PODC 2018,
Algorithm 2, in the NRL model of `Podc/Computability/Distributed/SharedMemory/NRL/Model.lean`.

* the implemented object `casRObj V`: a CAS object over `Option V` (`none` = the paper's
  `null`, the initial value) with operations `CAS(old, new)` (`new : V` is never `null`) and
  `READ`;
* base objects (`Obj`): the CAS object `C` holding pairs `<id, val> : Option P × Option V`
  (initially `<null, null>`, atomic `read` and `cas`) and SRSW registers `R[q][j] : Option V`
  (initially `null`; written only by `j`, read only by `q`);
* program locations `Loc` (one primitive per step, numbered by the lines of the paper):

```
 1: procedure CAS(old,new)                       12: procedure CAS.RECOVER(old, new)
 2:   <id,val> ← C.read()                 c2      13: if C = <p,new> ∨              r13, r14
 3:   if val ≠ old then                   c3            new ∈ {R[p][1..N]} then      rR i, rT i
 4:     return false                      c3      14:   return true                 r14, rT i
 5:   if id ≠ null then                   c3      15: else
 6:     R[id][p] ← val                    c3      16:   proceed from line 2         rR N
 7:   ret ← C.cas(<id,val>, <p,new>)      c7      17: procedure READ.RECOVER()
 8:   return ret                          c8      18: <id,val> ← C                  rd10
 9: procedure READ()                              19: return val                    rd11
10:   <id,val> ← C                        rd10
11:   return val                          rd11
```

The left term of line 13 is evaluated first (`r13`: read `C`, `r14`: test it), then the
registers `R[p][j]` are read one at a time in the order of the list `procs P` of all processes
(`rR i`: read `R[p][procs[i]]`, `rT i`: test it).
-/

namespace Podc.NestingSafeRecoverable.Alg2

open Cslib.SharedMemory Cslib.SharedMemory.NRL

/-- Operations of the implemented CAS object: `CAS(old, new)` and `READ`. -/
inductive CasROp (V : Type) where
  | cas (old : Option V) (new : V)
  | read
  deriving DecidableEq

/-- The implemented object: a compare-and-swap object over `Option V` (`none` is the paper's
`null`), initially `null`. `CAS(old, new)` responds `inl b` (success flag), `READ` responds
`inr val`. The new value of a `CAS` is never `null`. -/
abbrev casRObj (V : Type) [DecidableEq V] : ObjSpec where
  State := Option V
  Op := CasROp V
  Resp := Bool ⊕ Option V
  init := none
  δ q
    | .cas old new => if q = old then (some new, .inl true) else (q, .inl false)
    | .read => (q, .inr q)

/-- Base objects of Algorithm 2: the CAS object `C` and the registers `R[q][j]`. -/
inductive Obj (P : Type) where
  | C
  | R (q j : P)
  deriving DecidableEq

/-- Contents `<id, val>` of `C`. -/
abbrev Cnt (P V : Type) := Option P × Option V

variable {P V : Type} [DecidableEq P] [DecidableEq V]

/-- Specifications of the base objects. -/
abbrev baseT (P V : Type) [DecidableEq P] [DecidableEq V] : Obj P → ObjSpec
  | .C => casObject (Cnt P V) (none, none)
  | .R _ _ => register (Option V) none

/-- Volatile variables: the last content read from `C` (or `<null, r>` for a value `r` read
from a register), or the response of the last `cas`. -/
abbrev Vars (P V : Type) := Cnt P V ⊕ Bool

/-- Program locations (see the module docstring). -/
inductive Loc where
  | c2 | c3 | c7 | c8 | r13 | r14 | rR (i : ℕ) | rT (i : ℕ) | rd10 | rd11
  deriving DecidableEq

/-- All processes, in a fixed order (the loop of line 13). -/
noncomputable def procs (P : Type) [Fintype P] : List P := (Finset.univ : Finset P).toList

variable [Fintype P]

/-- The next action of process `p`. Combinations of an operation with a location of the other
operation are unreachable (the process just stutters). -/
noncomputable def act (p : P) : CasROp V → Loc → Vars P V →
    Act (baseT P V) Loc (Vars P V) (Bool ⊕ Option V)
  | .cas _ _, .c2, _ => .access .C CASOp.read .c3 id
  | .cas old _, .c3, v =>
    match v with
    | .inl (id, val) =>
      if val = old then
        match id with
        | some q => .access (.R q p) (RWOp.write val) .c7 (fun _ => v)
        | none => .internal .c7 v
      else .ret (.inl false)
    | .inr _ => .ret (.inl false)
  | .cas _ new, .c7, v =>
    match v with
    | .inl c => .access .C (CASOp.cas c (some p, some new)) .c8 id
    | .inr _ => .internal .c7 v
  | .cas _ _, .c8, v =>
    match v with
    | .inr b => .ret (.inl b)
    | .inl _ => .internal .c8 v
  | .cas _ _, .r13, _ => .access .C CASOp.read .r14 id
  | .cas _ new, .r14, v =>
    if v = .inl (some p, some new) then .ret (.inl true) else .internal (.rR 0) v
  | .cas _ _, .rR i, v =>
    if h : i < (procs P).length then
      .access (.R p (procs P)[i]) RWOp.read (.rT i) (fun r => .inl (none, r))
    else .internal .c2 v
  | .cas _ new, .rT i, v =>
    if v = .inl (none, some new) then .ret (.inl true) else .internal (.rR (i + 1)) v
  | .read, .rd10, _ => .access .C CASOp.read .rd11 id
  | .read, .rd11, v =>
    match v with
    | .inl (_, val) => .ret (.inr val)
    | .inr _ => .internal .rd11 v
  | _, pc, v => .internal pc v

/-- A dummy value of the volatile variables (their value at invocation and recovery). -/
abbrev v0 : Vars P V := .inr false

/-- Algorithm 2 of [ABH18]: a nesting-safe recoverable CAS object. -/
noncomputable def alg2 (P V : Type) [DecidableEq P] [DecidableEq V] [Fintype P] :
    Alg P (casRObj V) where
  ι := Obj P
  T := baseT P V
  PC := Loc
  V := Vars P V
  start _ o := match o with
    | .cas _ _ => (.c2, v0)
    | .read => (.rd10, v0)
  recover _ o _ := match o with
    | .cas _ _ => (.r13, v0)
    | .read => (.rd10, v0)
  act := act

/-- The `new` argument of a `CAS`. -/
def newOf : CasROp V → Option V
  | .cas _ new => some new
  | .read => none

/-- The environment assumption of [ABH18, §3.2]: every process invokes `CAS` with pairwise
distinct `new` values ("values written to `C` by the same process are distinct") and never
with `old = new`. -/
def Env2 (h : List (Label P (casRObj V))) : Prop :=
  ∀ p, ((opsOf h p).filterMap newOf).Nodup ∧
    ∀ old new, CasROp.cas old new ∈ opsOf h p → old ≠ some new

end Podc.NestingSafeRecoverable.Alg2
