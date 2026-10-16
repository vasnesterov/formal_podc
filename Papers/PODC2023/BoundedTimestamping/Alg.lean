import Papers.PODC2023.BoundedTimestamping.Defs

/-!
# The MTS algorithm (Figures 1 and 2)

The implementation `alg n κ` of an `n`-process MTS from `n` single-bit registers `A[i]`,
`n` LL/SC objects `TS[i]`, `n` LL/SC objects `LookupTable[i]` and one `mod 3δ`-FAI object
`Counter` (Corollary 10 level: the mod-`φ` FAI and the LL/SC objects are atomic base objects).

Every shared-memory operation of the pseudocode is one base-object access; local computation
is folded into the continuations. Process identifiers inside local states are natural numbers
(converted with `Fin.ofNat`). Procedure calls are encoded by program counters and one return
address per procedure (`hret`, `cret`, `enested`): the call graph is
`updateTS → helpUpdateTS, helpSystem, helpActiveCluster`, `helpSystem → helpUpdateTS, isEarlier`,
`isEarlier → helpUpdateTS, helpActiveCluster`, so each procedure has at most one active
instance per process.

**`helpMoveTS` is a coroutine.** Line 23 ("perform `κ` steps from `helpMoveTS()`") executes the
next `κ` shared-memory steps of a *persistent* `helpMoveTS()` call (field `mv`); when a call
finishes, the next step starts a new call. This is the only reading compatible with constant
step complexity and with the proof of Lemma 33 ("only one of these calls can be invoked before
`t`, and a complete `helpMoveTS()` call requires at most `κ · n` steps").

**Lines 70–72 with `⊥` indices** are not specified by the paper. We read "`j ∈ oldCluster` such
that `localTS[j].index` is maximal" as "the `≪`-dominant entry of the old cluster" (the paper's
own words in the proofs of Lemmas 6 and 51), i.e. `⊥` entries first (larger identifier first),
then the largest index; and "`i ∈ activeCluster` with minimal index" as the `≪`-minimal entry;
`min(⊥, 0)` is read as `0`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.BoundedTS

open Cslib.SharedMemory

/-- Return addresses of `helpUpdateTS`: line 4 (`updateTS`), line 15 (`helpSystem`), line 36,
line 38 (`isEarlier`). -/
inductive HRet where
  | U | S | Ex | Ey
  deriving DecidableEq, Repr

/-- Return addresses of `helpActiveCluster`: line 6 (`updateTS`), line 39 (`isEarlier`). -/
inductive CRet where
  | U | E
  deriving DecidableEq, Repr

/-- Program counters of the main control (named after the pseudocode lines). `K s`: `s` more
steps of `helpMoveTS` in the current `helpActiveCluster` call (line 23). -/
inductive PC where
  | idle
  | U2 | U3
  | H9 | H10 | H12 | H13
  | S16 | S19
  | R26 | R29 | R30 | R33
  | K (s : ℕ)
  | E35 | E36 | E37 | E38 | E40 | E41 | E42 | E44 | E45 | E46 | E48 | E50 | E51 | E55 | E56
  | done (r : Option Bool)
  deriving DecidableEq, Repr

/-- Program counters of `helpMoveTS` (Figure 2). -/
inductive MPC where
  | m58 | m59 | m61 (i : ℕ) | m62 | m65 (i : ℕ) | m66 | m73
  deriving DecidableEq, Repr

/-- State of the persistent `helpMoveTS` coroutine: program counter, `localTS`, `c`. -/
structure MoveSt where
  pc : MPC
  loc : List TSVal
  c : ℕ
  deriving DecidableEq, Repr

/-- Local state of a process. -/
structure Loc where
  /-- program counter -/
  pc : PC
  /-- `helpID` (persistent, line 20) -/
  helpID : ℕ
  /-- the `helpMoveTS` coroutine (persistent) -/
  mv : MoveSt
  /-- `ts.flag` of line 2 -/
  uflag : Bool
  /-- `helpUpdateTS`: `id`, iteration, `ts.flag`, `a`, return address -/
  hid : ℕ
  hit : ℕ
  hflag : Bool
  ha : Bool
  hc : ℕ
  hret : HRet
  /-- `helpSystem`: result `c` of the nested `isEarlier` (line 18) -/
  sres : Option Bool
  /-- `isEarlier`: `x`, `y`, `flag`, iteration, `xTS`, `yTS`, `res`, nested in `helpSystem`? -/
  ex : ℕ
  ey : ℕ
  eflag : Bool
  eit : ℕ
  exTS : TSVal
  eyTS : TSVal
  eres : Bool
  enested : Bool
  /-- `conditionalReset`: iteration, `i`, `ts`, `⌊c/δ⌋`; return address of
  `helpActiveCluster` -/
  rit : ℕ
  ri : ℕ
  rts : TSVal
  rk : ℕ
  cret : CRet
  deriving DecidableEq, Repr

section Alg

variable (n κ : ℕ) [NeZero n]

/-- A process identifier from a natural number. -/
def fid (i : ℕ) : Fin n := Fin.ofNat n i

/-- `Counter mod δ` is in the move phase `[η, η + μ - 1]`. -/
def inMove (c : ℕ) : Bool :=
  decide (eta n ≤ c % delta n) && decide (c % delta n ≤ eta n + mu n - 1)

/-- `localTS[i]`. -/
def getL (loc : List TSVal) (i : ℕ) : TSVal := loc.getD i tsInit

/-- The old cluster `(⌊c/δ⌋ - 1) mod 3`. -/
def oldCl (c : ℕ) : ℕ := (c / delta n + 2) % 3

/-- `helpMoveTS` line 64–65: the next index `≥ i` whose local copy is in the old cluster
(a `VL` is executed only for those), or line 66. -/
def next65 (m : MoveSt) (i : ℕ) : MPC :=
  match (List.range' i (n - i)).find? (fun j => decide ((getL m.loc j).cl = oldCl n m.c)) with
  | some j => .m65 j
  | none => .m66

/-- `oldCluster` (line 68). -/
def oldList (m : MoveSt) : List ℕ :=
  (List.range n).filter (fun j => decide ((getL m.loc j).cl = oldCl n m.c))

/-- `activeCluster` (line 67). -/
def actList (m : MoveSt) : List ℕ :=
  (List.range n).filter (fun j => decide ((getL m.loc j).cl = m.c / delta n))

/-- The `≪`-maximal element of a list of indices (line 70). -/
def selMax (loc : List TSVal) (l : List ℕ) : Option ℕ :=
  l.foldl (fun best j => match best with
    | none => some j
    | some b => if less (getL loc b) (getL loc j) b j then some j else some b) none

/-- The `≪`-minimal element of a list of indices (line 71). -/
def selMin (loc : List TSVal) (l : List ℕ) : Option ℕ :=
  l.foldl (fun best j => match best with
    | none => some j
    | some b => if less (getL loc j) (getL loc b) j b then some j else some b) none

/-- The value written by the `SC` of line 73 to `TS[j]` (line 72). -/
def moveVal (m : MoveSt) (j : ℕ) : TSVal :=
  let k := m.c / delta n
  let lj := getL m.loc j
  match lj.idx with
  | none => ⟨k, none, lj.flag, k⟩
  | some _ =>
    let base : ℤ := match selMin m.loc (actList n m) with
      | some i => (getL m.loc i).idx.getD 0
      | none => 0
    ⟨k, some (min base 0 - 1), lj.flag, k⟩

/-- A fresh `helpMoveTS()` call. -/
def fresh (m : MoveSt) : MoveSt := { m with pc := .m58 }

/-- One shared-memory step of the `helpMoveTS` coroutine of process `p`, continuing with
`cont` applied to the new coroutine state. -/
def moveAct (p : Fin n) (m : MoveSt) (cont : MoveSt → Loc) :
    Action (mtsObj n) (Base n) Loc :=
  match m.pc with
  | .m58 => .access (.TS (fid n (n - 1))) (.ll p) fun r =>
      cont { m with loc := m.loc.set (n - 1) r.1, pc := .m59 }
  | .m59 => .access .ctr .read fun c =>
      cont (if inMove n c then
        (if n - 1 = 0 then { m with pc := .m62 } else { m with pc := .m61 0 })
      else fresh m)
  | .m61 i => .access (.TS (fid n i)) (.ll p) fun r =>
      let m' := { m with loc := m.loc.set i r.1 }
      cont (if i + 1 < n - 1 then { m' with pc := .m61 (i + 1) } else { m' with pc := .m62 })
  | .m62 => .access .ctr .read fun c =>
      cont (if inMove n c then
        let m' := { m with c := c }
        { m' with pc := next65 n m' 0 }
      else fresh m)
  | .m65 i => .access (.TS (fid n i)) (.vl p) fun r =>
      cont (if r.2 then { m with pc := next65 n m (i + 1) } else fresh m)
  | .m66 => .access (.TS (fid n (n - 1))) (.vl p) fun r =>
      cont (if r.2 then
        (match selMax m.loc (oldList n m) with
         | some _ => { m with pc := .m73 }
         | none => fresh m)
      else fresh m)
  | .m73 =>
      let j := (selMax m.loc (oldList n m)).getD 0
      .access (.TS (fid n j)) (.sc p (moveVal n m j)) fun _ => cont (fresh m)

/-- Return from `helpActiveCluster`. -/
def retC (l : Loc) : Loc :=
  match l.cret with
  | .U => { l with pc := .done none }
  | .E => { l with pc := .E40 }

/-- After `conditionalReset`: the `κ` steps of `helpMoveTS` (line 23). -/
def startK (l : Loc) : Loc :=
  if κ = 0 then retC l else { l with pc := .K κ }

/-- Call `helpActiveCluster()` (lines 21–22). -/
def callC (l : Loc) (ret : CRet) : Loc := { l with pc := .R26, rit := 0, cret := ret }

/-- Call `helpUpdateTS(id)` (line 7). -/
def callH (l : Loc) (id : ℕ) (ret : HRet) : Loc :=
  { l with pc := .H9, hid := id, hit := 0, hret := ret }

/-- End of `helpSystem` (line 20), then line 6 of `updateTS`. -/
def afterS (l : Loc) : Loc := callC { l with helpID := (l.helpID + 1) % n } .U

/-- Return from `helpUpdateTS`. -/
def retH (l : Loc) : Loc :=
  match l.hret with
  | .U => callH l l.helpID .S
  | .S => { l with pc := .S16 }
  | .Ex => { l with pc := .E37 }
  | .Ey => callC l .E

/-- Return from `isEarlier` with result `r`. -/
def retE (l : Loc) (r : Option Bool) : Loc :=
  if l.enested then { l with pc := .S19, sres := r } else { l with pc := .done r }

/-- The program of process `p` (Figures 1 and 2). -/
def act (p : Fin n) (l : Loc) : Action (mtsObj n) (Base n) Loc :=
  match l.pc with
  | .idle => .ret none l
  | .done r => .ret r { l with pc := .idle }
  -- updateTS
  | .U2 => .access (.TS p) (.ll p) fun r => { l with pc := .U3, uflag := r.1.flag }
  | .U3 => .access (.A p) (.write (!l.uflag)) fun _ => callH l p.val .U
  -- helpUpdateTS(id)
  | .H9 => .access (.TS (fid n l.hid)) (.ll p) fun r => { l with pc := .H10, hflag := r.1.flag }
  | .H10 => .access (.A (fid n l.hid)) .read fun a =>
      if a = l.hflag then retH l else { l with pc := .H12, ha := a }
  | .H12 => .access .ctr .fai fun c =>
      { l with pc := .H13, hc := c }
  | .H13 =>
      let c := l.hc
      .access (.TS (fid n l.hid))
        (.sc p ⟨c / delta n, some (c % delta n : ℕ), l.ha, c / delta n⟩) fun r =>
        if r.2 then retH l
        else if l.hit < 2 then { l with pc := .H9, hit := l.hit + 1 } else retH l
  -- helpSystem (line 15 is the call in `retH`)
  | .S16 => .access (.LT (fid n l.helpID)) (.ll p) fun r =>
      match r.1.res with
      | none => { l with pc := .E35, ex := r.1.x.val, ey := r.1.y.val, enested := true }
      | some _ => afterS n l
  | .S19 => .access (.LT (fid n l.helpID)) (.sc p ⟨fid n l.ex, fid n l.ey, l.sres⟩) fun _ =>
      afterS n l
  -- conditionalReset
  | .R26 => .access .ctr .read fun c =>
      if eta n ≤ c % delta n then startK κ l
      else { l with pc := .R29, ri := c % delta n / zeta n }
  | .R29 => .access (.TS (fid n l.ri)) (.ll p) fun r => { l with pc := .R30, rts := r.1 }
  | .R30 => .access .ctr .read fun c =>
      if eta n ≤ c % delta n then startK κ l
      else if l.rts.inv = c / delta n then startK κ l
      else { l with pc := .R33, rk := c / delta n }
  | .R33 => .access (.TS (fid n l.ri)) (.sc p ⟨l.rts.cl, l.rts.idx, l.rts.flag, l.rk⟩) fun _ =>
      if l.rit = 0 then { l with pc := .R26, rit := 1 } else startK κ l
  -- κ steps of helpMoveTS
  | .K s => moveAct n p l.mv fun m =>
      let l' := { l with mv := m }
      if s ≤ 1 then retC l' else { l' with pc := .K (s - 1) }
  -- isEarlier(x, y)
  | .E35 => .access (.TS (fid n l.ex)) (.ll p) fun r => { l with pc := .E36, eflag := r.1.flag }
  | .E36 => .access (.A (fid n l.ex)) .read fun a =>
      if a ≠ l.eflag then callH l l.ex .Ex else { l with pc := .E37 }
  | .E37 => .access (.TS (fid n l.ey)) (.ll p) fun r => { l with pc := .E38, eflag := r.1.flag }
  | .E38 => .access (.A (fid n l.ey)) .read fun a =>
      if a ≠ l.eflag then callH l l.ey .Ey else callC l .E
  | .E40 => .access (.LT p) (.ll p) fun _ => { l with pc := .E41 }
  | .E41 => .access (.LT p) (.sc p ⟨fid n l.ex, fid n l.ey, none⟩) fun _ => { l with pc := .E42 }
  | .E42 => .access (.LT p) (.ll p) fun _ => { l with pc := .E44, eit := 0 }
  | .E44 => .access (.TS (fid n l.ex)) (.ll p) fun r => { l with pc := .E45, exTS := r.1 }
  | .E45 => .access (.TS (fid n l.ey)) (.ll p) fun r => { l with pc := .E46, eyTS := r.1 }
  | .E46 => .access (.TS (fid n l.ex)) (.vl p) fun r =>
      if r.2 then { l with pc := .E48, eres := less l.exTS l.eyTS l.ex l.ey }
      else { l with pc := .E50 }
  | .E48 => .access (.LT p) (.sc p ⟨fid n l.ex, fid n l.ey, some l.eres⟩) fun _ =>
      retE l (some l.eres)
  | .E50 => .access (.TS (fid n l.ex)) (.ll p) fun r => { l with pc := .E51, exTS := r.1 }
  | .E51 => .access (.TS (fid n l.ey)) (.vl p) fun r =>
      if r.2 then { l with pc := .E48, eres := less l.exTS l.eyTS l.ex l.ey }
      else if l.eit < 5 then { l with pc := .E44, eit := l.eit + 1 } else { l with pc := .E55 }
  | .E55 => .access (.LT p) (.sc p ⟨fid n l.ex, fid n l.ey, some true⟩) fun _ =>
      { l with pc := .E56 }
  | .E56 => .access (.LT p) (.ll p) fun r => retE l r.1.res

/-- Invocation: `updateTS()` starts at line 2, `isEarlier(x, y)` at line 35. -/
def invoke (l : Loc) : MOp n → Loc
  | .upd _ => { l with pc := .U2 }
  | .ie x y => { l with pc := .E35, ex := x.val, ey := y.val, enested := false }

/-- Initial local state. -/
def locInit : Loc where
  pc := .idle
  helpID := 0
  mv := ⟨.m58, List.replicate n tsInit, 0⟩
  uflag := false
  hid := 0
  hit := 0
  hflag := false
  ha := false
  hc := 0
  hret := .U
  sres := none
  ex := 0
  ey := 0
  eflag := false
  eit := 0
  exTS := tsInit
  eyTS := tsInit
  eres := false
  enested := false
  rit := 0
  ri := 0
  rts := tsInit
  rk := 0
  cret := .U

/-- Initial memory: `A[i] = 0`, `TS[i] = (0, ⊥, 0, 2)`, `LookupTable[i] = (0, 0, True)`,
`Counter = 0`, no links. -/
def memInit : (i : Obj n) → (Base n i).State
  | .A _ => false
  | .TS _ => (tsInit, [])
  | .LT _ => (⟨0, 0, some true⟩, [])
  | .ctr => 0

/-- Which operations a process may invoke: `updateTS()` only by itself, and never by process
`n - 1` (whose `TS` entry detects wrap-arounds, Section 4.1.1); `isEarlier` by everyone. -/
def allowedOp (p : Fin n) : MOp n → Prop
  | .upd q => q = p ∧ p.val ≠ n - 1
  | .ie _ _ => True

/-- **The MTS algorithm of Figures 1 and 2** with parameter `κ` (line 23). -/
def alg : Impl (mtsObj n) (Base n) (Fin n) Loc where
  memInit := memInit n
  locInit := fun _ => locInit n
  invoke := fun _ l o => invoke n l o
  act := act n κ
  allowed := allowedOp n

end Alg

end Cslib.SharedMemory.BoundedTS
