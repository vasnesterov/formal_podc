import Papers.PODC2012.LimitedUseSnapshots.Spec

/-!
# Algorithm 1: the unbounded 2-component max array `UB-MaxArray`

Baïg, Hendler, Milani, Travers, *Long-Lived Snapshots with Polylogarithmic Amortized Step
Complexity* (PODC 2020), Algorithm 1 (Section 3).

## Model

* Asynchronous shared memory with `n` processes `Fin n`, deterministic processes; a crashed
  process is one that stops taking steps (CSLib `Cslib.SharedMemory.Impl`).
* The implemented object is the 2-component max array `maxArrObj` of
  `Podc.LimitedUseSnapshots` (unbounded components): `MaxUpdate(left, v)` is `MAOp.upd0 v`,
  `MaxUpdate(right, v)` is `MAOp.upd1 v`, `MaxScan` is `MAOp.scan`; updates return `(0, 0)`.
* **Base objects are atomic**, as the paper uses them as linearizable black boxes:
  `MR_left`, `MR_right` (`Obj.mrL`, `Obj.mrR`) are atomic unbounded max registers (CSLib
  `maxRegObj`), every `MA_j` (`Obj.ma j`, `j : ℕ`) is an atomic 2-component max array
  (`maxArrObj`; only values `< m` are ever written to it), and `H[i]` (`Obj.help i`) is an atomic
  register holding a pair `(timestamp, view)`.
* `X` is the period of the helping mechanism, `⌊n / log² m⌋` in the paper (lines 23, 25). It is a
  parameter; the correctness results hold for every `X`.
* Every program counter performs exactly one base-object access (or returns); purely local
  computations (lines 13, 14, 19, 20, 23, 25, 27, 29) are folded into the continuations.
  `Collect(H)` reads `H[0], …, H[n-1]` one at a time.

### Reading of lines 23–25

Line 25 reads `else if c mod X = 0`: taken literally, it is executed already for `c = 0`, before
the first collect of line 24, and line 27 then compares with an undefined `h₀`. The text (p. 5–6:
"Otherwise, this is not the first collect …") shows the intent: the second collects happen at
`c = 2X, 3X, …`. We model the intended version, `X < c ∧ c % X = 0` (`afterFail`).
-/

namespace Podc.LongLivedSnapshotsPolylog

open Cslib.SharedMemory
open Podc.LimitedUseSnapshots (maxArrObj MAOp)

/-- Base objects of Algorithm 1. -/
inductive Obj (n : ℕ) where
  /-- `MR_left`. -/
  | mrL
  /-- `MR_right`. -/
  | mrR
  /-- The bounded max array `MA_j`. -/
  | ma (j : ℕ)
  /-- The helping register `H[i]`. -/
  | help (i : Fin n)
  deriving DecidableEq

/-- An entry of the helping array: a timestamp and a view. -/
abbrev HEntry := ℕ × (ℕ × ℕ)

/-- Specifications of the base objects. -/
abbrev objSpec (n : ℕ) : Obj n → ObjSpec
  | .mrL => maxRegObj
  | .mrR => maxRegObj
  | .ma _ => maxArrObj
  | .help _ => register HEntry (0, (0, 0))

/-- The local variables of an instance of `CompScan` that survive a loop iteration: whether the
instance belongs to a `MaxUpdate` (its view is then discarded), the iteration counter `c` and the
first collect `h₀` (`none` before line 24 is executed). -/
structure CS (n : ℕ) where
  upd : Bool
  c : ℕ
  h0 : Option (Fin n → HEntry)
  deriving DecidableEq

/-- Program counters of Algorithm 1 (local variables included).

* `wm s v`: line 4, `WriteMax(MR_s, v)` (`s = false`: left, `true`: right);
* `rdR1 cs`, `rdL cs r1`, `rdR2 cs r1 l`: lines 10, 11, 12;
* `upL cs l r2`, `upR cs l r2`, `scanMA cs l r2`: lines 15, 16, 17 (`h = l / m + r2 / m`);
* `chkL cs l r2 v`, `chkR cs l r2 v`: the two reads of line 18 (`v` = the view of `MA_h`);
* `wH cs v`: lines 20–21 (`v` = the direct view);
* `col cs first k acc`: a collect of `H` (line 24 if `first`, line 26 otherwise), about to read
  `H[k]`, `acc` = entries read so far;
* `retV r`: return `r` (line 2/22/28 for `MaxScan`, line 6 for `MaxUpdate`). -/
inductive PC (n : ℕ) where
  | idle
  | wm (s : Bool) (v : ℕ)
  | rdR1 (cs : CS n)
  | rdL (cs : CS n) (r1 : ℕ)
  | rdR2 (cs : CS n) (r1 l : ℕ)
  | upL (cs : CS n) (l r2 : ℕ)
  | upR (cs : CS n) (l r2 : ℕ)
  | scanMA (cs : CS n) (l r2 : ℕ)
  | chkL (cs : CS n) (l r2 : ℕ) (v : ℕ × ℕ)
  | chkR (cs : CS n) (l r2 : ℕ) (v : ℕ × ℕ)
  | wH (cs : CS n) (v : ℕ × ℕ)
  | col (cs : CS n) (first : Bool) (k : Fin n) (acc : Fin n → HEntry)
  | retV (r : ℕ × ℕ)
  deriving DecidableEq

/-- Local state: the persistent timestamp `ts_i` and the program counter. -/
structure Loc (n : ℕ) where
  ts : ℕ
  pc : PC n
  deriving DecidableEq

variable {n : ℕ}

/-- The index `h` of line 14 (sum of the high-order bits). -/
def idx (m l r2 : ℕ) : ℕ := l / m + r2 / m

/-- What a `CompScan` returns to its operation: the view for `MaxScan`, `(0, 0)` for
`MaxUpdate`. -/
def retOf (cs : CS n) (v : ℕ × ℕ) : PC n := if cs.upd then .retV (0, 0) else .retV v

/-- Lines 23–29 after an unsuccessful iteration (local computation): start the first collect
(line 24), a further collect (line 26), or the next iteration (line 29). -/
def afterFail (X : ℕ) (i : Fin n) (cs : CS n) : PC n :=
  if cs.c = X then .col cs true ⟨0, i.pos⟩ (fun _ => (0, (0, 0)))
  else if X < cs.c ∧ cs.c % X = 0 then .col cs false ⟨0, i.pos⟩ (fun _ => (0, (0, 0)))
  else .rdR1 { cs with c := cs.c + 1 }

/-- Line 27: the view of the first entry `j` whose timestamp grew by at least `2` between the
collects `h₀` and `h₁`. -/
def findHelp (h0 h1 : Fin n → HEntry) : Option (ℕ × ℕ) :=
  ((List.finRange n).find? (fun j => decide ((h0 j).1 + 1 < (h1 j).1))).map (fun j => (h1 j).2)

/-- End of a collect (all entries read): store `h₀` (line 24), or test line 27. -/
def afterCollect (cs : CS n) (first : Bool) (acc : Fin n → HEntry) : PC n :=
  if first then .rdR1 { cs with c := cs.c + 1, h0 := some acc }
  else match cs.h0.bind (fun h0 => findHelp h0 acc) with
    | some v => retOf cs v
    | none => .rdR1 { cs with c := cs.c + 1 }

/-- The start of a `CompScan` (line 8). -/
def csInit (upd : Bool) : CS n := ⟨upd, 0, none⟩

/-- The next action of process `i` (Algorithm 1 with parameters `m` and `X`). -/
def act (m X : ℕ) (i : Fin n) (lc : Loc n) : Action maxArrObj (objSpec n) (Loc n) :=
  match lc.pc with
  | .idle => .ret (0, 0) lc
  | .wm false v => .access .mrL (MaxOp.writeMax v) (fun _ => ⟨lc.ts, .rdR1 (csInit true)⟩)
  | .wm true v => .access .mrR (MaxOp.writeMax v) (fun _ => ⟨lc.ts, .rdR1 (csInit true)⟩)
  | .rdR1 cs => .access .mrR MaxOp.readMax (fun r1 => ⟨lc.ts, .rdL cs r1⟩)
  | .rdL cs r1 => .access .mrL MaxOp.readMax (fun l => ⟨lc.ts, .rdR2 cs r1 l⟩)
  | .rdR2 cs r1 l => .access .mrR MaxOp.readMax (fun r2 =>
      ⟨lc.ts, if r1 / m = r2 / m then .upL cs l r2 else afterFail X i cs⟩)
  | .upL cs l r2 => .access (.ma (idx m l r2)) (MAOp.upd0 (l % m)) (fun _ => ⟨lc.ts, .upR cs l r2⟩)
  | .upR cs l r2 => .access (.ma (idx m l r2)) (MAOp.upd1 (r2 % m))
      (fun _ => ⟨lc.ts, .scanMA cs l r2⟩)
  | .scanMA cs l r2 => .access (.ma (idx m l r2)) MAOp.scan (fun v => ⟨lc.ts, .chkL cs l r2 v⟩)
  | .chkL cs l r2 v => .access .mrL MaxOp.readMax (fun x =>
      ⟨lc.ts, if x / m = l / m then .chkR cs l r2 v else afterFail X i cs⟩)
  | .chkR cs l r2 v => .access .mrR MaxOp.readMax (fun x =>
      ⟨lc.ts, if x / m = r2 / m then
        .wH cs ((l / m) * m + v.1, (r2 / m) * m + v.2) else afterFail X i cs⟩)
  | .wH cs v => .access (.help i) (RWOp.write (lc.ts + 1, v)) (fun _ => ⟨lc.ts + 1, retOf cs v⟩)
  | .col cs first k acc => .access (.help k) RWOp.read (fun e =>
      let acc' := Function.update acc k e
      ⟨lc.ts, if h : k.1 + 1 < n then .col cs first ⟨k.1 + 1, h⟩ acc'
        else afterCollect cs first acc'⟩)
  | .retV r => .ret r ⟨lc.ts, .idle⟩

/-- Initial memory: everything `0`. -/
def memInit : (o : Obj n) → (objSpec n o).State
  | .mrL => (0 : ℕ)
  | .mrR => (0 : ℕ)
  | .ma _ => ((0, 0) : ℕ × ℕ)
  | .help _ => ((0, (0, 0)) : HEntry)

/-- **Algorithm 1** (`UB-MaxArray`) for `n` processes, with `MA_j` of range `m` and helping
period `X`. -/
abbrev alg1 (n m X : ℕ) : Impl maxArrObj (objSpec n) (Fin n) (Loc n) where
  memInit := memInit
  locInit _ := ⟨0, .idle⟩
  invoke _ lc o := match o with
    | .upd0 v => ⟨lc.ts, .wm false v⟩
    | .upd1 v => ⟨lc.ts, .wm true v⟩
    | .scan => ⟨lc.ts, .rdR1 (csInit false)⟩
  act := act m X

end Podc.LongLivedSnapshotsPolylog
