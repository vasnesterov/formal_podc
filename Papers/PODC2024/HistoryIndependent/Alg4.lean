import Cslib.Computability.Distributed.SharedMemory.SWSRRegister
import Mathlib

/-!
# Algorithm 4: a wait-free quiescent HI SWSR `K`-valued register (definitions)

Algorithm 4 of Attiya, Bender, Farach-Colton, Oshman, Schiller, *History-Independent Concurrent
Objects* (PODC 2024): a single-writer single-reader register with values `Fin K` (the paper's
`{1, …, K}`, here 0-based) and initial value `v₀`, implemented from binary registers
`A[0..K-1]` (initially `A[v₀] = 1`, all others `0`), `B[0..K-1]` (initially `0`) and
`flag[1], flag[2]` (initially `0`). The writer keeps a local variable `last` (`last-val`,
initially `v₀`).

```
Read():                                   Write(v):
 1: flag[1] ← 1                            11: if ∀ j, B[j] = 0 then
 2: for it = 1, 2 do                       12:   if flag[1] = 1 then
 3:   val ← TryRead()                      13:     B[last] ← 1
 4:   if val ≠ ⊥ then goto 7               14:     if flag[2] = 1 or flag[1] = 0 then
 5: for j = 1..K do                        15:       B[last] ← 0
 6:   if B[j] = 1 then val ← j             16: A[v] ← 1
 7: flag[2] ← 1                            17: for j = v-1 .. 1 do A[j] ← 0
 8: for j = 1..K do B[j] ← 0               18: for j = v+1 .. K do A[j] ← 0
 9: flag[1] ← 0; flag[2] ← 0               19: last ← v
10: return val
```

`TryRead()` scans `A` upwards for the first `j` with `A[j] = 1` (returning `⊥` if there is
none), then scans downwards from `j - 1` and returns the smallest index read as `1`.

## Modelling

* Two processes `Proc.w` (writer) and `Proc.r` (reader); `allowed = RWOp.SWSR w r`.
* Base objects `Cell K`: `a j`, `b j`, `f1`, `f2`, all binary registers.
* Local states `Loc K` hold the writer's `last` and program counter `wpc`, and the reader's
  program counter `rpc` (each process only uses its own fields). Program counters are
  *normalized*: each one denotes exactly one pending low-level access (loops are unrolled into
  states carrying the loop index; the exit of a loop goes directly to the state of the next
  access), or the return. The writer's local update of `last` (Line 19) happens with the return.
* The reader's `val` is an `Option (Fin K)` (`none` = `⊥`); a `Read` returns `val.getD v₀`
  (by Lemma 10, `val ≠ ⊥` when it returns, `lemma10`).
* The paper's `flag[2] = 1 or flag[1] = 0` in Line 14 reads `flag[2]` first and only reads
  `flag[1]` if `flag[2] = 0` (short-circuit; as described in the paper's text: "it reads flag[2]
  and then flag[1]"). Similarly the scan of Line 11 stops at the first `B[j] = 1`.

## Files

* `Alg4State` — abstract state with ghost variables, transition function `sstep`, simulation
  (`rel_run`); the ghost state of an execution is `sOf v₀ α`.
* `Alg4Inv`, `Alg4StepR`, `Alg4StepW`, `Alg4Main` — the invariant `Inv` and its preservation
  (`inv_sOf`).
* `Alg4Lin` — the history in terms of the abstract state (`link`), the reads-from assignment
  `rfOf`, the reads-from criterion (`readsFrom`), linearizability (`isLinFun`, `linearizable`).
* `Alg4WaitFree` — `Impl.waitFree_of_potential` (general) and `waitFree`.
* `Alg4Thm` — `lemma34`, `lemma10`, `lemma11`, `mem_quiescent`, `quiescentHI_any`,
  `quiescentHI`, **`theorem12`**, and the non-vacuity check `nonvacuous`.
-/

namespace Cslib.SharedMemory

namespace Alg4

/-- The two processes: the writer and the reader. -/
inductive Proc where
  | w
  | r
  deriving DecidableEq

/-- The base objects (binary registers). -/
inductive Cell (K : ℕ) where
  | a (j : Fin K)
  | b (j : Fin K)
  | f1
  | f2
  deriving DecidableEq

/-- All base objects are binary registers. -/
abbrev Obj (K : ℕ) : Cell K → ObjSpec := fun _ => binaryRegister

/-- The high-level object. -/
abbrev Reg {K : ℕ} (v₀ : Fin K) : ObjSpec := register (Fin K) v₀

/-- Program counter of the reader. -/
inductive RPC (K : ℕ) where
  /-- No pending `Read`. -/
  | idle
  /-- Line 1: about to write `flag[1] ← 1`. -/
  | start
  /-- `TryRead` number `snd + 1`, upward scan, about to read `A[j]`. -/
  | up (snd : Bool) (j : Fin K)
  /-- Downward scan of a `TryRead` with current value `val`, about to read `A[j]` (`j < val`). -/
  | down (val j : Fin K)
  /-- Lines 5-6, about to read `B[j]`, current value `val`. -/
  | bscan (j : Fin K) (val : Option (Fin K))
  /-- Line 7. -/
  | setF2 (val : Option (Fin K))
  /-- Line 8, about to write `B[j] ← 0`. -/
  | clr (j : Fin K) (val : Option (Fin K))
  /-- Line 9, `flag[1] ← 0`. -/
  | resF1 (val : Option (Fin K))
  /-- Line 9, `flag[2] ← 0`. -/
  | resF2 (val : Option (Fin K))
  /-- Line 10, about to return. -/
  | done (val : Option (Fin K))
  deriving DecidableEq

/-- Program counter of the writer (executing `Write(v)`). -/
inductive WPC (K : ℕ) where
  /-- No pending `Write`. -/
  | idle
  /-- Line 11, about to read `B[j]`. -/
  | scanB (v j : Fin K)
  /-- Line 12, about to read `flag[1]`. -/
  | rdF1 (v : Fin K)
  /-- Line 13, about to write `B[last] ← 1`. -/
  | setB (v : Fin K)
  /-- Line 14, about to read `flag[2]`. -/
  | rdF2 (v : Fin K)
  /-- Line 14, about to read `flag[1]`. -/
  | rdF1' (v : Fin K)
  /-- Line 15, about to write `B[last] ← 0`. -/
  | clrB (v : Fin K)
  /-- Line 16, about to write `A[v] ← 1`. -/
  | setA (v : Fin K)
  /-- Line 17, about to write `A[j] ← 0` (`j < v`). -/
  | down (v j : Fin K)
  /-- Line 18, about to write `A[j] ← 0` (`v < j`). -/
  | up (v j : Fin K)
  /-- Line 19, about to return. -/
  | done (v : Fin K)
  deriving DecidableEq

/-- Local states (both processes have one; each uses only its own fields). -/
structure Loc (K : ℕ) where
  /-- The writer's `last-val`. -/
  last : Fin K
  /-- The writer's program counter. -/
  wpc : WPC K
  /-- The reader's program counter. -/
  rpc : RPC K

variable {K : ℕ} [NeZero K]

/-! ### Control flow -/

/-- Reader: `A[j] = 1` found in the upward scan; scan down from `j - 1`. -/
def RPC.found (j : Fin K) : RPC K :=
  if h : j.val = 0 then .setF2 (some j) else .down j ⟨j.val - 1, by have := j.isLt; omega⟩

/-- Reader: `A[j] = 0` read in the upward scan of `TryRead` number `snd + 1`. -/
def RPC.upNext (snd : Bool) (j : Fin K) : RPC K :=
  if h : j.val + 1 < K then .up snd ⟨j.val + 1, h⟩ else if snd then .bscan 0 none else .up true 0

/-- Reader: `A[j] = bit` read in the downward scan with current value `val`. -/
def RPC.downNext (val j : Fin K) (bit : Bool) : RPC K :=
  if h : j.val = 0 then .setF2 (some (if bit then j else val))
  else .down (if bit then j else val) ⟨j.val - 1, by have := j.isLt; omega⟩

/-- Reader: `B[j] = bit` read in Line 6. -/
def RPC.bscanNext (j : Fin K) (val : Option (Fin K)) (bit : Bool) : RPC K :=
  if h : j.val + 1 < K then .bscan ⟨j.val + 1, h⟩ (if bit then some j else val)
  else .setF2 (if bit then some j else val)

/-- Reader: after `B[j] ← 0` in Line 8. -/
def RPC.clrNext (j : Fin K) (val : Option (Fin K)) : RPC K :=
  if h : j.val + 1 < K then .clr ⟨j.val + 1, h⟩ val else .resF1 val

/-- Writer: `B[j] = bit` read in Line 11. -/
def WPC.scanNext (v j : Fin K) (bit : Bool) : WPC K :=
  if bit then .setA v else if h : j.val + 1 < K then .scanB v ⟨j.val + 1, h⟩ else .rdF1 v

/-- Writer: start (or continue) the upward clearing loop of Line 18 at index `j`. -/
def WPC.upFrom (v : Fin K) (j : ℕ) : WPC K := if h : j < K then .up v ⟨j, h⟩ else .done v

/-- Writer: after `A[v] ← 1` (Line 16). -/
def WPC.afterSetA (v : Fin K) : WPC K :=
  if h : v.val = 0 then WPC.upFrom v (v.val + 1)
  else .down v ⟨v.val - 1, by have := v.isLt; omega⟩

/-- Writer: after `A[j] ← 0` in Line 17. -/
def WPC.downNext (v j : Fin K) : WPC K :=
  if h : j.val = 0 then WPC.upFrom v (v.val + 1)
  else .down v ⟨j.val - 1, by have := j.isLt; omega⟩

/-- Writer: after `A[j] ← 0` in Line 18. -/
def WPC.upNext (v j : Fin K) : WPC K := WPC.upFrom v (j.val + 1)

/-! ### The implementation -/

variable (v₀ : Fin K)

/-- The code of the writer. -/
def actW (l : Loc K) : Action (Reg v₀) (Obj K) (Loc K) :=
  match l.wpc with
  | .idle => .ret v₀ l
  | .scanB v j => .access (.b j) RWOp.read (fun x => { l with wpc := WPC.scanNext v j x })
  | .rdF1 v => .access .f1 RWOp.read (fun x => { l with wpc := if x then .setB v else .setA v })
  | .setB v => .access (.b l.last) (RWOp.write true) (fun _ => { l with wpc := .rdF2 v })
  | .rdF2 v => .access .f2 RWOp.read (fun x => { l with wpc := if x then .clrB v else .rdF1' v })
  | .rdF1' v => .access .f1 RWOp.read (fun x => { l with wpc := if x then .setA v else .clrB v })
  | .clrB v => .access (.b l.last) (RWOp.write false) (fun _ => { l with wpc := .setA v })
  | .setA v => .access (.a v) (RWOp.write true) (fun _ => { l with wpc := WPC.afterSetA v })
  | .down v j => .access (.a j) (RWOp.write false) (fun _ => { l with wpc := WPC.downNext v j })
  | .up v j => .access (.a j) (RWOp.write false) (fun _ => { l with wpc := WPC.upNext v j })
  | .done v => .ret v { l with last := v, wpc := .idle }

/-- The code of the reader. -/
def actR (l : Loc K) : Action (Reg v₀) (Obj K) (Loc K) :=
  match l.rpc with
  | .idle => .ret v₀ l
  | .start => .access .f1 (RWOp.write true) (fun _ => { l with rpc := .up false 0 })
  | .up snd j => .access (.a j) RWOp.read
      (fun x => { l with rpc := if x then RPC.found j else RPC.upNext snd j })
  | .down val j => .access (.a j) RWOp.read (fun x => { l with rpc := RPC.downNext val j x })
  | .bscan j val => .access (.b j) RWOp.read (fun x => { l with rpc := RPC.bscanNext j val x })
  | .setF2 val => .access .f2 (RWOp.write true) (fun _ => { l with rpc := .clr 0 val })
  | .clr j val => .access (.b j) (RWOp.write false) (fun _ => { l with rpc := RPC.clrNext j val })
  | .resF1 val => .access .f1 (RWOp.write false) (fun _ => { l with rpc := .resF2 val })
  | .resF2 val => .access .f2 (RWOp.write false) (fun _ => { l with rpc := .done val })
  | .done val => .ret (val.getD v₀) { l with rpc := .idle }

/-- The code. -/
def act : Proc → Loc K → Action (Reg v₀) (Obj K) (Loc K)
  | .w, l => actW v₀ l
  | .r, l => actR v₀ l

/-- Invocations. -/
def invoke : Proc → Loc K → RWOp (Fin K) → Loc K
  | .w, l, .write v => { l with wpc := .scanB v 0 }
  | .r, l, .read => { l with rpc := .start }
  | _, l, _ => l

/-- Initial memory: `A[v₀] = 1`, everything else `0`. -/
def memInit : (i : Cell K) → (Obj K i).State
  | .a j => decide (j = v₀)
  | _ => false

/-- **Algorithm 4.** -/
def alg4 : Impl (Reg v₀) (Obj K) Proc (Loc K) where
  memInit := memInit v₀
  locInit _ := ⟨v₀, .idle, .idle⟩
  invoke := invoke
  act := act v₀
  allowed := RWOp.SWSR Proc.w Proc.r

/-- Configurations of Algorithm 4. -/
abbrev Cfg := Config (Reg v₀) (Obj K) Proc (Loc K)

/-- Labels of executions of Algorithm 4. -/
abbrev Lbl := Label Proc (Reg v₀)

end Alg4

end Cslib.SharedMemory
