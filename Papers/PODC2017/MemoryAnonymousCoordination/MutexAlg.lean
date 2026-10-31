import Podc.Computability.Distributed.SharedMemory.Unnamed
import Cslib.Computability.Distributed.SharedMemory.Mutex

/-!
# Figure 1 of Taubenfeld, *Coordination Without Prior Agreement* (PODC 2017): the algorithm

A memory-anonymous symmetric deadlock-free mutual exclusion algorithm for two processes with `m`
registers (`m` odd, `m ≥ 3`):

```
Code of process i
Shared: p.i[1..m]: atomic registers, initially 0
1  repeat
2    for j = 1 to m do if p.i[j] = 0 then p.i[j] := i fi od
3    for j = 1 to m do myview[j] := p.i[j] od
4    if i appears in less than ⌈m/2⌉ of the entries of myview[1..m] then
5      for j = 1 to m do if p.i[j] = i then p.i[j] := 0 fi od
6      repeat
7        for j = 1 to m do myview[j] := p.i[j] od
8      until ∀ j : myview[j] = 0
9    fi
10 until ∀ j : myview[j] = i
11 critical section
12 for j = 1 to m do p.i[j] := 0 od
```

## Modelling

* Registers hold `Option P`: `none` is `0`, `some q` is the identifier of `q`.
* Granularity: every shared-memory access is one atomic step. In particular line 2 and line 5
  are a *read* followed (if the test succeeds) by a *separate write* step to the same register
  (`scan j` / `scanW j`, `rst j` / `rstW j`); every read of the collects of lines 3 and 7 is one
  step; line 12 (`unlock`) is `m` unconditional writes of `0`. `lock()` returns when the test of
  line 10 succeeds; the critical section is the time between the response of `lock()` and the
  invocation of `unlock()`.
* The view `myview` of line 3 is kept as the list `vs` of the values read so far
  (`coll vs`, about to read local register `vs.length`). The wait loop of lines 6–8 only keeps the
  flag `z` "all values read so far in this pass were `0`" (`wait j z`). The tests of lines 4, 8
  and 10 are folded into the continuation of the last read of the corresponding loop. After the
  wait loop the test of line 10 fails (the view is all `0`), so the process restarts at line 2.
* Positions are natural numbers `j < m` (an invariant), the access to local register `j` is the
  access to physical register `π p ⟨j, _⟩` of `Impl.unnamed`.
* The code of process `p` only uses `some p` (to write it and to compare register values with it),
  so the algorithm is symmetric in the sense of the paper.
-/

namespace Podc.MemoryAnonymousCoordination.Mutex

open Cslib.SharedMemory

/-- Local state (program counter and the relevant local variables) of a process. -/
inductive Loc (P : Type) where
  /-- remainder section -/
  | rem
  /-- line 2: read `p.i[j]` -/
  | scan (j : ℕ)
  /-- line 2: write `i` to `p.i[j]` (after reading `0`) -/
  | scanW (j : ℕ)
  /-- line 3: read `p.i[vs.length]`; `vs` are the values read so far -/
  | coll (vs : List (Option P))
  /-- line 5: read `p.i[j]` -/
  | rst (j : ℕ)
  /-- line 5: write `0` to `p.i[j]` (after reading `i`) -/
  | rstW (j : ℕ)
  /-- line 7: read `p.i[j]`; `z`: all values read so far in this pass were `0` -/
  | wait (j : ℕ) (z : Bool)
  /-- `lock()` returns -/
  | retLock
  /-- critical section -/
  | cs
  /-- line 12: write `0` to `p.i[j]` -/
  | exit (j : ℕ)
  /-- `unlock()` returns -/
  | retUnlock
  deriving DecidableEq

variable {P : Type}

/-- The threshold `⌈m/2⌉` of line 4. -/
def thr (m : ℕ) : ℕ := (m + 1) / 2

/-- Continue line 2 after position `j` (or start the collect of line 3). -/
def nextScan (m j : ℕ) : Loc P := if j + 1 < m then .scan (j + 1) else .coll []

/-- Continue line 5 after position `j` (or start waiting, line 6). -/
def nextRst (m j : ℕ) : Loc P := if j + 1 < m then .rst (j + 1) else .wait 0 true

/-- Continue line 12 after position `j` (or return from `unlock()`). -/
def nextExit (m j : ℕ) : Loc P := if j + 1 < m then .exit (j + 1) else .retUnlock

variable [DecidableEq P]

set_option linter.unusedSectionVars false

/-- Continuation of the collect of line 3 with the values `vs` read so far: continue the collect,
or perform the tests of lines 4 and 10. -/
def afterColl (m : ℕ) (p : P) (vs : List (Option P)) : Loc P :=
  if vs.length < m then .coll vs
  else if vs.count (some p) < thr m then .rst 0
  else if vs.count (some p) = m then .retLock
  else .scan 0

/-- Continuation of a read of line 7 at position `j` returning `v`. -/
def afterWait (m j : ℕ) (z : Bool) (v : Option P) : Loc P :=
  if j + 1 < m then .wait (j + 1) (z && v.isNone)
  else if z && v.isNone then .scan 0 else .wait 0 true

/-- The registers: `m` read/write registers over `Option P`, initially `none` (`0`). -/
abbrev Regs (m : ℕ) (P : Type) : Fin m → ObjSpec := RegFamily (Fin m) (Option P) none

/-- **Figure 1** (in local register names) for `m` registers. -/
def alg (m : ℕ) : Impl mutexObj (Regs m P) P (Loc P) where
  memInit _ := none
  locInit _ := .rem
  invoke _ l o := match l, o with
    | .rem, .lock => .scan 0
    | .cs, .unlock => .exit 0
    | l, _ => l
  act p
    | .scan j => if h : j < m then
        .access ⟨j, h⟩ .read (fun v => if v = none then .scanW j else nextScan m j)
        else .ret () (.scan j)
    | .scanW j => if h : j < m then
        .access ⟨j, h⟩ (.write (some p)) (fun _ => nextScan m j)
        else .ret () (.scanW j)
    | .coll vs => if h : vs.length < m then
        .access ⟨vs.length, h⟩ .read (fun v => afterColl m p (vs ++ [v]))
        else .ret () (.coll vs)
    | .rst j => if h : j < m then
        .access ⟨j, h⟩ .read (fun v => if v = some p then .rstW j else nextRst m j)
        else .ret () (.rst j)
    | .rstW j => if h : j < m then
        .access ⟨j, h⟩ (.write none) (fun _ => nextRst m j)
        else .ret () (.rstW j)
    | .wait j z => if h : j < m then
        .access ⟨j, h⟩ .read (afterWait m j z)
        else .ret () (.wait j z)
    | .exit j => if h : j < m then
        .access ⟨j, h⟩ (.write none) (fun _ => nextExit m j)
        else .ret () (.exit j)
    | .retLock => .ret () .cs
    | .retUnlock => .ret () .rem
    | .rem => .ret () .rem
    | .cs => .ret () .cs

/-- Configurations of the algorithm. -/
abbrev Cfg (m : ℕ) (P : Type) := Config mutexObj (Regs m P) P (Loc P)

variable (m : ℕ) (π : P → Equiv.Perm (Fin m))

/-- Effect of one step of process `x` on its local state and on the memory (positions are local
register names, accesses go to `π x`). `idle`: nothing changes (invocations violating the client
pattern, responses from `rem`/`cs`, out-of-range positions). -/
inductive TStep (x : P) : Loc P → (Fin m → Option P) → Loc P → (Fin m → Option P) → Prop
  | scan0 {j : ℕ} {M : Fin m → Option P} (hj : j < m) (h0 : M (π x ⟨j, hj⟩) = none) :
      TStep x (.scan j) M (.scanW j) M
  | scan1 {j : ℕ} {M : Fin m → Option P} (hj : j < m) (h0 : M (π x ⟨j, hj⟩) ≠ none) :
      TStep x (.scan j) M (nextScan m j) M
  | scanW {j : ℕ} {M : Fin m → Option P} (hj : j < m) :
      TStep x (.scanW j) M (nextScan m j) (Function.update M (π x ⟨j, hj⟩) (some x))
  | coll {vs : List (Option P)} {M : Fin m → Option P} (hj : vs.length < m) :
      TStep x (.coll vs) M (afterColl m x (vs ++ [M (π x ⟨vs.length, hj⟩)])) M
  | rst0 {j : ℕ} {M : Fin m → Option P} (hj : j < m) (h0 : M (π x ⟨j, hj⟩) = some x) :
      TStep x (.rst j) M (.rstW j) M
  | rst1 {j : ℕ} {M : Fin m → Option P} (hj : j < m) (h0 : M (π x ⟨j, hj⟩) ≠ some x) :
      TStep x (.rst j) M (nextRst m j) M
  | rstW {j : ℕ} {M : Fin m → Option P} (hj : j < m) :
      TStep x (.rstW j) M (nextRst m j) (Function.update M (π x ⟨j, hj⟩) none)
  | wait {j : ℕ} {z : Bool} {M : Fin m → Option P} (hj : j < m) :
      TStep x (.wait j z) M (afterWait m j z (M (π x ⟨j, hj⟩))) M
  | exit {j : ℕ} {M : Fin m → Option P} (hj : j < m) :
      TStep x (.exit j) M (nextExit m j) (Function.update M (π x ⟨j, hj⟩) none)
  | retLock {M : Fin m → Option P} : TStep x .retLock M .cs M
  | retUnlock {M : Fin m → Option P} : TStep x .retUnlock M .rem M
  | invLock {M : Fin m → Option P} : TStep x .rem M (.scan 0) M
  | invUnlock {M : Fin m → Option P} : TStep x .cs M (.exit 0) M
  | idle {l : Loc P} {M : Fin m → Option P} : TStep x l M l M

/-- The shared-memory access steps (internal steps) of process `x`: the constructors of `TStep`
for the program counters at a memory access. -/
inductive ATStep (x : P) : Loc P → (Fin m → Option P) → Loc P → (Fin m → Option P) → Prop
  | scan0 {j : ℕ} {M : Fin m → Option P} (hj : j < m) (h0 : M (π x ⟨j, hj⟩) = none) :
      ATStep x (.scan j) M (.scanW j) M
  | scan1 {j : ℕ} {M : Fin m → Option P} (hj : j < m) (h0 : M (π x ⟨j, hj⟩) ≠ none) :
      ATStep x (.scan j) M (nextScan m j) M
  | scanW {j : ℕ} {M : Fin m → Option P} (hj : j < m) :
      ATStep x (.scanW j) M (nextScan m j) (Function.update M (π x ⟨j, hj⟩) (some x))
  | coll {vs : List (Option P)} {M : Fin m → Option P} (hj : vs.length < m) :
      ATStep x (.coll vs) M (afterColl m x (vs ++ [M (π x ⟨vs.length, hj⟩)])) M
  | rst0 {j : ℕ} {M : Fin m → Option P} (hj : j < m) (h0 : M (π x ⟨j, hj⟩) = some x) :
      ATStep x (.rst j) M (.rstW j) M
  | rst1 {j : ℕ} {M : Fin m → Option P} (hj : j < m) (h0 : M (π x ⟨j, hj⟩) ≠ some x) :
      ATStep x (.rst j) M (nextRst m j) M
  | rstW {j : ℕ} {M : Fin m → Option P} (hj : j < m) :
      ATStep x (.rstW j) M (nextRst m j) (Function.update M (π x ⟨j, hj⟩) none)
  | wait {j : ℕ} {z : Bool} {M : Fin m → Option P} (hj : j < m) :
      ATStep x (.wait j z) M (afterWait m j z (M (π x ⟨j, hj⟩))) M
  | exit {j : ℕ} {M : Fin m → Option P} (hj : j < m) :
      ATStep x (.exit j) M (nextExit m j) (Function.update M (π x ⟨j, hj⟩) none)

/-- The algorithm under the register numberings `π`. -/
abbrev I : Impl mutexObj (Regs m P) P (Loc P) := (alg m).unnamed π

variable {m π}

lemma invoke_eq (x : P) (l : Loc P) (o : MutexOp) :
    (I m π).invoke x l o = (match l, o with
      | .rem, .lock => .scan 0
      | .cs, .unlock => .exit 0
      | l, _ => l) := rfl

/-- Every step is a `TStep` of the stepping process; other local states are unchanged. -/
theorem step_tstep {C C' : Cfg m P} {ℓ : Label P mutexObj} (h : (I m π).step C ℓ = some C') :
    TStep m π ℓ.proc (C.loc ℓ.proc) C.mem (C'.loc ℓ.proc) C'.mem ∧
      ∀ y, y ≠ ℓ.proc → C'.loc y = C.loc y := by
  refine ⟨?_, fun y hy => (Impl.step_other h (Ne.symm hy)).1⟩
  cases ℓ with
  | inv x o =>
    obtain ⟨-, -, -, hloc, hmem⟩ := Impl.step_inv h
    simp only [Label.proc, hloc, Function.update_self, hmem, invoke_eq]
    cases hl : C.loc x <;> cases o <;> first | exact TStep.idle | exact TStep.invLock |
      exact TStep.invUnlock
  | ret x r =>
    obtain ⟨-, -, hmem, l, hact, hloc⟩ := Impl.step_ret h
    simp only [Label.proc, hloc, Function.update_self, hmem]
    cases hl : C.loc x <;>
      simp only [hl, Impl.unnamed, alg] at hact <;>
      (try split_ifs at hact) <;> (try simp at hact) <;>
      (subst hact; first | exact TStep.idle | exact TStep.retLock | exact TStep.retUnlock)
  | tau x =>
    obtain ⟨-, -, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
    simp only [Label.proc, hloc, Function.update_self, hmem]
    cases hl : C.loc x with
    | scan j =>
      simp only [hl, Impl.unnamed, alg] at hact
      split_ifs at hact with hj
      · simp only [Action.access.injEq] at hact
        obtain ⟨rfl, rfl, hk⟩ := hact
        simp only [heq_eq_eq] at hk; subst hk
        simp only [Function.update_eq_self]
        by_cases h0 : C.mem (π x ⟨j, hj⟩) = none
        · simp only [h0, ↓reduceIte]; exact TStep.scan0 hj h0
        · simp only [h0, ↓reduceIte]; exact TStep.scan1 hj h0
    | scanW j =>
      simp only [hl, Impl.unnamed, alg] at hact
      split_ifs at hact with hj
      · simp only [Action.access.injEq] at hact
        obtain ⟨rfl, rfl, hk⟩ := hact
        simp only [heq_eq_eq] at hk; subst hk
        exact TStep.scanW hj
    | coll vs =>
      simp only [hl, Impl.unnamed, alg] at hact
      split_ifs at hact with hj
      · simp only [Action.access.injEq] at hact
        obtain ⟨rfl, rfl, hk⟩ := hact
        simp only [heq_eq_eq] at hk; subst hk
        simp only [Function.update_eq_self]
        exact TStep.coll hj
    | rst j =>
      simp only [hl, Impl.unnamed, alg] at hact
      split_ifs at hact with hj
      · simp only [Action.access.injEq] at hact
        obtain ⟨rfl, rfl, hk⟩ := hact
        simp only [heq_eq_eq] at hk; subst hk
        simp only [Function.update_eq_self]
        by_cases h0 : C.mem (π x ⟨j, hj⟩) = some x
        · simp only [h0, ↓reduceIte]; exact TStep.rst0 hj h0
        · simp only [h0, ↓reduceIte]; exact TStep.rst1 hj h0
    | rstW j =>
      simp only [hl, Impl.unnamed, alg] at hact
      split_ifs at hact with hj
      · simp only [Action.access.injEq] at hact
        obtain ⟨rfl, rfl, hk⟩ := hact
        simp only [heq_eq_eq] at hk; subst hk
        exact TStep.rstW hj
    | wait j z =>
      simp only [hl, Impl.unnamed, alg] at hact
      split_ifs at hact with hj
      · simp only [Action.access.injEq] at hact
        obtain ⟨rfl, rfl, hk⟩ := hact
        simp only [heq_eq_eq] at hk; subst hk
        simp only [Function.update_eq_self]
        exact TStep.wait hj
    | exit j =>
      simp only [hl, Impl.unnamed, alg] at hact
      split_ifs at hact with hj
      · simp only [Action.access.injEq] at hact
        obtain ⟨rfl, rfl, hk⟩ := hact
        simp only [heq_eq_eq] at hk; subst hk
        exact TStep.exit hj
    | rem => simp [hl, Impl.unnamed, alg] at hact
    | cs => simp [hl, Impl.unnamed, alg] at hact
    | retLock => simp [hl, Impl.unnamed, alg] at hact
    | retUnlock => simp [hl, Impl.unnamed, alg] at hact

/-- `step_tstep` with the new local states as a function update. -/
theorem step_tstep' {C C' : Cfg m P} {ℓ : Label P mutexObj} (h : (I m π).step C ℓ = some C') :
    TStep m π ℓ.proc (C.loc ℓ.proc) C.mem (C'.loc ℓ.proc) C'.mem ∧
      C'.loc = Function.update C.loc ℓ.proc (C'.loc ℓ.proc) := by
  obtain ⟨h1, h2⟩ := step_tstep h
  refine ⟨h1, funext fun y => ?_⟩
  by_cases hy : y = ℓ.proc
  · subst hy; simp
  · rw [Function.update_of_ne hy, h2 y hy]

/-- Every internal step is a shared-memory access step. -/
theorem step_tau_atstep {C C' : Cfg m P} {x : P} (h : (I m π).step C (.tau x) = some C') :
    ATStep m π x (C.loc x) C.mem (C'.loc x) C'.mem := by
  obtain ⟨-, -, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  simp only [hloc, Function.update_self, hmem]
  cases hl : C.loc x with
  | scan j =>
    simp only [hl, Impl.unnamed, alg] at hact
    split_ifs at hact with hj
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, rfl, hk⟩ := hact
    simp only [heq_eq_eq] at hk; subst hk
    simp only [Function.update_eq_self]
    by_cases h0 : C.mem (π x ⟨j, hj⟩) = none
    · simp only [h0, ↓reduceIte]; exact ATStep.scan0 hj h0
    · simp only [h0, ↓reduceIte]; exact ATStep.scan1 hj h0
  | scanW j =>
    simp only [hl, Impl.unnamed, alg] at hact
    split_ifs at hact with hj
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, rfl, hk⟩ := hact
    simp only [heq_eq_eq] at hk; subst hk
    exact ATStep.scanW hj
  | coll vs =>
    simp only [hl, Impl.unnamed, alg] at hact
    split_ifs at hact with hj
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, rfl, hk⟩ := hact
    simp only [heq_eq_eq] at hk; subst hk
    simp only [Function.update_eq_self]
    exact ATStep.coll hj
  | rst j =>
    simp only [hl, Impl.unnamed, alg] at hact
    split_ifs at hact with hj
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, rfl, hk⟩ := hact
    simp only [heq_eq_eq] at hk; subst hk
    simp only [Function.update_eq_self]
    by_cases h0 : C.mem (π x ⟨j, hj⟩) = some x
    · simp only [h0, ↓reduceIte]; exact ATStep.rst0 hj h0
    · simp only [h0, ↓reduceIte]; exact ATStep.rst1 hj h0
  | rstW j =>
    simp only [hl, Impl.unnamed, alg] at hact
    split_ifs at hact with hj
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, rfl, hk⟩ := hact
    simp only [heq_eq_eq] at hk; subst hk
    exact ATStep.rstW hj
  | wait j z =>
    simp only [hl, Impl.unnamed, alg] at hact
    split_ifs at hact with hj
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, rfl, hk⟩ := hact
    simp only [heq_eq_eq] at hk; subst hk
    simp only [Function.update_eq_self]
    exact ATStep.wait hj
  | exit j =>
    simp only [hl, Impl.unnamed, alg] at hact
    split_ifs at hact with hj
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, rfl, hk⟩ := hact
    simp only [heq_eq_eq] at hk; subst hk
    exact ATStep.exit hj
  | rem => simp [hl, Impl.unnamed, alg] at hact
  | cs => simp [hl, Impl.unnamed, alg] at hact
  | retLock => simp [hl, Impl.unnamed, alg] at hact
  | retUnlock => simp [hl, Impl.unnamed, alg] at hact

/-! ### Bounds -/

/-- Positions are in range. -/
def Bounded (m : ℕ) : Loc P → Prop
  | .scan j | .scanW j | .rst j | .rstW j | .exit j => j < m
  | .wait j _ => j < m
  | .coll vs => vs.length < m
  | _ => True

/-- Local states performing a shared-memory access. -/
def IsAccess : Loc P → Prop
  | .scan _ | .scanW _ | .rst _ | .rstW _ | .exit _ | .wait _ _ | .coll _ => True
  | _ => False

lemma bounded_nextScan {j : ℕ} (hm : 0 < m) : Bounded m (nextScan m j : Loc P) := by
  unfold nextScan; split_ifs <;> simp [Bounded, *]

lemma bounded_nextRst {j : ℕ} (hm : 0 < m) : Bounded m (nextRst m j : Loc P) := by
  unfold nextRst; split_ifs <;> simp [Bounded, *]

lemma bounded_nextExit {j : ℕ} : Bounded m (nextExit m j : Loc P) := by
  unfold nextExit; split_ifs <;> simp [Bounded, *]

lemma bounded_afterColl {x : P} {vs : List (Option P)} (hm : 0 < m) :
    Bounded m (afterColl m x vs) := by
  unfold afterColl; split_ifs <;> simp [Bounded, *]

lemma bounded_afterWait {j : ℕ} {z : Bool} {v : Option P} (hm : 0 < m) :
    Bounded m (afterWait m j z v) := by
  unfold afterWait; split_ifs <;> simp [Bounded, *]

lemma TStep.bounded {x : P} {l l' : Loc P} {M M' : Fin m → Option P} (hm : 0 < m)
    (hs : TStep m π x l M l' M') (hb : Bounded m l) : Bounded m l' := by
  cases hs <;> first | exact hb | exact bounded_nextScan hm | exact bounded_nextRst hm |
    exact bounded_nextExit | exact bounded_afterColl hm | exact bounded_afterWait hm |
    simp [Bounded, hm]

/-- A process taking an internal step is at a shared-memory access. -/
lemma isAccess_of_tau {C C' : Cfg m P} {x : P} (h : (I m π).step C (.tau x) = some C') :
    IsAccess (C.loc x) := by
  obtain ⟨-, -, i, o, k, hact, -, -⟩ := Impl.step_tau h
  cases hl : C.loc x <;> simp_all [Impl.unnamed, alg, IsAccess]

/-- Responses: from `retLock`, from `retUnlock`, or without effect from `rem`, `cs` or an
out-of-range position. -/
lemma ret_cases {C C' : Cfg m P} {x : P} {r : Unit} (h : (I m π).step C (.ret x r) = some C') :
    (C.loc x = .retLock ∧ C'.loc x = .cs) ∨ (C.loc x = .retUnlock ∧ C'.loc x = .rem) ∨
      (C'.loc x = C.loc x ∧ (C.loc x = .rem ∨ C.loc x = .cs ∨ ¬ Bounded m (C.loc x))) := by
  obtain ⟨-, -, -, l, hact, hloc⟩ := Impl.step_ret h
  have hl' : C'.loc x = l := by rw [hloc]; simp
  rw [hl']
  cases hl : C.loc x <;> simp only [hl, Impl.unnamed, alg] at hact <;>
    (try split_ifs at hact with hj) <;> (try simp at hact) <;> subst hact <;>
    simp_all [Bounded]

/-! ### Regions -/

/-- The client region corresponding to a local state. -/
def regOf : Loc P → Region
  | .rem => .rem
  | .cs => .cs
  | .exit _ => .exiting
  | .retUnlock => .exiting
  | _ => .trying

lemma regOf_tstep {x : P} {l l' : Loc P} {M M' : Fin m → Option P}
    (hs : TStep m π x l M l' M') (ha : IsAccess l) : regOf l' = regOf l := by
  cases hs <;> simp_all [IsAccess, regOf, nextScan, nextRst, nextExit, afterColl, afterWait] <;>
    split_ifs <;> simp

lemma clientWF_prefix {α : List (Label P mutexObj)} {ℓ : Label P mutexObj}
    (h : ClientWF (α ++ [ℓ])) : ClientWF α := by
  intro p hp
  apply h p
  rw [regionOf_append_singleton, hp]
  split_ifs <;> rfl

/-- The region invariant: in a client-well-formed execution the region of every process is the
one of its local state, it is idle iff it is in `rem` or `cs`, and positions are in range. -/
theorem reg_inv (hm : 0 < m) {α : List (Label P mutexObj)} {C : Cfg m P} (hwf : ClientWF α)
    (h : (I m π).run α = some C) : ∀ p, regionOf α p = some (regOf (C.loc p)) ∧
      (C.pend p = none ↔ (C.loc p = .rem ∨ C.loc p = .cs)) ∧ Bounded m (C.loc p) := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run_nil, Option.some.injEq] at h; subst h
    intro p; simp [regOf, Impl.initCfg, alg, Bounded]
  | append_singleton α ℓ ih =>
    rw [Impl.run_concat] at h
    cases hα : (I m π).run α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some] at h
      have IH := ih (clientWF_prefix hwf) hα
      intro p
      by_cases hp : ℓ.proc = p
      · subst hp
        have hwfp := hwf ℓ.proc
        rw [regionOf_append_singleton, ite_eq_left rfl, (IH ℓ.proc).1] at hwfp ⊢
        obtain ⟨IH1, IH2, IH3⟩ := IH ℓ.proc
        cases ℓ with
        | inv x o =>
          obtain ⟨h0, -, hpend, hloc, -⟩ := Impl.step_inv h
          simp only [Label.proc] at hwfp IH2 h0 ⊢
          have hl : C.loc x = (I m π).invoke x (C₀.loc x) o := by rw [hloc]; simp
          have hpx : C.pend x = some o := by rw [hpend]; simp
          rw [hl, hpx]
          rcases IH2.1 h0 with h1 | h1 <;> rw [h1] at hwfp ⊢ <;>
            cases o <;> simp_all [regOf, Region.next, invoke_eq, Bounded]
        | tau x =>
          obtain ⟨h0, hpend, -⟩ := Impl.step_tau h
          have ha := isAccess_of_tau h
          have hs := (step_tstep h).1
          simp only [Label.proc] at hs ⊢
          have hr := regOf_tstep hs ha
          refine ⟨by simp [Region.next, hr], ?_, hs.bounded hm IH3⟩
          rw [hpend]
          constructor
          · intro h1; exact absurd h1 h0
          · intro h1; rcases h1 with h1 | h1 <;> rw [h1] at hr <;>
              cases hl : C₀.loc x <;> simp_all [regOf, IsAccess]
        | ret x r =>
          obtain ⟨h0, hpend, -⟩ := Impl.step_ret h
          have hpx : C.pend x = none := by rw [hpend]; simp
          simp only [Label.proc] at hwfp ⊢
          rcases ret_cases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp_all [regOf, Region.next, Bounded]
          · simp_all [regOf, Region.next, Bounded]
          · exfalso
            rcases h2 with h2 | h2 | h2
            · exact h0 (IH2.2 (Or.inl h2))
            · exact h0 (IH2.2 (Or.inr h2))
            · exact h2 IH3
      · rw [regionOf_append_singleton_of_ne _ _ hp, (Impl.step_other h hp).1,
          (Impl.step_other h hp).2]
        exact IH p

end Podc.MemoryAnonymousCoordination.Mutex
