import Papers.PODC2019.AnonymousMutex.LowerBound

/-!
# Algorithm 1: read/write + snapshot memory-anonymous mutex

Aghazadeh, Imbs, Raynal, Taubenfeld, Woelfel, PODC 2019 (arXiv:1810.03723), Section 3.

```
operation owned() is return |{x : view[x] = id}|
operation shrink() is
(2) for each x such that view[x] = id do if R.read(x) = id then R.write(x, ⊥)
operation lock() is
(3) repeat
(4)   repeat view ← R.snapshot() until owned() > 0 ∨ ∀ x : view[x] = ⊥
(5)   if ∃ x : view[x] = ⊥
(6)     then R.write(x, id)
(7)     else % view is full %
(8)       let cnt = |{view[1], …, view[m]}|
(9)       if owned() < m / cnt then shrink()
(11) until ∀ x : view[x] = id
operation unlock() is (12) shrink()
```

Modelling choices (see `README.md`):
* registers hold `Option Id` (`none` = `⊥`), the snapshot is an atomic primitive (as assumed in
  the paper, §2.1);
* the register written at line 6 is the first `⊥` entry of the view in the process's *local*
  order (the paper leaves the choice open); `shrink()` visits the registers in local order;
* every iteration of a loop is one memory access; the bookkeeping between accesses is folded into
  the continuations (`afterSnap`, `shrinkFrom`), so the program counter always designates the
  next access;
* `owned() < m / cnt` is `owned * cnt < m`.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex.Alg1

/-- Program counters of Algorithm 1. -/
inductive PC (m : ℕ)
  /-- remainder section -/
  | rem
  /-- line 4: take a snapshot -/
  | snap
  /-- line 6: write the own identifier into local register `x` -/
  | write (x : Fin m)
  /-- line 2: read local register `i` in `shrink()` (`unl`: the shrink of `unlock()`) -/
  | shRead (i : ℕ) (unl : Bool)
  /-- line 2: write `⊥` into local register `i` in `shrink()` -/
  | shWrite (i : ℕ) (unl : Bool)
  /-- `lock()` returns -/
  | retLock
  /-- critical section -/
  | cs
  /-- `unlock()` returns -/
  | retUnlock
  deriving DecidableEq

/-- Local state: identifier, program counter, last snapshot (`view`). -/
structure St (Id : Type) (m : ℕ) where
  me : Id
  pc : PC m
  view : Fin m → Option Id
  deriving DecidableEq

variable {Id : Type} [DecidableEq Id] {m : ℕ}

/-- The first local index `≥ i` whose view entry is the own identifier (`m` if none). -/
def nextOwn (view : Fin m → Option Id) (me : Id) (i : ℕ) : ℕ :=
  (((List.finRange m).find? (fun x => decide (i ≤ x.val) && decide (view x = some me))).map
    Fin.val).getD m

/-- Continue `shrink()` at local index `i` (or finish it). -/
def shrinkFrom (s : St Id m) (i : ℕ) (unl : Bool) : St Id m :=
  if nextOwn s.view s.me i < m then { s with pc := .shRead (nextOwn s.view s.me i) unl }
  else { s with pc := if unl then .retUnlock else .snap }

/-- `owned()`: number of entries of the view equal to `me`. -/
def owned (view : Fin m → Option Id) (me : Id) : ℕ :=
  (Finset.univ.filter (fun x => view x = some me)).card

/-- `cnt`: number of distinct values in the view. -/
def cnt (view : Fin m → Option Id) : ℕ := (Finset.univ.image view).card

/-- The first `⊥` entry of the view in local order. -/
def firstBot (view : Fin m → Option Id) : Option (Fin m) :=
  (List.finRange m).find? (fun x => view x = none)

/-- Lines 4–11 after a snapshot `w`. -/
def afterSnap (s : St Id m) (w : Fin m → Option Id) : St Id m :=
  if 0 < owned w s.me ∨ ∀ x, w x = none then
    match firstBot w with
    | some x => { s with view := w, pc := .write x }
    | none =>
      if owned w s.me = m then { s with view := w, pc := .retLock }
      else if owned w s.me * cnt w < m then shrinkFrom { s with view := w } 0 false
      else { s with view := w, pc := .snap }
  else { s with view := w, pc := .snap }

/-- Algorithm 1 as a symmetric algorithm. -/
def alg1 (Id : Type) [DecidableEq Id] (m : ℕ) : SymAlg mutexObj Id m (Option Id) (St Id m) where
  bot := none
  init a := ⟨a, .rem, fun _ => none⟩
  invoke s o := match s.pc, o with
    | .rem, .lock => { s with pc := .snap }
    | .cs, .unlock => shrinkFrom s 0 true
    | _, _ => s
  act s := match s.pc with
    | .snap => .snap (afterSnap s)
    | .write x => .rmw x (fun _ => some s.me) (fun _ => { s with pc := .snap })
    | .shRead i unl =>
      if h : i < m then
        .rmw ⟨i, h⟩ (fun v => v)
          (fun v => if v = some s.me then { s with pc := .shWrite i unl } else shrinkFrom s (i + 1) unl)
      else .ret () s
    | .shWrite i unl =>
      if h : i < m then .rmw ⟨i, h⟩ (fun _ => none) (fun _ => shrinkFrom s (i + 1) unl)
      else .ret () s
    | .retLock => .ret () { s with pc := .cs }
    | .retUnlock => .ret () { s with pc := .rem }
    | _ => .ret () s

end AnonymousMutex.Alg1
