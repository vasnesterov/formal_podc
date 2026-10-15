import Papers.PODC2019.AnonymousMutex.LowerBound
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Algorithm 2: read/modify/write (compare&swap) memory-anonymous mutex

Aghazadeh, Imbs, Raynal, Taubenfeld, Woelfel, PODC 2019 (arXiv:1810.03723), Section 5.

```
operation lock() is
(1) repeat
(2)   for each x ∈ {1..m} do R.compare&swap(x, ⊥, id)
(3)   for each x ∈ {1..m} do view[x] ← R.read(x)
(4)   most_present ← maximum number of times the same non-⊥ value appears in view
(5)   owned ← |{x : view[x] = id}|
(6)   if owned < most_present then
(7)     for each x ∈ {1..m} do if view[x] = id then R.write(x, ⊥)
(8)     repeat
(9)       for each x ∈ {1..m} do view[x] ← R.read(x)
(10)    until ∀ x : view[x] = ⊥
(11)  end if
(12) until owned > m/2
operation unlock() is
(13) for each x ∈ {1..m} do R.compare&swap(x, id, ⊥)
```

Modelling choices (see `README.md`): registers hold `Option Id` (`none` = `⊥`); every loop
iteration is one atomic access (iterations of line 7 with `view[x] ≠ id` do nothing and are
skipped); loops run in the process's local order; the bookkeeping between accesses (lines 4–6,
10–12) is folded into the continuation of the preceding access; `owned > m/2` is `m < 2 owned`.
The loop of lines 8–10 keeps a flag `ab` ("all entries read so far were `⊥`").
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex.Alg2

/-- Program counters of Algorithm 2. -/
inductive PC
  /-- remainder section -/
  | rem
  /-- line 2: `compare&swap(i, ⊥, id)` -/
  | cas (i : ℕ)
  /-- line 3: `view[i] ← read(i)` -/
  | read (i : ℕ)
  /-- line 7: `write(i, ⊥)` (only for `view[i] = id`) -/
  | wr (i : ℕ)
  /-- line 9: `read(i)`; `ab` = all entries read so far in this scan were `⊥` -/
  | wait (i : ℕ) (ab : Bool)
  /-- `lock()` returns -/
  | retLock
  /-- critical section -/
  | cs
  /-- line 13: `compare&swap(i, id, ⊥)` -/
  | un (i : ℕ)
  /-- `unlock()` returns -/
  | retUnlock
  deriving DecidableEq

/-- Local state: identifier, program counter, view. -/
structure St (Id : Type) (m : ℕ) where
  me : Id
  pc : PC
  view : Fin m → Option Id

variable {Id : Type} [DecidableEq Id] {m : ℕ}

/-- The first local index `≥ i` whose view entry is the own identifier (`m` if none). -/
def nextOwn (view : Fin m → Option Id) (me : Id) (i : ℕ) : ℕ :=
  (((List.finRange m).find? (fun x => decide (i ≤ x.val) && decide (view x = some me))).map
    Fin.val).getD m

/-- `owned`: number of entries of the view equal to `me`. -/
def owned (view : Fin m → Option Id) (me : Id) : ℕ :=
  (Finset.univ.filter (fun x => view x = some me)).card

/-- `most_present`: the maximal number of occurrences of a non-`⊥` value in the view. -/
def mostPresent (view : Fin m → Option Id) : ℕ :=
  Finset.univ.sup (fun x => if view x = none then 0 else
    (Finset.univ.filter (fun y => view y = view x)).card)

/-- Continue the loop of line 7 at local index `i` (or start waiting, lines 8–10). -/
def wrFrom (s : St Id m) (i : ℕ) : St Id m :=
  if nextOwn s.view s.me i < m then { s with pc := .wr (nextOwn s.view s.me i) }
  else { s with pc := .wait 0 true }

/-- Lines 4–6 and 12 after the view `w` has been read. -/
def afterRead (s : St Id m) (w : Fin m → Option Id) : St Id m :=
  if owned w s.me < mostPresent w then wrFrom { s with view := w } 0
  else if m < 2 * owned w s.me then { s with view := w, pc := .retLock }
  else { s with view := w, pc := .cas 0 }

/-- Algorithm 2 as a symmetric algorithm. -/
def alg2 (Id : Type) [DecidableEq Id] (m : ℕ) : SymAlg mutexObj Id m (Option Id) (St Id m) where
  bot := none
  init a := ⟨a, .rem, fun _ => none⟩
  invoke s o := match s.pc, o with
    | .rem, .lock => { s with pc := .cas 0 }
    | .cs, .unlock => { s with pc := .un 0 }
    | _, _ => s
  act s := match s.pc with
    | .cas i =>
      if h : i < m then
        .rmw ⟨i, h⟩ (fun v => if v = none then some s.me else v)
          (fun _ => if i + 1 < m then { s with pc := .cas (i + 1) } else { s with pc := .read 0 })
      else .ret () s
    | .read i =>
      if h : i < m then
        .rmw ⟨i, h⟩ (fun v => v) (fun v =>
          if i + 1 < m then { s with view := Function.update s.view ⟨i, h⟩ v, pc := .read (i + 1) }
          else afterRead s (Function.update s.view ⟨i, h⟩ v))
      else .ret () s
    | .wr i =>
      if h : i < m then .rmw ⟨i, h⟩ (fun _ => none) (fun _ => wrFrom s (i + 1))
      else .ret () s
    | .wait i ab =>
      if h : i < m then
        .rmw ⟨i, h⟩ (fun v => v) (fun v =>
          if i + 1 < m then { s with pc := .wait (i + 1) (ab && v == none) }
          else if ab && v == none then { s with pc := .cas 0 } else { s with pc := .wait 0 true })
      else .ret () s
    | .retLock => .ret () { s with pc := .cs }
    | .un i =>
      if h : i < m then
        .rmw ⟨i, h⟩ (fun v => if v = some s.me then none else v)
          (fun _ => if i + 1 < m then { s with pc := .un (i + 1) } else { s with pc := .retUnlock })
      else .ret () s
    | .retUnlock => .ret () { s with pc := .rem }
    | _ => .ret () s

end AnonymousMutex.Alg2
