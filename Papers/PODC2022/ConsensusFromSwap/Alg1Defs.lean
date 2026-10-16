import Papers.PODC2022.ConsensusFromSwap.Model

/-!
# Algorithm 1: obstruction-free m-valued k-set agreement from `n − k` swap objects

Algorithm 1 of Ovens (PODC 2022), in the model of `Model.lean`.

* `N` swap objects `B 0, …, B (N-1)` (the paper: `N = n − k`), each storing a pair
  `(lap counter, identifier)` with lap counters `Fin m → ℕ`, initially `(0, ⊥)` (`⊥ = none`).
  Swap objects do **not** support `Read`.
* Local state of a process: its identifier `me`, its lap counter `U`, the index `idx` of the next
  object to swap (loop on lines 6–12), the flag `conf` (`conflict`) and the decision `dec`.
* One step = one `Swap` (line 7) together with the following local computation (lines 8–12 and,
  after the last object, lines 13–20). The decision (line 17) happens in the step that swaps the
  last object of a conflict-free iteration.
-/

namespace ConsensusFromSwap.Alg1

open ConsensusFromSwap

/-- Lap counters. -/
abbrev Lap (m : ℕ) := Fin m → ℕ

/-- Values stored in the swap objects: a lap counter and a process identifier (`none` = `⊥`). -/
abbrev Val (P : Type) (m : ℕ) := Lap m × Option P

/-- The objects: `N` swap objects storing `Val P m`. -/
abbrev T (P : Type) (m N : ℕ) : Fin N → Cslib.SharedMemory.ObjSpec :=
  fun _ => swapObj (Val P m) (0, none)

/-- Local states. -/
structure LState (P : Type) (m N : ℕ) where
  /-- The identifier of the process. -/
  me : P
  /-- The local lap counter `U`. -/
  U : Lap m
  /-- The next object to swap. -/
  idx : Fin N
  /-- The `conflict` flag. -/
  conf : Bool
  /-- The decided value, if any. -/
  dec : Option (Fin m)

variable {P : Type} [DecidableEq P] {m N : ℕ} [NeZero m] [NeZero N]

/-- The value chosen on lines 14–15: the smallest index with a maximal component. -/
def lead (U : Lap m) : Fin m :=
  (Finset.univ.filter fun j => ∀ j', U j' ≤ U j).min' (by
    obtain ⟨j, hj⟩ := (Finset.univ : Finset (Fin m)).exists_max_image U
      ⟨0, Finset.mem_univ _⟩
    exact ⟨j, by simpa using fun j' => hj.2 j' (Finset.mem_univ _)⟩)

/-- Lines 13–20 after a conflict-free iteration: decide (line 17) or increment the leading
component (line 20) and start a new iteration. -/
def lap (me : P) (U : Lap m) : LState P m N :=
  if ∀ j, j ≠ lead U → U j + 2 ≤ U (lead U) then
    ⟨me, U, 0, false, some (lead U)⟩
  else
    ⟨me, Function.update U (lead U) (U (lead U) + 1), 0, false, none⟩

/-- The local computation after a swap on object `s.idx` with response `r` (lines 8–20). -/
def after (s : LState P m N) (r : Val P m) : LState P m N :=
  let conf' := s.conf || decide (r ≠ (s.U, some s.me))
  let U' : Lap m := fun j => max (s.U j) (r.1 j)
  if h : s.idx.val + 1 < N then ⟨s.me, U', ⟨s.idx.val + 1, h⟩, conf', none⟩
  else if conf' then ⟨s.me, U', 0, false, none⟩
  else lap s.me U'

/-- The initial lap counter of a process with input `v` (lines 2–3). -/
def initU (v : Fin m) : Lap m := fun j => if j = v then 1 else 0

variable (P m N) in
/-- Algorithm 1 for processes `P`, inputs `Fin m` and `N` swap objects. -/
def alg : Alg (T P m N) P (Fin m) where
  L := LState P m N
  init p v := ⟨p, initU v, 0, false, none⟩
  act s := match s.dec with
    | some v => .out v
    | none => .access s.idx (s.U, some s.me) (fun r => after s r)
  mem₀ _ := (0, none)

end ConsensusFromSwap.Alg1
