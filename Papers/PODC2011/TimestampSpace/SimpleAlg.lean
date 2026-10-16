import Papers.PODC2011.TimestampSpace.Defs
import Papers.PODC2024.HistoryIndependent.Alg4WaitFree

/-!
# Section 5: a simple one-shot timestamp implementation from `⌈n/2⌉` registers

Algorithms 1 (`simple-compare`) and 2 (`simple-getTS`) of Helmi, Higham, Pacheco, Woelfel,
*The space complexity of long-lived and one-shot timestamp implementations* (PODC 2011,
arXiv:1103.5794v2), and the algorithm part of Lemma 5.1.

* Processes `Fin n` (0-based), registers `R : Fin ((n+1)/2)` (`(n+1)/2 = ⌈n/2⌉`), CSLib
  registers with values in `ℕ`, initially `0`. Process `p` owns register `p / 2`
  (`own p`; the paper's `⌈p/2⌉` for 1-based ids, so `R[i]` is written by the processes `2i`
  and `2i+1`).
* `compare t₁ t₂` returns `t₁ < t₂` without accessing memory.
* `getTS` reads `R[0], R[1], …` in order; at its own register `i = own p` it performs the
  non-atomic increment `R[i] := R[i] + 1` as a read of `r` followed by a write of `r + 1`.
  The instruction `sum := sum + R[i]` after the increment is modelled in two ways
  (parameter `reread`):
  - `reread = true` (the literal code): `R[i]` is read again and the value read is added;
  - `reread = false`: the value just written (`r + 1`) is added.
  Both versions are proved correct.
* The local state has one ghost field, `wrote` (whether the process has written its register),
  which the algorithm never reads.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp.SimpleTS

open Cslib.SharedMemory

/-- Program counter of a process. -/
inductive PC where
  /-- No pending operation. -/
  | idle
  /-- `compare` computed; about to return `b`. -/
  | cmp (b : Bool)
  /-- `getTS`: about to read `R[i]`; `s` = sum of the values of `R[0..i-1]`. Returns `s` if
  `i ≥ ⌈n/2⌉`. -/
  | rd (i s : ℕ)
  /-- `getTS`: has read `r` from its own register, about to write `r + 1`. -/
  | wr (r s : ℕ)
  /-- `getTS`: has written its own register, about to re-read it (only if `reread`). -/
  | rr (s : ℕ)

/-- Local state: program counter and a ghost flag "has written its register". -/
structure Loc where
  /-- Program counter. -/
  pc : PC
  /-- Ghost: the process has written its register. -/
  wrote : Bool

variable {n : ℕ}

/-- The register shared by process `p` (and its partner `p xor 1`). -/
def own (p : Fin n) : Fin ((n + 1) / 2) := ⟨p.val / 2, by omega⟩

/-- The base objects: `⌈n/2⌉` registers over `ℕ`, initially `0`. -/
abbrev Regs (n : ℕ) : Fin ((n + 1) / 2) → ObjSpec := fun _ => register ℕ 0

/-- One step of a process (Algorithms 1 and 2). -/
def act (reread : Bool) (p : Fin n) (l : Loc) : Action (tsObj ℕ) (Regs n) Loc :=
  match l.pc with
  | .idle => .ret (.inr false) l
  | .cmp b => .ret (.inr b) { l with pc := .idle }
  | .rd i s =>
    if h : i < (n + 1) / 2 then
      if i = (own p).val then .access ⟨i, h⟩ .read (fun v => { l with pc := .wr v s })
      else .access ⟨i, h⟩ .read (fun v => { l with pc := .rd (i + 1) (s + v) })
    else .ret (.inl s) { l with pc := .idle }
  | .wr r s => .access (own p) (.write (r + 1)) (fun _ =>
      { pc := if reread then .rr s else .rd ((own p).val + 1) (s + (r + 1)), wrote := true })
  | .rr s => .access (own p) .read (fun v => { l with pc := .rd ((own p).val + 1) (s + v) })

/-- Local state after an invocation. -/
def invoke (l : Loc) : TSOp ℕ → Loc
  | .getTS => { l with pc := .rd 0 0 }
  | .compare a b => { l with pc := .cmp (decide (a < b)) }

/-- **Algorithms 1 and 2** for `n` processes, from `⌈n/2⌉ = (n+1)/2` registers. -/
def alg (n : ℕ) (reread : Bool) : Impl (tsObj ℕ) (Regs n) (Fin n) Loc where
  memInit _ := 0
  locInit _ := ⟨.idle, false⟩
  invoke _ l o := invoke l o
  act := act reread

/-! ### Wait-freedom -/

/-- Potential: at most `3⌈n/2⌉ + 3` accesses per `getTS`, none per `compare`. -/
def pot (p : Fin n) (l : Loc) : ℕ :=
  match l.pc with
  | .rd i _ => 3 * ((n + 1) / 2 - i) + 3
  | .wr _ _ => 3 * ((n + 1) / 2 - (own p).val) + 2
  | .rr _ => 3 * ((n + 1) / 2 - (own p).val) + 1
  | _ => 0

/-- **Lemma 5.1 (wait-freedom).** Every operation finishes within `3⌈n/2⌉ + 3` own steps. -/
theorem waitFree (reread : Bool) : (alg n reread).WaitFree := by
  refine (alg n reread).waitFree_of_potential pot ?_
  intro p l i o k hact x
  have hown : (own p).val < (n + 1) / 2 := (own p).isLt
  simp only [alg, act] at hact
  cases hpc : l.pc with
  | idle => simp [hpc] at hact
  | cmp b => simp [hpc] at hact
  | rd j s =>
    simp only [hpc] at hact
    split_ifs at hact with h1 h2
    · cases hact; simp [pot, hpc]; omega
    · cases hact; simp [pot, hpc]; omega
  | wr r s =>
    simp only [hpc] at hact; cases hact
    cases reread
    · simp [pot, hpc]; omega
    · simp [pot, hpc]
  | rr s =>
    simp only [hpc] at hact; cases hact; simp [pot, hpc]; omega

end Cslib.SharedMemory.Timestamp.SimpleTS
