import Cslib.Computability.Distributed.Byzantine.PartialSync.Omission
import Podc.PartialSync.Runs

-- CSLib candidate: Cslib/Computability/Distributed/Byzantine/PartialSync/Omission.lean

/-!
# Standard omission executions

Complements CSLib's synchronous omission executions `OmExec` with the two executions used by
message lower bounds:

* `OmExec.ff x`: the fault-free execution with inputs `x` (every batch is delivered);
* `OmExec.solo x B`: every process of `B` is *isolated*: it receives only its own messages
  (admissible with faulty set `B`, `OmExec.solo_admits`). An isolated process behaves as in
  any other execution in which it is isolated with the same input (`OmExec.solo_st`).

`Run.st_eq_ff`: a fault-free run with zero delays has the states of the fault-free omission
execution; in particular the quiet fault-free run `Run.quiet ∅ x` decides as `OmExec.ff x`
(`Run.quiet_empty_decides_iff`).
-/

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M S VI VO : Type*}

namespace OmExec

/-- The fault-free omission execution with inputs `x`. -/
def ff (x : P → VI) : OmExec P VI where
  inp := x
  ok _ _ _ := true

/-- The omission execution with inputs `x` in which every process of `B` is isolated: it receives
only its own messages. -/
def solo [DecidableEq P] (x : P → VI) (B : Finset P) : OmExec P VI where
  inp := x
  ok _ q p := !decide (p ∈ B ∧ q ≠ p)

variable {A : Algorithm P M S VI VO} {x : P → VI}

@[simp] theorem ff_inp : (ff x).inp = x := rfl
@[simp] theorem ff_ok (τ : ℕ) (q p : P) : (ff x).ok τ q p = true := rfl

/-- Every faulty set is admissible for the fault-free execution. -/
theorem ff_admits (F : Finset P) : (ff x).Admits A F := fun _ _ _ h => by simp at h

@[simp] theorem ff_inbox (τ : ℕ) (p q : P) :
    (ff x).inbox A τ p q = A.send q ((ff x).st A τ q) p := rfl

section solo

variable [DecidableEq P] {B : Finset P}

@[simp] theorem solo_inp : (solo x B).inp = x := rfl

theorem solo_ok (τ : ℕ) (q p : P) : (solo x B).ok τ q p = !decide (p ∈ B ∧ q ≠ p) := rfl

/-- In `solo x B`, the processes of `B` are a legal set of omission-faulty processes. -/
theorem solo_admits : (solo x B).Admits A B := by
  intro τ q p h _
  simp only [solo_ok, Bool.not_eq_false', decide_eq_true_eq] at h
  exact ⟨h.2, Or.inr h.1⟩

/-- An isolated process receives nothing from the other processes. -/
theorem solo_inbox_of_mem {p q : P} (hp : p ∈ B) (hq : q ≠ p) (τ : ℕ) :
    (solo x B).inbox A τ p q = [] := by
  simp [inbox, solo_ok, hp, hq]

/-- An isolated process behaves as in any other execution in which it is isolated with the same
input. -/
theorem solo_st {y : P → VI} {C : Finset P} {p : P} (hpB : p ∈ B) (hpC : p ∈ C)
    (hxy : x p = y p) (τ : ℕ) : (solo x B).st A τ p = (solo y C).st A τ p := by
  refine st_eq_of_inbox_eq (X := fun _ => {p}) (fun _ => le_rfl)
    (fun q hq => by rw [Set.mem_singleton_iff.mp hq]; exact hxy) (fun τ ih q hq => ?_) τ p rfl
  rw [Set.mem_singleton_iff.mp hq]
  funext r
  refine inbox_congr ?_ fun hok => ?_
  · by_cases hr : r = p <;> simp [solo_ok, hpB, hpC, hr]
  · by_cases hr : r = p
    · subst hr; exact ih r rfl
    · simp [solo_ok, hpB, hr] at hok

end solo

end OmExec

namespace Run

variable [DecidableEq P] {A : Algorithm P M S VI VO}

/-- A fault-free run with zero delays has the states of the fault-free omission execution. -/
theorem st_eq_ff {R : Run P M VI} (hf : R.faulty = ∅) (hdl : ∀ q τ p, R.dl q τ p = τ) :
    R.st A = (OmExec.ff R.inp).st A := by
  funext τ
  induction τ with
  | zero => rfl
  | succ τ ih =>
    funext p
    rw [st_succ, OmExec.st_succ, ih]
    congr 1
    funext q
    rw [inbox_of_dl_eq A hdl, out_of_correct A _ (by simp [hf]), ih, OmExec.ff_inbox]

/-- The quiet fault-free run decides as the fault-free omission execution. -/
theorem quiet_empty_decides_iff {x : P → VI} {p : P} {v : VO} :
    (quiet (M := M) ∅ x).Decides A p v ↔ (OmExec.ff x).Decides A p v := by
  simp only [Decides, OmExec.Decides, st_eq_ff (R := quiet (M := M) ∅ x) rfl (fun _ _ _ => rfl),
    quiet_inp]

end Run

end Cslib.Byzantine.PartialSync
