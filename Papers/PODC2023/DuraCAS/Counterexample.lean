import Papers.PODC2023.DuraCAS.Spec

/-!
# DuraCAS is not durably linearizable under the brief announcement's recovery discipline

The brief announcement states the obligation of a crashed process *per object*: "when `π`
subsequently restarts, it must execute `O.Recover()` before invoking any other operation on `O`".
So after crashing inside an operation on `O₀`, a process may invoke an operation on another
DuraCAS object `O₁` first. But the DurEC handle `h.Critical` (with its `Val` field) is shared by all
objects: if the crash happened right after the install at line 10 of DurEC's `ECSC` on `O₀`'s `Z`
(the install is not forwarded yet), the `ECSC` of the new operation on `O₁` overwrites
`h.Critical.Val` at line 7, and any helper then forwards *that* value into `O₀`'s `Z`.

`StepPO` adds the transition allowed by the per-object discipline ("postpone the recovery of `O`
and invoke an operation on `O' ≠ O`"). `perObject_counterexample`: two processes, two objects,
initial values `0`; a `READ` of `O₀` returns `2`, a value only ever proposed to `O₁`.
-/

namespace Podc.DuraCAS

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

/-- Labels of the per-object discipline: additionally, a process that has just crashed (it is at
line 22 of `RECOVER` of its pending operation on `k`) may invoke an operation on `k' ≠ k` instead. -/
inductive LblPO (P K V : Type) where
  | base (ℓ : Lbl P K V)
  | postpone (p : P) (k : K) (op : Op V)
  deriving DecidableEq

/-- Enabledness under the per-object discipline. -/
def LblPO.En (s : St P K V) : LblPO P K V → Prop
  | .base ℓ => ℓ.En s
  | .postpone p k _ => (s.ps p).pc = .recv 0 ∧ (s.ps p).fr = none ∧
      ((s.ps p).op.map OpRec.k).isSome ∧ (s.ps p).op.map OpRec.k ≠ some k

instance (s : St P K V) : (ℓ : LblPO P K V) → Decidable (ℓ.En s)
  | .base ℓ => inferInstanceAs (Decidable (ℓ.En s))
  | .postpone p k _ => inferInstanceAs (Decidable ((s.ps p).pc = .recv 0 ∧ (s.ps p).fr = none ∧
      ((s.ps p).op.map OpRec.k).isSome ∧ (s.ps p).op.map OpRec.k ≠ some k))

/-- Effect of a per-object-discipline transition. -/
def LblPO.apply (s : St P K V) : LblPO P K V → St P K V
  | .base ℓ => ℓ.apply s
  | .postpone p k op => doInvoke s p k op

/-- One step under the per-object recovery discipline. -/
def StepPO (s s' : St P K V) : Prop := ∃ ℓ : LblPO P K V, ℓ.En s ∧ s' = ℓ.apply s

/-- Reachable states under the per-object discipline. -/
def ReachPO (init : K → V) (hv0 : Hd P → V × Bool) : St P K V → Prop :=
  Relation.ReflTransGen StepPO (initSt init hv0)

/-- Run a list of labels (none if some label is not enabled). -/
def runPO (s : St P K V) : List (LblPO P K V) → Option (St P K V)
  | [] => some s
  | ℓ :: ls => if ℓ.En s then runPO (ℓ.apply s) ls else none

theorem reachPO_of_runPO {init : K → V} {hv0} {s s' : St P K V} (hs : ReachPO init hv0 s) :
    ∀ ls, runPO s ls = some s' → ReachPO init hv0 s' := by
  intro ls
  induction ls generalizing s with
  | nil => intro h; simp [runPO] at h; exact h ▸ hs
  | cons ℓ ls ih =>
    intro h
    simp only [runPO] at h
    split_ifs at h with hen
    exact ih (hs.tail ⟨ℓ, hen, rfl⟩) h

section Example

/-- Abbreviations for the concrete instance: processes and objects `Fin 2`, values `ℕ`. -/
local notation "L2" => LblPO (Fin 2) (Fin 2) ℕ

private def st (p : Fin 2) : L2 := .base (.step p)

/-- The schedule of the counterexample. -/
def ceSchedule : List L2 :=
  -- p₀: O₀.CAS(0, 1): lines 7, 19, 20, 21 (skip), DurEC ECSC on Z₀: lines 6, 7, 8, 9, 10 (install)
  [.base (.invoke 0 0 (.cas 0 1)), st 0, st 0, st 0, st 0, st 0, st 0, st 0, st 0,
  -- p₀ crashes right after its install on Z₀
   .base (.crash 0),
  -- p₀ invokes O₁.CAS(0, 2) without recovering O₀; DurEC ECSC on Z₁ up to line 7: h.Val ← (2, 0)
   .postpone 0 1 (.cas 0 2), st 0, st 0, st 0, st 0, st 0,
  -- p₁: O₀.CAS(0, 1): its install fails (hitchhiker), its FORWARD moves h₀.Val = (2, 0) into Z₀;
  -- second iteration reads Z₀.val = 2 ≠ 0 and returns false
   .base (.invoke 1 0 (.cas 0 1)), st 1, st 1, st 1, st 1, st 1, st 1, st 1, st 1, st 1, st 1,
   st 1, st 1, st 1, st 1, st 1,
  -- p₁: O₀.READ returns 2
   .base (.invoke 1 0 .read), st 1]

/-- The history produced by the schedule. -/
def ceHist : List (Ev (Fin 2) (Fin 2) ℕ) :=
  [.inv 0 0 0 (.cas 0 1) 0, .crash 0, .inv 1 0 1 (.cas 0 2) 0, .inv 2 1 0 (.cas 0 1) 0,
   .ret 2 (.ok false) 0, .inv 3 1 0 .read 0, .ret 3 (.val 2) 0]

theorem ceSchedule_hist :
    (runPO (initSt (fun _ => 0) (fun _ => (0, false))) ceSchedule).map St.hist = some ceHist := by
  decide +kernel

/-- **Counterexample (per-object recovery discipline).** There is a reachable state whose history is
not durably linearizable: object `0` (initial value `0`) is read as `2`, although only `CAS(0, 1)`
operations were invoked on it. -/
theorem perObject_counterexample :
    ∃ s : St (Fin 2) (Fin 2) ℕ, ReachPO (fun _ => 0) (fun _ => (0, false)) s ∧
      ¬ DurLinearizable (fun _ => (0 : ℕ)) s.hist := by
  obtain ⟨s, hs, hh⟩ : ∃ s, runPO (initSt (fun _ => 0) (fun _ => (0, false))) ceSchedule = some s
      ∧ s.hist = ceHist := by
    have h := ceSchedule_hist
    cases hr : runPO (initSt (fun _ => 0) (fun _ => (0, false))) ceSchedule with
    | none => rw [hr] at h; simp at h
    | some s => rw [hr] at h; exact ⟨s, rfl, by simpa using h⟩
  refine ⟨s, reachPO_of_runPO Relation.ReflTransGen.refl _ hs, ?_⟩
  intro hDL
  rw [hh] at hDL
  have := read_val_of_durLin (id := 3) (k := 0) (v := 2) (d := 0) hDL
    ⟨1, 0, by simp [ceHist]⟩ (by simp [ceHist])
    (by rintro k' op' ⟨p, d, h⟩; simp [ceHist] at h; exact ⟨h.2.1, h.2.2.1⟩)
  simp [ceHist] at this

end Example

end Podc.DuraCAS
