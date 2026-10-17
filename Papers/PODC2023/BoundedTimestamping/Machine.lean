import Papers.PODC2023.BoundedTimestamping.Alg
import Cslib.Computability.Distributed.SharedMemory.Sequential

/-!
# A computable copy of `alg n κ` for evaluating concrete executions

`Impl.step` is noncomputable and stores memory and local states as functions, so long concrete
executions cannot be evaluated by the kernel. `MState` stores everything in lists; `cstep`
mirrors `Impl.step` and `step_toCfg` proves that it computes the same configurations.
`runScript` runs a list of operations, each solo to completion, and returns the history
`H` with `seqExec H` a valid execution of `alg n κ` (`valid_of_runScript`).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.BoundedTS

open Cslib.SharedMemory

/-- A configuration of `alg n κ` in list form. -/
structure MState (n : ℕ) where
  loc : List Loc
  pend : List (Option (MOp n))
  A : List Bool
  TS : List (TSVal × List (Fin n))
  LT : List (LTVal n × List (Fin n))
  ctr : ℕ

section Machine

variable (n κ : ℕ) [NeZero n]

/-- Initial value of `LookupTable[i]`. -/
def ltInit : LTVal n := ⟨0, 0, some true⟩

namespace MState

variable {n}

/-- Memory of an `MState`. -/
def getMem (s : MState n) : (i : Obj n) → (Base n i).State
  | .A j => s.A.getD j false
  | .TS j => s.TS.getD j (tsInit, [])
  | .LT j => s.LT.getD j (ltInit n, [])
  | .ctr => s.ctr

/-- Update one base object. -/
def setMem (s : MState n) : (i : Obj n) → (Base n i).State → MState n
  | .A j, v => { s with A := s.A.set j v }
  | .TS j, v => { s with TS := s.TS.set j v }
  | .LT j, v => { s with LT := s.LT.set j v }
  | .ctr, v => { s with ctr := v }

/-- All lists have length `n`. -/
def WF (s : MState n) : Prop :=
  s.loc.length = n ∧ s.pend.length = n ∧ s.A.length = n ∧ s.TS.length = n ∧ s.LT.length = n

end MState

/-- The configuration represented by an `MState`. -/
def toCfg (s : MState n) : Config (mtsObj n) (Base n) (Fin n) Loc where
  loc p := s.loc.getD p (locInit n)
  pend p := s.pend.getD p none
  mem := s.getMem

/-- The initial `MState`. -/
def initMS : MState n where
  loc := List.replicate n (locInit n)
  pend := List.replicate n none
  A := List.replicate n false
  TS := List.replicate n (tsInit, [])
  LT := List.replicate n (ltInit n, [])
  ctr := 0

/-- Decidable version of `allowedOp`. -/
def allowedB (p : Fin n) : MOp n → Bool
  | .upd q => decide (q = p) && decide (p.val ≠ n - 1)
  | .ie _ _ => true

/-- `Impl.step` of `alg n κ` on `MState`s. -/
def cstep (s : MState n) : Label (Fin n) (mtsObj n) → Option (MState n)
  | .inv p o =>
    if (s.pend.getD p none).isNone && allowedB n p o then
      some { s with pend := s.pend.set p (some o),
                    loc := s.loc.set p (invoke n (s.loc.getD p (locInit n)) o) }
    else none
  | .tau p =>
    if (s.pend.getD p none).isNone then none else
    match act n κ p (s.loc.getD p (locInit n)) with
    | .access i o k =>
      let r := (Base n i).δ (s.getMem i) o
      some { s.setMem i r.1 with loc := s.loc.set p (k r.2) }
    | .ret _ _ => none
  | .ret p r =>
    if (s.pend.getD p none).isNone then none else
    match act n κ p (s.loc.getD p (locInit n)) with
    | .access _ _ _ => none
    | .ret r' l =>
      if r = r' then some { s with pend := s.pend.set p none, loc := s.loc.set p l } else none

/-- Run a list of labels. -/
def crun (s : MState n) : List (Label (Fin n) (mtsObj n)) → Option (MState n)
  | [] => some s
  | ℓ :: α => (cstep n κ s ℓ).bind (fun s' => crun s' α)

/-- Internal steps of `p` until its next action is a response (at most `fuel` steps);
returns the state and the number of steps. -/
def runTaus (p : Fin n) : ℕ → MState n → Option (MState n × ℕ)
  | 0, _ => none
  | fuel + 1, s =>
    match act n κ p (s.loc.getD p (locInit n)) with
    | .ret _ _ => some (s, 0)
    | .access _ _ _ =>
      match cstep n κ s (.tau p) with
      | some s' => (runTaus p fuel s').map (fun x => (x.1, x.2 + 1))
      | none => none

/-- The pending response of `p`, if its next action is a response. -/
def nextRet (s : MState n) (p : Fin n) : Option (Option Bool) :=
  match act n κ p (s.loc.getD p (locInit n)) with
  | .ret r _ => some r
  | .access _ _ _ => none

/-- Run operation `o` of process `p` solo to completion. -/
def soloOp (s : MState n) (p : Fin n) (o : MOp n) (fuel : ℕ) :
    Option (MState n × (Fin n × MOp n × Option Bool × ℕ)) := do
  let s₁ ← cstep n κ s (.inv p o)
  let (s₂, k) ← runTaus n κ p fuel s₁
  let r ← nextRet n κ s₂ p
  let s₃ ← cstep n κ s₂ (.ret p r)
  return (s₃, (p, o, r, k))

/-- Run a script of operations, each solo to completion; returns the final state and the
history. -/
def runScript (fuel : ℕ) : MState n → List (Fin n × MOp n) →
    Option (MState n × List (Fin n × MOp n × Option Bool × ℕ))
  | s, [] => some (s, [])
  | s, (p, o) :: sc => do
    let (s₁, h) ← soloOp n κ s p o fuel
    let (s₂, H) ← runScript fuel s₁ sc
    return (s₂, h :: H)


/-! ### `cstep` computes `Impl.step` -/

lemma getD_set_fun {α : Type} (l : List α) (hl : l.length = n) (p : Fin n) (v d : α) :
    (fun q : Fin n => (l.set p v).getD q d) = Function.update (fun q : Fin n => l.getD q d) p v := by
  funext q
  by_cases h : q = p
  · subst h; simp [List.getD_eq_getElem?_getD, hl]
  · rw [Function.update_of_ne h]
    have : (p : ℕ) ≠ q := fun e => h (Fin.ext e.symm)
    simp [List.getD_eq_getElem?_getD, this]

namespace MState

variable {n}

lemma getMem_setMem (s : MState n) (hs : s.WF) (i : Obj n) (v : (Base n i).State) :
    (s.setMem i v).getMem = Function.update s.getMem i v := by
  obtain ⟨-, -, hA, hT, hL⟩ := hs
  funext j
  cases i with
  | A a =>
    cases j with
    | A b =>
      by_cases h : b = a
      · subst h; simp [setMem, getMem, List.getD_eq_getElem?_getD, hA]
      · rw [Function.update_of_ne (by simp [h])]
        have : (a : ℕ) ≠ b := fun e => h (Fin.ext e.symm)
        simp [setMem, getMem, List.getD_eq_getElem?_getD, this]
    | _ => rw [Function.update_of_ne (by simp)]; rfl
  | TS a =>
    cases j with
    | TS b =>
      by_cases h : b = a
      · subst h; simp [setMem, getMem, List.getD_eq_getElem?_getD, hT]
      · rw [Function.update_of_ne (by simp [h])]
        have : (a : ℕ) ≠ b := fun e => h (Fin.ext e.symm)
        simp [setMem, getMem, List.getD_eq_getElem?_getD, this]
    | _ => rw [Function.update_of_ne (by simp)]; rfl
  | LT a =>
    cases j with
    | LT b =>
      by_cases h : b = a
      · subst h; simp [setMem, getMem, List.getD_eq_getElem?_getD, hL]
      · rw [Function.update_of_ne (by simp [h])]
        have : (a : ℕ) ≠ b := fun e => h (Fin.ext e.symm)
        simp [setMem, getMem, List.getD_eq_getElem?_getD, this]
    | _ => rw [Function.update_of_ne (by simp)]; rfl
  | ctr =>
    cases j with
    | ctr => simp [setMem, getMem]
    | _ => rw [Function.update_of_ne (by simp)]; rfl

lemma WF.setMem {s : MState n} (hs : s.WF) (i : Obj n) (v : (Base n i).State) :
    (s.setMem i v).WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  cases i <;> simp [MState.setMem, WF, *]

@[simp] lemma setMem_loc (s : MState n) (i : Obj n) (v : (Base n i).State) :
    (s.setMem i v).loc = s.loc := by cases i <;> rfl

@[simp] lemma setMem_pend (s : MState n) (i : Obj n) (v : (Base n i).State) :
    (s.setMem i v).pend = s.pend := by cases i <;> rfl

lemma WF.with_loc {s : MState n} (hs : s.WF) (l : List Loc) (hl : l.length = n) :
    ({ s with loc := l } : MState n).WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs; exact ⟨hl, h2, h3, h4, h5⟩

end MState

lemma allowedB_iff (p : Fin n) (o : MOp n) : allowedB n p o = true ↔ allowedOp n p o := by
  cases o <;> simp [allowedB, allowedOp]

lemma cstep_wf {s s' : MState n} (hs : s.WF) {ℓ : Label (Fin n) (mtsObj n)}
    (h : cstep n κ s ℓ = some s') : s'.WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  cases ℓ with
  | inv p o =>
    simp only [cstep] at h; split_ifs at h; cases h; simp [MState.WF, *]
  | tau p =>
    simp only [cstep] at h; split_ifs at h
    split at h
    · cases h
      exact (MState.WF.setMem ⟨h1, h2, h3, h4, h5⟩ _ _).with_loc _ (by simp [h1])
    · cases h
  | ret p r =>
    simp only [cstep] at h; split_ifs at h
    split at h
    · cases h
    · split_ifs at h; cases h; simp [MState.WF, *]

lemma step_toCfg {s : MState n} (hs : s.WF) (ℓ : Label (Fin n) (mtsObj n)) :
    (alg n κ).step (toCfg n s) ℓ = (cstep n κ s ℓ).map (toCfg n) := by
  have hs' := hs
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs'
  have e : ∀ p : Fin n, (alg n κ).act p ((toCfg n s).loc p) = act n κ p (s.loc.getD p (locInit n)) :=
    fun _ => rfl
  have ep : ∀ p : Fin n, (toCfg n s).pend p = s.pend.getD p none := fun _ => rfl
  cases ℓ with
  | inv p o =>
    dsimp only [Impl.step, cstep]
    have key : ((s.pend.getD p none).isNone && allowedB n p o) = true ↔
        ((toCfg n s).pend p = none ∧ (alg n κ).allowed p o) := by
      rw [ep, Bool.and_eq_true, allowedB_iff, Option.isNone_iff_eq_none]; rfl
    by_cases hc : ((s.pend.getD p none).isNone && allowedB n p o) = true
    · rw [ite_eq_left (key.1 hc), ite_eq_left hc]
      simp only [Option.map_some, toCfg, Option.some.injEq, Config.mk.injEq]
      exact ⟨(getD_set_fun n _ h1 _ _ _).symm, (getD_set_fun n _ h2 _ _ _).symm, rfl⟩
    · rw [ite_eq_right (fun h => hc (key.2 h)),
        ite_eq_right hc]; rfl
  | tau p =>
    dsimp only [Impl.step, cstep]
    rw [e p, ep p]
    by_cases hc : s.pend.getD p none = none
    · simp only [List.getD_eq_getElem?_getD] at hc; simp [hc]
    · have hc' : ¬ (s.pend.getD p none).isNone = true := by simpa using hc
      rw [ite_eq_right hc, ite_eq_right hc']
      generalize act n κ p (s.loc.getD p (locInit n)) = a
      cases a with
      | access i o k =>
        simp only [Option.map_some, toCfg, Option.some.injEq, Config.mk.injEq]
        refine ⟨?_, by simp, ?_⟩
        · exact (getD_set_fun n _ h1 _ _ _).symm
        · exact (MState.getMem_setMem s hs _ _).symm
      | ret r l => rfl
  | ret p r =>
    dsimp only [Impl.step, cstep]
    rw [e p, ep p]
    by_cases hc : s.pend.getD p none = none
    · simp only [List.getD_eq_getElem?_getD] at hc; simp [hc]
    · have hc' : ¬ (s.pend.getD p none).isNone = true := by simpa using hc
      rw [ite_eq_right hc, ite_eq_right hc']
      generalize act n κ p (s.loc.getD p (locInit n)) = a
      cases a with
      | access i o k => rfl
      | ret r' l =>
        by_cases hr : r = r'
        · subst hr
          simp only [ite_true, Option.map_some, toCfg, Option.some.injEq, Config.mk.injEq]
          exact ⟨(getD_set_fun n _ h1 _ _ _).symm, (getD_set_fun n _ h2 _ _ _).symm, rfl⟩
        · simp only [hr, ite_false, Option.map_none]

lemma runFrom_toCfg {s : MState n} (hs : s.WF) (α : List (Label (Fin n) (mtsObj n))) :
    (alg n κ).runFrom (toCfg n s) α = (crun n κ s α).map (toCfg n) := by
  induction α generalizing s with
  | nil => rfl
  | cons ℓ α ih =>
    simp only [Impl.runFrom_cons, crun, step_toCfg n κ hs]
    cases h : cstep n κ s ℓ with
    | none => rfl
    | some s' => exact ih (cstep_wf n κ hs h)

lemma crun_wf {s s' : MState n} (hs : s.WF) {α : List (Label (Fin n) (mtsObj n))}
    (h : crun n κ s α = some s') : s'.WF := by
  induction α generalizing s with
  | nil => cases h; exact hs
  | cons ℓ α ih =>
    simp only [crun] at h
    cases h' : cstep n κ s ℓ with
    | none => simp [h'] at h
    | some s₁ => simp only [h', Option.bind_some] at h; exact ih (cstep_wf n κ hs h') h

lemma crun_append (s : MState n) (α β : List (Label (Fin n) (mtsObj n))) :
    crun n κ s (α ++ β) = (crun n κ s α).bind (fun s' => crun n κ s' β) := by
  induction α generalizing s with
  | nil => rfl
  | cons ℓ α ih =>
    simp only [List.cons_append, crun, ih]
    cases cstep n κ s ℓ <;> simp

lemma runTaus_spec (p : Fin n) {fuel : ℕ} {s s' : MState n} {k : ℕ}
    (h : runTaus n κ p fuel s = some (s', k)) :
    crun n κ s (List.replicate k (.tau p)) = some s' := by
  induction fuel generalizing s k with
  | zero => simp [runTaus] at h
  | succ fuel ih =>
    simp only [runTaus] at h
    split at h
    · cases h; rfl
    · split at h
      · rename_i s₁ hs₁
        cases h' : runTaus n κ p fuel s₁ with
        | none => simp [h'] at h
        | some x =>
          obtain ⟨t, m⟩ := x
          simp only [h', Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [List.replicate_succ, crun, hs₁, Option.bind_some]
          exact ih h'
      · cases h

lemma soloOp_spec {s s' : MState n} {p : Fin n} {o : MOp n} {fuel : ℕ}
    {x : Fin n × MOp n × Option Bool × ℕ} (h : soloOp n κ s p o fuel = some (s', x)) :
    crun n κ s (segLabels x) = some s' := by
  simp only [soloOp, Option.bind_eq_bind] at h
  cases h1 : cstep n κ s (.inv p o) with
  | none => simp [h1] at h
  | some s₁ =>
    simp only [h1, Option.bind_some] at h
    cases h2 : runTaus n κ p fuel s₁ with
    | none => simp [h2] at h
    | some y =>
      obtain ⟨s₂, k⟩ := y
      simp only [h2, Option.bind_some] at h
      cases h3 : nextRet n κ s₂ p with
      | none => simp [h3] at h
      | some r =>
        simp only [h3, Option.bind_some] at h
        cases h4 : cstep n κ s₂ (.ret p r) with
        | none => simp [h4] at h
        | some s₃ =>
          simp only [h4, Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [segLabels, crun, h1, Option.bind_some, crun_append, runTaus_spec n κ p h2,
            h4]

lemma runScript_spec {fuel : ℕ} {sc : List (Fin n × MOp n)} {s s' : MState n}
    {H : List (Fin n × MOp n × Option Bool × ℕ)} (h : runScript n κ fuel s sc = some (s', H)) :
    crun n κ s (seqExec H) = some s' := by
  induction sc generalizing s s' H with
  | nil => simp only [runScript, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | cons po sc ih =>
    obtain ⟨p, o⟩ := po
    simp only [runScript, Option.bind_eq_bind] at h
    cases h1 : soloOp n κ s p o fuel with
    | none => simp [h1] at h
    | some y =>
      obtain ⟨s₁, x⟩ := y
      simp only [h1, Option.bind_some] at h
      cases h2 : runScript n κ fuel s₁ sc with
      | none => simp [h2] at h
      | some z =>
        obtain ⟨s₂, H'⟩ := z
        simp only [h2, Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [seqExec, List.flatMap_cons, crun_append]
        rw [soloOp_spec n κ h1, Option.bind_some]
        exact ih h2

lemma initMS_wf : (initMS n).WF := by simp [MState.WF, initMS]

lemma toCfg_initMS : toCfg n (initMS n) = (alg n κ).initCfg := by
  simp only [toCfg, Impl.initCfg, alg, Config.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext p; simp [initMS, List.getD_eq_getElem?_getD]
  · funext p; simp [initMS, List.getD_eq_getElem?_getD]
  · funext i
    cases i <;> simp [initMS, MState.getMem, memInit, List.getD_eq_getElem?_getD,
      ltInit]

/-- An execution accepted by the computable machine is a valid execution of `alg n κ`. -/
theorem valid_of_crun {α : List (Label (Fin n) (mtsObj n))} {s : MState n}
    (h : crun n κ (initMS n) α = some s) : (alg n κ).Valid α := by
  refine ⟨toCfg n s, ?_⟩
  rw [Impl.run, ← toCfg_initMS n κ, runFrom_toCfg n κ (initMS_wf n), h]
  rfl

/-- A successful script run yields a valid sequential execution of `alg n κ`. -/
theorem valid_of_runScript {fuel : ℕ} {sc : List (Fin n × MOp n)} {s : MState n}
    {H : List (Fin n × MOp n × Option Bool × ℕ)} (h : runScript n κ fuel (initMS n) sc = some (s, H)) :
    (alg n κ).Valid (seqExec H) := by
  refine ⟨toCfg n s, ?_⟩
  rw [Impl.run, ← toCfg_initMS n κ, runFrom_toCfg n κ (initMS_wf n), runScript_spec n κ h]
  rfl

end Machine

end Cslib.SharedMemory.BoundedTS
