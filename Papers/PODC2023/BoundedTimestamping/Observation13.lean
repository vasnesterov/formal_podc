import Papers.PODC2023.BoundedTimestamping.Machine

/-!
# Observation 13 and Lemma 2 are false

Observation 13 claims that during one `updateTS()` call a process increments `Counter` at most
six times, and Lemma 2 that a process incrementing `Counter` `i` times completes at least
`⌈i/6⌉ - 1` `helpActiveCluster()` calls in that interval (via Lemma 14: at most 6 increments
between consecutive `helpActiveCluster()` calls). The proof of Observation 13 overlooks that
`helpSystem()` (line 5) may call `isEarlier()` (line 18), which calls `helpUpdateTS()` twice
(lines 36, 38) *before* its own `helpActiveCluster()` (line 39). So before its first
`helpActiveCluster()` an `updateTS()` may run four `helpUpdateTS()` calls — up to 12
increments.

Concrete execution (`n = 4`, `κ = 3`, `obsLabels`, 177 labels): process `0` invokes
`isEarlier(2, 2)` and stops after announcing it (line 41); process `2` starts an `updateTS()`;
process `1` runs `updateTS()`: one increment for itself, then in `helpSystem()` (`helpID = 0`) it
finds the announcement and calls `isEarlier(2, 2)`, whose two `helpUpdateTS(2)` calls each
increment `Counter` three times, because after each of process `1`'s `FAI()`s process `2`
completes its `updateTS()` and starts a new one. Process `1` performs 7 increments within one
`updateTS()` call, without having started any `helpActiveCluster()` call.

This is a gap in the proofs of Lemmas 21 and 33 (which use Lemma 2 with the constants
`ζ = 6n + 2` and `μ = 6n³ + 6n² + 2`), not by itself a counterexample to the algorithm.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.BoundedTS

open Cslib.SharedMemory

section Count

variable (n κ : ℕ) [NeZero n]

/-- Number of internal steps of `p` in `α` (from configuration `C`) taken in a local state
satisfying `f`. -/
noncomputable def countSteps (f : Loc → Bool) (p : Fin n) :
    Config (mtsObj n) (Base n) (Fin n) Loc → List (Label (Fin n) (mtsObj n)) → ℕ
  | _, [] => 0
  | C, ℓ :: α =>
    match (alg n κ).step C ℓ with
    | none => 0
    | some C' =>
      (match ℓ with
       | .tau q => if q = p ∧ f (C.loc p) = true then 1 else 0
       | _ => 0) + countSteps f p C' α

/-- `countSteps` on `MState`s. -/
def ccount (f : Loc → Bool) (p : Fin n) : MState n → List (Label (Fin n) (mtsObj n)) → ℕ
  | _, [] => 0
  | s, ℓ :: α =>
    match cstep n κ s ℓ with
    | none => 0
    | some s' =>
      (match ℓ with
       | .tau q => if q = p ∧ f (s.loc.getD p (locInit n)) = true then 1 else 0
       | _ => 0) + ccount f p s' α

lemma countSteps_toCfg (f : Loc → Bool) (p : Fin n) {s : MState n} (hs : s.WF)
    (α : List (Label (Fin n) (mtsObj n))) :
    countSteps n κ f p (toCfg n s) α = ccount n κ f p s α := by
  induction α generalizing s with
  | nil => rfl
  | cons ℓ α ih =>
    simp only [countSteps, ccount, step_toCfg n κ hs]
    cases h : cstep n κ s ℓ with
    | none => rfl
    | some s' =>
      simp only [Option.map_some]
      rw [ih (cstep_wf n κ hs h)]
      rfl

end Count

/-- The local state is about to apply `Counter.FAI()`. -/
def isFAI {n : ℕ} [NeZero n] : Action (mtsObj n) (Base n) Loc → Bool
  | .access .ctr .fai _ => true
  | _ => false
def tausUntil (n κ : ℕ) [NeZero n] (p : Fin n) (pred : Loc → Bool) : ℕ → MState n → Option (MState n × List (Label (Fin n) (mtsObj n)))
  | 0, _ => none
  | f+1, s => if pred (s.loc.getD p (locInit n)) then some (s, []) else
     match cstep n κ s (.tau p) with
     | some s' => (tausUntil n κ p pred f s').map (fun x => (x.1, .tau p :: x.2))
     | none => none
/-- run x's pending update to completion and start a new one (2 steps) -/
def xRestart (s : MState 4) : Option (MState 4 × List (Label (Fin 4) (mtsObj 4))) := do
  let (s, k) ← runTaus 4 3 2 1000 s
  let r ← nextRet 4 3 s 2
  let s ← cstep 4 3 s (.ret 2 r)
  let s ← cstep 4 3 s (.inv 2 (.upd 2))
  let s ← cstep 4 3 s (.tau 2)
  let s ← cstep 4 3 s (.tau 2)
  return (s, List.replicate k (.tau 2) ++ [.ret 2 r, .inv 2 (.upd 2), .tau 2, .tau 2])
/-- p steps; after each FAI step targeting 2, x restarts; stop after `m` FAIs -/
def pLoop : ℕ → ℕ → MState 4 → Option (MState 4 × List (Label (Fin 4) (mtsObj 4)))
  | 0, _, s => some (s, [])
  | f+1, m, s =>
    if m = 0 then some (s, []) else
    let l := s.loc.getD 1 (locInit 4)
    let fai := isFAI (act 4 3 1 l)
    match cstep 4 3 s (.tau 1) with
    | none => none
    | some s' =>
      if fai then
        if l.hid = 2 then
          match xRestart s' with
          | none => none
          | some (s'', ls) => (pLoop f (m-1) s'').map (fun x => (x.1, .tau 1 :: ls ++ x.2))
        else (pLoop f (m-1) s').map (fun x => (x.1, .tau 1 :: x.2))
      else (pLoop f m s').map (fun x => (x.1, .tau 1 :: x.2))
def obsExec : Option (List (Label (Fin 4) (mtsObj 4))) := do
  let s0 := initMS 4
  let s ← cstep 4 3 s0 (.inv 0 (.ie 2 2))
  let (s, l1) ← tausUntil 4 3 0 (fun l => l.pc == PC.E42) 1000 s
  let s ← cstep 4 3 s (.inv 2 (.upd 2))
  let s ← cstep 4 3 s (.tau 2)
  let s ← cstep 4 3 s (.tau 2)
  let s ← cstep 4 3 s (.inv 1 (.upd 1))
  let (_, l2) ← pLoop 1000 7 s
  return [.inv 0 (.ie 2 2)] ++ l1 ++ [.inv 2 (.upd 2), .tau 2, .tau 2, .inv 1 (.upd 1)] ++ l2

/-- The execution described in the module docstring. -/
def obsLabels : List (Label (Fin 4) (mtsObj 4)) := obsExec.getD []

theorem obsLabels_run : (crun 4 3 (initMS 4) obsLabels).isSome = true := by decide +kernel

theorem obsLabels_facts :
    opsOf obsLabels 1 = [MOp.upd 1] ∧
    ccount 4 3 (fun l => isFAI (act 4 3 1 l)) 1 (initMS 4) obsLabels = 7 ∧
    ccount 4 3 (fun l => l.pc == PC.R26 && l.rit == 0) 1 (initMS 4) obsLabels = 0 := by
  decide +kernel

/-- **Observation 13 and Lemma 2 of [BJW23] are false.** In some execution of the algorithm
(`n = 4`, `κ = 3`), process `1` invokes a single operation, `updateTS()`, and executes
`Counter.FAI()` seven times while it has not started any `helpActiveCluster()` call
(a call starts with line 26 in its first iteration). Observation 13 bounds the number of
increments per call by 6; Lemma 2 (with `i = 7`) requires `⌈7/6⌉ - 1 = 1` completed
`helpActiveCluster()` call in this interval. -/
theorem observation13_false : ∃ α C, (alg 4 3).run α = some C ∧ opsOf α 1 = [MOp.upd 1] ∧
    countSteps 4 3 (fun l => isFAI (act 4 3 1 l)) 1 (alg 4 3).initCfg α = 7 ∧
    countSteps 4 3 (fun l => l.pc == PC.R26 && l.rit == 0) 1 (alg 4 3).initCfg α = 0 := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 obsLabels_run
  obtain ⟨h1, h2, h3⟩ := obsLabels_facts
  refine ⟨obsLabels, toCfg 4 s, ?_, h1, ?_, ?_⟩
  · rw [Impl.run, ← toCfg_initMS 4 3, runFrom_toCfg 4 3 (initMS_wf 4), hs]; rfl
  · rw [← toCfg_initMS 4 3, countSteps_toCfg 4 3 _ _ (initMS_wf 4)]; exact h2
  · rw [← toCfg_initMS 4 3, countSteps_toCfg 4 3 _ _ (initMS_wf 4)]; exact h3

end Cslib.SharedMemory.BoundedTS
