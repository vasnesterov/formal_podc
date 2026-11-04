import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Recoverable

/-!
# Recoverable consensus in shared memory (Golab, PODC 2019 BA / arXiv 1804.10597) — definitions

The model is CSLib's crash-recovery shared-memory model
(`Cslib.SharedMemory.Recoverable`: algorithms `Alg n T`, configurations `Cfg`, events
`Ev.step p` / `Ev.crash p`, deterministic `run`; binary consensus: inputs and outputs are `Bool`).
On top of it we define:

* `numCrashes α`, `AtMost f α`: the total number of crash events of an execution (the paper's
  parameter `f` counts the failures of *all* processes, footnote 3), and the set of executions
  with at most `f` crashes;
* `Outputs C α p v`: process `p` is in an output state with value `v` at some point of `α`;
* `SolvesP A Adm`: the paper's *recoverable consensus* (Section 2): agreement between
  **distinct** processes (as written in the paper), validity, and recoverable wait-freedom
  (as in CSLib's `Solves`). CSLib's `Solves` (agreement among all outputs, also of different
  incarnations of one process) implies it (`Solves.solvesP`); impossibility results are stated
  for `SolvesP` (stronger), algorithms are proved correct for `Solves` (stronger);
* `consObj V`: an atomic (sticky) consensus object: the first `propose v` fixes the decision,
  every `propose` returns it;
* the **simultaneous** (system-wide) crash-recovery model (Section 2): events `SEv.step p` and
  `SEv.crashAll` (resets the local states of all processes), `srun`, and `SolvesS A`
  (agreement, validity, recoverable wait-freedom).
-/

namespace Podc.RecoverableHierarchy

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ}

/-! ## Counting crashes -/

/-- Is `e` a crash event? -/
def Ev.isCrash : Ev n → Bool
  | .step _ => false
  | .crash _ => true

@[simp] lemma Ev.isCrash_step (p : Fin n) : Ev.isCrash (.step p) = false := rfl
@[simp] lemma Ev.isCrash_crash (p : Fin n) : Ev.isCrash (.crash p) = true := rfl

/-- The total number of crash events (of all processes) in `α`. -/
def numCrashes (α : List (Ev n)) : ℕ := α.countP Ev.isCrash

@[simp] lemma numCrashes_nil : numCrashes ([] : List (Ev n)) = 0 := rfl

@[simp] lemma numCrashes_append (α β : List (Ev n)) :
    numCrashes (α ++ β) = numCrashes α + numCrashes β := by
  simp [numCrashes, List.countP_append]

@[simp] lemma numCrashes_cons_step (p : Fin n) (α : List (Ev n)) :
    numCrashes (.step p :: α) = numCrashes α := by
  simp [numCrashes]

@[simp] lemma numCrashes_cons_crash (p : Fin n) (α : List (Ev n)) :
    numCrashes (.crash p :: α) = numCrashes α + 1 := by
  simp [numCrashes, List.countP_cons]

/-- The executions with at most `f` crash-recovery failures in total. -/
def AtMost (f : ℕ) (α : List (Ev n)) : Prop := numCrashes α ≤ f

/-! ## The paper's specification -/

/-- Process `p` is in an output state with value `v` at some configuration of the execution `α`
from `C` (including `C` itself): "`p` returns `v` in `α`". -/
def Outputs {A : Alg n T} (C : Cfg A) (α : List (Ev n)) (p : Fin n) (v : Bool) : Prop :=
  ∃ k ≤ α.length, (run C (α.take k)).Out p v

lemma Outputs.dec {A : Alg n T} {C : Cfg A} {α : List (Ev n)} {p : Fin n} {v : Bool}
    (h : Outputs C α p v) : Dec C α v := by
  obtain ⟨k, hk, hp⟩ := h
  exact ⟨k, hk, p, hp⟩

lemma Dec.exists_outputs {A : Alg n T} {C : Cfg A} {α : List (Ev n)} {v : Bool}
    (h : Dec C α v) : ∃ p, Outputs C α p v := by
  obtain ⟨k, hk, p, hp⟩ := h
  exact ⟨p, k, hk, hp⟩

variable (A : Alg n T) in
/-- **Recoverable consensus** as specified in Section 2 of the paper, on the admissible executions
`Adm`:
1. *agreement*: distinct processes never output different decisions;
2. *validity*: each decision is the input of some process;
3. *recoverable wait-freedom*: in every infinite execution whose prefixes are admissible, a
   process that takes infinitely many steps and does not crash after time `N` outputs at some
   time `≥ N` ("each time a process executes its algorithm from the beginning, it either returns a
   decision after a finite number of its own steps, or crashes").

Agreement is literally the paper's ("distinct processes"); CSLib's `Solves` additionally requires
agreement between outputs of the same process in different incarnations. -/
structure SolvesP (Adm : List (Ev n) → Prop) : Prop where
  agree : ∀ x γ, Adm γ → ∀ p q, p ≠ q → ∀ v w,
    Outputs (initCfg A x) γ p v → Outputs (initCfg A x) γ q w → v = w
  valid : ∀ x γ, Adm γ → ∀ v, Dec (initCfg A x) γ v → ∃ p, x p = v
  prog : ∀ x (e : ℕ → Ev n) p N, (∀ t, Adm (pre e t)) → (∀ M, ∃ t ≥ M, e t = .step p) →
    (∀ t ≥ N, e t ≠ .crash p) → ∃ t ≥ N, ∃ v, (run (initCfg A x) (pre e t)).Out p v

/-- CSLib's (stronger) specification implies the paper's. -/
lemma Solves.solvesP {A : Alg n T} {Adm : List (Ev n) → Prop} (h : Solves A Adm) :
    SolvesP A Adm where
  agree x γ hγ _ _ _ v w hv hw := h.agree x γ hγ v w hv.dec hw.dec
  valid := h.valid
  prog := h.prog

/-! ## Atomic consensus objects -/

/-- An atomic (sticky) consensus object over values `V`: the state is the decided value (`none`
before the first proposal); `propose v` decides `v` if undecided and returns the decision.
-- CSLib candidate (several papers define the same object). -/
abbrev consObj (V : Type) : ObjSpec where
  State := Option V
  Op := V
  Resp := V
  init := none
  δ s v := (some (s.getD v), s.getD v)

@[simp] lemma consObj_δ {V : Type} (s : Option V) (v : V) :
    (consObj V).δ s v = (some (s.getD v), s.getD v) := rfl

/-! ## Simultaneous (system-wide) crash-recovery failures -/

/-- Events of the simultaneous-failure model: a step of a process, or a system-wide crash that
resets the local states of all processes (shared objects are unaffected). -/
inductive SEv (n : ℕ) where
  /-- The next step of `p`. -/
  | step (p : Fin n)
  /-- A simultaneous crash of all processes (followed by recovery from their initial states). -/
  | crashAll
  deriving DecidableEq

/-- Apply an event of the simultaneous-failure model. -/
def snext {A : Alg n T} (C : Cfg A) : SEv n → Cfg A
  | .step p => C.stepP p
  | .crashAll => { C with loc := fun p => A.init p (C.inp p) }

/-- The configuration reached from `C` by the events `α` (simultaneous-failure model). -/
def srun {A : Alg n T} (C : Cfg A) (α : List (SEv n)) : Cfg A := α.foldl snext C

@[simp] lemma srun_nil {A : Alg n T} (C : Cfg A) : srun C [] = C := rfl

@[simp] lemma srun_cons {A : Alg n T} (C : Cfg A) (e : SEv n) (α : List (SEv n)) :
    srun C (e :: α) = srun (snext C e) α := rfl

lemma srun_append {A : Alg n T} (C : Cfg A) (α β : List (SEv n)) :
    srun C (α ++ β) = srun (srun C α) β := by
  simp [srun, List.foldl_append]

/-- Some process outputs `v` at some configuration of `α` from `C` (simultaneous model). -/
def SDec {A : Alg n T} (C : Cfg A) (α : List (SEv n)) (v : Bool) : Prop :=
  ∃ k ≤ α.length, ∃ p, (srun C (α.take k)).Out p v

/-- The first `t` events of an infinite event sequence (simultaneous model). -/
def spre (e : ℕ → SEv n) (t : ℕ) : List (SEv n) := (List.range t).map e

variable (A : Alg n T) in
/-- Recoverable consensus with simultaneous crash-recovery failures (arbitrarily many):
agreement (all outputs of an execution are equal, also those of different incarnations of one
process — stronger than the paper's agreement between distinct processes), validity and
recoverable wait-freedom. -/
structure SolvesS : Prop where
  agree : ∀ x γ v w, SDec (initCfg A x) γ v → SDec (initCfg A x) γ w → v = w
  valid : ∀ x γ v, SDec (initCfg A x) γ v → ∃ p, x p = v
  prog : ∀ x (e : ℕ → SEv n) p N, (∀ M, ∃ t ≥ M, e t = .step p) →
    (∀ t ≥ N, e t ≠ .crashAll) → ∃ t ≥ N, ∃ v, (srun (initCfg A x) (spre e t)).Out p v

end Podc.RecoverableHierarchy
