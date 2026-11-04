import Mathlib
import Cslib.Computability.Distributed.SharedMemory.ObjClasses

-- CSLib candidate: shared memory with caller-aware, possibly blocking base objects; valency
-- toolkit (deciders, critical configurations, all processes poised on one object).

/-!
# The model: asynchronous shared memory with (possibly blocking) base objects

Imbs, Raynal, Taubenfeld. *On Asymmetric Progress Conditions.* PODC 2010 (full version:
IRISA research report PI-1952, May 2010, HAL inria-00486977). Section 2 and Section 3.3.

**Processes.** `n` deterministic, asynchronous processes `Fin n`. Process `p` starts in the local
state `A.init p x` determined by its (binary) input `x` — every process participates and
proposes its input (binary consensus, as in the proofs of the paper, Section 3.3). A crash is a
process that stops taking steps (crash-stop): executions are finite or infinite *schedules*
(sequences of process identifiers), and a process is correct in an infinite schedule iff it
occurs infinitely often.

**Base objects.** Objects are indexed by `ι`; object `i` is a `BObj n`: a deterministic,
*caller-aware* transition function `δ : State → Fin n → Op → State × Option Resp`. A response
`none` means that the object has taken the step of the caller but has not responded yet: the
caller stays poised on the same operation. Atomic objects (registers, wait-free consensus
objects, any linearizable wait-free object) always respond (`BObj.ofSpec` embeds a CSLib
sequential specification). Blocking responses are needed only to model the non-wait-free
`(n, x)`-live consensus base objects of Theorem 2 (`liveCons`).

**Algorithms.** A local state either outputs a value (`Act.out v`; steps in output states are
no-ops) or is poised to apply an operation `o` to object `i`, continuing with `k r` on response
`r` (`Act.access i o k`). Local computation is folded into the continuation.

**Correctness of an implementation of consensus** (`Safe`, `OFree`, `WFree`, `FFree`):
agreement and validity over all finite executions from initial configurations;
*obstruction-freedom* of `p` (from every reachable configuration, `p` running solo eventually
outputs); *wait-freedom* of `p` (in every infinite schedule in which `p` takes infinitely many
steps, `p` outputs); *fault-freedom* of `p` (in every infinite schedule in which every process
takes infinitely many steps, `p` outputs). An implementation is `(n, X)`-live (`Live A X`) if it
is safe, obstruction-free for every process and wait-free for the processes of `X`; the paper's
`(n, x)`-liveness is `Live A X` with `X.card = x`.
-/

namespace Podc.AsymmetricProgress

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

/-- A base object of an `n`-process system: a deterministic transition function that may depend
on the calling process and may withhold the response (`none`; the caller then stays poised on
the same operation). -/
structure BObj (n : ℕ) where
  /-- States of the object. -/
  State : Type
  /-- Operations. -/
  Op : Type
  /-- Responses. -/
  Resp : Type
  /-- The transition: new state and (possibly no) response. -/
  δ : State → Fin n → Op → State × Option Resp

namespace BObj

variable {n : ℕ}

/-- The atomic object with sequential specification `S`: it always responds and ignores the
identity of the caller. -/
def ofSpec (S : ObjSpec) : BObj n where
  State := S.State
  Op := S.Op
  Resp := S.Resp
  δ s _ o := ((S.δ s o).1, some (S.δ s o).2)

/-- *Read/write-like* objects: every operation is read-only (never changes the state) or a blind
overwrite (new state and response independent of the old state). Atomic read/write registers are
read/write-like (`BObj.register_rwLike`). -/
def RWLike (B : BObj n) : Prop :=
  ∀ o, (∀ s p, (B.δ s p o).1 = s) ∨ ∀ s s' p, B.δ s p o = B.δ s' p o

lemma ofSpec_rwLike {S : ObjSpec} (h : S.RWLike) : (ofSpec S : BObj n).RWLike := by
  intro o
  rcases h o with h | h
  · exact Or.inl fun s _ => h s
  · refine Or.inr fun s s' _ => ?_
    have := h s s'
    simp only [ofSpec, this]

/-- Atomic read/write registers are read/write-like. -/
lemma register_rwLike (V : Type) (v₀ : V) : (ofSpec (register V v₀) : BObj n).RWLike :=
  ofSpec_rwLike (Cslib.SharedMemory.register_rwLike V v₀)

end BObj

variable {n : ℕ} {ι : Type}

/-- What a process does in a local state: apply operation `o` to object `i` and continue with
`k r` on response `r`, or output `v`. -/
inductive Act (T : ι → BObj n) (L : Type) where
  /-- Apply `o` to object `i`, continue with `k r` on response `r`. -/
  | access (i : ι) (o : (T i).Op) (k : (T i).Resp → L)
  /-- Output (decide) `v`. -/
  | out (v : Bool)

/-- An `n`-process (binary consensus) algorithm using the base objects `T i`. -/
structure Alg (n : ℕ) (T : ι → BObj n) where
  /-- Local states. -/
  L : Type
  /-- Initial local state of `p` with input `x`. -/
  init : Fin n → Bool → L
  /-- The next action in a local state. -/
  act : L → Act T L
  /-- Initial states of the base objects. -/
  mem₀ : (i : ι) → (T i).State

variable {T : ι → BObj n}

/-- Configurations: local states and object states. -/
@[ext]
structure Cfg (A : Alg n T) where
  /-- Local states. -/
  loc : Fin n → A.L
  /-- States of the base objects. -/
  mem : (i : ι) → (T i).State

variable {A : Alg n T}

/-- `p` has output (decided) `v`. -/
def Cfg.Out (C : Cfg A) (p : Fin n) (v : Bool) : Prop := A.act (C.loc p) = .out v

/-- The object `p` is poised to access (`none` if `p` has output). -/
def Cfg.objOf (C : Cfg A) (p : Fin n) : Option ι :=
  match A.act (C.loc p) with
  | .access i _ _ => some i
  | .out _ => none

variable [DecidableEq ι]

/-- The next step of `p`. -/
def Cfg.step (C : Cfg A) (p : Fin n) : Cfg A :=
  match A.act (C.loc p) with
  | .access i o k =>
    { loc := (((T i).δ (C.mem i) p o).2).elim C.loc (fun r => Function.update C.loc p (k r))
      mem := Function.update C.mem i ((T i).δ (C.mem i) p o).1 }
  | .out _ => C

/-- The configuration reached from `C` by the schedule `σ`. -/
def run (C : Cfg A) (σ : List (Fin n)) : Cfg A := σ.foldl Cfg.step C

variable (A) in
/-- The initial configuration with inputs `x`. -/
def initCfg (x : Fin n → Bool) : Cfg A := ⟨fun p => A.init p (x p), A.mem₀⟩

/-- `C` is reachable: it is reached from some initial configuration by a finite schedule. -/
def Reachable (C : Cfg A) : Prop := ∃ x σ, C = run (initCfg A x) σ

/-- The first `t` steps of an infinite schedule. -/
def pre (e : ℕ → Fin n) (t : ℕ) : List (Fin n) := (List.range t).map e

variable (A) in
/-- Agreement and validity of binary consensus, over all finite executions. -/
def Safe : Prop :=
  (∀ x σ p q v w, (run (initCfg A x) σ).Out p v → (run (initCfg A x) σ).Out q w → v = w) ∧
  (∀ x σ p v, (run (initCfg A x) σ).Out p v → ∃ q, x q = v)

variable (A) in
/-- Obstruction-freedom for `p`: from every reachable configuration, `p` running alone long
enough outputs. -/
def OFree (p : Fin n) : Prop :=
  ∀ C : Cfg A, Reachable C → ∃ k v, (run C (List.replicate k p)).Out p v

variable (A) in
/-- Wait-freedom for `p`: in every infinite execution in which `p` takes infinitely many steps
(i.e. `p` is correct), `p` outputs. -/
def WFree (p : Fin n) : Prop :=
  ∀ x (e : ℕ → Fin n), (∀ M, ∃ t ≥ M, e t = p) →
    ∃ t v, (run (initCfg A x) (pre e t)).Out p v

variable (A) in
/-- Fault-freedom for `p`: in every infinite execution in which every process takes infinitely
many steps (all processes participate and none fails), `p` outputs. -/
def FFree (p : Fin n) : Prop :=
  ∀ x (e : ℕ → Fin n), (∀ q M, ∃ t ≥ M, e t = q) →
    ∃ t v, (run (initCfg A x) (pre e t)).Out p v

variable (A) in
/-- `A` implements an `(n, X)`-live consensus object: agreement, validity, obstruction-freedom
for all processes and wait-freedom for the processes in `X`. (The paper's `(n, x)`-liveness:
`X.card = x`.) -/
def Live (X : Set (Fin n)) : Prop :=
  Safe A ∧ (∀ p, OFree A p) ∧ ∀ p ∈ X, WFree A p

variable (A) in
/-- `A` accesses object `i` only through the ports `Y i`: in every reachable configuration, a
process poised on `i` is in `Y i`. -/
def RespectsPorts (Y : ι → Set (Fin n)) : Prop :=
  ∀ C : Cfg A, Reachable C → ∀ p i, C.objOf p = some i → p ∈ Y i

/-! ## Basic lemmas -/

@[simp] lemma run_nil (C : Cfg A) : run C [] = C := rfl

@[simp] lemma run_cons (C : Cfg A) (p : Fin n) (σ : List (Fin n)) :
    run C (p :: σ) = run (C.step p) σ := rfl

lemma run_append (C : Cfg A) (σ τ : List (Fin n)) : run C (σ ++ τ) = run (run C σ) τ := by
  simp [run, List.foldl_append]

lemma run_concat (C : Cfg A) (σ : List (Fin n)) (p : Fin n) :
    run C (σ ++ [p]) = (run C σ).step p := by
  simp [run_append]

lemma run_replicate_succ (C : Cfg A) (k : ℕ) (p : Fin n) :
    run C (List.replicate (k + 1) p) = (run C (List.replicate k p)).step p := by
  rw [List.replicate_succ', run_concat]

lemma step_of_access {C : Cfg A} {p : Fin n} {i : ι} {o : (T i).Op} {k : (T i).Resp → A.L}
    (h : A.act (C.loc p) = .access i o k) :
    C.step p = { loc := (((T i).δ (C.mem i) p o).2).elim C.loc
                    (fun r => Function.update C.loc p (k r))
                 mem := Function.update C.mem i ((T i).δ (C.mem i) p o).1 } := by
  unfold Cfg.step; rw [h]

lemma step_of_out {C : Cfg A} {p : Fin n} {v : Bool} (h : C.Out p v) : C.step p = C := by
  unfold Cfg.step; rw [show A.act (C.loc p) = .out v from h]

lemma step_loc_other (C : Cfg A) {p q : Fin n} (h : q ≠ p) : (C.step p).loc q = C.loc q := by
  unfold Cfg.step
  split
  · rename_i i o k _
    cases ((T i).δ (C.mem i) p o).2 <;> simp [Function.update_of_ne h]
  · rfl

lemma step_mem_other (C : Cfg A) {p : Fin n} {j : ι} (h : C.objOf p ≠ some j) :
    (C.step p).mem j = C.mem j := by
  unfold Cfg.step
  unfold Cfg.objOf at h
  split
  · rename_i i o k hi
    rw [hi] at h
    have : j ≠ i := fun hji => h (by simp [hji])
    simp [Function.update_of_ne this]
  · rfl

lemma objOf_step_other (C : Cfg A) {p q : Fin n} (h : q ≠ p) :
    (C.step p).objOf q = C.objOf q := by
  unfold Cfg.objOf; rw [step_loc_other C h]

lemma out_step_other {C : Cfg A} {p q : Fin n} (h : q ≠ p) {v : Bool} :
    (C.step p).Out q v ↔ C.Out q v := by
  unfold Cfg.Out; rw [step_loc_other C h]

lemma Cfg.Out.step {C : Cfg A} {p : Fin n} {v : Bool} (h : C.Out p v) (q : Fin n) :
    (C.step q).Out p v := by
  by_cases hq : p = q
  · subst hq; rwa [step_of_out h]
  · exact (out_step_other hq).2 h

/-- Outputs persist. -/
lemma Cfg.Out.run {C : Cfg A} {p : Fin n} {v : Bool} (h : C.Out p v) (σ : List (Fin n)) :
    (Podc.AsymmetricProgress.run C σ).Out p v := by
  induction σ generalizing C with
  | nil => exact h
  | cons q σ ih => exact ih (h.step q)

lemma Cfg.Out.unique {C : Cfg A} {p : Fin n} {v w : Bool} (hv : C.Out p v) (hw : C.Out p w) :
    v = w := by
  unfold Cfg.Out at hv hw
  rw [hv] at hw
  cases hw; rfl

lemma objOf_eq_none_iff {C : Cfg A} {p : Fin n} : C.objOf p = none ↔ ∃ v, C.Out p v := by
  unfold Cfg.objOf Cfg.Out
  split <;> simp_all

lemma objOf_eq_some_iff {C : Cfg A} {p : Fin n} {i : ι} :
    C.objOf p = some i ↔ ∃ o k, A.act (C.loc p) = .access i o k := by
  unfold Cfg.objOf
  split
  · rename_i i' o k h
    rw [h]
    constructor
    · rintro ⟨⟩; exact ⟨o, k, rfl⟩
    · rintro ⟨o', k', h'⟩; cases h'; rfl
  · rename_i v h
    rw [h]; simp

lemma Reachable.run {C : Cfg A} (h : Reachable C) (σ : List (Fin n)) :
    Reachable (Podc.AsymmetricProgress.run C σ) := by
  obtain ⟨x, τ, rfl⟩ := h
  exact ⟨x, τ ++ σ, by rw [run_append]⟩

lemma Reachable.step {C : Cfg A} (h : Reachable C) (p : Fin n) : Reachable (C.step p) :=
  h.run [p]

lemma reachable_initCfg (x : Fin n → Bool) : Reachable (initCfg A x) := ⟨x, [], rfl⟩

lemma Safe.agree (h : Safe A) {C : Cfg A} (hC : Reachable C) {p q : Fin n} {v w : Bool}
    (hv : C.Out p v) (hw : C.Out q w) : v = w := by
  obtain ⟨x, σ, rfl⟩ := hC
  exact h.1 x σ p q v w hv hw

lemma pre_zero (e : ℕ → Fin n) : pre e 0 = [] := rfl

lemma pre_succ (e : ℕ → Fin n) (t : ℕ) : pre e (t + 1) = pre e t ++ [e t] := by
  simp [pre, List.range_succ]

lemma length_pre (e : ℕ → Fin n) (t : ℕ) : (pre e t).length = t := by simp [pre]

lemma pre_add (e : ℕ → Fin n) (a b : ℕ) :
    pre e (a + b) = pre e a ++ pre (fun t => e (a + t)) b := by
  induction b with
  | zero => simp [pre]
  | succ b ih => rw [← Nat.add_assoc, pre_succ, ih, pre_succ, List.append_assoc]

/-- Outputs persist along an infinite schedule. -/
lemma out_pre_mono {C : Cfg A} {e : ℕ → Fin n} {t t' : ℕ} (h : t ≤ t') {p : Fin n} {v : Bool}
    (hv : (run C (pre e t)).Out p v) : (run C (pre e t')).Out p v := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pre_add, run_append]
  exact hv.run _

/-! ## Commuting steps -/

/-- Steps of two different processes that are not poised on the same object commute. -/
lemma step_comm (C : Cfg A) {p q : Fin n} (hpq : p ≠ q)
    (h : ∀ i, C.objOf p = some i → C.objOf q ≠ some i) :
    (C.step p).step q = (C.step q).step p := by
  rcases hp : A.act (C.loc p) with ⟨i, o, k⟩ | v
  · rcases hq : A.act (C.loc q) with ⟨j, o', k'⟩ | w
    · have hij : i ≠ j := by
        intro hij; subst hij
        exact h i (objOf_eq_some_iff.2 ⟨o, k, hp⟩) (objOf_eq_some_iff.2 ⟨o', k', hq⟩)
      have hq' : A.act ((C.step p).loc q) = .access j o' k' := by
        rw [step_loc_other C hpq.symm, hq]
      have hp' : A.act ((C.step q).loc p) = .access i o k := by
        rw [step_loc_other C hpq, hp]
      rw [step_of_access hq', step_of_access hp', step_of_access hp, step_of_access hq]
      simp only [Function.update_of_ne hij.symm, Function.update_of_ne hij]
      ext r
      · simp only
        cases h1 : ((T i).δ (C.mem i) p o).2 <;> cases h2 : ((T j).δ (C.mem j) q o').2 <;>
          simp [Function.update_comm hpq]
      · simp only
        rw [Function.update_comm hij]
    · rw [step_of_out (C := C) (show C.Out q w from hq),
        step_of_out (C := C.step p) (show (C.step p).Out q w by
          rw [Cfg.Out, step_loc_other C hpq.symm]; exact hq)]
  · rw [step_of_out (C := C) (show C.Out p v from hp),
      step_of_out (C := C.step q) (show (C.step q).Out p v by
        rw [Cfg.Out, step_loc_other C hpq]; exact hp)]

end Podc.AsymmetricProgress
