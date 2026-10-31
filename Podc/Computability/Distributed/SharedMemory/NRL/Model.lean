import Mathlib
import Cslib.Computability.Distributed.SharedMemory.LinPoints

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/NRL/Model.lean

/-!
# Individual crash-recovery on non-volatile memory; nesting-safe recoverable linearizability

The model of Attiya, Ben-Baruch and Hendler (PODC 2018, "Nesting-safe recoverable
linearizability") for one implemented recoverable object `O` built from atomic base objects
(primitives), with *individual* process crashes:

* shared memory is non-volatile: base objects `T i` keep their state across crashes;
* a process's local state is a program location `pc : PC` plus volatile variables `v : V`;
* a crash of a process `p` with a pending operation `o` erases its volatile variables and the
  system restarts `p` in `Op.Recover` — `recover p o li` — where `li` is the location `p` was
  about to execute when it crashed (the paper's non-volatile `LI_p`). The arguments `o` of the
  crashed operation are passed to the recovery code again;
* a step of a running process is an access to one base object (`Act.access`: the response is
  stored into the volatile variables, the next location does not depend on it), an internal step
  (`Act.internal`) or the response of the implemented operation (`Act.ret`).

A crash and the matching recovery step are one event `Ev.crash p` (the time between a crash and
the recovery of `p` is indistinguishable from `p` being slow); a crash of an idle process has no
effect. The full history `Cfg.hist` records invocations, responses, crashes and recoveries
(`HStep`); `N H` is the history without crash and recovery steps, a CSLib `Label` history.

Main definitions:
* `Alg P O`, `Cfg`, `Ev`, `Cfg.ev`, `Cfg.run`, `Alg.init`;
* `RecWellFormed` (Definition 3), `HistNRL` (Definition 4), `Alg.NRL Env` (all finite histories
  whose crash-free projection satisfies the environment assumption `Env` satisfy NRL);
* `Alg.WaitFree Env`: a process that takes infinitely many steps and does not crash any more
  eventually completes its operation (wait-free operations *and* wait-free recovery functions).

Main statement: `recWellFormed_run` (Lemma 1 of the paper for one implemented object: every
history of the model is recoverable well-formed), so `Alg.nrl_iff` reduces NRL to the
linearizability of `N H`.
-/

namespace Cslib.SharedMemory.NRL

open Cslib.SharedMemory

/-- What a process does next. -/
inductive Act {ι : Type} (T : ι → ObjSpec) (PC V R : Type) where
  /-- Apply operation `o` to base object `i`, continue at location `pc` with the volatile
  variables `v r` (`r` = the response of the primitive). -/
  | access (i : ι) (o : (T i).Op) (pc : PC) (v : (T i).Resp → V)
  /-- An internal step (no shared-memory access). -/
  | internal (pc : PC) (v : V)
  /-- Return `r` from the implemented operation. -/
  | ret (r : R)

/-- An implementation of a recoverable object `O` from base objects `T i` (initially in their
initial states `(T i).init`), for processes `P`. -/
structure Alg (P : Type) (O : ObjSpec) where
  /-- Names of base objects. -/
  ι : Type
  /-- Base objects (atomic primitives). -/
  T : ι → ObjSpec
  /-- Program locations (instruction labels). -/
  PC : Type
  /-- Volatile local variables. -/
  V : Type
  /-- Location and variables of `p` when it invokes `o`. -/
  start : P → O.Op → PC × V
  /-- Location and variables of `p` when the system invokes `o.Recover` after a crash that
  happened when `p` was about to execute location `li` (the paper's `LI_p`). -/
  recover : P → O.Op → PC → PC × V
  /-- The next action of `p`, running operation `o`, at location `pc` with variables `v`. -/
  act : P → O.Op → PC → V → Act T PC V O.Resp

variable {P : Type} {O : ObjSpec} [DecidableEq P]

/-- Steps of a (full) history: invocation, response, crash and recovery steps. -/
inductive HStep (P : Type) (O : ObjSpec) where
  | inv (p : P) (o : O.Op)
  | res (p : P) (r : O.Resp)
  | crash (p : P)
  | recover (p : P)

namespace HStep

/-- The process of a history step. -/
def proc : HStep P O → P
  | inv p _ => p
  | res p _ => p
  | crash p => p
  | recover p => p

/-- Invocation and response steps as CSLib labels; crash and recovery steps are dropped. -/
def toLabel : HStep P O → Option (Label P O)
  | inv p o => some (.inv p o)
  | res p r => some (.ret p r)
  | crash _ => none
  | recover _ => none

end HStep

/-- `N(H)`: the history `H` without its crash and recovery steps. -/
def N (H : List (HStep P O)) : List (Label P O) := H.filterMap HStep.toLabel

@[simp] lemma N_nil : N ([] : List (HStep P O)) = [] := rfl

@[simp] lemma N_append (H H' : List (HStep P O)) : N (H ++ H') = N H ++ N H' := by
  simp [N, List.filterMap_append]

@[simp] lemma N_inv (p : P) (o : O.Op) : N [HStep.inv p o] = [Label.inv p o] := rfl
@[simp] lemma N_res (p : P) (r : O.Resp) : N [HStep.res p r] = [Label.ret p r] := rfl
@[simp] lemma N_crash_rec (p : P) : N [HStep.crash (O := O) p, HStep.recover p] = [] := rfl

/-- Events of the model: invocation of an operation, a step, a crash of a process (together with
the matching recovery step). -/
inductive Ev (P : Type) (O : ObjSpec) where
  | inv (p : P) (o : O.Op)
  | step (p : P)
  | crash (p : P)

namespace Alg

variable (A : Alg P O)

/-- Configurations: base-object states, process states (`none` = no pending operation,
`some (o, pc, v)` = running operation `o` or its recovery at location `pc` with volatile
variables `v`) and the full history so far. -/
structure Cfg where
  mem : (i : A.ι) → (A.T i).State
  st : P → Option (O.Op × A.PC × A.V)
  hist : List (HStep P O)

/-- The initial configuration. -/
def init : A.Cfg := ⟨fun i => (A.T i).init, fun _ => none, []⟩

variable {A}

open Classical in
/-- One event. Events that are not enabled (an invocation by a process with a pending operation,
a step or a crash of a process without one) have no effect. -/
noncomputable def Cfg.ev (C : A.Cfg) : Ev P O → A.Cfg
  | .inv p o =>
    match C.st p with
    | none => { C with st := Function.update C.st p (some (o, A.start p o)),
                       hist := C.hist ++ [.inv p o] }
    | some _ => C
  | .step p =>
    match C.st p with
    | none => C
    | some (o, pc, v) =>
      match A.act p o pc v with
      | .access i op pc' k =>
        { C with mem := Function.update C.mem i ((A.T i).δ (C.mem i) op).1,
                 st := Function.update C.st p (some (o, pc', k ((A.T i).δ (C.mem i) op).2)) }
      | .internal pc' v' => { C with st := Function.update C.st p (some (o, pc', v')) }
      | .ret r => { C with st := Function.update C.st p none, hist := C.hist ++ [.res p r] }
  | .crash p =>
    match C.st p with
    | none => C
    | some (o, pc, _) => { C with st := Function.update C.st p (some (o, A.recover p o pc)),
                                  hist := C.hist ++ [.crash p, .recover p] }

/-- Running a list of events. -/
noncomputable def Cfg.run (C : A.Cfg) (es : List (Ev P O)) : A.Cfg := es.foldl Cfg.ev C

@[simp] lemma Cfg.run_nil (C : A.Cfg) : C.run [] = C := rfl

@[simp] lemma Cfg.run_cons (C : A.Cfg) (e : Ev P O) (es : List (Ev P O)) :
    C.run (e :: es) = (C.ev e).run es := rfl

lemma Cfg.run_append (C : A.Cfg) (es es' : List (Ev P O)) :
    C.run (es ++ es') = (C.run es).run es' := by
  simp [Cfg.run, List.foldl_append]

@[simp] lemma Cfg.run_singleton (C : A.Cfg) (e : Ev P O) : C.run [e] = C.ev e := rfl

lemma Cfg.run_concat (C : A.Cfg) (es : List (Ev P O)) (e : Ev P O) :
    C.run (es ++ [e]) = (C.run es).ev e := by
  rw [Cfg.run_append]; rfl

/-! ### One-step lemmas -/

section Step

variable (C : A.Cfg)

lemma ev_inv_of_none {p : P} (o : O.Op) (h : C.st p = none) :
    C.ev (.inv p o) = { C with st := Function.update C.st p (some (o, A.start p o)),
                               hist := C.hist ++ [.inv p o] } := by
  simp [Cfg.ev, h]

lemma ev_inv_of_some {p : P} (o : O.Op) {x} (h : C.st p = some x) : C.ev (.inv p o) = C := by
  simp [Cfg.ev, h]

lemma ev_step_of_none {p : P} (h : C.st p = none) : C.ev (.step p) = C := by
  simp [Cfg.ev, h]

lemma ev_crash_of_none {p : P} (h : C.st p = none) : C.ev (.crash p) = C := by
  simp [Cfg.ev, h]

lemma ev_crash_of_some {p : P} {o : O.Op} {pc : A.PC} {v : A.V} (h : C.st p = some (o, pc, v)) :
    C.ev (.crash p) = { C with st := Function.update C.st p (some (o, A.recover p o pc)),
                               hist := C.hist ++ [.crash p, .recover p] } := by
  simp [Cfg.ev, h]

open Classical in
lemma ev_step_access {p : P} {o : O.Op} {pc : A.PC} {v : A.V} (h : C.st p = some (o, pc, v))
    {i : A.ι} {op : (A.T i).Op} {pc' : A.PC} {k : (A.T i).Resp → A.V}
    (ha : A.act p o pc v = .access i op pc' k) :
    C.ev (.step p) =
      { C with mem := Function.update C.mem i ((A.T i).δ (C.mem i) op).1,
               st := Function.update C.st p (some (o, pc', k ((A.T i).δ (C.mem i) op).2)) } := by
  simp [Cfg.ev, h, ha]

lemma ev_step_internal {p : P} {o : O.Op} {pc : A.PC} {v : A.V} (h : C.st p = some (o, pc, v))
    {pc' : A.PC} {v' : A.V} (ha : A.act p o pc v = .internal pc' v') :
    C.ev (.step p) = { C with st := Function.update C.st p (some (o, pc', v')) } := by
  simp [Cfg.ev, h, ha]

lemma ev_step_ret {p : P} {o : O.Op} {pc : A.PC} {v : A.V} (h : C.st p = some (o, pc, v))
    {r : O.Resp} (ha : A.act p o pc v = .ret r) :
    C.ev (.step p) = { C with st := Function.update C.st p none,
                              hist := C.hist ++ [.res p r] } := by
  simp [Cfg.ev, h, ha]

/-- Every event appends to the history. -/
lemma ev_hist (e : Ev P O) : ∃ h, (C.ev e).hist = C.hist ++ h := by
  rcases e with ⟨p, o⟩ | p | p
  · rcases hs : C.st p with _ | x
    · exact ⟨_, by rw [ev_inv_of_none C o hs]⟩
    · exact ⟨[], by rw [ev_inv_of_some C o hs]; simp⟩
  · rcases hs : C.st p with _ | ⟨o, pc, v⟩
    · exact ⟨[], by rw [ev_step_of_none C hs]; simp⟩
    · rcases ha : A.act p o pc v with ⟨i, op, pc', k⟩ | ⟨pc', v'⟩ | r
      · exact ⟨[], by rw [ev_step_access C hs ha]; simp⟩
      · exact ⟨[], by rw [ev_step_internal C hs ha]; simp⟩
      · exact ⟨_, by rw [ev_step_ret C hs ha]⟩
  · rcases hs : C.st p with _ | ⟨o, pc, v⟩
    · exact ⟨[], by rw [ev_crash_of_none C hs]; simp⟩
    · exact ⟨_, by rw [ev_crash_of_some C hs]⟩

lemma run_hist (es : List (Ev P O)) : ∃ h, (C.run es).hist = C.hist ++ h := by
  induction es generalizing C with
  | nil => exact ⟨[], by simp⟩
  | cons e es ih =>
    obtain ⟨h₁, h1⟩ := ev_hist C e
    obtain ⟨h₂, h2⟩ := ih (C.ev e)
    exact ⟨h₁ ++ h₂, by simp [h2, h1]⟩

end Step

/-! ### Histories of the model are recoverable well-formed (Lemma 1) -/

/-- The subhistory `H|p`. -/
def restrict (H : List (HStep P O)) (p : P) : List (HStep P O) :=
  H.filter (fun s => decide (s.proc = p))

/-- Definition 3 (recoverable well-formedness): every crash step of `p` is `p`'s last step or
is followed in `H|p` by a matching recovery step, and `N(H)` is well-formed. -/
def RecWellFormed (H : List (HStep P O)) : Prop :=
  (∀ p H₁ H₂, restrict H p = H₁ ++ HStep.crash p :: H₂ → H₂ = [] ∨ H₂.head? = some (HStep.recover p))
    ∧ WellFormed (N H)

/-- Definition 4: a finite history satisfies NRL if it is recoverable well-formed and `N(H)` is
linearizable. -/
def HistNRL (H : List (HStep P O)) : Prop :=
  RecWellFormed H ∧ ∃ L, IsLinearization (N H) L

/-- An implementation satisfies NRL (for the environments `Env`, a condition on the invocations,
e.g. "written values are distinct") if every finite history it produces satisfies NRL. -/
def NRL (A : Alg P O) (Env : List (Label P O) → Prop) : Prop :=
  ∀ es : List (Ev P O), Env (N (A.init.run es).hist) → HistNRL (A.init.run es).hist

/-- The first `n` events of an infinite schedule. -/
def pre (e : ℕ → Ev P O) (n : ℕ) : List (Ev P O) := (List.range n).map e

/-- Wait-freedom of the operations and of their recovery functions: in an infinite execution
(from a reachable configuration, obeying `Env`), a process with a pending operation that never
crashes again and takes infinitely many steps eventually completes its operation. -/
def WaitFree (A : Alg P O) (Env : List (Label P O) → Prop) : Prop :=
  ∀ (es : List (Ev P O)) (e : ℕ → Ev P O) (p : P),
    (∀ n, Env (N ((A.init.run es).run (pre e n)).hist)) →
    ((A.init.run es).st p).isSome →
    (∀ n, e n ≠ .crash p) → (∀ m, ∃ n, m ≤ n ∧ e n = .step p) →
    ∃ n, ((A.init.run es).run (pre e n)).st p = none

/-! ### Lemma 1 -/

section WF

/-- Every crash step in `H|p` is immediately followed by the matching recovery step. -/
def CrashRec (H : List (HStep P O)) : Prop :=
  ∀ p H₁ H₂, restrict H p = H₁ ++ HStep.crash p :: H₂ → H₂.head? = some (HStep.recover p)

lemma restrict_append (H H' : List (HStep P O)) (p : P) :
    restrict (H ++ H') p = restrict H p ++ restrict H' p := by
  simp [restrict, List.filter_append]

lemma CrashRec.append {H H' : List (HStep P O)} (hH : CrashRec H) (hH' : CrashRec H') :
    CrashRec (H ++ H') := by
  intro p H₁ H₂ h
  rw [restrict_append] at h
  rcases List.append_eq_append_iff.1 h with ⟨a', rfl, h2⟩ | ⟨c', h1, h2⟩
  · exact hH' p a' H₂ h2
  · rcases c' with _ | ⟨c, c'⟩
    · simp only [List.nil_append] at h2
      exact hH' p [] H₂ (by simpa using h2.symm)
    · simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      have := hH p H₁ c' h1
      rcases c' with _ | ⟨d, c'⟩
      · simp at this
      · simpa using this

lemma crashRec_nil : CrashRec ([] : List (HStep P O)) := by
  intro p H₁ H₂ h; simp [restrict] at h

lemma crashRec_single {s : HStep P O} (hs : ∀ p, s ≠ .crash p) : CrashRec [s] := by
  intro p H₁ H₂ h
  rcases H₁ with _ | ⟨a, H₁⟩
  · by_cases hp : s.proc = p
    · simp only [restrict, List.filter_cons, hp, decide_true, ↓reduceIte, List.filter_nil,
        List.nil_append, List.cons.injEq] at h
      exact absurd h.1 (hs p)
    · simp [restrict, hp] at h
  · by_cases hp : s.proc = p
    · simp [restrict, hp] at h
    · simp [restrict, hp] at h

lemma crashRec_pair (p : P) : CrashRec [HStep.crash (O := O) p, HStep.recover p] := by
  intro q H₁ H₂ h
  by_cases hq : p = q
  · subst hq
    simp only [restrict, HStep.proc, decide_true, List.filter_cons_of_pos, List.filter_nil] at h
    rcases H₁ with _ | ⟨a, _ | ⟨b, H₁⟩⟩
    · simp only [List.nil_append, List.cons.injEq] at h; rw [← h.2]; rfl
    · simp at h
    · simp at h
  · simp [restrict, HStep.proc, hq] at h

/-- Definition 3, in the form produced by the model. -/
lemma RecWellFormed.of_crashRec {H : List (HStep P O)} (h : CrashRec H) (hw : WellFormed (N H)) :
    RecWellFormed H :=
  ⟨fun p H₁ H₂ hs => Or.inr (h p H₁ H₂ hs), hw⟩

/-- The invariant behind Lemma 1: `N(H)` is well formed, a process has a pending operation iff
it has more invocations than responses, and every crash step is immediately followed by its
recovery step. -/
structure WFInv (C : A.Cfg) : Prop where
  wf : WellFormed (N C.hist)
  pend : ∀ p, (opsOf (N C.hist) p).length =
    (respsOf (N C.hist) p).length + (if (C.st p).isSome then 1 else 0)
  crash : CrashRec C.hist

lemma wfInv_init : WFInv (A.init) := by
  refine ⟨?_, ?_, crashRec_nil⟩
  · intro β ℓ γ h; simp [init] at h
  · intro p; simp [init]

lemma WFInv.ev {C : A.Cfg} (hC : WFInv C) (e : Ev P O) : WFInv (C.ev e) := by
  rcases e with ⟨p, o⟩ | p | p
  · rcases hs : C.st p with _ | x
    · rw [ev_inv_of_none C o hs]
      have hp := hC.pend p
      simp only [hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, add_zero] at hp
      refine ⟨?_, ?_, hC.crash.append (crashRec_single (by intro q; simp))⟩
      · simpa using hC.wf.append_inv hp
      · intro q
        have hq := hC.pend q
        by_cases hpq : q = p
        · subst hpq; simp [opsOf_append, respsOf_append, hs, hp]
        · simp [opsOf_append, respsOf_append, Function.update_of_ne hpq, Ne.symm hpq, hq]
    · rw [ev_inv_of_some C o hs]; exact hC
  · rcases hs : C.st p with _ | ⟨o, pc, v⟩
    · rw [ev_step_of_none C hs]; exact hC
    · rcases ha : A.act p o pc v with ⟨i, op, pc', k⟩ | ⟨pc', v'⟩ | r
      · rw [ev_step_access C hs ha]
        refine ⟨hC.wf, ?_, hC.crash⟩
        intro q
        by_cases hpq : q = p
        · subst hpq; simpa [hs] using hC.pend q
        · simpa [Function.update_of_ne hpq] using hC.pend q
      · rw [ev_step_internal C hs ha]
        refine ⟨hC.wf, ?_, hC.crash⟩
        intro q
        by_cases hpq : q = p
        · subst hpq; simpa [hs] using hC.pend q
        · simpa [Function.update_of_ne hpq] using hC.pend q
      · rw [ev_step_ret C hs ha]
        have hp := hC.pend p
        simp only [hs, Option.isSome_some, ↓reduceIte] at hp
        refine ⟨?_, ?_, hC.crash.append (crashRec_single (by intro q; simp))⟩
        · simpa using hC.wf.append_ret hp
        · intro q
          have hq := hC.pend q
          by_cases hpq : q = p
          · subst hpq; simp [opsOf_append, respsOf_append, hp]
          · simp [opsOf_append, respsOf_append, Function.update_of_ne hpq, Ne.symm hpq, hq]
  · rcases hs : C.st p with _ | ⟨o, pc, v⟩
    · rw [ev_crash_of_none C hs]; exact hC
    · rw [ev_crash_of_some C hs]
      refine ⟨by simpa using hC.wf, ?_, hC.crash.append (crashRec_pair p)⟩
      intro q
      by_cases hpq : q = p
      · subst hpq; simpa [hs] using hC.pend q
      · simpa [Function.update_of_ne hpq] using hC.pend q

lemma WFInv.run {C : A.Cfg} (hC : WFInv C) (es : List (Ev P O)) : WFInv (C.run es) := by
  induction es generalizing C with
  | nil => exact hC
  | cons e es ih => exact ih (hC.ev e)

lemma wfInv_run (es : List (Ev P O)) : WFInv (A.init.run es) := wfInv_init.run es

/-- **Lemma 1** (for one implemented object over atomic base objects): every history of the
model is recoverable well-formed. -/
theorem recWellFormed_run (es : List (Ev P O)) : RecWellFormed (A.init.run es).hist :=
  RecWellFormed.of_crashRec (wfInv_run es).crash (wfInv_run es).wf

/-- By Lemma 1, NRL is linearizability of `N(H)`. -/
theorem nrl_iff (Env : List (Label P O) → Prop) :
    A.NRL Env ↔ ∀ es : List (Ev P O), Env (N (A.init.run es).hist) →
      ∃ L, IsLinearization (N (A.init.run es).hist) L :=
  ⟨fun h es he => (h es he).2, fun h es he => ⟨recWellFormed_run es, h es he⟩⟩

end WF

end Alg

end Cslib.SharedMemory.NRL
