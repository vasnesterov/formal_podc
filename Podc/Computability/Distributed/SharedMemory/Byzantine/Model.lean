import Cslib.Computability.Distributed.SharedMemory.Model
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Byzantine/Model.lean

/-!
# Asynchronous shared memory with Byzantine processes

An execution model for implementations of a high-level object `A` from atomic base objects
`B i` (`i : ι`) in an asynchronous system where some processes are *Byzantine*.

* The data of an implementation is CSLib's `Impl A B P L` (`memInit`, `locInit`, `invoke`, `act`,
  `allowed`), read with a different semantics (`Impl.bstep`):
  - a process may take steps (`Event.tau`) also when it has no pending operation, i.e. it may
    "help" others outside its own operation intervals; a step whose next action is a response
    while the process is idle is a stutter step;
  - *Byzantine* processes do not run their program at all: they apply arbitrary primitives
    to base objects (`Event.byz p i o`), subject only to the *access rights* `acc p i o`
    (e.g. only the owner of an SWMR register may write it).
* `Event.Respects Bz`: in an execution with Byzantine set `Bz`, correct processes (`∉ Bz`) only
  take invocation/response/algorithm steps and Byzantine processes only take `byz` steps.
* `Impl.RespectsAccess acc`: the program of every process only applies primitives it is allowed to.
* `hist α`: the high-level history (invocations and responses) of an execution.
* `ByzLinearizable allowed Bz h` (Cohen–Keidar): there is a well-formed history `h'` of the
  object, using only allowed operations, that agrees with `h` on the correct processes and is
  linearizable.
* `Impl.ByzCorrect acc f adm`: Byzantine linearizability of every finite execution and termination
  (every operation of a correct process completes) in every fair infinite execution, for every
  Byzantine set of size `≤ f`, among the executions in which every correct process `p` invokes a
  sequence of operations allowed by `adm p` (e.g. one-shot objects).

Main lemmas: `Impl.bcounts` (pending ↔ one more invocation than response), `Impl.bhist_wellFormed`,
`Impl.replay` (turning a set `G` of processes Byzantine without changing what the others see),
`Impl.mem_eq_of_owner` (single-writer base objects), `Impl.exists_setMem` (Byzantine owners can
overwrite their objects), `Impl.ByzCorrect.exists_completion` (termination yields a finite
continuation, by a round-robin fair schedule).
-/

namespace Cslib.SharedMemory.Byzantine

open Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

/-- Access rights to base objects: `acc p i o` — process `p` may apply primitive `o` to the base
object `i` (this also constrains Byzantine processes). -/
abbrev Access (P : Type) (B : ι → ObjSpec) := P → (i : ι) → (B i).Op → Prop

/-- Events of executions with Byzantine processes. -/
inductive Event (P : Type) (A : ObjSpec) (B : ι → ObjSpec) where
  /-- The (correct) process `p` invokes the high-level operation `o`. -/
  | inv (p : P) (o : A.Op)
  /-- The (correct) process `p` returns response `r`. -/
  | ret (p : P) (r : A.Resp)
  /-- The (correct) process `p` takes an algorithm step (a base-object access, or a stutter). -/
  | tau (p : P)
  /-- The Byzantine process `p` applies the primitive `o` to the base object `i`. -/
  | byz (p : P) (i : ι) (o : (B i).Op)

namespace Event

/-- The process of an event. -/
def proc : Event P A B → P
  | inv p _ => p
  | ret p _ => p
  | tau p => p
  | byz p _ _ => p

/-- The high-level label of an event (invocations and responses only). -/
def hist : Event P A B → Option (Label P A)
  | inv p o => some (.inv p o)
  | ret p r => some (.ret p r)
  | _ => none

/-- An algorithm step (response or internal step) of `p`. -/
def IsStepOf (p : P) : Event P A B → Prop
  | ret q _ => q = p
  | tau q => q = p
  | _ => False

/-- The event is compatible with the Byzantine set `Bz`. -/
def Respects (Bz : Finset P) : Event P A B → Prop
  | inv p _ => p ∉ Bz
  | ret p _ => p ∉ Bz
  | tau p => p ∉ Bz
  | byz p _ _ => p ∈ Bz

@[simp] lemma proc_inv (p : P) (o : A.Op) : (inv p o : Event P A B).proc = p := rfl
@[simp] lemma proc_ret (p : P) (r : A.Resp) : (ret p r : Event P A B).proc = p := rfl
@[simp] lemma proc_tau (p : P) : (tau p : Event P A B).proc = p := rfl
@[simp] lemma proc_byz (p : P) (i : ι) (o : (B i).Op) : (byz p i o : Event P A B).proc = p := rfl
@[simp] lemma hist_inv (p : P) (o : A.Op) : (inv p o : Event P A B).hist = some (.inv p o) := rfl
@[simp] lemma hist_ret (p : P) (r : A.Resp) : (ret p r : Event P A B).hist = some (.ret p r) :=
  rfl
@[simp] lemma hist_tau (p : P) : (tau p : Event P A B).hist = none := rfl
@[simp] lemma hist_byz (p : P) (i : ι) (o : (B i).Op) : (byz p i o : Event P A B).hist = none :=
  rfl

lemma proc_of_hist {e : Event P A B} {ℓ : Label P A} (h : e.hist = some ℓ) : ℓ.proc = e.proc := by
  cases e <;> simp_all [hist] <;> subst h <;> rfl

lemma IsStepOf.proc {p : P} {e : Event P A B} (h : e.IsStepOf p) : e.proc = p := by
  cases e <;> simp_all [IsStepOf]

lemma IsStepOf.respects {p : P} {e : Event P A B} {Bz : Finset P} (h : e.IsStepOf p)
    (hp : p ∉ Bz) : e.Respects Bz := by
  cases e <;> simp_all [IsStepOf, Respects]

lemma IsStepOf.hist_inv {p : P} {e : Event P A B} (h : e.IsStepOf p) (q : P) (o : A.Op) :
    e.hist ≠ some (.inv q o) := by
  cases e <;> simp_all [IsStepOf, Event.hist]

end Event

/-- The high-level history of an execution. -/
def hist (α : List (Event P A B)) : List (Label P A) := α.filterMap Event.hist

@[simp] lemma hist_nil : hist ([] : List (Event P A B)) = [] := rfl
@[simp] lemma hist_append (α β : List (Event P A B)) : hist (α ++ β) = hist α ++ hist β := by
  simp [hist]
@[simp] lemma hist_cons (e : Event P A B) (α : List (Event P A B)) :
    hist (e :: α) = e.hist.toList ++ hist α := by
  cases h : e.hist <;> simp [hist, h]

/-- The first `k` events of an infinite event sequence. -/
def pre (ev : ℕ → Event P A B) (k : ℕ) : List (Event P A B) := (List.range k).map ev

/-- Fairness: every correct process takes infinitely many algorithm steps. -/
def Fair (Bz : Finset P) (ev : ℕ → Event P A B) : Prop :=
  ∀ p ∉ Bz, ∀ k, ∃ m ≥ k, (ev m).IsStepOf p

section ByzLin

variable [DecidableEq P]

/-- Definition 7 of Hu–Toueg (Cohen–Keidar's Byzantine linearizability) for a finite history `h`
with Byzantine set `Bz`: some well-formed history `h'` using only allowed operations agrees with
`h` on the correct processes (`h'|correct = h|correct`) and is linearizable. -/
def ByzLinearizable (allowed : P → A.Op → Prop) (Bz : Finset P) (h : List (Label P A)) : Prop :=
  ∃ h' : List (Label P A), WellFormed h' ∧ (∀ p o, Label.inv p o ∈ h' → allowed p o) ∧
    h'.filter (fun ℓ => ℓ.proc ∉ Bz) = h.filter (fun ℓ => ℓ.proc ∉ Bz) ∧
    ∃ L, IsLinearization h' L

end ByzLin

/-- The base objects are *single-writer* with respect to `owner`: a primitive applied by a process
other than the owner never changes the object (e.g. reads of an SWMR register), and the owner can
overwrite its object with any state in one step (e.g. writes of an SWMR register). -/
structure SingleWriter (acc : Access P B) (owner : ι → P) : Prop where
  /-- Only the owner changes an object. -/
  readOnly : ∀ p i o, acc p i o → owner i ≠ p → ∀ q, ((B i).δ q o).1 = q
  /-- The owner can put its object into any state. -/
  overwrite : ∀ i q q', ∃ o, acc (owner i) i o ∧ ((B i).δ q o).1 = q'

/-- Two configurations with the same memory in which the processes of `S` have the same local
states and pending operations. -/
def Agree (S : Finset P) (C D : Config A B P L) : Prop :=
  C.mem = D.mem ∧ ∀ p ∈ S, C.loc p = D.loc p ∧ C.pend p = D.pend p

end Cslib.SharedMemory.Byzantine

namespace Cslib.SharedMemory.Impl

open Cslib.SharedMemory.Byzantine

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}
variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L) (acc : Access P B)

/-- The effect of an event (`none` if it is not enabled). -/
noncomputable def bstep (C : Config A B P L) : Event P A B → Option (Config A B P L)
  | .inv p o => by
    classical
    exact if C.pend p = none ∧ I.allowed p o then
      some { C with pend := Function.update C.pend p (some o),
                    loc := Function.update C.loc p (I.invoke p (C.loc p) o) }
    else none
  | .tau p =>
    match I.act p (C.loc p) with
    | .access i o k =>
      some { C with mem := Function.update C.mem i ((B i).δ (C.mem i) o).1,
                    loc := Function.update C.loc p (k ((B i).δ (C.mem i) o).2) }
    | .ret _ _ => if C.pend p = none then some C else none
  | .ret p r =>
    if C.pend p = none then none else
    match I.act p (C.loc p) with
    | .access _ _ _ => none
    | .ret r' l => by
      classical
      exact if r = r' then
        some { C with pend := Function.update C.pend p none, loc := Function.update C.loc p l }
      else none
  | .byz p i o => by
    classical
    exact if acc p i o then
      some { C with mem := Function.update C.mem i ((B i).δ (C.mem i) o).1 }
    else none

/-- Run a list of events from a configuration. -/
noncomputable def brunFrom (C : Config A B P L) : List (Event P A B) → Option (Config A B P L)
  | [] => some C
  | e :: α => (I.bstep acc C e).bind (fun C' => brunFrom C' α)

/-- Run a list of events from the initial configuration. -/
noncomputable def brun (α : List (Event P A B)) : Option (Config A B P L) :=
  I.brunFrom acc I.initCfg α

/-- `α` is a finite execution with Byzantine set `Bz`. -/
def BExec (Bz : Finset P) (α : List (Event P A B)) : Prop :=
  (∃ C, I.brun acc α = some C) ∧ ∀ e ∈ α, e.Respects Bz

/-- The program only applies allowed primitives. -/
def RespectsAccess : Prop := ∀ p l i o k, I.act p l = .access i o k → acc p i o

/-- Correctness (Definition 9 of Hu–Toueg) against at most `f` Byzantine processes, for the
executions in which every correct process `p` invokes a sequence of operations satisfying
`adm p`: every finite execution has a Byzantine linearizable history, and in every fair infinite
execution every correct process is idle infinitely often (completes all its operations). -/
def ByzCorrect (f : ℕ) (adm : P → List A.Op → Prop) : Prop :=
  (∀ Bz : Finset P, Bz.card ≤ f → ∀ α, I.BExec acc Bz α →
      (∀ p ∉ Bz, adm p (opsOf (hist α) p)) → ByzLinearizable I.allowed Bz (hist α)) ∧
  (∀ Bz : Finset P, Bz.card ≤ f → ∀ ev : ℕ → Event P A B, (∀ k, I.BExec acc Bz (pre ev k)) →
      Fair Bz ev → (∀ k, ∀ p ∉ Bz, adm p (opsOf (hist (pre ev k)) p)) →
      ∀ p ∉ Bz, ∀ k, ∃ m ≥ k, ∀ C, I.brun acc (pre ev m) = some C → C.pend p = none)

/-! ## Basic run lemmas -/

@[simp] lemma brunFrom_nil (C : Config A B P L) : I.brunFrom acc C [] = some C := rfl

@[simp] lemma brunFrom_cons (C : Config A B P L) (e : Event P A B) (α : List (Event P A B)) :
    I.brunFrom acc C (e :: α) = (I.bstep acc C e).bind (fun C' => I.brunFrom acc C' α) := rfl

lemma brunFrom_append (C : Config A B P L) (α β : List (Event P A B)) :
    I.brunFrom acc C (α ++ β) = (I.brunFrom acc C α).bind (fun C' => I.brunFrom acc C' β) := by
  induction α generalizing C with
  | nil => simp
  | cons e α ih =>
    simp only [List.cons_append, brunFrom_cons, ih]
    cases I.bstep acc C e <;> simp

lemma brunFrom_append_of_eq {C C' : Config A B P L} {α : List (Event P A B)}
    (h : I.brunFrom acc C α = some C') (β : List (Event P A B)) :
    I.brunFrom acc C (α ++ β) = I.brunFrom acc C' β := by
  rw [brunFrom_append, h]; rfl

lemma brunFrom_singleton (C : Config A B P L) (e : Event P A B) :
    I.brunFrom acc C [e] = I.bstep acc C e := by
  simp only [brunFrom_cons, brunFrom_nil]; cases I.bstep acc C e <;> rfl

lemma brunFrom_append_eq_some {C D : Config A B P L} {α β : List (Event P A B)}
    (h : I.brunFrom acc C (α ++ β) = some D) :
    ∃ C', I.brunFrom acc C α = some C' ∧ I.brunFrom acc C' β = some D := by
  rw [brunFrom_append] at h
  cases h' : I.brunFrom acc C α with
  | none => simp [h'] at h
  | some C' => exact ⟨C', rfl, by simpa [h'] using h⟩

lemma brunFrom_trans {C C' C'' : Config A B P L} {α β : List (Event P A B)}
    (h₁ : I.brunFrom acc C α = some C') (h₂ : I.brunFrom acc C' β = some C'') :
    I.brunFrom acc C (α ++ β) = some C'' := by
  rw [I.brunFrom_append_of_eq acc h₁, h₂]

/-- Induction along an execution: a property of configurations preserved by every step. -/
lemma brunFrom_induction (Q : Config A B P L → Prop)
    (hstep : ∀ C e C', Q C → I.bstep acc C e = some C' → Q C') :
    ∀ {C C' : Config A B P L} {α : List (Event P A B)}, Q C →
      I.brunFrom acc C α = some C' → Q C' := by
  intro C C' α hC h
  induction α generalizing C with
  | nil => simp at h; exact h ▸ hC
  | cons e α ih =>
    simp only [brunFrom_cons] at h
    cases he : I.bstep acc C e with
    | none => simp [he] at h
    | some D => simp only [he, Option.bind_some] at h; exact ih (hstep C e D hC he) h

/-! ## Step inversion -/

lemma bstep_pend_ne {C C' : Config A B P L} {e : Event P A B} (h : I.bstep acc C e = some C')
    {p : P} (hp : e.proc ≠ p) : C'.pend p = C.pend p ∧ C'.loc p = C.loc p := by
  cases e with
  | inv q o =>
    simp only [Event.proc] at hp
    simp only [bstep] at h; split_ifs at h; cases h
    simp [Function.update_of_ne (Ne.symm hp)]
  | tau q =>
    simp only [Event.proc] at hp
    simp only [bstep] at h
    split at h
    · cases h; simp [Function.update_of_ne (Ne.symm hp)]
    · split_ifs at h; cases h; simp
  | ret q r =>
    simp only [Event.proc] at hp
    simp only [bstep] at h
    split_ifs at h
    split at h
    · simp at h
    · split_ifs at h; cases h; simp [Function.update_of_ne (Ne.symm hp)]
  | byz q i o =>
    simp only [bstep] at h; split_ifs at h; cases h; simp

lemma bstep_byz_eq {C C' : Config A B P L} {p : P} {i : ι} {o : (B i).Op}
    (h : I.bstep acc C (.byz p i o) = some C') :
    acc p i o ∧ C' = { C with mem := Function.update C.mem i ((B i).δ (C.mem i) o).1 } := by
  simp only [bstep] at h; split_ifs at h with h1; cases h; exact ⟨h1, rfl⟩

/-- Events of other processes do not change the local state of `p`. -/
lemma brunFrom_pend_loc {C C' : Config A B P L} {α : List (Event P A B)} {p : P}
    (h : I.brunFrom acc C α = some C') (hp : ∀ e ∈ α, e.proc ≠ p) :
    C'.pend p = C.pend p ∧ C'.loc p = C.loc p := by
  induction α generalizing C with
  | nil => simp at h; subst h; simp
  | cons e α ih =>
    simp only [brunFrom_cons] at h
    cases he : I.bstep acc C e with
    | none => simp [he] at h
    | some D =>
      simp only [he, Option.bind_some] at h
      have h1 := I.bstep_pend_ne acc he (hp e (by simp))
      have h2 := ih h (fun e' he' => hp e' (by simp [he']))
      exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-- `byz` events do not change local states. -/
lemma brunFrom_pend_loc_of_byz {C C' : Config A B P L} {α : List (Event P A B)}
    (h : I.brunFrom acc C α = some C') (hα : ∀ e ∈ α, ∃ p i o, e = .byz p i o) :
    C'.pend = C.pend ∧ C'.loc = C.loc := by
  induction α generalizing C with
  | nil => simp at h; subst h; simp
  | cons e α ih =>
    simp only [brunFrom_cons] at h
    obtain ⟨p, i, o, rfl⟩ := hα e (by simp)
    cases he : I.bstep acc C (.byz p i o) with
    | none => simp [he] at h
    | some D =>
      simp only [he, Option.bind_some] at h
      obtain ⟨-, rfl⟩ := I.bstep_byz_eq acc he
      have := ih h (fun e' he' => hα e' (by simp [he']))
      exact this

lemma bstep_inv_isSome {C : Config A B P L} {p : P} {o : A.Op} (hp : C.pend p = none)
    (ho : I.allowed p o) : ∃ C', I.bstep acc C (.inv p o) = some C' := by
  simp [bstep, hp, ho]

/-! ## Counting invocations and responses -/

/-- Invariant: a process is pending iff it has one more invocation than responses. -/
theorem bcounts {α : List (Event P A B)} {C : Config A B P L} (h : I.brun acc α = some C) (p : P) :
    (opsOf (hist α) p).length =
      (respsOf (hist α) p).length + (if C.pend p = none then 0 else 1) := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [brun, brunFrom_nil, Option.some.injEq] at h; subst h; simp [initCfg]
  | append_singleton α e ih =>
    obtain ⟨D, hD, he⟩ := I.brunFrom_append_eq_some acc h
    rw [brunFrom_singleton] at he
    have ih := ih hD
    have hh : hist (α ++ [e]) = hist α ++ e.hist.toList := by
      simp only [hist, List.filterMap_append]; cases h : e.hist <;> simp [h]
    rw [hh, opsOf_append, respsOf_append, List.length_append, List.length_append]
    by_cases hp : e.proc = p
    · cases e with
      | inv q o =>
        simp only [Event.proc] at hp; subst hp
        simp only [bstep] at he; split_ifs at he with h1; cases he
        rw [ite_eq_left h1.1] at ih
        simp [ih]
      | tau q =>
        simp only [Event.proc] at hp; subst hp
        simp only [bstep] at he
        split at he
        · cases he; simp [ih]
        · split_ifs at he; cases he; simp [ih]
      | ret q r =>
        simp only [Event.proc] at hp; subst hp
        simp only [bstep] at he
        split_ifs at he with h1
        split at he
        · simp at he
        · split_ifs at he; cases he
          rw [ite_eq_right h1] at ih
          simp [ih]
      | byz q i o =>
        simp only [Event.proc] at hp; subst hp
        obtain ⟨-, rfl⟩ := I.bstep_byz_eq acc he
        simp [ih]
    · have h1 := I.bstep_pend_ne acc he hp
      have hi : opsOf e.hist.toList p = [] := by
        cases hh : e.hist with
        | none => simp [opsOf]
        | some ℓ =>
          simp [opsOf, Label.invOf_eq_none_of_proc_ne (by rw [Event.proc_of_hist hh]; exact hp)]
      have hr : respsOf e.hist.toList p = [] := by
        cases hh : e.hist with
        | none => simp [respsOf]
        | some ℓ =>
          simp [respsOf, Label.retOf_eq_none_of_proc_ne (by rw [Event.proc_of_hist hh]; exact hp)]
      rw [hi, hr, h1.1]
      simpa using ih

lemma pend_eq_none_of_opsOf_nil {α : List (Event P A B)} {C : Config A B P L}
    (h : I.brun acc α = some C) {p : P} (hp : opsOf (hist α) p = []) : C.pend p = none := by
  have := I.bcounts acc h p
  rw [hp] at this
  by_contra hc; rw [ite_eq_right hc] at this; simp at this

lemma respsOf_length_of_idle {α : List (Event P A B)} {C : Config A B P L}
    (h : I.brun acc α = some C) {p : P} (hp : C.pend p = none) :
    (respsOf (hist α) p).length = (opsOf (hist α) p).length := by
  have := I.bcounts acc h p
  rw [ite_eq_left hp] at this; omega

/-- Histories of executions are well formed. -/
theorem bhist_wellFormed {α : List (Event P A B)} {C : Config A B P L}
    (h : I.brun acc α = some C) : WellFormed (hist α) := by
  induction α using List.reverseRecOn generalizing C with
  | nil => intro β ℓ γ h; simp at h
  | append_singleton α e ih =>
    obtain ⟨D, hD, he⟩ := I.brunFrom_append_eq_some acc h
    rw [brunFrom_singleton] at he
    have hc := I.bcounts acc hD
    have ih := ih hD
    cases e with
    | inv q o =>
      simp only [bstep] at he; split_ifs at he with h1
      have := hc q; rw [ite_eq_left h1.1] at this
      simpa using ih.append_inv (o := o) (by simpa using this)
    | tau q => simpa using ih
    | ret q r =>
      simp only [bstep] at he
      split_ifs at he with h1
      have := hc q; rw [ite_eq_right h1] at this
      simpa using ih.append_ret (r := r) this
    | byz q i o => simpa using ih

/-! ## Memory -/

/-- A step changes at most one base object, by a primitive that the stepping process may apply. -/
lemma bstep_mem (hI : I.RespectsAccess acc) {C C' : Config A B P L} {e : Event P A B}
    (h : I.bstep acc C e = some C') (i : ι) :
    C'.mem i = C.mem i ∨ ∃ o, acc e.proc i o ∧ C'.mem i = ((B i).δ (C.mem i) o).1 := by
  cases e with
  | inv q o => simp only [bstep] at h; split_ifs at h; cases h; simp
  | tau q =>
    simp only [bstep] at h
    split at h
    · rename_i j o k hact
      cases h
      by_cases hij : i = j
      · subst hij; right; exact ⟨o, hI _ _ _ _ _ hact, by simp⟩
      · left; simp [Function.update_of_ne hij]
    · split_ifs at h; cases h; simp
  | ret q r =>
    simp only [bstep] at h
    split_ifs at h
    split at h
    · simp at h
    · split_ifs at h; cases h; simp
  | byz q j o =>
    obtain ⟨hacc, rfl⟩ := I.bstep_byz_eq acc h
    by_cases hij : i = j
    · subst hij; right; exact ⟨o, hacc, by simp⟩
    · left; simp [Function.update_of_ne hij]

/-- A step changes at most one base object. -/
lemma bstep_mem_finite {C C' : Config A B P L} {e : Event P A B}
    (h : I.bstep acc C e = some C') : ∃ T : Finset ι, ∀ i ∉ T, C'.mem i = C.mem i := by
  cases e with
  | inv q o => simp only [bstep] at h; split_ifs at h; cases h; exact ⟨∅, by simp⟩
  | tau q =>
    simp only [bstep] at h
    split at h
    · rename_i j o k hact
      cases h
      exact ⟨{j}, fun i hi => by simp at hi; simp [Function.update_of_ne hi]⟩
    · split_ifs at h; cases h; exact ⟨∅, by simp⟩
  | ret q r =>
    simp only [bstep] at h
    split_ifs at h
    split at h
    · simp at h
    · split_ifs at h; cases h; exact ⟨∅, by simp⟩
  | byz q j o =>
    obtain ⟨-, rfl⟩ := I.bstep_byz_eq acc h
    exact ⟨{j}, fun i hi => by simp at hi; simp [Function.update_of_ne hi]⟩

/-- A finite execution changes only finitely many base objects. -/
lemma brunFrom_mem_finite {C C' : Config A B P L} {α : List (Event P A B)}
    (h : I.brunFrom acc C α = some C') : ∃ T : Finset ι, ∀ i ∉ T, C'.mem i = C.mem i := by
  induction α generalizing C with
  | nil => simp at h; subst h; exact ⟨∅, by simp⟩
  | cons e α ih =>
    simp only [brunFrom_cons] at h
    cases he : I.bstep acc C e with
    | none => simp [he] at h
    | some D =>
      simp only [he, Option.bind_some] at h
      obtain ⟨T₁, h₁⟩ := I.bstep_mem_finite acc he
      obtain ⟨T₂, h₂⟩ := ih h
      classical
      exact ⟨T₁ ∪ T₂, fun i hi => by
        simp only [Finset.mem_union, not_or] at hi; rw [h₂ i hi.2, h₁ i hi.1]⟩

/-- Single-writer objects are only changed by events of their owner. -/
lemma brunFrom_mem_of_owner (hI : I.RespectsAccess acc) {owner : ι → P}
    (hSW : SingleWriter acc owner) {C C' : Config A B P L} {α : List (Event P A B)}
    (h : I.brunFrom acc C α = some C') {i : ι} (hi : ∀ e ∈ α, e.proc ≠ owner i) :
    C'.mem i = C.mem i := by
  induction α generalizing C with
  | nil => simp at h; subst h; rfl
  | cons e α ih =>
    simp only [brunFrom_cons] at h
    cases he : I.bstep acc C e with
    | none => simp [he] at h
    | some D =>
      simp only [he, Option.bind_some] at h
      rw [ih h (fun e' he' => hi e' (by simp [he']))]
      rcases I.bstep_mem acc hI he i with h1 | ⟨o, ho, h1⟩
      · exact h1
      · rw [h1, hSW.readOnly _ _ _ ho (Ne.symm (hi e (by simp)))]

/-- Byzantine owners can overwrite a finite set `T` of their objects with arbitrary states. -/
theorem exists_setMem {owner : ι → P} (hSW : SingleWriter acc owner) (Bz : Finset P)
    (T : Finset ι) (hT : ∀ i ∈ T, owner i ∈ Bz) (C : Config A B P L)
    (M : (i : ι) → (B i).State) :
    ∃ β C', I.brunFrom acc C β = some C' ∧ (∀ e ∈ β, e.Respects Bz ∧ e.proc ∈ Bz) ∧
      hist β = [] ∧ C'.loc = C.loc ∧ C'.pend = C.pend ∧
      ∀ i, C'.mem i = if i ∈ T then M i else C.mem i := by
  induction T using Finset.induction_on with
  | empty => exact ⟨[], C, rfl, by simp, rfl, rfl, rfl, by simp⟩
  | insert a T haT ih =>
    obtain ⟨β, C₁, h₁, hβ, hh, hl, hp, hm⟩ := ih (fun i hi => hT i (by simp [hi]))
    obtain ⟨o, ho, hδ⟩ := hSW.overwrite a (C₁.mem a) (M a)
    have hstep : I.bstep acc C₁ (.byz (owner a) a o) =
        some { C₁ with mem := Function.update C₁.mem a ((B a).δ (C₁.mem a) o).1 } := by
      simp [bstep, ho]
    refine ⟨β ++ [.byz (owner a) a o],
      { C₁ with mem := Function.update C₁.mem a ((B a).δ (C₁.mem a) o).1 }, I.brunFrom_trans acc h₁
      ((I.brunFrom_singleton acc _ _).trans hstep), ?_, ?_, hl, hp, ?_⟩
    · intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hβ e he
      · have := hT a (by simp); exact ⟨this, this⟩
    · simp [hh]
    · intro i
      by_cases hia : i = a
      · subst hia; simp [hδ]
      · simp [hm, hia]

/-! ## Replaying an execution with more Byzantine processes -/

lemma bstep_agree {S : Finset P} {C C' D : Config A B P L} {e : Event P A B}
    (h : I.bstep acc C e = some C') (he : e.proc ∈ S) (hCD : Agree S C D) :
    ∃ D', I.bstep acc D e = some D' ∧ Agree S C' D' := by
  obtain ⟨hm, hl⟩ := hCD
  cases e with
  | inv p o =>
    simp only [Event.proc] at he
    obtain ⟨hlp, hpp⟩ := hl p he
    simp only [bstep] at h ⊢
    split_ifs at h with h1; cases h
    rw [ite_eq_left (by rw [← hpp]; exact h1)]
    refine ⟨_, rfl, hm, fun q hq => ?_⟩
    by_cases hqp : q = p
    · subst hqp; simp [hlp]
    · simp [Function.update_of_ne hqp, hl q hq]
  | tau p =>
    simp only [Event.proc] at he
    obtain ⟨hlp, hpp⟩ := hl p he
    simp only [bstep] at h ⊢
    rw [← hlp]
    split at h
    · rename_i j o k hact
      cases h
      refine ⟨_, rfl, by simp [hm], fun q hq => ?_⟩
      by_cases hqp : q = p
      · subst hqp; simp [hm, hpp]
      · simp [Function.update_of_ne hqp, hl q hq]
    · rename_i r l hact
      split_ifs at h with h1; cases h
      rw [ite_eq_left (by rw [← hpp]; exact h1)]
      exact ⟨_, rfl, hm, hl⟩
  | ret p r =>
    simp only [Event.proc] at he
    obtain ⟨hlp, hpp⟩ := hl p he
    simp only [bstep] at h ⊢
    rw [← hlp, ← hpp]
    split_ifs at h with h1
    split at h
    · simp at h
    · rename_i r' l hact
      split_ifs at h with h2; cases h
      rw [ite_eq_right h1, ite_eq_left h2]
      refine ⟨_, rfl, hm, fun q hq => ?_⟩
      by_cases hqp : q = p
      · subst hqp; simp
      · simp [Function.update_of_ne hqp, hl q hq]
  | byz p i o =>
    obtain ⟨hacc, rfl⟩ := I.bstep_byz_eq acc h
    exact ⟨{ D with mem := Function.update D.mem i ((B i).δ (D.mem i) o).1 },
      by simp [bstep, hacc], by simp [hm], hl⟩

lemma replay_step (hI : I.RespectsAccess acc) {S G Bz' : Finset P}
    (hG : G ⊆ Bz') {C C' D : Config A B P L} {e : Event P A B}
    (h : I.bstep acc C e = some C') (he : e.proc ∈ S ∪ G) (hS : e.proc ∈ S → e.Respects Bz')
    (hCD : Agree S C D) :
    ∃ β D', I.brunFrom acc D β = some D' ∧ (∀ e' ∈ β, e'.Respects Bz' ∧ e'.proc = e.proc) ∧
      hist β = e.hist.toList.filter (fun ℓ => ℓ.proc ∈ S) ∧ Agree S C' D' ∧
      ∀ p ∉ S, D'.loc p = D.loc p ∧ D'.pend p = D.pend p := by
  by_cases heS : e.proc ∈ S
  · obtain ⟨D', hD', hag⟩ := I.bstep_agree acc h heS hCD
    refine ⟨[e], D', by rw [brunFrom_singleton]; exact hD', by simpa using hS heS, ?_, hag,
      fun p hp => (I.bstep_pend_ne acc hD' (fun h : e.proc = p => hp (h ▸ heS))).symm⟩
    cases hh : e.hist with
    | none => simp [hh]
    | some ℓ => simp [hh, Event.proc_of_hist hh, heS]
  · have heG : e.proc ∈ G := by simpa [heS] using he
    have hfilt : e.hist.toList.filter (fun ℓ => ℓ.proc ∈ S) = [] := by
      cases hh : e.hist with
      | none => simp
      | some ℓ => simp [Event.proc_of_hist hh, heS]
    rw [hfilt]
    obtain ⟨hm, hl⟩ := hCD
    have hlS : ∀ q ∈ S, C'.loc q = D.loc q ∧ C'.pend q = D.pend q := fun q hq => by
      have := I.bstep_pend_ne acc h (fun h' => heS (h'.symm ▸ hq))
      rw [this.1, this.2]; exact hl q hq
    cases e with
    | inv p o =>
      simp only [bstep] at h; split_ifs at h; cases h
      exact ⟨[], D, rfl, by simp, rfl, ⟨hm, hlS⟩, fun _ _ => ⟨rfl, rfl⟩⟩
    | ret p r =>
      simp only [bstep] at h
      split_ifs at h
      split at h
      · simp at h
      · split_ifs at h; cases h
        exact ⟨[], D, rfl, by simp, rfl, ⟨hm, hlS⟩, fun _ _ => ⟨rfl, rfl⟩⟩
    | tau p =>
      simp only [Event.proc] at heG heS
      simp only [bstep] at h
      split at h
      · rename_i j o k hact
        cases h
        have hacc := hI _ _ _ _ _ hact
        refine ⟨[.byz p j o], { D with mem := Function.update D.mem j ((B j).δ (D.mem j) o).1 },
          by simp [bstep, hacc], ?_, by simp,
          ⟨by simp [hm], hlS⟩, fun _ _ => ⟨rfl, rfl⟩⟩
        simpa [Event.Respects] using hG heG
      · split_ifs at h; cases h
        exact ⟨[], D, rfl, by simp, rfl, ⟨hm, hlS⟩, fun _ _ => ⟨rfl, rfl⟩⟩
    | byz p j o =>
      simp only [Event.proc] at heG heS
      obtain ⟨hacc, rfl⟩ := I.bstep_byz_eq acc h
      refine ⟨[.byz p j o], { D with mem := Function.update D.mem j ((B j).δ (D.mem j) o).1 },
        by simp [bstep, hacc], ?_, by simp, ⟨by simp [hm], hl⟩, fun _ _ => ⟨rfl, rfl⟩⟩
      simpa [Event.Respects] using hG heG

/-- **Replay.** Turning the processes of `G` Byzantine (they replay their base-object accesses as
`byz` events) does not change what the processes of `S` see. -/
theorem replay (hI : I.RespectsAccess acc) {S G Bz' : Finset P}
    (hG : G ⊆ Bz') {C C' D : Config A B P L} {α : List (Event P A B)}
    (h : I.brunFrom acc C α = some C') (hα : ∀ e ∈ α, e.proc ∈ S ∪ G)
    (hS : ∀ e ∈ α, e.proc ∈ S → e.Respects Bz') (hCD : Agree S C D) :
    ∃ β D', I.brunFrom acc D β = some D' ∧ (∀ e ∈ β, e.Respects Bz' ∧ e.proc ∈ S ∪ G) ∧
      hist β = (hist α).filter (fun ℓ => ℓ.proc ∈ S) ∧ Agree S C' D' ∧
      ∀ p ∉ S, D'.loc p = D.loc p ∧ D'.pend p = D.pend p := by
  induction α generalizing C D with
  | nil =>
    simp at h; subst h
    exact ⟨[], D, rfl, by simp, rfl, hCD, fun _ _ => ⟨rfl, rfl⟩⟩
  | cons e α ih =>
    simp only [brunFrom_cons] at h
    cases he : I.bstep acc C e with
    | none => simp [he] at h
    | some C₁ =>
      simp only [he, Option.bind_some] at h
      obtain ⟨β₁, D₁, h₁, hβ₁, hh₁, hag₁, hl₁⟩ := I.replay_step acc hI hG he
        (hα e (by simp)) (hS e (by simp)) hCD
      obtain ⟨β₂, D₂, h₂, hβ₂, hh₂, hag₂, hl₂⟩ := ih h (fun e' he' => hα e' (by simp [he']))
        (fun e' he' => hS e' (by simp [he'])) hag₁
      refine ⟨β₁ ++ β₂, D₂, I.brunFrom_trans acc h₁ h₂, ?_, ?_, hag₂, fun p hp => ?_⟩
      · intro e' he'
        rcases List.mem_append.1 he' with he' | he'
        · exact ⟨(hβ₁ e' he').1, (hβ₁ e' he').2 ▸ hα e (by simp)⟩
        · exact hβ₂ e' he'
      · simp [hh₁, hh₂, List.filter_append]
      · exact ⟨(hl₂ p hp).1.trans (hl₁ p hp).1, (hl₂ p hp).2.trans (hl₁ p hp).2⟩

/-! ## Fair continuations and termination -/

/-- The next algorithm step of `p`: always enabled (`bstep_nextEv`). -/
noncomputable def nextEv (p : P) (C : Config A B P L) : Event P A B :=
  match I.act p (C.loc p) with
  | .access _ _ _ => .tau p
  | .ret r _ => if C.pend p = none then .tau p else .ret p r

omit [DecidableEq P] [DecidableEq ι] in
lemma nextEv_isStepOf (p : P) (C : Config A B P L) : (I.nextEv p C).IsStepOf p := by
  unfold nextEv; split
  · rfl
  · split_ifs <;> rfl

lemma bstep_nextEv (p : P) (C : Config A B P L) : ∃ C', I.bstep acc C (I.nextEv p C) = some C' := by
  unfold nextEv
  split
  · rename_i i o k hact; simp [bstep, hact]
  · rename_i r l hact
    split_ifs with h
    · simp [bstep, hact, h]
    · simp [bstep, hact, h]

/-- The configurations of the schedule `f` (process `f j` takes its next step at time `j`). -/
noncomputable def schedCfg (C : Config A B P L) (f : ℕ → P) : ℕ → Config A B P L
  | 0 => C
  | j + 1 => (I.bstep acc (schedCfg C f j) (I.nextEv (f j) (schedCfg C f j))).getD
      (schedCfg C f j)

/-- The events of the schedule `f`. -/
noncomputable def schedEv (C : Config A B P L) (f : ℕ → P) (j : ℕ) : Event P A B :=
  I.nextEv (f j) (I.schedCfg acc C f j)

lemma brunFrom_schedEv (C : Config A B P L) (f : ℕ → P) (j : ℕ) :
    I.brunFrom acc C (pre (I.schedEv acc C f) j) = some (I.schedCfg acc C f j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pre, List.range_succ, List.map_append, ← pre, I.brunFrom_append_of_eq acc ih,
      List.map_singleton, brunFrom_singleton]
    obtain ⟨C', hC'⟩ := I.bstep_nextEv acc (f j) (I.schedCfg acc C f j)
    simp only [schedEv, schedCfg, hC', Option.getD_some]

omit [DecidableEq P] [DecidableEq ι] in
lemma pre_succ (g : ℕ → Event P A B) (k : ℕ) : pre g (k + 1) = pre g k ++ [g k] := by
  simp [pre, List.range_succ]

omit [DecidableEq P] [DecidableEq ι] in
lemma pre_append_sched (α : List (Event P A B)) (g : ℕ → Event P A B) (k : ℕ) :
    pre (fun k => if h : k < α.length then α[k] else g (k - α.length)) k =
      if k ≤ α.length then α.take k else α ++ pre g (k - α.length) := by
  induction k with
  | zero => simp [pre]
  | succ k ih =>
    rw [pre_succ, ih]
    by_cases hk : k < α.length
    · rw [ite_eq_left hk.le, ite_eq_left (by omega : k + 1 ≤ α.length), List.take_add_one,
        List.getElem?_eq_getElem hk]
      simp [hk]
    · rw [ite_eq_right (by omega : ¬ k + 1 ≤ α.length),
        show k + 1 - α.length = (k - α.length) + 1 by omega, pre_succ]
      have h2 : (if k ≤ α.length then α.take k else α ++ pre g (k - α.length)) =
          α ++ pre g (k - α.length) := by
        split_ifs with h
        · have : k = α.length := by omega
          subst this; simp [pre]
        · rfl
      rw [h2]; simp [hk]

/-- **Termination yields finite continuations.** In a correct implementation, after any finite
execution a correct process `p` completes its operation if all correct processes keep taking
steps (round robin): there is a continuation made only of algorithm steps of correct processes
after which `p` is idle. -/
theorem ByzCorrect.exists_completion [Fintype P] {f : ℕ} {adm : P → List A.Op → Prop}
    (hC : I.ByzCorrect acc f adm) {Bz : Finset P} (hBz : Bz.card ≤ f) {α : List (Event P A B)}
    {C : Config A B P L} (hα : I.brun acc α = some C) (hresp : ∀ e ∈ α, e.Respects Bz)
    (hadm : ∀ k, ∀ p ∉ Bz, adm p (opsOf (hist (α.take k)) p)) {p : P} (hp : p ∉ Bz) :
    ∃ β C', I.brunFrom acc C β = some C' ∧ (∀ e ∈ β, ∃ q ∉ Bz, e.IsStepOf q) ∧
      C'.pend p = none := by
  classical
  set l : List P := (Finset.univ.filter (· ∉ Bz)).toList with hl
  have hpl : p ∈ l := by simp [hl, hp]
  have hlen : 0 < l.length := List.length_pos_of_mem hpl
  let sch : ℕ → P := fun j => l[j % l.length]'(Nat.mod_lt _ hlen)
  have hsch : ∀ j, sch j ∉ Bz := fun j => by
    have : sch j ∈ l := List.getElem_mem _
    simpa [hl] using this
  set g := I.schedEv acc C sch with hg
  set ev : ℕ → Event P A B := fun k => if h : k < α.length then α[k] else g (k - α.length)
    with hev
  have hpre : ∀ k, pre ev k = if k ≤ α.length then α.take k else α ++ pre g (k - α.length) :=
    pre_append_sched α g
  have hgstep : ∀ k, ∀ e ∈ pre g k, ∃ q ∉ Bz, e.IsStepOf q := fun k e he => by
    simp only [pre, List.mem_map, List.mem_range] at he
    obtain ⟨j, -, rfl⟩ := he
    exact ⟨sch j, hsch j, I.nextEv_isStepOf _ _⟩
  have hopsg : ∀ k q, opsOf (hist (pre g k)) q = [] := fun k q => by
    simp only [opsOf, hist, List.filterMap_eq_nil_iff]
    intro ℓ hℓ
    obtain ⟨e, he, hℓe⟩ := List.mem_filterMap.1 hℓ
    obtain ⟨r, -, hr⟩ := hgstep k e he
    cases ℓ with
    | inv q' o => exact absurd hℓe (hr.hist_inv q' o)
    | ret _ _ => rfl
    | tau _ => rfl
  have hrun : ∀ k, ∃ D, I.brun acc (pre ev k) = some D := fun k => by
    rw [hpre]
    split_ifs with hk
    · rw [← List.take_append_drop k α, brun] at hα
      obtain ⟨D, hD, -⟩ := I.brunFrom_append_eq_some acc hα
      exact ⟨D, hD⟩
    · exact ⟨_, I.brunFrom_trans acc hα (I.brunFrom_schedEv acc C sch _)⟩
  obtain ⟨m, hm, hfin⟩ := hC.2 Bz hBz ev
    (fun k => ⟨hrun k, fun e he => by
      rw [hpre] at he
      split_ifs at he
      · exact hresp e (List.mem_of_mem_take he)
      · rcases List.mem_append.1 he with he | he
        · exact hresp e he
        · obtain ⟨q, hq, hqe⟩ := hgstep _ e he; exact hqe.respects hq⟩)
    (fun q hq k => by
      obtain ⟨i, hi, hiq⟩ := List.getElem_of_mem (show q ∈ l by simp [hl, hq])
      refine ⟨α.length + (i + l.length * k),
        by have := Nat.le_mul_of_pos_left k hlen; omega, ?_⟩
      simp only [hev, show ¬ (α.length + (i + l.length * k) < α.length) by omega, dite_false,
        Nat.add_sub_cancel_left, hg, schedEv]
      have : sch (i + l.length * k) = q := by
        simp only [sch, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, hiq]
      rw [this]; exact I.nextEv_isStepOf _ _)
    (fun k q hq => by
      rw [hpre]
      split_ifs with hk
      · exact hadm k q hq
      · have := hadm α.length q hq
        rw [List.take_length] at this
        simpa [hopsg] using this)
    p hp α.length
  rw [hpre] at hfin
  split_ifs at hfin with hk
  · have : m = α.length := le_antisymm hk hm
    subst this
    rw [List.take_length] at hfin
    exact ⟨[], C, rfl, by simp, hfin C hα⟩
  · refine ⟨pre g (m - α.length), _, I.brunFrom_schedEv acc C sch _, fun e he => hgstep _ e he,
      hfin _ ?_⟩
    exact I.brunFrom_trans acc hα (I.brunFrom_schedEv acc C sch _)

end Cslib.SharedMemory.Impl
