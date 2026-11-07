import Podc.Computability.Distributed.SharedMemory.Resilience
import Cslib.Computability.Distributed.SharedMemory.Consensus

/-!
# Lemma 6.1 of Taubenfeld (PODC 2012): the construction `A'` and its safety

Model: CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`), deterministic
processes, atomic base objects; a task algorithm is an `Impl` of `taskObj In Out` (invocation =
input, response = output), safety is `Impl.Solves` (the task relation holds in every finite
one-shot execution, for the inputs/outputs given so far).

Given an algorithm `A` (base objects `B i`, `i : ι`), the algorithm `A' = withOutput A` (proof
of Lemma 6.1) has one extra register `output : Option Out`, initially `none` (= ⊥), base objects
`OutB B Out : ι ⊕ Unit → ObjSpec`. A process of `A'` alternates
* `check`: read `output`; if it contains `v`, go to `adopt v` (then return `v`), else go to
* `exec`: take the next step of `A`; if `A` returns `r`, write `some r` into `output` (phase
  `fin r`) and then return `r`.

The local state of `A'` records the local state of `A` and the operation that `A` considers
pending (`OutL`), so that every configuration of `A'` *projects* (`projC`) to a configuration of
`A`; a step of `A'` is simulated by the labels `projStep A C ℓ` of `A` (`sim_step`): reading
`output` and returning are invisible, the write of `output` is the response of `A`. Processes
that adopt simply stop in the projected execution of `A` (they look crashed there).

* `wstep_cases` — classification of the steps of `A'`; `OutInv` — structural invariant;
* `sim_step` — the simulation (for invocations in one-shot executions, `outInv_cond`);
* `SafeInv`, `safeInv_of_run` — every finite one-shot execution of `A'` projects to one of `A`
  with the same inputs in which every value returned by `A'` (own decision or adopted) is the
  output of some process;
* `Colorless` — colorless tasks: `Δ ins outs ↔ R (vals ins) (vals outs)` for a relation `R`
  on (input value set, output value set) that is downward closed in the output set (as for the
  colorless tasks of Herlihy–Kozlov–Rajsbaum, whose output complexes are closed under faces);
  `AdoptClosed` — the only consequence used: outputs may be replaced by `⊥` or by an output of
  another process (`Colorless.adoptClosed`);
* `solves_withOutput` — **safety of `A'`**: `A.Solves T → (withOutput A).Solves T` for
  adopt-closed `T`. Colorlessness is needed exactly here (adopting).

Liveness is in `ColorlessLiveness.lean`, the statements of Section 6 in `Section6.lean`.
-/

set_option linter.unusedSectionVars false

namespace Podc.CloserLookFT

open Cslib.SharedMemory

/-! ## The construction `A'` -/

/-- Control phase of a process of `A'`. -/
inductive Phase (Out : Type) where
  /-- no pending operation (initially, and after returning) -/
  | idle
  /-- next step: read the register `output` -/
  | check
  /-- next step: the next action of `A` -/
  | exec
  /-- `A` returned `r` and `r` was written into `output`; next step: return `r` -/
  | fin (r : Out)
  /-- `output` was found to contain `v`; next step: return `v` (adopt) -/
  | adopt (v : Out)

variable {P : Type} [DecidableEq P] {In Out : Type} [Inhabited Out]
  {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}

/-- The base objects of `A'`: those of `A` plus one register `output` over `Option Out`,
initially `none` (= ⊥). -/
abbrev OutB (B : ι → ObjSpec) (Out : Type) : ι ⊕ Unit → ObjSpec :=
  Sum.elim B fun _ => register (Option Out) none

/-- Local states of `A'`: the local state of `A`, the operation `A` considers pending, and the
phase. -/
abbrev OutL (L In Out : Type) : Type := L × Option In × Phase Out

/-- The local state after reading `x` from `output`: adopt `v` if `x = some v`, otherwise go on
with `A`. -/
def checkNext (s : OutL L In Out) : Option Out → OutL L In Out
  | none => (s.1, s.2.1, .exec)
  | some v => (s.1, s.2.1, .adopt v)

/-- The algorithm `A'` of the proof of Lemma 6.1. -/
def withOutput (A : Impl (taskObj In Out) B P L) :
    Impl (taskObj In Out) (OutB B Out) P (OutL L In Out) where
  memInit
    | .inl i => A.memInit i
    | .inr _ => (none : Option Out)
  locInit p := (A.locInit p, none, .idle)
  invoke p s o := (A.invoke p s.1 o, some o, .check)
  act p s :=
    match s.2.2 with
    | .check => .access (.inr ()) (RWOp.read : RWOp (Option Out)) (checkNext s)
    | .exec =>
      match A.act p s.1 with
      | .access i o k => .access (.inl i) o fun r => (k r, s.2.1, .check)
      | .ret r l' => .access (.inr ()) (RWOp.write (some r) : RWOp (Option Out))
          fun _ => (l', none, .fin r)
    | .fin r => .ret r (s.1, s.2.1, .idle)
    | .adopt v => .ret v (s.1, s.2.1, .idle)
    | .idle => .ret (default : Out) (s.1, s.2.1, .idle)
  allowed := A.allowed


/-- Configurations of `A'`. -/
abbrev OutCfg (In Out : Type) [Inhabited Out] (B : ι → ObjSpec) (P L : Type) : Type :=
  Config (taskObj In Out) (OutB B Out) P (OutL L In Out)

/-- The content of the register `output`. -/
def outReg (C : OutCfg In Out B P L) : Option Out := C.mem (.inr ())

variable (A : Impl (taskObj In Out) B P L)

section Steps

variable {A} {C D : OutCfg In Out B P L} {p : P}

/-- The action of `A'` in phase `check`. -/
lemma act_check {s : OutL L In Out} (h : s.2.2 = .check) :
    (withOutput A).act p s = .access (.inr ()) (RWOp.read : RWOp (Option Out)) (checkNext s) := by
  obtain ⟨l, a, ph⟩ := s; subst h; rfl

/-- The action of `A'` in phase `exec` when `A` accesses a base object. -/
lemma act_exec_access {s : OutL L In Out} (h : s.2.2 = .exec) {i : ι} {o : (B i).Op}
    {k : (B i).Resp → L} (hA : A.act p s.1 = .access i o k) :
    (withOutput A).act p s = .access (.inl i) o fun r => (k r, s.2.1, .check) := by
  obtain ⟨l, a, ph⟩ := s; subst h; simp only [withOutput, hA]

/-- The action of `A'` in phase `exec` when `A` returns: write `output`. -/
lemma act_exec_ret {s : OutL L In Out} (h : s.2.2 = .exec) {r : Out} {l' : L}
    (hA : A.act p s.1 = .ret r l') :
    (withOutput A).act p s = .access (.inr ()) (RWOp.write (some r) : RWOp (Option Out))
      fun _ => (l', none, .fin r) := by
  obtain ⟨l, a, ph⟩ := s; subst h; simp only [withOutput, hA]

/-- The steps of `A'`. -/
lemma wstep_cases {ℓ : Label P (taskObj In Out)} (h : (withOutput A).step C ℓ = some D) :
    (∃ p o, ℓ = .inv p o ∧ C.pend p = none ∧ A.allowed p o ∧
      D = { C with pend := Function.update C.pend p (some o),
                   loc := Function.update C.loc p (A.invoke p (C.loc p).1 o, some o, .check) }) ∨
    (∃ p, ℓ = .tau p ∧ C.pend p ≠ none ∧ (C.loc p).2.2 = .check ∧
      D = { C with loc := Function.update C.loc p (checkNext (C.loc p) (outReg C)) }) ∨
    (∃ p i o k, ℓ = .tau p ∧ C.pend p ≠ none ∧ (C.loc p).2.2 = .exec ∧
      A.act p (C.loc p).1 = .access i o k ∧
      D = { C with mem := Function.update C.mem (.inl i) ((B i).δ (C.mem (.inl i)) o).1,
                   loc := Function.update C.loc p
                     (k ((B i).δ (C.mem (.inl i)) o).2, (C.loc p).2.1, .check) }) ∨
    (∃ p r l', ℓ = .tau p ∧ C.pend p ≠ none ∧ (C.loc p).2.2 = .exec ∧
      A.act p (C.loc p).1 = .ret r l' ∧
      D = { C with mem := Function.update C.mem (.inr ()) (some r : Option Out),
                   loc := Function.update C.loc p (l', none, .fin r) }) ∨
    (∃ p r, ℓ = .ret p r ∧ C.pend p ≠ none ∧
      ((C.loc p).2.2 = .fin r ∨ (C.loc p).2.2 = .adopt r ∨ (C.loc p).2.2 = .idle) ∧
      D = { C with pend := Function.update C.pend p none,
                   loc := Function.update C.loc p ((C.loc p).1, (C.loc p).2.1, .idle) }) := by
  cases ℓ with
  | inv p o =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := Impl.step_inv h
    left
    refine ⟨p, o, rfl, h1, h2, ?_⟩
    cases D; simp only at h3 h4 h5; subst h3 h4 h5; rfl
  | tau p =>
    have hp := (Impl.step_tau h).1
    rcases hph : (C.loc p).2.2 with _ | _ | _ | r | v
    · simp [Impl.step, hp, withOutput, hph] at h
    · rw [Impl.step_tau_eq_some hp (act_check hph)] at h
      cases h
      right; left
      refine ⟨p, rfl, hp, hph, ?_⟩
      simp [outReg]
    · cases hA : A.act p (C.loc p).1 with
      | access i o k =>
        rw [Impl.step_tau_eq_some hp (act_exec_access hph hA)] at h
        cases h
        right; right; left
        exact ⟨p, i, o, k, rfl, hp, hph, hA, rfl⟩
      | ret r l' =>
        rw [Impl.step_tau_eq_some hp (act_exec_ret hph hA)] at h
        cases h
        right; right; right; left
        exact ⟨p, r, l', rfl, hp, hph, hA, rfl⟩
    · simp [Impl.step, hp, withOutput, hph] at h
    · simp [Impl.step, hp, withOutput, hph] at h
  | ret p r =>
    obtain ⟨h1, h2, h3, l, h4, h5⟩ := Impl.step_ret h
    right; right; right; right
    have key : ((C.loc p).2.2 = .fin r ∨ (C.loc p).2.2 = .adopt r ∨ (C.loc p).2.2 = .idle) ∧
        l = ((C.loc p).1, (C.loc p).2.1, .idle) := by
      rcases hph : (C.loc p).2.2 with _ | _ | _ | r' | v <;> simp only [withOutput, hph] at h4
      · cases h4; simp
      · cases h4
      · split at h4 <;> cases h4
      · cases h4; simp
      · cases h4; simp
    refine ⟨p, r, rfl, h1, key.1, ?_⟩
    cases D; simp only at h2 h3 h5; subst h2 h3 h5; rw [key.2]

end Steps

/-! ## Simulation of `A'` by `A` -/

/-- The projection of a configuration of `A'` to a configuration of `A`: local states and
pending operations as recorded by `A'`, and the base objects of `A`. -/
def projC (C : OutCfg In Out B P L) : Config (taskObj In Out) B P L :=
  ⟨fun p => (C.loc p).1, fun p => (C.loc p).2.1, fun i => C.mem (.inl i)⟩

/-- The labels of `A` simulated by a step of `A'` from `C`: invocations are copied, steps of
`A` (in phase `exec`) become the corresponding step of `A` (writing `output` is the response of
`A`), reading `output` and the responses of `A'` are invisible. -/
def projStep (C : OutCfg In Out B P L) :
    Label P (taskObj In Out) → List (Label P (taskObj In Out))
  | .inv p o => [.inv p o]
  | .ret _ _ => []
  | .tau p =>
    match (C.loc p).2.2 with
    | .exec =>
      match A.act p (C.loc p).1 with
      | .access _ _ _ => [.tau p]
      | .ret r _ => [.ret p r]
    | _ => []

/-- Structural invariant of `A'`: in phases `check`/`exec` the operation recorded for `A` is
the pending one, idle processes have no pending operation, and processes in phases
`fin`/`adopt` have seen a non-`⊥` `output`. -/
def OutInv (C : OutCfg In Out B P L) : Prop :=
  ∀ p, ((C.loc p).2.2 = .check ∨ (C.loc p).2.2 = .exec → (C.loc p).2.1 = C.pend p) ∧
    ((C.loc p).2.2 = .idle → C.pend p = none) ∧
    (∀ v, (C.loc p).2.2 = .fin v ∨ (C.loc p).2.2 = .adopt v → outReg C ≠ none)

variable {A}

/-- The invariant holds initially. -/
lemma outInv_initCfg : OutInv (withOutput A).initCfg := by
  intro p; simp [Impl.initCfg, withOutput]

/-- Reading `output` does not change the recorded state of `A`. -/
lemma checkNext_fst (s : OutL L In Out) (x : Option Out) : (checkNext s x).1 = s.1 := by
  cases x <;> rfl

/-- Reading `output` does not change the recorded pending operation of `A`. -/
lemma checkNext_snd_fst (s : OutL L In Out) (x : Option Out) :
    (checkNext s x).2.1 = s.2.1 := by
  cases x <;> rfl

/-- Updating a base object of `A` does not change `output`. -/
@[simp] lemma update_inl_inr (f : (j : ι ⊕ Unit) → (OutB B Out j).State) (i : ι)
    (x : (B i).State) : Function.update f (.inl i) x (.inr ()) = f (.inr ()) :=
  Function.update_of_ne (by simp) _ _

/-- Updating a base object of `A` inside the memory of `A'`. -/
lemma update_inl_inl (f : (j : ι ⊕ Unit) → (OutB B Out j).State) (i : ι)
    (x : (B i).State) (j : ι) :
    Function.update f (.inl i) x (.inl j) = Function.update (fun j => f (.inl j)) i x j := by
  unfold Function.update
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]; rfl

/-- Writing `output`. -/
@[simp] lemma update_inr_self (f : (j : ι ⊕ Unit) → (OutB B Out j).State) (x : Option Out) :
    Function.update f (.inr ()) (x : (OutB B Out (.inr ())).State) (.inr ()) = x :=
  Function.update_self ..

/-- The invariant is preserved by steps. -/
lemma outInv_step {C D : OutCfg In Out B P L} {ℓ : Label P (taskObj In Out)} (hI : OutInv C)
    (h : (withOutput A).step C ℓ = some D) : OutInv D := by
  rcases wstep_cases h with ⟨p, o, rfl, hp, -, rfl⟩ | ⟨p, rfl, hp, hph, rfl⟩ |
    ⟨p, i, o, k, rfl, hp, hph, hA, rfl⟩ | ⟨p, r, l', rfl, hp, hph, hA, rfl⟩ |
    ⟨p, r, rfl, hp, hph, rfl⟩
  · intro q
    by_cases hq : q = p
    · subst hq; exact ⟨fun _ => by simp; rfl, by simp, by simp⟩
    · simpa [Function.update_of_ne hq, outReg] using hI q
  · intro q
    by_cases hq : q = p
    · subst hq
      obtain ⟨h1, -, -⟩ := hI q
      cases hx : outReg C with
      | none => simp [checkNext, outReg] at h1 ⊢; exact h1 (Or.inl hph)
      | some v => simp [outReg] at hx; simp [checkNext, hx, outReg]
    · simpa [Function.update_of_ne hq, outReg] using hI q
  · intro q
    by_cases hq : q = p
    · subst hq
      obtain ⟨h1, -, -⟩ := hI q
      simpa [outReg] using h1 (Or.inr hph)
    · simpa [Function.update_of_ne hq, outReg] using hI q
  · intro q
    by_cases hq : q = p
    · subst hq; simp [outReg]
    · obtain ⟨h1, h2, -⟩ := hI q
      simpa [Function.update_of_ne hq, outReg] using ⟨h1, h2⟩
  · intro q
    by_cases hq : q = p
    · subst hq; simp
    · simpa [Function.update_of_ne hq, outReg] using hI q

/-- The invariant holds in all reachable configurations. -/
lemma outInv_of_run {α : List (Label P (taskObj In Out))} {C : OutCfg In Out B P L}
    (h : (withOutput A).run α = some C) : OutInv C :=
  Impl.invariant_of_run outInv_initCfg (fun _ _ _ hI hs => outInv_step hI hs) h

/-- Once written, `output` stays non-`⊥`. -/
lemma outReg_ne_none_step {C D : OutCfg In Out B P L} {ℓ : Label P (taskObj In Out)}
    (h : (withOutput A).step C ℓ = some D) (hC : outReg C ≠ none) : outReg D ≠ none := by
  rcases wstep_cases h with ⟨p, o, rfl, hp, -, rfl⟩ | ⟨p, rfl, hp, hph, rfl⟩ |
    ⟨p, i, o, k, rfl, hp, hph, hA, rfl⟩ | ⟨p, r, l', rfl, hp, hph, hA, rfl⟩ |
    ⟨p, r, rfl, hp, hph, rfl⟩
  · exact hC
  · exact hC
  · simpa [outReg] using hC
  · simp [outReg]
  · exact hC

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
/-- **Simulation.** A step of `A'` from `C` is simulated by the labels `projStep A C ℓ` of `A`
from `projC C` (an invocation must find `A`'s pending operation empty, which holds in one-shot
executions). -/
lemma sim_step {C D : OutCfg In Out B P L} {ℓ : Label P (taskObj In Out)} (hI : OutInv C)
    (h : (withOutput A).step C ℓ = some D)
    (hinv : ∀ p o, ℓ = .inv p o → (C.loc p).2.1 = none) :
    A.runFrom (projC C) (projStep A C ℓ) = some (projC D) := by
  rcases wstep_cases h with ⟨p, o, rfl, hp, ho, rfl⟩ | ⟨p, rfl, hp, hph, rfl⟩ |
    ⟨p, i, o, k, rfl, hp, hph, hA, rfl⟩ | ⟨p, r, l', rfl, hp, hph, hA, rfl⟩ |
    ⟨p, r, rfl, hp, hph, rfl⟩
  · simp only [projStep, Impl.runFrom_singleton]
    rw [Impl.step_inv_eq_some (hinv p o rfl) ho]
    simp only [projC, Option.some.injEq]
    congr 1 <;> funext x <;> (try by_cases hq : x = p) <;>
      (simp [*, update_inl_inl, checkNext_fst, checkNext_snd_fst, Function.update_apply]
       try (unfold Function.update; split_ifs <;> simp_all <;> rfl))
  · simp only [projStep, hph, Impl.runFrom_nil, projC, Option.some.injEq]
    congr 1 <;> funext x <;> (try by_cases hq : x = p) <;>
      (simp [*, update_inl_inl, checkNext_fst, checkNext_snd_fst, Function.update_apply]
       try (unfold Function.update; split_ifs <;> simp_all <;> rfl))
  · have hpA : (projC C).pend p ≠ none := by
      simpa [projC, (hI p).1 (Or.inr hph)] using hp
    simp only [projStep, hph, hA, Impl.runFrom_singleton]
    rw [Impl.step_tau_eq_some hpA (show A.act p ((projC C).loc p) = _ from hA)]
    simp only [projC, Option.some.injEq]
    congr 1 <;> funext x <;> (try by_cases hq : x = p) <;>
      (simp [*, update_inl_inl, checkNext_fst, checkNext_snd_fst, Function.update_apply]
       try (unfold Function.update; split_ifs <;> simp_all <;> rfl))
  · have hpA : (projC C).pend p ≠ none := by
      simpa [projC, (hI p).1 (Or.inr hph)] using hp
    simp only [projStep, hph, hA, Impl.runFrom_singleton]
    rw [Impl.step_ret_eq_some hpA (show A.act p ((projC C).loc p) = _ from hA)]
    simp only [projC, Option.some.injEq]
    congr 1 <;> funext x <;> (try by_cases hq : x = p) <;>
      (simp [*, update_inl_inl, checkNext_fst, checkNext_snd_fst, Function.update_apply]
       try (unfold Function.update; split_ifs <;> simp_all <;> rfl))
  · simp only [projStep, Impl.runFrom_nil, projC, Option.some.injEq]
    congr 1 <;> funext x <;> (try by_cases hq : x = p) <;>
      (simp [*, update_inl_inl, checkNext_fst, checkNext_snd_fst, Function.update_apply]
       try (unfold Function.update; split_ifs <;> simp_all <;> rfl))

/-- The simulated labels contain exactly the invocations of the step. -/
lemma opsOf_projStep (C : OutCfg In Out B P L) (ℓ : Label P (taskObj In Out)) (q : P) :
    opsOf (projStep A C ℓ) q = (ℓ.invOf q).toList := by
  cases ℓ with
  | inv p o =>
    simp only [projStep, opsOf, List.filterMap_cons, List.filterMap_nil, Label.invOf_inv]
    split_ifs <;> rfl
  | ret p r => simp [projStep, opsOf]
  | tau p =>
    simp only [projStep, Label.invOf_tau, Option.toList_none]
    split
    · split <;> simp [opsOf]
    · simp [opsOf]

/-- A process that has not invoked anything is still in its initial local state. -/
lemma loc_eq_locInit {α : List (Label P (taskObj In Out))} {C : OutCfg In Out B P L}
    (h : (withOutput A).run α = some C) {p : P} (hp : opsOf α p = []) :
    C.loc p = (withOutput A).locInit p :=
  ((withOutput A).runFrom_other h ((withOutput A).proc_ne_of_opsOf_eq_nil h hp)).1

/-- In a one-shot execution, an invocation finds `A`'s pending operation empty. -/
lemma outInv_cond {α : List (Label P (taskObj In Out))} {C : OutCfg In Out B P L}
    (h : (withOutput A).run α = some C) {ℓ : Label P (taskObj In Out)}
    (hos : OneShot (α ++ [ℓ])) : ∀ p o, ℓ = .inv p o → (C.loc p).2.1 = none := by
  rintro p o rfl
  have h1 := hos p
  simp only [opsOf_append, List.length_append, opsOf_cons, Label.invOf_inv, ↓reduceIte,
    Option.toList_some, opsOf_nil, List.append_nil, List.length_singleton] at h1
  have hp : opsOf α p = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [loc_eq_locInit h hp]; rfl

/-- Outputs persist. -/
lemma outputs_mono {α : List (Label P (taskObj In Out))} (β : List (Label P (taskObj In Out)))
    {q : P} {v : Out} (h : outputs α q = some v) : outputs (α ++ β) q = some v := by
  rw [outputs_append_of_ne_none β (by rw [h]; exact Option.some_ne_none _), h]

/-- The safety invariant: the projected execution `α` of `A`, with the same invocations; every
value in `output`, adopted, or output by `A'` is an output of some process in `α`. -/
def SafeInv (A : Impl (taskObj In Out) B P L) (α' : List (Label P (taskObj In Out)))
    (C : OutCfg In Out B P L) : Prop :=
  ∃ α, A.run α = some (projC C) ∧ (∀ p, opsOf α p = opsOf α' p) ∧
    (∀ v, outReg C = some v → ∃ q, outputs α q = some v) ∧
    (∀ p v, (C.loc p).2.2 = .adopt v → ∃ q, outputs α q = some v) ∧
    (∀ p r, (C.loc p).2.2 = .fin r → outputs α p = some r) ∧
    (∀ p v, outputs α' p = some v → ∃ q, outputs α q = some v)

/-- The safety invariant holds along one-shot executions of `A'`. -/
lemma safeInv_of_run {α' : List (Label P (taskObj In Out))} {C : OutCfg In Out B P L}
    (h : (withOutput A).run α' = some C) (hos : OneShot α') : SafeInv A α' C := by
  induction α' using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run_nil, Option.some.injEq] at h; subst h
    refine ⟨[], ?_, fun _ => rfl, ?_, ?_, ?_, ?_⟩
    · rfl
    · intro v hv; simp [outReg, Impl.initCfg, withOutput] at hv
    · intro p v hv; simp [Impl.initCfg, withOutput] at hv
    · intro p v hv; simp [Impl.initCfg, withOutput] at hv
    · intro p v hv; simp [outputs, respsOf] at hv
  | append_singleton α' ℓ ih =>
    rw [Impl.run_concat] at h
    cases hC : (withOutput A).run α' with
    | none => simp [hC] at h
    | some C₀ =>
      simp only [hC, Option.bind_some] at h
      obtain ⟨α, hα, hops, hreg, hadopt, hfin, hout⟩ := ih hC hos.of_append
      have hI := outInv_of_run hC
      have hsim := sim_step hI h (outInv_cond hC hos)
      refine ⟨α ++ projStep A C₀ ℓ, by rw [Impl.run_append_of_eq A hα, hsim], ?_, ?_⟩
      · intro p
        rw [opsOf_append, opsOf_append, hops, opsOf_projStep]; congr 1
      rcases wstep_cases h with ⟨p, o, rfl, hp, -, rfl⟩ | ⟨p, rfl, hp, hph, rfl⟩ |
        ⟨p, i, o, k, rfl, hp, hph, hA, rfl⟩ | ⟨p, r, l', rfl, hp, hph, hA, rfl⟩ |
        ⟨p, r, rfl, hp, hph, rfl⟩
      · simp only [projStep]
        refine ⟨fun v hv => ?_, fun q v hv => ?_, fun q r hr => ?_, fun q v hv => ?_⟩
        · obtain ⟨q, hq⟩ := hreg v hv; exact ⟨q, outputs_mono _ hq⟩
        · by_cases hq : q = p
          · subst hq; simp at hv
          · obtain ⟨q', hq'⟩ := hadopt q v (by simpa [Function.update_of_ne hq] using hv)
            exact ⟨q', outputs_mono _ hq'⟩
        · by_cases hq : q = p
          · subst hq; simp at hr
          · exact outputs_mono _ (hfin q r (by simpa [Function.update_of_ne hq] using hr))
        · rw [outputs_append_inv] at hv
          obtain ⟨q', hq'⟩ := hout q v hv; exact ⟨q', outputs_mono _ hq'⟩
      · simp only [projStep, hph, List.append_nil]
        refine ⟨hreg, fun q v hv => ?_, fun q r hr => ?_, fun q v hv => ?_⟩
        · by_cases hq : q = p
          · subst hq
            cases hx : outReg C₀ with
            | none => simp [hx, checkNext] at hv
            | some w =>
              simp [hx, checkNext] at hv; subst hv; exact hreg w hx
          · exact hadopt q v (by simpa [Function.update_of_ne hq] using hv)
        · by_cases hq : q = p
          · subst hq
            cases hx : outReg C₀ <;> simp [hx, checkNext] at hr
          · exact hfin q r (by simpa [Function.update_of_ne hq] using hr)
        · rw [outputs_append_tau] at hv; exact hout q v hv
      · simp only [projStep, hph, hA]
        refine ⟨fun v hv => ?_, fun q v hv => ?_, fun q r hr => ?_, fun q v hv => ?_⟩
        · obtain ⟨q, hq⟩ := hreg v (by simpa [outReg] using hv)
          exact ⟨q, outputs_mono _ hq⟩
        · by_cases hq : q = p
          · subst hq; simp at hv
          · obtain ⟨q', hq'⟩ := hadopt q v (by simpa [Function.update_of_ne hq] using hv)
            exact ⟨q', outputs_mono _ hq'⟩
        · by_cases hq : q = p
          · subst hq; simp at hr
          · exact outputs_mono _ (hfin q r (by simpa [Function.update_of_ne hq] using hr))
        · rw [outputs_append_tau] at hv
          obtain ⟨q', hq'⟩ := hout q v hv; exact ⟨q', outputs_mono _ hq'⟩
      · simp only [projStep, hph, hA]
        -- `p` has not output in `α` yet
        have hpA : (projC C₀).pend p ≠ none := by
          simpa [projC, (hI p).1 (Or.inr hph)] using hp
        have hnone : outputs α p = none := by
          have h1 := A.run_pend_counts hα hpA
          have h2 := hos p
          rw [hops p] at h1
          simp only [opsOf_append, List.length_append] at h2
          have : respsOf α p = [] := List.eq_nil_of_length_eq_zero (by omega)
          simp [outputs, this]
        have hnew : outputs (α ++ [.ret p r]) p = some r := by
          rw [outputs_concat, hnone]; simp
        refine ⟨fun v hv => ?_, fun q v hv => ?_, fun q r' hr => ?_, fun q v hv => ?_⟩
        · simp [outReg] at hv; cases hv; exact ⟨p, hnew⟩
        · by_cases hq : q = p
          · subst hq; simp at hv
          · obtain ⟨q', hq'⟩ := hadopt q v (by simpa [Function.update_of_ne hq] using hv)
            exact ⟨q', outputs_mono _ hq'⟩
        · by_cases hq : q = p
          · subst hq; simp at hr; cases hr; exact hnew
          · exact outputs_mono _ (hfin q r' (by simpa [Function.update_of_ne hq] using hr))
        · rw [outputs_append_tau] at hv
          obtain ⟨q', hq'⟩ := hout q v hv; exact ⟨q', outputs_mono _ hq'⟩
      · simp only [projStep, List.append_nil]
        refine ⟨hreg, fun q v hv => ?_, fun q r' hr => ?_, fun q v hv => ?_⟩
        · by_cases hq : q = p
          · subst hq; simp at hv
          · exact hadopt q v (by simpa [Function.update_of_ne hq] using hv)
        · by_cases hq : q = p
          · subst hq; simp at hr
          · exact hfin q r' (by simpa [Function.update_of_ne hq] using hr)
        · rw [outputs_concat] at hv
          cases ho : outputs α' q with
          | some w => rw [ho] at hv; simp at hv; subst hv; exact hout q w ho
          | none =>
            rw [ho] at hv
            by_cases hq : q = p
            · subst hq
              simp at hv; subst hv
              rcases hph with hph | hph | hph
              · exact ⟨q, hfin q _ hph⟩
              · exact hadopt q _ hph
              · exact absurd ((hI q).2.1 hph) hp
            · simp at hv; exact absurd hv.1.symm hq

/-! ## Colorless tasks and safety of `A'` -/

/-- The set of values of a partial vector. -/
def vals {X : Type} (f : P → Option X) : Set X := {x | ∃ p, f p = some x}

/-- A task is **colorless** if its input/output relation only depends on the *set* of input
values and the *set* of output values, and allowed output sets are closed under subsets
(so a process may adopt the output of another process, or not have decided yet). -/
def Colorless (T : Cslib.SharedMemory.Task P) : Prop :=
  ∃ R : Set T.In → Set T.Out → Prop, (∀ X Y Y', Y' ⊆ Y → R X Y → R X Y') ∧
    ∀ ins outs, T.Δ ins outs ↔ R (vals ins) (vals outs)

/-- The only consequence of colorlessness used in Lemma 6.1: legal outputs stay legal if
processes replace their output by `⊥` or by the output of another process. -/
def AdoptClosed (T : Cslib.SharedMemory.Task P) : Prop :=
  ∀ ins outs outs', T.Δ ins outs → (∀ p y, outs' p = some y → ∃ q, outs q = some y) →
    T.Δ ins outs'

lemma Colorless.adoptClosed {T : Cslib.SharedMemory.Task P} (h : Colorless T) :
    AdoptClosed T := by
  obtain ⟨R, hmono, hR⟩ := h
  intro ins outs outs' hΔ hsub
  rw [hR] at hΔ ⊢
  refine hmono _ _ _ (fun y ⟨p, hp⟩ => ?_) hΔ
  obtain ⟨q, hq⟩ := hsub p y hp
  exact ⟨q, hq⟩

/-- Safety of `A'`: if `A` solves an adopt-closed (e.g. colorless) task, so does `A'`. -/
theorem solves_withOutput {T : Cslib.SharedMemory.Task P} [Inhabited T.Out]
    (hT : AdoptClosed T)
    {A : Impl (taskObj T.In T.Out) B P L} (hA : A.Solves T) : (withOutput A).Solves T := by
  rintro α' ⟨C, hC⟩ hos
  obtain ⟨α, hα, hops, -, -, -, hout⟩ := safeInv_of_run hC hos
  have hos' : OneShot α := fun p => by rw [hops]; exact hos p
  have hin : inputs α = inputs α' := funext fun p => by simp only [inputs, hops]
  have := hA α ⟨_, hα⟩ hos'
  rw [hin] at this
  exact hT _ _ _ this hout

end Podc.CloserLookFT
