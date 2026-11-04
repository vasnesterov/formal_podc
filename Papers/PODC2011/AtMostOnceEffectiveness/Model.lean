import Mathlib

/-!
# The at-most-once problem: model

Sotirios Kentros, Aggelos Kiayias. *Solving the At-Most-Once Problem with Nearly Optimal
Effectiveness.* PODC 2011 (full version: arXiv 1107.2990v2, TCS 2013), Section 2.

`m` asynchronous crash-prone processes (`Fin m`) communicate through atomic read/write registers
(`R`, values in `V`) and perform jobs `1, …, n` (action `do_{p,j}`). Every process runs a
*deterministic* program: in local state `l` it either reads a register, writes a register, performs
a job, takes an internal step, or has terminated (`Step.halt`: no locally controlled action is
enabled). This covers the I/O-automaton formalisation of the paper for deterministic algorithms
(each process has exactly one enabled locally controlled action in every state).

* A configuration records the local states, the memory and a ghost `log` of all `do` actions.
* Finite executions are lists of process identifiers (`runFrom`); `Reachable` is the inductive
  version.
* Infinite executions (`Run`) may *stutter* (`ev k = none`), so finite executions followed by
  stuttering are runs too; a run is `Fair F` (the processes of `F` crash) if every process outside
  `F` takes a step at infinitely many times or terminates. Crashes are therefore fairness exemptions
  rather than events: a crashed process simply stops being scheduled (the paper's `stop_p`).
* `Run.Do n` is the number of jobs in `{1, …, n}` performed in the run (Definition 2.1),
  `Alg.AtMostOnce n` is Definition 2.2, `Alg.effectiveness n f` is Definition 2.4
  (the infimum of `Do` over the fair runs with at most `f` crashes).
-/

set_option linter.unusedSectionVars false

-- CSLib candidate: the generic at-most-once / task-allocation model (deterministic read/write
-- processes with `do` actions, stuttering runs, crashes as fairness exemptions, effectiveness).
namespace Podc.AtMostOnceEffectiveness

/-- What a process does next (its unique enabled locally controlled action). -/
inductive Step (R V L : Type) where
  /-- Read register `r` and continue in local state `k v` (`v` = the value read). -/
  | read (r : R) (k : V → L)
  /-- Write `v` to register `r` and continue in local state `l`. -/
  | write (r : R) (v : V) (l : L)
  /-- Perform job `j` (action `do_{p,j}`) and continue in local state `l`. -/
  | perform (j : ℕ) (l : L)
  /-- Internal step to local state `l`. -/
  | internal (l : L)
  /-- The process has terminated: no locally controlled action is enabled. -/
  | halt

/-- A deterministic algorithm for `m` processes with registers `R` holding values in `V` and
local states `L`. -/
structure Alg (m : ℕ) (R V L : Type) where
  /-- Initial values of the registers. -/
  memInit : R → V
  /-- Initial local states. -/
  locInit : Fin m → L
  /-- The next action of process `p` in local state `l`. -/
  next : Fin m → L → Step R V L

/-- A configuration: local states, memory and the (ghost) log of performed `do` actions, in
order. -/
structure Config (m : ℕ) (R V L : Type) where
  /-- Local states. -/
  loc : Fin m → L
  /-- Register values. -/
  mem : R → V
  /-- All `do_{p,j}` actions performed so far, oldest first. -/
  log : List (Fin m × ℕ)

namespace Alg

variable {m : ℕ} {R V L : Type} (A : Alg m R V L)

/-- The initial configuration. -/
def init : Config m R V L := ⟨A.locInit, A.memInit, []⟩

/-- Process `p` has terminated in `C`. -/
def Halted (C : Config m R V L) (p : Fin m) : Prop := A.next p (C.loc p) = .halt

variable [DecidableEq R]

/-- One step of process `p` (`none` if `p` has terminated). -/
def step (C : Config m R V L) (p : Fin m) : Option (Config m R V L) :=
  match A.next p (C.loc p) with
  | .read r k => some { C with loc := Function.update C.loc p (k (C.mem r)) }
  | .write r v l => some { C with mem := Function.update C.mem r v,
                                  loc := Function.update C.loc p l }
  | .perform j l => some { C with loc := Function.update C.loc p l, log := C.log ++ [(p, j)] }
  | .internal l => some { C with loc := Function.update C.loc p l }
  | .halt => none

/-- A step or a stutter (`none`). -/
def stepO (C : Config m R V L) : Option (Fin m) → Option (Config m R V L)
  | none => some C
  | some p => A.step C p

/-- Run a finite schedule from `C`. -/
def runFrom (C : Config m R V L) : List (Fin m) → Option (Config m R V L)
  | [] => some C
  | p :: α => (A.step C p).bind (fun C' => runFrom C' α)

/-- Reachable configurations (final configurations of finite executions). -/
inductive Reachable : Config m R V L → Prop
  | init : Reachable A.init
  | step {C C' : Config m R V L} {p : Fin m} : Reachable C → A.step C p = some C' →
      Reachable C'

/-- An infinite execution, possibly stuttering (`ev k = none`): finite executions followed by
stuttering are runs as well. -/
structure Run where
  /-- The configuration at time `k`. -/
  cfg : ℕ → Config m R V L
  /-- The process taking the step at time `k` (`none` = no step). -/
  ev : ℕ → Option (Fin m)
  cfg_zero : cfg 0 = A.init
  cfg_succ : ∀ k, A.stepO (cfg k) (ev k) = some (cfg (k + 1))

/-- Weak fairness with crash set `F`: every process outside `F` takes a step at infinitely many
times, or terminates. -/
def Run.Fair {A : Alg m R V L} (r : A.Run) (F : Finset (Fin m)) : Prop :=
  ∀ p, p ∉ F → ∀ k, ∃ k' ≥ k, r.ev k' = some p ∨ A.Halted (r.cfg k') p

/-- The jobs of `{1, …, n}` performed in `C` (`J_α` of Definition 2.1). -/
def jobs (n : ℕ) (C : Config m R V L) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun j => j ∈ C.log.map Prod.snd)

/-- The number of jobs performed in `C` (`Do(α)`, Definition 2.1). -/
def Do (n : ℕ) (C : Config m R V L) : ℕ := (jobs n C).card

open Classical in
/-- The jobs of `{1, …, n}` performed in a run. -/
noncomputable def Run.jobs {A : Alg m R V L} (r : A.Run) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun j => ∃ k, j ∈ (r.cfg k).log.map Prod.snd)

/-- The number of jobs performed in a run (`Do(α)`, Definition 2.1). -/
noncomputable def Run.Do {A : Alg m R V L} (r : A.Run) (n : ℕ) : ℕ := (r.jobs n).card

/-- Definition 2.2: the algorithm solves the at-most-once problem for the jobs `1, …, n`: in every
execution, every job is performed at most once (by all processes together). -/
def AtMostOnce (n : ℕ) : Prop :=
  ∀ C, A.Reachable C → ∀ j ∈ Finset.Icc 1 n, (C.log.map Prod.snd).count j ≤ 1

/-- Definition 2.4: the effectiveness `E_A(n, m, f)`, the minimum of `Do(α)` over all fair
executions with at most `f` crashes. -/
noncomputable def effectiveness (n f : ℕ) : ℕ :=
  sInf {d | ∃ (F : Finset (Fin m)) (r : A.Run), F.card ≤ f ∧ r.Fair F ∧ r.Do n = d}

/-! ## Basic lemmas -/

variable {A}

lemma step_loc_ne {C C' : Config m R V L} {p q : Fin m} (h : A.step C p = some C')
    (hq : q ≠ p) : C'.loc q = C.loc q := by
  unfold step at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [Function.update_of_ne hq]

lemma step_log {C C' : Config m R V L} {p : Fin m} (h : A.step C p = some C') :
    ∃ l, C'.log = C.log ++ l := by
  unfold step at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp

lemma step_ne_none_iff {C : Config m R V L} {p : Fin m} : A.step C p ≠ none ↔ ¬ A.Halted C p := by
  unfold step Halted
  split <;> simp_all

lemma step_isSome_of_not_halted {C : Config m R V L} {p : Fin m} (h : ¬ A.Halted C p) :
    ∃ C', A.step C p = some C' := by
  rw [← step_ne_none_iff] at h
  exact Option.ne_none_iff_exists'.mp h

lemma not_halted_of_step {C C' : Config m R V L} {p : Fin m} (h : A.step C p = some C') :
    ¬ A.Halted C p := by
  rw [← step_ne_none_iff, h]; simp

lemma jobs_mono {n : ℕ} {C C' : Config m R V L} (h : ∃ l, C'.log = C.log ++ l) :
    jobs n C ⊆ jobs n C' := by
  obtain ⟨l, hl⟩ := h
  intro j hj
  simp only [jobs, Finset.mem_filter, hl, List.map_append, List.mem_append] at hj ⊢
  exact ⟨hj.1, Or.inl hj.2⟩

namespace Run

variable {r : A.Run}

lemma reachable (r : A.Run) (k : ℕ) : A.Reachable (r.cfg k) := by
  induction k with
  | zero => rw [r.cfg_zero]; exact .init
  | succ k ih =>
    have h := r.cfg_succ k
    cases hk : r.ev k with
    | none => rw [hk] at h; simp only [stepO, Option.some.injEq] at h; rw [← h]; exact ih
    | some p => rw [hk] at h; exact .step ih h

lemma log_mono (r : A.Run) {k k' : ℕ} (h : k ≤ k') :
    ∃ l, (r.cfg k').log = (r.cfg k).log ++ l := by
  induction k', h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ k' _ ih =>
    obtain ⟨l, hl⟩ := ih
    have h := r.cfg_succ k'
    cases hk : r.ev k' with
    | none =>
      rw [hk] at h; simp only [stepO, Option.some.injEq] at h
      exact ⟨l, by rw [← h, hl]⟩
    | some p =>
      rw [hk] at h
      obtain ⟨l', hl'⟩ := step_log h
      exact ⟨l ++ l', by rw [hl', hl, List.append_assoc]⟩

lemma jobs_mono' (r : A.Run) (n : ℕ) {k k' : ℕ} (h : k ≤ k') :
    Alg.jobs n (r.cfg k) ⊆ Alg.jobs n (r.cfg k') := jobs_mono (r.log_mono h)

lemma jobs_cfg_subset (r : A.Run) (n k : ℕ) : Alg.jobs n (r.cfg k) ⊆ r.jobs n := by
  intro j hj
  simp only [Alg.jobs, Finset.mem_filter] at hj
  simp only [Run.jobs, Finset.mem_filter]
  exact ⟨hj.1, k, hj.2⟩

lemma do_cfg_le (r : A.Run) (n k : ℕ) : Alg.Do n (r.cfg k) ≤ r.Do n :=
  Finset.card_le_card (r.jobs_cfg_subset n k)

/-- The jobs of a run are the jobs of one of its configurations. -/
lemma exists_jobs_eq (r : A.Run) (n : ℕ) : ∃ k, r.jobs n = Alg.jobs n (r.cfg k) := by
  classical
  have : ∀ j ∈ r.jobs n, ∃ k, j ∈ Alg.jobs n (r.cfg k) := by
    intro j hj
    simp only [Run.jobs, Finset.mem_filter] at hj
    obtain ⟨hj, k, hk⟩ := hj
    exact ⟨k, Finset.mem_filter.mpr ⟨hj, hk⟩⟩
  choose! t ht using this
  refine ⟨(r.jobs n).sup t, ?_⟩
  apply Finset.Subset.antisymm
  · intro j hj
    exact r.jobs_mono' n (Finset.le_sup hj) (ht j hj)
  · exact r.jobs_cfg_subset n _

lemma do_le_of_forall (r : A.Run) (n b : ℕ) (h : ∀ k, Alg.Do n (r.cfg k) ≤ b) : r.Do n ≤ b := by
  obtain ⟨k, hk⟩ := r.exists_jobs_eq n
  unfold Run.Do; rw [hk]; exact h k

/-- After the last step, the configuration does not change. -/
lemma cfg_eq_of_stutter (r : A.Run) {K : ℕ} (h : ∀ k ≥ K, r.ev k = none) :
    ∀ k ≥ K, r.cfg k = r.cfg K := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hle ih =>
    have hs := r.cfg_succ k
    rw [h k hle] at hs
    simp only [stepO, Option.some.injEq] at hs
    rw [← hs, ih]

lemma do_eq_of_stutter (r : A.Run) (n : ℕ) {K : ℕ} (h : ∀ k ≥ K, r.ev k = none) :
    r.Do n = Alg.Do n (r.cfg K) := by
  apply le_antisymm
  · apply r.do_le_of_forall
    intro k
    rcases le_total k K with hk | hk
    · exact Finset.card_le_card (r.jobs_mono' n hk)
    · rw [r.cfg_eq_of_stutter h k hk]
  · exact r.do_cfg_le n K

end Run

end Alg

end Podc.AtMostOnceEffectiveness
