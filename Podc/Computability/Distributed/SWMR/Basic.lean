/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Computability/Distributed/SWMR/Basic.lean
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.OfFn

/-!
# The asynchronous read/write SWMR model with crash failures

A small, self-contained model of the standard asynchronous shared-memory model used in
task-computability results (Herlihy–Shavit, Biran–Moran–Zaks, …):

* a finite set `P` of deterministic processes (state machines with possibly infinitely many
  states, `Alg.S`);
* every process `p` owns a bank of single-writer multi-reader atomic registers indexed by `K`
  (register `i` of every process holds values of type `V i`, initially `Alg.v₀ i`); usually
  `K = Unit` (one register per process);
* one atomic step of a process is (`Act`) a write to one of its own registers, a read of any
  register of any process, or a *decision* `decide y`, which irrevocably sets the output of the
  process to `y` (the first decision counts; the process may keep taking steps afterwards);
* an execution is determined by the inputs and the schedule, a finite (`List P`) or infinite
  (`ℕ → P`) sequence of process identifiers (each entry is one step of that process);
* crash failures: in an infinite schedule a process is *correct* if it takes infinitely many
  steps (`InfOften`), *faulty* otherwise.

A task is a predicate `Task P In Out` on input vectors and partial output vectors. An algorithm
solves a task `t`-resiliently (`Alg.Solves A t T`) if every finite execution satisfies the task
(safety) and in every infinite execution with at most `t` faulty processes every correct process
eventually decides (termination). With `t = card P - 1` this is wait-freedom (an infinite schedule
always has a correct process).

## Main definitions

* `Act`, `Alg`, `Config`, `Alg.step`, `Alg.run`, `Alg.initCfg`
* `InfOften`, `Faulty`, `pre`, `Alg.Solves`
* `AgreeOn`: configurations that agree on the local states and outputs of a set of processes and
  on the whole memory; runs of these processes preserve it (`AgreeOn.run`)

## Main statements

* `Alg.run_append`, `Alg.out_run_of_out`: outputs are irrevocable
* `Alg.Solves.exists_decide`: the processes of a set `S` with `|Sᶜ| ≤ t` running alone after any
  finite execution eventually decide (round-robin scheduling of `S`)
-/

namespace Cslib.SWMR

/-- A step of a process: write `v` to its own register `i`, read register `i` of process `q`
(continuation `k` receives the value), or decide `y`. Each carries the next local state. -/
inductive Act (P K : Type) (V : K → Type) (Out S : Type) : Type
  | write (i : K) (v : V i) (s : S)
  | read (q : P) (i : K) (k : V i → S)
  | decide (y : Out) (s : S)

/-- A deterministic algorithm in the SWMR read/write model: processes `P`, register banks indexed
by `K` with values `V i`, inputs `In`, outputs `Out`. -/
structure Alg (P K : Type) (V : K → Type) (In Out : Type) where
  /-- Local states. -/
  S : Type
  /-- Initial value of register `i` (the same for every process). -/
  v₀ : ∀ i, V i
  /-- Initial local state of process `p` with input `x`. -/
  init : P → In → S
  /-- The next step of process `p` in local state `s`. -/
  next : P → S → Act P K V Out S

variable {P K : Type} {V : K → Type} {In Out : Type}

/-- A configuration: local states, memory (`mem p i` = register `i` of `p`), outputs. -/
@[ext]
structure Config (A : Alg P K V In Out) where
  loc : P → A.S
  mem : P → ∀ i, V i
  out : P → Option Out

namespace Alg

variable (A : Alg P K V In Out) [DecidableEq P] [DecidableEq K]

/-- One atomic step of process `p`. -/
def step (p : P) (C : Config A) : Config A :=
  match A.next p (C.loc p) with
  | .write i v s =>
    { C with loc := Function.update C.loc p s,
             mem := Function.update C.mem p (Function.update (C.mem p) i v) }
  | .read q i k => { C with loc := Function.update C.loc p (k (C.mem q i)) }
  | .decide y s =>
    { C with loc := Function.update C.loc p s,
             out := Function.update C.out p ((C.out p).or (some y)) }

/-- Run a finite schedule from a configuration. -/
def run (C : Config A) (σ : List P) : Config A :=
  σ.foldl (fun C p => A.step p C) C

/-- The initial configuration for the input vector `x`. -/
def initCfg (x : P → In) : Config A where
  loc p := A.init p (x p)
  mem _ := A.v₀
  out _ := none

variable {A}

lemma step_of_write {p : P} {C : Config A} {i : K} {v : V i} {s : A.S}
    (h : A.next p (C.loc p) = .write i v s) :
    A.step p C = { C with loc := Function.update C.loc p s,
                          mem := Function.update C.mem p (Function.update (C.mem p) i v) } := by
  simp [step, h]

lemma step_of_read {p q : P} {C : Config A} {i : K} {k : V i → A.S}
    (h : A.next p (C.loc p) = .read q i k) :
    A.step p C = { C with loc := Function.update C.loc p (k (C.mem q i)) } := by
  simp [step, h]

lemma step_of_decide {p : P} {C : Config A} {y : Out} {s : A.S}
    (h : A.next p (C.loc p) = .decide y s) :
    A.step p C = { C with loc := Function.update C.loc p s,
                          out := Function.update C.out p ((C.out p).or (some y)) } := by
  simp [step, h]

@[simp] lemma run_nil (C : Config A) : A.run C [] = C := rfl

@[simp] lemma run_cons (C : Config A) (p : P) (σ : List P) :
    A.run C (p :: σ) = A.run (A.step p C) σ := rfl

lemma run_append (C : Config A) (σ τ : List P) :
    A.run C (σ ++ τ) = A.run (A.run C σ) τ := by
  simp [run, List.foldl_append]

@[simp] lemma run_concat (C : Config A) (σ : List P) (p : P) :
    A.run C (σ ++ [p]) = A.step p (A.run C σ) := by
  simp [run_append]

/-- Steps of `p` only change `p`'s local state. -/
lemma step_loc_ne (C : Config A) {p q : P} (h : q ≠ p) : (A.step p C).loc q = C.loc q := by
  unfold step; split <;> simp [Function.update_of_ne h]

/-- Steps of `p` only change `p`'s registers. -/
lemma step_mem_ne (C : Config A) {p q : P} (h : q ≠ p) : (A.step p C).mem q = C.mem q := by
  unfold step; split <;> simp [Function.update_of_ne h]

/-- Steps of `p` only change `p`'s output. -/
lemma step_out_ne (C : Config A) {p q : P} (h : q ≠ p) : (A.step p C).out q = C.out q := by
  unfold step; split <;> simp [Function.update_of_ne h]

/-- Outputs are irrevocable (one step). -/
lemma step_out_of_out (C : Config A) (p : P) {q : P} {y : Out} (h : C.out q = some y) :
    (A.step p C).out q = some y := by
  by_cases hq : q = p
  · subst hq; unfold step; split <;> simp [h]
  · rw [step_out_ne C hq, h]

/-- Outputs are irrevocable. -/
lemma out_run_of_out (C : Config A) (σ : List P) {q : P} {y : Out} (h : C.out q = some y) :
    (A.run C σ).out q = some y := by
  induction σ generalizing C with
  | nil => exact h
  | cons p σ ih => exact ih _ (step_out_of_out C p h)

/-- Runs of processes other than `q` do not change `q`'s local state. -/
lemma run_loc_of_notMem (C : Config A) (σ : List P) {q : P} (h : q ∉ σ) :
    (A.run C σ).loc q = C.loc q := by
  induction σ generalizing C with
  | nil => rfl
  | cons p σ ih =>
    simp only [List.mem_cons, not_or] at h
    rw [run_cons, ih _ h.2, step_loc_ne _ h.1]

/-- Runs of processes other than `q` do not change `q`'s registers. -/
lemma run_mem_of_notMem (C : Config A) (σ : List P) {q : P} (h : q ∉ σ) :
    (A.run C σ).mem q = C.mem q := by
  induction σ generalizing C with
  | nil => rfl
  | cons p σ ih =>
    simp only [List.mem_cons, not_or] at h
    rw [run_cons, ih _ h.2, step_mem_ne _ h.1]

/-- Runs of processes other than `q` do not change `q`'s output. -/
lemma run_out_of_notMem (C : Config A) (σ : List P) {q : P} (h : q ∉ σ) :
    (A.run C σ).out q = C.out q := by
  induction σ generalizing C with
  | nil => rfl
  | cons p σ ih =>
    simp only [List.mem_cons, not_or] at h
    rw [run_cons, ih _ h.2, step_out_ne _ h.1]

end Alg

/-! ### Indistinguishability -/

/-- `C` and `D` agree on the local states and outputs of the processes in `S` and on the whole
memory. -/
def AgreeOn {A : Alg P K V In Out} (S : Set P) (C D : Config A) : Prop :=
  (∀ p ∈ S, C.loc p = D.loc p ∧ C.out p = D.out p) ∧ C.mem = D.mem

namespace AgreeOn

variable {A : Alg P K V In Out} [DecidableEq P] [DecidableEq K] {S : Set P} {C D : Config A}

omit [DecidableEq P] [DecidableEq K] in
lemma refl (C : Config A) : AgreeOn S C C := ⟨fun _ _ => ⟨rfl, rfl⟩, rfl⟩

omit [DecidableEq P] [DecidableEq K] in
lemma symm (h : AgreeOn S C D) : AgreeOn S D C :=
  ⟨fun p hp => ⟨(h.1 p hp).1.symm, (h.1 p hp).2.symm⟩, h.2.symm⟩

/-- A step of a process of `S` preserves agreement on `S`. -/
lemma step (h : AgreeOn S C D) {p : P} (hp : p ∈ S) : AgreeOn S (A.step p C) (A.step p D) := by
  obtain ⟨hl, ho⟩ := h.1 p hp
  have hm := h.2
  unfold Alg.step
  rw [hl]
  split
  · refine ⟨fun q hq => ?_, by rw [hm]⟩
    by_cases hqp : q = p
    · subst hqp; simp [ho]
    · simp [Function.update_of_ne hqp, (h.1 q hq).1, (h.1 q hq).2]
  · refine ⟨fun q hq => ?_, hm⟩
    by_cases hqp : q = p
    · subst hqp; simp [ho, hm]
    · simp [Function.update_of_ne hqp, (h.1 q hq).1, (h.1 q hq).2]
  · refine ⟨fun q hq => ?_, hm⟩
    by_cases hqp : q = p
    · subst hqp; simp [ho]
    · simp [Function.update_of_ne hqp, (h.1 q hq).1, (h.1 q hq).2]

/-- Runs of processes of `S` preserve agreement on `S`. -/
lemma run (h : AgreeOn S C D) {σ : List P} (hσ : ∀ p ∈ σ, p ∈ S) :
    AgreeOn S (A.run C σ) (A.run D σ) := by
  induction σ generalizing C D with
  | nil => exact h
  | cons p σ ih =>
    exact ih (h.step (hσ p (by simp))) (fun q hq => hσ q (by simp [hq]))

end AgreeOn

/-! ### Infinite schedules, crashes, solvability -/

/-- `p` takes infinitely many steps in the infinite schedule `σ`. -/
def InfOften (σ : ℕ → P) (p : P) : Prop := ∀ N, ∃ m, N ≤ m ∧ σ m = p

/-- The faulty processes of an infinite schedule: those taking finitely many steps. -/
def Faulty (σ : ℕ → P) : Set P := {p | ¬ InfOften σ p}

/-- The first `T` steps of an infinite schedule. -/
def pre (σ : ℕ → P) (T : ℕ) : List P := (List.range T).map σ

@[simp] lemma pre_zero (σ : ℕ → P) : pre σ 0 = [] := rfl

lemma pre_succ (σ : ℕ → P) (T : ℕ) : pre σ (T + 1) = pre σ T ++ [σ T] := by
  simp [pre, List.range_succ]

@[simp] lemma length_pre (σ : ℕ → P) (T : ℕ) : (pre σ T).length = T := by simp [pre]

/-- A task: which (partial) output vectors are legal for an input vector (`none` = not decided). -/
abbrev Task (P In Out : Type) := (P → In) → (P → Option Out) → Prop

/-- `A` solves the task `T` in the `t`-resilient model: every finite execution satisfies `T`
(safety), and in every infinite execution with at most `t` faulty processes every correct process
eventually decides (termination). -/
def Alg.Solves [DecidableEq P] [DecidableEq K] (A : Alg P K V In Out) (t : ℕ)
    (T : Task P In Out) : Prop :=
  (∀ (x : P → In) (σ : List P), T x (A.run (A.initCfg x) σ).out) ∧
  ∀ (x : P → In) (σ : ℕ → P), (Faulty σ).ncard ≤ t → ∀ p, InfOften σ p →
    ∃ T, ((A.run (A.initCfg x) (pre σ T)).out p).isSome

/-- Solvability is monotone in the resilience: tolerating more crashes is harder. -/
lemma Alg.Solves.mono [DecidableEq P] [DecidableEq K] {A : Alg P K V In Out} {t t' : ℕ}
    {T : Task P In Out} (h : A.Solves t' T) (htt : t ≤ t') : A.Solves t T :=
  ⟨h.1, fun x σ hσ => h.2 x σ (le_trans hσ htt)⟩

/-- Binary consensus (with the weak validity condition: if all inputs are `b`, the only possible
decision is `b`) and agreement. Impossibility results for it imply impossibility for the usual
validity condition ("the decision is the input of some process"). -/
def binConsensus : Task P Bool Bool := fun x y =>
  (∀ b, (∀ p, x p = b) → ∀ p c, y p = some c → c = b) ∧
  ∀ p q c c', y p = some c → y q = some c' → c = c'

/-- Discretized binary `1/k`-agreement: inputs in `{0, 1}`, an output `m : ℕ` stands for the value
`m / k ∈ [0, 1]`; validity (if all inputs are `b`, every decision is `b`, i.e. `0` or `k`), range
(`m ≤ k`) and `1/k`-agreement (any two decisions differ by at most `1`). -/
def epsAgreement (k : ℕ) : Task P Bool ℕ := fun x y =>
  (∀ p m, y p = some m → m ≤ k) ∧
  (∀ b, (∀ p, x p = b) → ∀ p m, y p = some m → m = if b then k else 0) ∧
  ∀ p q m m', y p = some m → y q = some m' → m ≤ m' + 1

/-! ### Round-robin continuation of a finite schedule -/

/-- The infinite schedule that runs `σ` and then the nonempty list `l` cyclically. -/
def thenCycle (σ l : List P) (hl : l ≠ []) (m : ℕ) : P :=
  if h : m < σ.length then σ[m]
  else l[(m - σ.length) % l.length]'(Nat.mod_lt _ (List.length_pos_of_ne_nil hl))

lemma pre_thenCycle (σ l : List P) (hl : l ≠ []) (T : ℕ) :
    ∃ τ, pre (thenCycle σ l hl) (σ.length + T) = σ ++ τ ∧ ∀ q ∈ τ, q ∈ l := by
  induction T with
  | zero =>
    refine ⟨[], ?_, by simp⟩
    simp only [Nat.add_zero, List.append_nil]
    apply List.ext_getElem (by simp)
    intro m h1 h2
    simp only [pre, List.getElem_map, List.getElem_range, thenCycle]
    simp only [length_pre] at h1
    simp [h1]
  | succ T ih =>
    obtain ⟨τ, hτ, hτl⟩ := ih
    refine ⟨τ ++ [thenCycle σ l hl (σ.length + T)], ?_, ?_⟩
    · rw [← Nat.add_assoc, pre_succ, hτ, List.append_assoc]
    · intro q hq
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | rfl
      · exact hτl q hq
      · simp [thenCycle, List.getElem_mem]

lemma infOften_thenCycle (σ l : List P) (hl : l ≠ []) {p : P} (hp : p ∈ l) :
    InfOften (thenCycle σ l hl) p := by
  intro N
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
  refine ⟨σ.length + j + N * l.length, by
    have : N ≤ N * l.length := Nat.le_mul_of_pos_right N (List.length_pos_of_ne_nil hl)
    omega, ?_⟩
  have h1 : ¬ (σ.length + j + N * l.length < σ.length) := by omega
  simp only [thenCycle, h1, dite_false]
  congr 1
  rw [show σ.length + j + N * l.length - σ.length = j + N * l.length by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

lemma faulty_thenCycle_subset (σ l : List P) (hl : l ≠ []) :
    Faulty (thenCycle σ l hl) ⊆ {p | p ∉ l} := fun _ hp hpl => hp (infOften_thenCycle σ l hl hpl)

/-- A process taking infinitely many steps takes at least `B` steps in some finite prefix. -/
lemma InfOften.exists_count_ge [DecidableEq P] {σ : ℕ → P} {p : P} (h : InfOften σ p) (B : ℕ) :
    ∃ T, B ≤ (pre σ T).count p := by
  induction B with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ B ih =>
    obtain ⟨T, hT⟩ := ih
    obtain ⟨m, hm, hmp⟩ := h T
    refine ⟨m + 1, ?_⟩
    rw [pre_succ, List.count_append, hmp]
    have : (pre σ T).count p ≤ (pre σ m).count p := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
      clear hm hmp
      induction d with
      | zero => rfl
      | succ d ihd =>
        rw [← Nat.add_assoc, pre_succ, List.count_append]
        omega
    simp
    omega

/-- Termination from a step bound: if every process has decided once it has taken `B` steps,
then every correct process of every infinite execution decides (in any resilience model). -/
lemma Alg.termination_of_bound [DecidableEq P] [DecidableEq K] (A : Alg P K V In Out) (B : ℕ)
    (hB : ∀ x (σ : List P) p, B ≤ σ.count p → ((A.run (A.initCfg x) σ).out p).isSome)
    (x : P → In) (σ : ℕ → P) (p : P) (hp : InfOften σ p) :
    ∃ T, ((A.run (A.initCfg x) (pre σ T)).out p).isSome := by
  obtain ⟨T, hT⟩ := hp.exists_count_ge B
  exact ⟨T, hB x _ p hT⟩

namespace Alg.Solves

variable [Fintype P] [DecidableEq P] [DecidableEq K] {A : Alg P K V In Out} {t : ℕ}
  {T : Task P In Out}

/-- If at most `t` processes are outside `S`, then after any finite execution, every process
of `S` decides in some extension in which only processes of `S` take steps. -/
theorem exists_decide (hA : A.Solves t T) (S : Finset P) (hS : Sᶜ.card ≤ t)
    (x : P → In) (σ : List P) {u : P} (hu : u ∈ S) :
    ∃ τ : List P, (∀ q ∈ τ, q ∈ S) ∧
      ((A.run (A.initCfg x) (σ ++ τ)).out u).isSome := by
  have hl : S.toList ≠ [] := by
    simpa [← Finset.nonempty_iff_ne_empty] using ⟨u, hu⟩
  set ρ := thenCycle σ S.toList hl
  have hF : (Faulty ρ).ncard ≤ t := by
    refine le_trans (Set.ncard_le_ncard (faulty_thenCycle_subset σ _ hl) (Set.toFinite _)) ?_
    convert hS using 1
    rw [← Set.ncard_coe_finset]
    congr 1
    ext p; simp
  obtain ⟨T, hT⟩ := hA.2 x ρ hF u (infOften_thenCycle σ _ hl (by simpa using hu))
  obtain ⟨τ, hτ, hτS⟩ := pre_thenCycle σ S.toList hl T
  refine ⟨τ, fun q hq => by simpa using hτS q hq, ?_⟩
  rw [← hτ]
  -- outputs are irrevocable, so it suffices to look at a longer prefix
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hT
  have : ∀ T', T ≤ T' → (A.run (A.initCfg x) (pre ρ T')).out u = some y := by
    intro T' hT'
    induction T', hT' using Nat.le_induction with
    | base => exact hy
    | succ T' _ ih => rw [pre_succ, run_concat]; exact Alg.step_out_of_out _ _ ih
  by_cases hTl : T ≤ σ.length + T
  · rw [this _ hTl]; rfl
  · omega

end Alg.Solves

end Cslib.SWMR
