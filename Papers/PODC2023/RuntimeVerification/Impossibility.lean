import Mathlib
import Papers.PODC2023.RuntimeVerification.Similarity

/-!
# The interactive model of Section 3 and the impossibility results (Theorem 5.1, Theorem A.1)

Castañeda, Rodríguez, *Asynchronous Wait-Free Runtime Verification and Enforcement of
Linearizability*, PODC 2023 (arXiv 2301.02638v3).

## The model (Section 3, Figure 2)

`n` asynchronous processes run a *verifier* `V`. Each process repeats forever:
* Lines 03–05: the environment (adversary) chooses the next operation `o` (never chosen before by
  this process); the process updates its local state and the shared memory (`Verifier.pre`);
* Line 06: it invokes `Apply(o)` of the black-box implementation `A` (`Ev.inv`);
* Line 07: it receives the response `y` of `A` (`Ev.res`);
* Lines 08–12: it updates its local state and the shared memory, and possibly reports
  `(ERROR, w)` (`Verifier.post`).

Strengthenings with respect to the paper (they make the impossibility stronger):
* the shared memory is an arbitrary type `M` and each block is one *atomic* transition on it, so
  base objects of any consensus number (indeed an atomic snapshot-and-update of the whole memory)
  are allowed;
* each block may read a perfectly synchronized clock (the global time `t`);
* a verifier block that takes several (wait-free) steps, when run solo, is a function of the
  starting time, local state and memory, so it is subsumed (our executions run blocks solo, as
  the paper's proof does);
* the verifier may report at the end of any iteration.

`A` is an *abstract implementation*: a prefix-closed set `𝒜` of well-formed histories; in an
execution, the history of `A` (`Cfg.hist`) stays in `𝒜` at all times (`IsExec.legal`).

The verifier `V` does not depend on `A` (the quantifier order is `∃ V, ∀ A`): `A` is a black box
and "the only way `V_O` can obtain information of `A` is by invoking high-level operations of
it". The paper also says that this is "modeled as conceptually `V_O` taking `A` as its input";
read literally (`V` may depend on `A`), Definition 6.1 becomes trivially solvable
(`trivialVerifier_predictive`), so Theorem A.1 needs the black-box (uniform) reading.

## Results

* `thm_5_1` — Theorem 5.1 (generic form): for every sequential object admitting operations
  `a, b, c₁, c₂, …` with `⟨a:ra⟩⟨b:rb⟩⟨c₁:rc⟩⟨c₂:rc⟩…` legal but `⟨b:rb⟩` illegal, no verifier
  (with `n ≥ 2`) runtime verifies linearizability; even the weak version of completeness (some
  process reports something) fails. Instances for queues, stacks, sets, priority queues,
  counters and consensus are in `Objects.lean`.
* `thm_A_1` — Theorem A.1: the same objects are not predictively verifiable either (uniform
  verifiers).
* `trivialVerifier_predictive` — under the non-uniform reading, a trivial verifier solves
  predictive verification for every correctness condition.
-/

namespace Podc2023.RuntimeVerification.Impossibility

open Cslib.SharedMemory.HerlihyWing
open Podc2023.RuntimeVerification

/-- A verifier (Figure 2) for `n` processes, operations `Op`, responses `Y` of the verified
implementation and witnesses `W` reported together with `ERROR`. -/
structure Verifier (n : ℕ) (Op Y W : Type) where
  /-- Local states. -/
  L : Type
  /-- Shared memory (arbitrary base objects). -/
  M : Type
  /-- Initial memory. -/
  m0 : M
  /-- Initial local states. -/
  l0 : Fin n → L
  /-- Lines 03–05 at time `t`, by process `p`, with the chosen operation `o`. -/
  pre : ℕ → Fin n → L → Op → M → L × M
  /-- Lines 08–12 at time `t`, by process `p`, with the response `y`; the last component is the
  report `(ERROR, w)`, if any. -/
  post : ℕ → Fin n → L → Y → M → L × M × Option W

/-- Program counter of a process. -/
inductive Phase (Op Y : Type)
  | idle
  | ready (o : Op)
  | waiting (o : Op)
  | got (o : Op) (y : Y)

/-- Scheduling events. -/
inductive Ev (n : ℕ) (Op Y : Type)
  /-- Lines 03–05 with the operation `o` chosen by the environment. -/
  | pre (p : Fin n) (o : Op)
  /-- Line 06: invocation of `A`. -/
  | inv (p : Fin n)
  /-- Line 07: response `y` of `A`. -/
  | res (p : Fin n) (y : Y)
  /-- Lines 08–12. -/
  | post (p : Fin n)

variable {n : ℕ} {Op Y W : Type}

/-- Configurations: memory, local states, program counters and the history of `A` so far. -/
structure Cfg (V : Verifier n Op Y W) where
  mem : V.M
  loc : Fin n → V.L
  ph : Fin n → Phase Op Y
  hist : Hist (Fin n) Op Y

namespace Verifier

variable (V : Verifier n Op Y W)

/-- The initial configuration. -/
def init : Cfg V := ⟨V.m0, V.l0, fun _ => .idle, []⟩

/-- One step at time `t`: the new configuration and the report (if any). -/
def step (t : ℕ) (c : Cfg V) : Ev n Op Y → Option (Cfg V × Option W)
  | .pre p o =>
    match c.ph p with
    | .idle =>
      some (⟨(V.pre t p (c.loc p) o c.mem).2, Function.update c.loc p (V.pre t p (c.loc p) o c.mem).1,
        Function.update c.ph p (.ready o), c.hist⟩, none)
    | _ => none
  | .inv p =>
    match c.ph p with
    | .ready o => some (⟨c.mem, c.loc, Function.update c.ph p (.waiting o), c.hist ++ [.inv p () o]⟩, none)
    | _ => none
  | .res p y =>
    match c.ph p with
    | .waiting o => some (⟨c.mem, c.loc, Function.update c.ph p (.got o y), c.hist ++ [.res p () y]⟩, none)
    | _ => none
  | .post p =>
    match c.ph p with
    | .got _ y =>
      some (⟨(V.post t p (c.loc p) y c.mem).2.1, Function.update c.loc p (V.post t p (c.loc p) y c.mem).1,
        Function.update c.ph p .idle, c.hist⟩, (V.post t p (c.loc p) y c.mem).2.2)
    | _ => none

end Verifier

/-- `A` is an abstract implementation: a prefix-closed set of well-formed histories. -/
def IsAbstractImpl (𝒜 : Set (Hist (Fin n) Op Y)) : Prop :=
  (∀ h ∈ 𝒜, WellFormed h) ∧ ∀ h ∈ 𝒜, ∀ h', h' <+: h → h' ∈ 𝒜

/-- An infinite execution of `V` with input `𝒜`: schedule `s`, configurations `c`, reports
`out`. Every process starts infinitely many iterations, never chooses the same operation twice,
and the history of `A` is always a history of `𝒜`. -/
structure IsExec (V : Verifier n Op Y W) (𝒜 : Set (Hist (Fin n) Op Y)) (s : ℕ → Ev n Op Y)
    (c : ℕ → Cfg V) (out : ℕ → Option W) : Prop where
  init : c 0 = V.init
  step : ∀ t, V.step t (c t) (s t) = some (c (t + 1), out t)
  legal : ∀ t, (c t).hist ∈ 𝒜
  distinct : ∀ p o t t', t < t' → s t = .pre p o → s t' = .pre p o → False
  fair : ∀ p t, ∃ t', t ≤ t' ∧ s t' = .post p

/-- **Definition 3.1** (distributed runtime verification of the correctness condition `Pr`):
soundness and completeness (with a witness: a history of `A` violating `Pr`) in every execution,
for every input implementation. -/
def RuntimeVerifies (V : Verifier n Op Y (Hist (Fin n) Op Y)) (Pr : Set (Hist (Fin n) Op Y)) :
    Prop :=
  ∀ 𝒜, IsAbstractImpl 𝒜 → ∀ s c out, IsExec V 𝒜 s c out →
    ((∀ t, (c t).hist ∈ Pr) → ∀ t, out t = none) ∧
    ((∃ t, (c t).hist ∉ Pr) → ∃ t w, out t = some w ∧ w ∈ 𝒜 ∧ w ∉ Pr)

/-- A weaker requirement: soundness and completeness without witnesses (any report counts). -/
def WeaklyVerifies (V : Verifier n Op Y W) (Pr : Set (Hist (Fin n) Op Y)) : Prop :=
  ∀ 𝒜, IsAbstractImpl 𝒜 → ∀ s c out, IsExec V 𝒜 s c out →
    ((∀ t, (c t).hist ∈ Pr) → ∀ t, out t = none) ∧ ((∃ t, (c t).hist ∉ Pr) → ∃ t, out t ≠ none)

theorem RuntimeVerifies.weaklyVerifies {V : Verifier n Op Y (Hist (Fin n) Op Y)}
    {Pr : Set (Hist (Fin n) Op Y)} (h : RuntimeVerifies V Pr) : WeaklyVerifies V Pr := by
  intro 𝒜 h𝒜 s c out hE
  refine ⟨(h 𝒜 h𝒜 s c out hE).1, fun hc => ?_⟩
  obtain ⟨t, w, hw, -⟩ := (h 𝒜 h𝒜 s c out hE).2 hc
  exact ⟨t, by simp [hw]⟩

/-- **Definition 6.1** (distributed runtime predictive verification), for all input
implementations: predictive soundness (if `A`'s history always satisfies `Pr`, then either nobody
reports, or some process reports with a witness for `A`) and completeness. -/
def PredictivelyVerifies (V : Verifier n Op Y (Hist (Fin n) Op Y))
    (Pr : Set (Hist (Fin n) Op Y)) : Prop :=
  ∀ 𝒜, IsAbstractImpl 𝒜 → ∀ s c out, IsExec V 𝒜 s c out →
    ((∀ t, (c t).hist ∈ Pr) →
      (∀ t, out t = none) ∨ ∃ t w, out t = some w ∧ w ∈ 𝒜 ∧ w ∉ Pr) ∧
    ((∃ t, (c t).hist ∉ Pr) → ∃ t w, out t = some w ∧ w ∈ 𝒜 ∧ w ∉ Pr)

theorem RuntimeVerifies.predictivelyVerifies {V : Verifier n Op Y (Hist (Fin n) Op Y)}
    {Pr : Set (Hist (Fin n) Op Y)} (h : RuntimeVerifies V Pr) : PredictivelyVerifies V Pr :=
  fun 𝒜 h𝒜 s c out hE => ⟨fun hs => Or.inl ((h 𝒜 h𝒜 s c out hE).1 hs), (h 𝒜 h𝒜 s c out hE).2⟩

/-! ## The executions `E` and `F` of the proof of Theorem 5.1 -/

/-- The data of the indistinguishability argument: `p₀` (the paper's `p₁`) invokes `a` and gets
`ra`; `p₁` (the paper's `p₂`) invokes `b` and gets `rb`; afterwards, for `k = 1, 2, …`, process
`k mod n` invokes `c k` and gets `rc`. For the queue: `a = Enqueue(1)`, `ra = true`,
`b = Dequeue()`, `rb = 1`, `c k = Dequeue()`, `rc = empty`. -/
structure ImpData (Op Y : Type) where
  a : Op
  b : Op
  c : ℕ → Op
  ra : Y
  rb : Y
  rc : Y

variable (hn : 2 ≤ n)

/-- The paper's `p₁`. -/
def p₀ : Fin n := ⟨0, by omega⟩
/-- The paper's `p₂`. -/
def p₁ : Fin n := ⟨1, by omega⟩
/-- The process of the `k`-th round-robin iteration. -/
def q (k : ℕ) : Fin n := ⟨k % n, Nat.mod_lt _ (by omega)⟩

variable (D : ImpData Op Y)

/-- The schedules: `sched false` is `E` (`p₂`'s operation first), `sched true` is `F` (`p₁`'s
operation first). -/
def sched (swap : Bool) : ℕ → Ev n Op Y
  | 0 => .pre (p₁ hn) D.b
  | 1 => .pre (p₀ hn) D.a
  | 2 => if swap then .inv (p₀ hn) else .inv (p₁ hn)
  | 3 => if swap then .res (p₀ hn) D.ra else .res (p₁ hn) D.rb
  | 4 => if swap then .inv (p₁ hn) else .inv (p₀ hn)
  | 5 => if swap then .res (p₁ hn) D.rb else .res (p₀ hn) D.ra
  | 6 => .post (p₁ hn)
  | 7 => .post (p₀ hn)
  | t + 8 =>
    match t % 4 with
    | 0 => .pre (q hn (t / 4 + 1)) (D.c (t / 4 + 1))
    | 1 => .inv (q hn (t / 4 + 1))
    | 2 => .res (q hn (t / 4 + 1)) D.rc
    | _ => .post (q hn (t / 4 + 1))

/-- Run a schedule (stuttering if a step is not enabled; this never happens for `sched`). -/
def runCfg (V : Verifier n Op Y W) (s : ℕ → Ev n Op Y) : ℕ → Cfg V
  | 0 => V.init
  | t + 1 =>
    match V.step t (runCfg V s t) (s t) with
    | some r => r.1
    | none => runCfg V s t

/-- Reports of a run. -/
def runOut (V : Verifier n Op Y W) (s : ℕ → Ev n Op Y) (t : ℕ) : Option W :=
  match V.step t (runCfg V s t) (s t) with
  | some r => r.2
  | none => none

theorem runCfg_succ_of_step {V : Verifier n Op Y W} {s : ℕ → Ev n Op Y} {t : ℕ}
    {c' : Cfg V} {w : Option W} (h : V.step t (runCfg V s t) (s t) = some (c', w)) :
    runCfg V s (t + 1) = c' ∧ runOut V s t = w := by
  simp [runCfg, runOut, h]

/-- The first four events of `A` in `E` / `F`. -/
def H0 (swap : Bool) : Hist (Fin n) Op Y :=
  if swap then [.inv (p₀ hn) () D.a, .res (p₀ hn) () D.ra, .inv (p₁ hn) () D.b, .res (p₁ hn) () D.rb]
  else [.inv (p₁ hn) () D.b, .res (p₁ hn) () D.rb, .inv (p₀ hn) () D.a, .res (p₀ hn) () D.ra]

/-- The events of `A` in the first `i` round-robin iterations. -/
def tailH (i : ℕ) : Hist (Fin n) Op Y :=
  (List.range i).flatMap fun j => [.inv (q hn (j + 1)) () (D.c (j + 1)), .res (q hn (j + 1)) () D.rc]

/-- History of `A` after `8 + 4 i` steps. -/
def histAt (swap : Bool) (i : ℕ) : Hist (Fin n) Op Y := H0 hn D swap ++ tailH hn D i

/-! ## Runs -/

section Run

variable {V : Verifier n Op Y W}

/-- Agreement of configurations on everything except the history of `A` (which the processes
cannot observe). -/
def Agree (c d : Cfg V) : Prop := c.mem = d.mem ∧ c.loc = d.loc ∧ c.ph = d.ph

theorem step_agree {c d : Cfg V} (h : Agree c d) (t : ℕ) (e : Ev n Op Y) :
    Option.map (fun r => (r.1.mem, r.1.loc, r.1.ph, r.2)) (V.step t c e) =
      Option.map (fun r => (r.1.mem, r.1.loc, r.1.ph, r.2)) (V.step t d e) := by
  obtain ⟨hm, hl, hp⟩ := h
  cases e <;> simp only [Verifier.step, hm, hl, hp] <;> split <;> simp

theorem runCfg_agree_succ {s s' : ℕ → Ev n Op Y} {t : ℕ}
    (h : Agree (runCfg V s t) (runCfg V s' t)) (hs : s t = s' t) :
    Agree (runCfg V s (t + 1)) (runCfg V s' (t + 1)) ∧ runOut V s t = runOut V s' t := by
  have key := step_agree h t (s t)
  rw [hs] at key
  simp only [runCfg, runOut]
  rcases h1 : V.step t (runCfg V s t) (s' t) with _ | ⟨c1, w1⟩ <;>
    rcases h2 : V.step t (runCfg V s' t) (s' t) with _ | ⟨c2, w2⟩ <;>
    rw [h1, h2] at key <;> simp at key ⊢
  · rw [hs]; simp only [h1]; exact ⟨h, trivial⟩
  · rw [hs]; simp only [h1]
    obtain ⟨e1, e2, e3, e4⟩ := key
    exact ⟨⟨e1, e2, e3⟩, e4⟩

theorem step_pre {c : Cfg V} {t : ℕ} {p : Fin n} {o : Op} (h : c.ph p = .idle) :
    V.step t c (.pre p o) = some (⟨(V.pre t p (c.loc p) o c.mem).2,
      Function.update c.loc p (V.pre t p (c.loc p) o c.mem).1,
      Function.update c.ph p (.ready o), c.hist⟩, none) := by
  simp [Verifier.step, h]

theorem step_inv {c : Cfg V} {t : ℕ} {p : Fin n} {o : Op} (h : c.ph p = .ready o) :
    V.step t c (.inv p) =
      some (⟨c.mem, c.loc, Function.update c.ph p (.waiting o), c.hist ++ [.inv p () o]⟩, none) := by
  simp [Verifier.step, h]

theorem step_res {c : Cfg V} {t : ℕ} {p : Fin n} {o : Op} {y : Y} (h : c.ph p = .waiting o) :
    V.step t c (.res p y) =
      some (⟨c.mem, c.loc, Function.update c.ph p (.got o y), c.hist ++ [.res p () y]⟩, none) := by
  simp [Verifier.step, h]

theorem step_post {c : Cfg V} {t : ℕ} {p : Fin n} {o : Op} {y : Y} (h : c.ph p = .got o y) :
    V.step t c (.post p) = some (⟨(V.post t p (c.loc p) y c.mem).2.1,
      Function.update c.loc p (V.post t p (c.loc p) y c.mem).1, Function.update c.ph p .idle,
      c.hist⟩, (V.post t p (c.loc p) y c.mem).2.2) := by
  simp [Verifier.step, h]

theorem step_hist {c c' : Cfg V} {t : ℕ} {e : Ev n Op Y} {w : Option W}
    (h : V.step t c e = some (c', w)) : c.hist <+: c'.hist := by
  cases e <;> simp only [Verifier.step] at h <;> split at h <;> simp at h <;>
    obtain ⟨rfl, -⟩ := h <;> simp

theorem hist_prefix_succ (s : ℕ → Ev n Op Y) (t : ℕ) :
    (runCfg V s t).hist <+: (runCfg V s (t + 1)).hist := by
  simp only [runCfg]
  rcases h : V.step t (runCfg V s t) (s t) with _ | ⟨c', w⟩
  · exact List.prefix_refl _
  · exact step_hist h

theorem hist_prefix (s : ℕ → Ev n Op Y) {t t' : ℕ} (h : t ≤ t') :
    (runCfg V s t).hist <+: (runCfg V s t').hist := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (hist_prefix_succ s _)

end Run


/-! ## The runs of `E` and `F` -/

section Sched

variable {V : Verifier n Op Y W}

theorem p₀_ne_p₁ : p₀ hn ≠ p₁ hn := by simp [p₀, p₁, Fin.ext_iff]

/-- Program counters after the first two steps. -/
def ph2 : Fin n → Phase Op Y :=
  Function.update (Function.update (fun _ => .idle) (p₁ hn) (.ready D.b)) (p₀ hn) (.ready D.a)

/-- Program counters after six steps. -/
def ph6 : Fin n → Phase Op Y :=
  Function.update (Function.update (fun _ => .idle) (p₁ hn) (.got D.b D.rb)) (p₀ hn) (.got D.a D.ra)

theorem run_two (swap : Bool) :
    (runCfg V (sched hn D swap) 2).ph = ph2 hn D ∧ (runCfg V (sched hn D swap) 2).hist = [] ∧
      runOut V (sched hn D swap) 0 = none ∧ runOut V (sched hn D swap) 1 = none ∧
      ∀ t < 2, ∃ r, V.step t (runCfg V (sched hn D swap) t) (sched hn D swap t) = some r := by
  have h0 := step_pre (V := V) (t := 0) (o := D.b) (c := runCfg V (sched hn D swap) 0)
    (p := p₁ hn) (by simp [runCfg, Verifier.init])
  obtain ⟨e1, o0⟩ := runCfg_succ_of_step (s := sched hn D swap) h0
  have h1 := step_pre (V := V) (t := 1) (o := D.a) (c := runCfg V (sched hn D swap) 1)
    (p := p₀ hn) (by rw [e1]; simp [runCfg, Verifier.init, Function.update_of_ne (p₀_ne_p₁ hn)])
  obtain ⟨e2, o1⟩ := runCfg_succ_of_step (s := sched hn D swap) h1
  refine ⟨?_, ?_, o0, o1, fun t ht => ?_⟩
  · rw [e2, e1]; simp [ph2, runCfg, Verifier.init]
  · rw [e2, e1]; simp [runCfg, Verifier.init]
  · obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    exacts [⟨_, h0⟩, ⟨_, h1⟩]

theorem agree_two : Agree (runCfg V (sched hn D false) 2) (runCfg V (sched hn D true) 2) := by
  have a0 : Agree (runCfg V (sched hn D false) 0) (runCfg V (sched hn D true) 0) :=
    ⟨rfl, rfl, rfl⟩
  have a1 := (runCfg_agree_succ a0 rfl).1
  exact (runCfg_agree_succ a1 rfl).1

theorem run_six (swap : Bool) :
    (runCfg V (sched hn D swap) 6).mem = (runCfg V (sched hn D swap) 2).mem ∧
    (runCfg V (sched hn D swap) 6).loc = (runCfg V (sched hn D swap) 2).loc ∧
    (runCfg V (sched hn D swap) 6).ph = ph6 hn D ∧
    (runCfg V (sched hn D swap) 6).hist = H0 hn D swap ∧
    (∀ t, 2 ≤ t → t < 6 → runOut V (sched hn D swap) t = none) ∧
    ∀ t, 2 ≤ t → t < 6 → ∃ r, V.step t (runCfg V (sched hn D swap) t) (sched hn D swap t) = some r := by
  obtain ⟨hph, hh, -, -, -⟩ := run_two (V := V) hn D swap
  have hne := p₀_ne_p₁ hn
  set c2 := runCfg V (sched hn D swap) 2 with hc2
  cases swap with
  | false =>
    have s2 := step_inv (V := V) (t := 2) (c := c2) (p := p₁ hn) (o := D.b)
      (by rw [hph]; simp [ph2, Function.update_of_ne hne.symm])
    obtain ⟨e3, o2⟩ := runCfg_succ_of_step (s := sched hn D false) s2
    have s3 := step_res (V := V) (t := 3) (y := D.rb) (c := runCfg V (sched hn D false) 3)
      (p := p₁ hn) (o := D.b) (by rw [e3]; simp)
    obtain ⟨e4, o3⟩ := runCfg_succ_of_step (s := sched hn D false) s3
    have s4 := step_inv (V := V) (t := 4) (c := runCfg V (sched hn D false) 4) (p := p₀ hn)
      (o := D.a) (by rw [e4, e3]; simp [hph, ph2, Function.update_of_ne hne])
    obtain ⟨e5, o4⟩ := runCfg_succ_of_step (s := sched hn D false) s4
    have s5 := step_res (V := V) (t := 5) (y := D.ra) (c := runCfg V (sched hn D false) 5)
      (p := p₀ hn) (o := D.a) (by rw [e5]; simp)
    obtain ⟨e6, o5⟩ := runCfg_succ_of_step (s := sched hn D false) s5
    refine ⟨by rw [e6, e5, e4, e3], by rw [e6, e5, e4, e3], ?_, ?_, ?_, ?_⟩
    · rw [e6, e5, e4, e3, hph]
      funext r
      simp only [ph2, ph6, Function.update]
      split_ifs <;> subst_vars <;> simp_all
    · rw [e6, e5, e4, e3, hh]; simp [H0]
    · intro t h1 h2
      obtain rfl | rfl | rfl | rfl : t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
      exacts [o2, o3, o4, o5]
    · intro t h1 h2
      obtain rfl | rfl | rfl | rfl : t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
      exacts [⟨_, s2⟩, ⟨_, s3⟩, ⟨_, s4⟩, ⟨_, s5⟩]
  | true =>
    have s2 := step_inv (V := V) (t := 2) (c := c2) (p := p₀ hn) (o := D.a)
      (by rw [hph]; simp [ph2])
    obtain ⟨e3, o2⟩ := runCfg_succ_of_step (s := sched hn D true) s2
    have s3 := step_res (V := V) (t := 3) (y := D.ra) (c := runCfg V (sched hn D true) 3)
      (p := p₀ hn) (o := D.a) (by rw [e3]; simp)
    obtain ⟨e4, o3⟩ := runCfg_succ_of_step (s := sched hn D true) s3
    have s4 := step_inv (V := V) (t := 4) (c := runCfg V (sched hn D true) 4) (p := p₁ hn)
      (o := D.b) (by rw [e4, e3]; simp [hph, ph2, Function.update_of_ne hne.symm])
    obtain ⟨e5, o4⟩ := runCfg_succ_of_step (s := sched hn D true) s4
    have s5 := step_res (V := V) (t := 5) (y := D.rb) (c := runCfg V (sched hn D true) 5)
      (p := p₁ hn) (o := D.b) (by rw [e5]; simp)
    obtain ⟨e6, o5⟩ := runCfg_succ_of_step (s := sched hn D true) s5
    refine ⟨by rw [e6, e5, e4, e3], by rw [e6, e5, e4, e3], ?_, ?_, ?_, ?_⟩
    · rw [e6, e5, e4, e3, hph]
      funext r
      simp only [ph2, ph6, Function.update]
      split_ifs <;> subst_vars <;> simp_all
    · rw [e6, e5, e4, e3, hh]; simp [H0]
    · intro t h1 h2
      obtain rfl | rfl | rfl | rfl : t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
      exacts [o2, o3, o4, o5]
    · intro t h1 h2
      obtain rfl | rfl | rfl | rfl : t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
      exacts [⟨_, s2⟩, ⟨_, s3⟩, ⟨_, s4⟩, ⟨_, s5⟩]


theorem run_eight (swap : Bool) :
    (runCfg V (sched hn D swap) 8).ph = (fun _ => .idle) ∧
    (runCfg V (sched hn D swap) 8).hist = H0 hn D swap ∧
    (∃ r, V.step 6 (runCfg V (sched hn D swap) 6) (sched hn D swap 6) = some r) ∧
    (∃ r, V.step 7 (runCfg V (sched hn D swap) 7) (sched hn D swap 7) = some r) := by
  obtain ⟨-, -, hph, hh, -, -⟩ := run_six (V := V) hn D swap
  have hne := p₀_ne_p₁ hn
  have s6 := step_post (V := V) (t := 6) (c := runCfg V (sched hn D swap) 6) (p := p₁ hn)
    (o := D.b) (y := D.rb) (by rw [hph]; simp [ph6, Function.update_of_ne hne.symm])
  obtain ⟨e7, -⟩ := runCfg_succ_of_step (s := sched hn D swap) s6
  have s7 := step_post (V := V) (t := 7) (c := runCfg V (sched hn D swap) 7) (p := p₀ hn)
    (o := D.a) (y := D.ra) (by rw [e7]; simp [hph, ph6, Function.update_of_ne hne])
  obtain ⟨e8, -⟩ := runCfg_succ_of_step (s := sched hn D swap) s7
  refine ⟨?_, by rw [e8, e7, hh], ⟨_, s6⟩, ⟨_, s7⟩⟩
  rw [e8, e7, hph]
  funext r
  simp only [ph6, Function.update]
  split_ifs <;> subst_vars <;> simp_all

theorem sched_pre (swap : Bool) (i : ℕ) :
    sched hn D swap (4 * i + 8) = .pre (q hn (i + 1)) (D.c (i + 1)) := by
  simp [sched, Nat.mul_mod_right]

theorem sched_inv (swap : Bool) (i : ℕ) :
    sched hn D swap (4 * i + 1 + 8) = .inv (q hn (i + 1)) := by
  have h1 : (4 * i + 1) % 4 = 1 := by omega
  have h2 : (4 * i + 1) / 4 = i := by omega
  simp [sched, h1, h2]

theorem sched_res (swap : Bool) (i : ℕ) :
    sched hn D swap (4 * i + 2 + 8) = .res (q hn (i + 1)) D.rc := by
  have h1 : (4 * i + 2) % 4 = 2 := by omega
  have h2 : (4 * i + 2) / 4 = i := by omega
  simp [sched, h1, h2]

theorem sched_post (swap : Bool) (i : ℕ) :
    sched hn D swap (4 * i + 3 + 8) = .post (q hn (i + 1)) := by
  have h1 : (4 * i + 3) % 4 = 3 := by omega
  have h2 : (4 * i + 3) / 4 = i := by omega
  simp [sched, h1, h2]

theorem histAt_succ (swap : Bool) (i : ℕ) :
    histAt hn D swap (i + 1) =
      histAt hn D swap i ++ [.inv (q hn (i + 1)) () (D.c (i + 1)), .res (q hn (i + 1)) () D.rc] := by
  simp [histAt, tailH, List.range_succ, List.flatMap_append]

/-- One round-robin iteration. -/
theorem period_step (swap : Bool) (i : ℕ)
    (hph : (runCfg V (sched hn D swap) (4 * i + 8)).ph = fun _ => .idle) :
    (runCfg V (sched hn D swap) (4 * (i + 1) + 8)).ph = (fun _ => .idle) ∧
    (runCfg V (sched hn D swap) (4 * (i + 1) + 8)).hist =
      (runCfg V (sched hn D swap) (4 * i + 8)).hist ++
        [.inv (q hn (i + 1)) () (D.c (i + 1)), .res (q hn (i + 1)) () D.rc] ∧
    (∀ j < 4, ∃ r, V.step (4 * i + j + 8) (runCfg V (sched hn D swap) (4 * i + j + 8))
      (sched hn D swap (4 * i + j + 8)) = some r) ∧
    (∀ j < 3, runOut V (sched hn D swap) (4 * i + j + 8) = none) := by
  set s := sched hn D swap
  set p := q hn (i + 1)
  have s0 := step_pre (V := V) (t := 4 * i + 8) (c := runCfg V s (4 * i + 8)) (p := p)
    (o := D.c (i + 1)) (by rw [hph])
  rw [← sched_pre hn D swap i] at s0
  obtain ⟨e1, o0⟩ := runCfg_succ_of_step s0
  have s1 := step_inv (V := V) (t := 4 * i + 1 + 8) (c := runCfg V s (4 * i + 1 + 8)) (p := p)
    (o := D.c (i + 1)) (by rw [show 4 * i + 1 + 8 = 4 * i + 8 + 1 by omega, e1]; simp)
  rw [← sched_inv hn D swap i] at s1
  obtain ⟨e2, o1⟩ := runCfg_succ_of_step s1
  have s2 := step_res (V := V) (t := 4 * i + 2 + 8) (c := runCfg V s (4 * i + 2 + 8)) (p := p)
    (o := D.c (i + 1)) (y := D.rc)
    (by rw [show 4 * i + 2 + 8 = 4 * i + 1 + 8 + 1 by omega, e2]; simp)
  rw [← sched_res hn D swap i] at s2
  obtain ⟨e3, o2⟩ := runCfg_succ_of_step s2
  have s3 := step_post (V := V) (t := 4 * i + 3 + 8) (c := runCfg V s (4 * i + 3 + 8)) (p := p)
    (o := D.c (i + 1)) (y := D.rc)
    (by rw [show 4 * i + 3 + 8 = 4 * i + 2 + 8 + 1 by omega, e3]; simp)
  rw [← sched_post hn D swap i] at s3
  obtain ⟨e4, -⟩ := runCfg_succ_of_step s3
  have E1 : runCfg V s (4 * i + 1 + 8) = _ := (show 4 * i + 1 + 8 = 4 * i + 8 + 1 by omega) ▸ e1
  have E2 : runCfg V s (4 * i + 2 + 8) = _ := (show 4 * i + 2 + 8 = 4 * i + 1 + 8 + 1 by omega) ▸ e2
  have E3 : runCfg V s (4 * i + 3 + 8) = _ := (show 4 * i + 3 + 8 = 4 * i + 2 + 8 + 1 by omega) ▸ e3
  have E4 : runCfg V s (4 * (i + 1) + 8) = _ := (show 4 * i + 3 + 8 + 1 = 4 * (i + 1) + 8 by omega) ▸ e4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [E4, E3, E2, E1, hph]; funext r; by_cases hr : r = p <;> simp [hr]
  · rw [E4, E3, E2, E1]; simp
  · intro j hj
    obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    exacts [⟨_, s0⟩, ⟨_, s1⟩, ⟨_, s2⟩, ⟨_, s3⟩]
  · intro j hj
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    exacts [o0, o1, o2]

/-- The periodic part of the runs. -/
theorem run_period (swap : Bool) (i : ℕ) :
    (runCfg V (sched hn D swap) (4 * i + 8)).ph = (fun _ => .idle) ∧
    (runCfg V (sched hn D swap) (4 * i + 8)).hist = histAt hn D swap i := by
  induction i with
  | zero =>
    obtain ⟨hph, hh, -, -⟩ := run_eight (V := V) hn D swap
    exact ⟨by simpa using hph, by simpa [histAt, tailH] using hh⟩
  | succ i ih =>
    obtain ⟨h1, h2, -, -⟩ := period_step (V := V) hn D swap i ih.1
    exact ⟨h1, by rw [h2, ih.2, histAt_succ]⟩

/-- All steps of the runs of `E` and `F` are enabled. -/
theorem step_some (swap : Bool) (t : ℕ) :
    ∃ r, V.step t (runCfg V (sched hn D swap) t) (sched hn D swap t) = some r := by
  rcases Nat.lt_or_ge t 8 with ht | ht
  · obtain ⟨-, -, -, -, h01⟩ := run_two (V := V) hn D swap
    obtain ⟨-, -, -, -, -, h25⟩ := run_six (V := V) hn D swap
    obtain ⟨-, -, h6, h7⟩ := run_eight (V := V) hn D swap
    rcases Nat.lt_or_ge t 2 with h | h
    · exact h01 t h
    rcases Nat.lt_or_ge t 6 with h' | h'
    · exact h25 t h h'
    obtain rfl | rfl : t = 6 ∨ t = 7 := by omega
    exacts [h6, h7]
  · obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < 4 ∧ t = 4 * i + j + 8 := ⟨(t - 8) / 4, (t - 8) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
    exact (period_step (V := V) hn D swap i (run_period (V := V) hn D swap i).1).2.2.1 j hj


/-- `E` and `F` are indistinguishable: from time `6` on, all memories, local states and program
counters coincide. -/
theorem agree_ge_six (t : ℕ) (ht : 6 ≤ t) :
    Agree (runCfg V (sched hn D false) t) (runCfg V (sched hn D true) t) ∧
      runOut V (sched hn D false) t = runOut V (sched hn D true) t := by
  induction t, ht using Nat.le_induction with
  | base =>
    obtain ⟨m1, l1, p1, -, -, -⟩ := run_six (V := V) hn D false
    obtain ⟨m2, l2, p2, -, -, -⟩ := run_six (V := V) hn D true
    obtain ⟨am, al, -⟩ := agree_two (V := V) hn D
    have hag : Agree (runCfg V (sched hn D false) 6) (runCfg V (sched hn D true) 6) :=
      ⟨by rw [m1, m2, am], by rw [l1, l2, al], by rw [p1, p2]⟩
    exact ⟨hag, (runCfg_agree_succ hag rfl).2⟩
  | succ t ht ih =>
    have hs : ∀ u, 6 ≤ u → sched hn D false u = sched hn D true u := by
      intro u hu
      obtain rfl | rfl | ⟨v, rfl⟩ : u = 6 ∨ u = 7 ∨ ∃ v, u = v + 8 :=
        by rcases Nat.lt_or_ge u 8 with h | h
           · omega
           · exact Or.inr (Or.inr ⟨u - 8, by omega⟩)
      all_goals rfl
    have h1 := (runCfg_agree_succ ih.1 (hs t ht)).1
    exact ⟨h1, (runCfg_agree_succ h1 (hs (t + 1) (by omega))).2⟩

/-- The reports of `E` and `F` coincide. -/
theorem runOut_eq (t : ℕ) : runOut V (sched hn D false) t = runOut V (sched hn D true) t := by
  rcases Nat.lt_or_ge t 6 with h | h
  · obtain ⟨-, -, o0f, o1f, -⟩ := run_two (V := V) hn D false
    obtain ⟨-, -, o0t, o1t, -⟩ := run_two (V := V) hn D true
    obtain ⟨-, -, -, -, of, -⟩ := run_six (V := V) hn D false
    obtain ⟨-, -, -, -, ot, -⟩ := run_six (V := V) hn D true
    rcases Nat.lt_or_ge t 2 with h' | h'
    · obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
      · rw [o0f, o0t]
      · rw [o1f, o1t]
    · rw [of t h' h, ot t h' h]
  · exact (agree_ge_six (V := V) hn D t h).2

theorem hist_mem (swap : Bool) (t : ℕ) :
    (runCfg V (sched hn D swap) t).hist <+: histAt hn D swap t := by
  have := hist_prefix (V := V) (sched hn D swap) (show t ≤ 4 * t + 8 by omega)
  rwa [(run_period (V := V) hn D swap t).2] at this

theorem sched_eq_pre {swap : Bool} {t : ℕ} {p : Fin n} {o : Op}
    (h : sched hn D swap t = .pre p o) :
    (t = 0 ∧ p = p₁ hn ∧ o = D.b) ∨ (t = 1 ∧ p = p₀ hn ∧ o = D.a) ∨
      ∃ i, t = 4 * i + 8 ∧ p = q hn (i + 1) ∧ o = D.c (i + 1) := by
  rcases Nat.lt_or_ge t 8 with ht | ht
  · interval_cases t <;> cases swap <;> simp_all [sched]
  · obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < 4 ∧ t = 4 * i + j + 8 :=
      ⟨(t - 8) / 4, (t - 8) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
    obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    · rw [show 4 * i + 0 + 8 = 4 * i + 8 by omega, sched_pre] at h
      simp only [Ev.pre.injEq] at h
      exact Or.inr (Or.inr ⟨i, by omega, h.1.symm, h.2.symm⟩)
    · rw [sched_inv] at h; cases h
    · rw [sched_res] at h; cases h
    · rw [sched_post] at h; cases h

/-- The runs of `E` and `F` are executions. -/
theorem isExec (swap : Bool) (𝒜 : Set (Hist (Fin n) Op Y))
    (h𝒜 : ∀ t, (runCfg V (sched hn D swap) t).hist ∈ 𝒜) (hinj : Function.Injective D.c)
    (ha : ∀ k, D.c k ≠ D.a) (hb : ∀ k, D.c k ≠ D.b) :
    IsExec V 𝒜 (sched hn D swap) (runCfg V (sched hn D swap)) (runOut V (sched hn D swap)) where
  init := rfl
  step t := by
    obtain ⟨r, hr⟩ := step_some (V := V) hn D swap t
    obtain ⟨e1, e2⟩ := runCfg_succ_of_step hr
    rw [hr, e1, e2]
  legal := h𝒜
  distinct p o t t' htt' h1 h2 := by
    have hne := p₀_ne_p₁ hn
    rcases sched_eq_pre hn D h1 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨i, rfl, rfl, rfl⟩ <;>
      rcases sched_eq_pre hn D h2 with ⟨rfl, h3, h4⟩ | ⟨rfl, h3, h4⟩ | ⟨i', rfl, h3, h4⟩
    all_goals first
      | omega
      | exact hne h3
      | exact hne h3.symm
      | exact hb _ h4.symm
      | exact ha _ h4.symm
      | (have := hinj h4; omega)
  fair p t := by
    refine ⟨4 * (p.val + n * (t + 1) - 1) + 3 + 8, ?_, ?_⟩
    · have : t + 1 ≤ n * (t + 1) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    · rw [sched_post]
      congr 1
      ext
      simp only [q]
      rw [show p.val + n * (t + 1) - 1 + 1 = p.val + n * (t + 1) by
        have : 1 ≤ n * (t + 1) := Nat.one_le_iff_ne_zero.2 (by positivity); omega]
      simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt p.isLt]

end Sched


/-! ## Theorem 5.1 and Theorem A.1 -/

section Main

/-- The sequential history of `F`: `⟨a:ra⟩⟨b:rb⟩⟨c₁:rc⟩…⟨cᵢ:rc⟩`. -/
def Mseq (i : ℕ) : List (OpRec (Fin n) Unit Op Y) :=
  ⟨p₀ hn, (), D.a, D.ra⟩ :: ⟨p₁ hn, (), D.b, D.rb⟩ ::
    (List.range i).map (fun j => ⟨q hn (j + 1), (), D.c (j + 1), D.rc⟩)

/-- The sequential history of `E`: `⟨b:rb⟩⟨a:ra⟩⟨c₁:rc⟩…⟨cᵢ:rc⟩`. -/
def MseqE (i : ℕ) : List (OpRec (Fin n) Unit Op Y) :=
  ⟨p₁ hn, (), D.b, D.rb⟩ :: ⟨p₀ hn, (), D.a, D.ra⟩ ::
    (List.range i).map (fun j => ⟨q hn (j + 1), (), D.c (j + 1), D.rc⟩)

theorem histAt_true (i : ℕ) : histAt hn D true i = seqHist (Mseq hn D i) := by
  simp [histAt, H0, tailH, Mseq, seqHist, OpRec.events, List.flatMap_map]

theorem histAt_false (i : ℕ) : histAt hn D false i = seqHist (MseqE hn D i) := by
  simp [histAt, H0, tailH, MseqE, seqHist, OpRec.events, List.flatMap_map]

/-- Hypotheses on a sequential specification and the data `D` for the indistinguishability
argument: the specification is prefix closed, `⟨a:ra⟩⟨b:rb⟩⟨c₁:rc⟩⟨c₂:rc⟩…` is legal, `⟨b:rb⟩` alone
is illegal, and the operations `a, b, c₁, c₂, …` are pairwise distinct. -/
structure ImpData.Good (spec : SeqSpec (Fin n) Unit Op Y) : Prop where
  prefixClosed : PrefixClosedSpec spec
  legal : ∀ i, seqHist (Mseq hn D i) ∈ spec ()
  illegal : seqHist [⟨p₁ hn, (), D.b, D.rb⟩] ∉ spec ()
  c_inj : Function.Injective D.c
  c_ne_a : ∀ k, D.c k ≠ D.a
  c_ne_b : ∀ k, D.c k ≠ D.b

variable {hn D}
variable {spec : SeqSpec (Fin n) Unit Op Y}

/-- The non-linearizable implementation `A` of the proof: its histories are the prefixes of
the histories of `A` in `E` and `F`. -/
def badImpl (hn : 2 ≤ n) (D : ImpData Op Y) : Set (Hist (Fin n) Op Y) :=
  {h | ∃ swap i, h <+: histAt hn D swap i}

theorem badImpl_isAbstractImpl : IsAbstractImpl (badImpl hn D) := by
  refine ⟨?_, ?_⟩
  · rintro h ⟨swap, i, hp⟩
    have hwf : WellFormed (histAt hn D swap i) := by
      cases swap
      · rw [histAt_false]; exact wellFormed_seqHist _
      · rw [histAt_true]; exact wellFormed_seqHist _
    obtain ⟨t, ht⟩ := hp
    rw [← ht] at hwf
    exact hwf.of_append
  · rintro h ⟨swap, i, hp⟩ h' hh'
    exact ⟨swap, i, hh'.trans hp⟩

theorem linearizable_F (hD : D.Good hn spec) (V : Verifier n Op Y W) (t : ℕ) :
    Linearizable spec (runCfg V (sched hn D true) t).hist := by
  have hl : Linearizable spec (histAt hn D true t) := by
    rw [histAt_true]; exact linearizable_seqHist ((legal_seqHist_iff_of_subsingleton ()).2 (hD.legal t))
  exact lemma_7_1_prefix hD.prefixClosed hl (hist_mem hn D true t)

theorem not_linearizable_E (hD : D.Good hn spec) (V : Verifier n Op Y W) :
    ¬ Linearizable spec (runCfg V (sched hn D false) 6).hist := by
  intro hl
  obtain ⟨-, -, -, hh, -, -⟩ := run_six (V := V) hn D false
  rw [hh] at hl
  refine hD.illegal ((legal_seqHist_iff_of_subsingleton ()).1 (Linearizable.legal_seqHist ?_))
  exact lemma_7_1_prefix hD.prefixClosed hl ⟨[.inv (p₀ hn) () D.a, .res (p₀ hn) () D.ra], rfl⟩

/-- The core of the proof of Theorem 5.1: with input `badImpl`, a verifier cannot be sound in
`F` and (weakly) complete in `E`. -/
theorem core (hD : D.Good hn spec) (V : Verifier n Op Y W)
    (hV : ∀ s c out, IsExec V (badImpl hn D) s c out →
      ((∀ t, (c t).hist ∈ {H | Linearizable spec H}) → ∀ t, out t = none) ∧
      ((∃ t, (c t).hist ∉ {H | Linearizable spec H}) → ∃ t, out t ≠ none)) : False := by
  have hE := isExec (V := V) hn D false (badImpl hn D) (fun t => ⟨false, t, hist_mem hn D false t⟩)
    hD.c_inj hD.c_ne_a hD.c_ne_b
  have hF := isExec (V := V) hn D true (badImpl hn D) (fun t => ⟨true, t, hist_mem hn D true t⟩)
    hD.c_inj hD.c_ne_a hD.c_ne_b
  have hsound := (hV _ _ _ hF).1 (fun t => linearizable_F hD V t)
  obtain ⟨t, ht⟩ := (hV _ _ _ hE).2 ⟨6, not_linearizable_E hD V⟩
  exact ht (by rw [runOut_eq, hsound t])

/-- **Theorem 5.1** (generic form). If the sequential object admits operations `a, b, c₁, c₂, …`
such that `⟨a:ra⟩⟨b:rb⟩⟨c₁:rc⟩⟨c₂:rc⟩…` is legal but `⟨b:rb⟩` alone is not, then no verifier for
`n ≥ 2` processes, whatever its base objects (arbitrary shared memory with atomic blocks) and even
with synchronized clocks, distributed runtime verifies linearizability; in fact no verifier is
sound and (even weakly) complete. -/
theorem thm_5_1_weak (hD : D.Good hn spec) (V : Verifier n Op Y W) :
    ¬ WeaklyVerifies V {H | Linearizable spec H} :=
  fun hV => core hD V (hV _ badImpl_isAbstractImpl)

/-- **Theorem 5.1.** Linearizability is not distributed runtime verifiable (Definition 3.1). -/
theorem thm_5_1 (hD : D.Good hn spec) (V : Verifier n Op Y (Hist (Fin n) Op Y)) :
    ¬ RuntimeVerifies V {H | Linearizable spec H} :=
  fun h => thm_5_1_weak hD V h.weaklyVerifies

/-- **Theorem A.1.** Linearizability is not distributed runtime *predictively* verifiable
(Definition 6.1) for the general class of implementations. -/
theorem thm_A_1 (hD : D.Good hn spec) (V : Verifier n Op Y (Hist (Fin n) Op Y)) :
    ¬ PredictivelyVerifies V {H | Linearizable spec H} := by
  intro hV
  have hE := isExec (V := V) hn D false (badImpl hn D) (fun t => ⟨false, t, hist_mem hn D false t⟩)
    hD.c_inj hD.c_ne_a hD.c_ne_b
  have hgood : IsAbstractImpl {H : Hist (Fin n) Op Y | Linearizable spec H} :=
    ⟨fun h hh => hh.1, fun h hh h' hh' => lemma_7_1_prefix hD.prefixClosed hh hh'⟩
  have hF := isExec (V := V) hn D true {H | Linearizable spec H} (fun t => linearizable_F hD V t)
    hD.c_inj hD.c_ne_a hD.c_ne_b
  have hsound : ∀ t, runOut V (sched hn D true) t = none := by
    rcases (hV _ hgood _ _ _ hF).1 (fun t => linearizable_F hD V t) with h | ⟨t, w, -, hw1, hw2⟩
    · exact h
    · exact absurd hw1 hw2
  obtain ⟨t, w, hw, -⟩ := (hV _ badImpl_isAbstractImpl _ _ _ hE).2 ⟨6, not_linearizable_E hD V⟩
  rw [runOut_eq, hsound t] at hw
  cases hw

/-- The non-uniform reading of Section 3 ("`V_O` taking `A` as its input") does not help the
verifier for Definition 3.1: the proof of Theorem 5.1 uses a single input implementation. -/
theorem thm_5_1_nonuniform (hD : D.Good hn spec)
    (V : Set (Hist (Fin n) Op Y) → Verifier n Op Y (Hist (Fin n) Op Y)) :
    ¬ ∀ 𝒜, IsAbstractImpl 𝒜 → ∀ s c out, IsExec (V 𝒜) 𝒜 s c out →
      ((∀ t, (c t).hist ∈ {H | Linearizable spec H}) → ∀ t, out t = none) ∧
      ((∃ t, (c t).hist ∉ {H | Linearizable spec H}) → ∃ t, out t ≠ none) := by
  intro hV
  exact core hD (V (badImpl hn D)) (hV _ badImpl_isAbstractImpl)

end Main

/-! ## The non-uniform reading makes Definition 6.1 trivial -/

section Trivial

open Classical in
/-- A verifier that *knows* its input implementation `𝒜`: it reports a fixed violating history
of `𝒜` (if there is one) at every iteration, without looking at the execution. -/
noncomputable def trivialVerifier (𝒜 Pr : Set (Hist (Fin n) Op Y)) :
    Verifier n Op Y (Hist (Fin n) Op Y) where
  L := Unit
  M := Unit
  m0 := ()
  l0 := fun _ => ()
  pre := fun _ _ _ _ _ => ((), ())
  post := fun _ _ _ _ _ => ((), (), if h : ∃ w ∈ 𝒜, w ∉ Pr then some h.choose else none)

open Classical in
theorem trivialVerifier_out {𝒜 Pr : Set (Hist (Fin n) Op Y)} {s c out}
    (hE : IsExec (trivialVerifier 𝒜 Pr) 𝒜 s c out) (t : ℕ) :
    out t = none ∨ (∃ h : ∃ w ∈ 𝒜, w ∉ Pr, out t = some h.choose) := by
  have := hE.step t
  revert this
  cases s t <;> simp only [Verifier.step] <;> split <;> simp <;> intro _ h <;> rw [← h] <;>
    simp only [trivialVerifier] <;> (try split_ifs with h') <;> simp_all

/-- The process of an event. -/
def Ev.proc : Ev n Op Y → Fin n
  | .pre p _ => p
  | .inv p => p
  | .res p _ => p
  | .post p => p

open Classical in
theorem trivialVerifier_post {𝒜 Pr : Set (Hist (Fin n) Op Y)} {s c out}
    (hE : IsExec (trivialVerifier 𝒜 Pr) 𝒜 s c out) (hw : ∃ w ∈ 𝒜, w ∉ Pr) :
    ∃ t w, out t = some w ∧ w ∈ 𝒜 ∧ w ∉ Pr := by
  obtain ⟨t, -, ht⟩ := hE.fair (s 0).proc 0
  refine ⟨t, hw.choose, ?_, hw.choose_spec.1, hw.choose_spec.2⟩
  have := hE.step t
  rw [ht] at this
  revert this
  simp only [Verifier.step]
  split
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro _ h; rw [← h]; simp [trivialVerifier, hw]
  · simp

/-- Under the non-uniform reading (the verifier may depend on its input implementation `𝒜`),
predictive soundness and completeness (Definition 6.1) are achieved by `trivialVerifier`, for any
correctness condition `Pr` and any input. So Theorem A.1 needs the black-box reading. -/
theorem trivialVerifier_predictive (Pr : Set (Hist (Fin n) Op Y)) (𝒜 : Set (Hist (Fin n) Op Y))
    (s : ℕ → Ev n Op Y) (c : ℕ → Cfg (trivialVerifier 𝒜 Pr)) (out : ℕ → Option (Hist (Fin n) Op Y))
    (hE : IsExec (trivialVerifier 𝒜 Pr) 𝒜 s c out) :
    ((∀ t, (c t).hist ∈ Pr) →
      (∀ t, out t = none) ∨ ∃ t w, out t = some w ∧ w ∈ 𝒜 ∧ w ∉ Pr) ∧
    ((∃ t, (c t).hist ∉ Pr) → ∃ t w, out t = some w ∧ w ∈ 𝒜 ∧ w ∉ Pr) := by
  by_cases hw : ∃ w ∈ 𝒜, w ∉ Pr
  · exact ⟨fun _ => Or.inr (trivialVerifier_post hE hw), fun _ => trivialVerifier_post hE hw⟩
  · refine ⟨fun _ => Or.inl fun t => ?_, fun ⟨t, ht⟩ => absurd ⟨_, hE.legal t, ht⟩ hw⟩
    rcases trivialVerifier_out hE t with h | ⟨h, -⟩
    · exact h
    · exact absurd h hw

end Trivial

end Podc2023.RuntimeVerification.Impossibility
