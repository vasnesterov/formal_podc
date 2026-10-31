import Mathlib
import Cslib.Foundations.Data.Nat.Descent

/-!
# Write–scan loops in the fully-anonymous shared-memory model

Losa and Gafni, *Understanding Read-Write Wait-Free Coverings in the Fully-Anonymous Shared-Memory
Model* (PODC 2024), study algorithms in which every processor repeatedly

* writes its local information to a register it has not written since it last wrote all registers
  (fair, round-robin writes; label `l0`/`write` of Figures 1 and 3), and then
* reads all registers one by one, in any order (label `l1`/`scan`).

This file contains a generic model of such *write–scan loops*.

* Processors `P` and registers `R` are finite types. The registers are anonymous: the paper fixes,
  for each processor, an unknown permutation (wiring) of the registers, and the algorithms pick a
  register nondeterministically (`with (r ∈ R \ written)`), so the wiring is absorbed into the
  nondeterministic choice of the register in each step (`Act.write p r`, `Act.read p r` name
  *physical* registers). Quantifying over all executions of the nondeterministic model covers every
  wiring and every deterministic resolution of the choices.
* A register holds a value of type `X` together with a ghost field `writer` (the processor that
  wrote it last; `none` initially). The algorithms never read the ghost field.
* The local state of a processor consists of algorithm data `d : D`, the set `written` of
  registers written in the current round-robin cycle, and `scan : Option (Finset R)`: `none` at
  the write label, `some S` while scanning, where `S` is the set of registers read in the current
  scan.
* An algorithm (`Algo`) says what a processor writes (`wr`), how a read updates its data (`rd`),
  what it computes at the end of a scan (`fin`), and when it stops (`stop`, checked at the write
  label; a stopped processor can only take idle steps).
* An execution is an infinite sequence of configurations with a sequence of actions, each
  consecutive pair being a step of the action's processor (asynchrony: the schedule is arbitrary).
-/

namespace Podc.AnonymousCoverings

open Finset

/-- Local state of a processor. -/
structure Loc (R D : Type*) where
  /-- Algorithm-specific data (view, level, values read so far, …). -/
  d : D
  /-- Registers written since `written` was last reset (round-robin writes). -/
  written : Finset R
  /-- `none`: at the write label; `some S`: scanning, having read the registers in `S`. -/
  scan : Option (Finset R)

/-- Content of a register: a value and the (ghost) last writer. -/
structure Cell (P X : Type*) where
  /-- The value stored in the register. -/
  val : X
  /-- Ghost: the processor that wrote the register last (`none` if never written). -/
  writer : Option P

/-- A configuration: the registers and the local states. -/
structure Cfg (P R D X : Type*) where
  /-- Register contents. -/
  reg : R → Cell P X
  /-- Local states. -/
  loc : P → Loc R D

/-- A write–scan algorithm. -/
structure Algo (R D X : Type*) where
  /-- Value written at the write label. -/
  wr : D → X
  /-- Update of the data upon reading value `x` in register `r`. -/
  rd : D → R → X → D
  /-- Local computation at the end of a scan. -/
  fin : D → D
  /-- Termination condition, checked at the write label. -/
  stop : D → Prop

/-- Actions: a write of register `r`, a read of register `r`, or an idle step of a stopped
processor. -/
inductive Act (P R : Type*) where
  | write (p : P) (r : R)
  | read (p : P) (r : R)
  | idle (p : P)

/-- The processor taking an action. -/
def Act.proc {P R : Type*} : Act P R → P
  | .write p _ => p
  | .read p _ => p
  | .idle p => p

variable {P R D X : Type*} [DecidableEq P] [DecidableEq R] [Fintype R]

/-- Round-robin bookkeeping: add `r` to `written`, resetting to `∅` once all registers have
been written (`written := if written ∪ {r} = R then {} else written ∪ {r}`). -/
def nextWritten (w : Finset R) (r : R) : Finset R :=
  if insert r w = univ then ∅ else insert r w

/-- Configuration after `p` writes register `r`. -/
def writePost (A : Algo R D X) (c : Cfg P R D X) (p : P) (r : R) : Cfg P R D X :=
  ⟨Function.update c.reg r ⟨A.wr (c.loc p).d, some p⟩,
   Function.update c.loc p ⟨(c.loc p).d, nextWritten (c.loc p).written r, some ∅⟩⟩

/-- Configuration after `p` reads register `r` (ending the scan if all registers are read). -/
def readPost (A : Algo R D X) (c : Cfg P R D X) (p : P) (r : R) : Cfg P R D X :=
  let S := ((c.loc p).scan).getD ∅
  ⟨c.reg, Function.update c.loc p
    (if insert r S = univ then
      ⟨A.fin (A.rd (c.loc p).d r (c.reg r).val), (c.loc p).written, none⟩
    else ⟨A.rd (c.loc p).d r (c.reg r).val, (c.loc p).written, some (insert r S)⟩)⟩

/-- The step relation. -/
def Step (A : Algo R D X) : Act P R → Cfg P R D X → Cfg P R D X → Prop
  | .write p r, c, c' => (c.loc p).scan = none ∧ r ∉ (c.loc p).written ∧ ¬ A.stop (c.loc p).d ∧
      c' = writePost A c p r
  | .read p r, c, c' => (∃ S, (c.loc p).scan = some S ∧ r ∉ S) ∧ c' = readPost A c p r
  | .idle p, c, c' => (c.loc p).scan = none ∧ A.stop (c.loc p).d ∧ c' = c

/-- An (infinite) execution: configurations and actions such that every consecutive pair of
configurations is a step. The initial configuration is constrained separately. -/
structure Exec (A : Algo R D X) where
  /-- Configuration at each time. -/
  cfg : ℕ → Cfg P R D X
  /-- Action taken at each time. -/
  act : ℕ → Act P R
  /-- Every consecutive pair is a step. -/
  step : ∀ t, Step A (act t) (cfg t) (cfg (t + 1))

namespace Exec

variable {A : Algo R D X} (e : Exec (P := P) A)

/-- The local state of `p` at time `t`. -/
abbrev loc (t : ℕ) (p : P) : Loc R D := (e.cfg t).loc p

/-- The register `r` at time `t`. -/
abbrev reg (t : ℕ) (r : R) : Cell P X := (e.cfg t).reg r

/-- `p` is *live*: it takes infinitely many (non-idle) steps. -/
def Live (p : P) : Prop :=
  ∀ T, ∃ t ≥ T, ∃ r, e.act t = .write p r ∨ e.act t = .read p r

/-- `p` completes a scan at time `t`: its read at time `t` ends the scan. -/
def Completes (t : ℕ) (p : P) : Prop :=
  (∃ r, e.act t = .read p r) ∧ (e.loc (t + 1) p).scan = none

/-- `p` writes (some register) at time `t`. -/
def WritesAt (t : ℕ) (p : P) : Prop := ∃ r, e.act t = .write p r

/-! ### Basic step lemmas -/

theorem loc_succ_of_ne {t : ℕ} {q : P} (h : (e.act t).proc ≠ q) : e.loc (t + 1) q = e.loc t q := by
  have hs := e.step t
  unfold loc
  generalize e.act t = a at hs h
  cases a with
  | write p r =>
    obtain ⟨-, -, -, h'⟩ := hs
    simp only [Act.proc] at h
    rw [h']; simp [writePost, Function.update_of_ne (Ne.symm h)]
  | read p r =>
    obtain ⟨-, h'⟩ := hs
    simp only [Act.proc] at h
    rw [h']; simp [readPost, Function.update_of_ne (Ne.symm h)]
  | idle p =>
    obtain ⟨-, -, h'⟩ := hs
    rw [h']

theorem reg_succ_of_not_write {t : ℕ} {r : R} (h : ∀ p, e.act t ≠ .write p r) :
    e.reg (t + 1) r = e.reg t r := by
  have hs := e.step t
  unfold reg
  generalize e.act t = a at hs h
  cases a with
  | write p r' =>
    obtain ⟨-, -, -, h'⟩ := hs
    have : r ≠ r' := fun hr => h p (by rw [hr])
    rw [h']; simp [writePost, Function.update_of_ne this]
  | read p r' =>
    obtain ⟨-, h'⟩ := hs
    rw [h']; simp [readPost]
  | idle p =>
    obtain ⟨-, -, h'⟩ := hs
    rw [h']

theorem write_spec {t : ℕ} {p : P} {r : R} (h : e.act t = .write p r) :
    (e.loc t p).scan = none ∧ r ∉ (e.loc t p).written ∧ ¬ A.stop (e.loc t p).d ∧
      e.reg (t + 1) r = ⟨A.wr (e.loc t p).d, some p⟩ ∧
      e.loc (t + 1) p = ⟨(e.loc t p).d, nextWritten (e.loc t p).written r, some ∅⟩ := by
  have hs := e.step t
  rw [h] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · unfold reg; rw [h4]; simp [writePost]
  · unfold loc; rw [h4]; simp [writePost]

theorem read_spec {t : ℕ} {p : P} {r : R} (h : e.act t = .read p r) :
    ∃ S, (e.loc t p).scan = some S ∧ r ∉ S ∧
      e.loc (t + 1) p = (if insert r S = univ then
        ⟨A.fin (A.rd (e.loc t p).d r (e.reg t r).val), (e.loc t p).written, none⟩
      else ⟨A.rd (e.loc t p).d r (e.reg t r).val, (e.loc t p).written, some (insert r S)⟩) := by
  have hs := e.step t
  rw [h] at hs
  obtain ⟨⟨S, hS, hr⟩, h4⟩ := hs
  refine ⟨S, hS, hr, ?_⟩
  unfold loc reg; rw [h4]; simp [readPost, show (e.cfg t).loc p = e.loc t p from rfl, hS]

theorem idle_spec {t : ℕ} {p : P} (h : e.act t = .idle p) :
    (e.loc t p).scan = none ∧ A.stop (e.loc t p).d ∧ e.cfg (t + 1) = e.cfg t := by
  have hs := e.step t
  rw [h] at hs
  exact hs

/-- Registers are unchanged by reads and idle steps. -/
theorem reg_succ_of_read {t : ℕ} {p : P} {r : R} (h : e.act t = .read p r) (r' : R) :
    e.reg (t + 1) r' = e.reg t r' :=
  e.reg_succ_of_not_write (fun q => by rw [h]; simp)

/-- A write of `r` by `p` makes `p` the last writer of `r`. -/
theorem writer_succ_of_write {t : ℕ} {p : P} {r : R} (h : e.act t = .write p r) :
    (e.reg (t + 1) r).writer = some p := by
  rw [(e.write_spec h).2.2.2.1]

/-- The (ghost) last writer of `r` at time `t`, if any, did write `r` at an earlier time, and no
write of `r` happened since. -/
theorem exists_last_write {t : ℕ} {r : R} {q : P} (h : (e.reg t r).writer = some q)
    (h0 : (e.reg 0 r).writer = none) :
    ∃ w < t, e.act w = .write q r ∧ e.reg (w + 1) r = e.reg t r ∧
      ∀ w', w < w' → w' < t → ∀ p, e.act w' ≠ .write p r := by
  induction t with
  | zero => rw [h0] at h; exact absurd h (by simp)
  | succ t ih =>
    by_cases hw : ∃ p, e.act t = .write p r
    · obtain ⟨p, hp⟩ := hw
      have := e.writer_succ_of_write hp
      rw [h] at this
      cases this
      exact ⟨t, by omega, hp, rfl, fun w' h1 h2 => by omega⟩
    · push Not at hw
      have heq := e.reg_succ_of_not_write hw
      rw [heq] at h ⊢
      obtain ⟨w, hw1, hw2, hw3, hw4⟩ := ih h
      refine ⟨w, by omega, hw2, hw3, fun w' h1 h2 p => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
      · exact hw4 w' h1 h2 p
      · subst h2; exact hw p

/-- If the register `r` is unchanged over `[t, t']` unless written, its content is determined by
the last write. A register that no one writes during `[t, t')` keeps its content. -/
theorem reg_eq_of_no_write {t t' : ℕ} {r : R} (htt : t ≤ t')
    (h : ∀ w, t ≤ w → w < t' → ∀ p, e.act w ≠ .write p r) : e.reg t' r = e.reg t r := by
  induction t', htt using Nat.le_induction with
  | base => rfl
  | succ t' ht' ih =>
    rw [e.reg_succ_of_not_write (h t' ht' (by omega)), ih fun w h1 h2 => h w h1 (by omega)]

/-- If `p` is at the write label, its next non-idle action is a write. -/
theorem scan_none_of_write {t : ℕ} {p : P} {r : R} (h : e.act t = .write p r) :
    (e.loc t p).scan = none := (e.write_spec h).1

/-- The local state of `q` is unchanged over `[t, t']` if `q` takes no step. -/
theorem loc_eq_of_no_step {t t' : ℕ} {q : P} (htt : t ≤ t')
    (h : ∀ w, t ≤ w → w < t' → (e.act w).proc ≠ q) : e.loc t' q = e.loc t q := by
  induction t', htt using Nat.le_induction with
  | base => rfl
  | succ t' ht' ih =>
    rw [e.loc_succ_of_ne (h t' ht' (by omega)), ih fun w h1 h2 => h w h1 (by omega)]

end Exec

end Podc.AnonymousCoverings
