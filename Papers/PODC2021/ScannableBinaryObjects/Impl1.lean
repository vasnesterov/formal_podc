import Papers.PODC2021.ScannableBinaryObjects.Defs
import Cslib.Computability.Distributed.SharedMemory.LinPoints

/-!
# Implementation 1 of Ovens (PODC 2021): the algorithm

Implementation 1 (Section 4.1) is a lock-free `s`-scanner, `u`-updater implementation of the
scannable binary object `[O 0, …, O (k-1)]` from `s + k` one-bit base objects:

* `k` base objects `B i` of the same type as the components (`Obj O Sc (.inl i)`),
* one binary *handshaking* register `R j` per scanner `j ∈ Sc` (`Obj O Sc (.inr j)`).

`Update(i, op)`: write `1` to every handshaking bit, one at a time, then apply `op` to `B i`
and return its response. `Scan` by `p`: collect `B 0, …, B (k-1)` into `b`, write `0` to `R p`,
then repeatedly collect `B 0, …, B (k-1), R p`; return `b` after `u + 1` consecutive such
collects that read `b` and `0`; restart as soon as some `B i` differs from `b i` or `R p` reads
`1`.

The paper assumes the components are *readable*; we make this explicit: `BitObj.Readable O`
provides an invocation `rd` that does not change the value and whose response determines it.

Local states (`Loc`): `idle`; `upd i o rest` (update, handshaking bits in `rest` still to be
written; with `rest = []` the next step applies `o` to `B i`); `scan1 m b` (first collect, next
read is `B m`; for `m ≥ k` the next step writes `0` to `R p`); `scan2 c m b` (validation phase,
`c` successful collects so far, next read `B m`, or `R p` for `m ≥ k`); `done r` (return `r`).

The initial values of the handshaking bits are a parameter `h₀` (the proofs never use them).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Scannable

open Cslib.SharedMemory

/-- A *readable* 1-bit object: the invocation `rd` does not change the value and its response
determines the value (`val`). The paper assumes every component of a scannable object is
readable. -/
structure BitObj.Readable (O : BitObj) where
  /-- The read invocation. -/
  rd : O.Op
  /-- Decoding of the response of `rd`. -/
  val : O.Resp → Bool
  δ_rd_fst : ∀ v, (O.δ v rd).1 = v
  val_δ_rd : ∀ v, val (O.δ v rd).2 = v

/-- `scan` is the read-only operation of a scannable object. -/
def ScanOp.isScan {k : ℕ} {O : Fin k → BitObj} : ScanOp O → Bool
  | .scan => true
  | .update _ _ => false

namespace Impl1

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P]

/-- Base objects: `B i` (type of component `i`) and one binary register per scanner. -/
abbrev Obj (O : Fin k → BitObj) (Sc : Finset P) : Fin k ⊕ Sc → ObjSpec
  | .inl i => (O i).spec
  | .inr _ => binaryRegister

/-- Local states of Implementation 1. -/
inductive Loc (O : Fin k → BitObj) (Sc : Finset P) where
  | idle
  | upd (i : Fin k) (o : (O i).Op) (rest : List Sc)
  | scan1 (m : ℕ) (b : Fin k → Bool)
  | scan2 (c m : ℕ) (b : Fin k → Bool)
  | done (r : ScanResp O)

/-- The programs (`u` = number of updaters). -/
def act (R : ∀ i, (O i).Readable) (Sc : Finset P) (u : ℕ) (p : P) :
    Loc O Sc → Action (scannable O) (Obj O Sc) (Loc O Sc)
  | .idle => .ret (.view fun _ => false) .idle
  | .upd i o (j :: rest) =>
    .access (.inr j) (RWOp.write true) (fun _ => .upd i o rest)
  | .upd i o [] => .access (.inl i) o (fun r => .done (.resp i r))
  | .scan1 m b =>
    if h : m < k then
      .access (.inl ⟨m, h⟩) (R ⟨m, h⟩).rd
        (fun r => .scan1 (m + 1) (Function.update b ⟨m, h⟩ ((R ⟨m, h⟩).val r)))
    else if hp : p ∈ Sc then
      .access (.inr ⟨p, hp⟩) (RWOp.write false) (fun _ => .scan2 0 0 b)
    else .ret (.view b) .idle
  | .scan2 c m b =>
    if h : m < k then
      .access (.inl ⟨m, h⟩) (R ⟨m, h⟩).rd
        (fun r => if (R ⟨m, h⟩).val r = b ⟨m, h⟩ then .scan2 c (m + 1) b else .scan1 0 b)
    else if hp : p ∈ Sc then
      .access (.inr ⟨p, hp⟩) RWOp.read
        (fun v => if v = true then .scan1 0 b else if c < u then .scan2 (c + 1) 0 b
          else .done (.view b))
    else .ret (.view b) .idle
  | .done r => .ret r .idle

/-- **Implementation 1** with scanners `Sc`, updaters `Up` (a process may be both), readable
components (`R`) and initial values `h₀` of the handshaking bits. -/
noncomputable def impl1 (R : ∀ i, (O i).Readable) (Sc Up : Finset P) (h₀ : Sc → Bool) :
    Impl (scannable O) (Obj O Sc) P (Loc O Sc) where
  memInit
    | .inl _ => false
    | .inr j => h₀ j
  locInit _ := .idle
  invoke _ _ o := match o with
    | .scan => .scan1 0 (fun _ => false)
    | .update i o => .upd i o (Finset.univ : Finset Sc).toList
  act p l := act R Sc Up.card p l
  allowed p o := match o with
    | .scan => p ∈ Sc
    | .update _ _ => p ∈ Up


/-! ### Effects of individual steps -/

section Steps

variable {R : ∀ i, (O i).Readable} {Sc Up : Finset P} {h₀ : Sc → Bool}
  {C C' : Config (scannable O) (Obj O Sc) P (Loc O Sc)} {q : P}

lemma step_upd_cons {i : Fin k} {o : (O i).Op} {j : Sc} {rest : List Sc}
    (hl : C.loc q = .upd i o (j :: rest)) (h : (impl1 R Sc Up h₀).step C (.tau q) = some C') :
    C'.pend = C.pend ∧ C'.mem = Function.update C.mem (.inr j) true ∧
      C'.loc = Function.update C.loc q (.upd i o rest) := by
  obtain ⟨-, hpend, i', o', k', hact, hmem, hloc⟩ := Impl.step_tau h
  simp only [impl1, act, hl, Action.access.injEq] at hact
  obtain ⟨rfl, h1, h2⟩ := hact
  cases eq_of_heq h1; cases eq_of_heq h2
  exact ⟨hpend, hmem, hloc⟩

lemma step_upd_nil {i : Fin k} {o : (O i).Op}
    (hl : C.loc q = .upd i o []) (h : (impl1 R Sc Up h₀).step C (.tau q) = some C') :
    C'.pend = C.pend ∧
      C'.mem = Function.update C.mem (.inl i) ((O i).δ (C.mem (.inl i)) o).1 ∧
      C'.loc = Function.update C.loc q (.done (.resp i ((O i).δ (C.mem (.inl i)) o).2)) := by
  obtain ⟨-, hpend, i', o', k', hact, hmem, hloc⟩ := Impl.step_tau h
  simp only [impl1, act, hl, Action.access.injEq] at hact
  obtain ⟨rfl, h1, h2⟩ := hact
  cases eq_of_heq h1; cases eq_of_heq h2
  exact ⟨hpend, hmem, hloc⟩

lemma step_scan1_lt {m : ℕ} {b : Fin k → Bool} (hm : m < k)
    (hl : C.loc q = .scan1 m b) (h : (impl1 R Sc Up h₀).step C (.tau q) = some C') :
    C'.pend = C.pend ∧ C'.mem = C.mem ∧
      C'.loc = Function.update C.loc q (.scan1 (m + 1) (Function.update b ⟨m, hm⟩
        (C.mem (.inl ⟨m, hm⟩)))) := by
  obtain ⟨-, hpend, i', o', k', hact, hmem, hloc⟩ := Impl.step_tau h
  simp only [impl1, act, hl, hm, dite_true, Action.access.injEq] at hact
  obtain ⟨rfl, h1, h2⟩ := hact
  cases eq_of_heq h1; cases eq_of_heq h2
  refine ⟨hpend, ?_, ?_⟩
  · rw [hmem]; exact Function.update_eq_self_iff.2 ((R ⟨m, hm⟩).δ_rd_fst _)
  · rw [hloc]; simp only [(R ⟨m, hm⟩).val_δ_rd]

lemma step_scan1_ge {m : ℕ} {b : Fin k → Bool} (hm : ¬ m < k)
    (hl : C.loc q = .scan1 m b) (h : (impl1 R Sc Up h₀).step C (.tau q) = some C') :
    ∃ hq : q ∈ Sc, C'.pend = C.pend ∧ C'.mem = Function.update C.mem (.inr ⟨q, hq⟩) false ∧
      C'.loc = Function.update C.loc q (.scan2 0 0 b) := by
  obtain ⟨-, hpend, i', o', k', hact, hmem, hloc⟩ := Impl.step_tau h
  by_cases hq : q ∈ Sc
  · simp only [impl1, act, hl, hm, hq, dite_true, dite_false, Action.access.injEq] at hact
    obtain ⟨rfl, h1, h2⟩ := hact
    cases eq_of_heq h1; cases eq_of_heq h2
    exact ⟨hq, hpend, hmem, hloc⟩
  · simp [impl1, act, hl, hm, hq] at hact

lemma step_scan2_lt {c m : ℕ} {b : Fin k → Bool} (hm : m < k)
    (hl : C.loc q = .scan2 c m b) (h : (impl1 R Sc Up h₀).step C (.tau q) = some C') :
    C'.pend = C.pend ∧ C'.mem = C.mem ∧
      C'.loc = Function.update C.loc q
        (if C.mem (.inl ⟨m, hm⟩) = b ⟨m, hm⟩ then .scan2 c (m + 1) b else .scan1 0 b) := by
  obtain ⟨-, hpend, i', o', k', hact, hmem, hloc⟩ := Impl.step_tau h
  simp only [impl1, act, hl, hm, dite_true, Action.access.injEq] at hact
  obtain ⟨rfl, h1, h2⟩ := hact
  cases eq_of_heq h1; cases eq_of_heq h2
  refine ⟨hpend, ?_, ?_⟩
  · rw [hmem]; exact Function.update_eq_self_iff.2 ((R ⟨m, hm⟩).δ_rd_fst _)
  · rw [hloc]; simp only [(R ⟨m, hm⟩).val_δ_rd]

lemma step_scan2_ge {c m : ℕ} {b : Fin k → Bool} (hm : ¬ m < k)
    (hl : C.loc q = .scan2 c m b) (h : (impl1 R Sc Up h₀).step C (.tau q) = some C') :
    ∃ hq : q ∈ Sc, C'.pend = C.pend ∧ C'.mem = C.mem ∧
      C'.loc = Function.update C.loc q
        (if C.mem (.inr ⟨q, hq⟩) = true then .scan1 0 b else if c < Up.card then
          .scan2 (c + 1) 0 b else .done (.view b)) := by
  obtain ⟨-, hpend, i', o', k', hact, hmem, hloc⟩ := Impl.step_tau h
  by_cases hq : q ∈ Sc
  · simp only [impl1, act, hl, hm, hq, dite_true, dite_false, Action.access.injEq] at hact
    obtain ⟨rfl, h1, h2⟩ := hact
    cases eq_of_heq h1; cases eq_of_heq h2
    refine ⟨hq, hpend, ?_, hloc⟩
    rw [hmem]; exact Function.update_eq_self_iff.2 rfl
  · simp [impl1, act, hl, hm, hq] at hact

lemma step_tau_idle (hl : C.loc q = .idle) :
    (impl1 R Sc Up h₀).step C (.tau q) = none := by
  cases h : (impl1 R Sc Up h₀).step C (.tau q) with
  | none => rfl
  | some C' =>
    obtain ⟨-, -, i', o', k', hact, -⟩ := Impl.step_tau h
    simp [impl1, act, hl] at hact

lemma step_tau_done {r : ScanResp O} (hl : C.loc q = .done r) :
    (impl1 R Sc Up h₀).step C (.tau q) = none := by
  cases h : (impl1 R Sc Up h₀).step C (.tau q) with
  | none => rfl
  | some C' =>
    obtain ⟨-, -, i', o', k', hact, -⟩ := Impl.step_tau h
    simp [impl1, act, hl] at hact

end Steps

end Impl1

end Cslib.SharedMemory.Scannable
