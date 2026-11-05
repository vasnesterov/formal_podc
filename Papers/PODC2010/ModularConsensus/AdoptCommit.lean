import Papers.PODC2010.ModularConsensus.Basic
import Cslib.Computability.Distributed.SharedMemory.Potential
import Mathlib.Data.Finset.Sort

/-!
# Procedure AdoptCommit (Section 6.1, Theorem 8)

Model: CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`): any set `P` of
deterministic processes (finitely or infinitely many), atomic multi-writer registers, arbitrary
interleavings chosen by the scheduler, crashes = processes that stop taking steps (all
properties are stated for every finite, possibly partial, one-shot execution).

Shared data: a register `proposal : Option V` (initially `⊥ = none`) and binary registers
`r i`, `i : ι` (initially `0 = false`). Given write quorums `W v` and read quorums `R v`
(finite sets of registers), process `p` with input `v` executes

```
1  foreach r_i ∈ W_v do r_i ← 1
4  u ← proposal; if u ≠ ⊥ then preference ← u
7  else preference ← v; proposal ← preference
10 if r_i ≠ 0 for some r_i ∈ R_preference then return (adopt, preference)
13 else return (commit, preference)
```

The registers of a quorum are accessed in the order of `Finset.toList`; line 10 reads the
registers of `R_preference` one at a time and stops at the first `1` (reading the remaining ones
would not change anything).

## Main results

* `theorem8_safety` / `theorem8_solves` — **Theorem 8**: if `W v ∩ R v' = ∅ ↔ v = v'`,
  Procedure AdoptCommit satisfies validity, coherence and convergence in every finite (possibly
  partial) one-shot execution (`Impl.Solves (adoptCommitTask P V)`);
* `theorem8_waitFree` — termination: wait-freedom (when the read quorums have bounded size, e.g.
  finitely many values).

The proof is an invariant (`Inv`) over all reachable configurations; its key clause `Inv.k2`
says: if `p` is executing line 10 with preference `v` and has read the registers `S ⊆ R v` as
`0`, then no process with input `≠ v` that read `⊥` from `proposal` writes a register of `S`.
* `steps_le` — individual work: an operation performs at most `|W v| + 2 + ρ` register
  operations, where `ρ` bounds the sizes of the read quorums.
* `commit_eq_input` — the remark in the proof: a process can only commit its own input.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.ModularConsensus.AC

open Cslib.SharedMemory

variable {V ι : Type} [DecidableEq V] [DecidableEq ι] [Inhabited V]

/-- The adopt-commit object: operation = input value, response = (decision, value). -/
abbrev acObj (V : Type) [Inhabited V] : ObjSpec where
  State := Unit
  Op := V
  Resp := Decision × V
  init := ()
  δ _ _ := ((), default)

lemma acObj_eq_taskObj : acObj V = taskObj V (Decision × V) := rfl

/-- The base objects: `none` is the register `proposal` (values `Option V`, initially `⊥`),
`some i` is the binary register `r i` (initially `0`). -/
abbrev Mem (V ι : Type) : Option ι → ObjSpec
  | none => register (Option V) none
  | some _ => binaryRegister false

/-- Program counter. -/
inductive PC where
  /-- not invoked yet -/
  | idle
  /-- lines 1–4: writing `W v`, then reading `proposal` -/
  | ann
  /-- line 8: about to write `proposal` -/
  | wprop
  /-- line 10: reading `R preference` -/
  | chk
  /-- line 11: a `1` was read, about to return `adopt` -/
  | fin
  /-- returned -/
  | done
  deriving DecidableEq

/-- Local state of a process. -/
structure Loc (V ι : Type) where
  /-- Program counter. -/
  pc : PC
  /-- Input `v`. -/
  inp : V
  /-- The value `u` read from `proposal` (`none` = `⊥`). -/
  u : Option V
  /-- Remaining registers of the current quorum. -/
  todo : List ι
  /-- The decision returned (meaningful when `pc = done`). -/
  dec : Decision

/-- `preference`: the value read from `proposal`, or the input if it was `⊥`. -/
def Loc.pref (l : Loc V ι) : V := l.u.getD l.inp

/-- **Procedure AdoptCommit** with write quorums `W` and read quorums `R`. -/
noncomputable def acImpl (P : Type) (W R : V → Finset ι) : Impl (acObj V) (Mem V ι) P (Loc V ι) where
  memInit
    | none => (none : Option V)
    | some _ => false
  locInit _ := ⟨.idle, default, none, [], .adopt⟩
  invoke _ _ v := ⟨.ann, v, none, (W v).toList, .adopt⟩
  act _ l := match l.pc with
    | .ann => match l.todo with
      | i :: rest => .access (some i) (.write true) (fun _ => { l with todo := rest })
      | [] => .access none .read (fun x => match x with
        | none => { l with pc := .wprop, u := none }
        | some y => { l with pc := .chk, u := some y, todo := (R y).toList })
    | .wprop => .access none (.write (some l.inp)) (fun _ => { l with pc := .chk, todo := (R l.inp).toList })
    | .chk => match l.todo with
      | i :: rest => .access (some i) .read
          (fun b => if b then { l with pc := .fin } else { l with todo := rest })
      | [] => .ret (.commit, l.pref) { l with pc := .done, dec := .commit }
    | .fin => .ret (.adopt, l.pref) { l with pc := .done, dec := .adopt }
    | .done => .ret (l.dec, l.pref) l
    | .idle => .ret default l

/-! ### Shapes of steps -/

section Steps

variable {P : Type} [DecidableEq P] {W R : V → Finset ι}

/-- Configurations of Procedure AdoptCommit. -/
abbrev Cfg (P V ι : Type) [Inhabited V] := Config (acObj V) (Mem V ι) P (Loc V ι)

/-- The possible internal steps (register accesses) of a process. -/
lemma step_tau_cases {C C' : Cfg P V ι} {p : P}
    (h : (acImpl P W R).step C (.tau p) = some C') :
    C'.pend = C.pend ∧
    ((∃ i rest, (C.loc p).pc = .ann ∧ (C.loc p).todo = i :: rest ∧
        C'.loc = Function.update C.loc p { C.loc p with todo := rest } ∧
        C'.mem = Function.update C.mem (some i) true) ∨
     ((C.loc p).pc = .ann ∧ (C.loc p).todo = [] ∧ C.mem none = none ∧
        C'.loc = Function.update C.loc p { C.loc p with pc := .wprop, u := none } ∧
        C'.mem = C.mem) ∨
     (∃ y, (C.loc p).pc = .ann ∧ (C.loc p).todo = [] ∧ C.mem none = some y ∧
        C'.loc = Function.update C.loc p
          { C.loc p with pc := .chk, u := some y, todo := (R y).toList } ∧
        C'.mem = C.mem) ∨
     ((C.loc p).pc = .wprop ∧
        C'.loc = Function.update C.loc p
          { C.loc p with pc := .chk, todo := (R (C.loc p).inp).toList } ∧
        C'.mem = Function.update C.mem none (some (C.loc p).inp)) ∨
     (∃ i rest, (C.loc p).pc = .chk ∧ (C.loc p).todo = i :: rest ∧ C.mem (some i) = true ∧
        C'.loc = Function.update C.loc p { C.loc p with pc := .fin } ∧ C'.mem = C.mem) ∨
     (∃ i rest, (C.loc p).pc = .chk ∧ (C.loc p).todo = i :: rest ∧ C.mem (some i) = false ∧
        C'.loc = Function.update C.loc p { C.loc p with todo := rest } ∧ C'.mem = C.mem)) := by
  have hp : C.pend p ≠ none := (Impl.step_tau h).1
  rcases hl : C.loc p with ⟨pc, inp, u, todo, dec⟩
  cases pc <;> try (simp [Impl.step, hp, acImpl, hl] at h)
  · -- ann
    cases todo with
    | cons i rest =>
      simp [Impl.step, hp, acImpl, hl] at h
      subst h
      refine ⟨rfl, Or.inl ⟨i, rest, rfl, rfl, rfl, rfl⟩⟩
    | nil =>
      simp [Impl.step, hp, acImpl, hl] at h
      subst h
      rcases hm : C.mem none with _ | y
      · refine ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl, ?_, ?_⟩)⟩
        · simp [hm]
        · simp
      · refine ⟨rfl, Or.inr (Or.inr (Or.inl ⟨y, rfl, rfl, rfl, ?_, ?_⟩))⟩
        · simp [hm]
        · simp
  · -- wprop
    subst h
    exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))⟩
  · -- chk
    cases todo with
    | nil => simp [Impl.step, hp, acImpl, hl] at h
    | cons i rest =>
      simp [Impl.step, hp, acImpl, hl] at h
      subst h
      rcases hb : C.mem (some i) with _ | _
      · refine ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, rest, rfl, rfl, hb, ?_, ?_⟩))))⟩
        · simp [hb]
        · simp
      · refine ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rest, rfl, rfl, hb, ?_, ?_⟩))))⟩
        · simp [hb]
        · simp

end Steps

/-! ### The invariant -/

section Invariant

variable {P : Type} [DecidableEq P] {W R : V → Finset ι}

/-- The process has read `proposal` (it is past line 4). -/
def Rd (l : Loc V ι) : Prop := l.pc = .wprop ∨ l.pc = .chk ∨ l.pc = .fin ∨ l.pc = .done

/-- The process is past line 9 (`proposal` is set). -/
def Post (l : Loc V ι) : Prop := l.pc = .chk ∨ l.pc = .fin ∨ l.pc = .done

/-- The process read `⊥` from `proposal`. -/
def ReadBot (l : Loc V ι) : Prop := Rd l ∧ l.u = none

/-- The process is executing line 10 without having seen a `1`, or has committed. -/
def Clean (l : Loc V ι) : Prop := l.pc = .chk ∨ (l.pc = .done ∧ l.dec = .commit)

/-- The registers of `R (pref p)` already read by `p` (as `0`). -/
def Seen (R : V → Finset ι) (l : Loc V ι) (i : ι) : Prop := i ∈ R l.pref ∧ i ∉ l.todo

/-- The invariant of Procedure AdoptCommit. -/
structure Inv (W R : V → Finset ι) (C : Cfg P V ι) : Prop where
  pend : ∀ q, C.pend q = none ↔ ((C.loc q).pc = .idle ∨ (C.loc q).pc = .done)
  ann : ∀ q, (C.loc q).pc = .ann → ∀ i ∈ W (C.loc q).inp, i ∉ (C.loc q).todo →
    C.mem (some i) = true
  g1 : ∀ q, Rd (C.loc q) → ∀ i ∈ W (C.loc q).inp, C.mem (some i) = true
  g4 : ∀ q, Post (C.loc q) → C.mem none ≠ none
  wprop : ∀ q, (C.loc q).pc = .wprop → (C.loc q).u = none
  g5 : ∀ x, C.mem none = some x → ∃ q, Post (C.loc q) ∧ (C.loc q).u = none ∧ (C.loc q).inp = x
  g6 : ∀ q x, (C.loc q).u = some x →
    ∃ q', Post (C.loc q') ∧ (C.loc q').u = none ∧ (C.loc q').inp = x
  g8 : ∀ i, C.mem (some i) = true → ∃ q, (C.loc q).pc ≠ .idle ∧ i ∈ W (C.loc q).inp
  fin : ∀ q, ((C.loc q).pc = .fin ∨ ((C.loc q).pc = .done ∧ (C.loc q).dec = .adopt)) →
    ∃ i ∈ R (C.loc q).pref, C.mem (some i) = true
  doneT : ∀ q, (C.loc q).pc = .done → (C.loc q).dec = .commit → (C.loc q).todo = []
  k1 : ∀ p, Clean (C.loc p) → ∀ i, Seen R (C.loc p) i → i ∉ W (C.loc p).inp
  k2 : ∀ p q, Clean (C.loc p) → ReadBot (C.loc q) → (C.loc q).inp ≠ (C.loc p).pref →
    ∀ i, Seen R (C.loc p) i → i ∉ W (C.loc q).inp
  idle : ∀ q, (C.loc q).pc = .idle → (C.loc q).u = none
  annU : ∀ q, (C.loc q).pc = .ann → (C.loc q).u = none
  annSub : ∀ q, (C.loc q).pc = .ann → ∀ i ∈ (C.loc q).todo, i ∈ W (C.loc q).inp
  chkSub : ∀ q, (C.loc q).pc = .chk → ∀ i ∈ (C.loc q).todo, i ∈ R (C.loc q).pref

lemma inv_init : Inv (P := P) W R (acImpl P W R).initCfg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Impl.initCfg, acImpl, Rd, Post, ReadBot, Clean]


@[simp] lemma upd_none_some {m : (j : Option ι) → (Mem V ι j).State} {x : Option V} (i : ι) :
    Function.update m none x (some i) = m (some i) :=
  Function.update_of_ne (by simp) _ _

@[simp] lemma upd_none_none {m : (j : Option ι) → (Mem V ι j).State} {x : Option V} :
    Function.update m none x none = x :=
  Function.update_self _ _ _

@[simp] lemma upd_some_none {m : (j : Option ι) → (Mem V ι j).State} {b : Bool} (i : ι) :
    Function.update m (some i) b none = m none :=
  Function.update_of_ne (by simp) _ _

lemma upd_some_some {m : (j : Option ι) → (Mem V ι j).State} {b : Bool} (i j : ι) :
    Function.update m (some i) b (some j) = if j = i then b else m (some j) := by
  by_cases h : j = i
  · subst h; simp
  · rw [Function.update_of_ne (by simpa using h)]; simp [h]


lemma Clean.post {l : Loc V ι} (h : Clean l) : Post l := by
  rcases h with h | ⟨h, -⟩ <;> simp [Post, h]

lemma Post.rd {l : Loc V ι} (h : Post l) : Rd l := by
  rcases h with h | h | h <;> simp [Rd, h]

lemma loc_upd {C' : Cfg P V ι} {L : P → Loc V ι} {p : P} {l : Loc V ι}
    (hl : C'.loc = Function.update L p l) (q : P) :
    C'.loc q = if q = p then l else L q := by
  rw [hl, Function.update_apply]

/-- Step T1: `p` writes `1` into the next register of `W v`. -/
lemma inv_T1 {C C' : Cfg P V ι} {p : P} {i : ι} {rest : List ι} (hI : Inv W R C)
    (hpc : (C.loc p).pc = .ann) (ht : (C.loc p).todo = i :: rest)
    (hpend : C'.pend = C.pend)
    (hl : C'.loc = Function.update C.loc p { C.loc p with todo := rest })
    (hm : C'.mem = Function.update C.mem (some i) true) : Inv W R C' := by
  have hi : i ∈ W (C.loc p).inp := hI.annSub p hpc i (by simp [ht])
  have L := loc_upd hl
  have M0 : C'.mem none = C.mem none := by rw [hm]; simp
  have M1 : ∀ j, C'.mem (some j) = if j = i then true else C.mem (some j) := by
    intro j; rw [hm, upd_some_some]
  have Mmono : ∀ j, C.mem (some j) = true → C'.mem (some j) = true := by
    intro j h; rw [M1]; split_ifs <;> simp_all
  -- the fields of `p` other than `todo` are unchanged
  have Lpc : ∀ q, (C'.loc q).pc = (C.loc q).pc := by intro q; rw [L]; split_ifs with h <;> simp [h]
  have Linp : ∀ q, (C'.loc q).inp = (C.loc q).inp := by
    intro q; rw [L]; split_ifs with h <;> simp [h]
  have Lu : ∀ q, (C'.loc q).u = (C.loc q).u := by intro q; rw [L]; split_ifs with h <;> simp [h]
  have Ldec : ∀ q, (C'.loc q).dec = (C.loc q).dec := by
    intro q; rw [L]; split_ifs with h <;> simp [h]
  have Lpref : ∀ q, (C'.loc q).pref = (C.loc q).pref := by
    intro q; simp [Loc.pref, Lu, Linp]
  have Ltodo : ∀ q, q ≠ p → (C'.loc q).todo = (C.loc q).todo := by
    intro q hq; rw [L]; simp [hq]
  have Lrd : ∀ q, Rd (C'.loc q) ↔ Rd (C.loc q) := by intro q; simp [Rd, Lpc]
  have Lpost : ∀ q, Post (C'.loc q) ↔ Post (C.loc q) := by intro q; simp [Post, Lpc]
  have Lclean : ∀ q, Clean (C'.loc q) ↔ Clean (C.loc q) := by intro q; simp [Clean, Lpc, Ldec]
  have Lrb : ∀ q, ReadBot (C'.loc q) ↔ ReadBot (C.loc q) := by intro q; simp [ReadBot, Lrd, Lu]
  have Lseen : ∀ q, Clean (C.loc q) → ∀ j, Seen R (C'.loc q) j ↔ Seen R (C.loc q) j := by
    intro q hq j
    have : q ≠ p := by
      rintro rfl; rcases hq with h | ⟨h, -⟩ <;> simp [h] at hpc
    simp [Seen, Lpref, Ltodo q this]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q; rw [hpend, Lpc]; exact hI.pend q
  · intro q hq j hj hjt
    rw [Lpc] at hq; rw [Linp] at hj
    by_cases hqp : q = p
    · subst hqp
      rw [M1]
      split_ifs with hji
      · rfl
      · apply hI.ann q hq j hj
        rw [ht]; simp only [List.mem_cons, not_or]
        refine ⟨hji, ?_⟩
        simpa [L] using hjt
    · rw [Ltodo q hqp] at hjt
      exact Mmono j (hI.ann q hq j hj hjt)
  · intro q hq j hj
    rw [Lrd] at hq; rw [Linp] at hj
    exact Mmono j (hI.g1 q hq j hj)
  · intro q hq; rw [Lpost] at hq; rw [M0]; exact hI.g4 q hq
  · intro q hq; rw [Lpc] at hq; rw [Lu]; exact hI.wprop q hq
  · intro x hx; rw [M0] at hx
    obtain ⟨q, h1, h2, h3⟩ := hI.g5 x hx
    exact ⟨q, (Lpost q).2 h1, by rw [Lu]; exact h2, by rw [Linp]; exact h3⟩
  · intro q x hx; rw [Lu] at hx
    obtain ⟨q', h1, h2, h3⟩ := hI.g6 q x hx
    exact ⟨q', (Lpost q').2 h1, by rw [Lu]; exact h2, by rw [Linp]; exact h3⟩
  · intro j hj
    rw [M1] at hj
    split_ifs at hj with hji
    · subst hji; exact ⟨p, by rw [Lpc, hpc]; simp, by rw [Linp]; exact hi⟩
    · obtain ⟨q, h1, h2⟩ := hI.g8 j hj
      exact ⟨q, by rw [Lpc]; exact h1, by rw [Linp]; exact h2⟩
  · intro q hq
    rw [Lpc, Ldec] at hq
    obtain ⟨j, hj, hj'⟩ := hI.fin q hq
    exact ⟨j, by rw [Lpref]; exact hj, Mmono j hj'⟩
  · intro q hq hd
    rw [Lpc] at hq; rw [Ldec] at hd
    have hqp : q ≠ p := by rintro rfl; simp [hq] at hpc
    rw [Ltodo q hqp]; exact hI.doneT q hq hd
  · intro q hq j hj
    rw [Lclean] at hq; rw [Lseen q hq] at hj; rw [Linp]
    exact hI.k1 q hq j hj
  · intro q r hq hr hne j hj
    rw [Lclean] at hq; rw [Lrb] at hr; rw [Linp, Lpref] at hne; rw [Lseen q hq] at hj
    rw [Linp]; exact hI.k2 q r hq hr hne j hj
  · intro q hq; rw [Lpc] at hq; rw [Lu]; exact hI.idle q hq
  · intro q hq; rw [Lpc] at hq; rw [Lu]; exact hI.annU q hq
  · intro q hq j hj
    rw [Lpc] at hq; rw [Linp]
    by_cases hqp : q = p
    · subst hqp
      apply hI.annSub q hq j
      rw [ht]; simp only [L, ↓reduceIte] at hj; simp [hj]
    · rw [Ltodo q hqp] at hj; exact hI.annSub q hq j hj
  · intro q hq j hj
    rw [Lpc] at hq; rw [Lpref]
    have hqp : q ≠ p := by rintro rfl; simp [hq] at hpc
    rw [Ltodo q hqp] at hj; exact hI.chkSub q hq j hj


/-- Step T2: `p` reads `⊥` from `proposal`. -/
lemma inv_T2 {C C' : Cfg P V ι} {p : P} (hI : Inv W R C)
    (hpc : (C.loc p).pc = .ann) (ht : (C.loc p).todo = []) (hb : C.mem none = none)
    (hpend : C'.pend = C.pend)
    (hl : C'.loc = Function.update C.loc p { C.loc p with pc := .wprop, u := none })
    (hm : C'.mem = C.mem) : Inv W R C' := by
  have L := loc_upd hl
  have Lp : C'.loc p = { C.loc p with pc := .wprop, u := none } := by simp [L]
  have Lo : ∀ q, q ≠ p → C'.loc q = C.loc q := by intro q hq; simp [L, hq]
  have hu : (C.loc p).u = none := hI.annU p hpc
  have noClean : ∀ q, ¬ Clean (C.loc q) := fun q hq => hI.g4 q hq.post hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q; rw [hpend]
    by_cases hqp : q = p
    · subst hqp; rw [Lp]
      have := hI.pend q; simp only [hpc] at this; simpa using this
    · rw [Lo q hqp]; exact hI.pend q
  · intro q hq j hj hjt
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq hj hjt; rw [hm]; exact hI.ann q hq j hj hjt
  · intro q hq j hj
    rw [hm]
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hj; exact hI.ann q hpc j hj (by simp [ht])
    · rw [Lo q hqp] at hq hj; exact hI.g1 q hq j hj
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [Post] at hq
    · rw [Lo q hqp] at hq; rw [hm]; exact hI.g4 q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp]
    · rw [Lo q hqp] at hq ⊢; exact hI.wprop q hq
  · intro x hx; rw [hm] at hx
    obtain ⟨q, h1, h2, h3⟩ := hI.g5 x hx
    have hqp : q ≠ p := by rintro rfl; simp [Post, hpc] at h1
    exact ⟨q, by rw [Lo q hqp]; exact h1, by rw [Lo q hqp]; exact h2, by rw [Lo q hqp]; exact h3⟩
  · intro q x hx
    have hqp : q ≠ p := by rintro rfl; rw [Lp] at hx; simp at hx
    rw [Lo q hqp] at hx
    obtain ⟨q', h1, h2, h3⟩ := hI.g6 q x hx
    have hqp' : q' ≠ p := by rintro rfl; simp [Post, hpc] at h1
    exact ⟨q', by rw [Lo q' hqp']; exact h1, by rw [Lo q' hqp']; exact h2,
      by rw [Lo q' hqp']; exact h3⟩
  · intro j hj; rw [hm] at hj
    obtain ⟨q, h1, h2⟩ := hI.g8 j hj
    by_cases hqp : q = p
    · subst hqp; exact ⟨q, by rw [Lp]; simp, by rw [Lp]; exact h2⟩
    · exact ⟨q, by rw [Lo q hqp]; exact h1, by rw [Lo q hqp]; exact h2⟩
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; rw [hm]; exact hI.fin q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.doneT q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [Clean] at hq
    · rw [Lo q hqp] at hq; exact absurd hq (noClean q)
  · intro q r hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [Clean] at hq
    · rw [Lo q hqp] at hq; exact absurd hq (noClean q)
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.idle q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.annU q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.annSub q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.chkSub q hq


/-- Step T3: `p` reads a value `y ≠ ⊥` from `proposal` and adopts it as its preference. -/
lemma inv_T3 {C C' : Cfg P V ι} {p : P} {y : V} (hI : Inv W R C)
    (hpc : (C.loc p).pc = .ann) (ht : (C.loc p).todo = []) (hb : C.mem none = some y)
    (hpend : C'.pend = C.pend)
    (hl : C'.loc = Function.update C.loc p
      { C.loc p with pc := .chk, u := some y, todo := (R y).toList })
    (hm : C'.mem = C.mem) : Inv W R C' := by
  have L := loc_upd hl
  have Lp : C'.loc p = { C.loc p with pc := .chk, u := some y, todo := (R y).toList } := by
    simp [L]
  have Lo : ∀ q, q ≠ p → C'.loc q = C.loc q := by intro q hq; simp [L, hq]
  have notPost : ¬ Post (C.loc p) := by simp [Post, hpc]
  have neP : ∀ q, Post (C.loc q) → q ≠ p := by rintro q h rfl; exact notPost h
  have hpref : (C'.loc p).pref = y := by rw [Lp]; simp [Loc.pref]
  have seenP : ∀ j, ¬ Seen R (C'.loc p) j := by
    intro j hj; rw [Seen, hpref] at hj; rw [Lp] at hj; simp at hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q; rw [hpend]
    by_cases hqp : q = p
    · subst hqp; rw [Lp]
      have := hI.pend q; simp only [hpc] at this; simpa using this
    · rw [Lo q hqp]; exact hI.pend q
  · intro q hq j hj hjt
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq hj hjt; rw [hm]; exact hI.ann q hq j hj hjt
  · intro q hq j hj
    rw [hm]
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hj; exact hI.ann q hpc j hj (by simp [ht])
    · rw [Lo q hqp] at hq hj; exact hI.g1 q hq j hj
  · intro q _; rw [hm, hb]; simp
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.wprop q hq
  · intro x hx; rw [hm] at hx
    obtain ⟨q, h1, h2, h3⟩ := hI.g5 x hx
    have hqp := neP q h1
    exact ⟨q, by rw [Lo q hqp]; exact h1, by rw [Lo q hqp]; exact h2, by rw [Lo q hqp]; exact h3⟩
  · intro q x hx
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hx; simp only [Option.some.injEq] at hx; subst hx
      obtain ⟨q', h1, h2, h3⟩ := hI.g5 _ hb
      have hqp' := neP q' h1
      exact ⟨q', by rw [Lo q' hqp']; exact h1, by rw [Lo q' hqp']; exact h2,
        by rw [Lo q' hqp']; exact h3⟩
    · rw [Lo q hqp] at hx
      obtain ⟨q', h1, h2, h3⟩ := hI.g6 q x hx
      have hqp' := neP q' h1
      exact ⟨q', by rw [Lo q' hqp']; exact h1, by rw [Lo q' hqp']; exact h2,
        by rw [Lo q' hqp']; exact h3⟩
  · intro j hj; rw [hm] at hj
    obtain ⟨q, h1, h2⟩ := hI.g8 j hj
    by_cases hqp : q = p
    · subst hqp; exact ⟨q, by rw [Lp]; simp, by rw [Lp]; exact h2⟩
    · exact ⟨q, by rw [Lo q hqp]; exact h1, by rw [Lo q hqp]; exact h2⟩
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; rw [hm]; exact hI.fin q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.doneT q hq
  · intro q hq j hj
    by_cases hqp : q = p
    · subst hqp; exact absurd hj (seenP j)
    · rw [Lo q hqp] at hq hj ⊢; exact hI.k1 q hq j hj
  · intro q r hq hr hne j hj
    by_cases hqp : q = p
    · subst hqp; exact absurd hj (seenP j)
    · by_cases hrp : r = p
      · subst hrp; rw [Lp] at hr; simp [ReadBot] at hr
      · rw [Lo q hqp] at hq hj hne; rw [Lo r hrp] at hr hne ⊢
        exact hI.k2 q r hq hr hne j hj
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.idle q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.annU q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.annSub q hq
  · intro q hq j hj
    by_cases hqp : q = p
    · subst hqp; rw [hpref]; rw [Lp] at hj; simpa using hj
    · rw [Lo q hqp] at hq hj ⊢; exact hI.chkSub q hq j hj


/-- Step T4: `p` writes its input into `proposal`. -/
lemma inv_T4 {C C' : Cfg P V ι} {p : P} (hI : Inv W R C)
    (hpc : (C.loc p).pc = .wprop)
    (hpend : C'.pend = C.pend)
    (hl : C'.loc = Function.update C.loc p
      { C.loc p with pc := .chk, todo := (R (C.loc p).inp).toList })
    (hm : C'.mem = Function.update C.mem none (some (C.loc p).inp)) : Inv W R C' := by
  have L := loc_upd hl
  have Lp : C'.loc p = { C.loc p with pc := .chk, todo := (R (C.loc p).inp).toList } := by
    simp [L]
  have Lo : ∀ q, q ≠ p → C'.loc q = C.loc q := by intro q hq; simp [L, hq]
  have hu : (C.loc p).u = none := hI.wprop p hpc
  have M0 : C'.mem none = some (C.loc p).inp := by rw [hm]; simp
  have M1 : ∀ j, C'.mem (some j) = C.mem (some j) := by intro j; rw [hm]; simp
  have notPost : ¬ Post (C.loc p) := by simp [Post, hpc]
  have neP : ∀ q, Post (C.loc q) → q ≠ p := by rintro q h rfl; exact notPost h
  have hpref : (C'.loc p).pref = (C.loc p).inp := by rw [Lp]; simp [Loc.pref, hu]
  have seenP : ∀ j, ¬ Seen R (C'.loc p) j := by
    intro j hj; rw [Seen, hpref] at hj; rw [Lp] at hj; simp at hj
  have rdP : Rd (C.loc p) := by simp [Rd, hpc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q; rw [hpend]
    by_cases hqp : q = p
    · subst hqp; rw [Lp]
      have := hI.pend q; simp only [hpc] at this; simpa using this
    · rw [Lo q hqp]; exact hI.pend q
  · intro q hq j hj hjt
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq hj hjt; rw [M1]; exact hI.ann q hq j hj hjt
  · intro q hq j hj
    rw [M1]
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hj; exact hI.g1 q rdP j hj
    · rw [Lo q hqp] at hq hj; exact hI.g1 q hq j hj
  · intro q _; rw [M0]; simp
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.wprop q hq
  · intro x hx; rw [M0] at hx; simp only [Option.some.injEq] at hx; subst hx
    exact ⟨p, by rw [Lp]; simp [Post], by rw [Lp]; exact hu, by rw [Lp]⟩
  · intro q x hx
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hx; simp [hu] at hx
    · rw [Lo q hqp] at hx
      obtain ⟨q', h1, h2, h3⟩ := hI.g6 q x hx
      have hqp' := neP q' h1
      exact ⟨q', by rw [Lo q' hqp']; exact h1, by rw [Lo q' hqp']; exact h2,
        by rw [Lo q' hqp']; exact h3⟩
  · intro j hj; rw [M1] at hj
    obtain ⟨q, h1, h2⟩ := hI.g8 j hj
    by_cases hqp : q = p
    · subst hqp; exact ⟨q, by rw [Lp]; simp, by rw [Lp]; exact h2⟩
    · exact ⟨q, by rw [Lo q hqp]; exact h1, by rw [Lo q hqp]; exact h2⟩
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢
      obtain ⟨j, hj, hj'⟩ := hI.fin q hq
      exact ⟨j, hj, by rw [M1]; exact hj'⟩
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.doneT q hq
  · intro q hq j hj
    by_cases hqp : q = p
    · subst hqp; exact absurd hj (seenP j)
    · rw [Lo q hqp] at hq hj ⊢; exact hI.k1 q hq j hj
  · intro q r hq hr hne j hj
    by_cases hqp : q = p
    · subst hqp; exact absurd hj (seenP j)
    · rw [Lo q hqp] at hq hj hne
      by_cases hrp : r = p
      · subst hrp
        have hr0 : ReadBot (C.loc r) := ⟨rdP, hu⟩
        rw [Lp] at hne ⊢
        exact hI.k2 q r hq hr0 hne j hj
      · rw [Lo r hrp] at hr hne ⊢
        exact hI.k2 q r hq hr hne j hj
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.idle q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.annU q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.annSub q hq
  · intro q hq j hj
    by_cases hqp : q = p
    · subst hqp; rw [hpref]; rw [Lp] at hj; simpa using hj
    · rw [Lo q hqp] at hq hj ⊢; exact hI.chkSub q hq j hj


/-- Step T5: `p` reads `1` from a register of `R preference`. -/
lemma inv_T5 {C C' : Cfg P V ι} {p : P} {i : ι} {rest : List ι} (hI : Inv W R C)
    (hpc : (C.loc p).pc = .chk) (ht : (C.loc p).todo = i :: rest) (hb : C.mem (some i) = true)
    (hpend : C'.pend = C.pend)
    (hl : C'.loc = Function.update C.loc p { C.loc p with pc := .fin })
    (hm : C'.mem = C.mem) : Inv W R C' := by
  have L := loc_upd hl
  have Lp : C'.loc p = { C.loc p with pc := .fin } := by simp [L]
  have Lo : ∀ q, q ≠ p → C'.loc q = C.loc q := by intro q hq; simp [L, hq]
  have postP : Post (C.loc p) := by simp [Post, hpc]
  have rdP : Rd (C.loc p) := postP.rd
  have hpref : (C'.loc p).pref = (C.loc p).pref := by rw [Lp]; simp [Loc.pref]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q; rw [hpend]
    by_cases hqp : q = p
    · subst hqp; rw [Lp]
      have := hI.pend q; simp only [hpc] at this; simpa using this
    · rw [Lo q hqp]; exact hI.pend q
  · intro q hq j hj hjt
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq hj hjt; rw [hm]; exact hI.ann q hq j hj hjt
  · intro q hq j hj
    rw [hm]
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hj; exact hI.g1 q rdP j hj
    · rw [Lo q hqp] at hq hj; exact hI.g1 q hq j hj
  · intro q hq; rw [hm]
    by_cases hqp : q = p
    · subst hqp; exact hI.g4 q postP
    · rw [Lo q hqp] at hq; exact hI.g4 q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.wprop q hq
  · intro x hx; rw [hm] at hx
    obtain ⟨q, h1, h2, h3⟩ := hI.g5 x hx
    by_cases hqp : q = p
    · subst hqp; exact ⟨q, by rw [Lp]; simp [Post], by rw [Lp]; exact h2, by rw [Lp]; exact h3⟩
    · exact ⟨q, by rw [Lo q hqp]; exact h1, by rw [Lo q hqp]; exact h2, by rw [Lo q hqp]; exact h3⟩
  · intro q x hx
    have hx' : (C.loc q).u = some x := by
      by_cases hqp : q = p
      · subst hqp; rw [Lp] at hx; exact hx
      · rw [Lo q hqp] at hx; exact hx
    obtain ⟨q', h1, h2, h3⟩ := hI.g6 q x hx'
    by_cases hqp' : q' = p
    · subst hqp'; exact ⟨q', by rw [Lp]; simp [Post], by rw [Lp]; exact h2, by rw [Lp]; exact h3⟩
    · exact ⟨q', by rw [Lo q' hqp']; exact h1, by rw [Lo q' hqp']; exact h2,
        by rw [Lo q' hqp']; exact h3⟩
  · intro j hj; rw [hm] at hj
    obtain ⟨q, h1, h2⟩ := hI.g8 j hj
    by_cases hqp : q = p
    · subst hqp; exact ⟨q, by rw [Lp]; simp, by rw [Lp]; exact h2⟩
    · exact ⟨q, by rw [Lo q hqp]; exact h1, by rw [Lo q hqp]; exact h2⟩
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [hpref, hm]
      exact ⟨i, hI.chkSub q hpc i (by simp [ht]), hb⟩
    · rw [Lo q hqp] at hq ⊢; rw [hm]; exact hI.fin q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.doneT q hq
  · intro q hq j hj
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [Clean] at hq
    · rw [Lo q hqp] at hq hj ⊢; exact hI.k1 q hq j hj
  · intro q r hq hr hne j hj
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [Clean] at hq
    · rw [Lo q hqp] at hq hj hne
      by_cases hrp : r = p
      · subst hrp
        have hr0 : ReadBot (C.loc r) := by
          rw [Lp] at hr; exact ⟨rdP, hr.2⟩
        rw [Lp] at hne ⊢
        exact hI.k2 q r hq hr0 hne j hj
      · rw [Lo r hrp] at hr hne ⊢
        exact hI.k2 q r hq hr hne j hj
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.idle q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.annU q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.annSub q hq
  · intro q hq j hj
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq hj ⊢; exact hI.chkSub q hq j hj

/-- Step T6: `p` reads `0` from a register of `R preference`. -/
lemma inv_T6 {C C' : Cfg P V ι} {p : P} {i : ι} {rest : List ι} (hI : Inv W R C)
    (hpc : (C.loc p).pc = .chk) (ht : (C.loc p).todo = i :: rest) (hb : C.mem (some i) = false)
    (hpend : C'.pend = C.pend)
    (hl : C'.loc = Function.update C.loc p { C.loc p with todo := rest })
    (hm : C'.mem = C.mem) : Inv W R C' := by
  have L := loc_upd hl
  have Lp : C'.loc p = { C.loc p with todo := rest } := by simp [L]
  have Lo : ∀ q, q ≠ p → C'.loc q = C.loc q := by intro q hq; simp [L, hq]
  have postP : Post (C.loc p) := by simp [Post, hpc]
  have rdP : Rd (C.loc p) := postP.rd
  have hpref : (C'.loc p).pref = (C.loc p).pref := by rw [Lp]; simp [Loc.pref]
  have cleanP : Clean (C.loc p) := Or.inl hpc
  -- the registers seen by `p` after the step: the old ones and `i`
  have seenP : ∀ j, Seen R (C'.loc p) j → j = i ∨ Seen R (C.loc p) j := by
    intro j hj
    rw [Seen, hpref, Lp] at hj
    by_cases hji : j = i
    · exact Or.inl hji
    · refine Or.inr ⟨hj.1, ?_⟩
      rw [ht]; simp only [List.mem_cons, not_or]; exact ⟨hji, hj.2⟩
  -- a process that read `⊥` has written its whole write quorum, so `i` is not in it
  have notW : ∀ q, Rd (C.loc q) → i ∉ W (C.loc q).inp := by
    intro q hq hi; have := hI.g1 q hq i hi; rw [hb] at this; exact Bool.false_ne_true this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q; rw [hpend]
    by_cases hqp : q = p
    · subst hqp; rw [Lp]
      exact hI.pend q
    · rw [Lo q hqp]; exact hI.pend q
  · intro q hq j hj hjt
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [hpc] at hq
    · rw [Lo q hqp] at hq hj hjt; rw [hm]; exact hI.ann q hq j hj hjt
  · intro q hq j hj
    rw [hm]
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hj; exact hI.g1 q rdP j hj
    · rw [Lo q hqp] at hq hj; exact hI.g1 q hq j hj
  · intro q hq; rw [hm]
    by_cases hqp : q = p
    · subst hqp; exact hI.g4 q postP
    · rw [Lo q hqp] at hq; exact hI.g4 q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [hpc] at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.wprop q hq
  · intro x hx; rw [hm] at hx
    obtain ⟨q, h1, h2, h3⟩ := hI.g5 x hx
    by_cases hqp : q = p
    · subst hqp; exact ⟨q, by rw [Lp]; exact h1, by rw [Lp]; exact h2, by rw [Lp]; exact h3⟩
    · exact ⟨q, by rw [Lo q hqp]; exact h1, by rw [Lo q hqp]; exact h2, by rw [Lo q hqp]; exact h3⟩
  · intro q x hx
    have hx' : (C.loc q).u = some x := by
      by_cases hqp : q = p
      · subst hqp; rw [Lp] at hx; exact hx
      · rw [Lo q hqp] at hx; exact hx
    obtain ⟨q', h1, h2, h3⟩ := hI.g6 q x hx'
    by_cases hqp' : q' = p
    · subst hqp'; exact ⟨q', by rw [Lp]; exact h1, by rw [Lp]; exact h2, by rw [Lp]; exact h3⟩
    · exact ⟨q', by rw [Lo q' hqp']; exact h1, by rw [Lo q' hqp']; exact h2,
        by rw [Lo q' hqp']; exact h3⟩
  · intro j hj; rw [hm] at hj
    obtain ⟨q, h1, h2⟩ := hI.g8 j hj
    by_cases hqp : q = p
    · subst hqp; exact ⟨q, by rw [Lp]; exact h1, by rw [Lp]; exact h2⟩
    · exact ⟨q, by rw [Lo q hqp]; exact h1, by rw [Lo q hqp]; exact h2⟩
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [hpc] at hq
    · rw [Lo q hqp] at hq ⊢; rw [hm]; exact hI.fin q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [hpc] at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.doneT q hq
  · intro q hq j hj
    by_cases hqp : q = p
    · subst hqp
      rw [Lp]
      rcases seenP j hj with rfl | hj'
      · exact notW q rdP
      · exact hI.k1 q cleanP j hj'
    · rw [Lo q hqp] at hq hj ⊢; exact hI.k1 q hq j hj
  · intro q r hq hr hne j hj
    have hr' : ReadBot (C.loc r) := by
      by_cases hrp : r = p
      · subst hrp; rw [Lp] at hr; exact hr
      · rw [Lo r hrp] at hr; exact hr
    have hinp : (C'.loc r).inp = (C.loc r).inp := by
      by_cases hrp : r = p
      · subst hrp; rw [Lp]
      · rw [Lo r hrp]
    rw [hinp] at hne ⊢
    by_cases hqp : q = p
    · subst hqp
      rw [hpref] at hne
      rcases seenP j hj with rfl | hj'
      · exact notW r hr'.1
      · exact hI.k2 q r cleanP hr' hne j hj'
    · rw [Lo q hqp] at hq hj hne
      exact hI.k2 q r hq hr' hne j hj
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [hpc] at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.idle q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [hpc] at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.annU q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [hpc] at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.annSub q hq
  · intro q hq j hj
    by_cases hqp : q = p
    · subst hqp; rw [hpref]; rw [Lp] at hj
      exact hI.chkSub q hpc j (by rw [ht]; exact List.mem_cons_of_mem _ hj)
    · rw [Lo q hqp] at hq hj ⊢; exact hI.chkSub q hq j hj


/-- The shape of a response step (given the invariant). -/
lemma step_ret_cases {C C' : Cfg P V ι} {p : P} {r : Decision × V} (hI : Inv W R C)
    (h : (acImpl P W R).step C (.ret p r) = some C') :
    C'.pend = Function.update C.pend p none ∧ C'.mem = C.mem ∧
    (((C.loc p).pc = .chk ∧ (C.loc p).todo = [] ∧ r = (.commit, (C.loc p).pref) ∧
        C'.loc = Function.update C.loc p { C.loc p with pc := .done, dec := .commit }) ∨
     ((C.loc p).pc = .fin ∧ r = (.adopt, (C.loc p).pref) ∧
        C'.loc = Function.update C.loc p { C.loc p with pc := .done, dec := .adopt })) := by
  obtain ⟨hp, hpend, hm, l, hact, hl⟩ := Impl.step_ret h
  refine ⟨hpend, hm, ?_⟩
  have hpc := (hI.pend p).not.1 hp
  rcases hlp : C.loc p with ⟨pc, inp, u, todo, dec⟩
  rw [hlp] at hact hpc
  cases pc <;> simp [acImpl] at hact hpc
  · cases todo <;> simp at hact
  · cases todo with
    | nil =>
      simp only [Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      exact Or.inl ⟨rfl, rfl, rfl, by rw [hl]⟩
    | cons i rest => simp at hact
  · obtain ⟨rfl, rfl⟩ := hact
    exact Or.inr ⟨rfl, rfl, by rw [hl]⟩

/-- A response step preserves the invariant. -/
lemma inv_ret {C C' : Cfg P V ι} {p : P} {r : Decision × V} (hI : Inv W R C)
    (h : (acImpl P W R).step C (.ret p r) = some C') : Inv W R C' := by
  obtain ⟨hpend, hm, hcase⟩ := step_ret_cases hI h
  -- in both cases, `p` moves to `done` keeping `inp`, `u`, `todo`
  obtain ⟨d, hpc, hl, hd⟩ : ∃ d, ((C.loc p).pc = .chk ∨ (C.loc p).pc = .fin) ∧
      C'.loc = Function.update C.loc p { C.loc p with pc := .done, dec := d } ∧
      (d = .commit → (C.loc p).pc = .chk ∧ (C.loc p).todo = []) ∧
      (d = .adopt → (C.loc p).pc = .fin) := by
    rcases hcase with ⟨h1, h2, -, h4⟩ | ⟨h1, -, h3⟩
    · exact ⟨.commit, Or.inl h1, h4, fun _ => ⟨h1, h2⟩, by simp⟩
    · exact ⟨.adopt, Or.inr h1, h3, by simp, fun _ => h1⟩
  have L := loc_upd hl
  have Lp : C'.loc p = { C.loc p with pc := .done, dec := d } := by simp [L]
  have Lo : ∀ q, q ≠ p → C'.loc q = C.loc q := by intro q hq; simp [L, hq]
  have postP : Post (C.loc p) := by rcases hpc with h | h <;> simp [Post, h]
  have rdP : Rd (C.loc p) := postP.rd
  have hpref : (C'.loc p).pref = (C.loc p).pref := by rw [Lp]; simp [Loc.pref]
  have notW : ¬ ((C.loc p).pc = .wprop) := by rcases hpc with h | h <;> simp [h]
  have notA : ¬ ((C.loc p).pc = .ann) := by rcases hpc with h | h <;> simp [h]
  have notI : ¬ ((C.loc p).pc = .idle) := by rcases hpc with h | h <;> simp [h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q; rw [hpend]
    by_cases hqp : q = p
    · subst hqp; rw [Lp]; simp
    · rw [Lo q hqp, Function.update_of_ne hqp]; exact hI.pend q
  · intro q hq j hj hjt
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq hj hjt; rw [hm]; exact hI.ann q hq j hj hjt
  · intro q hq j hj
    rw [hm]
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hj; exact hI.g1 q rdP j hj
    · rw [Lo q hqp] at hq hj; exact hI.g1 q hq j hj
  · intro q hq; rw [hm]
    by_cases hqp : q = p
    · subst hqp; exact hI.g4 q postP
    · rw [Lo q hqp] at hq; exact hI.g4 q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.wprop q hq
  · intro x hx; rw [hm] at hx
    obtain ⟨q, h1, h2, h3⟩ := hI.g5 x hx
    by_cases hqp : q = p
    · subst hqp; exact ⟨q, by rw [Lp]; simp [Post], by rw [Lp]; exact h2, by rw [Lp]; exact h3⟩
    · exact ⟨q, by rw [Lo q hqp]; exact h1, by rw [Lo q hqp]; exact h2, by rw [Lo q hqp]; exact h3⟩
  · intro q x hx
    have hx' : (C.loc q).u = some x := by
      by_cases hqp : q = p
      · subst hqp; rw [Lp] at hx; exact hx
      · rw [Lo q hqp] at hx; exact hx
    obtain ⟨q', h1, h2, h3⟩ := hI.g6 q x hx'
    by_cases hqp' : q' = p
    · subst hqp'; exact ⟨q', by rw [Lp]; simp [Post], by rw [Lp]; exact h2, by rw [Lp]; exact h3⟩
    · exact ⟨q', by rw [Lo q' hqp']; exact h1, by rw [Lo q' hqp']; exact h2,
        by rw [Lo q' hqp']; exact h3⟩
  · intro j hj; rw [hm] at hj
    obtain ⟨q, h1, h2⟩ := hI.g8 j hj
    by_cases hqp : q = p
    · subst hqp; exact ⟨q, by rw [Lp]; simp, by rw [Lp]; exact h2⟩
    · exact ⟨q, by rw [Lo q hqp]; exact h1, by rw [Lo q hqp]; exact h2⟩
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [hpref, hm]
      rw [Lp] at hq
      have hfin : (C.loc q).pc = .fin := by
        rcases hq with h | ⟨-, h⟩
        · simp at h
        · exact hd.2 (by simpa using h)
      exact hI.fin q (Or.inl hfin)
    · rw [Lo q hqp] at hq ⊢; rw [hm]; exact hI.fin q hq
  · intro q hq hdc
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hdc ⊢; exact (hd.1 (by simpa using hdc)).2
    · rw [Lo q hqp] at hq hdc ⊢; exact hI.doneT q hq hdc
  · intro q hq j hj
    by_cases hqp : q = p
    · subst hqp
      rw [Lp] at hq hj ⊢
      have hc : d = .commit := by rcases hq with h | ⟨-, h⟩ <;> simp_all
      exact hI.k1 q (Or.inl (hd.1 hc).1) j hj
    · rw [Lo q hqp] at hq hj ⊢; exact hI.k1 q hq j hj
  · intro q r hq hr hne j hj
    have hr' : ReadBot (C.loc r) := by
      by_cases hrp : r = p
      · subst hrp; rw [Lp] at hr; exact ⟨rdP, hr.2⟩
      · rw [Lo r hrp] at hr; exact hr
    have hinp : (C'.loc r).inp = (C.loc r).inp := by
      by_cases hrp : r = p
      · subst hrp; rw [Lp]
      · rw [Lo r hrp]
    rw [hinp] at hne ⊢
    by_cases hqp : q = p
    · subst hqp
      rw [Lp] at hq hj hne
      have hc : d = .commit := by rcases hq with h | ⟨-, h⟩ <;> simp_all
      exact hI.k2 q r (Or.inl (hd.1 hc).1) hr' hne j hj
    · rw [Lo q hqp] at hq hj hne
      exact hI.k2 q r hq hr' hne j hj
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.idle q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.annU q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.annSub q hq
  · intro q hq j hj
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq hj ⊢; exact hI.chkSub q hq j hj

/-- An invocation by an idle process preserves the invariant. -/
lemma inv_inv {C C' : Cfg P V ι} {p : P} {v : V} (hI : Inv W R C)
    (hidle : (C.loc p).pc = .idle)
    (h : (acImpl P W R).step C (.inv p v) = some C') : Inv W R C' := by
  obtain ⟨-, -, hpend, hl, hm⟩ := Impl.step_inv h
  have L := loc_upd hl
  have Lp : C'.loc p = ⟨.ann, v, none, (W v).toList, .adopt⟩ := by simp [L, acImpl]
  have Lo : ∀ q, q ≠ p → C'.loc q = C.loc q := by intro q hq; simp [L, hq]
  have neP : ∀ q, (C.loc q).pc ≠ .idle → q ≠ p := by
    intro q hq' hqp; subst hqp; exact hq' hidle
  have nePost : ∀ q, Post (C.loc q) → q ≠ p := by
    intro q hq' hqp; subst hqp; rcases hq' with h1 | h1 | h1 <;> simp [h1] at hidle
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q; rw [hpend]
    by_cases hqp : q = p
    · subst hqp; rw [Lp]; simp
    · rw [Lo q hqp, Function.update_of_ne hqp]; exact hI.pend q
  · intro q hq j hj hjt
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hj hjt; simp at hjt; exact absurd hj hjt
    · rw [Lo q hqp] at hq hj hjt; rw [hm]; exact hI.ann q hq j hj hjt
  · intro q hq j hj
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [Rd] at hq
    · rw [Lo q hqp] at hq hj; rw [hm]; exact hI.g1 q hq j hj
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [Post] at hq
    · rw [Lo q hqp] at hq; rw [hm]; exact hI.g4 q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.wprop q hq
  · intro x hx; rw [hm] at hx
    obtain ⟨q, h1, h2, h3⟩ := hI.g5 x hx
    have hqp := nePost q h1
    exact ⟨q, by rw [Lo q hqp]; exact h1, by rw [Lo q hqp]; exact h2, by rw [Lo q hqp]; exact h3⟩
  · intro q x hx
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hx; simp at hx
    · rw [Lo q hqp] at hx
      obtain ⟨q', h1, h2, h3⟩ := hI.g6 q x hx
      have hqp' := nePost q' h1
      exact ⟨q', by rw [Lo q' hqp']; exact h1, by rw [Lo q' hqp']; exact h2,
        by rw [Lo q' hqp']; exact h3⟩
  · intro j hj; rw [hm] at hj
    obtain ⟨q, h1, h2⟩ := hI.g8 j hj
    have hqp := neP q h1
    exact ⟨q, by rw [Lo q hqp]; exact h1, by rw [Lo q hqp]; exact h2⟩
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; rw [hm]; exact hI.fin q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.doneT q hq
  · intro q hq j hj
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [Clean] at hq
    · rw [Lo q hqp] at hq hj ⊢; exact hI.k1 q hq j hj
  · intro q r hq hr hne j hj
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp [Clean] at hq
    · by_cases hrp : r = p
      · subst hrp; rw [Lp] at hr; simp [ReadBot, Rd] at hr
      · rw [Lo q hqp] at hq hj hne; rw [Lo r hrp] at hr hne ⊢
        exact hI.k2 q r hq hr hne j hj
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.idle q hq
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp]
    · rw [Lo q hqp] at hq ⊢; exact hI.annU q hq
  · intro q hq j hj
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hj ⊢; simpa using hj
    · rw [Lo q hqp] at hq hj ⊢; exact hI.annSub q hq j hj
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [Lp] at hq; simp at hq
    · rw [Lo q hqp] at hq ⊢; exact hI.chkSub q hq

/-- An internal step preserves the invariant. -/
lemma inv_tau {C C' : Cfg P V ι} {p : P} (hI : Inv W R C)
    (h : (acImpl P W R).step C (.tau p) = some C') : Inv W R C' := by
  obtain ⟨hpend, hc⟩ := step_tau_cases h
  rcases hc with ⟨i, rest, h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨y, h1, h2, h3, h4, h5⟩ |
    ⟨h1, h2, h3⟩ | ⟨i, rest, h1, h2, h3, h4, h5⟩ | ⟨i, rest, h1, h2, h3, h4, h5⟩
  · exact inv_T1 hI h1 h2 hpend h3 h4
  · exact inv_T2 hI h1 h2 h3 hpend h4 h5
  · exact inv_T3 hI h1 h2 h3 hpend h4 h5
  · exact inv_T4 hI h1 hpend h2 h3
  · exact inv_T5 hI h1 h2 h3 hpend h4 h5
  · exact inv_T6 hI h1 h2 h3 hpend h4 h5

end Invariant

/-! ### Inputs, outputs and the main theorem -/

section Main

variable {P : Type} [DecidableEq P] {W R : V → Finset ι}

/-- An internal step keeps the input and leaves `p` running. -/
lemma step_tau_loc {C C' : Cfg P V ι} {p : P} (h : (acImpl P W R).step C (.tau p) = some C') :
    (C'.loc p).inp = (C.loc p).inp ∧ (C.loc p).pc ≠ .idle ∧ (C.loc p).pc ≠ .done ∧
      (C'.loc p).pc ≠ .idle ∧ (C'.loc p).pc ≠ .done := by
  obtain ⟨-, hc⟩ := step_tau_cases h
  rcases hc with ⟨i, rest, h1, -, h3, -⟩ | ⟨h1, -, -, h3, -⟩ | ⟨y, h1, -, -, h3, -⟩ |
    ⟨h1, h3, -⟩ | ⟨i, rest, h1, -, -, h3, -⟩ | ⟨i, rest, h1, -, -, h3, -⟩ <;>
    simp [h3, h1]

/-- The bookkeeping relating the local states to the inputs and outputs of the execution. -/
def Book (α : List (Label P (acObj V))) (C : Cfg P V ι) : Prop :=
  (∀ q, (C.loc q).pc = .idle ↔ opsOf α q = []) ∧
  (∀ q, (C.loc q).pc ≠ .idle → inputs α q = some (C.loc q).inp) ∧
  (∀ q, outputs α q =
    if (C.loc q).pc = .done then some ((C.loc q).dec, (C.loc q).pref) else none)

/-- The invariant and the bookkeeping hold after every one-shot execution. -/
theorem inv_of_run {α : List (Label P (acObj V))} {C : Cfg P V ι}
    (h : (acImpl P W R).run α = some C) (hos : OneShot α) : Inv W R C ∧ Book α C := by
  refine Impl.run_induction (Q := fun α C => OneShot α → Inv W R C ∧ Book α C)
    ?_ ?_ h hos
  · intro _
    refine ⟨inv_init, ?_, ?_, ?_⟩
    · intro q; simp [Impl.initCfg, acImpl]
    · intro q hq; simp [Impl.initCfg, acImpl] at hq
    · intro q; simp [Impl.initCfg, acImpl, outputs]
  · intro α C ℓ C' _ ih hs hos'
    obtain ⟨hI, hb1, hb2, hb3⟩ := ih hos'.of_append
    cases ℓ with
    | inv p v =>
      have hops : opsOf α p = [] := by
        have := hos' p
        simp only [opsOf_concat, Label.invOf_inv, ↓reduceIte, Option.toList_some,
          List.length_append, List.length_singleton] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      have hidle : (C.loc p).pc = .idle := (hb1 p).2 hops
      refine ⟨inv_inv hI hidle hs, ?_, ?_, ?_⟩ <;>
        obtain ⟨-, -, -, hl, -⟩ := Impl.step_inv hs
      · intro q
        rw [loc_upd hl, opsOf_concat]
        by_cases hqp : q = p
        · subst hqp; simp [acImpl]
        · simp [hqp, Ne.symm hqp, hb1 q]
      · intro q hq
        rw [loc_upd hl] at hq ⊢
        by_cases hqp : q = p
        · subst hqp; simp [inputs, opsOf_concat, hops, acImpl]
        · simp only [hqp, ↓reduceIte] at hq ⊢
          rw [inputs_append_of_ne_none _ (by rw [hb2 q hq]; simp), hb2 q hq]
      · intro q
        rw [loc_upd hl, outputs_append_inv, hb3 q]
        by_cases hqp : q = p
        · subst hqp; simp [hidle, acImpl]
        · simp [hqp]
    | tau p =>
      refine ⟨inv_tau hI hs, ?_, ?_, ?_⟩
      · intro q
        rw [opsOf_append_tau]
        by_cases hqp : q = p
        · subst hqp
          obtain ⟨-, h2, -, h4, -⟩ := step_tau_loc hs
          rw [← hb1 q]; simp [h2, h4]
        · rw [(Impl.step_other hs (by simpa [Label.proc] using Ne.symm hqp)).1]; exact hb1 q
      · intro q hq
        have : inputs (α ++ [.tau p]) q = inputs α q := by simp [inputs, opsOf_append_tau]
        rw [this]
        by_cases hqp : q = p
        · subst hqp
          obtain ⟨h1, h2, -, -, -⟩ := step_tau_loc hs
          rw [h1]; exact hb2 q h2
        · rw [(Impl.step_other hs (by simpa [Label.proc] using Ne.symm hqp)).1] at hq ⊢
          exact hb2 q hq
      · intro q
        rw [outputs_append_tau, hb3 q]
        by_cases hqp : q = p
        · subst hqp
          obtain ⟨-, -, h3, -, h5⟩ := step_tau_loc hs
          simp [h3, h5]
        · rw [(Impl.step_other hs (by simpa [Label.proc] using Ne.symm hqp)).1]
    | ret p r =>
      refine ⟨inv_ret hI hs, ?_, ?_, ?_⟩ <;>
        obtain ⟨hpend, -, hcase⟩ := step_ret_cases hI hs
      all_goals
        obtain ⟨d, hpc, hl, hr⟩ : ∃ d, ((C.loc p).pc = .chk ∨ (C.loc p).pc = .fin) ∧
            C'.loc = Function.update C.loc p { C.loc p with pc := .done, dec := d } ∧
            r = (d, (C.loc p).pref) := by
          rcases hcase with ⟨h1, -, h3, h4⟩ | ⟨h1, h3, h4⟩
          · exact ⟨.commit, Or.inl h1, h4, h3⟩
          · exact ⟨.adopt, Or.inr h1, h4, h3⟩
      · intro q
        rw [opsOf_append_ret, loc_upd hl]
        by_cases hqp : q = p
        · subst hqp; rw [← hb1 q]; rcases hpc with h | h <;> simp [h]
        · simp [hqp, hb1 q]
      · intro q hq
        have : inputs (α ++ [.ret p r]) q = inputs α q := by simp [inputs, opsOf_append_ret]
        rw [this]
        rw [loc_upd hl] at hq ⊢
        by_cases hqp : q = p
        · subst hqp; simp only [↓reduceIte]
          exact hb2 q (by rcases hpc with h | h <;> simp [h])
        · simp only [hqp, ↓reduceIte] at hq ⊢; exact hb2 q hq
      · intro q
        rw [loc_upd hl]
        by_cases hqp : q = p
        · subst hqp
          rw [outputs_concat, hb3 q]
          have : (C.loc q).pc ≠ .done := by rcases hpc with h | h <;> simp [h]
          simp [this, hr, Loc.pref]
        · rw [outputs_concat_of_ne (by intro r' h; cases h; exact hqp rfl), hb3 q]
          simp [hqp]

/-- If `p` has committed `v`, every process that has read `⊥` from `proposal` has input `v`. -/
lemma readBot_inp {C : Cfg P V ι} (hI : Inv W R C)
    (hWR : ∀ v v', Disjoint (W v) (R v') ↔ v = v') {p : P}
    (hp : (C.loc p).pc = .done) (hd : (C.loc p).dec = .commit) {q : P}
    (hq : ReadBot (C.loc q)) : (C.loc q).inp = (C.loc p).pref := by
  by_contra hne
  have ht := hI.doneT p hp hd
  have hdisj : Disjoint (W (C.loc q).inp) (R (C.loc p).pref) := by
    rw [Finset.disjoint_left]
    intro i hiW hiR
    exact hI.k2 p q (Or.inr ⟨hp, hd⟩) hq hne i ⟨hiR, by simp [ht]⟩ hiW
  exact hne ((hWR _ _).1 hdisj)

/-- The preference of a process that read `proposal` is the input of a process that read `⊥`
(or its own input). -/
lemma pref_eq {C : Cfg P V ι} (hI : Inv W R C) {q : P} (hq : Rd (C.loc q)) :
    ∃ q', ReadBot (C.loc q') ∧ (C.loc q').inp = (C.loc q).pref := by
  rcases hu : (C.loc q).u with _ | x
  · exact ⟨q, ⟨hq, hu⟩, by simp [Loc.pref, hu]⟩
  · obtain ⟨q', h1, h2, h3⟩ := hI.g6 q x hu
    exact ⟨q', ⟨h1.rd, h2⟩, by simp [Loc.pref, hu, h3]⟩

/-- **Theorem 8.** Let `W v ∩ R v' = ∅` if and only if `v = v'`. Then Procedure AdoptCommit
satisfies validity, coherence and convergence (in every finite, possibly partial, one-shot
execution, for any number of processes and any schedule). -/
theorem theorem8_safety (hWR : ∀ v v', Disjoint (W v) (R v') ↔ v = v')
    (α : List (Label P (acObj V))) (hα : (acImpl P W R).Valid α) (hos : OneShot α) :
    Validity (inputs α) (outputs α) ∧ Coherence (outputs α) ∧
      Convergence (inputs α) (outputs α) := by
  obtain ⟨C, hC⟩ := hα
  obtain ⟨hI, hb1, hb2, hb3⟩ := inv_of_run hC hos
  have hout : ∀ q d w, outputs α q = some (d, w) →
      (C.loc q).pc = .done ∧ (C.loc q).dec = d ∧ (C.loc q).pref = w := by
    intro q d w h
    rw [hb3 q] at h
    split_ifs at h with h1
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨h1, h.1, h.2⟩
  have hrd : ∀ q, (C.loc q).pc = .done → Rd (C.loc q) := fun q h => by simp [Rd, h]
  -- validity: the output value is the input of some process
  have hval : ∀ q d w, outputs α q = some (d, w) → ∃ q', inputs α q' = some w := by
    intro q d w h
    obtain ⟨h1, -, h3⟩ := hout q d w h
    obtain ⟨q', hq', hinp⟩ := pref_eq hI (hrd q h1)
    refine ⟨q', ?_⟩
    rw [hb2 q', hinp, h3]
    rcases hq'.1 with h | h | h | h <;> simp [h]
  refine ⟨hval, ?_, ?_⟩
  · -- coherence
    intro p q v d w hp hq
    obtain ⟨hp1, hp2, hp3⟩ := hout p .commit v hp
    obtain ⟨hq1, -, hq3⟩ := hout q d w hq
    obtain ⟨q', hq', hinp⟩ := pref_eq hI (hrd q hq1)
    rw [← hq3, ← hinp, readBot_inp hI hWR hp1 hp2 hq', hp3]
  · -- convergence
    intro v hall q d w hq
    obtain ⟨q', hq'⟩ := hval q d w hq
    have hw : w = v := hall q' w hq'
    refine ⟨?_, hw⟩
    obtain ⟨hq1, hq2, hq3⟩ := hout q d w hq
    cases d with
    | commit => rfl
    | adopt =>
      exfalso
      obtain ⟨i, hiR, hi⟩ := hI.fin q (Or.inr ⟨hq1, hq2⟩)
      obtain ⟨q'', h1, h2⟩ := hI.g8 i hi
      have hin : (C.loc q'').inp = v := hall q'' _ (hb2 q'' h1)
      rw [hq3, hw, ← hin] at hiR
      exact Finset.disjoint_left.1 ((hWR _ _).2 rfl) h2 hiR

/-- **Theorem 8** (safety, as a CSLib task): Procedure AdoptCommit solves the adopt-commit task. -/
theorem theorem8_solves (hWR : ∀ v v', Disjoint (W v) (R v') ↔ v = v') :
    (acImpl P W R).Solves (adoptCommitTask P V) :=
  fun α hα hos => theorem8_safety hWR α hα hos

/-- A process can only commit its own input (remark in the proof of Theorem 8). -/
theorem commit_eq_input (hWR : ∀ v v', Disjoint (W v) (R v') ↔ v = v')
    {α : List (Label P (acObj V))} (hα : (acImpl P W R).Valid α) (hos : OneShot α) {p : P}
    {v : V} (h : outputs α p = some (.commit, v)) : inputs α p = some v := by
  obtain ⟨C, hC⟩ := hα
  obtain ⟨hI, -, hb2, hb3⟩ := inv_of_run hC hos
  rw [hb3 p] at h
  split_ifs at h with h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨h2, h3⟩ := h
  have ht := hI.doneT p h1 h2
  have hdisj : Disjoint (W (C.loc p).inp) (R (C.loc p).pref) := by
    rw [Finset.disjoint_left]
    intro i hiW hiR
    exact hI.k1 p (Or.inr ⟨h1, h2⟩) i ⟨hiR, by simp [ht]⟩ hiW
  rw [hb2 p (by simp [h1]), ← h3, (hWR _ _).1 hdisj]

/-! ### Termination and individual work -/

/-- The potential: an upper bound on the remaining register operations of a process, when all
read quorums have at most `ρ` registers. -/
def μ (ρ : ℕ) (_ : P) (l : Loc V ι) : ℕ :=
  match l.pc with
  | .ann => l.todo.length + 2 + ρ
  | .wprop => 1 + ρ
  | .chk => l.todo.length
  | _ => 0

lemma μ_access (ρ : ℕ) (hρ : ∀ v, (R v).card ≤ ρ) (p : P) (l : Loc V ι) (i : Option ι)
    (o : (Mem V ι i).Op) (k : (Mem V ι i).Resp → Loc V ι)
    (h : (acImpl P W R).act p l = .access i o k) (x : (Mem V ι i).Resp) :
    μ ρ p (k x) < μ ρ p l := by
  rcases l with ⟨pc, inp, u, todo, dec⟩
  cases pc with
  | idle => simp [acImpl] at h
  | fin => simp [acImpl] at h
  | done => simp [acImpl] at h
  | ann =>
    cases todo with
    | cons j rest =>
      simp only [acImpl, Action.access.injEq] at h
      obtain ⟨rfl, -, hk⟩ := h
      subst hk; simp [μ]
    | nil =>
      simp only [acImpl, Action.access.injEq] at h
      obtain ⟨rfl, -, hk⟩ := h
      subst hk
      rcases x with _ | y
      · simp [μ]
      · simp only [μ, List.length_nil, Finset.length_toList]
        have := hρ y; omega
  | wprop =>
    simp only [acImpl, Action.access.injEq] at h
    obtain ⟨rfl, -, hk⟩ := h
    subst hk
    simp only [μ, Finset.length_toList]
    have := hρ inp; omega
  | chk =>
    cases todo with
    | cons j rest =>
      simp only [acImpl, Action.access.injEq] at h
      obtain ⟨rfl, -, hk⟩ := h
      subst hk
      cases x <;> simp [μ]
    | nil => simp [acImpl] at h

/-- **Theorem 8** (termination). If all read quorums have at most `ρ` registers (e.g. finitely
many values), Procedure AdoptCommit is wait-free. -/
theorem theorem8_waitFree (ρ : ℕ) (hρ : ∀ v, (R v).card ≤ ρ) : (acImpl P W R).WaitFree :=
  Impl.waitFree_of_potential _ (μ ρ) (μ_access ρ hρ)

/-- **Individual work.** After invoking `AdoptCommit(v)`, a process performs at most
`|W v| + 2 + ρ` register operations before it returns, where `ρ` bounds the sizes of the read
quorums (`|W v|` writes, one read and possibly one write of `proposal`, at most `ρ` reads). -/
theorem steps_le (ρ : ℕ) (hρ : ∀ v, (R v).card ≤ ρ) {α γ : List (Label P (acObj V))} {p : P}
    {v : V} (hv : (acImpl P W R).Valid (α ++ .inv p v :: γ)) (hret : ∀ r, .ret p r ∉ γ) :
    γ.countP (Label.isTauOf p) ≤ (W v).card + 2 + ρ := by
  obtain ⟨l, hl⟩ := Impl.tauSteps_le_potential_invoke _ (μ ρ) (μ_access ρ hρ) hv hret
  simpa [μ, acImpl] using hl

end Main

end Podc.ModularConsensus.AC
