-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/ConflictFreedom.lean
-- (progress conditions `ConflictFree`, `WeakConflictFree`, Propositions 3.3–3.4)
import Cslib.Computability.Distributed.SharedMemory.Progress
import Podc.Foundations.Data.Mazurkiewicz.Defs

/-!
# Conflict-freedom and weak conflict-freedom (Section 3)

Kuznetsov, Sutra and Toyos-Marfurt, *Conflict-Freedom as a Progress Condition*, PODC 2026.

We work in CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`: deterministic
processes, atomic base objects, executions as label sequences, any number of crashes) and state
the progress conditions of the paper over its infinite executions (`Impl.InfExec`):

* `ObjSpec.Conflicting A a b`: `a ≍ b`, the operations do not commute in some state;
* `Correct e p`: `p` takes infinitely many steps or eventually has no pending operation;
* `PendingFrom e p n`: the operation of `p` pending at time `n` never completes;
* `SoloFrom e p τ`: from time `τ` on only `p` takes steps (step-contention-freedom);
* `EventuallyConflictFree e`: from some time on no two simultaneously pending operations of
  distinct processes conflict (two operation instances are concurrent iff they are pending at a
  common time);
* `WaitFreeP`, `LockFreeP`, `ObstructionFreeP`, `ConflictFree` (Definition 3.1),
  `WeakConflictFree` (Definition 3.2): the paper's definitions, verbatim.

Main results: Proposition 3.3 (`waitFree_conflictFree`, `conflictFree_weakConflictFree`,
`weakConflictFree_obstructionFree`, `progress_hierarchy`) and the parts of Proposition 3.4 that
hold without further assumptions (`conflictFree_iff_of_total`, `weakConflictFree_iff_of_total`,
`conflictFree_iff_of_empty`, `WeakConflictFree.lockFreeP_of_empty`). We also relate the paper's
wait-freedom and obstruction-freedom to CSLib's (`waitFreeP_iff`,
`ObstructionFreeP.obstructionFree`).
-/

namespace Podc.ConflictFreedom

open Cslib.SharedMemory Cslib.Mazurkiewicz

/-- The conflict relation `≍` of a sequential object (Section 3.1): `a ≍ b` iff `a` and `b` do
not commute in some state. -/
def _root_.Cslib.SharedMemory.ObjSpec.Conflicting (A : ObjSpec) (a b : A.Op) : Prop :=
  Conflict A.δ a b

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
  {I : Impl A B P L}

section Defs

variable (e : I.InfExec)

/-- `p` takes infinitely many steps in `e`. -/
def TakesInfSteps (p : P) : Prop := ∀ N, ∃ m ≥ N, (e.lbl m).IsStep ∧ (e.lbl m).proc = p

/-- `p` is correct in `e`: it takes infinitely many steps or eventually has no pending
operation. -/
def Correct (p : P) : Prop := TakesInfSteps e p ∨ ∃ N, ∀ m ≥ N, (e.cfg m).pend p = none

/-- The operation of `p` pending at time `n` never completes. -/
def PendingFrom (p : P) (n : ℕ) : Prop := ∀ m ≥ n, (e.cfg m).pend p ≠ none

/-- `p` completes each of its operations in `e`. -/
def CompletesAll (p : P) : Prop := ∀ n, ¬ PendingFrom e p n

/-- From time `τ` on, only `p` takes steps in `e`. -/
def SoloFrom (p : P) (τ : ℕ) : Prop := ∀ m ≥ τ, (e.lbl m).IsStep → (e.lbl m).proc = p

/-- `e` is eventually conflict-free: from some time on, no two concurrent operation instances
(of distinct processes, pending at a common time) conflict. -/
def EventuallyConflictFree : Prop :=
  ∃ τ, ∀ m ≥ τ, ∀ p q, p ≠ q → ∀ o o', (e.cfg m).pend p = some o → (e.cfg m).pend q = some o' →
    ¬ A.Conflicting o o'

end Defs

variable (I)

/-- Wait-freedom (Section 3.1): in every infinite execution, every operation invoked by a correct
process completes. -/
def WaitFreeP : Prop := ∀ (e : I.InfExec) p n, Correct e p → ¬ PendingFrom e p n

/-- Lock-freedom (Section 3.1): in every infinite execution, at least one correct process
completes each of its operations. -/
def LockFreeP : Prop := ∀ e : I.InfExec, ∃ p, Correct e p ∧ CompletesAll e p

/-- Obstruction-freedom (Section 3.1): in every infinite execution, an operation invoked by a
correct process completes whenever it is eventually step-contention-free. -/
def ObstructionFreeP : Prop :=
  ∀ (e : I.InfExec) p n, Correct e p → PendingFrom e p n → ¬ ∃ τ, SoloFrom e p τ

/-- Definition 3.1 (conflict-freedom): in every infinite execution, every operation invoked by a
correct process completes whenever the operation is eventually step-contention-free or the
execution is eventually conflict-free. -/
def ConflictFree : Prop :=
  ∀ (e : I.InfExec) p n, Correct e p → PendingFrom e p n →
    ¬ (∃ τ, SoloFrom e p τ) ∧ ¬ EventuallyConflictFree e

/-- Definition 3.2 (weak conflict-freedom): (1) in every infinite execution, every operation
invoked by a correct process completes whenever it is eventually step-contention-free, and (2)
if the execution is eventually conflict-free, then some correct process completes all of its
operations. -/
def WeakConflictFree : Prop :=
  ObstructionFreeP I ∧ ∀ e : I.InfExec, EventuallyConflictFree e → ∃ p, Correct e p ∧ CompletesAll e p

variable {I}

/-! ### Basic facts about infinite executions -/

/-- A process takes a step only while it has a pending operation. -/
lemma pend_ne_none_of_isStep (e : I.InfExec) {m : ℕ} (h : (e.lbl m).IsStep) :
    (e.cfg m).pend (e.lbl m).proc ≠ none := by
  have hs := e.step_eq m
  cases hl : e.lbl m with
  | inv q o => rw [hl] at h; exact h.elim
  | tau q => rw [hl] at hs; exact (Impl.step_tau hs).1
  | ret q r => rw [hl] at hs; exact (Impl.step_ret hs).1

/-- With finitely many processes, some process takes infinitely many steps in every infinite
execution. -/
lemma exists_takesInfSteps [Finite P] (e : I.InfExec) : ∃ p, TakesInfSteps e p := by
  have := Fintype.ofFinite P
  -- some process has infinitely many labels
  obtain ⟨p, hp⟩ : ∃ p, ∀ N, ∃ m ≥ N, (e.lbl m).proc = p := by
    by_contra hno
    push Not at hno
    choose Nf hNf using hno
    exact hNf _ (Finset.univ.sup Nf) (Finset.le_sup (Finset.mem_univ _)) rfl
  refine ⟨p, fun N => ?_⟩
  by_contra hst
  push Not at hst
  -- all labels of `p` from `N` on are invocations; two of them yield a response in between
  obtain ⟨t₁, ht₁, hp₁⟩ := hp N
  obtain ⟨t₂, ht₂, hp₂⟩ := hp (t₁ + 1)
  have hinv : ∀ t ≥ N, (e.lbl t).proc = p → ∃ o, e.lbl t = .inv p o := by
    intro t ht hpt
    cases hl : e.lbl t with
    | inv q o => rw [hl] at hpt; simp only [Label.proc] at hpt; exact ⟨o, by rw [hpt]⟩
    | tau q => exact absurd hpt (hst t ht (by rw [hl]; trivial))
    | ret q r => exact absurd hpt (hst t ht (by rw [hl]; trivial))
  obtain ⟨o₁, ho₁⟩ := hinv t₁ ht₁ hp₁
  obtain ⟨o₂, ho₂⟩ := hinv t₂ (by omega) hp₂
  have h1 : (e.cfg (t₁ + 1)).pend p ≠ none := by
    have hs := e.step_eq t₁; rw [ho₁] at hs
    rw [(Impl.step_inv hs).2.2.1]; simp
  have h2 : (e.cfg t₂).pend p = none := by
    have hs := e.step_eq t₂; rw [ho₂] at hs; exact (Impl.step_inv hs).1
  obtain ⟨t, ht, -, r, hr⟩ := e.exists_ret_between ht₂ h1 h2
  exact hst t (by omega) (by rw [hr]; trivial) (by rw [hr]; rfl)

lemma Correct.of_takesInfSteps {e : I.InfExec} {p : P} (h : TakesInfSteps e p) : Correct e p :=
  Or.inl h

/-- A correct process whose operation is pending forever takes infinitely many steps. -/
lemma Correct.takesInfSteps {e : I.InfExec} {p : P} {n : ℕ} (hc : Correct e p)
    (hp : PendingFrom e p n) : TakesInfSteps e p := by
  rcases hc with h | ⟨N, hN⟩
  · exact h
  · exact absurd (hN (max N n) (le_max_left _ _)) (hp _ (le_max_right _ _))

/-- While `p` is pending forever, its steps are internal steps. -/
lemma eq_tau_of_pendingFrom {e : I.InfExec} {p : P} {n : ℕ} (hp : PendingFrom e p n) {m : ℕ}
    (hm : n ≤ m) (hs : (e.lbl m).IsStep) (hpr : (e.lbl m).proc = p) : e.lbl m = .tau p := by
  cases hl : e.lbl m with
  | inv q o => rw [hl] at hs; exact hs.elim
  | tau q => rw [hl] at hpr; simp only [Label.proc] at hpr; rw [hpr]
  | ret q r =>
    rw [hl] at hpr; simp only [Label.proc] at hpr; subst hpr
    have hs' := e.step_eq m; rw [hl] at hs'
    exact absurd (by rw [(Impl.step_ret hs').2.1]; simp) (hp (m + 1) (by omega))

/-! ### Relation to CSLib's progress conditions -/

/-- The paper's wait-freedom coincides with CSLib's `Impl.WaitFree`. -/
theorem waitFreeP_iff : WaitFreeP I ↔ I.WaitFree := by
  constructor
  · intro h e p n hp
    by_contra hinf
    push Not at hinf
    refine h e p n (Or.inl fun N => ?_) hp
    obtain ⟨m, hm, hl⟩ := hinf N
    exact ⟨m, hm, by rw [hl]; trivial, by rw [hl]; rfl⟩
  · intro h e p n hc hp
    obtain ⟨N, hN⟩ := h e p n hp
    obtain ⟨m, hm, hs, hpr⟩ := hc.takesInfSteps hp (max N n)
    exact hN m (le_of_max_le_left hm)
      (eq_tau_of_pendingFrom hp (le_of_max_le_right hm) hs hpr)

/-- The paper's obstruction-freedom implies CSLib's `Impl.ObstructionFree` (solo runs from
reachable configurations return). -/
theorem ObstructionFreeP.obstructionFree (h : ObstructionFreeP I) : I.ObstructionFree := by
  intro C p ⟨α, hα⟩ hp
  by_contra hcon
  push Not at hcon
  obtain ⟨e, -, he, hpend⟩ := I.exists_infExec_solo hα hcon
  refine h e p α.length (Or.inl fun N => ?_) hpend ⟨α.length, fun m hm _ => by rw [he m hm]; rfl⟩
  exact ⟨max N α.length, le_max_left _ _, by rw [he _ (le_max_right _ _)]; trivial,
    by rw [he _ (le_max_right _ _)]; rfl⟩

/-! ### Proposition 3.3: the hierarchy -/

/-- Proposition 3.3, first implication: wait-freedom implies conflict-freedom. -/
theorem waitFree_conflictFree (h : WaitFreeP I) : ConflictFree I :=
  fun e p n hc hp => absurd hp (h e p n hc)

/-- Proposition 3.3, second implication: conflict-freedom implies weak conflict-freedom
(finitely many processes). -/
theorem conflictFree_weakConflictFree [Finite P] (h : ConflictFree I) : WeakConflictFree I := by
  refine ⟨fun e p n hc hp => (h e p n hc hp).1, fun e hecf => ?_⟩
  obtain ⟨p, hp⟩ := exists_takesInfSteps e
  exact ⟨p, Or.inl hp, fun n hpn => (h e p n (Or.inl hp) hpn).2 hecf⟩

/-- Proposition 3.3, third implication: weak conflict-freedom implies obstruction-freedom. -/
theorem weakConflictFree_obstructionFree (h : WeakConflictFree I) : ObstructionFreeP I := h.1

/-- Proposition 3.3 of [KST26]: wait-freedom ⟹ conflict-freedom ⟹ weak conflict-freedom ⟹
obstruction-freedom. -/
theorem progress_hierarchy [Finite P] :
    (WaitFreeP I → ConflictFree I) ∧ (ConflictFree I → WeakConflictFree I) ∧
      (WeakConflictFree I → ObstructionFreeP I) :=
  ⟨waitFree_conflictFree, conflictFree_weakConflictFree, weakConflictFree_obstructionFree⟩

/-! ### Proposition 3.4: degenerate conflict relations -/

/-- If all operations conflict, then in an eventually conflict-free execution an operation that
is pending forever eventually runs solo. -/
lemma soloFrom_of_total (htot : ∀ a b, A.Conflicting a b) {e : I.InfExec}
    (hecf : EventuallyConflictFree e) {p : P} {n : ℕ} (hp : PendingFrom e p n) :
    ∃ τ, SoloFrom e p τ := by
  obtain ⟨τ, hτ⟩ := hecf
  refine ⟨max τ n, fun m hm hs => ?_⟩
  by_contra hq
  obtain ⟨o', ho'⟩ := Option.ne_none_iff_exists'.1 (pend_ne_none_of_isStep e hs)
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 (hp m (le_of_max_le_right hm))
  exact hτ m (le_of_max_le_left hm) p _ (Ne.symm hq) o o' ho ho' (htot o o')

/-- Proposition 3.4, first item (conflict-freedom part): if every pair of operations
conflicts, conflict-freedom is equivalent to obstruction-freedom. -/
theorem conflictFree_iff_of_total [Finite P] (htot : ∀ a b, A.Conflicting a b) :
    ConflictFree I ↔ ObstructionFreeP I := by
  refine ⟨fun h => (conflictFree_weakConflictFree h).1, fun h e p n hc hp => ⟨h e p n hc hp, ?_⟩⟩
  exact fun hecf => h e p n hc hp (soloFrom_of_total htot hecf hp)

/-- Proposition 3.4, first item (weak conflict-freedom part): if every pair of operations
conflicts, weak conflict-freedom is equivalent to obstruction-freedom. -/
theorem weakConflictFree_iff_of_total [Finite P] (htot : ∀ a b, A.Conflicting a b) :
    WeakConflictFree I ↔ ObstructionFreeP I := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun e hecf => ?_⟩⟩
  obtain ⟨p, hp⟩ := exists_takesInfSteps e
  exact ⟨p, Or.inl hp, fun n hpn => h e p n (Or.inl hp) hpn (soloFrom_of_total htot hecf hpn)⟩

/-- Without conflicts every execution is eventually conflict-free. -/
lemma eventuallyConflictFree_of_empty (hemp : ∀ a b, ¬ A.Conflicting a b) (e : I.InfExec) :
    EventuallyConflictFree e :=
  ⟨0, fun _ _ _ _ _ o o' _ _ => hemp o o'⟩

/-- Proposition 3.4, second item (conflict-freedom part): if no two operations conflict,
conflict-freedom is equivalent to wait-freedom. -/
theorem conflictFree_iff_of_empty (hemp : ∀ a b, ¬ A.Conflicting a b) :
    ConflictFree I ↔ WaitFreeP I :=
  ⟨fun h e p n hc hp => (h e p n hc hp).2 (eventuallyConflictFree_of_empty hemp e),
    waitFree_conflictFree⟩

/-- Proposition 3.4, second item (one direction of the weak conflict-freedom part): if no two
operations conflict, weak conflict-freedom implies lock-freedom. (For the converse see
`differencies.md`.) -/
theorem WeakConflictFree.lockFreeP_of_empty (hemp : ∀ a b, ¬ A.Conflicting a b)
    (h : WeakConflictFree I) : LockFreeP I :=
  fun e => h.2 e (eventuallyConflictFree_of_empty hemp e)

end Podc.ConflictFreedom
