import Cslib.Computability.Distributed.SharedMemory.Progress
import Cslib.Computability.Distributed.SharedMemory.Task
import Mathlib.Data.Set.Card

/-!
# Crash faults and `(t, f)`-resilience in the shared-memory model
-- CSLib candidate: `Cslib/Computability/Distributed/SharedMemory/Resilience.lean`

Crash failures on CSLib's infinite executions (`Impl.InfExec`), and the graded resilience
notions of Taubenfeld, *A closer look at fault tolerance* (PODC 2012; Theory Comput. Syst. 2018).

In an infinite execution `e`:
* `e.Participates p` — `p` has a pending operation at some time;
* `e.Crashed p` — from some time on `p` has a pending operation and takes no further step (a
  crash *during* an operation; a process that stops after returning has not visibly failed);
* `e.Blocked p` — from some time on `p` has a pending operation forever (an operation of `p`
  never completes);
* `e.Starved p` — `p` is blocked but has not crashed: a correct participating process that does
  not terminate.

`TFResilient Adm t f` (Section 1.3 of the paper): in every admissible infinite execution with
`t' ≤ t` crashed processes, at most `f t'` processes are starved. `AlmostResilient`
(`f 0 = 0`, `f t' = 1`), `PartiallyResilient` (`f t' = t'`) and `WeaklyResilient` (no starved
process without crashes; with crashes, if at least two correct processes participate, one of
them terminates) are the paper's three levels; the `…WaitFree` versions take `t = n - 1`.
`Adm` restricts the executions, e.g. to one-shot ones (`OneShotExec`) or to required
participation (`AllParticipate`).

Wait-freedom is `(n-1, 0)`-resilience; CSLib's `Impl.WaitFree` is the stronger statement that a
pending process taking infinitely many steps finishes, without any reference to crashes.
-/

namespace Cslib.SharedMemory.Impl

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
  {I : Impl A B P L}

namespace InfExec

/-- `p` has a pending operation at some time. -/
def Participates (e : I.InfExec) (p : P) : Prop := ∃ t, (e.cfg t).pend p ≠ none

/-- `p` crashes: from some time on it has a pending operation and takes no further step. -/
def Crashed (e : I.InfExec) (p : P) : Prop :=
  ∃ t, (e.cfg t).pend p ≠ none ∧ ∀ t' ≥ t, (e.lbl t').proc ≠ p

/-- Some operation of `p` never completes: `p` is pending from some time on. -/
def Blocked (e : I.InfExec) (p : P) : Prop := ∃ t, ∀ t' ≥ t, (e.cfg t').pend p ≠ none

/-- A correct participating process: it participates and does not crash. -/
def Correct (e : I.InfExec) (p : P) : Prop := e.Participates p ∧ ¬ e.Crashed p

/-- A correct (participating) process that does not terminate. -/
def Starved (e : I.InfExec) (p : P) : Prop := e.Blocked p ∧ ¬ e.Crashed p

lemma Starved.correct {e : I.InfExec} {p : P} (h : e.Starved p) : e.Correct p := by
  obtain ⟨⟨t, ht⟩, hc⟩ := h
  exact ⟨⟨t, ht t le_rfl⟩, hc⟩

/-- A process that does not crash takes a step after every time at which it is pending. -/
lemma exists_step_of_not_crashed {e : I.InfExec} {p : P} (h : ¬ e.Crashed p) {t : ℕ}
    (hp : (e.cfg t).pend p ≠ none) : ∃ t' ≥ t, (e.lbl t').proc = p := by
  by_contra h'
  push Not at h'
  exact h ⟨t, hp, h'⟩

/-- All prefixes of `e` are one-shot (every process invokes at most one operation). -/
def OneShotExec (e : I.InfExec) : Prop := ∀ t, OneShot (e.pre t)

/-- Required participation: every process participates. -/
def AllParticipate (e : I.InfExec) : Prop := ∀ p, e.Participates p

end InfExec

/-- **`(t, f)`-resilience** (Taubenfeld, Section 1.3): in every admissible infinite execution
with `t' ≤ t` crashed processes, at most `f t'` correct participating processes do not
terminate. -/
def TFResilient (Adm : I.InfExec → Prop) (t : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ e, Adm e → {p | e.Crashed p}.ncard ≤ t →
    {p | e.Starved p}.ncard ≤ f {p | e.Crashed p}.ncard

/-- **Almost-`t`-resilience**: `(t, f)`-resilience with `f 0 = 0` and `f t' = 1` for `t' ≥ 1`. -/
def AlmostResilient (Adm : I.InfExec → Prop) (t : ℕ) : Prop :=
  I.TFResilient Adm t fun t' => if t' = 0 then 0 else 1

/-- **Partial-`t`-resilience**: `(t, f)`-resilience with `f t' = t'`. -/
def PartiallyResilient (Adm : I.InfExec → Prop) (t : ℕ) : Prop :=
  I.TFResilient Adm t id

/-- **Weak `t`-resilience**: without crashes every correct participating process terminates;
with `1 ≤ t' ≤ t` crashes, if at least two correct processes participate then one of them
terminates. -/
def WeaklyResilient (Adm : I.InfExec → Prop) (t : ℕ) : Prop :=
  ∀ e, Adm e → {p | e.Crashed p}.ncard ≤ t →
    ({p | e.Crashed p}.ncard = 0 → ∀ p, ¬ e.Starved p) ∧
    (2 ≤ {p | e.Correct p}.ncard → ∃ p, e.Correct p ∧ ¬ e.Blocked p)

/-- **`t`-resilience** in the standard sense: `(t, 0)`-resilience. -/
def Resilient (Adm : I.InfExec → Prop) (t : ℕ) : Prop := I.TFResilient Adm t fun _ => 0

section WaitFree

variable [Fintype P]

/-- Almost-wait-freedom: almost-`(n-1)`-resilience. -/
def AlmostWaitFree (Adm : I.InfExec → Prop) : Prop := I.AlmostResilient Adm (Fintype.card P - 1)

/-- Partial wait-freedom: partial-`(n-1)`-resilience. -/
def PartiallyWaitFree (Adm : I.InfExec → Prop) : Prop :=
  I.PartiallyResilient Adm (Fintype.card P - 1)

/-- Weak wait-freedom: weak `(n-1)`-resilience. -/
def WeaklyWaitFree (Adm : I.InfExec → Prop) : Prop := I.WeaklyResilient Adm (Fintype.card P - 1)

end WaitFree

/-- Almost-resilience implies partial resilience. -/
lemma AlmostResilient.partiallyResilient {Adm : I.InfExec → Prop} {t : ℕ}
    (h : I.AlmostResilient Adm t) : I.PartiallyResilient Adm t := fun e he ht =>
  (h e he ht).trans (by simp only [id]; split_ifs with h0 <;> omega)

/-- `t`-resilience implies almost-`t`-resilience. -/
lemma Resilient.almostResilient {Adm : I.InfExec → Prop} {t : ℕ} (h : I.Resilient Adm t) :
    I.AlmostResilient Adm t := fun e he ht => (h e he ht).trans (Nat.zero_le _)

namespace InfExec

/-- A process participates iff it invokes an operation at some time. -/
lemma participates_iff_exists_inv {e : I.InfExec} {p : P} :
    e.Participates p ↔ ∃ t o, e.lbl t = .inv p o := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨t', -, -, o, ho⟩ :=
      e.exists_inv_between (Nat.zero_le t) (by simp [e.cfg_zero, Impl.initCfg]) ht
    exact ⟨t', o, ho⟩
  · rintro ⟨t, o, ho⟩
    have h := e.step_eq t
    rw [ho] at h
    exact ⟨t + 1, by simp [(Impl.step_inv h).2.2.1]⟩

/-- A participating process that never returns is blocked. -/
lemma blocked_of_forall_ne_ret {e : I.InfExec} {p : P} (hp : e.Participates p)
    (hr : ∀ t r, e.lbl t ≠ .ret p r) : e.Blocked p := by
  obtain ⟨t, ht⟩ := hp
  refine ⟨t, fun t' ht' hn => ?_⟩
  obtain ⟨s, -, -, r, hs⟩ := e.exists_ret_between ht' ht hn
  exact hr s r hs

/-- A process that does not crash and is pending at `t` takes a step at some time `t' ≥ t`, in
the local state and with the pending operation it had at `t`. -/
lemma exists_first_step {e : I.InfExec} {p : P} (h : ¬ e.Crashed p) {t : ℕ}
    (hp : (e.cfg t).pend p ≠ none) :
    ∃ t' ≥ t, (e.lbl t').proc = p ∧ (e.cfg t').loc p = (e.cfg t).loc p ∧
      (e.cfg t').pend p = (e.cfg t).pend p := by
  classical
  have hex : ∃ k, (e.lbl (t + k)).proc = p := by
    obtain ⟨t₁, ht₁, hq⟩ := exists_step_of_not_crashed h hp
    exact ⟨t₁ - t, by rw [Nat.add_sub_cancel' ht₁]; exact hq⟩
  have hc := e.cfg_add_of_proc_ne fun j hj => Nat.find_min hex hj
  exact ⟨t + Nat.find hex, by omega, Nat.find_spec hex, hc.1, hc.2⟩

end InfExec

/-- `t`-resilience implies weak `t`-resilience (for finitely many processes). -/
lemma Resilient.weaklyResilient [Finite P] {Adm : I.InfExec → Prop} {t : ℕ}
    (h : I.Resilient Adm t) : I.WeaklyResilient Adm t := by
  intro e he ht
  have hs : ∀ p, ¬ e.Starved p := fun p hp => by
    have h0 := h e he ht
    rw [Nat.le_zero, Set.ncard_eq_zero (Set.toFinite _)] at h0
    exact (Set.eq_empty_iff_forall_notMem.1 h0) p hp
  refine ⟨fun _ => hs, fun h2 => ?_⟩
  obtain ⟨p, hp⟩ : {p | e.Correct p}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne] at h2
  exact ⟨p, hp, fun hb => hs p ⟨hb, hp.2⟩⟩

end Cslib.SharedMemory.Impl
