import Cslib.Computability.Distributed.SharedMemory.Progress
import Cslib.Foundations.Data.Nat.Descent

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Progress.lean (append to the
-- `InfExec` section of the existing file)

/-!
# Fair infinite executions: processes that stay pending

Additions to `Cslib/Computability/Distributed/SharedMemory/Progress.lean`.

* `Impl.InfExec.exists_act_of_pending`: under fairness, a process that is pending forever acts
  infinitely often;
* `Impl.InfExec.false_of_descent`: a measure that never increases from some time on and strictly
  decreases at every action of a process that is pending forever gives a contradiction (under
  fairness). This is the usual termination argument for a process that is stuck in a loop.
-/

namespace Cslib.SharedMemory.Impl

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type} [DecidableEq P]
  {I : Impl A B P L}

/-- Under fairness, a process that is pending from time `T` on acts at some time `≥ t`, for every
`t ≥ T`. -/
theorem InfExec.exists_act_of_pending (e : I.InfExec) (hfair : e.Fair) {q : P} {T : ℕ}
    (hp : ∀ t ≥ T, (e.cfg t).pend q ≠ none) (t : ℕ) (ht : T ≤ t) :
    ∃ t' ≥ t, (e.lbl t').proc = q := by
  obtain ⟨t', h1, h2, -⟩ := e.first_act hfair (hp t ht)
  exact ⟨t', h1, h2⟩

/-- Under fairness, no process `q` can be pending from time `t₀` on if some measure `μ` of times
does not increase from `t₀` on and strictly decreases at every action of `q`. -/
theorem InfExec.false_of_descent (e : I.InfExec) (hfair : e.Fair) (q : P) (t₀ : ℕ) (μ : ℕ → ℕ)
    (hp : ∀ t ≥ t₀, (e.cfg t).pend q ≠ none)
    (hle : ∀ t ≥ t₀, (e.lbl t).proc ≠ q → μ (t + 1) ≤ μ t)
    (hlt : ∀ t ≥ t₀, (e.lbl t).proc = q → μ (t + 1) < μ t) : False := by
  have hmono : ∀ t ≥ t₀, μ (t + 1) ≤ μ t := fun t ht => by
    by_cases h : (e.lbl t).proc = q
    · exact (hlt t ht h).le
    · exact hle t ht h
  obtain ⟨T, hT, hc⟩ := Nat.eventually_not_of_succ_le hmono hlt
  obtain ⟨t', ht', hq⟩ := e.exists_act_of_pending hfair hp T hT
  exact hc t' ht' hq

end Cslib.SharedMemory.Impl
