import Podc.Computability.Distributed.MessagePassing.FailureDetectors.Model

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/FailureDetectors/Sigma.lean

/-!
# The quorum failure detector `Σ` and the trivial failure detector

* `SigmaFD P` is the quorum failure detector `Σ` of Delporte-Gallet, Fauconnier and Guerraoui
  (*Tight failure detection bounds on atomic object implementations*, J. ACM 2010): every process
  outputs a non-empty set of processes (a *quorum*); any two quorums, output by any two processes
  at any two times, intersect; and eventually the quorums output by a correct process contain only
  correct processes. (The name `Sigma` is avoided because of the root type `Sigma`.)
* `trivialFD P` is the failure detector that provides no information (`fd : ∅`).
-/

namespace Cslib.FailureDetectors

variable {P : Type*}

/-- The quorum failure detector `Σ`: outputs are non-empty sets of processes, any two outputs
(of any processes, at any times) intersect, and every correct process eventually outputs only
sets of correct processes. -/
def SigmaFD (P : Type*) : FailureDetector P (Set P) := fun F =>
  {H | (∀ p t, (H p t).Nonempty) ∧ (∀ p q t t', (H p t ∩ H q t').Nonempty) ∧
    ∀ p, F.Correct p → ∃ T, ∀ t ≥ T, H p t ⊆ {q | F.Correct q}}

/-- If some process `c` is correct, the constant history `{c}` is a history of `Σ`; in
particular `Σ` outputs a non-empty set of histories in every failure pattern with a correct
process. -/
lemma const_mem_SigmaFD (F : FailurePattern P) (c : P) (hc : F.Correct c) :
    (fun _ _ => ({c} : Set P)) ∈ SigmaFD P F :=
  ⟨fun _ _ => Set.singleton_nonempty c, fun _ _ _ _ => by simp,
    fun _ _ => ⟨0, fun _ _ q hq => by rw [Set.mem_singleton_iff.1 hq]; exact hc⟩⟩

/-- The trivial failure detector (`fd : ∅`), which provides no information. -/
def trivialFD (P : Type*) : FailureDetector P Unit := fun _ => Set.univ

lemma mem_trivialFD (F : FailurePattern P) (H : P → ℕ → Unit) : H ∈ trivialFD P F :=
  Set.mem_univ H

end Cslib.FailureDetectors
