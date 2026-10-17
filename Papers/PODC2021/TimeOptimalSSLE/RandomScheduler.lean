import Papers.PODC2021.TimeOptimalSSLE.Model
import Podc.PopulationProtocols.RandomScheduler
import Podc.Stabilization.Markov

/-!
# The uniformly random scheduler: "with probability 1" versus reachability

The paper's semantics (Section 2): at each step an ordered pair of distinct agents is chosen
uniformly at random and the (possibly randomized) transition is applied. A protocol
*self-stabilizes* if from every configuration a stably correct configuration is reached with
probability 1.

For a finite state space this is a finite Markov chain on configurations. We prove, for **any**
row-stochastic kernel whose positive entries are exactly the protocol's steps:

* `tendsto_not_stablyCorrect`: if `SelfStabilizes good` (from every configuration some stably
  correct configuration is reachable), then from every configuration the probability of not being
  in a stably correct configuration after `t` steps tends to `0` (stabilization with
  probability 1);
* `prob_stablyCorrect_eq_zero`: conversely, if from `C` no stably correct configuration is
  reachable, then the probability of being in a stably correct configuration is `0` at all times.

So `NProtocol.SelfStabilizes` is exactly the paper's "with probability 1" notion. Both are
instances of the generic bridge `Cslib.TransitionSystem.SelfStabilizes.tendsto` /
`Cslib.TransitionSystem.prob_eq_zero_of_not_reach` (`Podc.Stabilization.Markov`). The kernel of a
deterministic protocol under the uniform random scheduler is
`Cslib.PopulationProtocol.uniformKernel` (`uniformKernel_pos_iff`).
-/

open Cslib.PopulationProtocol Cslib.Probability.Markov Cslib.TransitionSystem Matrix Filter Topology

namespace TimeOptimalSSLE.NProtocol

variable {Q A : Type*} [DecidableEq A] [Fintype A] [Fintype Q] [DecidableEq Q]

open Classical in
/-- The set of stably correct configurations. -/
noncomputable def stablySet (P : NProtocol Q) (good : Config A Q → Prop) : Finset (Config A Q) :=
  Finset.univ.filter fun C => P.StablyCorrect good C

omit [DecidableEq Q] in
open Classical in
lemma stablySet_eq (P : NProtocol Q) (good : Config A Q → Prop) :
    stablySet P good = {C | P.StablyCorrect good C}.toFinset := by
  simp [stablySet]

/-- **Self-stabilization implies stabilization with probability 1.** For any Markov kernel whose
positive-probability moves are exactly protocol steps: if from every configuration a stably
correct configuration is reachable, the probability of not being stably correct after `t` steps
tends to `0`. -/
theorem tendsto_not_stablyCorrect (P : NProtocol Q) {good : Config A Q → Prop}
    {T : Matrix (Config A Q) (Config A Q) ℝ} (hT : T ∈ rowStochastic ℝ (Config A Q))
    (hstep : ∀ C D, 0 < T C D → P.Step C D) (hpos : ∀ C D, P.Step C D → 0 < T C D)
    (hP : P.SelfStabilizes good) (C : Config A Q) :
    Tendsto (fun t => ∑ D ∈ (stablySet P good)ᶜ, (T ^ t) C D) atTop (𝓝 0) := by
  classical
  rw [stablySet_eq]
  exact hP.tendsto hT hstep hpos C

/-- **Unreachability implies probability 0.** If from `C` no stably correct configuration is
reachable, then at every time the probability of being in a stably correct configuration is `0`
(so the protocol stabilizes from `C` with probability `0`). -/
theorem prob_stablyCorrect_eq_zero (P : NProtocol Q) {good : Config A Q → Prop}
    {T : Matrix (Config A Q) (Config A Q) ℝ} (hT : T ∈ rowStochastic ℝ (Config A Q))
    (hstep : ∀ C D, 0 < T C D → P.Step C D) {C : Config A Q}
    (hC : ∀ D, P.Reachable C D → ¬ P.StablyCorrect good D) (t : ℕ) :
    ∑ D ∈ stablySet P good, (T ^ t) C D = 0 := by
  classical
  rw [stablySet_eq]
  exact prob_eq_zero_of_not_reach hT hstep hC t

/-- **Deterministic protocols under the uniform random scheduler.** If a deterministic protocol
self-stabilizes (reachability sense), then from every configuration it reaches a stably correct
configuration with probability 1. -/
theorem uniform_tendsto (P : Protocol Q) (hA : 2 ≤ Fintype.card A) {good : Config A Q → Prop}
    (hP : (ofProtocol P).SelfStabilizes good) (C : Config A Q) :
    Tendsto (fun t => ∑ D ∈ (stablySet (ofProtocol P) good)ᶜ, (uniformKernel P ^ t) C D)
      atTop (𝓝 0) :=
  tendsto_not_stablyCorrect _ (uniformKernel_mem P hA)
    (fun C D h => (uniformKernel_pos_iff P C D).mp h)
    (fun C D h => (uniformKernel_pos_iff P C D).mpr h) hP C

end TimeOptimalSSLE.NProtocol
