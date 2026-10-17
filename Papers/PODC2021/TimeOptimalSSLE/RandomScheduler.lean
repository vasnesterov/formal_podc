import Papers.PODC2021.TimeOptimalSSLE.Model
import Cslib.Probability.Markov.Absorption

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

So `NProtocol.SelfStabilizes` is exactly the paper's "with probability 1" notion. The kernel of a
deterministic protocol under the uniform random scheduler is `uniformKernel`
(`uniformKernel_pos_iff`).
-/

open Cslib.PopulationProtocol Cslib.Probability.Markov Matrix Filter Topology

set_option linter.unusedSectionVars false

namespace TimeOptimalSSLE.NProtocol

variable {Q A : Type*} [DecidableEq A] [Fintype A] [Fintype Q] [DecidableEq Q]

open Classical in
/-- The set of stably correct configurations. -/
noncomputable def stablySet (P : NProtocol Q) (good : Config A Q → Prop) : Finset (Config A Q) :=
  Finset.univ.filter fun C => P.StablyCorrect good C

lemma reflTransGen_of_reachable {P : NProtocol Q} {T : Matrix (Config A Q) (Config A Q) ℝ}
    (hpos : ∀ C D, P.Step C D → 0 < T C D) {C D : Config A Q} (h : P.Reachable C D) :
    Relation.ReflTransGen (fun x y => 0 < T x y) C D := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact ih.tail (hpos _ _ hst)

-- CSLib candidate
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
  refine tendsto_sum_compl_of_absorbing hT ?_ ?_ C
  · intro X hX Y hY
    by_contra hne
    have hpos' : 0 < T X Y := lt_of_le_of_ne (nonneg_of_mem_rowStochastic hT) (Ne.symm hne)
    simp only [stablySet, Finset.mem_filter, Finset.mem_univ, true_and] at hX hY
    exact hY fun Z hZ => hX Z (Relation.ReflTransGen.head (hstep _ _ hpos') hZ)
  · intro X
    obtain ⟨D, hD, hDs⟩ := hP X
    exact ⟨D, by simp [stablySet, hDs], reflTransGen_of_reachable hpos hD⟩

-- CSLib candidate
/-- **Unreachability implies probability 0.** If from `C` no stably correct configuration is
reachable, then at every time the probability of being in a stably correct configuration is `0`
(so the protocol stabilizes from `C` with probability `0`). -/
theorem prob_stablyCorrect_eq_zero (P : NProtocol Q) {good : Config A Q → Prop}
    {T : Matrix (Config A Q) (Config A Q) ℝ} (hT : T ∈ rowStochastic ℝ (Config A Q))
    (hstep : ∀ C D, 0 < T C D → P.Step C D) {C : Config A Q}
    (hC : ∀ D, P.Reachable C D → ¬ P.StablyCorrect good D) (t : ℕ) :
    ∑ D ∈ stablySet P good, (T ^ t) C D = 0 := by
  classical
  refine Finset.sum_eq_zero fun D hD => ?_
  simp only [stablySet, Finset.mem_filter, Finset.mem_univ, true_and] at hD
  refine pow_eq_zero_of_closed hT (fun X => P.Reachable C X) ?_ Relation.ReflTransGen.refl t
    (fun h => hC D h hD)
  intro X Y hX hXY
  exact hX.tail (hstep _ _ hXY)

/-! ### The uniform random scheduler for deterministic protocols -/

/-- Ordered pairs of distinct agents. -/
abbrev Pairs (A : Type*) := {p : A × A // p.1 ≠ p.2}

-- CSLib candidate
/-- The Markov kernel of a deterministic protocol under the uniformly random scheduler: an ordered
pair of distinct agents is drawn uniformly and interacts. -/
noncomputable def uniformKernel (P : Protocol Q) : Matrix (Config A Q) (Config A Q) ℝ :=
  randomMap (fun _ : Pairs A => 1 / (Fintype.card (Pairs A) : ℝ))
    (fun ω C => P.interact C ω.1.1 ω.1.2)

lemma uniformKernel_mem (P : Protocol Q) (hA : 2 ≤ Fintype.card A) :
    uniformKernel (A := A) P ∈ rowStochastic ℝ (Config A Q) := by
  have hne : Nonempty (Pairs A) := by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hA
    exact ⟨⟨(a, b), hab⟩⟩
  refine randomMap_mem_rowStochastic (fun _ => by positivity) ?_ _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (Pairs A) : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := Pairs A); positivity
  field_simp

lemma uniformKernel_pos_iff (P : Protocol Q) (C D : Config A Q) :
    0 < uniformKernel (A := A) P C D ↔ (ofProtocol P).Step C D := by
  rw [ofProtocol_step_iff]
  constructor
  · intro h
    obtain ⟨ω, -, hω⟩ := exists_of_randomMap_pos h
    exact ⟨ω.1.1, ω.1.2, ω.2, hω.symm⟩
  · rintro ⟨a, b, hab, rfl⟩
    have : Nonempty (Pairs A) := ⟨⟨(a, b), hab⟩⟩
    have hc : (0 : ℝ) < Fintype.card (Pairs A) := by exact_mod_cast Fintype.card_pos
    have hμ : ∀ ω : Pairs A, (0 : ℝ) ≤ 1 / (Fintype.card (Pairs A) : ℝ) := fun _ => by positivity
    exact randomMap_pos hμ (fun ω C => P.interact C ω.1.1 ω.1.2)
      (ω := (⟨(a, b), hab⟩ : Pairs A)) (by positivity) C

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
