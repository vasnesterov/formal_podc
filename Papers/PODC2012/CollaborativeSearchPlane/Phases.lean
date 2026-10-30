import Papers.PODC2012.CollaborativeSearchPlane.Basic

/-!
# Phased search algorithms (the algorithms of §3 and of the appendix)

All upper-bound algorithms of the paper are built from *phases*: "go to a node `u` chosen
uniformly at random in the ball `B(R)`, perform a spiral search of length `t` starting at `u`,
return to the source". Phases are grouped into *blocks* `b = 0, 1, 2, …` (stages, resp. big
stages), block `b` consisting of the finitely many phases `P b`.

As in the paper, the navigation procedures are atomic, with the guarantees the paper assumes
(§2 and footnote 1):

* walking to `u` takes `d(u) ≤ R` steps, a spiral search of length `t` takes `t` steps and
  ends within distance `t` of `u`, so returning takes `≤ R + t` steps: a phase lasts at most
  `2R + 2t` (`phaseDur`);
* a spiral search of length `t` from `u` visits every node `v` with `σ · d(u, v)² ≤ t`
  (the paper takes `σ = 4`: "visits all nodes at distance at most `√x/2`"; we keep the constant
  `σ ≥ 1` as a parameter, any value gives the same asymptotics).

Hence an agent whose node `u` in phase `x` satisfies `σ · d(u, τ)² ≤ t` has found the treasure by
the end of phase `x`. We formalize the analysis at this level: the random choices of all agents in
all phases are independent (`Measure.infinitePi`), `notFoundBefore S b` is the event that no agent
has hit its success set in a block `< b`, and if every agent finishes block `b'` within time
`∑_{b'' ≤ b'} dur b''`, then the search is over by time

`timeBound S dur = ∑_b dur b · 1[notFoundBefore S b]`.

`lintegral_timeBound` computes its expectation exactly:
`E[timeBound] = ∑_b dur b · ∏_{a} ∏_{phases x before b} Pr[u_{a,x} ∉ S(a,x)]`.
-/

namespace Podc.CollaborativeSearchPlane

open MeasureTheory Finset
open scoped ENNReal

variable {P : ℕ → Type} [∀ b, Fintype (P b)]

/-- The random choices of a phased search with `k` agents: the node chosen by agent `a` in
phase `x = ⟨b, p⟩` (phase `p` of block `b`). -/
abbrev Choices (k : ℕ) (P : ℕ → Type) := Fin k × (Σ b, P b) → Node

/-- The phases of the blocks `< b`. -/
def phasesBefore (P : ℕ → Type) [∀ b, Fintype (P b)] (b : ℕ) : Finset (Σ b, P b) :=
  (range b).sigma fun _ => univ

theorem mem_phasesBefore {b : ℕ} {x : Σ b, P b} : x ∈ phasesBefore P b ↔ x.1 < b := by
  simp [phasesBefore]

/-- No agent has chosen a node of its success set in any phase of the blocks `< b`. -/
def notFoundBefore {k : ℕ} (S : Fin k × (Σ b, P b) → Set Node) (b : ℕ) : Set (Choices k P) :=
  {ω | ∀ a x, x.1 < b → ω (a, x) ∉ S (a, x)}

/-- The time by which the search is over: `∑_b dur b · 1[no success before block b]`. -/
noncomputable def timeBound {k : ℕ} (S : Fin k × (Σ b, P b) → Set Node) (dur : ℕ → ℝ≥0∞)
    (ω : Choices k P) : ℝ≥0∞ :=
  ∑' b, dur b * (notFoundBefore S b).indicator 1 ω

theorem notFoundBefore_eq_pi {k : ℕ} (S : Fin k × (Σ b, P b) → Set Node) (b : ℕ) :
    notFoundBefore S b = Set.pi ↑((univ : Finset (Fin k)) ×ˢ phasesBefore P b) fun i => (S i)ᶜ := by
  ext ω
  simp only [notFoundBefore, Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_product, Set.mem_prod,
    Finset.mem_coe, Finset.mem_univ, true_and, mem_phasesBefore, Set.mem_compl_iff, Prod.forall]

theorem measurableSet_notFoundBefore {k : ℕ} (S : Fin k × (Σ b, P b) → Set Node) (b : ℕ) :
    MeasurableSet (notFoundBefore S b) := by
  rw [notFoundBefore_eq_pi]
  exact MeasurableSet.pi (Finset.countable_toSet _) fun i _ => (S i)ᶜ.to_countable.measurableSet

-- CSLib candidate
/-- **Expected time of a phased search.** With independent choices of law `π (a, x)`, the
expected value of `timeBound` is `∑_b dur b · ∏_a ∏_{x before b} π (a,x) (S (a,x))ᶜ`. -/
theorem lintegral_timeBound {k : ℕ} (π : Fin k × (Σ b, P b) → Measure Node)
    [∀ i, IsProbabilityMeasure (π i)] (S : Fin k × (Σ b, P b) → Set Node) (dur : ℕ → ℝ≥0∞) :
    ∫⁻ ω, timeBound S dur ω ∂(Measure.infinitePi π)
      = ∑' b, dur b * ∏ a, ∏ x ∈ phasesBefore P b, π (a, x) (S (a, x))ᶜ := by
  unfold timeBound
  rw [lintegral_tsum (f := fun b ω => dur b * (notFoundBefore S b).indicator 1 ω)
    fun b => ((measurable_one.indicator
    (measurableSet_notFoundBefore S b)).const_mul _).aemeasurable]
  congr 1
  ext b
  rw [lintegral_const_mul _ (measurable_one.indicator (measurableSet_notFoundBefore S b)),
    lintegral_indicator_one (measurableSet_notFoundBefore S b), notFoundBefore_eq_pi,
    Measure.infinitePi_pi _ (fun i _ => (S i)ᶜ.to_countable.measurableSet), Finset.prod_product]

/-! ### Uniform choice in a ball -/

/-- The ball `B(R) = {u : d(s, u) ≤ R}` as a finite set. -/
def ballFinset (R : ℕ) : Finset Node :=
  ((Icc (-(R : ℤ)) R) ×ˢ (Icc (-(R : ℤ)) R)).filter fun u => dist u ≤ R

theorem mem_ballFinset {R : ℕ} {u : Node} : u ∈ ballFinset R ↔ dist u ≤ R := by
  unfold ballFinset
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  unfold dist
  constructor
  · exact fun h => h.2
  · intro h; refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, h⟩ <;> omega

theorem ballFinset_nonempty (R : ℕ) : (ballFinset R).Nonempty :=
  ⟨0, mem_ballFinset.2 (by simp [dist])⟩

/-- The uniform distribution on `B(R)`. -/
noncomputable def uniformBall (R : ℕ) : Measure Node :=
  (PMF.uniformOfFinset (ballFinset R) (ballFinset_nonempty R)).toMeasure

instance (R : ℕ) : IsProbabilityMeasure (uniformBall R) := by
  unfold uniformBall; infer_instance

open Classical in
theorem uniformBall_apply (R : ℕ) (A : Set Node) :
    uniformBall R A = ((ballFinset R).filter (· ∈ A)).card / (ballFinset R).card := by
  unfold uniformBall
  rw [PMF.toMeasure_uniformOfFinset_apply _ _ A.to_countable.measurableSet]

/-- The success set of a phase with spiral length `t` (spiral constant `σ`) for treasure `τ`. -/
def spiralSucc (σ : ℕ) (τ : Node) (t : ℕ) : Set Node := {u | σ * dist (u - τ) ^ 2 ≤ t}

/-- Duration bound of a phase: walk to `u ∈ B(R)`, spiral of length `t`, return. -/
def phaseDur (R t : ℕ) : ℕ := 2 * R + 2 * t

/-! ### Phased searches with uniform choices in balls -/

/-- Duration bound of block `b` when phase `x` samples in `B(R x)` and agent `a` spirals for
`t (a, x)` steps: the sum over the phases of the maximum over the agents of the phase durations. -/
def blockDur {k : ℕ} (R : (Σ b, P b) → ℕ) (t : Fin k × (Σ b, P b) → ℕ) (b : ℕ) : ℕ :=
  ∑ p : P b, (univ : Finset (Fin k)).sup fun a => phaseDur (R ⟨b, p⟩) (t (a, ⟨b, p⟩))

/-- The expected running time (bound) of the phased search with `k` agents in which phase `x`
picks a uniform node of `B(R x)` and agent `a` then spirals for `t (a, x)` steps (spiral
constant `σ`), for the treasure at `τ`. -/
noncomputable def phasedTime {k : ℕ} (σ : ℕ) (R : (Σ b, P b) → ℕ) (t : Fin k × (Σ b, P b) → ℕ)
    (τ : Node) : ℝ≥0∞ :=
  ∫⁻ ω, timeBound (fun i => spiralSucc σ τ (t i)) (fun b => (blockDur R t b : ℝ≥0∞)) ω
    ∂(Measure.infinitePi fun i : Fin k × (Σ b, P b) => uniformBall (R i.2))

/-- The "not found during block `b`" factor. -/
noncomputable def blockFail {k : ℕ} (σ : ℕ) (R : (Σ b, P b) → ℕ) (t : Fin k × (Σ b, P b) → ℕ)
    (τ : Node) (b : ℕ) : ℝ≥0∞ :=
  ∏ p : P b, ∏ a : Fin k, uniformBall (R ⟨b, p⟩) (spiralSucc σ τ (t (a, ⟨b, p⟩)))ᶜ

theorem phasedTime_eq {k : ℕ} (σ : ℕ) (R : (Σ b, P b) → ℕ) (t : Fin k × (Σ b, P b) → ℕ)
    (τ : Node) :
    phasedTime σ R t τ = ∑' b, (blockDur R t b : ℝ≥0∞) * ∏ b' ∈ range b, blockFail σ R t τ b' := by
  unfold phasedTime
  rw [lintegral_timeBound]
  congr 1; ext b; congr 1
  rw [Finset.prod_comm]
  unfold phasesBefore blockFail
  rw [Finset.prod_sigma]

theorem blockFail_le_one {k : ℕ} (σ : ℕ) (R : (Σ b, P b) → ℕ) (t : Fin k × (Σ b, P b) → ℕ)
    (τ : Node) (b : ℕ) : blockFail σ R t τ b ≤ 1 :=
  Finset.prod_le_one fun _ _ => Finset.prod_le_one fun _ _ => prob_le_one

end Podc.CollaborativeSearchPlane
