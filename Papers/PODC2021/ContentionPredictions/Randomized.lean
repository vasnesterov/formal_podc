import Papers.PODC2021.ContentionPredictions.Model
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Data.BitVec

-- CSLib candidate: radio-channel model (see wiki/library-map.md)

/-!
# Randomized contention resolution with perfect advice (Theorems 3.6 and 3.7, lower bounds)

**Model (randomized, private coins).** Players use independent private randomness.

* *No collision detection.* Before the problem is solved every player hears only silence, so a
  player's behaviour is a random *transmission schedule* `ℕ → Bool`; an algorithm with advice
  alphabet `A` is a family of laws `D a v` of these schedules (player `v`, advice `a`), and the
  schedules of different players are independent (`Measure.pi`). The success time
  `succTime P ω ∈ {1, 2, …, ⊤}` is one plus the first round in which exactly one participant
  of `P` transmits; `expTime (D a) P` is its expectation.
* *Collision detection.* A player's behaviour is a random *strategy* `List Bool → Bool`
  (transmit or not, given the common collision history); the execution for a fixed choice of
  strategies is the deterministic execution of `Model.lean`.

The lower bounds of the paper reduce to the lower bound of [18] (Newport 2014) for randomized
algorithms without advice and without collision detection, which we take as a hypothesis
(`NewportBound n c`: every algorithm without advice has a participant set with expected time
`≥ c log₂ n`).

* `theorem_3_6_lower`: with `|A|` advice values the worst-case expected time is `≥ c log₂ n / |A|`
  (the paper's "try all advice strings in parallel", made precise by round-robin interleaving).
* `expTime_simulation_le`: the paper's simulation of a collision-detection algorithm without
  collision detection (one round per possible history) gives expected time `≤ E[2^T]`, where `T` is
  the success time of the simulated algorithm. Combined with the interleaving,
  `theorem_3_7_lower_exp` gives `E[2^T] ≥ c log₂ n / 2^b` for some participant set. The paper
  concludes `E[T] ≥ log₂ (c log₂ n / 2^b)`, which would need `E[2^T] ≤ 2^{E[T]}`: Jensen's inequality
  goes the other way, so this step of the proof of Theorem 3.7 is a gap (see `differencies.md`).
-/

namespace Podc.ContentionPredictions

open MeasureTheory Finset
open scoped ENNReal

variable {n : ℕ}

/-! ### Success time -/

/-- Number of rounds until exactly one participant of `P` transmits (`⊤` if never), for the
transmission schedules `ω`. -/
noncomputable def succTime (P : Finset (Fin n)) (ω : Fin n → ℕ → Bool) : ℝ≥0∞ :=
  ⨅ (r : ℕ) (_ : (P.filter fun v => ω v r).card = 1), ((r + 1 : ℕ) : ℝ≥0∞)

theorem succTime_le {P : Finset (Fin n)} {ω : Fin n → ℕ → Bool} {r : ℕ}
    (h : (P.filter fun v => ω v r).card = 1) : succTime P ω ≤ ((r + 1 : ℕ) : ℝ≥0∞) :=
  iInf₂_le r h

theorem one_le_succTime (P : Finset (Fin n)) (ω : Fin n → ℕ → Bool) : 1 ≤ succTime P ω := by
  unfold succTime
  refine le_iInf₂ fun r _ => ?_
  exact_mod_cast Nat.succ_pos r

theorem measurable_succTime (P : Finset (Fin n)) : Measurable (succTime P) := by
  unfold succTime
  refine Measurable.iInf fun r => ?_
  have hS : MeasurableSet {ω : Fin n → ℕ → Bool | (P.filter fun v => ω v r).card = 1} := by
    have hm : Measurable fun (ω : Fin n → ℕ → Bool) (v : Fin n) => ω v r := by fun_prop
    exact hm (Set.toFinite {x : Fin n → Bool | (P.filter fun v => x v).card = 1}).measurableSet
  have : (fun ω : Fin n → ℕ → Bool =>
      ⨅ (_ : (P.filter fun v => ω v r).card = 1), ((r + 1 : ℕ) : ℝ≥0∞)) =
      fun ω => if (P.filter fun v => ω v r).card = 1 then ((r + 1 : ℕ) : ℝ≥0∞) else ⊤ := by
    ext ω; split_ifs with h <;> simp [h]
  rw [this]
  exact Measurable.ite hS measurable_const measurable_const

/-- Expected number of rounds for participants `P` when player `v` draws its schedule from `μ v`,
independently. -/
noncomputable def expTime (μ : Fin n → Measure (ℕ → Bool)) (P : Finset (Fin n)) : ℝ≥0∞ :=
  ∫⁻ ω, succTime P ω ∂(Measure.pi μ)

/-- Any algorithm needs at least one round in expectation. -/
theorem one_le_expTime (μ : Fin n → Measure (ℕ → Bool)) [∀ v, IsProbabilityMeasure (μ v)]
    (P : Finset (Fin n)) : 1 ≤ expTime μ P := by
  unfold expTime
  calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂(Measure.pi μ) := by simp
    _ ≤ _ := lintegral_mono fun ω => one_le_succTime P ω

/-- The lower bound of [18] (Newport, DISC 2014) for `n` players, taken as a hypothesis: every
randomized algorithm without advice and without collision detection has a nonempty participant
set with expected time at least `c log₂ n`. -/
def NewportBound (n : ℕ) (c : ℝ) : Prop :=
  ∀ μ : Fin n → Measure (ℕ → Bool), (∀ v, IsProbabilityMeasure (μ v)) →
    ∃ P : Finset (Fin n), P.Nonempty ∧ ENNReal.ofReal (c * Real.logb 2 n) ≤ expTime μ P

/-! ### Interleaving the advice values (proof of Theorem 3.6) -/

variable {A : Type*} [Fintype A] [Nonempty A]

/-- Round-robin interleaving of one schedule per advice value: round `j` of the combined schedule
is round `j / |A|` of the copy number `j % |A|`. -/
noncomputable def interleave (ω : A → ℕ → Bool) (j : ℕ) : Bool :=
  ω ((Fintype.equivFin A).symm ⟨j % Fintype.card A, Nat.mod_lt _ Fintype.card_pos⟩)
    (j / Fintype.card A)

theorem measurable_interleave : Measurable (interleave (A := A)) := by
  unfold interleave; fun_prop

/-- The no-advice algorithm running all advice values in parallel. -/
noncomputable def parallel (D : A → Fin n → Measure (ℕ → Bool)) (v : Fin n) :
    Measure (ℕ → Bool) :=
  (Measure.pi fun a => D a v).map interleave

instance (D : A → Fin n → Measure (ℕ → Bool)) [∀ a v, IsProbabilityMeasure (D a v)] (v : Fin n) :
    IsProbabilityMeasure (parallel D v) := by
  unfold parallel; infer_instance

/-- Pathwise: the interleaved execution succeeds no later than `|A|` times the success time of
the copy with advice `a`. -/
theorem succTime_interleave_le (P : Finset (Fin n)) (ω : Fin n → A → ℕ → Bool) (a : A) :
    succTime P (fun v => interleave (ω v)) ≤
      (Fintype.card A : ℝ≥0∞) * succTime P (fun v => ω v a) := by
  set B := Fintype.card A
  have hB : 0 < B := Fintype.card_pos
  set i := (Fintype.equivFin A a : ℕ) with hi
  have hiB : i < B := (Fintype.equivFin A a).isLt
  unfold succTime
  rw [ENNReal.mul_iInf_of_ne (by simp [hB.ne']) (by simp)]
  refine le_iInf fun r => ?_
  rw [ENNReal.mul_iInf_of_ne (by simp [hB.ne']) (by simp)]
  refine le_iInf fun hr => ?_
  have hj : (r * B + i) % B = i := by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hiB]
  have hj' : (r * B + i) / B = r := by
    rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hiB, add_zero]
  have hcopy : ∀ v, interleave (ω v) (r * B + i) = ω v a r := by
    intro v
    unfold interleave
    have : ((Fintype.equivFin A).symm ⟨(r * B + i) % B, Nat.mod_lt _ hB⟩) = a := by
      rw [Equiv.symm_apply_eq]; ext; exact hj
    rw [this, hj']
  refine (iInf₂_le (r * B + i) (by simpa only [hcopy] using hr)).trans ?_
  have : ((r * B + i + 1 : ℕ) : ℝ≥0∞) ≤ ((B * (r + 1) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast (by nlinarith : r * B + i + 1 ≤ B * (r + 1))
  simpa using this

/-- Expected time of the parallel algorithm is at most `|A|` times that of any single copy. -/
theorem expTime_parallel_le (D : A → Fin n → Measure (ℕ → Bool))
    [∀ a v, IsProbabilityMeasure (D a v)] (P : Finset (Fin n)) (a : A) :
    expTime (parallel D) P ≤ (Fintype.card A : ℝ≥0∞) * expTime (D a) P := by
  unfold expTime parallel
  rw [← Measure.pi_map_pi (fun v => measurable_interleave.aemeasurable)]
  have hmeas : Measurable fun (x : Fin n → A → ℕ → Bool) v => interleave (x v) :=
    Measurable.of_eval fun v => measurable_interleave.comp (measurable_pi_apply v)
  rw [lintegral_map (measurable_succTime P) hmeas]
  calc ∫⁻ x, succTime P (fun v => interleave (x v)) ∂Measure.pi (fun v => Measure.pi fun a => D a v)
      ≤ ∫⁻ x, (Fintype.card A : ℝ≥0∞) * succTime P (fun v => x v a)
          ∂Measure.pi (fun v => Measure.pi fun a => D a v) :=
        lintegral_mono fun x => succTime_interleave_le P x a
    _ = (Fintype.card A : ℝ≥0∞) * ∫⁻ x, succTime P (fun v => x v a)
          ∂Measure.pi (fun v => Measure.pi fun a => D a v) := by
        exact lintegral_const_mul (Fintype.card A : ℝ≥0∞)
          (f := fun x : Fin n → A → ℕ → Bool => succTime P fun v => x v a)
          ((measurable_succTime P).comp (by fun_prop))
    _ = (Fintype.card A : ℝ≥0∞) * ∫⁻ ω, succTime P ω ∂Measure.pi (D a) := by
        congr 1
        have hev : Measure.pi (D a) =
            (Measure.pi fun v => Measure.pi fun a => D a v).map (fun x v => x v a) := by
          rw [Measure.pi_map_pi (fun v => (measurable_pi_apply a).aemeasurable)]
          congr 1; funext v
          exact ((measurePreserving_eval (μ := fun a => D a v) a).map_eq).symm
        rw [hev, lintegral_map (measurable_succTime P)
          (by fun_prop)]

/-- **Theorem 3.6 of [Gilbert–Newport–Vaidya–Weaver, PODC 2021], lower bound**, conditional on the
lower bound of [18]: if every no-advice algorithm needs expected time `c log₂ n` on some
participant set, then every randomized algorithm without collision detection using advice from
`A` (`|A| = 2^b` for `b` bits) has a participant set `P` with expected time `≥ c log₂ n / |A|`
under its advice `f P`. -/
theorem theorem_3_6_lower {c : ℝ} (hN : NewportBound n c) (D : A → Fin n → Measure (ℕ → Bool))
    [∀ a v, IsProbabilityMeasure (D a v)] (f : Finset (Fin n) → A) :
    ∃ P : Finset (Fin n), P.Nonempty ∧
      ENNReal.ofReal (c * Real.logb 2 n) / Fintype.card A ≤ expTime (D (f P)) P := by
  obtain ⟨P, hP, hle⟩ := hN (parallel D) inferInstance
  refine ⟨P, hP, ?_⟩
  rw [ENNReal.div_le_iff (by simp) (by simp)]
  calc ENNReal.ofReal (c * Real.logb 2 n) ≤ expTime (parallel D) P := hle
    _ ≤ (Fintype.card A : ℝ≥0∞) * expTime (D (f P)) P := expTime_parallel_le D P (f P)
    _ = _ := mul_comm _ _

/-- Theorem 3.6 lower bound with `b`-bit advice: some participant set needs expected time
`≥ c log₂ n / 2^b`. -/
theorem theorem_3_6_lower_bits {c : ℝ} (hN : NewportBound n c) {b : ℕ}
    (D : Bits b → Fin n → Measure (ℕ → Bool)) [∀ a v, IsProbabilityMeasure (D a v)]
    (f : Finset (Fin n) → Bits b) :
    ∃ P : Finset (Fin n), P.Nonempty ∧
      ENNReal.ofReal (c * Real.logb 2 n) / 2 ^ b ≤ expTime (D (f P)) P := by
  obtain ⟨P, hP, h⟩ := theorem_3_6_lower hN D f
  exact ⟨P, hP, by simpa using h⟩

/-! ### Simulating collision detection without it (proof of Theorem 3.7) -/

/-- The `j`-th feedback history in order of length (`ε, 0, 1, 00, 10, 01, 11, …`): write `j + 1`
in binary and drop the leading `1`. -/
def histOfIndex (j : ℕ) : List Bool :=
  List.ofFn fun i : Fin (Nat.log 2 (j + 1)) => (j + 1).testBit i

/-- Index of a history `h` in this enumeration: `2^|h| - 1 + (h read in binary, little-endian)`. -/
def indexOfHist (h : List Bool) : ℕ := 2 ^ h.length - 1 + (BitVec.ofBoolListLE h).toNat

theorem histOfIndex_indexOfHist (h : List Bool) : histOfIndex (indexOfHist h) = h := by
  have hlt := (BitVec.ofBoolListLE h).isLt
  have hpos : 1 ≤ 2 ^ h.length := Nat.one_le_two_pow
  have e : indexOfHist h + 1 = 2 ^ h.length + (BitVec.ofBoolListLE h).toNat := by
    unfold indexOfHist; omega
  have hlog : Nat.log 2 (indexOfHist h + 1) = h.length := by
    rw [e]
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · omega
    · rw [pow_succ]; omega
  unfold histOfIndex
  apply List.ext_get
  · simp [hlog]
  · intro i h1 h2
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    have hi : i < h.length := h2
    rw [e, Nat.testBit_two_pow_add_gt hi]
    have := BitVec.getLsbD_ofBoolListLE (bs := h) (i := i)
    rw [BitVec.getLsbD, ] at this
    rw [this]
    simp [hi]

theorem indexOfHist_lt (h : List Bool) : indexOfHist h + 1 < 2 ^ (h.length + 1) := by
  have hlt := (BitVec.ofBoolListLE h).isLt
  have hpos : 1 ≤ 2 ^ h.length := Nat.one_le_two_pow
  unfold indexOfHist; rw [pow_succ]; omega

/-- The no-CD schedule obtained from a CD strategy: in round `j`, behave as the strategy does
after the `j`-th history. -/
def simSchedule (σ : List Bool → Bool) (j : ℕ) : Bool := σ (histOfIndex j)

theorem measurable_simSchedule : Measurable simSchedule := by
  unfold simSchedule; fun_prop

/-- The deterministic execution determined by fixed strategies `ω` (collision detection). -/
def stratAlg (ω : Fin n → List Bool → Bool) : DetAlg n Unit := fun _ h v => ω v h

/-- Success time `T` (number of rounds, `⊤` if never) of the CD execution with strategies `ω`. -/
noncomputable def cdTime (P : Finset (Fin n)) (ω : Fin n → List Bool → Bool) : ℝ≥0∞ :=
  ⨅ (r : ℕ) (_ : SolvedAt true (stratAlg ω) () P r), ((r + 1 : ℕ) : ℝ≥0∞)

/-- Expected number of rounds of a randomized CD algorithm (player `v` draws its strategy from
`D v`, independently). -/
noncomputable def expTimeCD (D : Fin n → Measure (List Bool → Bool)) (P : Finset (Fin n)) :
    ℝ≥0∞ :=
  ∫⁻ ω, cdTime P ω ∂(Measure.pi D)

theorem one_le_expTimeCD (D : Fin n → Measure (List Bool → Bool))
    [∀ v, IsProbabilityMeasure (D v)] (P : Finset (Fin n)) : 1 ≤ expTimeCD D P := by
  unfold expTimeCD
  calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂(Measure.pi D) := by simp
    _ ≤ _ := lintegral_mono fun ω => le_iInf₂ fun r _ => by exact_mod_cast Nat.succ_pos r

/-- `2^T` for the success time `T` (number of rounds) of the CD execution with strategies `ω`. -/
noncomputable def pow2Time (P : Finset (Fin n)) (ω : Fin n → List Bool → Bool) : ℝ≥0∞ :=
  ⨅ (r : ℕ) (_ : SolvedAt true (stratAlg ω) () P r), (2 : ℝ≥0∞) ^ (r + 1)

/-- Pathwise: the simulation succeeds within `2^T` rounds. -/
theorem succTime_sim_le (P : Finset (Fin n)) (ω : Fin n → List Bool → Bool) :
    succTime P (fun v => simSchedule (ω v)) ≤ pow2Time P ω := by
  unfold pow2Time
  refine le_iInf₂ fun r hr => ?_
  simp only [SolvedAt, transmitters, stratAlg] at hr
  set h := history true (stratAlg ω) () P r
  have hj : histOfIndex (indexOfHist h) = h := histOfIndex_indexOfHist h
  refine (succTime_le (r := indexOfHist h) ?_).trans ?_
  · simp only [simSchedule, hj]
    exact hr
  · have := indexOfHist_lt h
    rw [history_length] at this
    have : ((indexOfHist h + 1 : ℕ) : ℝ≥0∞) ≤ ((2 ^ (r + 1) : ℕ) : ℝ≥0∞) := by
      exact_mod_cast this.le
    simpa using this

/-- The simulation of a CD algorithm (laws `D v` of strategies) by a no-CD algorithm has expected
time at most `E[2^T]`. -/
theorem expTime_simulation_le (D : Fin n → Measure (List Bool → Bool))
    [∀ v, IsProbabilityMeasure (D v)] (P : Finset (Fin n)) :
    expTime (fun v => (D v).map simSchedule) P ≤ ∫⁻ ω, pow2Time P ω ∂(Measure.pi D) := by
  unfold expTime
  rw [← Measure.pi_map_pi (fun v => measurable_simSchedule.aemeasurable)]
  have hmeas : Measurable fun (x : Fin n → List Bool → Bool) v => simSchedule (x v) :=
    Measurable.of_eval fun v => measurable_simSchedule.comp (measurable_pi_apply v)
  rw [lintegral_map (measurable_succTime P) hmeas]
  exact lintegral_mono fun ω => succTime_sim_le P ω

/-- **What the proof of Theorem 3.7 establishes** (conditional on [18]): every randomized
algorithm *with* collision detection and advice from `A` has a participant set `P` with
`E[2^T] ≥ c log₂ n / |A|`, where `T` is its number of rounds. (The paper then claims
`E[T] ≥ log₂ (c log₂ n) - b`, which does not follow: `E[2^T] ≥ 2^{E[T]}`, not `≤`.) -/
theorem theorem_3_7_lower_exp {c : ℝ} (hN : NewportBound n c)
    (D : A → Fin n → Measure (List Bool → Bool)) [∀ a v, IsProbabilityMeasure (D a v)]
    (f : Finset (Fin n) → A) :
    ∃ P : Finset (Fin n), P.Nonempty ∧
      ENNReal.ofReal (c * Real.logb 2 n) / Fintype.card A ≤
        ∫⁻ ω, pow2Time P ω ∂(Measure.pi (D (f P))) := by
  have : ∀ a v, IsProbabilityMeasure ((D a v).map simSchedule) := fun _ _ => inferInstance
  obtain ⟨P, hP, h⟩ := theorem_3_6_lower hN (fun a v => (D a v).map simSchedule) f
  exact ⟨P, hP, h.trans (expTime_simulation_le (D (f P)) P)⟩

end Podc.ContentionPredictions
