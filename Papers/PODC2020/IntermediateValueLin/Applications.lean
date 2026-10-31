import Papers.PODC2020.IntermediateValueLin.Bounded
import Papers.PODC2020.IntermediateValueLin.BatchedCounter
import Papers.PODC2020.IntermediateValueLin.CountMin
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Theorem 1 applied

Non-vacuity check of Definitions 2–4 and Theorem 1: Algorithm 2 (a deterministic algorithm, i.e. a
randomized one with a single coin flip vector) is a randomized IVL implementation of the batched
counter (`alg2_randIVL`), the exact batched counter is a sequential `(0, 0)`-bounded object with
respect to itself (`bc_seqBounded`), so by Theorem 1 every read of Algorithm 2 returns a value
between the least and the largest value it can get in a linearization (`alg2_concBounded`).

The combination used in Section 5 ("combining Lemma 1 and Theorem 1"): if the hash functions of the
CountMin sketch are drawn at random (`hash : Ω → Fin d → E → Fin w`) and the sequential sketch is an
`(ε, δ)`-bounded `I` object, the concurrent sketch PCM is a concurrent `(ε, δ)`-bounded `I` object
(`pcm_concBounded`). The sequential error analysis of CountMin itself (Cormode–Muthukrishnan) is a
hypothesis, so Corollary 1's concrete bound is not derived.
-/

open Cslib.SharedMemory MeasureTheory
open scoped ENNReal

namespace Podc.IntermediateValueLin.Alg2

variable {n : ℕ}

/-- Algorithm 2 as a randomized algorithm with a trivial coin (`Ω = Unit`) is an IVL
implementation in the sense of Definition 2. -/
theorem alg2_randIVL :
    RandIVL (Ω := Unit) (fun _ => bcQ) (fun _ α => (alg2 n).Valid α) :=
  randIVL_of_canon _ _ (fun _ _ hv => hv.wellFormed) (fun _ _ hv => alg2_sandwich hv)

/-- The batched counter is a sequential `(0, 0)`-bounded object with respect to itself. -/
theorem bc_seqBounded :
    SeqBounded (A := batchedCounter) (Fin n) (fun _ : Unit => bcQ) bcQ (Measure.dirac ()) 0 0 := by
  intro L a _ _
  constructor <;>
  · refine le_trans ?_ (le_of_eq (measure_univ (μ := Measure.dirac ())).symm) |>.trans
      (measure_mono fun c _ => ?_)
    · simp
    · intro v w hv hw
      rw [hv] at hw; cases hw; simp

/-- **Theorem 1** applied to Algorithm 2: every read returns a value between `v_min` and `v_max`
(with probability `1`, there being no randomness). -/
theorem alg2_concBounded :
    ConcBounded (Ω := Unit) (fun _ α => (alg2 n).Valid α) bcQ (Measure.dirac ()) 0 0 :=
  theorem1 _ bc_seqBounded alg2_randIVL

end Podc.IntermediateValueLin.Alg2

namespace Podc.IntermediateValueLin

/-- Lemma 1 in the form of Definition 2: PCM with randomly drawn hash functions is a randomized
IVL implementation of the randomized CountMin specification (the linearizations `H₁`, `H₂` of the
proof of Lemma 1 do not depend on the hash functions). -/
theorem pcm_randIVL {Ω : Type*} [MeasurableSpace Ω] {E : Type} [DecidableEq E] {d w : ℕ} {P : Type} [DecidableEq P]
    (hash : Ω → Fin d → E → Fin w) :
    RandIVL (A := cmIface E) (fun c => cmSpec (hash c)) (fun c α => (pcm (hash c) P).Valid α) :=
  randIVL_of_canon _ _ (fun _ _ hv => hv.wellFormed) (fun c _ hv => pcm_sandwich (hash c) hv)

/-- Lemma 1 + **Theorem 1** (Section 5): if the sequential CountMin sketch with random hash
functions is an `(ε, δ)`-bounded `I` object, then so is the concurrent sketch PCM. -/
theorem pcm_concBounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {E : Type} [DecidableEq E] {d w : ℕ} {P : Type} [DecidableEq P]
    (hash : Ω → Fin d → E → Fin w) (I : QSpec (CMOp E) ℕ) (ε : ℕ) (δ : ℝ≥0∞)
    (hseq : SeqBounded (A := cmIface E) P (fun c => cmSpec (hash c)) I μ ε δ) :
    ConcBounded (fun c α => (pcm (hash c) P).Valid α) I μ ε δ :=
  theorem1 μ hseq (pcm_randIVL hash)

end Podc.IntermediateValueLin
