import Papers.PODC2014.RandomizationTwoHop.Model
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- CSLib candidate (paper-local for now; see README)

/-!
# The probabilistic definition of Las Vegas solvability

The paper's definition (§1.1): `A` solves `Π` if on every instance (1) every node outputs within
finite time **with probability 1**, and (2) every output labelling obtained **with positive
probability** is valid. The random bits are independent fair coins, one per node and round:
`bitMeasure V` is the product measure on `V × ℕ → Bool`.

`SolvesAS` is this definition; `Solves` (`Model.lean`) is the combinatorial version used in the
proofs. `SolvesAS.solves`: the probabilistic definition implies the combinatorial one (every
cylinder of finitely many fixed bits has positive probability). Hence `GRAN_AS.gran`: membership
in GRAN in the paper's (probabilistic) sense implies our `GRAN`, so Theorems 1 and 2 hold for the
paper's definition. (Validity conditions (2) of both definitions are equivalent, `Solves`'s
termination condition is weaker than termination with probability 1.)
-/

namespace Podc.RandomizationTwoHop

open MeasureTheory Cslib.PortNumbering

/-- A fair coin. -/
noncomputable def coin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure coin := by unfold coin; infer_instance

/-- Independent fair coins for every node and round. -/
noncomputable def bitMeasure (V : Type) : Measure (V × ℕ → Bool) :=
  Measure.infinitePi fun _ => coin

variable {In Out : Type}

/-- The paper's definition of "A solves Π" (Las Vegas): termination with probability 1, and
validity of every output labelling obtained with positive probability. -/
def SolvesAS (A : RAlg In Out) (Pb : Problem In Out) : Prop :=
  ∀ X : LGraph In, Pb.inst X → ∀ P : PNGraph X.V, P.IsSimple → P.toSimpleGraph = X.G →
    (∀ᵐ β ∂(bitMeasure X.V), ∃ t, ∀ v, (A.decided P X.lab (Function.curry β) t v).isSome) ∧
    (∀ o : X.V → Out,
      bitMeasure X.V {β | ∃ t, ∃ h : ∀ v, (A.decided P X.lab (Function.curry β) t v).isSome,
          (fun v => (A.decided P X.lab (Function.curry β) t v).get (h v)) = o} ≠ 0 →
        Pb.valid X o)

/-- GRAN with the paper's probabilistic notion of solvability. -/
def GRAN_AS (Pb : Problem In Out) : Prop :=
  (∃ A : RAlg In Out, SolvesAS A Pb) ∧ ∃ B : RAlg In Bool, SolvesAS B (decision Pb.inst)

theorem coin_singleton_ne_zero (b : Bool) : coin {b} ≠ 0 := by
  unfold coin
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
  simp [PMF.uniformOfFintype_apply]

/-- Cylinders (finitely many bits fixed) have positive probability. -/
theorem bitMeasure_cylinder_ne_zero {V : Type} [Finite V] (β₀ : V → ℕ → Bool) (t₀ : ℕ) :
    bitMeasure V {β | ∀ v k, k < t₀ → β (v, k) = β₀ v k} ≠ 0 := by
  classical
  have := Fintype.ofFinite V
  have hset : {β : V × ℕ → Bool | ∀ v k, k < t₀ → β (v, k) = β₀ v k} =
      Set.pi ((Finset.univ ×ˢ Finset.range t₀ : Finset (V × ℕ)) : Set (V × ℕ)) (fun i => {β₀ i.1 i.2}) := by
    ext β; simp
  rw [hset, bitMeasure, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  exact Finset.prod_ne_zero_iff.2 fun i _ => coin_singleton_ne_zero _

/-- The paper's probabilistic definition implies the combinatorial one used in the proofs. -/
theorem SolvesAS.solves {A : RAlg In Out} {Pb : Problem In Out} (h : SolvesAS A Pb) :
    Solves A Pb := by
  intro X hX P hPs hPG
  obtain ⟨hterm, hval⟩ := h X hX P hPs hPG
  refine ⟨fun β₀ t₀ => ?_, fun β t hall => ?_⟩
  · -- the cylinder has positive measure, the non-terminating set has measure zero
    by_contra hcon
    push Not at hcon
    apply bitMeasure_cylinder_ne_zero β₀ t₀
    refine measure_mono_null (fun β hβ => ?_) (ae_iff.1 hterm)
    intro ht
    obtain ⟨t, ht⟩ := ht
    obtain ⟨v, hv⟩ := hcon (Function.curry β) (fun v k hk => hβ v k hk) t
    exact hv (ht v)
  · apply hval
    apply ne_of_gt
    refine lt_of_lt_of_le (pos_iff_ne_zero.2 (bitMeasure_cylinder_ne_zero β t))
      (measure_mono fun β' hβ' => ?_)
    have hc : ∀ v k, k < t → Function.curry β' v k = β v k := hβ'
    have he := RAlg.decided_congr_bits (A := A) (P := P) (x := X.lab) hc
    refine ⟨t, fun v => by rw [he]; exact hall v, ?_⟩
    funext v
    simp only [he]

theorem GRAN_AS.gran {Pb : Problem In Out} (h : GRAN_AS Pb) : GRAN Pb :=
  ⟨h.1.elim fun A hA => ⟨A, hA.solves⟩, h.2.elim fun B hB => ⟨B, hB.solves⟩⟩

end Podc.RandomizationTwoHop
