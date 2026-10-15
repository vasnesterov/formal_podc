import Cslib.Computability.Distributed.SharedMemory.BinaryReduction
import Papers.PODC2016.ComplexityHierarchy.BufferLB
import Papers.PODC2016.ComplexityHierarchy.FetchInc
import Papers.PODC2016.ComplexityHierarchy.MaxRegister
import Papers.PODC2016.ComplexityHierarchy.TestAndSet

/-!
# The lower bounds for `m`-valued consensus (`m ≥ 2`), in particular for `n`-consensus

The paper states its lower bounds for binary consensus and notes that "lower bounds for binary
consensus also apply to `n`-consensus". Using the reduction `Impl.toBinary`
(`Cslib/Computability/Distributed/SharedMemory/BinaryReduction.lean`), we restate them for consensus on `Fin m`, `m ≥ 2`
(with the standard validity condition and one-shot obstruction-freedom).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory Impl

variable {P L : Type} [DecidableEq P] [Fintype P] {m : ℕ}

/-- Theorem 6.8 for `m`-valued consensus. -/
theorem theorem_6_8_multivalued {ι V : Type} [DecidableEq ι] [Fintype ι] {ℓ : ℕ} [NeZero m] (hm : 2 ≤ m)
    (I : Impl (taskObj (Fin m) (Fin m)) (fun _ : ι => bufferSpec ℓ V) P L)
    (hS : I.Solves (consensus P (Fin m))) (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v)
    (hℓ : 1 ≤ ℓ) (hn : 2 ≤ Fintype.card P) : Fintype.card P - 1 ≤ ℓ * Fintype.card ι :=
  theorem_6_8 (I.toBinary (⟨0, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin m))
    (solves_toBinary I _ _ (by simp [Fin.ext_iff]) hS) (oneShotOF_toBinary I _ _ hof)
    (fun p b => hall p _) hℓ hn

/-- Theorem 7.5 for `m`-valued consensus. -/
theorem theorem_7_5_multivalued {R V : Type} [DecidableEq R] [Fintype R] {ℓ : ℕ} [NeZero m] (hm : 2 ≤ m)
    (I : Impl (taskObj (Fin m) (Fin m)) (MB R ℓ V) P L)
    (hS : I.Solves (consensus P (Fin m))) (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v)
    (hℓ : 1 ≤ ℓ) (hn : 2 ≤ Fintype.card P) : Fintype.card P - 1 ≤ 2 * ℓ * Fintype.card R :=
  theorem_7_5 (I.toBinary (⟨0, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin m))
    (solves_toBinary I _ _ (by simp [Fin.ext_iff]) hS) (oneShotOF_toBinary I _ _ hof)
    (fun p b => hall p _) hℓ hn

/-- Theorem 4.1 for `m`-valued consensus. -/
theorem theorem_4_1_multivalued {X : Type} [LinearOrder X] [Inhabited X] [NeZero m] (hm : 2 ≤ m)
    (I : Impl (taskObj (Fin m) (Fin m)) (fun _ : Unit => maxReg X) P L)
    (hS : I.Solves (consensus P (Fin m))) (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v)
    (hn : 2 ≤ Fintype.card P) : False :=
  theorem_4_1 (I.toBinary (⟨0, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin m))
    (solves_toBinary I _ _ (by simp [Fin.ext_iff]) hS) (oneShotOF_toBinary I _ _ hof)
    (fun p b => hall p _) hn

/-- Theorem 5.1 for `m`-valued consensus. -/
theorem theorem_5_1_multivalued [NeZero m] (hm : 2 ≤ m)
    (I : Impl (taskObj (Fin m) (Fin m)) (fun _ : Unit => faiLoc) P L)
    (hS : I.Solves (consensus P (Fin m))) (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v)
    (hn : 2 ≤ Fintype.card P) : False :=
  theorem_5_1 (I.toBinary (⟨0, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin m))
    (solves_toBinary I _ _ (by simp [Fin.ext_iff]) hS) (oneShotOF_toBinary I _ _ hof)
    (fun p b => hall p _) hn

/-- **Theorem 9.2** as stated in the paper: for `n ≥ 3`, `n`-consensus (here: `m`-valued
consensus for any `m ≥ 2`, in particular `m = n`) cannot be solved with a bounded (finite) number
of locations supporting only `read()` and `test-and-set()`. -/
theorem theorem_9_2_multivalued {ι : Type} [DecidableEq ι] [Fintype ι] [NeZero m] (hm : 2 ≤ m)
    (I : Impl (taskObj (Fin m) (Fin m)) (fun _ : ι => tasLoc) P L)
    (hS : I.Solves (consensus P (Fin m))) (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v)
    (hn : 3 ≤ Fintype.card P) : False :=
  theorem_9_2 (I.toBinary (⟨0, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin m))
    (solves_toBinary I _ _ (by simp [Fin.ext_iff]) hS) (oneShotOF_toBinary I _ _ hof)
    (fun p b => hall p _) hn

end Cslib.SharedMemory.ComplexityHierarchy
