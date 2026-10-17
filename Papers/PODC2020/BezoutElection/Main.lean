import Papers.PODC2020.BezoutElection.Necessity
import Papers.PODC2020.BezoutElection.Alg1Main
import Papers.PODC2020.BezoutElection.Alg1Sym
import Papers.PODC2020.BezoutElection.Bezout

/-!
# Main results

Godard, Imbs, Raynal, Taubenfeld, PODC 2020.

* Theorem 1 (`theorem_1_1`, `theorem_1_2`) and the necessity parts of Corollaries 1–3
  (`Necessity.lean`).
* Theorem 2 (`Alg1.alg1_agreement`, `Alg1.alg1_terminates`, `Alg1.alg1_symmetric`,
  `Alg1.alg1_readWrite`).
* `one_register_leader_election`: with a single read/write register (`m = 1`, so
  `gcd(m, n) = 1`) a symmetric algorithm solves leader election for every `n ≥ 1` — the case
  `m = 1` of the sufficiency direction of Corollary 1, which refutes Styer–Peterson's
  conjecture that three registers are needed. It also shows that the hypotheses of Theorem 1
  are satisfiable (`theorem_1_nonvacuous`).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection

/-- **Section 3 / Corollary 1 for `m = 1`**: Algorithm 1 is a symmetric read/write algorithm on
one register that, for every anonymity permutation, terminates and elects exactly one process
(bit outputs), for any `n ≥ 1` processes with distinct identifiers. -/
theorem one_register_leader_election (Id : Type) [DecidableEq Id] {P : Type} [Fintype P]
    [DecidableEq P] [Nonempty P] (ids : P → Id) (hid : Function.Injective ids) :
    ∃ (A : SymAlg (elecObj Bool) Id 1 (Alg1.Reg Id) (Alg1.St Id)),
      A.Symmetric ∧ A.ReadWrite ∧ ∀ π, Terminates (A.impl ids π) ∧
        ExactElection 1 (A.impl ids π) ∧ DElection 1 (A.impl ids π) :=
  ⟨Alg1.alg1 Id (Fintype.card P) (fun a ℓ => decide (a = ℓ)),
    Alg1.alg1_symmetric _ _ (fun σ a b => by simp [σ.injective.eq_iff]),
    Alg1.alg1_readWrite _ _,
    fun π => ⟨Alg1.alg1_terminates _ _ ids hid rfl π, Alg1.alg1_exactElection _ ids hid rfl π,
      Alg1.alg1_dElection _ ids hid rfl π⟩⟩

/-- The hypotheses of Theorem 1 are satisfiable: for `m = 1` and `d = 1` Algorithm 1 meets
them, and indeed `gcd(1, n) = 1 ≤ 1`. -/
theorem theorem_1_nonvacuous (Id : Type) [DecidableEq Id] {P : Type} [Fintype P]
    [DecidableEq P] [Nonempty P] (ids : P → Id) (hid : Function.Injective ids) :
    ∃ (A : SymAlg (elecObj Bool) Id 1 (Alg1.Reg Id) (Alg1.St Id)), A.Symmetric ∧
      ∀ π, Terminates (A.impl ids π) ∧ DElection 1 (A.impl ids π) := by
  obtain ⟨A, hA, -, h⟩ := one_register_leader_election Id ids hid
  exact ⟨A, hA, fun π => ⟨(h π).1, (h π).2.2⟩⟩

end BezoutElection
