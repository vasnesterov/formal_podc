import Papers.PODC2020.BezoutElection.Alg1Term
import Papers.PODC2020.BezoutElection.Alg1Sym

/-!
# Algorithm 1 is correct (Theorem 2)

Godard, Imbs, Raynal, Taubenfeld, PODC 2020, Theorem 2: Algorithm 1 solves leader election
for `n` processes with a single read/write register.

* `alg1_agreement` (safety): all processes that return agree on one identifier `ℓ`, the
  identifier of some process (proof: the invariant `Inv` of `Alg1Inv.lean`).
* `alg1_terminates` (termination): in every fair execution in which all processes invoke
  `elect()`, every process returns (proof: `Alg1Term.lean`).
* `alg1_symmetric`, `alg1_readWrite` (`Alg1Sym.lean`): the algorithm is symmetric (with equality)
  and only uses reads and writes.
* `alg1_exactElection`, `alg1_dElection`: with the bit output "am I elected?", exactly one
  process is elected (exact 1-election).

The agreement statement needs `[Nonempty P]` (with no process there is no identifier to
elect).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection.Alg1

variable {Id : Type} [DecidableEq Id] {R : Type} [Inhabited R]
  {P : Type} [Fintype P] [DecidableEq P]

/-- **Theorem 2 (safety)**: all processes that return agree on one elected identifier `ℓ`,
which is the identifier of some process. -/
theorem alg1_agreement [Nonempty P] (n : ℕ) (out : Id → Id → R) (ids : P → Id)
    (hid : Function.Injective ids) (hn : Fintype.card P = n) (π : P → Equiv.Perm (Fin 1))
    (α : List (Label P (elecObj R))) (hα : ((alg1 Id n out).impl ids π).Valid α)
    (_h1 : OneShot α) :
    ∃ ℓ, (∃ r, ids r = ℓ) ∧ ∀ p a, outputs α p = some a → a = out (ids p) ℓ := by
  obtain ⟨C, hC⟩ := hα
  obtain ⟨-, hN | ⟨L, hL⟩⟩ := inv_run hid hn hC
  · obtain ⟨p⟩ := ‹Nonempty P›
    exact ⟨ids p, ⟨p, rfl⟩, fun q a h => by rw [hN.noout q] at h; cases h⟩
  · exact ⟨ids L, ⟨L, rfl⟩, fun q a h => hL.out q a h⟩

/-- **Theorem 2 (termination)**: when all processes participate and the execution is fair,
every process returns. -/
theorem alg1_terminates (n : ℕ) (out : Id → Id → R) (ids : P → Id)
    (hid : Function.Injective ids) (hn : Fintype.card P = n) (π : P → Equiv.Perm (Fin 1)) :
    Terminates ((alg1 Id n out).impl ids π) := by
  intro e _ hall hfair p
  exact Ctx.terminates ⟨hid, hn, hfair, hall⟩ p

/-- **Theorem 2, bit version**: with the output "am I elected?", exactly one process is
elected in every execution in which all processes return (exact 1-election). -/
theorem alg1_exactElection [Nonempty P] (n : ℕ) (ids : P → Id) (hid : Function.Injective ids)
    (hn : Fintype.card P = n) (π : P → Equiv.Perm (Fin 1)) :
    ExactElection 1 ((alg1 Id n (fun a ℓ => decide (a = ℓ))).impl ids π) := by
  intro α hα h1 hall
  obtain ⟨ℓ, ⟨r, rfl⟩, hout⟩ := alg1_agreement n _ ids hid hn π α hα h1
  have : elected α = {r} := by
    ext p
    simp only [elected, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (hall p)
    rw [hb, hout p b hb]
    simp [hid.eq_iff]
  rw [this, Finset.card_singleton]

/-- **Theorem 2, bit version**: Algorithm 1 solves 1-election. -/
theorem alg1_dElection [Nonempty P] (n : ℕ) (ids : P → Id) (hid : Function.Injective ids)
    (hn : Fintype.card P = n) (π : P → Equiv.Perm (Fin 1)) :
    DElection 1 ((alg1 Id n (fun a ℓ => decide (a = ℓ))).impl ids π) := by
  intro α hα h1 hall
  have := alg1_exactElection n ids hid hn π α hα h1 hall
  omega

end BezoutElection.Alg1
