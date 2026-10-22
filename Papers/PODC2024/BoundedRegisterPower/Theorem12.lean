import Papers.PODC2024.BoundedRegisterPower.Alg1
import Papers.PODC2024.BoundedRegisterPower.Alg2Correct
import Papers.PODC2024.BoundedRegisterPower.BMZ

/-!
# Theorem 1.2: 3-bit registers are universal for two processes

Algorithm 2 with Algorithm 1 as its ε-agreement subroutine. Besides the write-once register for
the task input (the paper's special input register `I_i`), every process uses the two registers of
Algorithm 1: its write-once input register (`⊥`, `0` or `1`) and its 1-bit register — `6 ≤ 2³`
values, i.e. one 3-bit register.

The hypothesis `BMZ Δ` is the Biran–Moran–Zaks characterization (Lemma 5.7 of the full version):
by [BMZ 1990], which the paper cites, every task that two processes solve wait-free with unbounded
registers satisfies it. We do not formalize that direction.
-/

namespace Podc.BoundedRegisterPower

open Cslib.SWMR

/-- Algorithm 1 satisfies the black-box interface used by Algorithm 2. -/
theorem alg1_eBox (k : ℕ) (hk : 1 ≤ k) : EBox (alg1 k) (2 * k + 1) (2 * k + 3) where
  safe x τ := (alg1_solves k hk).1 x τ
  zero x τ p h := (alg1_lemma_5_6 k hk x τ p).1 h
  one x τ p h := (alg1_lemma_5_6 k hk x τ p).2 h
  mid x τ p m hm h0 h1 := by
    obtain ⟨hne, hmem⟩ := alg1_mid k hk x τ p hm h0 h1
    refine ⟨hne, by_contra fun hp => ?_⟩
    rw [Alg.run_mem_of_notMem _ _ hp] at hmem
    simp [Alg.initCfg, alg1] at hmem
  bound x τ p h := alg1_decides k hk x τ p h

instance (i : Bool) : Fintype (Alg1Reg i) := by cases i <;> dsimp [Alg1Reg] <;> infer_instance

/-- The coordination registers of a process (Algorithm 1's input register and 1-bit register)
take `6 ≤ 2³` values: they fit in one 3-bit register. -/
theorem card_alg1Reg : Fintype.card (∀ i : Bool, Alg1Reg i) = 6 := by
  rw [Fintype.card_pi]; rfl

/-- **Theorem 1.2** (from Lemma 5.7). Every two-process task with finitely many inputs that
satisfies the Biran–Moran–Zaks conditions — by [BMZ], every task solvable wait-free by two
processes with unbounded registers — is solved wait-free by Algorithm 2 (with Algorithm 1 inside),
whose registers are the write-once task-input register and the 3 bits of `∀ i, Alg1Reg i`. -/
theorem theorem_1_2 {In O : Type} [Fintype In] [DecidableEq In]
    {Δ : (Bool → In) → (Bool → O) → Prop} (h : BMZ Δ) :
    ∃ A : Alg Bool (Option Bool) (Reg2 In Alg1Reg) In O, A.Solves 1 (taskOf Δ) := by
  obtain ⟨N, hN⟩ := exists_pathSystem h
  obtain ⟨PS⟩ := hN (2 * (N + 1) + 1) (by omega)
  exact ⟨alg2 (alg1 (N + 1)) PS, alg2_solves (alg1_eBox (N + 1) (by omega)) (by omega)⟩

end Podc.BoundedRegisterPower

namespace Podc.BoundedRegisterPower

/-- Non-vacuity: a task satisfying the Biran–Moran–Zaks conditions (every output is legal). -/
example : BMZ (fun (_ : Bool → Bool) (_ : Bool → Unit) => True) :=
  ⟨Set.univ, fun _ _ _ _ _ _ _ => Relation.ReflTransGen.single
      ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, true, rfl⟩,
    fun _ _ => ⟨(), fun _ => ⟨fun _ => (), trivial, trivial, rfl⟩⟩⟩

end Podc.BoundedRegisterPower
