import Papers.PODC2019.AnonymousMutex.Alg1Sym
import Papers.PODC2019.AnonymousMutex.Alg1Safety
import Papers.PODC2019.AnonymousMutex.Alg1Livelock
import Papers.PODC2019.AnonymousMutex.Alg2Sym
import Papers.PODC2019.AnonymousMutex.Alg2Safety
import Papers.PODC2019.AnonymousMutex.Alg2DF
import Papers.PODC2019.AnonymousMutex.OneRegister

/-!
# Main results of Aghazadeh–Imbs–Raynal–Taubenfeld–Woelfel (PODC 2019)

* `rmw_characterization` (§6, §7): for `m ≥ 1` anonymous read-modify-write registers, a symmetric
  deadlock-free mutual exclusion algorithm for the processes `P` (correct for every assignment of
  the anonymity permutations) exists **iff** `m ∈ M(|P|)`. Sufficiency: Algorithm 2
  (Theorems 3, 4); necessity: Theorem 5.
* `rw_necessity` (Theorem 5 / [15]) and `theorem_2_false`: for read/write registers (with
  snapshots) `m ∈ M(n)` is necessary, but the paper's Algorithm 1 does not show sufficiency
  (Theorem 2 fails for `n = 4`, `m = 5`).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex

/-- **Tight characterization for anonymous read-modify-write registers** (§6.2 and §7 of the
paper): there is a symmetric algorithm using `m ≥ 1` anonymous registers accessed only by atomic
read-modify-write operations which solves deadlock-free mutual exclusion for the processes `P`
(with identifiers `ids`) for every choice of the anonymity permutations if and only if
`m ∈ M(|P|)`. -/
theorem rmw_characterization {Id : Type} [DecidableEq Id] {P : Type} [Fintype P] [DecidableEq P]
    (ids : P → Id) (hid : Function.Injective ids) (m : ℕ) (hm : 0 < m) :
    (∃ (V S : Type) (_ : MulAction (Equiv.Perm Id) V) (_ : MulAction (Equiv.Perm Id) S)
        (A : SymAlg mutexObj Id m V S), A.Symmetric ∧ A.NoSnapshot ∧
        ∀ π : P → Equiv.Perm (Fin m),
          (A.impl ids π).MutualExclusion ∧ (A.impl ids π).DeadlockFree) ↔
      m ∈ M (Fintype.card P) := by
  constructor
  · rintro ⟨V, S, iV, iS, A, hA, -, h⟩
    exact theorem_5 hA ids hid h
  · intro hM
    exact ⟨Option Id, Alg2.St Id m, inferInstance, inferInstance, Alg2.alg2 Id m,
      Alg2.alg2_symmetric, fun s k => Alg2.act_ne_snap s k,
      fun π => ⟨Alg2.theorem_3 ids hid π hm, Alg2.theorem_4 ids hid π hm hM⟩⟩

/-- **Necessity for read/write registers** (Theorem 5, which also covers the read/write model with
snapshots of Algorithm 1). -/
theorem rw_necessity {Id V S : Type} [MulAction (Equiv.Perm Id) V] [MulAction (Equiv.Perm Id) S]
    {m : ℕ} {P : Type} [Fintype P] [DecidableEq P] (A : SymAlg mutexObj Id m V S)
    (hA : A.Symmetric) (ids : P → Id) (hid : Function.Injective ids)
    (h : ∀ π : P → Equiv.Perm (Fin m),
      (A.impl ids π).MutualExclusion ∧ (A.impl ids π).DeadlockFree) :
    m ∈ M (Fintype.card P) :=
  theorem_5 hA ids hid h

/-- **Necessity for read/write registers, complete form** (§4.2: `m ∈ M(n) \ {1}`): for at least
two processes, a symmetric read/write(+snapshot) algorithm solving deadlock-free mutual exclusion
for all anonymity permutations needs `m ∈ M(n)` (Theorem 5) and `m ≠ 1` (one register is not
enough, `one_register_impossible`; the paper cites Burns–Lynch for this). -/
theorem rw_necessity' {Id V S : Type} [MulAction (Equiv.Perm Id) V] [MulAction (Equiv.Perm Id) S]
    {m : ℕ} {P : Type} [Fintype P] [DecidableEq P] (hP : 2 ≤ Fintype.card P)
    (A : SymAlg mutexObj Id m V S) (hA : A.Symmetric) (hRW : A.ReadWrite) (ids : P → Id)
    (hid : Function.Injective ids)
    (h : ∀ π : P → Equiv.Perm (Fin m),
      (A.impl ids π).MutualExclusion ∧ (A.impl ids π).DeadlockFree) :
    m ∈ M (Fintype.card P) ∧ m ≠ 1 := by
  refine ⟨theorem_5 hA ids hid h, fun hm1 => ?_⟩
  subst hm1
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card (α := P) (by omega)
  exact one_register_impossible A hRW ids (fun _ => 1) hpq (h _)

/-- Algorithm 1 is a symmetric read/write(+snapshot) algorithm satisfying mutual exclusion
(Theorem 1), but it is not deadlock-free in general (Theorem 2 fails). -/
theorem alg1_summary :
    (∀ (Id : Type) [DecidableEq Id] (m : ℕ), (Alg1.alg1 Id m).Symmetric ∧ (Alg1.alg1 Id m).ReadWrite) ∧
    (∀ {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [Fintype P] [DecidableEq P]
      (ids : P → Id), Function.Injective ids → ∀ π : P → Equiv.Perm (Fin m),
      1 < m → m ∈ M (Fintype.card P) → ((Alg1.alg1 Id m).impl ids π).MutualExclusion) ∧
    ∃ (ids : Fin 4 → Fin 4) (π : Fin 4 → Equiv.Perm (Fin 5)), Function.Injective ids ∧
      1 < 5 ∧ 5 ∈ M (Fintype.card (Fin 4)) ∧ ¬ ((Alg1.alg1 (Fin 4) 5).impl ids π).DeadlockFree :=
  ⟨fun _ _ _ => ⟨Alg1.alg1_symmetric, Alg1.alg1_readWrite⟩,
    fun ids hid π h1 hM => Alg1.theorem_1_of_M ids hid π h1 hM, theorem_2_false⟩

end AnonymousMutex
