import Papers.PODC2025.StrangerFreeTasks.LowerBound
import Papers.PODC2025.StrangerFreeTasks.Alg1Safety
import Papers.PODC2025.StrangerFreeTasks.Alg1OF
import Papers.PODC2025.StrangerFreeTasks.Alg1Livelock
import Papers.PODC2025.StrangerFreeTasks.TwoProcess
import Papers.PODC2025.StrangerFreeTasks.Alg1WaitFreeK1

/-!
# Main results of "Brief Announcement: Stranger-Free Tasks" (PODC 2025)

* Theorem 2.1: `theorem_2_1` (wait-free), `theorem_2_1_obstructionFree`, covering form
  `covering_of_strangerFree` (`StrangerFree.lean`); tightness for `n = 2`: `theorem_2_1_tight`
  (`TwoProcess.lean`).
* Theorem 3.1 as stated (wait-free upper bound) is **not** established by the paper's Algorithm 1:
  `theorem_3_1_alg1_not_waitFree` (for every `k ≥ 2`, already with two processes).
* `k = 1`: Theorem 3.1 holds as stated — `theorem_3_1_k1` (Algorithm 1 is wait-free for `k = 1`
  and any, possibly infinite, set of processes).
* What holds for all `k`: `theorem_3_1_obstructionFree` — for every `k ≥ 1`, `k`-bounded lattice agreement is
  solved obstruction-free by Algorithm 1 with `k + 1` registers for every set of processes (in
  particular infinitely many), and no obstruction-free (or wait-free) algorithm solves it for
  `k + 1` processes with `k` registers; `theorem_3_1_lowerBound` is the wait-free lower bound.
-/

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory Impl

/-- **Theorem 3.1, obstruction-free version** (what survives of Theorem 3.1). For every `k ≥ 1`:
(1) for every set of processes `P` (finite or infinite), Algorithm 1 solves `k`-bounded lattice
agreement obstruction-free using `k + 1` registers, every process being allowed to participate;
(2) for `k + 1` processes, every obstruction-free algorithm (with every process allowed to
participate) uses at least `k + 1` registers. -/
theorem theorem_3_1_obstructionFree (k : ℕ) (hk : 1 ≤ k) :
    (∀ (P : Type) [DecidableEq P], (alg1 (P := P) k).Solves (boundedLA P k) ∧
      (alg1 (P := P) k).ObstructionFree ∧ (∀ p x, (alg1 (P := P) k).allowed p x) ∧
      Fintype.card (Fin (k + 1)) = k + 1) ∧
    (∀ (P : Type) [DecidableEq P] [Fintype P], Fintype.card P = k + 1 →
      ∀ (ι V L : Type) [DecidableEq ι] [Fintype ι] (v₀ : V)
        (I : Impl (laObj P) (RegFamily ι V v₀) P L),
        I.Solves (boundedLA P k) → I.ObstructionFree → (∀ p, I.allowed p ()) →
        k + 1 ≤ Fintype.card ι) :=
  ⟨fun P _ => ⟨alg1_solves k, alg1_obstructionFree k, fun _ _ => trivial, by simp⟩,
    fun P _ _ hP ι V L _ _ v₀ I hI hof hin => boundedLA_lowerBound hk hP I hI hof hin⟩

/-- **Lower bound of Theorem 3.1** (wait-free, as in the paper): `k`-bounded lattice agreement is not
wait-free solvable with `k` registers for `k + 1` processes. -/
theorem theorem_3_1_lowerBound (k : ℕ) (hk : 1 ≤ k) (P : Type) [DecidableEq P] [Fintype P]
    (hP : Fintype.card P = k + 1) (ι V L : Type) [DecidableEq ι] [Fintype ι] (v₀ : V)
    (I : Impl (laObj P) (RegFamily ι V v₀) P L) (hI : I.Solves (boundedLA P k))
    (hwf : I.WaitFree) (hin : ∀ p, I.allowed p ()) : k + 1 ≤ Fintype.card ι :=
  boundedLA_lowerBound_waitFree hk hP I hI hwf hin

/-- **The upper bound of Theorem 3.1 fails for the paper's algorithm**: for every `k ≥ 2`,
Algorithm 1 is not wait-free, already with two processes (`exists_livelock`: a one-shot execution
in which both processes stay pending forever and take infinitely many steps). -/
theorem theorem_3_1_alg1_not_waitFree (k : ℕ) (hk : 2 ≤ k) (P : Type) [DecidableEq P] (a b : P)
    (hab : a ≠ b) : ¬ (alg1 (P := P) k).WaitFree :=
  alg1_not_waitFree k hk a b hab

/-- **Theorem 3.1 for `k = 1`, as stated in the paper.** `1`-bounded lattice agreement is solved
wait-free by Algorithm 1 with `2` registers for every set of processes (in particular infinitely
many), and is not wait-free solvable with fewer than `2` registers by `2` processes. -/
theorem theorem_3_1_k1 :
    (∀ (P : Type) [DecidableEq P], (alg1 (P := P) 1).Solves (boundedLA P 1) ∧
      (alg1 (P := P) 1).WaitFree ∧ (∀ p x, (alg1 (P := P) 1).allowed p x) ∧
      Fintype.card (Fin (1 + 1)) = 2) ∧
    (∀ (P : Type) [DecidableEq P] [Fintype P], Fintype.card P = 2 →
      ∀ (ι V L : Type) [DecidableEq ι] [Fintype ι] (v₀ : V)
        (I : Impl (laObj P) (RegFamily ι V v₀) P L),
        I.Solves (boundedLA P 1) → I.WaitFree → (∀ p, I.allowed p ()) → 2 ≤ Fintype.card ι) :=
  ⟨fun P _ => ⟨alg1_solves 1, alg1_waitFree_one, fun _ _ => trivial, by simp⟩,
    fun P _ _ hP ι V L _ _ v₀ I hI hwf hin => boundedLA_lowerBound_waitFree le_rfl hP I hI hwf hin⟩

end Cslib.SharedMemory.StrangerFree
