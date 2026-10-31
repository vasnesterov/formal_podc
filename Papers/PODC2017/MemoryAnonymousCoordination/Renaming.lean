import Papers.PODC2017.MemoryAnonymousCoordination.RenamingOF

/-!
# Theorems 5.1–5.3 of Taubenfeld, *Coordination Without Prior Agreement* (PODC 2017)

The algorithm of Figure 3 (`alg`, see `RenamingDefs.lean` for the model) with `2n − 1`
memory-anonymous registers is an obstruction-free adaptive perfect renaming algorithm for at most
`n` processes with arbitrary identifiers, **for every** adversarial numbering `π` of the
registers and every admissible choice `S` of lines 9 and 15 (`Sel.OK`; e.g. `defaultSel`):

* `renaming_solves`: names are distinct (Theorem 5.2) and, when `k` processes participate, in
  `{1, …, k}` (Theorem 5.3; in particular in `{1, …, n}`);
* `renaming_obstructionFree`: a process running solo returns (Theorem 5.1).

The paper's proof of uniqueness (Theorem 5.2) is the same one-paragraph argument as for
consensus: "each one of the other `n − 1` processes might write into one of the registers
overwriting a value", ignoring non-atomic collects, stale pending writes, processes of other
rounds and catch-up. It is repaired by a per-round lock (`RenamingLock.lean`) whose bad records
are those of a round `≤ r` other than the winner's, and which records that every record of a
later round names the round-`r` winner in its history; the ghost invariant for collects and the
well-formedness of histories are in `RenamingSafety.lean`. The paper's proof of adaptivity
("if only `k < n` processes participate, the algorithm will terminate after `k` rounds") is
replaced by the observation that a process acquiring the name `a` knows a history naming `a − 1`
other participants.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Renaming

open Cslib.SharedMemory

variable {P : Type} [Fintype P] [DecidableEq P]

lemma two_mul_sub_one_add_one {n : ℕ} (hn : 1 ≤ n) : 2 * n - 1 + 1 = 2 * n := by omega

/-- **Theorem 5.2 (uniqueness) and Theorem 5.3 (adaptivity)** of [Taubenfeld, PODC 2017].
For at most `n ≥ 1` processes (`Fintype.card P ≤ n`, arbitrary identifiers), `2n − 1` registers,
every admissible choice `S` of lines 9 and 15 and **every** numbering `π` of the registers by the
processes, Figure 3 solves adaptive perfect renaming: in every (finite, one-shot) execution the
names acquired are distinct, and each is in `{1, …, k}` where `k` is the number of processes that
invoked the operation. -/
theorem renaming_solves {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card P ≤ n)
    (S : Sel P (2 * n - 1)) (hS : S.OK) (π : P → Equiv.Perm (Fin (2 * n - 1))) :
    ((alg n S).unnamed π).Solves (adaptiveRenaming P) :=
  solves_of_hm (two_mul_sub_one_add_one hn) hcard hS

/-- **Theorem 5.1 (termination under obstruction-freedom)** of [Taubenfeld, PODC 2017].
From every reachable configuration, a process with a pending renaming operation that runs alone
returns, for every numbering `π` and every admissible choice `S` of lines 9 and 15. -/
theorem renaming_obstructionFree {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card P ≤ n)
    (S : Sel P (2 * n - 1)) (hS : S.OK) (π : P → Equiv.Perm (Fin (2 * n - 1))) :
    ((alg n S).unnamed π).ObstructionFree :=
  obstructionFree_of_hm (two_mul_sub_one_add_one hn) hcard hS

/-- Theorem 5.1 in the one-shot form used for tasks. -/
theorem renaming_oneShotOF {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card P ≤ n)
    (S : Sel P (2 * n - 1)) (hS : S.OK) (π : P → Equiv.Perm (Fin (2 * n - 1))) :
    ((alg n S).unnamed π).OneShotOF :=
  Impl.ObstructionFree.oneShotOF _ (renaming_obstructionFree hn hcard S hS π)

/-- **Theorems 5.1–5.3**: Figure 3 is a memory-anonymous obstruction-free adaptive perfect
renaming algorithm for at most `n` processes using `2n − 1` registers (in the sense `RenOK` of
Theorem 6.5, which shows that `n − 1` registers do not suffice). -/
theorem figure3_correct {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card P ≤ n)
    (S : Sel P (2 * n - 1)) (hS : S.OK) :
    ∀ π : P → Equiv.Perm (Fin (2 * n - 1)),
      RenOK (alg n S) π ∧ ((alg n S).unnamed π).ObstructionFree :=
  fun π => ⟨⟨renaming_solves hn hcard S hS π, renaming_oneShotOF hn hcard S hS π⟩,
    renaming_obstructionFree hn hcard S hS π⟩

/-! ### The hypotheses on lines 9 and 15 are satisfiable -/

open Classical in
/-- Lines 9 and 15 made deterministic: some entry with the maximal round, resp. some entry
different from the own record, if there is one; else `d`. -/
noncomputable def defaultSel {m : ℕ} (d : Fin m) : Sel P m where
  up _ _ V := if h : ∃ k, rdOf (V k) = maxRd V then h.choose else d
  tgt p s V := if h : ∃ k, V k ≠ some (p, s) then h.choose else d

lemma defaultSel_ok {m : ℕ} (d : Fin m) : (defaultSel (P := P) d).OK := by
  refine ⟨?_, ?_⟩
  · intro p s V h
    have hex := exists_maxRd (V := V) (by omega)
    simp only [defaultSel, hex, ↓reduceDIte]
    exact hex.choose_spec
  · intro p s V h
    simp only [defaultSel, h, ↓reduceDIte]
    exact h.choose_spec

/-- Non-vacuity: for every `n ≥ 1` there is an admissible choice of lines 9 and 15, so Figure 3
is correct for at most `n` processes and every numbering. -/
theorem figure3_correct' {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card P ≤ n)
    (π : P → Equiv.Perm (Fin (2 * n - 1))) :
    let S := defaultSel (P := P) (⟨0, by omega⟩ : Fin (2 * n - 1))
    ((alg n S).unnamed π).Solves (adaptiveRenaming P) ∧ ((alg n S).unnamed π).ObstructionFree :=
  ⟨renaming_solves hn hcard _ (defaultSel_ok _) π,
    renaming_obstructionFree hn hcard _ (defaultSel_ok _) π⟩

end Podc.MemoryAnonymousCoordination.Renaming
