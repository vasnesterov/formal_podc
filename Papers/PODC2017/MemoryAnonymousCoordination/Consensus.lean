import Papers.PODC2017.MemoryAnonymousCoordination.ConsensusOF

/-!
# Theorems 4.1 and 4.2 of Taubenfeld, *Coordination Without Prior Agreement* (PODC 2017)

The algorithm of Figure 2 (`alg`, see `ConsensusDefs.lean` for the model) with `2n − 1`
memory-anonymous registers solves obstruction-free multi-valued consensus for at most `n`
processes with arbitrary identifiers, **for every** adversarial numbering `π` of the registers:

* `consensus_solves`: agreement and validity (Theorem 4.1, agreement part; Theorem 4.2);
* `consensus_obstructionFree`, `consensus_oneShotOF`: a process running solo decides (Theorem 4.1,
  termination part), for every choice `sel` of line 6 that picks an entry different from
  `(i, mypref)` when there is one (`SelOK`; e.g. `defaultSel`).

The paper's proof of agreement ("each of the other `n − 1` processes might write into one of the
registers overwriting the `(i, v)` value") ignores that collects are not atomic and that other
processes may be poised to write stale preferences; it is repaired by the invariant `Lock` (see
`ConsensusLock.lean`) and a ghost invariant for processes in the middle of a collect
(`ConsensusSafety.lean`).
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Consensus

open Cslib.SharedMemory

variable {P V : Type} [Fintype P] [DecidableEq P] [DecidableEq V] [Inhabited V]

lemma two_mul_sub_one_add_one {n : ℕ} (hn : 1 ≤ n) : 2 * n - 1 + 1 = 2 * n := by omega

lemma one_le_of_card_le [Nonempty P] {n : ℕ} (hcard : Fintype.card P ≤ n) : 1 ≤ n :=
  le_trans Fintype.card_pos hcard

/-- **Theorem 4.1 (agreement) and Theorem 4.2 (validity)** of [Taubenfeld, PODC 2017].
For at most `n` processes (`Fintype.card P ≤ n`, arbitrary identifiers), `2n − 1` registers, any
choice `sel` in line 6 and **every** numbering `π` of the registers by the processes, Figure 2
solves consensus: all decisions are equal, and each is the input of some participant. -/
theorem consensus_solves {n : ℕ} (hcard : Fintype.card P ≤ n)
    (sel : P → V → (Fin (2 * n - 1) → Option (P × V)) → Fin (2 * n - 1))
    (π : P → Equiv.Perm (Fin (2 * n - 1))) :
    ((alg n sel).unnamed π).Solves (consensus P V) := by
  cases isEmpty_or_nonempty P with
  | inl hP =>
    intro α _ _
    exact ⟨fun p => isEmptyElim p, fun p => isEmptyElim p⟩
  | inr hP =>
    exact solves_of_hm (two_mul_sub_one_add_one (one_le_of_card_le hcard)) hcard

/-- **Theorem 4.1 (termination under obstruction-freedom)** of [Taubenfeld, PODC 2017].
From every reachable configuration, a process with a pending consensus operation that runs alone
decides, for every numbering `π` and every choice `sel` in line 6 that selects an entry
different from `(i, mypref)` whenever one exists. -/
theorem consensus_obstructionFree {n : ℕ} (hcard : Fintype.card P ≤ n)
    (sel : P → V → (Fin (2 * n - 1) → Option (P × V)) → Fin (2 * n - 1)) (hsel : SelOK sel)
    (π : P → Equiv.Perm (Fin (2 * n - 1))) :
    ((alg n sel).unnamed π).ObstructionFree := by
  cases isEmpty_or_nonempty P with
  | inl hP => intro C p; exact isEmptyElim p
  | inr hP =>
    exact obstructionFree_of_hm (two_mul_sub_one_add_one (one_le_of_card_le hcard)) hcard hsel

/-- Theorem 4.1, termination part, in the one-shot form used for tasks. -/
theorem consensus_oneShotOF {n : ℕ} (hcard : Fintype.card P ≤ n)
    (sel : P → V → (Fin (2 * n - 1) → Option (P × V)) → Fin (2 * n - 1)) (hsel : SelOK sel)
    (π : P → Equiv.Perm (Fin (2 * n - 1))) :
    ((alg n sel).unnamed π).OneShotOF :=
  Impl.ObstructionFree.oneShotOF _ (consensus_obstructionFree hcard sel hsel π)

/-- **Theorem 4.1 + Theorem 4.2**: Figure 2 is a memory-anonymous obstruction-free consensus
algorithm for at most `n` processes using `2n − 1` registers. -/
theorem figure2_correct {n : ℕ} (hcard : Fintype.card P ≤ n)
    (sel : P → V → (Fin (2 * n - 1) → Option (P × V)) → Fin (2 * n - 1)) (hsel : SelOK sel) :
    ∀ π : P → Equiv.Perm (Fin (2 * n - 1)),
      ((alg n sel).unnamed π).Solves (consensus P V) ∧ ((alg n sel).unnamed π).ObstructionFree :=
  fun π => ⟨consensus_solves hcard sel π, consensus_obstructionFree hcard sel hsel π⟩

/-! ### The hypothesis on line 6 is satisfiable -/

open Classical in
/-- Line 6 made deterministic: some entry different from `(p, x)` if there is one, else `d`. -/
noncomputable def defaultSel {m : ℕ} (d : Fin m) (p : P) (x : V) (view : Fin m → Option (P × V)) :
    Fin m :=
  if h : ∃ k, view k ≠ some (p, x) then h.choose else d

lemma selOK_defaultSel {m : ℕ} (d : Fin m) : SelOK (defaultSel (P := P) (V := V) d) := by
  intro p x view h
  simp only [defaultSel, h, ↓reduceDIte]
  exact h.choose_spec

/-- Non-vacuity: for every `n ≥ 1` there is an admissible `sel`, so Figure 2 is correct for at
most `n` processes and every numbering. -/
theorem figure2_correct' {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card P ≤ n)
    (π : P → Equiv.Perm (Fin (2 * n - 1))) :
    let sel := defaultSel (P := P) (V := V) (⟨0, by omega⟩ : Fin (2 * n - 1))
    ((alg n sel).unnamed π).Solves (consensus P V) ∧ ((alg n sel).unnamed π).ObstructionFree :=
  figure2_correct hcard _ (selOK_defaultSel _) π

end Podc.MemoryAnonymousCoordination.Consensus
