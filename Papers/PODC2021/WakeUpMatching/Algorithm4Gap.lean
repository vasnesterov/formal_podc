import Papers.PODC2021.WakeUpMatching.Algorithm4
import Mathlib.Tactic.IntervalCases

/-!
# A false step in the proof of Theorem 6.5

The proof of Theorem 6.5 claims that after `k` iterations "at most
`(1 − 1/(2L+2))^k (1 − ε) n` nodes from `S ∪ R` will remain unassigned". This is not true: the
cross-graph maximal matchings may keep matching assigned vertices with unassigned vertices
outside `S ∪ R`.

Instance: the star `K_{1,9}` on `Fin 10` with centre `0`; the partial NAF `f` sends `1 ↦ 0`,
`2 ↦ 0`, `0 ↦ 1` (`S = S ∪ R = {0, 1, 2}`, load `L = 2`, so `(1−ε) n = 3`). The run: the first
call matches `0–1`, iteration `j` matches `0–(j+2)`. After `k = 7` iterations vertex `2 ∈ S` is
still unassigned, although `(1 − 1/6)^7 · 3 < 1`. (Theorem 6.5's coverage *statement* is not
affected: it counts all assigned vertices, see `theorem_6_5_coverage`.)
-/

namespace Podc.WakeUpMatching

open Finset

/-- The star `K_{1,9}` with centre `0`. -/
def star10 : SimpleGraph (Fin 10) where
  Adj i j := i ≠ j ∧ (i = 0 ∨ j = 0)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel star10.Adj := fun i j => inferInstanceAs (Decidable (i ≠ j ∧ _))

instance {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (A : Finset V) :
    DecidableRel (crossGraph G A).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ _))

/-- The matching `{0, c}`. -/
def pairWith (c : Fin 10) (v : Fin 10) : Option (Fin 10) :=
  if v = 0 then some c else if v = c then some 0 else none

/-- The run: call `0` matches `0–1`, iteration `j ∈ [1, 7]` matches `0–(j+2)`. -/
def gapRun : ℕ → Fin 10 → Option (Fin 10)
  | 0 => pairWith 1
  | 1 => pairWith 3
  | 2 => pairWith 4
  | 3 => pairWith 5
  | 4 => pairWith 6
  | 5 => pairWith 7
  | 6 => pairWith 8
  | 7 => pairWith 9
  | _ => fun _ => none

/-- The partial NAF `1 ↦ 0`, `2 ↦ 0`, `0 ↦ 1`. -/
def gapNAF (v : Fin 10) : Option (Fin 10) :=
  if v = 0 then some 1 else if v = 1 ∨ v = 2 then some 0 else none

theorem gapRun_isRun : IsRun star10 7 gapRun := by
  refine ⟨⟨⟨gapRun 0, by decide, by decide⟩, rfl, by unfold PMatching.IsMaximal; decide⟩,
    fun j hj => ⟨⟨gapRun (j + 1), ?_, ?_⟩, rfl, ?_⟩⟩
  · interval_cases j <;> decide
  · interval_cases j <;> decide
  · show ∀ v w, (crossGraph star10 (assigned gapRun j)).Adj v w →
      (gapRun (j + 1) v).isSome ∨ (gapRun (j + 1) w).isSome
    interval_cases j <;> decide

/-- The claim in the proof of Theorem 6.5 fails: after `k = 7` iterations the vertex `2` of
`S ∪ R` is still unassigned, while the claimed bound `(1 − 1/(2L+2))^k · |S ∪ R|` is `< 1`. -/
theorem proof_6_5_step_false :
    IsRun star10 7 gapRun ∧ IsPartialNAF star10 gapNAF ∧ pLoad gapNAF ≤ 2 ∧
      domain gapNAF = {0, 1, 2} ∧ (2 : Fin 10) ∉ assigned gapRun 7 ∧
      (1 - 1 / (2 * 2 + 2) : ℝ) ^ 7 * 3 < 1 := by
  refine ⟨gapRun_isRun, by unfold IsPartialNAF; decide, pLoad_le_iff.2 (by decide), by decide, by decide, by norm_num⟩

end Podc.WakeUpMatching
