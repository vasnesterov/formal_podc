import Mathlib
import Papers.PODC2023.RuntimeVerification.Theorems

/-!
# Lemma 7.4 is false as stated

Lemma 7.4 claims that for every tight execution `E` of `A*`, `E` and `X(λ_E)` are equivalent
(same process subhistories). This fails when a pending operation has executed its `N.Write` but
appears in no view: `X(λ_E)` only contains the operations that appear in views.

Counterexample (two processes, the second one idle): process `0`; its first operation completes (steps 0–7 at times 0–7: invocation,
`N.Write`, `A`, `N.Snapshot`, response, `M.Write`, `M.Snapshot`), then it invokes a second operation
and executes its `N.Write` (times 8, 9) and nothing else. The execution is tight. Its history has two
operations, `X(λ_E)` only one.

The consequence actually used later (Corollary 7.1: `E ∈ O ⟺ X(λ_E) ∈ O` for `O ∈ GenLin`) is
still true, by prefix closure; our proofs (`Theorems.lean`) avoid Lemma 7.4 altogether.
-/

namespace Podc2023.RuntimeVerification

open Cslib.SharedMemory.HerlihyWing Sketch

/-- The counterexample execution. -/
def ce74 : Exec 2 Unit Unit ℕ :=
  ⟨fun p => if p = 0 then 10 else 0, fun _ _ => (), fun _ _ => (), fun _ i => i⟩

theorem ce74_len {p : Fin 2} {i : ℕ} (h : i < ce74.len p) : p = 0 := by
  by_contra hp; simp [ce74, hp] at h

theorem ce74_WF : ce74.WF where
  mono _ _ _ h _ := h
  inj p q i j hi hj h := ⟨(ce74_len hi).trans (ce74_len hj).symm, h⟩

/-- **Lemma 7.4 is false**: the history of the tight execution `ce74` and the sketch `X(λ_E)` of
the set `λ_E` of all its 4-tuples are not equivalent. -/
theorem lemma_7_4_false :
    ¬ Equiv (ce74.hT 8).toList (XTH (ce74.tauAt 100)).toList := by
  intro h
  have h1 := Equiv.opsOf_eq h 0 ()
  rw [TH.opsOf_toList (Exec.hT_WF ce74_WF), TH.opsOf_toList (XTH_WF (Exec.valid_tauAt ce74_WF 100))]
    at h1
  have h2 := congrArg List.length h1
  simp only [List.length_map, List.length_range] at h2
  have hm : ¬ 1 < (XTH (ce74.tauAt 100)).m 0 := by
    rw [lt_m_iff (Exec.valid_tauAt ce74_WF 100)]
    rintro ⟨x, hx, hx1, hx2⟩
    obtain ⟨q, j, h3, -, -, h5, -⟩ := Exec.mem_allInv_tauAt.1 hx
    have hq := ce74_len h3
    subst hq
    have e : ce74.len 0 = 10 := rfl
    rw [e] at h3
    simp only [ce74, hx2] at h5
    omega
  have : (ce74.hT 8).m 0 = 2 := rfl
  omega

end Podc2023.RuntimeVerification
