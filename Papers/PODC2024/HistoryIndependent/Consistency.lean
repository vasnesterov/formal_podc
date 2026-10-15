import Papers.PODC2024.HistoryIndependent.Alg2
import Papers.PODC2024.HistoryIndependent.ClassC
import Papers.PODC2024.HistoryIndependent.Alg4Thm
import Papers.PODC2024.HistoryIndependent.Prop19

/-!
# Consistency check: Algorithm 2 is not wait-free

Combining Theorem 9 (Algorithm 2 is lock-free and state-quiescent HI) with Corollary 18 shows that
Algorithm 2 is not wait-free for `K ≥ 3` — as the paper explains (Section 4), the reader may starve.
This also confirms that the hypotheses of Corollary 18 are met by a concrete, non-trivial
implementation.
-/

namespace Cslib.SharedMemory

theorem alg2_not_waitFree {K : ℕ} (hK : 3 ≤ K) (v₀ : Fin K) : ¬ (Alg2.alg2 v₀).WaitFree := by
  intro hwf
  exact cor18 hK v₀ (fun _ => false) (Alg2.alg2 v₀) .w .r (by decide)
    (Or.inr ⟨rfl, rfl⟩) (fun v => Or.inl ⟨rfl, v, rfl⟩) ⟨hwf, (Alg2.theorem9 v₀).2.2⟩

/-! # Consistency check: in Algorithm 4 the reader writes

Theorem 12 (Algorithm 4 is wait-free and quiescent HI) and Proposition 19 imply that the reader of
Algorithm 4 must change the memory (it does: it writes `flag` and clears `B`).
-/

theorem alg4_reader_writes {K : ℕ} [NeZero K] (hK : 3 ≤ K) (v₀ : Fin K) :
    ¬ (Alg4.alg4 v₀).NeverWrites Alg4.Proc.r := by
  intro hnw
  exact prop19 hK v₀ (fun _ => false) (Alg4.alg4 v₀) .w .r (by decide) (fun _ _ => Iff.rfl) hnw
    ⟨(Alg4.theorem12 (v₀ := v₀)).2.1, (Alg4.theorem12 (v₀ := v₀)).2.2⟩

end Cslib.SharedMemory
