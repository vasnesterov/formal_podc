import Papers.PODC2022.MultipleSpending.LowerBound
import Papers.PODC2022.MultipleSpending.EchoBroadcast
import Papers.PODC2022.MultipleSpending.WeakLocalProgress
import Papers.PODC2022.MultipleSpending.Optimality
import Papers.PODC2022.MultipleSpending.Examples
import Papers.PODC2022.MultipleSpending.Liveness

/-!
# Summary: the optimal `k` for `k`-Consistent Broadcast (corrected §5)

For a trust model satisfying the paper's standing assumptions and a source `s`, the smallest `k`
for which a `k`-CB with (per-value) Local Progress exists is `max 1 λ_s`, where `λ_s` is the
largest independence number of a graph `G_{F,S}` with `s ∈ F` (`srcInconsistencyNumber`). The
paper claims it is `k_max = inconsistencyNumber T` (Theorem 5.1 + Algorithms 1–2); this fails
(`theorem_5_1_false`, `theorem_5_1_false'`).
-/

namespace Podc.MultipleSpending

open Cslib.Byzantine.AsyncBroadcast

variable {P V : Type} [Fintype P] [DecidableEq P]

/-- **Corrected Theorem 5.1 (tight).** Every `k`-CB with per-value Local Progress has
`λ_s ≤ k`, and the quorum-echo algorithm achieves `max 1 λ_s` with per-value Local Progress. -/
theorem optimal_kcb [Infinite V] (T : TrustModel P) (hself : T.SelfMem) (hQ : T.HasQuorums)
    (hdown : T.DownClosed) (hne : T.F.Nonempty) (s : P) :
    (∀ (M : Type) (A : Protocol P M (Option V) V) (k : ℕ), IsKCB T s k A →
        LocalProgressAll T s A → srcInconsistencyNumber T s ≤ k) ∧
      IsKCB (V := V) T s (max 1 (srcInconsistencyNumber T s)) (echoAlg T s) ∧
      LocalProgressAll (V := V) T s (echoAlg T s) := by
  obtain ⟨F, hF⟩ := hne
  have h0 : ∅ ∈ T.F := hdown F hF ∅ (Finset.empty_subset F)
  exact ⟨fun _ _ _ hA hLP => srcInconsistencyNumber_le h0 hA hLP, echoAlg_isKCB hself hQ s,
    echoAlg_localProgressAll T hself s⟩

end Podc.MultipleSpending
