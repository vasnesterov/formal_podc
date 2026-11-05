import Papers.PODC2013.ConstantBarriersMutex.RMRPassage
import Papers.PODC2013.ConstantBarriersMutex.Invariant

/-!
# Lemma 10 of the paper: constant barriers and `O(log n)` RMRs per passage

Attiya, Hendler, Levy, *An O(1)-Barriers Optimal RMRs Mutual Exclusion Algorithm*, PODC 2013,
Lemma 10: "A process performs a constant number of barriers and incurs `O(log n)` RMRs during a
passage."

Model: Algorithm 1 under TSO (`Model.lean`), `n = 2^h` processes, CC cost model of Section 3
(`RMR.lean`). The bounds hold for **every** run (no fairness) and every process `p`, for every
time interval `[t₁, t₂)` within one passage of `p` (`Run.WithinPassage`: `p` is not in the
remainder section at any time strictly between `t₁` and `t₂`), in particular for a complete
passage and for every prefix of an incomplete one.

* `lemma10_rmr`: at most `19·h + 23 = 19 log n + 23` RMRs.
* `lemma10_barriers_le`: at most `2` barriers complete; `lemma10_barriers`: a complete passage
  completes exactly `2` barriers (statements 22 and 50).
* `stmt25_rmr_le`: the busy-wait of statement 25 costs at most `6` RMRs (the paper's proof says
  4: "at most twice when it reads `exits` and at most twice when it reads `lock`"; `lock` can in
  fact be read remotely 4 times, see `README.md`); `stmt27_rmr_le`: statement 27 costs at most `2`.
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

/-- **Lemma 10 of [AHL13], RMR part.** In every run, the number of RMRs (CC model) incurred by a
process `p` during one passage, or during any part of a passage, is at most
`19·h + 23 = 19 log n + 23`. -/
theorem lemma10_rmr (r : Run h) (p : Proc h) {t₁ t₂ : ℕ} (hw : r.WithinPassage p t₁ t₂) :
    r.rmr p t₁ t₂ ≤ 19 * h + 23 :=
  r.rmr_le_of_inv r.inv p hw

/-- **Lemma 10 of [AHL13], barrier part (upper bound).** In every run, a process completes at
most two barriers during one passage (or any part of it). -/
theorem lemma10_barriers_le (r : Run h) (p : Proc h) {t₁ t₂ : ℕ}
    (hw : r.WithinPassage p t₁ t₂) : r.barriers p t₁ t₂ ≤ 2 :=
  r.barriers_le p hw

/-- **Lemma 10 of [AHL13], barrier part.** A complete passage completes exactly two barriers
(statements 22 and 50). -/
theorem lemma10_barriers (r : Run h) (p : Proc h) {t₁ t₂ : ℕ} (hP : r.Passage p t₁ t₂) :
    r.barriers p t₁ t₂ = 2 :=
  r.barriers_passage p hP

/-- **Statement 25 (proof of Lemma 10 of [AHL13]).** Busy-waiting at statement 25 costs at most
`6` RMRs: if `p` executes statement 24 at time `t₀` and stays at statement 25 at all times in
`(t₀, t₂)`, then `p` incurs at most `6` RMRs in the events at times `t₀ + 1, …, t₂ − 1`. (The paper
claims at most `4`.) -/
theorem stmt25_rmr_le (r : Run h) (p : Proc h) {t₀ t₂ : ℕ} (h0 : (r.s t₀).pc p = .e24)
    (he : r.ev t₀ = .step p) (hin : ∀ t, t₀ < t → t < t₂ → ((r.s t).pc p).At25) :
    r.rmr p (t₀ + 1) t₂ ≤ 6 :=
  r.stmt25_rmr_le_of_inv r.inv p h0 he hin

/-- **Statement 27 (proof of Lemma 10 of [AHL13]).** Busy-waiting at statement 27 costs at most
`2` RMRs. -/
theorem stmt27_rmr_le (r : Run h) (p : Proc h) {t₀ t₂ : ℕ}
    (hin : ∀ t, t₀ ≤ t → t < t₂ → (r.s t).pc p = .e27) : r.rmr p t₀ t₂ ≤ 2 :=
  r.stmt27_rmr_le_of_inv r.inv p hin

end Podc.ConstantBarriersMutex
