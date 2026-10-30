import Papers.PODC2013.ParetoOptimalConsensus.Lemma17

/-!
# Theorem 5: `U-Opt0` is an unbeatable uniform consensus protocol (Appendix C)

* **Corollary 1 of Appendix C** (`corollaryC1`): for `0 < t < n`, a protocol `Q ⪰ U-P0` that
  solves uniform consensus and decides at every node where `K_i ∃correct(0)`, or where there is no
  hidden path and `¬K_i ∃0`, is unbeatable (Lemmas 16 and 17).
* **Theorem 5** (`theorem5`): for `t < n`, `U-Opt0` is an unbeatable uniform consensus protocol,
  deciding by `f + 1` if `f ≥ t - 1` and by `f + 2` otherwise (Theorem 8). For `t = 0`,
  `U-Opt0` coincides with `Opt0` (`uOpt0_eq_opt0`) and Theorem 2 applies.
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Finset Podc.UnbeatableSetConsensus

variable {P : Type*} [Fintype P] {t : ℕ}

/-- **Corollary 1 (Appendix C).** -/
theorem corollaryC1 (ht0 : 0 < t) (ht : t < Fintype.card P) {Q' : Protocol P}
    (hQ' : SolvesUniformSetConsensus 1 t bin Q') (hdom' : Dominates t bin Q' (uP0 t))
    (hdec : ∀ r : Run P, Adm t bin r → ∀ i m, r.Alive i m →
      (KCorrect t r i m 0 ∨ (¬ HiddenPath r i m ∧ 0 ∉ vals r i m)) → DecidesBy Q' r i m) :
    UUnbeatable t Q' := by
  refine ⟨hQ', fun Q hQ hdomQ r hr i m v hv => ?_⟩
  have hdomP : Dominates t bin Q (uP0 t) := Dominates.trans hdomQ hdom'
  by_cases h : KCorrect t r i m 0 ∨ (¬ HiddenPath r i m ∧ 0 ∉ vals r i m)
  · exact hdec r hr i m hv.1 h
  · push Not at h
    obtain ⟨hnk, h2⟩ := h
    by_cases h0 : 0 ∈ vals r i m
    · exact absurd hv (lemma16 ht0 ht hQ hdomP hr h0 hnk v)
    · exact absurd hv (lemma17 ht0 ht hQ hdomP hr (not_not.1 fun hp => h0 (h2 hp)) h0 v)

/-- For `t = 0`, `U-Opt0` takes the decisions of `Opt0`. -/
lemma uOpt0_eq_opt0 (ht : 0 < Fintype.card P) : EqOnAdm 0 bin (uOpt0 0 : Protocol P) opt0 := by
  intro r hr i m
  have hal : r.Alive i m := by
    refine SyncCrash.Run.alive_of_not_faulty (fun hf => ?_) m
    have := hr.1.1
    have : i ∈ r.faulty := SyncCrash.Run.mem_faulty.2 hf
    have := card_pos.2 ⟨i, this⟩
    omega
  have hk : KCorrect 0 r i m 0 ↔ 0 ∈ vals r i m := by
    rw [lemma6 ht hr hal zero_mem_bin]
    exact ⟨fun h => h.1, fun h => ⟨h, Or.inr (by simp)⟩⟩
  simp only [uOpt0, optA, hk]
  split_ifs <;> simp_all

/-- **Theorem 5.** For `t < n`, `U-Opt0` is an unbeatable uniform consensus protocol in `γ_cr`.
Moreover, if `f ≥ t - 1` all decisions are made by time `f + 1`, and otherwise by `f + 2`. -/
theorem theorem5 (ht : t < Fintype.card P) :
    UUnbeatable t (uOpt0 t : Protocol P) ∧
      (∀ r : Run P, Adm t bin r → t ≤ r.faulty.card + 1 → ∀ i, r.Alive i (r.faulty.card + 1) →
        DecidesBy (uOpt0 t) r i (r.faulty.card + 1)) ∧
      (∀ r : Run P, Adm t bin r → ∀ i, r.Alive i (r.faulty.card + 2) →
        DecidesBy (uOpt0 t) r i (r.faulty.card + 2)) := by
  obtain ⟨hs, h1, h2⟩ := theorem8 ht
  refine ⟨?_, h1, h2⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · -- `t = 0`: uniform consensus is consensus, and `U-Opt0 = Opt0`
    have he := uOpt0_eq_opt0 (P := P) ht
    refine ⟨hs, fun Q hQ hdom => he.symm.dominates_left ?_⟩
    exact (theorem2 (P := P) (t := 0)).2 Q (uniform_toSet hQ) (he.dominates_right hdom)
  · refine corollaryC1 ht0 ht hs (lemma18 ht) fun r hr i m hal h => decidesBy_of_dec hal ?_
    rw [Ne, uOpt0_dec_eq_none]
    tauto

end Podc.ParetoOptimalConsensus
