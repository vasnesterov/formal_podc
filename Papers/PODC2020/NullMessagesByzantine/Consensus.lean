import Papers.PODC2020.NullMessagesByzantine.Compose

/-!
# Theorem 2.1: SmallCouncil composed with a binary consensus protocol is binary consensus

`smallCouncil_solves_BA`: if `B` solves binary Byzantine agreement (termination, validity,
agreement) against at most `t` Byzantine processes on the complete network, and `2t < n`, then so
does SmallCouncil composed with `B`. `theorem_2_1_consensus` is the paper's form (`k ≥ 3`,
`n > k t`).
-/

namespace Podc.NullMessagesByzantine

open Cslib.Byzantine.LockStep

variable {n : ℕ} {M₂ : Type*} (t : ℕ) (B : Protocol (Fin n) Bool M₂ Bool)
  (s : Scenario (Fin n) Bool (Msg M₂))

/-- If one correct process got no `err`, all correct processes have the same estimate. -/
lemma est_eq_of_not_gotErr (hrel : s.Reliable) (htn : t < n) (hF : s.byz.ncard ≤ t)
    {p₀ : Fin n} (hp₀ : p₀ ∉ s.byz) (hne : ¬ GotErr true t p₀ (s.input p₀) (H true t B s 3 p₀))
    {q : Fin n} (hq : q ∉ s.byz) :
    est t q (s.input q) (H true t B s 2 q) = est t p₀ (s.input p₀) (H true t B s 2 p₀) := by
  obtain ⟨c, hc⟩ := exists_unanimous_of_not_err t
    (not_err_of_not_gotErr t B s hrel (by norm_num) hq hne)
  obtain ⟨d, hd⟩ := exists_unanimous_of_not_err t
    (not_err_of_not_gotErr t B s hrel (by norm_num) hp₀ hne)
  rw [est_of_unanimous t hc, est_of_unanimous t hd]
  exact unanimous_agree true t B s hrel htn hF (by norm_num) (by norm_num) hq hp₀ hc hd

/-- **Theorem 2.1 (correctness).** If `B` is a binary Byzantine agreement protocol for at most `t`
Byzantine processes and `2t < n`, then SmallCouncil composed with `B` is one too. -/
theorem smallCouncil_solves_BA (h2t : 2 * t < n) (hB : Solves ⊤ B (atMost t) BA) :
    Solves ⊤ (smallCouncil t B) (atMost t) BA := by
  intro s hs hrel
  have hF : s.byz.ncard ≤ t := hs
  have htn : t < n := by omega
  -- decisions at time 3
  have hdec3 : ∀ p, ¬ GotErr true t p (s.input p) (H true t B s 3 p) →
      ∀ o, Decides ⊤ (smallCouncil t B) s p o ↔ o = est t p (s.input p) (H true t B s 2 p) := by
    intro p hp o
    have h := decides_of_not_gotErr true t B s hp
    exact ⟨fun h' => Decides.unique _ _ h' h, fun e => e ▸ h⟩
  by_cases hQ : ∃ q, q ∉ s.byz ∧ GotErr true t q (s.input q) (H true t B s 3 q)
  · -- some correct process sent `help!`: everybody runs the base protocol
    obtain ⟨q₀, hq₀, he₀⟩ := hQ
    have hall : ∀ q, q ∉ s.byz → Participates true t q (s.input q) (H true t B s 4 q) :=
      fun q _ => participates_of_gotErr t B s hrel (by norm_num) hq₀ he₀
    obtain ⟨hterm, hval, hagr⟩ :=
      hB (baseScenario true t B s) hs (baseScenario_reliable true t B s)
    simp only [baseScenario_honest] at hterm hval hagr
    have hdecB : ∀ p, p ∉ s.byz → GotErr true t p (s.input p) (H true t B s 3 p) →
        ∀ o, Decides ⊤ (smallCouncil t B) s p o ↔ Decides ⊤ B (baseScenario true t B s) p o :=
      fun p hp he o => decides_iff_base true t B s hrel hall hp he o
    -- if some correct process decided at time 3, the base run has unanimous inputs
    have hcommon : ∀ p₀, p₀ ∉ s.byz → ¬ GotErr true t p₀ (s.input p₀) (H true t B s 3 p₀) →
        ∀ p, p ∉ s.byz → ∀ o, Decides ⊤ (smallCouncil t B) s p o →
          o = est t p₀ (s.input p₀) (H true t B s 2 p₀) := by
      intro p₀ hp₀ hne p hp o ho
      have hinB : ∀ q ∈ s.honest, (baseScenario true t B s).input q =
          est t p₀ (s.input p₀) (H true t B s 2 p₀) :=
        fun q hq => est_eq_of_not_gotErr t B s hrel htn hF hp₀ hne hq
      by_cases he : GotErr true t p (s.input p) (H true t B s 3 p)
      · exact Decides.unique _ _ ((hdecB p hp he o).1 ho) (hval _ hinB p hp)
      · rw [(hdec3 p he o).1 ho]
        exact est_eq_of_not_gotErr t B s hrel htn hF hp₀ hne hp
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      by_cases he : GotErr true t p (s.input p) (H true t B s 3 p)
      · obtain ⟨o, ho⟩ := hterm p hp
        exact ⟨o, (hdecB p hp he o).2 ho⟩
      · exact ⟨_, decides_of_not_gotErr true t B s he⟩
    · intro v hv p hp
      have hest : ∀ q ∈ s.honest, est t q (s.input q) (H true t B s 2 q) = v :=
        fun q hq => est_honest_of_inputs true t B s hrel h2t hF hv (by norm_num) hq
      by_cases he : GotErr true t p (s.input p) (H true t B s 3 p)
      · exact (hdecB p hp he v).2 (hval v hest p hp)
      · exact (hdec3 p he v).2 (hest p hp).symm
    · intro p hp q hq v w hpv hqw
      by_cases hex : ∃ p₀, p₀ ∉ s.byz ∧ ¬ GotErr true t p₀ (s.input p₀) (H true t B s 3 p₀)
      · obtain ⟨p₀, hp₀, hne⟩ := hex
        rw [hcommon p₀ hp₀ hne p hp v hpv, hcommon p₀ hp₀ hne q hq w hqw]
      · push Not at hex
        exact hagr p hp q hq v w ((hdecB p hp (hex p hp) v).1 hpv)
          ((hdecB q hq (hex q hq) w).1 hqw)
  · -- no correct process got an `err`: everybody decides at time 3
    push Not at hQ
    refine ⟨fun p hp => ⟨_, decides_of_not_gotErr true t B s (hQ p hp)⟩, ?_, ?_⟩
    · intro v hv p hp
      rw [hdec3 p (hQ p hp)]
      exact (est_honest_of_inputs true t B s hrel h2t hF hv (by norm_num) hp).symm
    · intro p hp q hq v w hpv hqw
      rw [(hdec3 p (hQ p hp) v).1 hpv, (hdec3 q (hQ q hq) w).1 hqw]
      exact (est_eq_of_not_gotErr t B s hrel htn hF hq (hQ q hq) hp)

/-- **Theorem 2.1 (correctness), as stated.** Let `k ≥ 3` and let `B` be a binary consensus
protocol for `n > k t`. Then composing SmallCouncil onto `B` yields a binary consensus
protocol. -/
theorem theorem_2_1_consensus {k : ℕ} (hk : 3 ≤ k) (hn : k * t < n)
    (hB : Solves ⊤ B (atMost t) BA) : Solves ⊤ (smallCouncil t B) (atMost t) BA :=
  smallCouncil_solves_BA t B (by nlinarith) hB

end Podc.NullMessagesByzantine
