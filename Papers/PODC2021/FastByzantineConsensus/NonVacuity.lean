import Papers.PODC2021.FastByzantineConsensus.TwoStep
import Cslib.Computability.Distributed.Byzantine.PartialSync.Examples

/-!
# Sanity check: `FastConsensus` is satisfiable

The definition of a `t`-two-step consensus protocol is not contradictory: with no faults
(`f = t = 0`) the leader-echo algorithm of `Cslib.Byzantine.PartialSync.Examples` (decide the first value
heard from a fixed leader) is a `0`-resilient `0`-two-step consensus protocol, for any number of
processes. (See also `single_fastConsensus` for `n = 1` and arbitrary `f`, `t`.)
-/

namespace FastByzantineConsensus

open Cslib.Byzantine.PartialSync Cslib.Byzantine.PartialSync.Examples

variable {P V K : Type*} [Fintype P] [DecidableEq P]

theorem leaderEcho_fastConsensus (p₀ : P) (Au : Auth P V K) (δ : ℕ) :
    FastConsensus (leaderEcho (V := V) p₀) Au 0 0 δ := by
  refine ⟨?_, ?_⟩
  · have h := (leaderEcho_solves (p₀ := p₀) (V := V) δ).auth Au
    refine ⟨h.termination, h.agreement, fun R hR hRa p hp v hv => ?_⟩
    obtain ⟨q, hq⟩ := h.validity R hR hRa p hp v hv
    intro x hx
    rw [hx q] at hq
    exact (Option.some.inj hq).symm
  · intro I T hT x _
    have hT0 : T = ∅ := Finset.card_eq_zero.mp hT
    subst hT0
    set R := tsRun (leaderEcho (V := V) p₀) δ I ∅
    have hp₀ : p₀ ∉ R.faulty := by simp [R, tsRun]
    have hD : R.dl p₀ 0 x = δ := by simp [R, tsRun, nextRound]
    refine ⟨R.inp p₀, ?_⟩
    rcases snd_st hp₀ δ x with h | h
    · refine ⟨δ + 1, by omega, ?_⟩
      have hmem : R.inp p₀ ∈ R.inbox (leaderEcho p₀) x δ p₀ := by
        rw [Run.inbox_eq_flatMap, List.mem_flatMap]
        refine ⟨0, by simp, ?_⟩
        simp [Run.dlv, hD, Run.out_of_correct _ _ hp₀, leaderEcho]
      rcases snd_st hp₀ (δ + 1) x with h' | h'
      · exfalso
        rw [st_succ', h, Option.none_or, List.head?_eq_none_iff] at h'
        simp [h'] at hmem
      · exact h'
    · exact ⟨δ, by omega, h⟩

end FastByzantineConsensus
