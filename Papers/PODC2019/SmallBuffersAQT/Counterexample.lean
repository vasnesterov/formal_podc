import Papers.PODC2019.SmallBuffersAQT.Theorem41

/-!
# Lemma 4.8 fails for the schedule of Algorithm 3

Lemma 4.8 claims that during one phase (one round at each level, no injections after the first
round) the badness of every node with positive badness strictly decreases. Its proof uses that
"levels are activated in decreasing order over the course of a phase". Algorithm 3, however,
activates level `λ = t mod ℓ` in round `t`; phases start at `t ≡ 0 (mod ℓ)` (acceptance at
`λ = 0`), so the levels of a phase are `0, 1, …, ℓ-1` (increasing). With the indexing used in the
statement of Lemma 4.8 (phase = rounds `t+1, …, t+ℓ`, `t = (φ-1)ℓ`) they are `1, 2, …, ℓ-1, 0`.
In both cases a level is processed *after* a lower level, and badness pushed down to that lower
level (Case 2 of Claim 2) survives the phase.

Instance: `m = 3`, `ℓ = 3` (27 nodes), node `8` holds two packets to `15`, node `9` one packet
to `15`, node `10` two packets to `20` and one to `15`. Node `10` has badness `1` (a bad level-2
packet to intermediate destination `18`). In the level-2 round, node `8` forwards a packet to its
level-2 intermediate destination `9`, where it becomes pre-bad at level 1; `ActivatePreBad` moves
the level-1 packet of `9` to `10`, which is busy forwarding at level 2, so node `10` now has a bad
level-1 pseudo-buffer: the badness of `10` stays `1`. The rounds at levels `0` and `1` do nothing.
With the repaired order `2, 1, 0` the badness of node `10` drops to `0` (`fixed_order_ok`).
-/

namespace Podc.SmallBuffersAQT

open Finset

/-- A canonical (computable) choice of the forwarded packet: the smallest destination. -/
def canonSel (m ℓ : ℕ) (c : Config) (i : ℕ) (q : Key) : ℕ :=
  ((List.range (m ^ ℓ)).find? (fun w => 1 ≤ c i w ∧ i < w ∧ key m ℓ i w = q)).getD 0

lemma canonSel_valid (m ℓ : ℕ) (c : Config) : ValidSel m ℓ c (canonSel m ℓ c) := by
  intro i q h
  obtain ⟨w, hiw, hw, hk, hc⟩ := pb_pos h
  have hsome : ((List.range (m ^ ℓ)).find? (fun w => 1 ≤ c i w ∧ i < w ∧ key m ℓ i w = q)).isSome := by
    rw [List.find?_isSome]
    exact ⟨w, List.mem_range.2 hw, by simp [hc, hiw, hk]⟩
  obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.1 hsome
  have hmem := List.mem_of_find?_eq_some hw'
  have hp := List.find?_some hw'
  simp only [decide_eq_true_eq] at hp
  simp only [canonSel, hw', Option.getD_some]
  exact ⟨hp.1, hp.2.1, List.mem_range.1 hmem, hp.2.2⟩

/-- The statement of Lemma 4.8 for a phase whose `k`-th round works at level `sched k`
(an arbitrary configuration at the start of the phase, arbitrary valid choices of packets). -/
def Lemma48 (m ℓ : ℕ) (sched : ℕ → ℕ) : Prop :=
  ∀ d : ℕ → Config, (∀ k < ℓ, ∃ sel, ValidSel m ℓ (d k) sel ∧ d (k + 1) = hptsStep m ℓ (sched k) (d k) sel) →
    ∀ i, badness m ℓ (d ℓ) i ≤ badness m ℓ (d 0) i - 1

/-- The configuration of the counterexample. -/
def cex0 : Config := fun i w =>
  if i = 8 ∧ w = 15 then 2 else if i = 9 ∧ w = 15 then 1 else
  if i = 10 ∧ w = 20 then 2 else if i = 10 ∧ w = 15 then 1 else 0

/-- Run the phase with levels `l0, l1, l2` from `cex0` with the canonical choices. -/
def cexStep (l : ℕ) (c : Config) : Config := hptsStep 3 3 l c (canonSel 3 3 c)

/-- Run the phase with levels `l0, l1, l2` from `cex0` with the canonical choices. -/
def cexRun (l0 l1 l2 : ℕ) : ℕ → Config
  | 0 => cex0
  | 1 => cexStep l0 cex0
  | 2 => cexStep l1 (cexStep l0 cex0)
  | _ => cexStep l2 (cexStep l1 (cexStep l0 cex0))

lemma cexRun_hyp (sched : ℕ → ℕ) :
    ∀ k < 3, ∃ sel, ValidSel 3 3 (cexRun (sched 0) (sched 1) (sched 2) k) sel ∧
      cexRun (sched 0) (sched 1) (sched 2) (k + 1) =
        hptsStep 3 3 (sched k) (cexRun (sched 0) (sched 1) (sched 2) k) sel := by
  intro k hk
  interval_cases k <;> exact ⟨_, canonSel_valid 3 3 _, rfl⟩

set_option maxRecDepth 100000 in
lemma cex_badness_start : badness 3 3 cex0 10 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cex_badness_alg3 : badness 3 3 (cexRun 0 1 2 3) 10 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
lemma cex_badness_lemma48 : badness 3 3 (cexRun 1 2 0 3) 10 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
/-- Sanity check: with the repaired (decreasing) order the badness of node `10` drops. -/
lemma fixed_order_ok : badness 3 3 (cexRun 2 1 0 3) 10 = 0 := by decide +kernel

/-- Lemma 4.8 is false for the schedule of Algorithm 3 (levels `0, 1, …, ℓ-1` in a phase). -/
theorem lemma_4_8_false_alg3 : ¬ Lemma48 3 3 (fun k => k) := by
  intro h
  have := h (cexRun 0 1 2) (cexRun_hyp (fun k => k)) 10
  rw [cex_badness_alg3] at this
  rw [show cexRun _ _ _ 0 = cex0 from rfl, cex_badness_start] at this
  omega

/-- Lemma 4.8 is false with the indexing of its statement (phase = rounds `t+1, …, t+ℓ`,
levels `1, 2, …, ℓ-1, 0`). -/
theorem lemma_4_8_false_indexing : ¬ Lemma48 3 3 (fun k => (k + 1) % 3) := by
  intro h
  have := h (cexRun 1 2 0) (cexRun_hyp (fun k => (k + 1) % 3)) 10
  rw [cex_badness_lemma48] at this
  rw [show cexRun _ _ _ 0 = cex0 from rfl, cex_badness_start] at this
  omega

/-- Lemma 4.8 (repaired): it holds for the decreasing order `ℓ-1, …, 0`. -/
theorem lemma_4_8 {m ℓ : ℕ} (hℓ : 1 ≤ ℓ) : Lemma48 m ℓ (fixedSched ℓ) := by
  intro d hd i
  have hd' : ∀ k ≤ ℓ - 1, ∃ sel, ValidSel m ℓ (d k) sel ∧
      d (k + 1) = hptsStep m ℓ (ℓ - 1 - k) (d k) sel := fun k hk => hd k (by omega)
  obtain ⟨hle, hlt⟩ := phase_decreasing (m := m) (ℓ := ℓ) i (ℓ - 1) (by omega) d hd'
  rw [show ℓ - 1 + 1 = ℓ by omega] at hle hlt
  by_cases hpos : 0 < badness m ℓ (d 0) i
  · have := hlt hpos; omega
  · have := hle ℓ le_rfl; omega

end Podc.SmallBuffersAQT
