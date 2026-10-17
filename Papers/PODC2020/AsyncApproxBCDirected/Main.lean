import Papers.PODC2020.AsyncApproxBCDirected.Round
import Papers.PODC2020.AsyncApproxBCDirected.Necessity
import Cslib.Computability.Distributed.ApproxConsensus.Contraction
import Cslib.Computability.Distributed.Byzantine.Specs

/-!
# Main results: Theorem 4 (both directions), convergence and termination of the algorithm

* `Exec G f` — an execution of the whole algorithm: one `RoundExec` per asynchronous round, with
  the same Byzantine set, where the state value of every correct node at the start of round
  `r + 1` is its Filter-and-Average output of round `r`.
* `Exec.valid` (**Theorem 16**), `Exec.spread_le` (repeated **Lemma 15**:
  `U[r] − μ[r] ≤ (U[0] − μ[0]) / 2^r`), `Exec.converges` (convergence in the limit).
* `Exec.termination` — Section 4.6: with inputs in `[0, K]` for an a-priori known `K`, every node
  outputs its state of round `r* = min {r | K < ε·2^r}`; these outputs are valid and pairwise
  closer than `ε`, and every correct node completes every round (Theorem 9).
* `theorem4_sufficiency`, `theorem4_necessity` — the two directions of **Theorem 4** at the level
  of the round model. The end-to-end statement in the operational model, where the round-level
  hypotheses are proved for the actual algorithm, is `theorem4` in `Operational/Theorem4.lean`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

open Cslib.ApproxConsensus Cslib.ApproxConsensus.Async

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} {f : ℕ}

/-- An execution of Algorithm BW + FA: round executions with a common Byzantine set, chained by
the Filter-and-Average outputs. -/
structure Exec (G : Digraph V) (f : ℕ) where
  /-- The round executions. -/
  R : ℕ → RoundExec G f
  /-- The Byzantine nodes. -/
  F : Finset V
  F_eq : ∀ r, (R r).F = F
  /-- The state of a correct node at the start of round `r + 1` is its output of round `r`. -/
  next : ∀ r, ∀ v ∉ F, (R r).Output v ((R (r + 1)).x v)

namespace Exec

variable (E : Exec G f)

/-- State value `x_v[r]`. -/
def x (r : ℕ) (v : V) : ℝ := (E.R r).x v

/-- **Theorem 16** (validity): all state values of correct nodes stay within any bounds of the
inputs of correct nodes. -/
theorem valid {lo hi : ℝ} (h0 : ∀ w ∉ E.F, lo ≤ E.x 0 w ∧ E.x 0 w ≤ hi) (r : ℕ) :
    ∀ v ∉ E.F, lo ≤ E.x r v ∧ E.x r v ≤ hi := by
  induction r with
  | zero => exact h0
  | succ r ih =>
    intro v hv
    have hv' : v ∉ (E.R r).F := by rw [E.F_eq]; exact hv
    exact (E.R r).output_valid hv' (E.next r v hv) fun w hw => ih w (by rwa [E.F_eq] at hw)

/-- Repeated **Lemma 15**: after `r` rounds the correct state values lie in an interval of length
`(hi − lo) / 2^r` inside `[lo, hi]`. -/
theorem interval (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {lo hi : ℝ} (hlh : lo ≤ hi)
    (h0 : ∀ w ∉ E.F, lo ≤ E.x 0 w ∧ E.x 0 w ≤ hi) (r : ℕ) :
    ∃ lo' hi', lo ≤ lo' ∧ lo' ≤ hi' ∧ hi' ≤ hi ∧ hi' - lo' ≤ (hi - lo) / 2 ^ r ∧
      ∀ v ∉ E.F, lo' ≤ E.x r v ∧ E.x r v ≤ hi' := by
  have h := exists_Icc_pow_mul_of_step (H := fun _ => {v | v ∉ E.F}) (x := E.x) (c := 1 / 2)
    (by norm_num) hlh h0 (fun r lo' hi' _ h5 => by
      refine ⟨fun v hv => (E.R r).output_valid (by rw [E.F_eq]; exact hv) (E.next r v hv)
        fun w hw => h5 w (by rwa [E.F_eq] at hw), fun v hv u hu => ?_⟩
      rw [one_div_mul_eq_div]
      exact (le_abs_self _).trans ((E.R r).output_conv hG hn (by rw [E.F_eq]; exact hv)
        (by rw [E.F_eq]; exact hu) (E.next r v hv) (E.next r u hu)
        fun w hw => h5 w (by rwa [E.F_eq] at hw))) r
  rwa [one_div_pow, one_div_mul_eq_div] at h

/-- **Lemma 15** iterated: `|x_v[r] − x_u[r]| ≤ (hi − lo) / 2^r`. -/
theorem spread_le (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {lo hi : ℝ} (hlh : lo ≤ hi)
    (h0 : ∀ w ∉ E.F, lo ≤ E.x 0 w ∧ E.x 0 w ≤ hi) (r : ℕ) {v u : V} (hv : v ∉ E.F)
    (hu : u ∉ E.F) : |E.x r v - E.x r u| ≤ (hi - lo) / 2 ^ r := by
  obtain ⟨lo', hi', -, -, -, h4, h5⟩ := E.interval hG hn hlh h0 r
  rw [abs_le]; constructor <;> linarith [h5 v hv, h5 u hu]

/-- Convergence: the state values of correct nodes converge to a common limit. -/
theorem converges (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {lo hi : ℝ} (hlh : lo ≤ hi)
    (h0 : ∀ w ∉ E.F, lo ≤ E.x 0 w ∧ E.x 0 w ≤ hi) {v u : V} (hv : v ∉ E.F) (hu : u ∉ E.F) :
    Filter.Tendsto (fun r => E.x r v - E.x r u) Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto (fun r : ℕ => (hi - lo) / 2 ^ r) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul (hi - lo)
    simp only [mul_zero] at this
    refine this.congr fun r => ?_
    rw [one_div, inv_pow, div_eq_mul_inv]
  refine squeeze_zero_norm (fun r => ?_) hlim
  rw [Real.norm_eq_abs]
  exact E.spread_le hG hn hlh h0 r hv hu

/-- The output round of Section 4.6: the first `r` with `K < ε · 2^r`. -/
noncomputable def outRound (K ε : ℝ) : ℕ := by
  classical exact Nat.find (pow_unbounded_of_one_lt (K / ε) (by norm_num : (1 : ℝ) < 2))

theorem lt_outRound (K ε : ℝ) (hε : 0 < ε) : K < ε * 2 ^ outRound K ε := by
  classical
  have := Nat.find_spec (pow_unbounded_of_one_lt (K / ε) (by norm_num : (1 : ℝ) < 2))
  rw [div_lt_iff₀ hε] at this
  unfold outRound; linarith

/-- **Termination and correctness** (Section 4.6, Theorem 9, Lemma 15, Theorem 16): if the inputs
of the correct nodes lie in `[0, K]` for a known `K`, every correct node completes every round,
and the values output at round `r* = outRound K ε` are valid (between two correct inputs) and
pairwise closer than `ε`. -/
theorem termination (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {K ε : ℝ} (hε : 0 < ε)
    (hK : ∀ w ∉ E.F, 0 ≤ E.x 0 w ∧ E.x 0 w ≤ K) :
    (∀ r, ∀ v ∉ E.F, ∃ y, (E.R r).Output v y) ∧
    (∀ v ∉ E.F, ∀ u ∉ E.F, |E.x (outRound K ε) v - E.x (outRound K ε) u| < ε) ∧
    (∀ r, ∀ v ∉ E.F, (∃ w ∉ E.F, E.x 0 w ≤ E.x r v) ∧ ∃ w ∉ E.F, E.x r v ≤ E.x 0 w) := by
  classical
  refine ⟨fun r v hv => (E.R r).output_exists hG hn (by rw [E.F_eq]; exact hv), ?_, ?_⟩
  · intro v hv u hu
    have := E.spread_le hG hn (lo := 0) (hi := K) ((hK v hv).1.trans (hK v hv).2) hK
      (outRound K ε) hv hu
    have h2 : (0 : ℝ) < 2 ^ outRound K ε := by positivity
    have h3 : (K - 0) / 2 ^ outRound K ε < ε := by
      rw [sub_zero, div_lt_iff₀ h2]; linarith [lt_outRound K ε hε]
    linarith
  · exact fun r v hv => (Cslib.Byzantine.Problem.inRange_iff_forall_mem_Icc
      (H := {w | w ∉ E.F}) (Set.toFinite _) ⟨v, hv⟩).2 fun _ _ h0 => E.valid h0 r v hv

end Exec

/-- **Theorem 4, sufficiency** (Section 4): if `G` satisfies 3-reach (and `n ≥ 2`), then in every
execution of Algorithm BW + Filter-and-Average with at most `f` Byzantine nodes and inputs in a
known range `[0, K]`, all correct nodes complete all rounds, and their values at round
`outRound K ε` are valid and pairwise within `ε`. (Stated for the round-level model `Exec`.) -/
theorem theorem4_sufficiency (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) (E : Exec G f)
    {K ε : ℝ} (hε : 0 < ε) (hK : ∀ w ∉ E.F, 0 ≤ E.x 0 w ∧ E.x 0 w ≤ K) :
    (∀ r, ∀ v ∉ E.F, ∃ y, (E.R r).Output v y) ∧
    (∀ v ∉ E.F, ∀ u ∉ E.F,
      |E.x (Exec.outRound K ε) v - E.x (Exec.outRound K ε) u| < ε) ∧
    (∀ r, ∀ v ∉ E.F, (∃ w ∉ E.F, E.x 0 w ≤ E.x r v) ∧ ∃ w ∉ E.F, E.x r v ≤ E.x 0 w) :=
  E.termination hG hn hε hK

/-- **Theorem 4, necessity** (Theorem 18): if some deterministic algorithm solves asynchronous
approximate Byzantine consensus with up to `f` faults on `G` (in the message-passing model of
`AsyncModel.lean`), then `G` satisfies 3-reach. -/
theorem theorem4_necessity {M S : Type*} {A : Algorithm V M S} [DecidableRel G.Adj] {ε : ℝ}
    (hε : 0 < ε) (hA : Solves A G f ε) : ThreeReach G f :=
  threeReach_of_solves hε hA

end AsyncApproxBCDirected
