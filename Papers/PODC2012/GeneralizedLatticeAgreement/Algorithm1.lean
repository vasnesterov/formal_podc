import Papers.PODC2012.GeneralizedLatticeAgreement.Rounds
import Papers.PODC2012.GeneralizedLatticeAgreement.Runs

/-!
# Algorithm 1 (one-shot lattice agreement)

Algorithm 1 is our model started with `bufferedValues = initialValue` and run without `Receive`
steps (hence without `Buffer` steps): the first `Propose` then proposes `initialValue` (the paper's
guard `activeProposalNumber = 0`), and after the `Decide` the buffer is `⊥`, so no further
`Propose` is enabled. (The only difference: for `initialValue = ⊥`, Algorithm 1 proposes `⊥`
while our `Propose` is not enabled; the counterexample below has non-`⊥` initial values.)

* `alg1_consistency_false`: **Algorithm 1 violates Consistency as written**, in a failure-free
  execution with three proposers and three acceptors. `ProcessNACK` joins the rejection value
  into `proposedValue` while acknowledgements for the same proposal are still being counted, and
  `Decide` (guard `ackCount ≥ ⌈(N_a+1)/2⌉`) then outputs this enlarged `proposedValue`, which
  was never proposed, let alone chosen.
* `consistency_of_clean`: with the repaired `Decide` (additional guard `nackCount = 0`, as the
  prose of Section 3 describes: "If all these responses are acceptances, the proposer is done"),
  every output is a chosen value, so outputs are pairwise comparable. The repaired algorithm's
  executions are exactly the executions of the model in which every `Decide` step happens with
  `nackCount = 0`, i.e. in which every recorded decision is clean.
-/

namespace Podc.GeneralizedLatticeAgreement

variable {P A Ln L : Type}
variable [SemilatticeSup L] [OrderBot L] [DecidableEq P] [DecidableEq A] [DecidableEq Ln]
  [DecidableEq L] [DecidableLE L] [Fintype P] [Fintype A]

/-- **Consistency of the repaired Algorithm 1** (and, more generally, of the `outputValue`s of
Algorithm 2): if every `Decide` step was taken with `nackCount = 0`, any two output values are
comparable. Validity holds by `theorem_5_1` (the initial values are the received values). -/
theorem consistency_of_clean {b : P → L} {s : State P A Ln L} (hs : Reachable b s)
    (hclean : ∀ x ∈ s.decisions, x.2.2.2 = true) (p p' : P) :
    (s.prop p).output ≤ (s.prop p').output ∨ (s.prop p').output ≤ (s.prop p).output := by
  have h := hs.inv
  have hch : ∀ q, (s.prop q).output = ⊥ ∨ Chosen s (s.prop q).output := by
    intro q
    rcases h.output_dec q with h0 | ⟨n, c, hn⟩
    · exact Or.inl h0
    · have hc : c = true := hclean _ hn
      subst hc
      exact Or.inr (h.chosen_of_quorum (h.dec_clean hn) (h.dec_quorum hn).2.2)
  rcases hch p with h1 | h1
  · left; rw [h1]; exact bot_le
  rcases hch p' with h2 | h2
  · right; rw [h2]; exact bot_le
  exact h.chosen_comparable h1 h2

namespace Cex1

open Action

/-- Three processes. -/
abbrev N := Fin 3
/-- Power-set lattice. -/
abbrev V := Finset ℕ

/-- Initial values `{1}, {2}, {3}`. -/
def init : N → V := ![{1}, {2}, {3}]

/-- A failure-free schedule of Algorithm 1. -/
def tr : List (Action N N (Fin 1) V) := [
  propose 1, accept 2 1 1 {2},
  propose 0, reject 2 0 1 {1}, accept 0 0 1 {1}, accept 1 0 1 {1},
  -- proposer 0 processes the NACK first, then two ACKs, and decides its enlarged value {1,2}
  processNack 0 2 1 {1, 2}, processAck 0 0 1 {1}, processAck 0 1 1 {1}, decide 0,
  -- proposer 2 is rejected by acceptors 0 and 1, refines to {1,3} and decides it
  propose 2, reject 0 2 1 {3}, reject 1 2 1 {3},
  processNack 2 0 1 {1, 3}, processNack 2 1 1 {1, 3}, refine 2,
  accept 0 2 2 {1, 3}, accept 1 2 2 {1, 3}, processAck 2 0 2 {1, 3}, processAck 2 1 2 {1, 3},
  decide 2]

lemma run_tr : ((run (initState (A := N) (Ln := Fin 1) init) tr).elim false fun s =>
    decide ((s.prop 0).output = {1, 2} ∧ (s.prop 2).output = {1, 3} ∧
      (s.prop 0).active = false ∧ (s.prop 2).active = false)) = true := by
  decide +kernel

/-- **Algorithm 1 violates Consistency**: in a failure-free execution (no `Receive` steps, initial
values `{1}, {2}, {3}`), proposers `0` and `2` decide the incomparable values `{1,2}` and
`{1,3}`. -/
theorem alg1_consistency_false :
    ∃ s : State N N (Fin 1) V, Reachable init s ∧
      (∃ tr' : List (Action N N (Fin 1) V), run (initState init) tr' = some s ∧
        ∀ a ∈ tr', ¬ a.IsInput) ∧
      (s.prop 0).output = {1, 2} ∧ (s.prop 2).output = {1, 3} ∧
      ¬ ((s.prop 0).output ≤ (s.prop 2).output ∨ (s.prop 2).output ≤ (s.prop 0).output) := by
  have h := run_tr
  cases hr : run (initState (A := N) (Ln := Fin 1) init) tr with
  | none => rw [hr] at h; simp at h
  | some s =>
    rw [hr] at h
    simp only [Option.elim, decide_eq_true_eq] at h
    obtain ⟨h0, h2, -⟩ := h
    refine ⟨s, reachable_of_run .init hr, ⟨tr, hr, by decide⟩, h0, h2, ?_⟩
    rw [h0, h2]; decide

end Cex1

end Podc.GeneralizedLatticeAgreement
