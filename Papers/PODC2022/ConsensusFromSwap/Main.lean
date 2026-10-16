import Papers.PODC2022.ConsensusFromSwap.SetAgreementLB
import Papers.PODC2022.ConsensusFromSwap.BoundedSwap
import Papers.PODC2022.ConsensusFromSwap.Alg1Valid
import Papers.PODC2022.ConsensusFromSwap.Alg1OF
import Papers.PODC2022.ConsensusFromSwap.Alg1Agree

/-!
# The Space Complexity of Consensus from Swap — main results

Sean Ovens, PODC 2022 (arXiv 2305.06507).

* `algorithm1_correct` — Algorithm 1 (Lemmas 6–8): obstruction-free `m`-valued `k`-set agreement
  for `n` processes from `N ≥ n − k` swap objects (without `Read`), deciding within `8N` solo steps.
* `theorem10` / `theorem10_swap` (in `SetAgreementLB.lean`) — at least `⌈n/k⌉ − 1` swap objects.
* `consensus_swap_tight` — for consensus the bound `n − 1` is exactly attained.
* `theorem18` (in `BinarySwap.lean`) — at least `n − 2` readable binary swap objects for binary
  consensus.
* `theorem22` (in `BoundedSwap.lean`) — at least `(n − 2)/(3b + 1)` readable swap objects with
  domain size `b` for binary consensus.
-/

namespace ConsensusFromSwap

open Alg1

/-- **Algorithm 1** of [Ovens 2022] (Lemmas 6, 7, 8): for `k ≥ 1` and `N ≥ n − k` swap objects,
Algorithm 1 is an obstruction-free `m`-valued `k`-set agreement algorithm; every process running
solo from any configuration decides within `8N` steps. -/
theorem algorithm1_correct {P : Type} [DecidableEq P] [Fintype P] {m N : ℕ} [NeZero m]
    [NeZero N] {k : ℕ} (hk : 1 ≤ k) (hN : Fintype.card P ≤ N + k) :
    SolvesSetAgreement (alg P m N) k Set.univ ∧ ObstructionFree (alg P m N) Set.univ ∧
      ∀ (C : Cfg (alg P m N)) (p : P), ∃ t ≤ 8 * N, (run C (solo p t)).Dec p :=
  ⟨⟨fun x _ α => lemma6_agreement hk hN x α, validity_field⟩, lemma8_obstructionFree,
    lemma8_bound⟩

/-- For consensus from swap objects the bound of Theorem 10 is tight: with `n ≥ 2` processes and
`m ≥ 2` input values, Algorithm 1 solves obstruction-free consensus with `n − 1` swap objects,
and every obstruction-free consensus algorithm from swap objects needs at least `n − 1`. -/
theorem consensus_swap_tight {P : Type} [DecidableEq P] [Fintype P] {m : ℕ} [NeZero m]
    (hm : 2 ≤ m) (hn : 2 ≤ Fintype.card P) :
    (∃ (N : ℕ) (_ : NeZero N), N = Fintype.card P - 1 ∧
      SolvesSetAgreement (alg P m N) 1 Set.univ ∧ ObstructionFree (alg P m N) Set.univ) ∧
    (∀ {ι : Type} [DecidableEq ι] [Fintype ι] {D : ι → Type} {d₀ : (i : ι) → D i}
      (A : Alg (fun i => swapObj (D i) (d₀ i)) P (Fin m)),
      SolvesSetAgreement A 1 Set.univ → ObstructionFree A Set.univ →
      Fintype.card P - 1 ≤ Fintype.card ι) := by
  refine ⟨⟨Fintype.card P - 1, ⟨by omega⟩, rfl, ?_⟩, fun A hA hof => ?_⟩
  · have := @algorithm1_correct P _ _ m (Fintype.card P - 1) _ ⟨by omega⟩ 1 le_rfl (by omega)
    exact ⟨this.1, this.2.1⟩
  · refine consensus_swap_lowerBound (A := A) ?_ hA hof
    rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    exact_mod_cast hm

end ConsensusFromSwap
