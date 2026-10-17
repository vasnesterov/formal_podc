import Papers.PODC2019.VABA.ExpectedViews
import Papers.PODC2019.VABA.Liveness
import Papers.PODC2019.VABA.Counterexample

/-!
# VABA (Abraham, Malkhi, Spiegelman, PODC 2019): main results

The paper's properties of Theorem 1, for `n > 3f` parties with certificate threshold
`Q = n - f` (which is the paper's `2f + 1` when `n = 3f + 1`), an adaptive adversary corrupting at
most `f` parties, an asynchronous network, ideal threshold signatures and an ideal common coin
(model: `Model.lean`).

* `vaba_agreement`, `vaba_validity`: Agreement (Lemma 13) and external Validity (Corollary 16) in
  every reachable state.
* `vaba_view_progress`: every view completes when honest parties deliver each other's messages
  (Lemma 19, constructive form).
* `vaba_undecided_prob`, `vaba_expected_views`: for every adaptive adversary strategy, completing
  `k` views undecided has probability `≤ (f/n)^k` with `f/n < 1/3` (Lemmas 23–24), and the expected
  number of views until a view whose leader completed its broadcast is `< 3/2` (§3.3.1).
* `Counterexample.agreement_fails`: with the literal threshold `2f + 1`, agreement fails for
  `n = 5`, `f = 1`.
-/

namespace VABA

variable {P V : Type*} [Fintype P] [DecidableEq P] {C : Cfg P V}

/-- **Agreement** (Lemma 13) with the paper's parameters. -/
theorem vaba_agreement (hn : 3 * C.f < Fintype.card P) (hQ : C.Q = Fintype.card P - C.f)
    {s : Glob P V} (hR : Reach C s) {p q : P} {v w : V} (hv : v ∈ (s.loc p).decs)
    (hw : w ∈ (s.loc q).decs) : v = w :=
  agreement (by omega) hR hv hw

/-- **External validity** (Corollary 16) with the paper's parameters. -/
theorem vaba_validity (hn : 3 * C.f < Fintype.card P) (hQ : C.Q = Fintype.card P - C.f)
    {s : Glob P V} (hR : Reach C s) {p : P} {v : V} (hv : v ∈ (s.loc p).decs) : C.valid v :=
  validity (by omega) hR hv

/-- **Views complete** (Lemma 19, constructive form) with the paper's parameters. -/
theorem vaba_view_progress (hn : 3 * C.f < Fintype.card P) (hQ : C.Q = Fintype.card P - C.f)
    (hinput : ∀ p, C.valid (C.input p)) {s : Glob P V} (hR : Reach C s) {j : ℕ} (hj : 1 ≤ j)
    (hall : ∀ p, p ∉ s.corrupt → j ≤ (s.loc p).view) :
    ∃ s', Relation.ReflTransGen (HStep C) s s' ∧ ∀ p, p ∉ s'.corrupt → j < (s'.loc p).view :=
  view_progress (by omega) (by omega) hinput hR hj hall

open Classical in
/-- **Lemmas 23–24**: some party completes `k` views without deciding with probability at most
`(f / n) ^ k`, and `f / n < 1/3`. -/
theorem vaba_undecided_prob (hn : 3 * C.f < Fintype.card P) (hQ : C.Q = Fintype.card P - C.f)
    (σ : Strategy P V) (tail : ℕ → P) (k : ℕ) :
    ((Finset.univ.filter (fun x : Fin k → P => ∃ t p,
      k < ((run C σ (coins x tail) t).loc p).view ∧
      ((run C σ (coins x tail) t).loc p).decs = ∅)).card : ℝ) / (Fintype.card P : ℝ) ^ k ≤
        ((C.f : ℝ) / Fintype.card P) ^ k ∧ (C.f : ℝ) / Fintype.card P < 1 / 3 :=
  prob_undecided_le hn hQ σ tail k

/-- **Expected number of views** (§3.3.1): less than `3/2`. -/
theorem vaba_expected_views (hn : 3 * C.f < Fintype.card P) (hQ : C.Q = Fintype.card P - C.f)
    (σ : Strategy P V) (tail : ℕ → P) (K : ℕ) :
    (∑ x : Fin K → P, (firstGoodView C σ tail K x : ℚ)) / (Fintype.card P : ℚ) ^ K < 3 / 2 :=
  expected_views_lt hn hQ σ tail K

end VABA
