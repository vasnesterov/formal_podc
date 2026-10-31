import Papers.PODC2015.WeakestFDEventualConsistency.Driver

/-!
# Lemma 5: from eventual irrevocable consensus to eventual consensus (Algorithm 7)

Algorithm 7 of [DGKPS15] (Appendix A.3): on invocation of `proposeEC_ℓ(v)`, set `count := ℓ`
and invoke `proposeEIC_ℓ(v)`; on a response `v` of `proposeEIC_ℓ`, if `count = ℓ`, return `v` to
`proposeEC_ℓ`.

The application is folded into the algorithm (`inp p j` is the value `p` proposes to instance
`j`; instance `0` is invoked at the first step, instance `j + 1` in the step returning the
response to `j`), and so is the counter: the algorithm is the `Driver` whose data is trivial.
The EIC black box is given by its invocations (outputs `DOut.bb`) and its responses (input events
`(j, v)` chosen by the adversary), and is constrained only by the hypotheses of `lemma5`:

* it responds only to invoked instances (`RespAfterInv`);
* if it is used properly (`ProperUseEIC`, which the transformation guarantees:
  `Driver.bbHist_properUseEIC`), it satisfies EIC with agreement among **correct** processes
  (`EICCorrect`). The uniform (literal) EIC-Agreement is not needed.

The conclusion is the **uniform** EC of `Specs` (agreement among all processes from some instance
on): faulty processes reach only finitely many instances (`[Finite P]`), so beyond them only
correct processes respond.
-/

namespace Podc.WeakestFDEventualConsistency

open Cslib.FailureDetectors

namespace Alg7

variable {P V R : Type*} [DecidableEq P]

/-- **Algorithm 7** of [DGKPS15] (with the application folded in): the driver that forwards
each EC instance to the EIC instance with the same number and returns the first response. -/
def driver (inp : P → ℕ → V) : Driver P Unit V (AOut V) where
  d0 := ()
  startOut p := [.inv 0 (inp p 0)]
  upd _ _ _ _ := ()
  respOut p c x _ := [.resp c x, .inv (c + 1) (inp p (c + 1))]
  prop p j _ := inp p j

variable {inp : P → ℕ → V} {r : Run P R (ℕ × V)}

open Driver

lemma resp_iff {p : P} {j : ℕ} {v : V} {t : ℕ} :
    ((driver inp).appHist r).resp p j v t ↔
      (driver inp).n r p t = j + 1 ∧ r.σ t = some (p, .input (j, v)) := by
  simp only [appHist, out_app_iff]
  constructor
  · rintro (⟨-, -, -, h⟩ | ⟨c, x, hc, hσ, h⟩)
    · simp [driver] at h
    · simp only [driver, List.mem_cons, AOut.resp.injEq, reduceCtorEq, List.not_mem_nil,
        or_false] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hc, hσ⟩
  · rintro ⟨hc, hσ⟩
    exact Or.inr ⟨j, v, hc, hσ, by simp [driver]⟩

lemma inv_iff {p : P} {j : ℕ} {v : V} {t : ℕ} :
    ((driver inp).appHist r).inv p j v t ↔ ((driver inp).bbHist r).inv p j v t := by
  simp only [appHist, bbHist, out_iff']
  rcases (driver inp).step_cases r t p with ⟨-, h⟩ | ⟨-, hσ, -, hout⟩ | ⟨c, x, -, hσ, -, hout⟩
  · simp only [out_iff'] at h
    exact ⟨fun h' => absurd h' (h _), fun h' => absurd h' (h _)⟩
  · rw [hout]; simp [driver, hσ, and_comm]
  · rw [hout]; simp [driver, hσ, and_comm]

/-- The application's history produced by Algorithm 7 respects the usage assumption of EC. -/
theorem appHist_properUse (hR : ((driver inp).bbHist r).RespAfterInv) :
    ((driver inp).appHist r).ProperUse where
  inv_once p j v v' t t' h h' :=
    (bbHist_properUseEIC hR).inv_once p j v v' t t' (inv_iff.1 h) (inv_iff.1 h')
  inv_succ p j v t h := by
    obtain ⟨x, hx, -⟩ := (bbHist_properUseEIC hR).inv_succ p j v t (inv_iff.1 h)
    obtain ⟨h0, h1, -⟩ := out_bb_iff.1 (inv_iff.1 h)
    exact ⟨x, resp_iff.2 ⟨h0, hx⟩⟩
  resp_inv p j v t h := by
    obtain ⟨h0, hσ⟩ := resp_iff.1 h
    exact ⟨_, inv_iff.2 (out_bb_iff.2 ⟨h0, trans_of_input hσ h0, rfl⟩)⟩

/-- **Lemma 5** of [DGKPS15] (Algorithm 7): eventual irrevocable consensus can be transformed into
eventual consensus. In every admissible run of Algorithm 7 whose EIC black box responds only to
invoked instances and satisfies EIC (with agreement among correct processes) when used properly,
the application history satisfies (uniform) EC, and respects EC's usage assumption. -/
theorem lemma5 [Finite P] (hA : ((driver inp).alg R).Admissible r)
    (hR : ((driver inp).bbHist r).RespAfterInv)
    (hbb : ((driver inp).bbHist r).ProperUseEIC → EICCorrect r.F ((driver inp).bbHist r)) :
    EC r.F ((driver inp).appHist r) ∧ ((driver inp).appHist r).ProperUse := by
  obtain ⟨hterm, ⟨k₀, hint⟩, hagr, hval⟩ := hbb (bbHist_properUseEIC hR)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, appHist_properUse hR⟩
  · -- EC-Termination
    intro p hp j
    obtain ⟨v, t, h⟩ := hterm p hp j
    obtain ⟨t₁, x₁, -, h₁, -, hσ⟩ := exists_trans_of_resp hR h
    exact ⟨x₁, t₁, resp_iff.2 ⟨h₁, hσ⟩⟩
  · -- EC-Integrity
    intro p j v v' t t' h h'
    obtain ⟨h0, hσ⟩ := resp_iff.1 h
    obtain ⟨h0', hσ'⟩ := resp_iff.1 h'
    have := trans_unique (Dr := driver inp) (r := r) p (h0.trans h0'.symm)
      (by rw [trans_of_input hσ h0, h0]) (by rw [trans_of_input hσ' h0', h0'])
    subst this
    rw [hσ] at hσ'
    simp only [Option.some.injEq, Prod.mk.injEq, Choice.input.injEq, true_and] at hσ'
    exact ⟨rfl, hσ'⟩
  · -- EC-Validity
    intro p j v t h
    obtain ⟨q, t', ht', hinv⟩ := hval p j v t (resp_iff.1 h).2
    exact ⟨q, t', ht', inv_iff.2 hinv⟩
  · -- EC-Agreement
    obtain ⟨N, hN⟩ := exists_bound_faulty hA
    refine ⟨max k₀ (N + 1), fun j hj p q v v' t t' h h' => ?_⟩
    obtain ⟨h0, hσ⟩ := resp_iff.1 h
    obtain ⟨h0', hσ'⟩ := resp_iff.1 h'
    have hp : r.F.Correct p := by
      by_contra hp; have := hN p hp t; omega
    have hq : r.F.Correct q := by
      by_contra hq; have := hN q hq t'; omega
    by_contra hne
    refine hagr p q j hp hq fun T => ⟨max T (max t t' + 1), le_max_left _ _, v, v', hne, ?_, ?_⟩
    · refine ⟨t, by omega, hσ, fun t₁ v₁ h₁ h₂ hr => ?_⟩
      have := (hint j (by omega) p v v₁ t t₁ hσ hr).1; omega
    · refine ⟨t', by omega, hσ', fun t₁ v₁ h₁ h₂ hr => ?_⟩
      have := (hint j (by omega) q v' v₁ t' t₁ hσ' hr).1; omega

end Alg7

end Podc.WeakestFDEventualConsistency
