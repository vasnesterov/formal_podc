import Papers.PODC2020.SelfStabHighDynamics.Section3
import Papers.PODC2020.SelfStabHighDynamics.Alg1.Main

/-!
# Algorithm 1 and closure (Section 3.3, after Remark 3)

* `alg1_not_closed`: for `Δ ≥ 2` and at least two processes, no set of legitimate configurations
  of Algorithm 1 is closed (Theorem 1; Algorithm 1 is size-ambiguous).
* `corollary_1_as_stated_false`: Corollary 1 as printed ("if `L` is closed, then `A` is not
  size-ambiguous") is false: for a single process, the quasi-legitimate configurations of
  Algorithm 1 form a closed set of legitimate configurations, and Algorithm 1 is size-ambiguous.
  Only the contrapositive of Theorem 1 ("`A` is not `(k, V)`-ambiguous", `corollary_1`) holds.
-/

namespace Podc.SelfStabHighDynamics

open StabilizingLEDynamic (JssB)
open Alg1 (alg QLegit)

variable {ι : Type*} [LinearOrder ι]

/-- For `Δ ≥ 2` and `|V| ≥ 2`, no set of legitimate configurations of Algorithm 1 for `V` is
closed in `TC_B(Δ)`. -/
theorem alg1_not_closed {Δ : ℕ} (hΔ : 2 ≤ Δ) {V : Finset ι} (hV : 2 ≤ V.card)
    {L : Set (ι → Alg1.St ι)}
    (hL : IsLegit (alg Δ (by omega)) (JssB Δ) (spLE (alg Δ (by omega))) V L) :
    ¬ Closed (alg Δ (by omega)) (JssB Δ) V L :=
  theorem_1 hΔ (Alg1.selfStab _) hL (Alg1.ambiguous _ hV)

/-- For a single process `a`, the quasi-legitimate configurations of Algorithm 1 form a closed
set of legitimate configurations. -/
theorem alg1_singleton_closed {Δ : ℕ} (hΔ : 0 < Δ) (a : ι) :
    IsLegit (alg Δ hΔ) (JssB Δ) (spLE (alg Δ hΔ)) {a} {γ | γ ∈ (alg Δ hΔ).Cfg {a} ∧ QLegit {a} γ} ∧
    Closed (alg Δ hΔ) (JssB Δ) {a} {γ | γ ∈ (alg Δ hΔ).Cfg {a} ∧ QLegit {a} γ} := by
  have hcl : Closed (alg Δ hΔ) (JssB Δ) {a} {γ | γ ∈ (alg Δ hΔ).Cfg {a} ∧ QLegit {a} γ} :=
    fun G hG γ hγ t => ⟨Alg1.exec_mem_Cfg hΔ G hγ.1 t, Alg1.lemma_2 hΔ hG.1 hγ.2 t⟩
  refine ⟨⟨fun _ h => h.1, fun G hG γ hγ => ⟨2 * Δ, Alg1.exec_mem_Cfg hΔ G hγ (2 * Δ),
    Alg1.corollary_4 hΔ hG.1 hγ⟩, fun G hG γ hγ => ⟨a, Finset.mem_singleton_self a,
      fun t q hq => ?_⟩⟩, hcl⟩
  have := (hcl G hG γ hγ t).2.1 q hq
  exact Finset.mem_singleton.mp this

/-- **Corollary 1 as stated is false.** For every `Δ ≥ 2`, Algorithm 1 is a self-stabilizing
leader election algorithm for `TC_B(Δ)` with, for `V = {0}`, a closed set of legitimate
configurations, but it is size-ambiguous. -/
theorem corollary_1_as_stated_false {Δ : ℕ} (hΔ : 2 ≤ Δ) :
    ∃ (A : SAlg ℕ (Alg1.St ℕ)) (V : Finset ℕ) (L : Set (ℕ → Alg1.St ℕ)),
      SelfStab A (JssB Δ) (spLE A) ∧ IsLegit A (JssB Δ) (spLE A) V L ∧
      Closed A (JssB Δ) V L ∧ SizeAmbiguous A :=
  ⟨alg Δ (by omega), {0}, _, Alg1.selfStab _, (alg1_singleton_closed (by omega) 0).1,
    (alg1_singleton_closed (by omega) 0).2, Alg1.sizeAmbiguous _⟩

end Podc.SelfStabHighDynamics
