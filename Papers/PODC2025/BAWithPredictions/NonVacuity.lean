import Papers.PODC2025.BAWithPredictions.MessageLowerBound
import Papers.PODC2025.BAWithPredictions.Plurality
import Papers.PODC2024.AllBAExpensive.Solvability
import Cslib.Computability.Distributed.Byzantine.PartialSync.ICSync
import Cslib.Computability.Distributed.Byzantine.PartialSync.DolevStrong

/-!
# Non-vacuity of the message lower bound

The hypothesis of `message_lower_bound` is satisfiable: Byzantine agreement with predictions
(strong unanimity on the value component; predictions ignored) is solvable in synchrony

* without signatures for `n > 3t` (`strongUnanimity_solvableSync`), and
* with signatures for `n > 2t` (`strongUnanimity_solvableAuthSync`),

via interactive consistency (CSLib) and the reduction "decide the plurality of the agreed
vector" (Algorithm 2 of the All-BA-Expensive formalization).
-/

namespace BAWithPredictions

open Finset Cslib.Byzantine.PartialSync

variable {P V Pr : Type} [Fintype P] [DecidableEq P] [Nonempty V]

/-- Strong unanimity satisfies the containment condition when `n > 2t`: decide the plurality of
the values of the agreed vector. -/
theorem cc_strongUnanimity {t : ℕ} (h2t : 2 * t < Fintype.card P) :
    AllBAExpensive.ContainmentCondition t (strongUnanimity P V Pr) := by
  classical
  refine ⟨fun c => (plur univ (fun q => (c q).map Prod.fst) none).getD (Classical.arbitrary V),
    fun c _ c' hc' hcc' w hw => ?_⟩
  have hsub : c'.procs ⊆ univ.filter fun q => (c q).map Prod.fst = some w := by
    intro q hq
    rw [Config.mem_procs_iff_ne_none] at hq
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hq
    have := hcc' q hq
    simp only [mem_filter, mem_univ, true_and]
    rw [this, hx, Option.map_some, hw q x hx]
  have hcnt := card_le_card hsub
  unfold IsInputConfig at hc'
  have hp : plur univ (fun q => (c q).map Prod.fst) none = some w := by
    refine plur_eq_of_majority ?_
    have e : cnt univ (fun q => (c q).map Prod.fst) (some w) =
        (univ.filter fun q => (c q).map Prod.fst = some w).card := rfl
    rw [e, card_univ]
    omega
  simp only [hp, Option.getD_some]

/-- BA with predictions is solvable in synchrony without signatures if `n > 3t`. -/
theorem strongUnanimity_solvableSync {t : ℕ} (δ : ℕ) (h3t : 3 * t < Fintype.card P) :
    (strongUnanimity P V Pr).SolvableSync t δ :=
  AllBAExpensive.solvableSync_of_containmentCondition (cc_strongUnanimity (by omega))
    (icSolvableSync_of_three_t_lt h3t)

/-- BA with predictions is solvable in synchrony with signatures if `n > 2t`. -/
theorem strongUnanimity_solvableAuthSync {t : ℕ} (δ : ℕ) (h2t : 2 * t < Fintype.card P) :
    (strongUnanimity P V Pr).SolvableAuthSync t δ :=
  AllBAExpensive.solvableAuthSync_of_containmentCondition (cc_strongUnanimity h2t)
    (icSolvableAuthSync_dolevStrong (by omega))

end BAWithPredictions
