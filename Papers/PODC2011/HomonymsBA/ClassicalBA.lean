import Cslib.Computability.Distributed.Byzantine.PartialSync.ICSync
import Cslib.Computability.Distributed.Byzantine.PartialSync.Containment
import Mathlib

/-!
# Classical synchronous Byzantine agreement for `n > 3t` (black box of Proposition 2)

Proposition 2 of the paper transforms "any synchronous Byzantine agreement algorithm for `ℓ`
processes with unique identifiers (such algorithms exist when `ℓ = n > 3t`, e.g. [13])". We take
the classical model of CSLib (`Cslib.Byzantine.PartialSync`, synchronous runs `gst = 0` with
delay bound `δ = 0`, i.e. lock-step rounds) and obtain such an algorithm from CSLib's
interactive consistency for `n > 3t` (Pease–Shostak–Lamport) and the containment-condition
reduction (Civit et al.): Byzantine agreement validity (`baValidity`, "if all correct processes
propose `v`, only `v` may be decided") satisfies the containment condition for `n > 2t`.

Main result: `classicalBA_exists`.
-/

namespace Podc.HomonymsBA

open Cslib.Byzantine.PartialSync Finset

variable {P V : Type*} [Fintype P] [DecidableEq P]

/-- Byzantine agreement validity: if all processes of `π(c)` propose `v`, only `v` is admissible. -/
def baValidity (P V : Type*) : ValidityProperty P V V :=
  fun c => {w | ∀ v, (∀ p, c p ≠ none → c p = some v) → w = v}

open Classical in
/-- `baValidity` satisfies the containment condition for `n > 2t`: decide the value proposed by
at least `n - t` processes of the configuration (if any). -/
theorem baValidity_containment [Nonempty V] {t : ℕ} (hn : 2 * t < Fintype.card P) :
    (baValidity P V).ContainmentCondition t := by
  refine ⟨fun c => if h : ∃ v, Fintype.card P - t ≤ (univ.filter fun p => c p = some v).card
    then Classical.choose h else Classical.arbitrary V, ?_⟩
  intro c _ c' hc' hcont v hv
  -- the procs of `c'` all propose `v` in `c`
  have hsub : c'.procs ⊆ univ.filter fun p => c p = some v := by
    intro p hp
    rw [Config.mem_procs_iff_ne_none] at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcont p hp]; exact hv p hp
  have hcard : Fintype.card P - t ≤ (univ.filter fun p => c p = some v).card :=
    le_trans hc' (Finset.card_le_card hsub)
  have hex : ∃ v, Fintype.card P - t ≤ (univ.filter fun p => c p = some v).card := ⟨v, hcard⟩
  simp only [dif_pos hex]
  have hu := Classical.choose_spec hex
  by_contra huv
  set U := univ.filter fun p => c p = some (Classical.choose hex)
  set W := univ.filter fun p => c p = some v
  have hdisj : Disjoint U W := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    rw [h1] at h2
    exact huv (Option.some_injective _ h2)
  have h1 := Finset.card_union_of_disjoint hdisj
  have h2 := Finset.card_le_univ (U ∪ W)
  have h3 : Fintype.card P - t ≤ U.card := hu
  have h4 : Fintype.card P - t ≤ W.card := hcard
  omega

/-- **Classical synchronous Byzantine agreement** exists for `n > 3t` processes with unique
identifiers (lock-step rounds: `gst = 0`, `δ = 0`). -/
theorem classicalBA_exists {P : Type} [Fintype P] [DecidableEq P] {V : Type} [Nonempty V]
    {t : ℕ} (hn : 3 * t < Fintype.card P) :
    ∃ (M S : Type) (A : Algorithm P M S V V), SolvesConsensusSync t 0 A (baValidity P V) :=
  (baValidity_containment (by omega)).solvableSync (icSolvableSync_of_three_t_lt hn)

end Podc.HomonymsBA
