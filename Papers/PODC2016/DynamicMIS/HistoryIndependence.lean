import Papers.PODC2016.DynamicMIS.Corollary6

/-!
# Section 5: history independence

Definition 14: a dynamic algorithm is *history independent* if, for every graph `G`, the
distribution of its output depends only on `G` and not on the sequence of topology changes that
produced `G`.

We model the maintenance process with the direct implementation (Corollary 6): starting from the
greedy MIS of the initial configuration, each change is processed by running `|V|` synchronous
rounds (which suffice by `directAfter_eq_of_le`). The maintained set after any history is the greedy
MIS of the final configuration for the same order (`maintained_eq_greedyMIS`), so its distribution
only depends on the final configuration (`historyIndependent`).
-/

open Finset SimpleGraph
open scoped BigOperators

namespace DynamicMIS

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The configuration after a sequence of changes. -/
def applyAll (h : List (Change V)) (cfg : Config V) : Config V :=
  h.foldl (fun cfg c => c.apply cfg) cfg

/-- The MIS maintained along a history `h`, starting from configuration `cfg` with MIS `s`:
each change is processed by `|V|` rounds of the direct implementation on the new network. -/
noncomputable def maintained (r : V → ℕ) : List (Change V) → Config V → Set V → Set V
  | [], _, s => s
  | c :: h, cfg, s =>
    maintained r h (c.apply cfg)
      (directRun (c.apply cfg).graph (c.apply cfg).nodes r s (Fintype.card V))

/-- The maintained MIS is always the greedy MIS of the current configuration. -/
theorem maintained_eq_greedyMIS {r : V → ℕ} (hr : Function.Injective r) (h : List (Change V))
    (cfg : Config V) :
    maintained r h cfg (cfg.graph.greedyMIS cfg.nodes r) =
      (applyAll h cfg).graph.greedyMIS (applyAll h cfg).nodes r := by
  induction h generalizing cfg with
  | nil => rfl
  | cons c h ih =>
    simp only [maintained, applyAll, List.foldl_cons]
    have : directRun (c.apply cfg).graph (c.apply cfg).nodes r (cfg.graph.greedyMIS cfg.nodes r)
        (Fintype.card V) = (c.apply cfg).graph.greedyMIS (c.apply cfg).nodes r :=
      directAfter_eq_of_le hr ((Set.ncard_le_card _).trans_eq Nat.card_eq_fintype_card)
    rw [this]
    exact ih (c.apply cfg)

/-- **History independence** (Section 5). Two histories leading from the same initial
configuration to the same final configuration produce the same output for every order `π`; hence
the output distributions (over a uniformly random `π`) coincide. -/
theorem historyIndependent (cfg : Config V) (h₁ h₂ : List (Change V))
    (hfin : applyAll h₁ cfg = applyAll h₂ cfg) (P : Set V → Prop) [DecidablePred P] :
    #{π : V ≃ Fin (Fintype.card V) |
        P (maintained (orderRank π) h₁ cfg (cfg.graph.greedyMIS cfg.nodes (orderRank π)))} =
      #{π : V ≃ Fin (Fintype.card V) |
        P (maintained (orderRank π) h₂ cfg (cfg.graph.greedyMIS cfg.nodes (orderRank π)))} := by
  congr 1
  ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [maintained_eq_greedyMIS (orderRank_injective π), maintained_eq_greedyMIS
    (orderRank_injective π), hfin]

end DynamicMIS
