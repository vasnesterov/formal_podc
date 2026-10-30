import Papers.PODC2018.SpannerApproximation.Theorems
import Podc.Computability.Distributed.Congest.GatherInputs

/-!
# Non-vacuity of the hypotheses of Theorems 2.8 and 1.1

The hypothesis "the algorithm outputs an `α`-approximate minimum directed `k`-spanner of every
connected loopless digraph on `V` within `T` rounds" is satisfiable: full-information gathering
(`Cslib.Congest.gatherInputsAlg`, messages of `gatherInputsBits` bits) followed by every node
selecting its arcs of a fixed minimum spanner is an exact (`α = 1`) algorithm with `T = |V|`
rounds (`exact_algorithm`).
-/

namespace Podc.SpannerApproximation

open Finset Cslib.Congest

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Every digraph has a minimum `k`-spanner (`k ≥ 1`; the digraph itself is a spanner). -/
lemma exists_min_spanner (E : Finset (V × V)) {k : ℕ} (hk : 1 ≤ k) :
    ∃ H, IsDiSpanner E H k ∧ ∀ H', IsDiSpanner E H' k → H.card ≤ H'.card := by
  classical
  have hne : (E.powerset.filter fun H => IsDiSpanner E H k).Nonempty :=
    ⟨E, by
      simp only [mem_filter, mem_powerset, subset_refl, true_and]
      exact ⟨subset_refl _, fun e he => (Relation.RelatesWithinSteps.single he).mono hk⟩⟩
  obtain ⟨H, hH, hmin⟩ := exists_min_image _ card hne
  simp only [mem_filter, mem_powerset] at hH
  refine ⟨H, hH.2, fun H' hH' => hmin H' ?_⟩
  simp only [mem_filter, mem_powerset]
  exact ⟨hH'.1, hH'⟩

/-- A fixed minimum `k`-spanner of `E`. -/
noncomputable def minSpanner (k : ℕ) (E : Finset (V × V)) : Finset (V × V) := by
  classical
  exact if h : 1 ≤ k then Classical.choose (exists_min_spanner E h) else E

/-- The digraph reconstructed from a full knowledge map of the nodes' views. -/
def recover (st : V → Option (DInput V)) : Finset (V × V) :=
  univ.filter fun q => (match st q.1 with
    | some j => (j q.2).1
    | none => false) = true

lemma recover_view (E : Finset (V × V)) : recover (fun a => some (view E a)) = E := by
  ext q; simp [recover, view]

/-- Selector of the exact algorithm: select the arcs of the minimum spanner of the reconstructed
digraph. -/
noncomputable def exactPick (k : ℕ) : V → (V → Option (DInput V)) → V → V → Bool := by
  classical
  exact fun _ st u w => decide ((u, w) ∈ minSpanner k (recover st))

/-- On a connected network, after `|V|` rounds of gathering every node knows every view. -/
lemma gather_full (E : Finset (V × V)) (hc : (net E).Connected) (v : V) :
    (gatherInputsAlg V (DInput V)).run (net E) (view E) (Fintype.card V) v =
      fun a => some (view E a) := by
  funext a
  obtain ⟨p, hp⟩ := (hc v a).exists_isPath
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1
    (gatherInputs_known (net E) (view E) _ v a p hp.length_lt.le)
  rw [hj, gatherInputs_sound (net E) (view E) _ v a j hj]

/-- **Non-vacuity.** Gathering + local computation of a minimum spanner is a deterministic exact
(`α = 1`) algorithm for minimum directed `k`-spanner (`k ≥ 1`) with `|V|` rounds, so the
hypothesis of `theorem_2_8` is satisfiable. -/
theorem exact_algorithm {k : ℕ} (hk : 1 ≤ k) (E : Finset (V × V)) (hc : (net E).Connected) :
    IsApproxDiSpanner 1 E
      (outArcs (gatherInputsAlg V (DInput V)) (exactPick k) E (Fintype.card V)) k := by
  classical
  have hout : outArcs (gatherInputsAlg V (DInput V)) (exactPick k) E (Fintype.card V) =
      minSpanner k E := by
    ext q
    simp only [outArcs, selected, mem_filter, mem_univ, true_and, gather_full E hc, exactPick,
      recover_view, Bool.or_self, decide_eq_true_eq]
  rw [hout]
  have hs := Classical.choose_spec (exists_min_spanner E hk)
  have : minSpanner k E = Classical.choose (exists_min_spanner E hk) := by
    simp [minSpanner, hk]
  rw [this]
  exact ⟨hs.1, fun H' hH' => by rw [one_mul]; exact_mod_cast hs.2 H' hH'⟩

end Podc.SpannerApproximation
