/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2021.ApproxByzantineOptimization.Basic

/-!
# Theorem 2: `(2f, ε)`-redundancy suffices for `(f, 2ε)`-resilience

The algorithm of the proof of Theorem 2 of the paper (Liu, Gupta, Vaidya, PODC 2021):

* Step 2: for every set `T` of `n - f` received functions pick `x_T ∈ arg min ∑_{i∈T} R i`
  (`candidate`; the paper does not say what to do when this set is empty, which can happen when `T`
  contains faulty agents: we then pick an arbitrary point), and compute
  `r_T = max_{T̂ ⊆ T, |T̂| = n - 2f} dist (x_T, arg min ∑_{i∈T̂} R i)` (`score`; the distance to an
  empty set is `⊤`);
* Step 3: output `x_S` for a set `S` minimizing `r_T` (`chosen`, `algorithm`).

`theorem_2` is the paper's statement; `theorem_2_strong` shows that the proof only needs the
redundancy and non-emptiness for the sets of non-faulty agents of the execution at hand, and no
closedness (the paper uses closedness of `arg min` sets to pick nearest points; an `inf` argument
avoids it). The setting is an arbitrary (pseudo-e)metric space `E`.
-/

open Finset Metric
open scoped ENNReal NNReal

namespace Podc.ApproxByzantineOptimization

variable {E : Type*} [PseudoEMetricSpace E] [Nonempty E] {n : ℕ}

/-- Step 2 of the algorithm: a point `x_T` of `arg min ∑_{i ∈ T} R i` (an arbitrary point if this
set is empty). -/
noncomputable def candidate (R : Profile n E) (T : Finset (Fin n)) : E := by
  classical
  exact if h : (argminSet R T).Nonempty then h.some else Classical.arbitrary E

omit [PseudoEMetricSpace E] in
lemma candidate_mem {R : Profile n E} {T : Finset (Fin n)} (h : (argminSet R T).Nonempty) :
    candidate R T ∈ argminSet R T := by
  unfold candidate
  simp only [h, ↓reduceDIte]
  exact h.some_mem

/-- Step 2, (10)–(11): `r_T = max_{T̂ ⊆ T, |T̂| = n - 2f} dist (x_T, arg min ∑_{i ∈ T̂} R i)`. -/
noncomputable def score (f : ℕ) (R : Profile n E) (T : Finset (Fin n)) : ℝ≥0∞ :=
  (T.powerset.filter fun T' => T'.card + 2 * f = n).sup fun T' =>
    infEDist (candidate R T) (argminSet R T')

lemma infEDist_le_score {f : ℕ} {R : Profile n E} {T T' : Finset (Fin n)} (h : T' ⊆ T)
    (hc : T'.card + 2 * f = n) :
    infEDist (candidate R T) (argminSet R T') ≤ score f R T :=
  Finset.le_sup (f := fun T' => infEDist (candidate R T) (argminSet R T'))
    (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 h, hc⟩)

lemma score_le {f : ℕ} {R : Profile n E} {T : Finset (Fin n)} {r : ℝ≥0∞}
    (h : ∀ T' ⊆ T, T'.card + 2 * f = n → infEDist (candidate R T) (argminSet R T') ≤ r) :
    score f R T ≤ r :=
  Finset.sup_le fun T' hT' => by
    rw [Finset.mem_filter, Finset.mem_powerset] at hT'
    exact h T' hT'.1 hT'.2

/-- The sets of `n - f` agents. -/
def bigSets (n f : ℕ) : Finset (Finset (Fin n)) := univ.filter fun T => T.card + f = n

/-- Step 3, (12): a set `S` of `n - f` agents minimizing `r_S`. -/
noncomputable def chosen (f : ℕ) (R : Profile n E) : Finset (Fin n) :=
  if h : (bigSets n f).Nonempty then
    Classical.choose (Finset.exists_min_image (bigSets n f) (score f R) h)
  else ∅

lemma chosen_spec {f : ℕ} (R : Profile n E) (h : (bigSets n f).Nonempty) :
    chosen f R ∈ bigSets n f ∧ ∀ T ∈ bigSets n f, score f R (chosen f R) ≤ score f R T := by
  unfold chosen
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec (Finset.exists_min_image (bigSets n f) (score f R) h)

/-- The algorithm of the proof of Theorem 2: output `x_S` for the set `S` chosen in Step 3. -/
noncomputable def algorithm (f : ℕ) : Algorithm n E := fun R => candidate R (chosen f R)

/-- Two sets of `n - f` agents share at least `n - 2f` agents. -/
lemma exists_subset_inter {f : ℕ} (hf : 2 * f ≤ n) {S T : Finset (Fin n)} (hS : S.card + f = n)
    (hT : T.card + f = n) : ∃ U ⊆ S ∩ T, U.card + 2 * f = n := by
  have h1 := Finset.card_union_add_card_inter S T
  have h2 : (S ∪ T).card ≤ n := by
    simpa using Finset.card_le_univ (S ∪ T)
  obtain ⟨U, hU, hc⟩ := Finset.exists_subset_card_eq (s := S ∩ T) (n := n - 2 * f) (by omega)
  exact ⟨U, hU, by omega⟩

/-- **Theorem 2, strong form.** Fix an execution: true costs `Q`, a faulty set `B`, received
functions `R` with `R i = Q i` for `i ∉ B`. Assume `2f ≤ n` and, for the sets `G` of `n - f`
non-faulty agents only: `arg min ∑_{i∈G} Q i ≠ ∅` and the `(2f, ε)`-redundancy inequality (5) for
all `Ĝ ⊆ G`, `|Ĝ| = n - 2f`. Then the output of `algorithm f` is within `2ε` of the `arg min` of
every set of `n - f` non-faulty agents. -/
theorem theorem_2_strong {f : ℕ} (hf : 2 * f ≤ n) {ε : ℝ≥0} {Q : Profile n E}
    {B : Finset (Fin n)} (R : Profile n E) (hR : ∀ i, i ∉ B → R i = Q i)
    (hne : ∀ G : Finset (Fin n), Disjoint G B → G.card + f = n → (argminSet Q G).Nonempty)
    (hred : ∀ G G' : Finset (Fin n), G' ⊆ G → Disjoint G B → G.card + f = n →
      G'.card + 2 * f = n → hausdorffEDist (argminSet Q G) (argminSet Q G') ≤ ε)
    (S : Finset (Fin n)) (hSB : Disjoint S B) (hS : S.card + f = n) :
    infEDist (algorithm f R) (argminSet Q S) ≤ 2 * (ε : ℝ≥0∞) := by
  -- on sets of non-faulty agents, received and true `arg min`s agree
  have hag : ∀ T : Finset (Fin n), Disjoint T B → argminSet R T = argminSet Q T := fun T hT =>
    argminSet_congr fun i hi => hR i (Finset.disjoint_left.1 hT hi)
  have hSmem : S ∈ bigSets n f := by simp [bigSets, hS]
  obtain ⟨hSstar, hmin⟩ := chosen_spec (f := f) R ⟨S, hSmem⟩
  set S' := chosen f R with hS'def
  have hS' : S'.card + f = n := by simpa [bigSets] using hSstar
  -- (14)–(15): `r_S ≤ ε`
  have hscoreS : score f R S ≤ ε := by
    refine score_le fun G' hG' hc => ?_
    have hmemS : candidate R S ∈ argminSet Q S := by
      rw [← hag S hSB]; exact candidate_mem (by rw [hag S hSB]; exact hne S hSB hS)
    rw [hag G' (Finset.disjoint_of_subset_left hG' hSB)]
    exact (infEDist_le_hausdorffEDist_of_mem hmemS).trans (hred S G' hG' hSB hS hc)
  -- (16): `r_{S'} ≤ r_S ≤ ε`
  have hscore' : score f R S' ≤ ε := (hmin S hSmem).trans hscoreS
  -- a common subset `Ĝ ⊆ S' ∩ S` of `n - 2f` non-faulty agents
  obtain ⟨U, hU, hUc⟩ := exists_subset_inter hf hS' hS
  have hUS : U ⊆ S := hU.trans Finset.inter_subset_right
  have hUB : Disjoint U B := Finset.disjoint_of_subset_left hUS hSB
  -- (17): `dist (x_{S'}, X_Ĝ) ≤ ε`
  have h17 : infEDist (candidate R S') (argminSet Q U) ≤ ε := by
    rw [← hag U hUB]
    exact (infEDist_le_score (hU.trans Finset.inter_subset_left) hUc).trans hscore'
  -- (18)–(19): triangle inequality through the Hausdorff distance
  have hH : hausdorffEDist (argminSet Q U) (argminSet Q S) ≤ ε := by
    rw [hausdorffEDist_comm]; exact hred S U hUS hSB hS hUc
  calc infEDist (algorithm f R) (argminSet Q S)
      ≤ infEDist (candidate R S') (argminSet Q U) + hausdorffEDist (argminSet Q U) (argminSet Q S) :=
        infEDist_le_infEDist_add_hausdorffEDist
    _ ≤ ε + ε := add_le_add h17 hH
    _ = 2 * (ε : ℝ≥0∞) := (two_mul _).symm

/-- **Theorem 2** of the paper. Under Assumption 1, if the agents' cost functions satisfy
`(2f, ε)`-redundancy (and `f < n/2`, the paper's standing assumption; `2f ≤ n` suffices), then the
algorithm of the proof is `(f, 2ε)`-resilient. -/
theorem theorem_2 {f : ℕ} (hf : 2 * f ≤ n) {ε : ℝ≥0} {Q : Profile n E} (hA : Assumption1 Q)
    (hred : IsRedundant f ε Q) : IsResilient f (2 * ε) (algorithm f) Q := by
  intro B _ R hR S hSB hS
  have := theorem_2_strong hf R hR
    (fun G _ hG => by
      rcases G.eq_empty_or_nonempty with rfl | hG0
      · simp
      · exact (hA G hG0).1)
    (fun G G' hsub _ hG hc => hred G G' hsub hG hc) S hSB hS
  simpa using this

/-- Theorem 2 only uses the non-emptiness half of Assumption 1. -/
theorem theorem_2_of_nonempty {f : ℕ} (hf : 2 * f ≤ n) {ε : ℝ≥0} {Q : Profile n E}
    (hne : ∀ G : Finset (Fin n), G.card + f = n → (argminSet Q G).Nonempty)
    (hred : IsRedundant f ε Q) : IsResilient f (2 * ε) (algorithm f) Q := by
  intro B _ R hR S hSB hS
  have := theorem_2_strong hf R hR (fun G _ hG => hne G hG)
    (fun G G' hsub _ hG hc => hred G G' hsub hG hc) S hSB hS
  simpa using this

end Podc.ApproxByzantineOptimization
