import Papers.PODC2022.ArrowTopology.Complexes
import Papers.PODC2022.ArrowTopology.DomainBridge
import Papers.PODC2022.ArrowTopology.BaseCase
import Papers.PODC2022.ArrowTopology.Reduction

/-!
# Arrow's impossibility theorem via combinatorial topology — main results

S. Rajsbaum, A. Raventós-Pujol, *A Distributed Combinatorial Topology Approach to Arrow's
Impossibility Theorem*, PODC 2022.

* `theorem_2_2_base`: **Theorem 2.2** for `n = 2`, `|X| = 3`: a unanimous simplicial map
  `N_I → N_O` is a projection. Proved by the index-lemma argument of Section 3
  (`theorem_2_2_signs`, using Theorem 3.1 `Cslib.Simplicial.index_eq_content` and Lemma 3.2
  `lemma_3_2`), transported from the sign model to the set-theoretic complexes.
* `arrow_two_three`: Arrow's theorem for two voters and three alternatives (via Propositions 3, 4).
* `theorem_2_1`: **Theorem 2.1** (Arrow's impossibility theorem), for every finite set of at least
  two voters and every (possibly infinite) set of at least three alternatives (Lemmas 5.1, 5.2).
* `theorem_2_2`: **Theorem 2.2** in general.
-/

namespace Podc.ArrowTopology

open Cslib.SocialChoice PreAbstractSimplicialComplex

universe u

variable {X : Type*}

namespace ThreeAlts

variable (T : ThreeAlts X)

theorem ranks_sig1 (r : Pref X) (j : Fin 3) : Ranks r (T.pr j).1 (T.pr j).2 (T.sig1 r j) := by
  cases h : T.sig1 r j
  · exact (T.sig1_eq_false_iff r j).1 h
  · exact (T.sig1_eq_true_iff r j).1 h

end ThreeAlts

/-- **Theorem 2.2** of [Rajsbaum–Raventós-Pujol, PODC 2022] for two voters and three
alternatives (Section 3, proof by the index lemma): if `f : N_I → N_O` is a simplicial map with
`f (U^{(+,+)}_{αβ}) = U^+_{αβ}` for all `α ≠ β`, then `f` is a projection. -/
theorem theorem_2_2_base (T : ThreeAlts X) {f : VI (Fin 2) X → VO X}
    (hs : IsSimplicialMap (NI (Fin 2) X) (NO X) f) (hu : IsUnanimousMap f) : IsProjection f := by
  classical
  have hc := isChromatic_of_unanimous hs hu
  have hne := T.pr_fst_ne_snd
  -- the sign function of `f`
  let s : Vtx (Fin 2) → Bool := fun v =>
    decide (f (vI (T.pr v.1).1 (T.pr v.1).2 v.2 (hne v.1)) = vO _ _ true (hne v.1))
  have hsv : ∀ j σ, f (vI (T.pr j).1 (T.pr j).2 σ (hne j)) = vO _ _ (s (j, σ)) (hne j) := by
    intro j σ
    rcases chromatic_sign hc σ (hne j) with e | e
    · simp only [s, e, decide_true]
    · have : ¬ vO (T.pr j).1 (T.pr j).2 false (hne j) = vO _ _ true (hne j) :=
        fun e' => absurd (vO_inj e') (by decide)
      simp only [s, e, this, decide_false]
  have hU : SignUnanimous s := by
    intro j b
    cases b
    · have h1 := hu _ _ (hne j).symm
      have e1 : vI (ι := Fin 2) (T.pr j).2 (T.pr j).1 (fun _ => true) (hne j).symm =
          vI (T.pr j).1 (T.pr j).2 (fun _ => false) (hne j) :=
        vI_swap (ι := Fin 2) _ _ (fun _ => false) (hne j)
      have e2 : vO (T.pr j).2 (T.pr j).1 true (hne j).symm =
          vO (T.pr j).1 (T.pr j).2 false (hne j) := vO_swap _ _ false (hne j)
      rw [e1, e2] at h1
      have h2 := hsv j (fun _ => false)
      rw [h1] at h2
      exact (vO_inj h2).symm
    · have h2 := hsv j (fun _ => true)
      rw [hu _ _ (hne j)] at h2
      exact (vO_inj h2).symm
  have hS : SignSimplicial s := by
    intro t ht
    obtain ⟨R, hR⟩ := T.exists_sig_eq t ht
    rw [NI, NO, isSimplicialMap_nerve_iff] at hs
    have hmem : ∀ j, R ∈ U (T.pr j).1 (T.pr j).2 (t j) := by
      intro j i; rw [← hR]; exact T.ranks_sig1 (R i) j
    obtain ⟨r, hr⟩ := hs {vI _ _ (t 0) (hne 0), vI _ _ (t 1) (hne 1), vI _ _ (t 2) (hne 2)}
      (by simp) ⟨R, by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl <;> exact hmem _⟩
    have hj : ∀ j, T.sig1 r j = s (j, t j) := by
      intro j
      have : r ∈ (f (vI _ _ (t j) (hne j))).1 := by
        fin_cases j
        · exact hr _ (by simp)
        · exact hr _ (by simp)
        · exact hr _ (by simp)
      rw [hsv] at this
      exact ranks_unique (T.ranks_sig1 r j) this
    have := T.sig1_outTri r
    rwa [hj 0, hj 1, hj 2] at this
  obtain ⟨k, hk⟩ := theorem_2_2_signs hU hS
  refine ⟨k, fun a b σ h => ?_⟩
  obtain ⟨j, hj | hj⟩ := T.exists_pr a b h
  · have hv : vI a b σ h = vI (T.pr j).1 (T.pr j).2 σ (hne j) :=
      Subtype.ext (by simp only [vI, hj])
    rw [hv, hsv, hk]
    exact Subtype.ext (by simp only [vO, hj])
  · have hv : vI a b σ h = vI (T.pr j).1 (T.pr j).2 (fun i => !σ i) (hne j) := by
      apply Subtype.ext; simp only [vI, hj]; exact (U_swap a b σ).symm
    rw [hv, hsv, hk]
    apply Subtype.ext; simp only [vO, hj]; exact Uo_swap a b (σ k)

/-- Arrow's impossibility theorem for two voters and any three alternatives, obtained from the
topological Theorem 2.2 through Propositions 3 and 4. -/
theorem arrow_two_three (T : ThreeAlts X) : ArrowHolds (Fin 2) X := by
  intro F hU hI
  obtain ⟨f, hFf, hc, hs⟩ := prop_3_forward hI
  have hu := (prop_4_unanimity hFf hc).1 hU
  exact (prop_4_dictatorial hFf hc).2 (theorem_2_2_base T hs hu)

theorem arrow_base (Y : Type*) (hY : Nat.card Y = 3) : ArrowHolds (Fin 2) Y := by
  have : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  let e := (Finite.equivFinOfCardEq hY).symm
  exact arrow_two_three
    { x := e 0, y := e 1, z := e 2
      hxy := by simp [e]
      hyz := by simp [e]
      hxz := by simp [e]
      cover := by
        intro w
        obtain ⟨j, rfl⟩ := e.surjective w
        fin_cases j <;> simp }

/-- **Theorem 2.1** of [Rajsbaum–Raventós-Pujol, PODC 2022] (Arrow's impossibility theorem).
Let `|X| ≥ 3` and `n ≥ 2` (here: any finite set of voters `ι` with at least two elements; `X` may
be infinite). There is no aggregation map `F : W^n → W` satisfying unanimity, independence of
irrelevant alternatives and non-dictatorship. -/
theorem theorem_2_1 {ι : Type*} [Finite ι] {X : Type u} (hι : 2 ≤ Nat.card ι)
    (hX : ∃ x y z : X, x ≠ y ∧ y ≠ z ∧ x ≠ z) :
    ¬ ∃ F : Aggregation ι X, Unanimity F ∧ IIA F ∧ ¬ Dictatorial F := by
  rintro ⟨F, hU, hI, hD⟩
  exact hD (arrow_of_base (fun Y hY => arrow_base Y hY) hι hX F hU hI)

/-- **Theorem 2.2** of [Rajsbaum–Raventós-Pujol, PODC 2022] (Arrow's impossibility,
combinatorial-topology form). Let `|X| ≥ 3` and `n ≥ 2`. If `f : N_I → N_O` is a simplicial map
such that `f (U^{(+,…,+)}_{αβ}) = U^+_{αβ}` for all vertices `U^{(+,…,+)}_{αβ}`, then `f` is a
projection. (No chromaticity assumption is needed: it follows from unanimity,
`isChromatic_of_unanimous`.) -/
theorem theorem_2_2 {ι : Type*} [Finite ι] {X : Type u} (hι : 2 ≤ Nat.card ι)
    (hX : ∃ x y z : X, x ≠ y ∧ y ≠ z ∧ x ≠ z) {f : VI ι X → VO X}
    (hs : IsSimplicialMap (NI ι X) (NO X) f) (hu : IsUnanimousMap f) : IsProjection f := by
  have : Nonempty ι := by
    have : 0 < Nat.card ι := by omega
    exact (Nat.card_pos_iff.1 this).1
  have hc := isChromatic_of_unanimous hs hu
  obtain ⟨F, hI, hFf⟩ := prop_3_backward hc hs
  have hU := (prop_4_unanimity hFf hc).2 hu
  exact (prop_4_dictatorial hFf hc).1 (arrow_of_base (fun Y hY => arrow_base Y hY) hι hX F hU hI)

end Podc.ArrowTopology
