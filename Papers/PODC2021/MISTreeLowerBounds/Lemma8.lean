import Papers.PODC2021.MISTreeLowerBounds.Lemma6

/-!
# Lemma 8: `Π⁺_Δ(a, x)` is solvable in 0 rounds given a solution of `R̄(R(Π_Δ(a, x)))`

The proof of Lemma 8 does not compute `R̄(R(Π_Δ(a, x)))` completely. Instead it introduces a
problem `Π_rel` whose labels are the six sets `MUBQ, XMOUABPQ, PQ, OUABPQ, ABPQ, UBPQ` of labels of
`R(Π_Δ(a, x))` (in the renaming `L8` of Lemma 6) and which is `Π⁺_Δ(a, x)` after renaming
`M, X, P, O, A, C` to these sets (`toRel8`, `toRel`). The argument has two parts:

* every node configuration of `R̄(R(Π_Δ(a, x)))` can be *relaxed* to a node configuration of
  `Π_rel` (Definition 7), i.e. each set of the configuration is contained in the corresponding
  set of a configuration of `Π⁺` (`lemma_8_relax`; we choose the `Π⁺`-label per position, which
  absorbs the permutation of Definition 7);
* the edge constraint of `Π_rel` is obtained from the edge constraint of `R(Π_Δ(a, x))` by the
  method of §2.3 (two sets are compatible iff they contain an edge configuration of
  `R(Π_Δ(a, x))`), and after renaming it is the edge constraint of `Π⁺` (`toRel_edge`).

Hence replacing each set by the chosen superset is a 0-round reduction (`lemma_8_reduction`).

The relaxation part works with the sets `Y8 i ⊆ L8` corresponding to the sets `Y i` of a node
configuration of `R̄(R(Π))`: they are nonempty, right-closed for the inclusion order of the
renamed sets (Observation 4, Figure 5) and every choice satisfies the node constraint `N8` of
`R(Π_Δ(a, x))` (Lemma 6). The combinatorial core is `relax8`.
-/

namespace Podc.MISTreeLowerBounds

open Problem Finset

variable {Δ : ℕ}

/-! ### The problem `Π_rel` -/

/-- `[UBPQ]`. -/
def setUBPQ : Finset L8 := {.U, .B, .P, .Q}

/-- The renaming of Lemma 8 (after renaming the labels of `R(Π_Δ(a, x))` as in Lemma 6):
`M ↦ MUBQ`, `X ↦ XMOUABPQ`, `P ↦ PQ`, `O ↦ OUABPQ`, `A ↦ ABPQ`, `C ↦ UBPQ`. -/
def toRel8 : L6 → Finset L8
  | .M => setMUBQ
  | .X => univ
  | .P => setPQ
  | .O => setOUABPQ
  | .A => setABPQ
  | .C => setUBPQ

/-- The label of `Π_rel` corresponding to a label of `Π⁺_Δ(a, x)`, as a set of labels of
`R(Π_Δ(a, x))` (i.e. a set of sets of labels of `Π_Δ(a, x)`). -/
def toRel (ℓ : L6) : Finset (Finset L5) := (toRel8 ℓ).image toSet

theorem toRel_edge_all :
    ∀ ℓ ℓ' : L6, (∃ m ∈ toRel8 ℓ, ∃ m' ∈ toRel8 ℓ', E8 m m') ↔ E6 ℓ ℓ' := by
  decide

/-- Lemma 8 (edge constraint of `Π_rel`): two labels of `Π_rel` are compatible according to the
method of §2.3 (they contain labels forming an edge configuration `XQ, OB, AU, PM` of
`R(Π_Δ(a, x))`) iff the corresponding labels of `Π⁺_Δ(a, x)` form an edge configuration. -/
theorem toRel_edge (ℓ ℓ' : L6) : (∃ m ∈ toRel8 ℓ, ∃ m' ∈ toRel8 ℓ', E8 m m') ↔ E6 ℓ ℓ' :=
  toRel_edge_all ℓ ℓ'

/-! ### Right-closed sets of labels of `R(Π_Δ(a, x))` -/

/-- A set of labels of `R(Π_Δ(a, x))` that is right-closed w.r.t. the diagram of Figure 5 (the
inclusion order of the renamed sets). -/
def RClosed (Z : Finset L8) : Prop := ∀ m m', m ∈ Z → toSet m ⊆ toSet m' → m' ∈ Z

namespace RClosed

variable {Z : Finset L8}

/-- A right-closed set without `P` is contained in `MUBQ`. -/
theorem subset_MUBQ (hZ : RClosed Z) (h : L8.P ∉ Z) : Z ⊆ setMUBQ := by
  intro m hm
  cases m <;> first | decide | exact (h (hZ _ _ hm (by decide))).elim

/-- A right-closed set without `U` is contained in `ABPQ`. -/
theorem subset_ABPQ (hZ : RClosed Z) (h : L8.U ∉ Z) : Z ⊆ setABPQ := by
  intro m hm
  cases m <;> first | decide | exact (h (hZ _ _ hm (by decide))).elim

/-- A right-closed set without `M` is contained in `OUABPQ`. -/
theorem subset_OUABPQ (hZ : RClosed Z) (h : L8.M ∉ Z) : Z ⊆ setOUABPQ := by
  intro m hm
  cases m <;> first | decide | exact (h (hZ _ _ hm (by decide))).elim

/-- A right-closed set without `B` is contained in `PQ` (every label outside `PQ` is below `B`). -/
theorem subset_PQ (hZ : RClosed Z) (h : L8.B ∉ Z) : Z ⊆ setPQ := by
  intro m hm
  cases m <;> first | decide | exact (h (hZ _ _ hm (by decide))).elim

/-- A right-closed subset of `OUABPQ` without `A` is contained in `UBPQ`. -/
theorem subset_UBPQ (hZ : RClosed Z) (h0 : Z ⊆ setOUABPQ) (h : L8.A ∉ Z) : Z ⊆ setUBPQ := by
  intro m hm
  cases m <;> first | decide | exact (h (hZ _ _ hm (by decide))).elim |
    exact absurd (h0 hm) (by decide)

end RClosed

/-! ### The combinatorial core -/

/-- If the positions of `S` carry labels with property `K` and those of `T` labels without it,
then `|S| + |T| ≤ Δ`. -/
theorem card_add_card_le_of_prop {α : Type*} {m : Fin Δ → α} {K : α → Prop}
    {S T : Finset (Fin Δ)} (hS : ∀ j ∈ S, K (m j)) (hT : ∀ j ∈ T, ¬ K (m j)) :
    S.card + T.card ≤ Δ := by
  classical
  rw [← card_union_of_disjoint (disjoint_left.2 fun j hjS hjT => hT j hjT (hS j hjS))]
  exact (card_le_univ _).trans (by simp)

/-- The positions whose set contains the label `ℓ`. -/
abbrev withLabel (Y : Fin Δ → Finset L8) (ℓ : L8) : Finset (Fin Δ) := univ.filter fun i => ℓ ∈ Y i

/-- The positions whose set does not contain the label `ℓ`. -/
abbrev withoutLabel (Y : Fin Δ → Finset L8) (ℓ : L8) : Finset (Fin Δ) :=
  univ.filter fun i => ℓ ∉ Y i

theorem card_withLabel_add (Y : Fin Δ → Finset L8) (ℓ : L8) :
    (withLabel Y ℓ).card + (withoutLabel Y ℓ).card = Δ := by
  rw [card_filter_add_card_filter_not]; simp

/-- The configuration with label `ℓ` on `S` and `X` elsewhere relaxes `Y` as soon as the sets on
`S` are contained in `toRel8 ℓ`. -/
theorem subset_toRel8_ite {Y : Fin Δ → Finset L8} (S : Finset (Fin Δ)) (ℓ : L6)
    (h : ∀ i ∈ S, Y i ⊆ toRel8 ℓ) (i : Fin Δ) :
    Y i ⊆ toRel8 (if i ∈ S then ℓ else .X) := by
  split_ifs with hi
  · exact h i hi
  · exact fun _ _ => mem_univ _

/-- The core of Lemma 8 (proof, first part), in terms of the labels of `R(Π_Δ(a, x))`: if the sets
`Y i` are nonempty and right-closed and every choice from them is a node configuration of
`R(Π_Δ(a, x))`, then `Y` can be relaxed to a node configuration of `Π_rel`. -/
theorem relax8 {a x : ℕ} (hxa : x + 2 ≤ a) (ha : a ≤ Δ) {Y : Fin Δ → Finset L8}
    (hne : ∀ i, (Y i).Nonempty) (hcl : ∀ i, RClosed (Y i))
    (hN : ∀ m : Fin Δ → L8, (∀ i, m i ∈ Y i) → N8 Δ a x m) :
    ∃ σ : Fin Δ → L6, σ ∈ (PiPlus Δ a x).node ∧ ∀ i, Y i ⊆ toRel8 (σ i) := by
  classical
  simp only [PiPlus, Set.mem_ofPred_eq]
  -- At least `x + 2` sets contain `P`, otherwise relax to `MUBQ^{Δ-x-1} XMOUABPQ^{x+1}`.
  by_cases hPa : Δ - x - 1 ≤ (withoutLabel Y .P).card
  · obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq hPa
    refine ⟨fun i => if i ∈ S then .M else .X, Or.inl ?_,
      subset_toRel8_ite S .M fun i hi => (hcl i).subset_MUBQ (by simpa using hS hi)⟩
    have := cnt_ite S (ℓ₁ := L6.M) (ℓ₂ := L6.X) (by decide); omega
  have hP : x + 2 ≤ (withLabel Y .P).card := by have := card_withLabel_add Y .P; omega
  -- At least `Δ - a + x + 2` sets contain `U`, otherwise relax to
  -- `ABPQ^{a-x-1} XMOUABPQ^{Δ-a+x+1}`.
  by_cases hUa : a - x - 1 ≤ (withoutLabel Y .U).card
  · obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq hUa
    refine ⟨fun i => if i ∈ S then .A else .X, Or.inr (Or.inr (Or.inl ?_)),
      subset_toRel8_ite S .A fun i hi => (hcl i).subset_ABPQ (by simpa using hS hi)⟩
    have := cnt_ite S (ℓ₁ := L6.A) (ℓ₂ := L6.X) (by decide); omega
  have hU : Δ - a + x + 2 ≤ (withLabel Y .U).card := by have := card_withLabel_add Y .U; omega
  let d : ∀ j, L8 := fun j => (hne j).choose
  have hd : ∀ j, d j ∈ Y j := fun j => (hne j).choose_spec
  -- No set contains `M`: otherwise choose `M`, `x + 1` times `P` and `Δ - a` times `U`.
  have hM : ∀ i, L8.M ∉ Y i := by
    intro i hi
    obtain ⟨SP, hSP, hSPc⟩ := exists_subset_card_eq (s := (withLabel Y .P).erase i) (n := x + 1)
      (by have := pred_card_le_card_erase (s := withLabel Y .P) (a := i); omega)
    obtain ⟨SU, hSU, hSUc⟩ := exists_subset_card_eq (s := (withLabel Y .U).erase i \ SP)
      (n := Δ - a) (by
        have := pred_card_le_card_erase (s := withLabel Y .U) (a := i)
        have := le_card_sdiff SP ((withLabel Y .U).erase i); omega)
    have hSPi : ∀ j ∈ SP, j ≠ i ∧ L8.P ∈ Y j := fun j hj => by simpa using hSP hj
    have hSUi : ∀ j ∈ SU, (j ≠ i ∧ L8.U ∈ Y j) ∧ j ∉ SP := fun j hj => by simpa using hSU hj
    let m : Fin Δ → L8 := fun j =>
      if j = i then .M else if j ∈ SP then .P else if j ∈ SU then .U else d j
    have hm : ∀ j, m j ∈ Y j := by
      intro j
      simp only [m]
      split_ifs with h1 h2 h3
      · exact h1 ▸ hi
      · exact (hSPi j h2).2
      · exact (hSUi j h3).1.2
      · exact hd j
    have hmP : ∀ j ∈ SP, m j = .P := fun j hj => by simp [m, (hSPi j hj).1, hj]
    have hmU : ∀ j ∈ SU, m j = .U := fun j hj => by
      simp [m, (hSUi j hj).1.1, (hSUi j hj).2, hj]
    have hmi : m i = .M := by simp [m]
    rcases hN m hm with ⟨S, hS, hSM⟩ | ⟨k, hk, hk'⟩ | ⟨S, hS, hSA⟩
    · have := card_add_card_le_of_prop (T := SP) hSM fun j hj => by rw [hmP j hj]; decide
      omega
    · by_cases hki : k = i
      · subst hki; rw [hmi] at hk; exact absurd hk (by decide)
      · have := hk' i (Ne.symm hki); rw [hmi] at this; exact absurd this (by decide)
    · have hiSU : i ∉ SU := fun h => (hSUi i h).1.1 rfl
      have := card_add_card_le_of_prop (T := insert i SU) hSA fun j hj => by
        rcases mem_insert.1 hj with rfl | hj
        · rw [hmi]; decide
        · rw [hmU j hj]; decide
      rw [card_insert_of_notMem hiSU] at this
      omega
  have hO : ∀ i, Y i ⊆ setOUABPQ := fun i => (hcl i).subset_OUABPQ (hM i)
  -- Every set contains `B`, otherwise relax to `PQ OUABPQ^{Δ-1}`.
  by_cases hBa : ∃ i, L8.B ∉ Y i
  · obtain ⟨i, hi⟩ := hBa
    refine ⟨fun j => if j ∈ ({i} : Finset (Fin Δ)) then .P else .O, Or.inr (Or.inl ?_),
      fun j => ?_⟩
    · have := cnt_ite {i} (ℓ₁ := L6.P) (ℓ₂ := L6.O) (by decide)
      simpa using this
    · by_cases hj : j = i
      · subst hj; simpa [toRel8] using (hcl j).subset_PQ hi
      · simpa [toRel8, hj] using hO j
  push Not at hBa
  -- At least `x + 1` sets contain `A`, otherwise relax to `UBPQ^{Δ-x} XMOUABPQ^x`.
  by_cases hAa : Δ - x ≤ (withoutLabel Y .A).card
  · obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq hAa
    refine ⟨fun i => if i ∈ S then .C else .X, Or.inr (Or.inr (Or.inr ?_)),
      subset_toRel8_ite S .C fun i hi => (hcl i).subset_UBPQ (hO i) (by simpa using hS hi)⟩
    have := cnt_ite S (ℓ₁ := L6.C) (ℓ₂ := L6.X) (by decide); omega
  have hA : x + 1 ≤ (withLabel Y .A).card := by have := card_withLabel_add Y .A; omega
  -- Contradiction: choose `x + 1` times `A`, `Δ - a + 1` times `U` and `B` elsewhere.
  exfalso
  obtain ⟨SA, hSA, hSAc⟩ := exists_subset_card_eq hA
  obtain ⟨SU, hSU, hSUc⟩ := exists_subset_card_eq (s := withLabel Y .U \ SA) (n := Δ - a + 1)
    (by have := le_card_sdiff SA (withLabel Y .U); omega)
  have hSAi : ∀ j ∈ SA, L8.A ∈ Y j := fun j hj => by simpa using hSA hj
  have hSUi : ∀ j ∈ SU, L8.U ∈ Y j ∧ j ∉ SA := fun j hj => by simpa using hSU hj
  let m : Fin Δ → L8 := fun j => if j ∈ SA then .A else if j ∈ SU then .U else .B
  have hm : ∀ j, m j ∈ Y j := by
    intro j
    simp only [m]
    split_ifs with h1 h2
    · exact hSAi j h1
    · exact (hSUi j h2).1
    · exact hBa j
  have hmA : ∀ j ∈ SA, m j = .A := fun j hj => by simp [m, hj]
  have hmU : ∀ j ∈ SU, m j = .U := fun j hj => by simp [m, (hSUi j hj).2, hj]
  rcases hN m hm with ⟨S, hS, hSM⟩ | ⟨k, hk, -⟩ | ⟨S, hS, hSA'⟩
  · have := card_add_card_le_of_prop (T := SA) hSM fun j hj => by rw [hmA j hj]; decide
    omega
  · revert hk; simp only [m]; split_ifs <;> decide
  · have := card_add_card_le_of_prop (T := SU) hSA' fun j hj => by rw [hmU j hj]; decide
    omega

/-! ### From `R̄(R(Π_Δ(a, x)))` to the renamed labels -/

/-- Lemma 8 (proof, first part): every node configuration of `R̄(R(Π_Δ(a, x)))` can be relaxed
to a node configuration of `Π_rel`; we choose the `Π⁺_Δ(a, x)`-label of each position, which
absorbs the permutation of Definition 7. -/
theorem lemma_8_relax {a x : ℕ} (hxa : x + 2 ≤ a) (ha : a ≤ Δ) {Y : Fin Δ → Finset (Finset L5)}
    (hY : Y ∈ (Pi Δ a x).R.Rbar.node) :
    ∃ σ : Fin Δ → L6, σ ∈ (PiPlus Δ a x).node ∧ ∀ i, Y i ⊆ toRel (σ i) := by
  classical
  change (Pi Δ a x).R.nodeMax Y at hY
  -- Every set occurring in `Y` is a label of `R(Π_Δ(a, x))`.
  have hrange : ∀ i, ∀ s ∈ Y i, ∃ m, toSet m = s := by
    intro i s hs
    let y : Fin Δ → Finset L5 := Function.update (fun j => (hY.1.1 j).choose) i s
    have hy : y ∈ (Pi Δ a x).R.node := hY.1.2 y fun j => by
      by_cases hj : j = i
      · subst hj; simpa [y] using hs
      · simpa [y, Function.update_of_ne hj] using (hY.1.1 j).choose_spec
    have := hy.1 i
    rw [alphR_Pi] at this
    simpa [y] using this
  let Y8 : Fin Δ → Finset L8 := fun i => univ.filter fun m => toSet m ∈ Y i
  have hne : ∀ i, (Y8 i).Nonempty := by
    intro i
    obtain ⟨s, hs⟩ := hY.1.1 i
    obtain ⟨m, rfl⟩ := hrange i s hs
    exact ⟨m, by simpa [Y8] using hs⟩
  have hcl : ∀ i, RClosed (Y8 i) := by
    intro i m m' hm hmm'
    simp only [Y8, mem_filter, mem_univ, true_and] at hm ⊢
    exact hY.mem_of_stronger hm (R_nodeStronger hmm' (by rw [alphR_Pi]; exact ⟨m', rfl⟩))
  have hN : ∀ m : Fin Δ → L8, (∀ i, m i ∈ Y8 i) → N8 Δ a x m := by
    intro m hm
    refine (R_Pi_node (by omega) ha m).1 (hY.1.2 _ fun i => ?_)
    simpa [Y8] using hm i
  obtain ⟨σ, hσ, hsub⟩ := relax8 hxa ha hne hcl hN
  refine ⟨σ, hσ, fun i s hs => ?_⟩
  obtain ⟨m, rfl⟩ := hrange i s hs
  exact mem_image_of_mem _ (hsub i (by simpa [Y8] using hs))

/-- Lemma 8 (0-round reduction): for `x + 2 ≤ a ≤ Δ`, `Π⁺_Δ(a, x)` can be solved in 0 rounds
given a solution of `R̄(R(Π_Δ(a, x)))`: each node replaces each set of its configuration by the
superset given by `lemma_8_relax`, i.e. outputs the corresponding `Π⁺`-label. -/
theorem lemma_8_reduction {a x : ℕ} (hxa : x + 2 ≤ a) (ha : a ≤ Δ) :
    ZeroRoundReduction (Pi Δ a x).R.Rbar (PiPlus Δ a x) := by
  classical
  let f : (Fin Δ → Finset (Finset L5)) → (Fin Δ → L6) := fun Y =>
    if hY : Y ∈ (Pi Δ a x).R.Rbar.node then (lemma_8_relax hxa ha hY).choose else fun _ => .X
  have hf : ∀ Y (hY : Y ∈ (Pi Δ a x).R.Rbar.node),
      f Y ∈ (PiPlus Δ a x).node ∧ ∀ i, Y i ⊆ toRel (f Y i) := fun Y hY => by
    simp only [f, hY, dite_true]; exact (lemma_8_relax hxa ha hY).choose_spec
  refine ⟨f, fun Y hY => (hf Y hY).1, fun Y hY Y' hY' c hc => ?_⟩
  obtain ⟨-, -, s, hs, s', hs', hss'⟩ := hc
  obtain ⟨m, hm, rfl⟩ := mem_image.1 ((hf Y hY).2 c hs)
  obtain ⟨m', hm', rfl⟩ := mem_image.1 ((hf Y' hY').2 c hs')
  exact (toRel_edge _ _).1 ⟨m, hm, m', hm', (edgeMax_toSet a x m m').1 hss'⟩

end Podc.MISTreeLowerBounds
