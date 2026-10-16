import Papers.PODC2019.AutomaticSpeedup.Theorem1

/-!
# Warm-up II: colour reduction on rings (Brandt, PODC 2019, §4.5)

`coloring k` is proper `k`-colouring (for degree-`Δ` nodes: all `Δ` half-edges of a node carry the
node's colour; the two ends of an edge carry different colours). For `k = 2(m+1)` even, the paper
derives `(Π'_{1/2})_1` from `k`-colouring and makes it harder by keeping only the labels
`𝒴(s)`: one set out of every complementary pair of `k/2`-subsets of the colours. On rings
(`Δ = 2`) these labels behave like a proper colouring with `k' = 2^{C(k-1, k/2-1)}`
`= 2^{C(k, k/2)/2}` colours.

* `colorLabel_g`, `colorLabel_h`: the two properties checked in the paper.
* `labelHom_coloring`: `k'`-colouring maps to `(Π'_{1/2})_1` (so the latter is at most as hard).
* `colorReduction_step`: on any class of graphs of degree `≤ 2` with edge symmetry breaking at
  radius `t + 1` (e.g. an input proper colouring), a `t`-round `k'`-colouring algorithm yields a
  `(t+1)`-round `k`-colouring algorithm (Theorem 1/2, direction (2) ⇒ (1)).
* `two_mul_card_reps`: `2·|Reps m| = C(2m+2, m+1)`, i.e. `k' = 2^{C(k,k/2)/2}`; `card_reps_one`: `k = 4` gives `k' = 8`.
The resulting `O(log* n)` bound for 3-colouring rings is not formalized.
-/

namespace AutomaticSpeedup

open Problem

/-- Proper `k`-colouring as a problem: node configurations are constant, edges bichromatic. -/
def coloring (k : ℕ) : Problem (Fin k) where
  f _ := Set.univ
  g _ := {m | ∃ a b, m = {a, b} ∧ a ≠ b}
  h Δ := {m | ∃ a, m = Multiset.replicate Δ a}

/-- Representatives of complementary pairs of `(m+1)`-subsets of `Fin (2m+2)`: those containing
`0`. -/
abbrev Reps (m : ℕ) := {Z : Finset (Fin (2 * m + 2)) // Z.card = m + 1 ∧ (0 : Fin (2 * m + 2)) ∈ Z}

/-- The label `𝒴(s)`: for every representative `Z`, either `Z` (if `s Z`) or its complement. -/
def colorLabel {m : ℕ} (s : Reps m → Bool) : Set (Set (Fin (2 * m + 2))) :=
  {Y | ∃ Z : Reps m, (s Z = true ∧ Y = ↑Z.1) ∨ (s Z = false ∧ Y = ↑(Z.1ᶜ))}

theorem coloring_g_iff {k Δ : ℕ} {a b : Fin k} :
    ({a, b} : Multiset (Fin k)) ∈ (coloring k).g Δ ↔ a ≠ b := by
  constructor
  · rintro ⟨a', b', he, hne⟩
    rcases pair_eq_pair_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hne, hne.symm]
  · exact fun h => ⟨a, b, rfl, h⟩

theorem edgeAllMax_compl {m Δ : ℕ} (Z : Finset (Fin (2 * m + 2))) :
    (coloring (2 * m + 2)).EdgeAllMax Δ ↑Z ↑(Zᶜ) := by
  have hall : ∀ Y Y' : Set (Fin (2 * m + 2)),
      (coloring (2 * m + 2)).EdgeAll Δ Y Y' ↔ Disjoint Y Y' := by
    intro Y Y'
    simp only [EdgeAll, coloring, Set.subset_univ, true_and]
    constructor
    · intro h; rw [Set.disjoint_left]; intro a ha ha'
      exact ((coloring_g_iff (Δ := Δ)).1 (h a ha a ha')) rfl
    · intro h y hy z hz; exact (coloring_g_iff (Δ := Δ)).2 fun e => Set.disjoint_left.1 h hy (e ▸ hz)
  refine ⟨(hall _ _).2 (by simp [Finset.coe_compl, disjoint_compl_right]), fun Y' hY' h => ?_,
    fun Z' hZ' h => ?_⟩
  · obtain ⟨a, ha, ha'⟩ := Set.exists_of_ssubset hY'
    exact Set.disjoint_left.1 ((hall _ _).1 h) ha (by simpa using ha')
  · obtain ⟨a, ha, ha'⟩ := Set.exists_of_ssubset hZ'
    exact Set.disjoint_left.1 ((hall _ _).1 h) (by simpa using ha') ha

/-- Distinct labels `𝒴(s) ≠ 𝒴(s')` form a good edge of `(Π'_{1/2})_1` (§4.5, first property). -/
theorem colorLabel_g {m Δ : ℕ} {s s' : Reps m → Bool} (h : s ≠ s') :
    (coloring (2 * m + 2)).edgeStepMax.EdgeEx Δ (colorLabel s) (colorLabel s') := by
  obtain ⟨Z, hZ⟩ := Function.ne_iff.1 h
  refine ⟨fun _ _ => Set.subset_univ _, fun _ _ => Set.subset_univ _, ?_⟩
  cases hs : s Z <;> cases hs' : s' Z <;> simp only [hs, hs', ne_eq, not_true_eq_false] at hZ
  · refine ⟨↑(Z.1ᶜ), ⟨Z, Or.inr ⟨hs, rfl⟩⟩, ↑Z.1, ⟨Z, Or.inl ⟨hs', rfl⟩⟩, ?_⟩
    rw [Multiset.pair_comm, edgeStepMax_g_iff]; exact edgeAllMax_compl _
  · refine ⟨↑Z.1, ⟨Z, Or.inl ⟨hs, rfl⟩⟩, ↑(Z.1ᶜ), ⟨Z, Or.inr ⟨hs', rfl⟩⟩, ?_⟩
    rw [edgeStepMax_g_iff]; exact edgeAllMax_compl _

/-- Two disjoint `(m+1)`-subsets of `Fin (2m+2)` are complementary. -/
theorem eq_compl_of_disjoint {m : ℕ} {A B : Finset (Fin (2 * m + 2))} (hA : A.card = m + 1)
    (hB : B.card = m + 1) (h : Disjoint A B) : B = Aᶜ := by
  have hU : A ∪ B = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint h, hA, hB, Fintype.card_fin]; ring
  ext x
  simp only [Finset.mem_compl]
  constructor
  · intro hx hxA; exact Finset.disjoint_left.1 h hxA hx
  · intro hx
    have : x ∈ A ∪ B := hU ▸ Finset.mem_univ x
    rcases Finset.mem_union.1 this with h' | h'
    exacts [absurd h' hx, h']

/-- Every two members of `𝒴(s)` intersect, so `{𝒴(s), 𝒴(s)}` is a good node configuration of
`(Π'_{1/2})_1` on rings (§4.5, second property). -/
theorem colorLabel_h {m : ℕ} (s : Reps m → Bool) :
    (coloring (2 * m + 2)).edgeStepMax.NodeAll 2
      ((Multiset.range 2).map fun _ => colorLabel s) := by
  -- members of `𝒴(s)` are `(m+1)`-sets; two of them are never complementary
  have hmem : ∀ Y ∈ colorLabel s, ∃ A : Finset (Fin (2 * m + 2)), Y = ↑A ∧ A.card = m + 1 ∧
      ∀ Z : Reps m, (s Z = true → A ≠ Z.1ᶜ) ∧ (s Z = false → A ≠ Z.1) := by
    rintro Y ⟨Z, (⟨hs, rfl⟩ | ⟨hs, rfl⟩)⟩
    · refine ⟨Z.1, rfl, Z.2.1, fun Z' => ⟨fun _ he => ?_, fun hs' he => ?_⟩⟩
      · have := he ▸ Z.2.2; simp [Z'.2.2] at this
      · rw [Subtype.ext he] at hs; rw [hs] at hs'; cases hs'
    · refine ⟨Z.1ᶜ, rfl, by rw [Finset.card_compl, Z.2.1, Fintype.card_fin]; omega,
        fun Z' => ⟨fun hs' he => ?_, fun _ he => ?_⟩⟩
      · rw [compl_inj_iff] at he; rw [Subtype.ext he] at hs; rw [hs] at hs'; cases hs'
      · have := he ▸ Z'.2.2; simp [Z.2.2] at this
  rw [nodeAll_map_range]
  refine ⟨le_rfl, fun _ _ => fun _ _ => Set.subset_univ _, fun y hy => ?_⟩
  obtain ⟨A, hA, hAc, hAZ⟩ := hmem _ (hy 0 (by norm_num))
  obtain ⟨B, hB, hBc, -⟩ := hmem _ (hy 1 (by norm_num))
  have hne : ¬ Disjoint A B := by
    intro hd
    have hBA := eq_compl_of_disjoint hAc hBc hd
    obtain ⟨Z, (⟨hs, he⟩ | ⟨hs, he⟩)⟩ := hy 1 (by norm_num)
    · rw [hB, Finset.coe_inj, hBA] at he
      exact (hAZ Z).1 hs (by rw [← he, compl_compl])
    · rw [hB, Finset.coe_inj, hBA, compl_inj_iff] at he
      exact (hAZ Z).2 hs he
  obtain ⟨a, haA, haB⟩ := Finset.not_disjoint_iff.1 hne
  refine nodeEx_map_range_of le_rfl (fun _ _ => Set.subset_univ _) (fun _ => a) (fun i hi => ?_)
    ⟨a, by simp⟩
  interval_cases i
  · rw [hA]; exact haA
  · rw [hB]; exact haB

/-- `k'`-colouring (with `k' = 2^{|Reps m|}` colours, identified with the selectors `s`) maps to
`(Π'_{1/2})_1` derived from `(2m+2)`-colouring, on rings. -/
noncomputable def labelHom_coloring (m : ℕ) {k' : ℕ} (e : Fin k' ≃ (Reps m → Bool)) :
    LabelHom (coloring k') (coloring (2 * m + 2)).edgeStepMax.nodeStep 2 where
  φ a := colorLabel (e a)
  map_f _ _ := fun _ _ => Set.subset_univ _
  map_g := by
    rintro _ ⟨a, b, rfl, hab⟩
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    rw [← Multiset.insert_eq_cons, nodeStep_g_iff]
    exact colorLabel_g (e.injective.ne hab)
  map_h := by
    rintro _ ⟨a, rfl⟩
    show (coloring (2 * m + 2)).edgeStepMax.NodeAll 2 _
    rw [Multiset.map_replicate, show Multiset.replicate 2 (colorLabel (e a)) =
      (Multiset.range 2).map fun _ => colorLabel (e a) by simp]
    exact colorLabel_h _

/-- **Colour reduction step** (§4.5): on a class of graphs of degree `≤ 2` (rings) in which the
endpoints of every edge can be told apart at radius `t + 1` (e.g. an input proper colouring,
"any two adjacent nodes have different IDs"), a `t`-round algorithm for `k'`-colouring,
`k' = 2^{|Reps m|} = 2^{C(2m+1, m)}`, yields a `(t+1)`-round algorithm for `(2m+2)`-colouring. -/
theorem colorReduction_step {I : Type} {n t m k' : ℕ} {𝒢 : Set (LGraph I n)}
    (hk' : k' = 2 ^ Fintype.card (Reps m)) (hasym : EdgeAsym 𝒢 (t + 1))
    (h : SolvableIn 𝒢 (coloring k') 2 t) : SolvableIn 𝒢 (coloring (2 * m + 2)) 2 (t + 1) := by
  have e : Fin k' ≃ (Reps m → Bool) :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_fun, Fintype.card_bool, hk'])).symm
  have := h.of_labelHom (labelHom_coloring m e)
  exact solvableIn_of_edgeStepMax_nodeStep (Nat.le_add_left 1 t) hasym
    (by rw [Nat.add_sub_cancel]; exact this)

/-- For `k = 4` (`m = 1`): `k' = 2^3 = 8`, as in the paper. -/
theorem card_reps_one : Fintype.card (Reps 1) = 3 := by decide

/-- The paper's count: `k' = 2^{C(k, k/2)/2}`, i.e. `2 · |Reps m| = C(2m+2, m+1)`. -/
theorem two_mul_card_reps (m : ℕ) : 2 * Fintype.card (Reps m) = (2 * m + 2).choose (m + 1) := by
  classical
  have h1 := Fintype.card_finset_len (α := Fin (2 * m + 2)) (m + 1)
  rw [Fintype.card_fin] at h1
  rw [← h1, Fintype.card_subtype, Fintype.card_subtype]
  rw [← Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun Z : Finset (Fin (2 * m + 2)) => Z.card = m + 1)
    (fun Z => (0 : Fin _) ∈ Z)]
  rw [Finset.filter_filter, Finset.filter_filter, two_mul]
  congr 1
  refine Finset.card_bij (fun Z _ => Zᶜ) ?_ ?_ ?_
  · intro Z hZ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hZ ⊢
    refine ⟨?_, by simpa using hZ.2⟩
    rw [Finset.card_compl, hZ.1, Fintype.card_fin]; omega
  · intro a _ b _ h; exact compl_injective h
  · intro Z hZ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hZ
    refine ⟨Zᶜ, ?_, compl_compl Z⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · rw [Finset.card_compl, hZ.1, Fintype.card_fin]; omega
    · simpa using hZ.2

end AutomaticSpeedup
