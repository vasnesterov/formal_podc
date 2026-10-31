import Papers.PODC2012.EquivocationPrice.Defs

/-!
# Theorem 2: `f`-tolerance is `(n - 2f)`-disjointness

**Theorem 2** of [JMS12]: for a 3-uniform hypergraph `H` on `n` vertices and an integer
`f ≥ n/3`, `H` is `f`-tolerant iff it is `(n - 2f)`-disjoint. The paper defers the proof to the
full version; we give one.

* (⇐, `fTolerant_of_hDisjoint`, no hypothesis on `f`): for `S, T, Z` as in Definition 1 the sets
  `A = S \ Z`, `B = T \ Z`, `C = S ∩ T` form a valid colouring for `h = n - 2f`.
* (⇒, `hDisjoint_of_fTolerant`, uses `n ≤ 3f`): from a valid colouring `A, B, C` we shrink the
  three sets to sizes `p, q, c ≥ h` with `p + q + c = 2n - 3f` (possible exactly because
  `3h ≤ 2n - 3f ⇔ n ≤ 3f`), and pad with fresh faulty vertices `Zₛ, Zₜ` outside them:
  `S = P ∪ C' ∪ Zₛ`, `T = Q ∪ C' ∪ Zₜ`, `Z = C' ∪ Zₛ ∪ Zₜ`, with `|S| = |T| = n - f`, `|Z| = f`.

For `f ≥ n/2` the paper's `h = n - 2f` is `≤ 0`; with natural-number subtraction we get `h = 0`.
Then both properties fail as soon as `n ≥ 1` (`not_fTolerant_of_le_two_mul`,
`not_hDisjoint_zero`), so the equivalence still holds. For `n = 0` it fails: `f`-tolerance is
vacuous (there are no `S ≠ T`) while `0`-disjointness is false (`theorem_2_card_zero`).
-/

namespace Podc.EquivocationPrice

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Finset (Finset V)}

/-- (⇐) of Theorem 2, for every `f`: an `(n - 2f)`-disjoint hypergraph is `f`-tolerant. -/
theorem fTolerant_of_hDisjoint {f : ℕ} (hD : HDisjoint E (Fintype.card V - 2 * f)) :
    FTolerant E f := by
  intro S T Z _ hZ hS hT hSTZ hZST
  have hZST' : Z ⊆ S ∪ T := hZST.subset
  -- `A = S \ Z`, `B = T \ Z`, `C = S ∩ T`
  have hAB : Disjoint (S \ Z) (T \ Z) := by
    rw [Finset.disjoint_left]; intro x hx hx'
    simp only [Finset.mem_sdiff] at hx hx'
    exact hx.2 (hSTZ (Finset.mem_inter.2 ⟨hx.1, hx'.1⟩))
  have hAC : Disjoint (S \ Z) (S ∩ T) := by
    rw [Finset.disjoint_left]; intro x hx hx'
    exact (Finset.mem_sdiff.1 hx).2 (hSTZ hx')
  have hBC : Disjoint (T \ Z) (S ∩ T) := by
    rw [Finset.disjoint_left]; intro x hx hx'
    exact (Finset.mem_sdiff.1 hx).2 (hSTZ hx')
  -- cardinalities
  have hSZ : (S \ Z).card + (S ∩ Z).card = S.card := Finset.card_sdiff_add_card_inter S Z
  have hTZ : (T \ Z).card + (T ∩ Z).card = T.card := Finset.card_sdiff_add_card_inter T Z
  have hSZle : (S ∩ Z).card ≤ Z.card := Finset.card_le_card Finset.inter_subset_right
  have hTZle : (T ∩ Z).card ≤ Z.card := Finset.card_le_card Finset.inter_subset_right
  -- `|S ∩ Z| + |T ∩ Z| = |Z| + |S ∩ T|` since `S ∩ T ⊆ Z ⊆ S ∪ T`
  have hZsplit : (S ∩ Z).card + (T ∩ Z).card = Z.card + (S ∩ T).card := by
    have h1 := Finset.card_union_add_card_inter (S ∩ Z) (T ∩ Z)
    have h2 : S ∩ Z ∪ T ∩ Z = Z := by
      ext x; simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (h | h) <;> exact h.2
      · intro hx; rcases Finset.mem_union.1 (hZST' hx) with h | h <;> tauto
    have h3 : S ∩ Z ∩ (T ∩ Z) = S ∩ T := by
      ext x; simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨h1, _⟩, h2, _⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        have := hSTZ (Finset.mem_inter.2 ⟨h1, h2⟩); exact ⟨⟨h1, this⟩, h2, this⟩
    rw [h2, h3] at h1; exact h1.symm
  have hUnion : (S ∪ T).card ≤ Fintype.card V := Finset.card_le_univ _
  have hInter := Finset.card_union_add_card_inter S T
  by_cases h2f : 2 * f ≤ Fintype.card V
  · obtain ⟨x, hx, y, hy, z, hz, he⟩ := hD (S \ Z) (T \ Z) (S ∩ T)
      ⟨hAB, hAC, hBC, by omega, by omega, by omega, by omega⟩
    exact ⟨x, hx, y, hy, z, hz, he⟩
  · -- `h = 0`: `0`-disjointness is impossible (take `A = B = ∅`, `C = univ`)
    exfalso
    obtain ⟨x, hx, _⟩ := hD ∅ ∅ Finset.univ
      ⟨by simp, by simp, by simp, by simp; omega, by simp; omega, by simp, by simp; omega⟩
    simp at hx

/-- `0`-disjointness never holds (take `A = B = ∅`, `C = V`). -/
theorem not_hDisjoint_zero : ¬ HDisjoint E 0 := by
  intro hD
  obtain ⟨x, hx, _⟩ := hD ∅ ∅ Finset.univ
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp; omega⟩
  simp at hx

/-- For `n ≥ 1` and `n ≤ 2f`, no hypergraph is `f`-tolerant: take `S = Z` of size `n - f` and
`T` its complement; then `S \ Z = ∅`. -/
theorem not_fTolerant_of_le_two_mul {f : ℕ} (hn : 0 < Fintype.card V)
    (h2f : Fintype.card V ≤ 2 * f) : ¬ FTolerant E f := by
  intro hT
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq
    (show Fintype.card V - f ≤ (Finset.univ : Finset V).card by simp)
  have hTc : (Finset.univ \ S).card = Fintype.card V - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]; simp
  have hne : (Finset.univ \ S).Nonempty := by
    rw [← Finset.card_pos, hTc]; omega
  obtain ⟨t, ht⟩ := hne
  have hdisj : S ∩ (Finset.univ \ S) = ∅ := by simp
  obtain ⟨x, hx, -⟩ := hT S (Finset.univ \ S) S
    (fun h => by
      have h2 : t ∈ S := by rw [h]; exact ht
      exact (Finset.mem_sdiff.1 ht).2 h2)
    (by omega) (by omega) (by omega) (by simp)
    (by
      refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_union_left, fun h => ?_⟩
      have : t ∈ S ∪ (Finset.univ \ S) := Finset.mem_union_right _ ht
      rw [← h] at this; exact (Finset.mem_sdiff.1 ht).2 this)
  simp at hx

/-- (⇒) of Theorem 2, main case `h = n - 2f ≥ 1`. -/
theorem rainbow_of_fTolerant {f : ℕ} (hT : FTolerant E f) (hn3 : Fintype.card V ≤ 3 * f)
    (h2f : 2 * f < Fintype.card V) {A B C : Finset V}
    (hv : ValidColoring (Fintype.card V - 2 * f) A B C) : Rainbow E A B C := by
  obtain ⟨hAB, hAC, hBC, ha, hb, hc, hs⟩ := hv
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card V = n := ⟨_, rfl⟩
  rw [hn] at hn3 h2f ha hb hc hs
  -- target sizes `p, q, c ≥ h` with `p + q + c = 2n - 3f`
  obtain ⟨p, q, c, hp, hq, hcc, hpA, hqB, hcC, hsum⟩ : ∃ p q c : ℕ, n - 2 * f ≤ p ∧
      n - 2 * f ≤ q ∧ n - 2 * f ≤ c ∧ p ≤ A.card ∧ q ≤ B.card ∧ c ≤ C.card ∧
      p + q + c = 2 * n - 3 * f := by
    refine ⟨min A.card (2 * n - 3 * f - 2 * (n - 2 * f)),
      min B.card (2 * n - 3 * f - min A.card (2 * n - 3 * f - 2 * (n - 2 * f)) - (n - 2 * f)),
      2 * n - 3 * f - min A.card (2 * n - 3 * f - 2 * (n - 2 * f)) -
        min B.card (2 * n - 3 * f - min A.card (2 * n - 3 * f - 2 * (n - 2 * f)) - (n - 2 * f)),
      ?_, ?_, ?_, min_le_left _ _, min_le_left _ _, ?_, ?_⟩ <;> omega
  obtain ⟨P, hPA, hPc⟩ := Finset.exists_subset_card_eq hpA
  obtain ⟨Q, hQB, hQc⟩ := Finset.exists_subset_card_eq hqB
  obtain ⟨C', hCC, hCc⟩ := Finset.exists_subset_card_eq hcC
  -- membership facts
  have dPQ : ∀ x, x ∈ P → x ∉ Q := fun x hx hx' =>
    Finset.disjoint_left.1 hAB (hPA hx) (hQB hx')
  have dPC : ∀ x, x ∈ P → x ∉ C' := fun x hx hx' =>
    Finset.disjoint_left.1 hAC (hPA hx) (hCC hx')
  have dQC : ∀ x, x ∈ Q → x ∉ C' := fun x hx hx' =>
    Finset.disjoint_left.1 hBC (hQB hx) (hCC hx')
  have hPQC : (P ∪ Q ∪ C').card = 2 * n - 3 * f := by
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
    · omega
    · exact Finset.disjoint_left.2 dPQ
    · rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_left.2 dPC, Finset.disjoint_left.2 dQC⟩
  set R := Finset.univ \ (P ∪ Q ∪ C') with hR
  have hRc : R.card = n - (2 * n - 3 * f) := by
    rw [hR, Finset.card_sdiff_of_subset (Finset.subset_univ _), hPQC]; simp [hn]
  obtain ⟨Zs, hZsR, hZsc⟩ := Finset.exists_subset_card_eq
    (show n - f - p - c ≤ R.card by omega)
  obtain ⟨Zt, hZtR, hZtc⟩ := Finset.exists_subset_card_eq
    (show n - f - q - c ≤ (R \ Zs).card by
      rw [Finset.card_sdiff_of_subset hZsR]; omega)
  have mZs : ∀ x, x ∈ Zs → x ∉ P ∧ x ∉ Q ∧ x ∉ C' := by
    intro x hx; have := hZsR hx; simp [hR] at this; tauto
  have mZt : ∀ x, x ∈ Zt → x ∉ P ∧ x ∉ Q ∧ x ∉ C' ∧ x ∉ Zs := by
    intro x hx; have := hZtR hx; simp [hR] at this; tauto
  have hpos : 0 < p := by omega
  obtain ⟨x0, hx0⟩ := Finset.card_pos.1 (hPc ▸ hpos)
  -- the sets of Definition 1
  set S := P ∪ C' ∪ Zs with hS
  set T := Q ∪ C' ∪ Zt with hT'
  set Z := C' ∪ Zs ∪ Zt with hZ
  have hSZ : S \ Z ⊆ A := by
    intro x hx; simp only [hS, hZ, Finset.mem_sdiff, Finset.mem_union] at hx
    rcases hx with ⟨(h1 | h1) | h1, h2⟩
    · exact hPA h1
    · exact absurd (Or.inl (Or.inl h1)) h2
    · exact absurd (Or.inl (Or.inr h1)) h2
  have hTZ : T \ Z ⊆ B := by
    intro x hx; simp only [hT', hZ, Finset.mem_sdiff, Finset.mem_union] at hx
    rcases hx with ⟨(h1 | h1) | h1, h2⟩
    · exact hQB h1
    · exact absurd (Or.inl (Or.inl h1)) h2
    · exact absurd (Or.inr h1) h2
  have hST : S ∩ T ⊆ C' := by
    intro x hx; simp only [hS, hT', Finset.mem_inter, Finset.mem_union] at hx
    rcases hx with ⟨(h1 | h1) | h1, (h2 | h2) | h2⟩ <;> first
      | assumption
      | exact absurd h2 (dPQ x h1)
      | exact absurd h1 (dPC x ‹_›)
      | exact absurd h2 (dPC x h1)
      | exact absurd h1 (mZs x ‹_›).1
      | exact absurd h2 (mZs x h1).2.1
      | exact absurd h1 (mZt x h2).1
      | exact absurd h1 (mZt x h2).2.2.1
      | exact absurd h1 (mZt x h2).2.2.2
  have hSTZ : S ∩ T ⊆ Z := fun x hx => by
    simp only [hZ, Finset.mem_union]; exact Or.inl (Or.inl (hST hx))
  have hx0S : x0 ∈ S := by simp [hS, hx0]
  have hx0T : x0 ∉ T := by
    simp only [hT', Finset.mem_union, not_or]
    exact ⟨⟨dPQ x0 hx0, dPC x0 hx0⟩, fun h => (mZt x0 h).1 hx0⟩
  have hx0Z : x0 ∉ Z := by
    simp only [hZ, Finset.mem_union, not_or]
    exact ⟨⟨dPC x0 hx0, fun h => (mZs x0 h).1 hx0⟩, fun h => (mZt x0 h).1 hx0⟩
  have hZsub : Z ⊆ S ∪ T := by
    intro x hx; simp only [hZ, hS, hT', Finset.mem_union] at hx ⊢; tauto
  have hZcard : Z.card ≤ f := by
    rw [hZ]
    have := Finset.card_union_le (C' ∪ Zs) Zt
    have := Finset.card_union_le C' Zs
    omega
  have hScard : S.card = p + c + (n - f - p - c) := by
    rw [hS, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, hPc, hCc, hZsc]
    · exact Finset.disjoint_left.2 dPC
    · rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_right.2 fun x h => (mZs x h).1,
        Finset.disjoint_right.2 fun x h => (mZs x h).2.2⟩
  have hTcard : T.card = q + c + (n - f - q - c) := by
    rw [hT', Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, hQc, hCc, hZtc]
    · exact Finset.disjoint_left.2 dQC
    · rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_right.2 fun x h => (mZt x h).2.1,
        Finset.disjoint_right.2 fun x h => (mZt x h).2.2.1⟩
  obtain ⟨x, hx, y, hy, z, hz, he⟩ := hT S T Z
    (fun h => hx0T (h ▸ hx0S)) hZcard (by rw [hn]; omega) (by rw [hn]; omega) hSTZ
    (Finset.ssubset_iff_subset_ne.2 ⟨hZsub, fun h => hx0Z (h ▸ Finset.mem_union_left _ hx0S)⟩)
  exact ⟨x, hSZ hx, y, hTZ hy, z, hCC (hST hz), he⟩

/-- (⇒) of Theorem 2: for `n ≥ 1` and `f ≥ n/3`, an `f`-tolerant hypergraph is
`(n - 2f)`-disjoint. -/
theorem hDisjoint_of_fTolerant {f : ℕ} (hn : 0 < Fintype.card V)
    (hn3 : Fintype.card V ≤ 3 * f) (hT : FTolerant E f) :
    HDisjoint E (Fintype.card V - 2 * f) := by
  by_cases h2f : 2 * f < Fintype.card V
  · exact fun A B C hv => rainbow_of_fTolerant hT hn3 h2f hv
  · exact absurd hT (not_fTolerant_of_le_two_mul hn (by omega))

/-- **Theorem 2** of [JMS12]. Let `H` be a 3-uniform hypergraph on `n ≥ 1` vertices and
`f ≥ n/3`. Then `H` is `f`-tolerant iff it is `(n - 2f)`-disjoint. (3-uniformity is not
needed.) -/
theorem theorem_2 {f : ℕ} (hn : 0 < Fintype.card V) (hn3 : Fintype.card V ≤ 3 * f) :
    FTolerant E f ↔ HDisjoint E (Fintype.card V - 2 * f) :=
  ⟨hDisjoint_of_fTolerant hn hn3, fTolerant_of_hDisjoint⟩

/-- Theorem 2 needs `n ≥ 1`: on the empty vertex set every hypergraph is `f`-tolerant
(vacuously) but not `(n - 2f)`-disjoint. -/
theorem theorem_2_card_zero (f : ℕ) :
    FTolerant (∅ : Finset (Finset (Fin 0))) f ∧
      ¬ HDisjoint (∅ : Finset (Finset (Fin 0))) (Fintype.card (Fin 0) - 2 * f) := by
  refine ⟨fun S T _ hST _ _ _ _ _ => absurd (Subsingleton.elim S T) hST, ?_⟩
  simpa using (not_hDisjoint_zero (E := (∅ : Finset (Finset (Fin 0)))))

end Podc.EquivocationPrice
