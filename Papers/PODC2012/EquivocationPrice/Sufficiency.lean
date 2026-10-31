import Papers.PODC2012.EquivocationPrice.Defs

/-!
# Theorem 13: the sufficiency number `Uₙ(h)`

**Theorem 13** of [JMS12] claims, for `h ≤ n/3`,
`Uₙ(h) = C(n,3) − ((n − h)/2)·h² + 1`.
The proof (Claim 14, Proposition 15) minimises `abc` over integers `a, b, c ≥ h` with
`a + b + c ≥ (n + 3h)/2` and finds `a = b = h`, `c = (n − h)/2`, assuming `n ≡ h (mod 2)` ("the
second case is proved similarly"). For `n ≢ h (mod 2)` the minimum over integers is
`h²·⌈(n − h)/2⌉`, so the correct value is

  `Uₙ(h) = C(n,3) − h²·⌈(n − h)/2⌉ + 1`   (`theorem_13`),

and the displayed formula is wrong (not even an integer when `h` is odd) for every `n ≢ h`
(mod 2) with `h ≥ 1`: there the true value is smaller by `h²/2` (`theorem_13_false`;
e.g. `U₄(1) = 3`, not `3.5`: `U_four_one`).

The integer minimisation (Claim 14) is elementary: `ab ≥ h(a + b − h)` for `a, b ≥ h`, applied
twice, gives `abc ≥ h²(a + b + c − 2h)` (`mul_mul_ge`). The paper's real-variable argument
(Proposition 15) also contains a wrong statement, recorded in `differencies.md`: along the faces
`a = h` etc. of the polytope the critical point is a maximum, not the minimum.
-/

namespace Podc.EquivocationPrice

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Claim 14 of [JMS12] (integer form): for `a, b, c ≥ h`, `abc ≥ h²(a + b + c − 2h)`. -/
theorem mul_mul_ge {a b c h : ℕ} (ha : h ≤ a) (hb : h ≤ b) (hc : h ≤ c) :
    h * h * (a + b + c - 2 * h) ≤ a * b * c := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le hc
  have : h + a' + (h + b') + (h + c') - 2 * h = h + a' + b' + c' := by omega
  rw [this]
  nlinarith [Nat.zero_le (h * a' * b'), Nat.zero_le (h * a' * c'), Nat.zero_le (h * b' * c'),
    Nat.zero_le (a' * b' * c')]

/-- Claim 14 of [JMS12], corrected: over valid colourings the number of crossing triples is at
least `h²·⌈(n − h)/2⌉`. -/
theorem card_crossing_ge {h : ℕ} {A B C : Finset V} (hv : ValidColoring h A B C) :
    h * h * ((Fintype.card V - h + 1) / 2) ≤ (crossing A B C).card := by
  obtain ⟨hAB, hAC, hBC, ha, hb, hc, hs⟩ := hv
  rw [card_crossing hAB hAC hBC]
  refine le_trans (Nat.mul_le_mul_left _ ?_) (mul_mul_ge ha hb hc)
  omega

/-- A 3-uniform hypergraph with more than `C(n,3) − h²⌈(n − h)/2⌉` edges is `h`-disjoint. -/
theorem hDisjoint_of_card {h : ℕ} {E : Finset (Finset V)} (hE : Uniform3 E)
    (hcard : (Fintype.card V).choose 3 - h * h * ((Fintype.card V - h + 1) / 2) < E.card) :
    HDisjoint E h := by
  intro A B C hv
  by_contra hR
  rw [rainbow_iff, not_not] at hR
  have h2 := card_crossing_ge hv
  obtain ⟨hAB, hAC, hBC, -⟩ := hv
  have hsub : E ⊆ (Finset.univ : Finset V).powersetCard 3 \ crossing A B C := by
    intro e he
    refine Finset.mem_sdiff.2 ⟨?_, Finset.disjoint_left.1 hR he⟩
    rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, hE e he⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (crossing_subset_univ hAB hAC hBC),
    Finset.card_powersetCard, Finset.card_univ] at h1
  omega

/-- A colouring with parts of sizes `h, h, ⌈(n − h)/2⌉` (exists for `3h ≤ n`). -/
theorem exists_extremal_coloring {h : ℕ} (h3 : 3 * h ≤ Fintype.card V) :
    ∃ A B C : Finset V, Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ A.card = h ∧
      B.card = h ∧ C.card = (Fintype.card V - h + 1) / 2 := by
  obtain ⟨A, -, hA⟩ := Finset.exists_subset_card_eq
    (show h ≤ (Finset.univ : Finset V).card by simp; omega)
  have hB0 : h ≤ (Finset.univ \ A).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]; simp; omega
  obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq hB0
  have hC0 : (Fintype.card V - h + 1) / 2 ≤ ((Finset.univ \ A) \ B).card := by
    rw [Finset.card_sdiff_of_subset hB, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp; omega
  obtain ⟨C, hC, hCc⟩ := Finset.exists_subset_card_eq hC0
  refine ⟨A, B, C, ?_, ?_, ?_, hA, hBc, hCc⟩
  · exact Finset.disjoint_right.2 fun x hx => (Finset.mem_sdiff.1 (hB hx)).2
  · exact Finset.disjoint_right.2 fun x hx =>
      (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 (hC hx)).1).2
  · exact Finset.disjoint_right.2 fun x hx => (Finset.mem_sdiff.1 (hC hx)).2

/-- `h²⌈(n − h)/2⌉ ≤ C(n,3)` for `3h ≤ n` (the crossing triples of the extremal colouring). -/
theorem sq_mul_le_choose {h : ℕ} (h3 : 3 * h ≤ Fintype.card V) :
    h * h * ((Fintype.card V - h + 1) / 2) ≤ (Fintype.card V).choose 3 := by
  obtain ⟨A, B, C, hAB, hAC, hBC, hA, hB, hC⟩ := exists_extremal_coloring (V := V) h3
  have := Finset.card_le_card (crossing_subset_univ hAB hAC hBC)
  rwa [card_crossing hAB hAC hBC, hA, hB, hC, Finset.card_powersetCard,
    Finset.card_univ] at this

/-- The densest non-`h`-disjoint hypergraph: all triples except those crossing a colouring with
parts of sizes `h, h, ⌈(n − h)/2⌉`. -/
theorem exists_not_hDisjoint {h : ℕ} (h3 : 3 * h ≤ Fintype.card V) :
    ∃ E : Finset (Finset V), Uniform3 E ∧ ¬ HDisjoint E h ∧
      E.card = (Fintype.card V).choose 3 - h * h * ((Fintype.card V - h + 1) / 2) := by
  obtain ⟨A, B, C, hAB, hAC, hBC, hA, hBc, hCc⟩ := exists_extremal_coloring (V := V) h3
  refine ⟨(Finset.univ : Finset V).powersetCard 3 \ crossing A B C, ?_, ?_, ?_⟩
  · intro e he; exact (Finset.mem_powersetCard.1 (Finset.mem_sdiff.1 he).1).2
  · intro hD
    have := hD A B C ⟨hAB, hAC, hBC, hA.ge, hBc.ge, by omega, by omega⟩
    rw [rainbow_iff] at this
    exact this Finset.sdiff_disjoint
  · rw [Finset.card_sdiff_of_subset (crossing_subset_univ hAB hAC hBC),
      Finset.card_powersetCard, Finset.card_univ, card_crossing hAB hAC hBC, hA, hBc, hCc]

/-- **Theorem 13** of [JMS12], corrected: for `h ≤ n/3`,
`Uₙ(h) = C(n,3) − h²·⌈(n − h)/2⌉ + 1`. (The paper writes `(n − h)/2` instead of
`⌈(n − h)/2⌉`, which is right only for `n ≡ h (mod 2)`.) -/
theorem theorem_13 {n h : ℕ} (h3 : 3 * h ≤ n) :
    U n h = n.choose 3 - h ^ 2 * ((n - h + 1) / 2) + 1 := by
  have hmem : n.choose 3 - h ^ 2 * ((n - h + 1) / 2) + 1 ∈
      {m | ∀ E : Finset (Finset (Fin n)), Uniform3 E → m ≤ E.card → HDisjoint E h} := by
    intro E hE hc
    exact hDisjoint_of_card hE (by simp only [Fintype.card_fin]; rw [sq] at hc; omega)
  apply le_antisymm (Nat.sInf_le hmem)
  refine le_csInf ⟨_, hmem⟩ fun m hm => ?_
  obtain ⟨E, hE, hnD, hc⟩ := exists_not_hDisjoint (V := Fin n) (h := h) (by simpa using h3)
  simp only [Fintype.card_fin] at hc
  by_contra hlt
  exact hnD (hm E hE (by rw [hc, ← sq]; omega))

/-- `U₄(1) = 3` (the formula of Theorem 13 gives `3.5`). -/
theorem U_four_one : U 4 1 = 3 := by
  rw [theorem_13 (by norm_num)]; decide

/-- **Theorem 13** of [JMS12] is false as stated whenever `n ≢ h (mod 2)` and `h ≥ 1`: then
`Uₙ(h)` is smaller than the displayed value `C(n,3) − ((n − h)/2)·h² + 1` by `h²/2`. -/
theorem theorem_13_false {n h : ℕ} (h3 : 3 * h ≤ n) (h1 : 1 ≤ h) (hodd : (n - h) % 2 = 1) :
    (U n h : ℝ) = (n.choose 3 : ℝ) - ((n : ℝ) - h) / 2 * h ^ 2 + 1 - (h : ℝ) ^ 2 / 2 ∧
      (U n h : ℝ) ≠ (n.choose 3 : ℝ) - ((n : ℝ) - h) / 2 * h ^ 2 + 1 := by
  have hle := sq_mul_le_choose (V := Fin n) (h := h) (by simpa using h3)
  simp only [Fintype.card_fin] at hle
  obtain ⟨k, hk⟩ : ∃ k, n - h = 2 * k + 1 := ⟨(n - h) / 2, by omega⟩
  have hceil : (n - h + 1) / 2 = k + 1 := by omega
  have hnk : (n : ℝ) - h = 2 * k + 1 := by
    have : n = h + (2 * k + 1) := by omega
    rw [this]; push_cast; ring
  rw [theorem_13 h3, hceil, sq]
  rw [hceil] at hle
  push_cast [hle]
  rw [hnk]
  have : (1 : ℝ) ≤ h := by exact_mod_cast h1
  constructor
  · ring
  · intro h'; nlinarith

/-- The objective of Proposition 15 of [JMS12]: `g(a, b) = ab((n + 3h)/2 − a − b)`. -/
noncomputable def gObj (n h a b : ℝ) : ℝ := a * b * ((n + 3 * h) / 2 - a - b)

/-- Proposition 15 of [JMS12], second bullet, is false: it claims that the minimum of `g` along
the faces of the triangle `P = {a ≥ h, b ≥ h, a + b ≤ (n + h)/2}` is `(n + h)²h/16`; that value
is the critical value (a maximum) along a face. For `n = 4`, `h = 1` the point `(1, 1)` lies on
the face `a = h` and `g(1, 1) = 3/2 < 25/16`. (A claim inside the proof of Theorem 13; the
proof's final comparison still yields the right value, see `differencies.md`.) -/
theorem prop_15_face_false :
    let n : ℝ := 4; let h : ℝ := 1
    ∃ b : ℝ, h ≤ b ∧ h + b ≤ (n + h) / 2 ∧ gObj n h h b < (n + h) ^ 2 * h / 16 := by
  refine ⟨1, ?_, ?_, ?_⟩ <;> norm_num [gObj]

end Podc.EquivocationPrice
