import Papers.PODC2021.MISTreeLowerBounds.Family

/-!
# Lemma 6: the problem `R(Π_Δ(a, x))`

After renaming the eight sets `X, MX, OX, MOX, AOX, MAOX, PAOX, MPAOX` to `X, M, O, U, A, B, P, Q`
(`L8`, `toSet`), the alphabet of `R(Π_Δ(a, x))` is exactly these eight sets (`alphR_Pi`), its edge
constraint is `XQ`, `OB`, `AU`, `PM` (`edgeMax_toSet`), and its node constraint is
`[MUBQ]^{Δ-x} [XMOUABPQ]^x`, `[PQ] [OUABPQ]^{Δ-1}`, `[ABPQ]^a [XMOUABPQ]^{Δ-a}` (`R_Pi_node`).

The edge part is a finite computation (the edge constraint `E5` does not depend on `Δ, a, x`):
maximal pairs are the pairs `(A, B)` with `B = partner A` and `A = partner B` (`edgeMax_iff`), which
`decide` checks over the 32 subsets of `L5`.
-/

namespace Podc.MISTreeLowerBounds

open Problem

variable {Δ : ℕ}

/-! ### Maximal edge configurations via the partner map -/

namespace Problem

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The largest set of labels compatible with every label of `A`. -/
def partner (P : Problem Δ Λ) [DecidableRel P.edge] (A : Finset Λ) : Finset Λ :=
  Finset.univ.filter fun b => ∀ a ∈ A, P.edge a b

theorem edgeMax_iff (P : Problem Δ Λ) [DecidableRel P.edge] (A B : Finset Λ) :
    P.edgeMax A B ↔ A.Nonempty ∧ B.Nonempty ∧ B = P.partner A ∧ A = P.partner B := by
  have hsub : ∀ A B, P.EdgeAll A B → B ⊆ P.partner A := fun A B h b hb => by
    simp only [partner, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun a ha => h.2.2 a ha b hb
  have hsub' : ∀ A B, P.EdgeAll A B → A ⊆ P.partner B := fun A B h => hsub B A h.symm
  have hall : ∀ A, A.Nonempty → (P.partner A).Nonempty → P.EdgeAll A (P.partner A) :=
    fun A hA hB => ⟨hA, hB, fun a ha b hb => by
      simp only [partner, Finset.mem_filter, Finset.mem_univ, true_and] at hb; exact hb a ha⟩
  have anti : ∀ A A', A ⊆ A' → P.partner A' ⊆ P.partner A := fun A A' h b hb => by
    simp only [partner, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact fun a ha => hb a (h ha)
  constructor
  · rintro ⟨h, hmax⟩
    have hB : B = P.partner A := by
      have := hmax A (P.partner A) le_rfl (hsub A B h)
        (hall A h.1 (h.2.1.mono (hsub A B h)))
      exact this.2.symm
    have hA : A = P.partner B := by
      have := hmax (P.partner B) B (hsub' A B h) le_rfl
        ((hall B h.2.1 (h.1.mono (hsub' A B h))).symm)
      exact this.1.symm
    exact ⟨h.1, h.2.1, hB, hA⟩
  · rintro ⟨hA, hB, rfl, hAB⟩
    refine ⟨hall A hA hB, fun A' B' hAA' hBB' h' => ?_⟩
    have h1 : B' ⊆ P.partner A := (hsub A' B' h').trans (anti A A' hAA')
    have h2 : A' ⊆ A := by
      rw [hAB]; exact (hsub' A' B' h').trans (anti _ _ hBB')
    exact ⟨le_antisymm h2 hAA', le_antisymm h1 hBB'⟩

end Problem

/-! ### Renaming -/

/-- The labels of `R(Π_Δ(a, x))` after renaming. -/
inductive L8 | X | M | O | U | A | B | P | Q
  deriving DecidableEq, Repr

instance : Fintype L8 where
  elems := {.X, .M, .O, .U, .A, .B, .P, .Q}
  complete x := by cases x <;> decide

/-- The renaming of Lemma 6: `X ↦ {X}`, `M ↦ {M,X}`, `O ↦ {O,X}`, `U ↦ {M,O,X}`, `A ↦ {A,O,X}`,
`B ↦ {M,A,O,X}`, `P ↦ {P,A,O,X}`, `Q ↦ {M,P,A,O,X}`. -/
def toSet : L8 → Finset L5
  | .X => {.X}
  | .M => {.M, .X}
  | .O => {.O, .X}
  | .U => {.M, .O, .X}
  | .A => {.A, .O, .X}
  | .B => {.M, .A, .O, .X}
  | .P => {.P, .A, .O, .X}
  | .Q => {.M, .P, .A, .O, .X}

theorem toSet_injective : Function.Injective toSet := by decide

/-- The edge constraint of `R(Π_Δ(a, x))` after renaming: `XQ`, `OB`, `AU`, `PM`. -/
def E8 : L8 → L8 → Prop
  | .X, .Q | .Q, .X | .O, .B | .B, .O | .A, .U | .U, .A | .P, .M | .M, .P => True
  | _, _ => False

instance : DecidableRel E8 := fun a b => by cases a <;> cases b <;> simp [E8] <;> infer_instance

instance (a x : ℕ) : DecidableRel (Pi Δ a x).edge := inferInstanceAs (DecidableRel E5)

/-- The partner map of `E5`, independent of `Δ, a, x`. -/
def partner5 (A : Finset L5) : Finset L5 := Finset.univ.filter fun b => ∀ a ∈ A, E5 a b

theorem edgeMax_Pi_iff {a x : ℕ} (A B : Finset L5) :
    (Pi Δ a x).edgeMax A B ↔ A.Nonempty ∧ B.Nonempty ∧ B = partner5 A ∧ A = partner5 B :=
  edgeMax_iff _ A B

/-- The finite computation behind Lemma 6. -/
theorem partner5_spec : ∀ A : Finset L5,
    (A.Nonempty ∧ (partner5 A).Nonempty ∧ partner5 (partner5 A) = A) ↔ ∃ ℓ, toSet ℓ = A := by
  decide

theorem partner5_toSet : ∀ ℓ ℓ' : L8, partner5 (toSet ℓ) = toSet ℓ' ↔ E8 ℓ ℓ' := by
  decide

/-- Lemma 6 (alphabet): `Σ_{R(Π_Δ(a, x))}` consists of the eight right-closed sets. -/
theorem alphR_Pi (a x : ℕ) : (Pi Δ a x).alphR = Set.range toSet := by
  ext A
  simp only [alphR, Set.mem_ofPred_eq, edgeMax_Pi_iff, Set.mem_range]
  rw [← partner5_spec]
  constructor
  · rintro ⟨B, hA, hB, rfl, h⟩; exact ⟨hA, hB, h.symm⟩
  · rintro ⟨hA, hB, h⟩; exact ⟨_, hA, hB, rfl, h.symm⟩

/-- Lemma 6 (edge constraint): after renaming, the edge constraint of `R(Π_Δ(a, x))` is
`XQ, OB, AU, PM`. -/
theorem edgeMax_toSet (a x : ℕ) (ℓ ℓ' : L8) :
    (Pi Δ a x).R.edge (toSet ℓ) (toSet ℓ') ↔ E8 ℓ ℓ' := by
  change (Pi Δ a x).edgeMax _ _ ↔ _
  rw [edgeMax_Pi_iff]
  have hne : ∀ ℓ : L8, (toSet ℓ).Nonempty := by decide
  have hsymm : ∀ ℓ ℓ' : L8, E8 ℓ ℓ' → E8 ℓ' ℓ := by decide
  constructor
  · rintro ⟨-, -, h, -⟩; exact (partner5_toSet ℓ ℓ').1 h.symm
  · intro h
    exact ⟨hne ℓ, hne ℓ', ((partner5_toSet ℓ ℓ').2 h).symm,
      ((partner5_toSet ℓ' ℓ).2 (hsymm _ _ h)).symm⟩

/-! ### The node constraint -/

/-- `[MUBQ]`, `[PQ]`, `[OUABPQ]`, `[ABPQ]`. -/
def setMUBQ : Finset L8 := {.M, .U, .B, .Q}
/-- `[PQ]`. -/
def setPQ : Finset L8 := {.P, .Q}
/-- `[OUABPQ]`. -/
def setOUABPQ : Finset L8 := {.O, .U, .A, .B, .P, .Q}
/-- `[ABPQ]`. -/
def setABPQ : Finset L8 := {.A, .B, .P, .Q}

/-- The node constraint of `R(Π_Δ(a, x))` (after renaming), as condensed configurations:
`[MUBQ]^{Δ-x} [XMOUABPQ]^x`, `[PQ] [OUABPQ]^{Δ-1}`, `[ABPQ]^a [XMOUABPQ]^{Δ-a}`. -/
def N8 (Δ a x : ℕ) (ℓ : Fin Δ → L8) : Prop :=
  (∃ S : Finset (Fin Δ), S.card = Δ - x ∧ ∀ i ∈ S, ℓ i ∈ setMUBQ) ∨
  (∃ i, ℓ i ∈ setPQ ∧ ∀ j, j ≠ i → ℓ j ∈ setOUABPQ) ∨
  (∃ S : Finset (Fin Δ), S.card = a ∧ ∀ i ∈ S, ℓ i ∈ setABPQ)

theorem mem_toSet_M (ℓ : L8) : L5.M ∈ toSet ℓ ↔ ℓ ∈ setMUBQ := by cases ℓ <;> decide
theorem mem_toSet_P (ℓ : L8) : L5.P ∈ toSet ℓ ↔ ℓ ∈ setPQ := by cases ℓ <;> decide
theorem mem_toSet_O (ℓ : L8) : L5.O ∈ toSet ℓ ↔ ℓ ∈ setOUABPQ := by cases ℓ <;> decide
theorem mem_toSet_A (ℓ : L8) : L5.A ∈ toSet ℓ ↔ ℓ ∈ setABPQ := by cases ℓ <;> decide
theorem mem_toSet_X (ℓ : L8) : L5.X ∈ toSet ℓ := by cases ℓ <;> decide

/-- Lemma 6 (node constraint), for `x, a ≤ Δ` (the paper assumes `x + 2 ≤ a ≤ Δ`). -/
theorem R_Pi_node {a x : ℕ} (hx : x ≤ Δ) (ha : a ≤ Δ) (ℓ : Fin Δ → L8) :
    (fun i => toSet (ℓ i)) ∈ (Pi Δ a x).R.node ↔ N8 Δ a x ℓ := by
  simp only [R, Set.mem_ofPred_eq]
  rw [alphR_Pi]
  simp only [Set.mem_range, exists_apply_eq_apply, implies_true, true_and]
  simp only [Pi, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, hM | hA | hP⟩
    · refine Or.inl ⟨Finset.univ.filter fun i => y i = .M, hM.1, fun i hi => ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [← mem_toSet_M, ← hi]; exact hy i
    · refine Or.inr (Or.inr ⟨Finset.univ.filter fun i => y i = .A, hA.1, fun i hi => ?_⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [← mem_toSet_A, ← hi]; exact hy i
    · obtain ⟨i, hi⟩ : ∃ i, y i = .P := by
        by_contra h
        push Not at h
        have : cnt y .P = 0 := by
          unfold cnt; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun j _ => h j
        omega
      have hall := eq_or_eq_of_cnt_add_cnt (σ := y) (ℓ₁ := L5.P) (ℓ₂ := L5.O) (by decide)
        (by have : 0 < Δ := Fin.pos i; omega)
      refine Or.inr (Or.inl ⟨i, ?_, fun j hj => ?_⟩)
      · rw [← mem_toSet_P, ← hi]; exact hy i
      · rcases hall j with h | h
        · exfalso
          have : 2 ≤ cnt y .P := by
            unfold cnt
            have : ({i, j} : Finset (Fin Δ)) ⊆ Finset.univ.filter fun k => y k = .P := by
              intro k hk
              simp only [Finset.mem_insert, Finset.mem_singleton] at hk
              rcases hk with rfl | rfl <;> simp [hi, h]
            exact (Finset.card_le_card this).trans' (by rw [Finset.card_pair (Ne.symm hj)])
          omega
        · rw [← mem_toSet_O, ← h]; exact hy j
  · rintro (⟨S, hS, hSM⟩ | ⟨i, hi, hj⟩ | ⟨S, hS, hSA⟩)
    · refine ⟨fun i => if i ∈ S then .M else .X, fun i => ?_, Or.inl ?_⟩
      · by_cases hi : i ∈ S
        · simp only [hi, ite_true]; exact (mem_toSet_M _).2 (hSM i hi)
        · simp only [hi, ite_false]; exact mem_toSet_X _
      · have := cnt_ite S (ℓ₁ := L5.M) (ℓ₂ := L5.X) (by decide)
        omega
    · refine ⟨Function.update (fun _ => .O) i .P, fun j => ?_, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
      · by_cases h : j = i
        · subst h; simpa using (mem_toSet_P _).2 hi
        · simpa [Function.update_of_ne h] using (mem_toSet_O _).2 (hj j h)
      · unfold cnt
        rw [Finset.card_eq_one]
        exact ⟨i, by ext j; by_cases h : j = i <;> simp [h, Function.update_of_ne]⟩
      · unfold cnt
        have : (Finset.univ.filter fun j => Function.update (fun _ => L5.O) i L5.P j = L5.O) =
            Finset.univ.erase i := by
          ext j; by_cases h : j = i <;> simp [h, Function.update_of_ne]
        rw [this, Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    · refine ⟨fun i => if i ∈ S then .A else .X, fun i => ?_, Or.inr (Or.inl ?_)⟩
      · by_cases hi : i ∈ S
        · simp only [hi, ite_true]; exact (mem_toSet_A _).2 (hSA i hi)
        · simp only [hi, ite_false]; exact mem_toSet_X _
      · have := cnt_ite S (ℓ₁ := L5.A) (ℓ₂ := L5.X) (by decide)
        omega

end Podc.MISTreeLowerBounds
