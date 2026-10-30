import Papers.PODC2020.MISInapproxCongest.Linear

/-!
# Section 5: the family `F_x̄` for the quadratic lower bound

Two copies `G¹, G²` (`b = false, true`) of the construction `G` of Section 4. Nodes are
`Node2 t K P A = Fin t × Bool × (K ⊕ P × A)`. Inside each copy the edges are those of `G`; between
the copies the only edges are the input edges `v^{(i,1)}_{m₁} — v^{(i,2)}_{m₂}` for
`x^i_{(m₁,m₂)} = 0`. All `A`-nodes have weight `W` (the paper's `ℓ`), code nodes weight `1`.
The strings are indexed by `K × K` (the paper's `[k] × [k]`).

Main results: Claim 6 (`claim6_generic`, `claim6`), Claim 7 (`claim7_generic`, `claim7`) and
Lemma 3 (`lemma3`).
-/

set_option linter.unusedSectionVars false

namespace Podc.MISInapproxCongest

open Finset Cslib Cslib.CommunicationComplexity

/-- Nodes of `F`: player `i`, copy `b` (`false` = `G¹`, `true` = `G²`), node of `H`. -/
abbrev Node2 (t : ℕ) (K P A : Type*) := Fin t × Bool × (K ⊕ P × A)

section Graph

variable {t : ℕ} {K P A : Type*} [DecidableEq K] [DecidableEq P] [DecidableEq A]

/-- The input edges between `A^{(i,1)}` and `A^{(i,2)}` (seen from copy `b`). -/
def crossEdge (x : Fin t → K × K → Bool) (i : Fin t) : Bool → K ⊕ P × A → K ⊕ P × A → Prop
  | false, .inl m, .inl m' => x i (m, m') = false
  | true, .inl m, .inl m' => x i (m', m) = false
  | _, _, _ => False

instance (x : Fin t → K × K → Bool) (i : Fin t) (b : Bool) (u v : K ⊕ P × A) :
    Decidable (crossEdge x i b u v) :=
  match b, u, v with
  | false, .inl m, .inl m' => inferInstanceAs (Decidable (x i (m, m') = false))
  | true, .inl m, .inl m' => inferInstanceAs (Decidable (x i (m', m) = false))
  | false, .inl _, .inr _ => isFalse id
  | false, .inr _, _ => isFalse id
  | true, .inl _, .inr _ => isFalse id
  | true, .inr _, _ => isFalse id

/-- Adjacency of `F_x̄`. -/
def fAdj (c : K → P → A) (x : Fin t → K × K → Bool) (u v : Node2 t K P A) : Prop :=
  (u.2.1 = v.2.1 ∧ (graph c).Adj (u.1, u.2.2) (v.1, v.2.2)) ∨
    (u.2.1 ≠ v.2.1 ∧ u.1 = v.1 ∧ crossEdge x u.1 u.2.1 u.2.2 v.2.2)

/-- The graph `F_x̄` of Section 5.1. -/
def graph2 (c : K → P → A) (x : Fin t → K × K → Bool) : SimpleGraph (Node2 t K P A) where
  Adj := fAdj c x
  symm := ⟨by
    rintro ⟨i, b, u⟩ ⟨j, b', v⟩ (⟨hb, h⟩ | ⟨hb, hij, h⟩)
    · exact Or.inl ⟨hb.symm, h.symm⟩
    · refine Or.inr ⟨Ne.symm hb, hij.symm, ?_⟩
      simp only at hb hij h ⊢
      subst hij
      rcases b <;> rcases b' <;> simp at hb <;> rcases u with m | _ <;> rcases v with m' | _ <;>
        simp_all [crossEdge]⟩
  loopless := ⟨by
    rintro ⟨i, b, u⟩ (⟨-, h⟩ | ⟨h, -⟩)
    · exact (graph c).loopless.irrefl _ h
    · exact h rfl⟩

instance (c : K → P → A) (x : Fin t → K × K → Bool) : DecidableRel (graph2 c x).Adj :=
  fun u v => by unfold graph2 fAdj; infer_instance

/-- Node weights of `F`: `W` on the cliques `A^{(i,b)}`, `1` on the code gadgets. -/
def weight2 (W : ℕ) : Node2 t K P A → ℕ
  | ⟨_, _, .inl _⟩ => W
  | ⟨_, _, .inr _⟩ => 1

/-- The part of `I` in copy `b`, as a set of nodes of `G`. -/
def res [Fintype K] [Fintype P] [Fintype A] (I : Finset (Node2 t K P A)) (b : Bool) : Finset (Node t K P A) :=
  univ.filter fun v => (v.1, b, v.2) ∈ I

/-- Lift a set of nodes of `G` into copy `b`. -/
def lift (J : Finset (Node t K P A)) (b : Bool) : Finset (Node2 t K P A) :=
  J.map ⟨fun v => (v.1, b, v.2), fun v w h => by
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.2⟩

theorem mem_lift {J : Finset (Node t K P A)} {b : Bool} {v : Node2 t K P A} :
    v ∈ lift J b ↔ v.2.1 = b ∧ (v.1, v.2.2) ∈ J := by
  rcases v with ⟨i, b', u⟩
  simp only [lift, Finset.mem_map]
  constructor
  · rintro ⟨⟨i', u'⟩, h, he⟩
    obtain ⟨rfl, rfl, rfl⟩ : i' = i ∧ b = b' ∧ u' = u := by
      change (i', b, u') = (i, b', u) at he
      simpa using he
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨_, h, rfl⟩

theorem mem_lift_union (J J' : Finset (Node t K P A)) (v : Node2 t K P A) :
    v ∈ lift J false ∪ lift J' true ↔ (v.1, v.2.2) ∈ (if v.2.1 then J' else J) := by
  rcases v with ⟨i, b, u⟩
  cases b <;> simp [mem_lift]

variable [Fintype K] [Fintype P] [Fintype A] {c : K → P → A} {x : Fin t → K × K → Bool}

theorem res_indep {I : Finset (Node2 t K P A)} (hI : IsIndep (graph2 c x) I) (b : Bool) :
    IsIndep (graph c) (res I b) := fun u hu v hv h =>
  hI _ (mem_filter.1 hu).2 _ (mem_filter.1 hv).2 (Or.inl ⟨rfl, by simpa using h⟩)

/-- The weight of a set of nodes of `F` is the sum of the weights of its two copies (with all
`A`-nodes heavy). -/
theorem wsum2_eq (W : ℕ) (I : Finset (Node2 t K P A)) :
    wsum (weight2 W) I = ∑ b, wsum (weight W (fun _ _ => true)) (res I b) := by
  unfold wsum
  rw [← sum_fiberwise I (fun v => v.2.1)]
  refine sum_congr rfl fun b _ => ?_
  refine sum_nbij' (fun v => (v.1, v.2.2)) (fun u => (u.1, b, u.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, b', u⟩ hv
    simp only [mem_filter] at hv
    obtain ⟨hv, rfl⟩ := hv
    simpa [res] using hv
  · rintro ⟨i, u⟩ hu
    simpa [res] using hu
  · rintro ⟨i, b', u⟩ hv
    simp only [mem_filter] at hv
    obtain ⟨-, rfl⟩ := hv
    rfl
  · intro u _; rfl
  · rintro ⟨i, b', u | u⟩ _ <;> simp [weight2, weight]

end Graph

section Claims

variable {t : ℕ} {K P A : Type*} [DecidableEq K] [DecidableEq P] [DecidableEq A] [Fintype K]
  [Fintype P] [Fintype A] {c : K → P → A} {x : Fin t → K × K → Bool} {W : ℕ}

theorem res_lift_union (J J' : Finset (Node t K P A)) :
    res (lift J false ∪ lift J' true) false = J ∧ res (lift J false ∪ lift J' true) true = J' := by
  constructor <;> ext ⟨i, u⟩ <;> simp [res, mem_lift]

/-- **Claim 6** (generic). If `x^1_{(m₁,m₂)} = ⋯ = x^t_{(m₁,m₂)} = 1`, the set
`⋃_i {v^{(i,1)}_{m₁}} ∪ Code^{(i,1)}_{m₁} ∪ {v^{(i,2)}_{m₂}} ∪ Code^{(i,2)}_{m₂}` is independent in
`F_x̄` and weighs `2t (W + M)`. -/
theorem claim6_generic {m₁ m₂ : K} (hm : ∀ i, x i (m₁, m₂) = true) :
    IsIndep (graph2 c x) (lift (commonSet (t := t) c m₁) false ∪ lift (commonSet c m₂) true) ∧
      wsum (weight2 W) (lift (commonSet (t := t) c m₁) false ∪ lift (commonSet c m₂) true) =
        2 * (t * (W + Fintype.card P)) := by
  constructor
  · rintro ⟨i, b, u⟩ hu ⟨j, b', v⟩ hv (⟨hb, h⟩ | ⟨hb, hij, h⟩)
    · simp only at hb; subst hb
      rw [mem_lift_union] at hu hv
      cases b
      · exact property1 c m₁ _ hu _ hv h
      · exact property1 c m₂ _ hu _ hv h
    · simp only at hb hij h
      subst hij
      rw [mem_lift_union] at hu hv
      rcases b <;> rcases b' <;> simp at hb <;> rcases u with m | _ <;> rcases v with m' | _ <;>
        simp only [crossEdge] at h <;> (try (obtain rfl := (inl_mem_commonSet _ _ _).1 hu; obtain rfl := (inl_mem_commonSet _ _ _).1 hv)) <;>
        simp_all
  · rw [wsum2_eq, Fintype.sum_bool, (res_lift_union _ _).1, (res_lift_union _ _).2,
      (claim3_generic (W := W) (x := fun _ _ => true) (fun _ => rfl)).2,
      (claim3_generic (W := W) (x := fun _ _ => true) (fun _ => rfl)).2]
    ring


/-- The weight of an independent set of `F`, copy by copy and player by player. -/
theorem wsum2_eq' (I : Finset (Node2 t K P A)) :
    wsum (weight2 W) I = ∑ i, ((W * (aPart (res I false) i).card + (cPart (res I false) i).card) +
      (W * (aPart (res I true) i).card + (cPart (res I true) i).card)) := by
  rw [wsum2_eq, Fintype.sum_bool, wsum_eq, wsum_eq, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp only [weight, ite_true, sum_const, smul_eq_mul]
  ring

/-- **Claim 7** (generic). If the strings `x^1, …, x^t` are pairwise disjoint, every independent
set of `F_x̄` weighs at most `(t - p)(W + 2M) + 2pW + (p + 1) M + 2a (p choose 2)` for some
`p ≤ t` (the number of players `i` such that `I` meets both `A^{(i,1)}` and `A^{(i,2)}`). -/
theorem claim7_generic {a : ℕ} (hc : ∀ m m', m ≠ m' → agree (c m) (c m') ≤ a)
    (hx : PairwiseDisjoint x) {I : Finset (Node2 t K P A)} (hI : IsIndep (graph2 c x) I) :
    ∃ p ≤ t, wsum (weight2 W) I ≤ (t - p) * (W + 2 * Fintype.card P) + 2 * p * W +
      (p + 1) * Fintype.card P + 2 * a * p.choose 2 := by
  classical
  rw [wsum2_eq']
  set M := Fintype.card P
  set I0 := res I false
  set I1 := res I true
  have hI0 : IsIndep (graph c) I0 := res_indep hI false
  have hI1 : IsIndep (graph c) I1 := res_indep hI true
  set Hs := univ.filter fun i => (aPart I0 i).Nonempty ∧ (aPart I1 i).Nonempty with hHs
  refine ⟨Hs.card, card_le_univ _ |>.trans (by simp), ?_⟩
  rw [← sum_filter_add_sum_filter_not univ (· ∈ Hs)]
  have hfilt : univ.filter (· ∈ Hs) = Hs := by ext; simp
  rw [hfilt]
  -- light players
  have hlight : ∑ i ∈ univ.filter (· ∉ Hs), ((W * (aPart I0 i).card + (cPart I0 i).card) +
      (W * (aPart I1 i).card + (cPart I1 i).card)) ≤ (t - Hs.card) * (W + 2 * M) := by
    calc _ ≤ ∑ _i ∈ univ.filter (· ∉ Hs), (W + 2 * M) := by
          refine sum_le_sum fun i hi => ?_
          have hi' : i ∉ Hs := (mem_filter.1 hi).2
          have hA : (aPart I0 i).card + (aPart I1 i).card ≤ 1 := by
            have h0 := card_aPart_le_one hI0 i
            have h1 := card_aPart_le_one hI1 i
            by_cases e0 : (aPart I0 i).Nonempty
            · have : ¬(aPart I1 i).Nonempty := fun e1 => hi' (by simp [hHs, e0, e1])
              rw [not_nonempty_iff_eq_empty.1 this, card_empty]; omega
            · rw [not_nonempty_iff_eq_empty.1 e0, card_empty]; omega
          have := card_cPart_le hI0 i
          have := card_cPart_le hI1 i
          nlinarith
      _ = (t - Hs.card) * (W + 2 * M) := by
          rw [sum_const, smul_eq_mul, card_filter_not_mem_univ_eq Hs]
  rcases Nat.eq_zero_or_pos Hs.card with h0 | hpos
  · rw [card_eq_zero.1 h0] at hlight ⊢
    simp only [sum_empty, zero_add, card_empty] at hlight ⊢
    omega
  obtain ⟨i₀, hi₀⟩ := card_pos.1 hpos
  have hex : ∀ i ∈ Hs, ∃ m₁ m₂, m₁ ∈ aPart I0 i ∧ m₂ ∈ aPart I1 i := fun i hi => by
    simp only [hHs, mem_filter, mem_univ, true_and] at hi
    exact ⟨_, _, hi.1.choose_spec, hi.2.choose_spec⟩
  obtain ⟨m₀, -, -, -⟩ := hex i₀ hi₀
  have : Nonempty K := ⟨m₀⟩
  choose! m1 m2 hm using hex
  have hmem0 : ∀ i ∈ Hs, (i, .inl (m1 i)) ∈ I0 := fun i hi => (mem_filter.1 (hm i hi).1).2
  have hmem1 : ∀ i ∈ Hs, (i, .inl (m2 i)) ∈ I1 := fun i hi => (mem_filter.1 (hm i hi).2).2
  have hxt : ∀ i ∈ Hs, x i (m1 i, m2 i) = true := fun i hi => by
    by_contra hf
    refine hI _ (mem_filter.1 (hmem0 i hi)).2 _ (mem_filter.1 (hmem1 i hi)).2 (Or.inr ⟨?_, rfl, ?_⟩)
    · simp
    · simpa [crossEdge] using hf
  have hpair : ∀ i ∈ Hs, ∀ j ∈ Hs, m1 i = m1 j → m2 i = m2 j → i = j := by
    intro i hi j hj e1 e2
    by_contra hne
    have := hx i j hne _ (hxt i hi)
    rw [e1, e2, hxt j hj] at this
    exact Bool.noConfusion this
  -- copy 1
  set R := Hs.filter fun i => ∀ j ∈ Hs, m1 j = m1 i → i ≤ j with hR
  have hRinj : Set.InjOn m1 R := by
    intro i hi j hj e
    have hi' := (mem_filter.1 hi).2 j (mem_filter.1 hj).1 e.symm
    have hj' := (mem_filter.1 hj).2 i (mem_filter.1 hi).1 e
    exact le_antisymm hi' hj'
  have hcopy1 : ∑ i ∈ Hs, (cPart I0 i).card ≤
      (M + a * R.card.choose 2) + (Hs.card - R.card) * M := by
    rw [← sum_filter_add_sum_filter_not Hs fun i => ∀ j ∈ Hs, m1 j = m1 i → i ≤ j]
    refine add_le_add (card_code_le hc hI0 R m1 hRinj fun i hi => hmem0 i (mem_filter.1 hi).1) ?_
    calc _ ≤ ∑ _i ∈ Hs.filter (fun i => ¬∀ j ∈ Hs, m1 j = m1 i → i ≤ j), M :=
          sum_le_sum fun i _ => card_cPart_le hI0 i
      _ = (Hs.card - R.card) * M := by
          rw [sum_const, smul_eq_mul]
          have := card_filter_add_card_filter_not (s := Hs) (fun i => ∀ j ∈ Hs, m1 j = m1 i → i ≤ j)
          rw [← hR] at this
          congr 1; omega
  -- copy 2, class by class
  have himage : (Hs.image m1).card ≤ R.card := by
    refine le_trans (card_le_card (t := R.image m1) fun μ hμ => ?_) card_image_le
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hμ
    have hne : (Hs.filter fun j => m1 j = m1 i).Nonempty := ⟨i, mem_filter.2 ⟨hi, rfl⟩⟩
    set j := (Hs.filter fun j => m1 j = m1 i).min' hne
    have hj := mem_filter.1 ((Hs.filter fun j => m1 j = m1 i).min'_mem hne)
    refine mem_image.2 ⟨j, mem_filter.2 ⟨hj.1, fun j' hj' e => ?_⟩, hj.2⟩
    exact (Hs.filter fun j => m1 j = m1 i).min'_le _ (mem_filter.2 ⟨hj', e.trans hj.2⟩)
  have hcopy2 : ∑ i ∈ Hs, (cPart I1 i).card ≤ (Hs.image m1).card * M + a * Hs.card.choose 2 := by
    rw [← sum_fiberwise_of_maps_to (g := m1) (t := Hs.image m1) fun i hi => mem_image_of_mem m1 hi]
    have hfib : ∀ μ ∈ Hs.image m1, ∑ i ∈ Hs.filter (fun i => m1 i = μ), (cPart I1 i).card ≤
        M + a * (Hs.filter fun i => m1 i = μ).card.choose 2 := by
      intro μ _
      refine card_code_le hc hI1 _ m2 ?_ fun i hi => hmem1 i (mem_filter.1 hi).1
      intro i hi j hj e
      exact hpair i (mem_filter.1 hi).1 j (mem_filter.1 hj).1
        ((mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm) e
    refine (sum_le_sum hfib).trans ?_
    rw [sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum]
    refine add_le_add le_rfl (Nat.mul_le_mul_left _ ?_)
    -- `∑ (q_μ choose 2) ≤ (p choose 2)`
    have h2 : 2 * ∑ μ ∈ Hs.image m1, (Hs.filter fun i => m1 i = μ).card.choose 2 ≤
        2 * Hs.card.choose 2 := by
      rw [mul_sum, two_mul_choose_two]
      calc ∑ μ ∈ Hs.image m1, 2 * (Hs.filter fun i => m1 i = μ).card.choose 2
          ≤ ∑ μ ∈ Hs.image m1, (Hs.filter fun i => m1 i = μ).card * (Hs.card - 1) := by
            refine sum_le_sum fun μ _ => ?_
            rw [two_mul_choose_two]
            exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (card_le_card (filter_subset _ _)) 1)
        _ = Hs.card * (Hs.card - 1) := by
            rw [← sum_mul, ← card_eq_sum_card_fiberwise fun i hi => mem_image_of_mem m1 hi]
    omega
  have hRle : R.card ≤ Hs.card := card_le_card (filter_subset _ _)
  have hch : a * R.card.choose 2 ≤ a * Hs.card.choose 2 :=
    Nat.mul_le_mul_left _ (Nat.choose_le_choose 2 hRle)
  have hheavy : ∑ i ∈ Hs, ((W * (aPart I0 i).card + (cPart I0 i).card) +
      (W * (aPart I1 i).card + (cPart I1 i).card)) ≤
        2 * Hs.card * W + ∑ i ∈ Hs, (cPart I0 i).card + ∑ i ∈ Hs, (cPart I1 i).card := by
    have e : ∀ i, (W * (aPart I0 i).card + (cPart I0 i).card) +
        (W * (aPart I1 i).card + (cPart I1 i).card) =
          (W * (aPart I0 i).card + W * (aPart I1 i).card) + (cPart I0 i).card +
            (cPart I1 i).card := fun i => by ring
    simp only [e, sum_add_distrib]
    rw [← sum_add_distrib]
    refine add_le_add (add_le_add ?_ le_rfl) le_rfl
    calc ∑ i ∈ Hs, (W * (aPart I0 i).card + W * (aPart I1 i).card) ≤ ∑ _i ∈ Hs, 2 * W :=
          sum_le_sum fun i _ => by
            have := card_aPart_le_one hI0 i; have := card_aPart_le_one hI1 i; nlinarith
      _ = 2 * Hs.card * W := by rw [sum_const, smul_eq_mul]; ring
  have hsplit : (Hs.card - R.card) * M + (Hs.image m1).card * M ≤ Hs.card * M := by
    rw [← add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  nlinarith

end Claims

/-! ### The paper's statements -/

section Paper

variable {t : ℕ} {K P A : Type*} [DecidableEq K] [DecidableEq P] [DecidableEq A] [Fintype K]
  [Fintype P] [Fintype A] {c : K → P → A} {ℓ α : ℕ} {x : Fin t → K × K → Bool}

/-- **Claim 6.** If `x^1_{(m₁,m₂)} = ⋯ = x^t_{(m₁,m₂)} = 1` for some pair, `F_x̄` contains an
independent set of weight at least `4tℓ + 2αt`. -/
theorem claim6 (hP : Fintype.card P = ℓ + α) (hx : CommonElement x) :
    ∃ I, IsIndep (graph2 c x) I ∧ 4 * t * ℓ + 2 * α * t ≤ wsum (weight2 ℓ) I := by
  obtain ⟨⟨m₁, m₂⟩, hm⟩ := hx
  obtain ⟨h1, h2⟩ := claim6_generic (c := c) (W := ℓ) hm
  exact ⟨_, h1, by rw [h2, hP]; ring_nf; rfl⟩

/-- **Claim 7.** If the strings `x^1, …, x^t` are pairwise disjoint, every independent set of
`F_x̄` has weight at most `3(t + 1)ℓ + 3αt³` (for `t ≥ 1`). -/
theorem claim7 (hP : Fintype.card P = ℓ + α) (hc : ∀ m m', m ≠ m' → agree (c m) (c m') ≤ α)
    (ht : 1 ≤ t) (hx : PairwiseDisjoint x) {I : Finset (Node2 t K P A)}
    (hI : IsIndep (graph2 c x) I) :
    wsum (weight2 ℓ) I ≤ 3 * (t + 1) * ℓ + 3 * α * t ^ 3 := by
  obtain ⟨p, hp, h⟩ := claim7_generic (W := ℓ) hc hx hI
  rw [hP] at h
  refine h.trans ?_
  have hC := two_mul_choose_two p
  set C := p.choose 2
  obtain ⟨d, rfl⟩ : ∃ d, t = p + d := ⟨t - p, by omega⟩
  rw [show p + d - p = d by omega]
  rcases p with _ | p
  · simp at hC; rw [hC]
    have : d ≤ d ^ 3 := Nat.le_self_pow (by norm_num) d
    have : α * d ≤ α * d ^ 3 := Nat.mul_le_mul_left _ this
    nlinarith
  · simp only [Nat.add_sub_cancel] at hC
    have h1 : 2 * α * C = α * ((p + 1) * p) := by rw [mul_comm 2 α, mul_assoc, hC]
    have h : (p + 1 + d) ^ 2 ≤ (p + 1 + d) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h4 : (p + 1) * p + 2 * d + p + 2 ≤ 3 * (p + 1 + d) ^ 3 := by nlinarith
    have h5 := Nat.mul_le_mul_left α h4
    nlinarith

end Paper

/-- Arithmetic of **Lemma 3**: with `t := ⌈3/(2ε)⌉₊ + 3` players and `3 α t² ≤ 2 ε ℓ`,
`3(t + 1)ℓ + 3αt³ ≤ (3/4 + ε)(4tℓ + 2αt)`. -/
theorem lemma3_gap {ε : ℝ} (hε : 0 < ε) (ℓ α : ℕ)
    (hα : 3 * (α : ℝ) * (⌈3 / (2 * ε)⌉₊ + 3) ^ 2 ≤ 2 * ε * ℓ) :
    ((3 * (⌈3 / (2 * ε)⌉₊ + 3 + 1) * ℓ + 3 * α * (⌈3 / (2 * ε)⌉₊ + 3) ^ 3 : ℕ) : ℝ) ≤
      (3 / 4 + ε) * ((4 * (⌈3 / (2 * ε)⌉₊ + 3) * ℓ + 2 * α * (⌈3 / (2 * ε)⌉₊ + 3) : ℕ) : ℝ) := by
  push_cast at hα ⊢
  set T : ℝ := ⌈3 / (2 * ε)⌉₊ + 3
  have hT : 3 ≤ 2 * ε * T := by
    have : 3 / (2 * ε) ≤ ⌈3 / (2 * ε)⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ (by positivity)] at this
    simp only [T]; nlinarith
  have hℓ : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have hα0 : (0 : ℝ) ≤ α := Nat.cast_nonneg α
  have hT0 : (0 : ℝ) ≤ T := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hα hT0, mul_le_mul_of_nonneg_right hT hℓ]

/-- **Lemma 3.** For every `ε > 0` there is `t > 2` (namely `⌈3/(2ε)⌉ + 3`) such that `F_x̄` is a
`(3/4 + ε)`-approximate MaxIS family: if all strings share an index, some independent set weighs
`≥ β := 4tℓ + 2αt`; if they are pairwise disjoint, every independent set weighs `≤ (3/4 + ε) β`
(provided `3 α t² ≤ 2 ε ℓ`, true for the paper's parameters and large `k`). -/
theorem lemma3 {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ, 2 < t ∧ ∀ {K P A : Type*} [DecidableEq K] [DecidableEq P] [DecidableEq A]
      [Fintype K] [Fintype P] [Fintype A] {c : K → P → A} {ℓ α : ℕ},
      Fintype.card P = ℓ + α → (∀ m m', m ≠ m' → agree (c m) (c m') ≤ α) →
      3 * (α : ℝ) * t ^ 2 ≤ 2 * ε * ℓ → ∀ x : Fin t → K × K → Bool,
      (CommonElement x →
        ∃ I, IsIndep (graph2 c x) I ∧ 4 * t * ℓ + 2 * α * t ≤ wsum (weight2 ℓ) I) ∧
      (PairwiseDisjoint x → ∀ I, IsIndep (graph2 c x) I →
        (wsum (weight2 ℓ) I : ℝ) ≤ (3 / 4 + ε) * ((4 * t * ℓ + 2 * α * t : ℕ) : ℝ)) := by
  refine ⟨⌈3 / (2 * ε)⌉₊ + 3, by omega, ?_⟩
  intro K P A _ _ _ _ _ _ c ℓ α hP hc hαℓ x
  refine ⟨fun hx => claim6 hP hx, fun hx I hI => ?_⟩
  refine le_trans ?_ (lemma3_gap hε ℓ α (by exact_mod_cast hαℓ))
  exact_mod_cast claim7 hP hc (by omega) hx hI

end Podc.MISInapproxCongest
