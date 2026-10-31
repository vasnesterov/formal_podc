import Papers.PODC2012.EquivocationPrice.Equivalence

/-!
# Theorem 1: the reduction from balanced bipartite independent set

**Theorem 1** of [JMS12]: deciding whether a 3-uniform hypergraph is `h`-disjoint (equivalently,
by Theorem 2, whether Byzantine agreement is possible) is co-NP-complete. Membership in co-NP is
immediate (a violating colouring is a certificate). Hardness is by a reduction from balanced
bipartite independent set (BBIS), NP-complete by Alon, Duke, Lefmann, Rödl, Yuster.

We verify the combinatorial core: the correctness of the reduction (`theorem_1_reduction`).
Given a bipartite graph `G` between `X` and `Y` and `t ≥ 1`, the hypergraph `redE G` on
`X ⊕ Y ⊕ Z` with `|Z| = |X| + |Y| − t` has the hyperedges (Section 6)
* all triples inside `Z`; `(u, v, w)` for `u, v ∈ Z`, `w ∈ X ∪ Y`;
* `(u, v, w)` for `u, v ∈ X`, `w ∈ Z`, and for `u, v ∈ Y`, `w ∈ Z`;
* `(u, v, w)` for every edge `(u, v)` of `G` and `w ∈ Z`;
and `G` has an independent pair `A ⊆ X`, `B ⊆ Y` with `|A| = |B| = t` iff `redE G` is not
`t`-disjoint. The paper assumes `|X| = |Y|`; the reduction is correct for `t ≤ |X|, |Y|`.
The size of `redE G` is polynomial; the complexity-theoretic wrapper (NP-completeness of BBIS,
polynomial-time computability) is not formalized.

Through Theorem 2 the same instance decides `f`-tolerance with `n' = 2f + h`, `f = |X| + |Y| − t`,
`h = t ∈ [1..f]`, as the paper's statement of Theorem 1 in the introduction requires
(`theorem_1_reduction_fTolerant`).
-/

namespace Podc.EquivocationPrice

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

/-- Vertices of the reduction hypergraph: `X ⊕ Y ⊕ Z`. -/
abbrev RV (X Y Z : Type*) := X ⊕ Y ⊕ Z

/-- The vertex is in `X`. -/
def isX : RV X Y Z → Bool
  | .inl _ => true
  | _ => false

/-- The vertex is in `Y`. -/
def isY : RV X Y Z → Bool
  | .inr (.inl _) => true
  | _ => false

/-- The vertex is in `Z`. -/
def isZ : RV X Y Z → Bool
  | .inr (.inr _) => true
  | _ => false

/-- The ordered triples `(u, v, w)` added as hyperedges in the paper's construction. -/
def Allowed (G : X → Y → Prop) (u v w : RV X Y Z) : Prop :=
  (isZ u ∧ isZ v ∧ isZ w) ∨ (isZ u ∧ isZ v ∧ ¬ isZ w) ∨ (isX u ∧ isX v ∧ isZ w) ∨
    (isY u ∧ isY v ∧ isZ w) ∨ (∃ x y, u = .inl x ∧ v = .inr (.inl y) ∧ G x y ∧ isZ w)

open Classical in
/-- The hypergraph of the reduction (Section 6 of [JMS12]). -/
noncomputable def redE (G : X → Y → Prop) : Finset (Finset (RV X Y Z)) :=
  ((Finset.univ : Finset (RV X Y Z × RV X Y Z × RV X Y Z)).filter fun p =>
    p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 ∧ Allowed G p.1 p.2.1 p.2.2).image
    fun p => ({p.1, p.2.1, p.2.2} : Finset (RV X Y Z))

/-- Balanced bipartite independent set: `t`-subsets `A ⊆ X`, `B ⊆ Y` with no edge between. -/
def BBIS (G : X → Y → Prop) (t : ℕ) : Prop :=
  ∃ A : Finset X, ∃ B : Finset Y, A.card = t ∧ B.card = t ∧ ∀ x ∈ A, ∀ y ∈ B, ¬ G x y

theorem redE_uniform (G : X → Y → Prop) : Uniform3 (redE (Z := Z) G) := by
  intro e he
  simp only [redE, Finset.mem_image, Finset.mem_filter] at he
  obtain ⟨⟨u, v, w⟩, ⟨-, huv, huw, hvw, -⟩, rfl⟩ := he
  rw [Finset.card_insert_of_notMem (by simp [huv, huw]),
    Finset.card_insert_of_notMem (by simp [hvw]), Finset.card_singleton]

theorem mem_redE {G : X → Y → Prop} {u v w : RV X Y Z} (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) (h : Allowed G u v w) : ({u, v, w} : Finset (RV X Y Z)) ∈ redE G := by
  simp only [redE, Finset.mem_image, Finset.mem_filter]
  exact ⟨⟨u, v, w⟩, ⟨Finset.mem_univ _, huv, huw, hvw, h⟩, rfl⟩

/-- The only missing triples with one vertex in each of `X`, `Y`, `Z` are the non-edges of `G`. -/
theorem not_mem_redE {G : X → Y → Prop} {x : X} {y : Y} {z : Z} (hG : ¬ G x y) :
    ({.inl x, .inr (.inl y), .inr (.inr z)} : Finset (RV X Y Z)) ∉ redE G := by
  simp only [redE, Finset.mem_image, Finset.mem_filter, not_exists, not_and]
  rintro ⟨u, v, w⟩ ⟨-, huv, huw, hvw, hA⟩ he
  have mu : u ∈ ({u, v, w} : Finset (RV X Y Z)) := by simp
  have mv : v ∈ ({u, v, w} : Finset (RV X Y Z)) := by simp
  have mw : w ∈ ({u, v, w} : Finset (RV X Y Z)) := by simp
  simp only at he mu mv mw
  rw [he] at mu mv mw
  simp only [Finset.mem_insert, Finset.mem_singleton] at mu mv mw
  simp only [Allowed] at hA
  rcases mu with rfl | rfl | rfl <;> rcases mv with rfl | rfl | rfl <;>
    rcases mw with rfl | rfl | rfl <;> simp_all [isX, isY, isZ]

omit [Fintype Y] [Fintype Z] in
/-- Pull back a set of vertices lying in `X`. -/
theorem card_le_of_subset_X {A : Finset (RV X Y Z)} (hA : ∀ a ∈ A, isX a) :
    A.card ≤ (Finset.univ.filter fun x : X => (.inl x : RV X Y Z) ∈ A).card := by
  calc A.card ≤ ((Finset.univ.filter fun x : X => (.inl x : RV X Y Z) ∈ A).map
        Function.Embedding.inl).card := by
        apply Finset.card_le_card
        intro a ha
        have := hA a ha
        match a, ha, this with
        | .inl x, ha, _ => simp [ha]
    _ = _ := Finset.card_map _

omit [Fintype X] [Fintype Z] in
/-- Pull back a set of vertices lying in `Y`. -/
theorem card_le_of_subset_Y {A : Finset (RV X Y Z)} (hA : ∀ a ∈ A, isY a) :
    A.card ≤ (Finset.univ.filter fun y : Y => (.inr (.inl y) : RV X Y Z) ∈ A).card := by
  calc A.card ≤ ((Finset.univ.filter fun y : Y => (.inr (.inl y) : RV X Y Z) ∈ A).map
        (Function.Embedding.inl.trans Function.Embedding.inr)).card := by
        apply Finset.card_le_card
        intro a ha
        have := hA a ha
        match a, ha, this with
        | .inr (.inl y), ha, _ => simp [ha]
    _ = _ := Finset.card_map _

/-- The core of the reverse direction: if the `Z`-vertices of a violating colouring all lie in
`C`, then `A` and `B` give an independent pair. -/
theorem bbis_of_violation {G : X → Y → Prop} {t : ℕ} (ht : 1 ≤ t) {A B C : Finset (RV X Y Z)}
    (hv : ValidColoring t A B C) (hR : ¬ Rainbow (redE G) A B C)
    (hzC : ∃ z ∈ C, isZ z) (hzA : ∀ a ∈ A, ¬ isZ a) (hzB : ∀ b ∈ B, ¬ isZ b) : BBIS G t := by
  obtain ⟨hAB, hAC, hBC, ha, hb, hc, -⟩ := hv
  obtain ⟨z, hz, hzz⟩ := hzC
  have nAB := Finset.disjoint_left.1 hAB
  -- `X` (resp. `Y`) does not meet both `A` and `B`
  have hXX : ∀ a ∈ A, ∀ b ∈ B, isX a → ¬ isX b := by
    intro a ha b hb hxa hxb
    refine hR ⟨a, ha, b, hb, z, hz, mem_redE (fun h => nAB ha (h ▸ hb)) ?_ ?_ ?_⟩
    · rintro rfl; exact hzA a ha hzz
    · rintro rfl; exact hzB b hb hzz
    · simp [Allowed, hxa, hxb, hzz]
  have hYY : ∀ a ∈ A, ∀ b ∈ B, isY a → ¬ isY b := by
    intro a ha b hb hya hyb
    refine hR ⟨a, ha, b, hb, z, hz, mem_redE (fun h => nAB ha (h ▸ hb)) ?_ ?_ ?_⟩
    · rintro rfl; exact hzA a ha hzz
    · rintro rfl; exact hzB b hb hzz
    · simp [Allowed, hya, hyb, hzz]
  -- every vertex outside `Z` is in `X` or in `Y`
  have hxy : ∀ v : RV X Y Z, ¬ isZ v → (isX v ∨ isY v) := by
    rintro (x | y | z) h <;> simp_all [isX, isY, isZ]
  have hxny : ∀ v : RV X Y Z, isX v → ¬ isY v := by rintro (x | y | z) <;> simp [isX, isY]
  obtain ⟨a0, ha0⟩ := Finset.card_pos.1 (by omega : 0 < A.card)
  obtain ⟨b0, hb0⟩ := Finset.card_pos.1 (by omega : 0 < B.card)
  -- no edge of `G` between the two sides
  have hnoG : ∀ x y, (.inl x : RV X Y Z) ∈ A → (.inr (.inl y) : RV X Y Z) ∈ B → ¬ G x y := by
    intro x y hx hy hG
    exact hR ⟨_, hx, _, hy, z, hz, mem_redE (by simp) (by rintro rfl; exact hzA _ hx hzz)
      (by rintro rfl; exact hzB _ hy hzz) (by simp [Allowed, hG, hzz])⟩
  have hnoG' : ∀ x y, (.inl x : RV X Y Z) ∈ B → (.inr (.inl y) : RV X Y Z) ∈ A → ¬ G x y := by
    intro x y hx hy hG
    refine hR ⟨_, hy, _, hx, z, hz, ?_⟩
    rw [Finset.insert_comm]
    exact mem_redE (by simp) (by rintro rfl; exact hzB _ hx hzz)
      (by rintro rfl; exact hzA _ hy hzz) (by simp [Allowed, hG, hzz])
  rcases hxy a0 (hzA a0 ha0) with hxa0 | hya0
  · -- `A ⊆ X`, `B ⊆ Y`
    have hBY : ∀ b ∈ B, isY b := fun b hb =>
      (hxy b (hzB b hb)).resolve_left (hXX a0 ha0 b hb hxa0)
    have hAX : ∀ a ∈ A, isX a := fun a ha =>
      (hxy a (hzA a ha)).resolve_right (hYY a ha b0 hb0 · (hBY b0 hb0))
    obtain ⟨A', hA', hA'c⟩ := Finset.exists_subset_card_eq (le_trans ha (card_le_of_subset_X hAX))
    obtain ⟨B', hB', hB'c⟩ := Finset.exists_subset_card_eq (le_trans hb (card_le_of_subset_Y hBY))
    refine ⟨A', B', hA'c, hB'c, fun x hx y hy => hnoG x y ?_ ?_⟩
    · simpa using hA' hx
    · simpa using hB' hy
  · -- `A ⊆ Y`, `B ⊆ X`
    have hBX : ∀ b ∈ B, isX b := fun b hb =>
      (hxy b (hzB b hb)).resolve_right (hYY a0 ha0 b hb hya0)
    have hAY : ∀ a ∈ A, isY a := fun a ha =>
      (hxy a (hzA a ha)).resolve_left (hXX a ha b0 hb0 · (hBX b0 hb0))
    obtain ⟨A', hA', hA'c⟩ := Finset.exists_subset_card_eq (le_trans hb (card_le_of_subset_X hBX))
    obtain ⟨B', hB', hB'c⟩ := Finset.exists_subset_card_eq (le_trans ha (card_le_of_subset_Y hAY))
    refine ⟨A', B', hA'c, hB'c, fun x hx y hy => hnoG' x y ?_ ?_⟩
    · simpa using hA' hx
    · simpa using hB' hy

/-- **Theorem 1** of [JMS12], correctness of the reduction: for `1 ≤ t ≤ |X|, |Y|` and
`|Z| = |X| + |Y| − t`, the bipartite graph `G` has an independent pair of `t`-sets iff the
hypergraph `redE G` (on `n' = 2(|X| + |Y|) − t` vertices) is not `t`-disjoint. -/
theorem theorem_1_reduction (G : X → Y → Prop) {t : ℕ} (ht : 1 ≤ t) (htX : t ≤ Fintype.card X)
    (htY : t ≤ Fintype.card Y) (hZ : Fintype.card Z = Fintype.card X + Fintype.card Y - t) :
    BBIS G t ↔ ¬ HDisjoint (redE (Z := Z) G) t := by
  have hcard : Fintype.card (RV X Y Z) =
      Fintype.card X + Fintype.card Y + Fintype.card Z := by
    simp [RV, Fintype.card_sum, add_assoc]
  constructor
  · rintro ⟨A, B, hA, hB, hind⟩ hD
    obtain ⟨a, ha, b, hb, c, hc, he⟩ := hD (A.map Function.Embedding.inl)
      (B.map (Function.Embedding.inl.trans Function.Embedding.inr))
      (Finset.univ.map (Function.Embedding.inr.trans Function.Embedding.inr))
      ⟨by simp [Finset.disjoint_left], by simp [Finset.disjoint_left],
        by simp [Finset.disjoint_left], by simp [hA], by simp [hB], by simp; omega,
        by simp [hA, hB, hcard]; omega⟩
    simp only [Finset.mem_map, Function.Embedding.trans_apply, Function.Embedding.inl_apply,
      Function.Embedding.inr_apply] at ha hb hc
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    obtain ⟨z, -, rfl⟩ := hc
    exact not_mem_redE (hind x hx y hy) he
  · intro hnD
    simp only [HDisjoint, not_forall] at hnD
    obtain ⟨A, B, C, hv, hR⟩ := hnD
    -- some vertex of `Z` is used
    have hZused : ∃ v ∈ A ∪ B ∪ C, isZ v := by
      by_contra hno
      push Not at hno
      have hsub : A ∪ B ∪ C ⊆ Finset.univ.filter fun v : RV X Y Z => ¬ isZ v := by
        intro v hv; simpa using hno v hv
      have h1 := Finset.card_le_card hsub
      have h2 : (Finset.univ.filter fun v : RV X Y Z => ¬ isZ v).card ≤
          Fintype.card X + Fintype.card Y := by
        have hsub2 : (Finset.univ.filter fun v : RV X Y Z => ¬ isZ v) ⊆
            (Finset.univ : Finset (X ⊕ Y)).image
              (fun v => match v with | .inl x => .inl x | .inr y => .inr (.inl y)) := by
          intro v hv
          rcases v with x | y | z
          · exact Finset.mem_image.2 ⟨.inl x, Finset.mem_univ _, rfl⟩
          · exact Finset.mem_image.2 ⟨.inr y, Finset.mem_univ _, rfl⟩
          · simp [isZ] at hv
        refine (Finset.card_le_card hsub2).trans (Finset.card_image_le.trans ?_)
        simp [Fintype.card_sum]
      obtain ⟨hAB, hAC, hBC, -, -, -, hs⟩ := hv
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨hAC, hBC⟩),
        Finset.card_union_of_disjoint hAB] at h1
      rw [hcard] at hs
      omega
    have hv0 := hv
    obtain ⟨hAB, hAC, hBC, ha, hb, hc, -⟩ := hv0
    -- no two of the classes contain `Z`-vertices
    have twoZ : ∀ {P Q R : Finset (RV X Y Z)}, Disjoint P Q → 0 < R.card →
        Disjoint P R → Disjoint Q R → ¬ Rainbow (redE G) P Q R →
        ∀ p ∈ P, ∀ q ∈ Q, isZ p → ¬ isZ q := by
      intro P Q R hPQ hR0 hPR hQR hnR p hp q hq hzp hzq
      obtain ⟨r, hr⟩ := Finset.card_pos.1 hR0
      refine hnR ⟨p, hp, q, hq, r, hr, mem_redE (fun h => Finset.disjoint_left.1 hPQ hp (h ▸ hq))
        (fun h => Finset.disjoint_left.1 hPR hp (h ▸ hr))
        (fun h => Finset.disjoint_left.1 hQR hq (h ▸ hr)) ?_⟩
      by_cases hzr : isZ r
      · exact Or.inl ⟨hzp, hzq, hzr⟩
      · exact Or.inr (Or.inl ⟨hzp, hzq, hzr⟩)
    have rACB : ¬ Rainbow (redE G) A C B := fun h => hR (rainbow_swap23 h)
    have rBAC : ¬ Rainbow (redE G) B A C := fun h => hR (rainbow_swap12 h)
    have rBCA : ¬ Rainbow (redE G) B C A := fun h => rBAC (rainbow_swap23 h)
    have rCAB : ¬ Rainbow (redE G) C A B := fun h => rACB (rainbow_swap12 h)
    have rCBA : ¬ Rainbow (redE G) C B A := fun h => rCAB (rainbow_swap23 h)
    have pA : 0 < A.card := by omega
    have pB : 0 < B.card := by omega
    have pC : 0 < C.card := by omega
    simp only [Finset.mem_union] at hZused
    obtain ⟨w, hw, hzw⟩ := hZused
    rcases hw with (hwA | hwB) | hwC
    · -- `Z` meets `A`: use the colouring `B, C, A`
      refine bbis_of_violation ht (validColoring_swap23 (validColoring_swap12 hv)) rBCA
        ⟨w, hwA, hzw⟩ (fun b hb hzb => twoZ hAB.symm pC hBC hAC rBAC b hb w hwA hzb hzw)
        (fun c hc hzc => twoZ hAC.symm pB hBC.symm hAB rCAB c hc w hwA hzc hzw)
    · -- `Z` meets `B`: use the colouring `A, C, B`
      refine bbis_of_violation ht (validColoring_swap23 hv) rACB ⟨w, hwB, hzw⟩
        (fun a ha hza => twoZ hAB pC hAC hBC hR a ha w hwB hza hzw)
        (fun c hc hzc => twoZ hBC.symm pA hAC.symm hAB.symm rCBA c hc w hwB hzc hzw)
    · -- `Z` meets `C`
      refine bbis_of_violation ht hv hR ⟨w, hwC, hzw⟩
        (fun a ha hza => twoZ hAC pB hAB hBC.symm rACB a ha w hwC hza hzw)
        (fun b hb hzb => twoZ hBC pA hAB.symm hAC.symm rBCA b hb w hwC hzb hzw)

/-- **Theorem 1** of [JMS12] in the form of the introduction: the reduction instance has
`n' = 2f + t` vertices with `f = |X| + |Y| − t ≥ n'/3`, and `G` has an independent pair of
`t`-sets iff `redE G` is not `f`-tolerant (i.e. Byzantine agreement against `f` faults is not
possible, by the characterization of [38]). -/
theorem theorem_1_reduction_fTolerant (G : X → Y → Prop) {t : ℕ} (ht : 1 ≤ t)
    (htX : t ≤ Fintype.card X) (htY : t ≤ Fintype.card Y)
    (hZ : Fintype.card Z = Fintype.card X + Fintype.card Y - t) :
    Fintype.card (RV X Y Z) = 2 * (Fintype.card X + Fintype.card Y - t) + t ∧
      (BBIS G t ↔ ¬ FTolerant (redE (Z := Z) G) (Fintype.card X + Fintype.card Y - t)) := by
  have hcard : Fintype.card (RV X Y Z) =
      Fintype.card X + Fintype.card Y + Fintype.card Z := by
    simp [RV, Fintype.card_sum, add_assoc]
  refine ⟨by omega, ?_⟩
  rw [theorem_2 (by omega) (by omega), theorem_1_reduction G ht htX htY hZ]
  have : Fintype.card (RV X Y Z) - 2 * (Fintype.card X + Fintype.card Y - t) = t := by omega
  rw [this]

end Podc.EquivocationPrice
