import Papers.PODC2018.SpannerApproximation.Spanner

/-!
# The lower-bound graph `G(ℓ, β)` (§2 of Censor-Hillel–Dory, PODC 2018)

Vertices (`Vtx ℓ β p`): `X1 = {x¹ᵢ, x²ᵢ}`, `Y1 = {y¹ᵢ, y²ᵢ}`, `Y3 = {y³ᵢ}` (`i < ℓ`),
`X2 = {xⁱⱼ}`, `Y2 = {yⁱⱼ}` (`i < ℓ`, `j < β`), and `p` padding vertices (`p = 0` is the paper's
graph; padding is used to reach every number of vertices).

Arcs (`arc a b`), for inputs `a b : Fin ℓ × Fin ℓ → Bool`:
`x¹ᵢ → y¹ᵢ`, `x²ᵢ → y²ᵢ` (matching), `xⁱⱼ → x¹ᵢ`, `y²ᵢ → y³ᵢ`, `y³ᵢ → yⁱⱼ`, the complete
bipartite `D = {xⁱⱼ → yʳₛ}`, the input arcs `x¹ᵢ → x²ᵣ` iff `a (i, r) = 0` and `y¹ᵢ → y²ᵣ` iff
`b (i, r) = 0`, and `padᵩ → x¹₀`.

* `claim_2_2_path`, `claim_2_2_unique`: Claim 2.2.
* `nonD_isDiSpanner`, `card_nonD_le`, `card_inter_D_ge`: the two halves of Lemmas 2.3 / 2.6
  (`lemma_2_3`, `lemma_2_6` are the paper's statements for `p = 0`).
* `net_connected`: the underlying network is connected for all inputs.
-/

namespace Podc.SpannerApproximation

open Finset Relation

/-- Vertices of `G(ℓ, β)` with `p` padding vertices. -/
inductive Vtx (ℓ β p : ℕ) where
  /-- `x¹ᵢ ∈ X1`. -/
  | x1 (i : Fin ℓ)
  /-- `x²ᵢ ∈ X1`. -/
  | x2 (i : Fin ℓ)
  /-- `y¹ᵢ ∈ Y1`. -/
  | y1 (i : Fin ℓ)
  /-- `y²ᵢ ∈ Y1`. -/
  | y2 (i : Fin ℓ)
  /-- `y³ᵢ ∈ Y3`. -/
  | y3 (i : Fin ℓ)
  /-- `xⁱⱼ ∈ X2`. -/
  | xb (i : Fin ℓ) (j : Fin β)
  /-- `yⁱⱼ ∈ Y2`. -/
  | yb (i : Fin ℓ) (j : Fin β)
  /-- Padding vertex. -/
  | pad (q : Fin p)
  deriving DecidableEq

namespace Vtx

variable {ℓ β p : ℕ}

/-- `Vtx` as a sum type. -/
def equivSum : Vtx ℓ β p ≃ Fin ℓ ⊕ Fin ℓ ⊕ Fin ℓ ⊕ Fin ℓ ⊕ Fin ℓ ⊕ (Fin ℓ × Fin β) ⊕
    (Fin ℓ × Fin β) ⊕ Fin p where
  toFun
    | x1 i => .inl i
    | x2 i => .inr (.inl i)
    | y1 i => .inr (.inr (.inl i))
    | y2 i => .inr (.inr (.inr (.inl i)))
    | y3 i => .inr (.inr (.inr (.inr (.inl i))))
    | xb i j => .inr (.inr (.inr (.inr (.inr (.inl (i, j))))))
    | yb i j => .inr (.inr (.inr (.inr (.inr (.inr (.inl (i, j)))))))
    | pad q => .inr (.inr (.inr (.inr (.inr (.inr (.inr q))))))
  invFun
    | .inl i => x1 i
    | .inr (.inl i) => x2 i
    | .inr (.inr (.inl i)) => y1 i
    | .inr (.inr (.inr (.inl i))) => y2 i
    | .inr (.inr (.inr (.inr (.inl i)))) => y3 i
    | .inr (.inr (.inr (.inr (.inr (.inl (i, j)))))) => xb i j
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl (i, j))))))) => yb i j
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr q)))))) => pad q
  left_inv v := by cases v <;> rfl
  right_inv s := by
    rcases s with i | i | i | i | i | ⟨i, j⟩ | ⟨i, j⟩ | q <;> rfl

instance : Fintype (Vtx ℓ β p) := Fintype.ofEquiv _ equivSum.symm

/-- `G(ℓ, β)` with `p` padding vertices has `2ℓβ + 5ℓ + p` vertices. -/
lemma card : Fintype.card (Vtx ℓ β p) = 2 * ℓ * β + 5 * ℓ + p := by
  rw [Fintype.card_congr equivSum]
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
  ring

/-- Bob's side `V_B = Y1`. -/
def bobSide : Vtx ℓ β p → Bool
  | y1 _ => true
  | y2 _ => true
  | _ => false

end Vtx

open Vtx

variable {ℓ β p : ℕ}

/-- Inputs: `ℓ²`-bit strings indexed by pairs `(i, r)`. -/
abbrev Inp (ℓ : ℕ) := Fin ℓ × Fin ℓ → Bool

/-- The arcs of `G(ℓ, β)` for inputs `a`, `b`. -/
def arc (a b : Inp ℓ) : Vtx ℓ β p → Vtx ℓ β p → Bool
  | x1 i, y1 i' => decide (i = i')
  | x2 i, y2 i' => decide (i = i')
  | xb i _, x1 i' => decide (i = i')
  | y2 i, y3 i' => decide (i = i')
  | y3 i, yb i' _ => decide (i = i')
  | xb _ _, yb _ _ => true
  | x1 i, x2 r => !a (i, r)
  | y1 i, y2 r => !b (i, r)
  | pad _, x1 i => decide (i.val = 0)
  | _, _ => false

/-- The arcs of the dense subgraph `D` (from `X2` to `Y2`). -/
def isD : Vtx ℓ β p → Vtx ℓ β p → Bool
  | xb _ _, yb _ _ => true
  | _, _ => false

/-- The digraph `G(ℓ, β)` (with padding) as a set of arcs. -/
def arcs (a b : Inp ℓ) : Finset (Vtx ℓ β p × Vtx ℓ β p) :=
  univ.filter fun e => arc a b e.1 e.2 = true

/-- The arcs of `D`. -/
def dArcs : Finset (Vtx ℓ β p × Vtx ℓ β p) := univ.filter fun e => isD e.1 e.2 = true

/-- All arcs not in `D`. -/
def nonD (a b : Inp ℓ) : Finset (Vtx ℓ β p × Vtx ℓ β p) :=
  univ.filter fun e => arc a b e.1 e.2 = true ∧ isD e.1 e.2 = false

/-- The number of common elements of the inputs, `|a ∩ b|`. -/
def inter (a b : Inp ℓ) : Finset (Fin ℓ × Fin ℓ) := univ.filter fun q => a q = true ∧ b q = true

@[simp] lemma mem_arcs {a b : Inp ℓ} {e : Vtx ℓ β p × Vtx ℓ β p} :
    e ∈ arcs a b ↔ arc a b e.1 e.2 = true := by simp [arcs]

lemma arc_irrefl (a b : Inp ℓ) (v : Vtx ℓ β p) : arc a b v v = false := by
  cases v <;> rfl

lemma nonD_subset (a b : Inp ℓ) : nonD a b ⊆ (arcs a b : Finset (Vtx ℓ β p × _)) := by
  intro e he
  simp only [nonD, mem_filter, mem_univ, true_and] at he
  simpa using he.1

/-! ### Claim 2.2 -/

/-- The vertices that can be reached from `x¹ᵢ`: an over-approximation that is closed under arcs. -/
def reach (a b : Inp ℓ) (i : Fin ℓ) : Vtx ℓ β p → Prop
  | x1 i' => i' = i
  | y1 i' => i' = i
  | x2 r => a (i, r) = false
  | y2 r => a (i, r) = false ∨ b (i, r) = false
  | y3 r => a (i, r) = false ∨ b (i, r) = false
  | yb r _ => a (i, r) = false ∨ b (i, r) = false
  | _ => False

lemma reach_step {a b : Inp ℓ} {i : Fin ℓ} {u v : Vtx ℓ β p} (hu : reach a b i u)
    (huv : arc a b u v = true) : reach a b i v := by
  cases u <;> cases v <;> simp_all [reach, arc]

lemma reach_of_reflTransGen {a b : Inp ℓ} {i : Fin ℓ} {v : Vtx ℓ β p}
    (h : ReflTransGen (arcRel (arcs a b)) (x1 i) v) : reach a b i v := by
  induction h with
  | refl => rfl
  | tail _ hst ih => exact reach_step ih (by simpa [arcRel] using hst)

/-- **Claim 2.2, first part.** If `(x¹ᵢ, x²ᵣ)` or `(y¹ᵢ, y²ᵣ)` is an arc, there is a directed path of
length `5` from `xⁱⱼ` to `yʳₛ` avoiding `D`. -/
theorem claim_2_2_path {a b : Inp ℓ} {i r : Fin ℓ} (j s : Fin β)
    (h : a (i, r) = false ∨ b (i, r) = false) :
    RelatesInSteps (arcRel (nonD a b : Finset (Vtx ℓ β p × _))) (xb i j) (yb r s) 5 := by
  have st : ∀ u v : Vtx ℓ β p, arc a b u v = true → isD u v = false →
      arcRel (nonD a b) u v := fun u v h1 h2 => by simp [arcRel, nonD, h1, h2]
  have s1 := st (xb i j) (x1 i) (by simp [arc]) rfl
  have s4 := st (y2 r) (y3 r) (by simp [arc]) rfl
  have s5 := st (y3 r) (yb r s) (by simp [arc]) rfl
  rcases h with h | h
  · have s2 := st (x1 i) (x2 r) (by simp [arc, h]) rfl
    have s3 := st (x2 r) (y2 r) (by simp [arc]) rfl
    exact .tail _ _ _ _ (.tail _ _ _ _ (.tail _ _ _ _ (.tail _ _ _ _
      (.single s1) s2) s3) s4) s5
  · have s2 := st (x1 i) (y1 i) (by simp [arc]) rfl
    have s3 := st (y1 i) (y2 r) (by simp [arc, h]) rfl
    exact .tail _ _ _ _ (.tail _ _ _ _ (.tail _ _ _ _ (.tail _ _ _ _
      (.single s1) s2) s3) s4) s5

/-- **Claim 2.2, second part.** If neither `(x¹ᵢ, x²ᵣ)` nor `(y¹ᵢ, y²ᵣ)` is an arc, the only directed
walk from `xⁱⱼ` to `yʳₛ` is the arc `(xⁱⱼ, yʳₛ)` itself: every walk has length `1`. -/
theorem claim_2_2_unique {a b : Inp ℓ} {i r : Fin ℓ} {j s : Fin β}
    (h : a (i, r) = true ∧ b (i, r) = true) {n : ℕ}
    (hw : RelatesInSteps (arcRel (arcs a b : Finset (Vtx ℓ β p × _))) (xb i j) (yb r s) n) :
    n = 1 := by
  rcases n with _ | n
  · cases hw.zero
  obtain ⟨w, hw1, hw2⟩ := hw.succ'
  simp only [arcRel, mem_arcs] at hw1
  cases w with
  | x1 i' =>
    have hi : i = i' := by simpa [arc] using hw1
    subst hi
    have := reach_of_reflTransGen hw2.reflTransGen
    simp [reach, h.1, h.2] at this
  | yb r' s' =>
    rcases n with _ | n
    · rfl
    obtain ⟨w', hw', -⟩ := hw2.succ'
    simp only [arcRel, mem_arcs] at hw'
    cases w' <;> simp [arc] at hw'
  | _ => simp [arc] at hw1

/-- Consequence of Claim 2.2: a spanner (of any stretch) contains all arcs `(xⁱⱼ, yʳₛ)` of `D`
for which `aᵢᵣ = bᵢᵣ = 1`. -/
lemma mem_of_isDiSpanner {a b : Inp ℓ} {H : Finset (Vtx ℓ β p × Vtx ℓ β p)} {k : ℕ}
    (hH : IsDiSpanner (arcs a b) H k) {i r : Fin ℓ} (h : a (i, r) = true ∧ b (i, r) = true)
    (j s : Fin β) : (xb i j, yb r s) ∈ H := by
  obtain ⟨m, -, hm⟩ := hH.2 (xb i j, yb r s) (by simp [arc])
  have hm' : RelatesInSteps (arcRel (arcs a b)) (xb i j) (yb r s) m :=
    RelatesInSteps.map (r := arcRel H) id (fun u v huv => hH.1 huv) hm
  have := claim_2_2_unique h hm'
  subst this
  obtain ⟨w, h1, h2⟩ := hm.succ'
  rw [h2.zero] at h1
  exact h1

/-! ### Lemmas 2.3 and 2.6 -/

/-- If the inputs are disjoint, the arcs not in `D` form a `5`-spanner (hence a `k`-spanner for
`k ≥ 5`). -/
theorem nonD_isDiSpanner {a b : Inp ℓ} (hab : ∀ q, ¬(a q = true ∧ b q = true)) {k : ℕ}
    (hk : 5 ≤ k) : IsDiSpanner (arcs a b) (nonD a b : Finset (Vtx ℓ β p × _)) k := by
  refine ⟨nonD_subset a b, fun e he => ?_⟩
  obtain ⟨u, v⟩ := e
  simp only [mem_arcs] at he
  by_cases hD : isD u v = true
  · cases u <;> cases v <;> simp [isD] at hD
    rename_i i j r s
    have : a (i, r) = false ∨ b (i, r) = false := by
      have := hab (i, r)
      cases ha : a (i, r) <;> cases hb : b (i, r) <;> simp_all
    exact ⟨5, hk, claim_2_2_path j s this⟩
  · exact (RelatesWithinSteps.single (by simp [arcRel, nonD, he, hD])).mono (by omega)

/-- The number of arcs not in `D` is at most `2ℓβ + 2ℓ² + 3ℓ + p`. -/
theorem card_nonD_le (a b : Inp ℓ) :
    (nonD a b : Finset (Vtx ℓ β p × _)).card ≤ 2 * ℓ * β + 2 * ℓ ^ 2 + 3 * ℓ + p := by
  classical
  -- every non-`D` arc is the image of one of the following parametrisations
  let f1 : Fin ℓ → Vtx ℓ β p × Vtx ℓ β p := fun i => (x1 i, y1 i)
  let f2 : Fin ℓ → Vtx ℓ β p × Vtx ℓ β p := fun i => (x2 i, y2 i)
  let f3 : Fin ℓ → Vtx ℓ β p × Vtx ℓ β p := fun i => (y2 i, y3 i)
  let f4 : Fin ℓ × Fin β → Vtx ℓ β p × Vtx ℓ β p := fun q => (xb q.1 q.2, x1 q.1)
  let f5 : Fin ℓ × Fin β → Vtx ℓ β p × Vtx ℓ β p := fun q => (y3 q.1, yb q.1 q.2)
  let f6 : Fin ℓ × Fin ℓ → Vtx ℓ β p × Vtx ℓ β p := fun q => (x1 q.1, x2 q.2)
  let f7 : Fin ℓ × Fin ℓ → Vtx ℓ β p × Vtx ℓ β p := fun q => (y1 q.1, y2 q.2)
  let f8 : Fin p → Vtx ℓ β p × Vtx ℓ β p := fun q => (pad q, if h : 0 < ℓ then x1 ⟨0, h⟩
    else pad q)
  have hsub : nonD a b ⊆ (((((((univ.image f1 ∪ univ.image f2) ∪ univ.image f3) ∪
      univ.image f4) ∪ univ.image f5) ∪ univ.image f6) ∪ univ.image f7) ∪ univ.image f8) := by
    rintro ⟨u, v⟩ he
    simp only [nonD, mem_filter, mem_univ, true_and] at he
    obtain ⟨h1, h2⟩ := he
    simp only [mem_union, mem_image, mem_univ, true_and, f1, f2, f3, f4, f5, f6, f7, f8,
      Prod.mk.injEq, Prod.exists]
    cases u <;> cases v <;> simp [arc, isD] at h1 h2 ⊢ <;> try (subst_vars; simp)
    rename_i i h1
    have hl : 0 < ℓ := by have := i.isLt; omega
    simp only [hl, ↓reduceDIte]
    congr 1
    ext
    simp [h1]
  have e : ∀ {α : Type} [Fintype α] (f : α → Vtx ℓ β p × Vtx ℓ β p),
      (univ.image f).card ≤ Fintype.card α := fun f => card_image_le.trans (by simp)
  have e1 := e f1; have e2 := e f2; have e3 := e f3; have e4 := e f4
  have e5 := e f5; have e6 := e f6; have e7 := e f7; have e8 := e f8
  simp only [Fintype.card_fin, Fintype.card_prod] at e1 e2 e3 e4 e5 e6 e7 e8
  have u1 := card_union_le (image f1 univ) (image f2 univ)
  have u2 := card_union_le (image f1 univ ∪ image f2 univ) (image f3 univ)
  have u3 := card_union_le (image f1 univ ∪ image f2 univ ∪ image f3 univ) (image f4 univ)
  have u4 := card_union_le (image f1 univ ∪ image f2 univ ∪ image f3 univ ∪ image f4 univ)
    (image f5 univ)
  have u5 := card_union_le (image f1 univ ∪ image f2 univ ∪ image f3 univ ∪ image f4 univ ∪
    image f5 univ) (image f6 univ)
  have u6 := card_union_le (image f1 univ ∪ image f2 univ ∪ image f3 univ ∪ image f4 univ ∪
    image f5 univ ∪ image f6 univ) (image f7 univ)
  have u7 := card_union_le (image f1 univ ∪ image f2 univ ∪ image f3 univ ∪ image f4 univ ∪
    image f5 univ ∪ image f6 univ ∪ image f7 univ) (image f8 univ)
  have := card_le_card hsub
  nlinarith

/-- Every `k`-spanner contains at least `β² · |a ∩ b|` arcs of `D` (Claim 2.2: for every common
element `(i, r)` all `β²` arcs from block `i` of `X2` to block `r` of `Y2`). -/
theorem card_inter_D_ge {a b : Inp ℓ} {H : Finset (Vtx ℓ β p × Vtx ℓ β p)} {k : ℕ}
    (hH : IsDiSpanner (arcs a b) H k) : β ^ 2 * (inter a b).card ≤ (H ∩ dArcs).card := by
  classical
  let f : (Fin ℓ × Fin ℓ) × Fin β × Fin β → Vtx ℓ β p × Vtx ℓ β p :=
    fun q => (xb q.1.1 q.2.1, yb q.1.2 q.2.2)
  have hf : Function.Injective f := by
    rintro ⟨⟨i, r⟩, j, s⟩ ⟨⟨i', r'⟩, j', s'⟩ h
    simp only [f, Prod.mk.injEq, xb.injEq, yb.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    rfl
  have hsub : (inter a b ×ˢ (univ : Finset (Fin β × Fin β))).image f ⊆ H ∩ dArcs := by
    intro e he
    simp only [mem_image, mem_product, inter, mem_filter, mem_univ, true_and, and_true] at he
    obtain ⟨⟨⟨i, r⟩, j, s⟩, hq, rfl⟩ := he
    exact mem_inter.2 ⟨mem_of_isDiSpanner hH hq j s, by simp only [dArcs, mem_filter, mem_univ, true_and]; rfl⟩
  have := card_le_card hsub
  rw [card_image_of_injective _ hf, card_product, card_univ, Fintype.card_prod,
    Fintype.card_fin] at this
  calc β ^ 2 * (inter a b).card = (inter a b).card * (β * β) := by ring
    _ ≤ _ := this

/-- **Lemma 2.3** (`ℓ ≤ β`, no padding). If the inputs are disjoint, `G(ℓ, β)` has a `k`-spanner
with at most `7ℓβ` arcs; otherwise every `k`-spanner contains at least `β²` arcs of `D`. -/
theorem lemma_2_3 {a b : Inp ℓ} (hℓβ : ℓ ≤ β) {k : ℕ} (hk : 5 ≤ k) :
    ((∀ q, ¬(a q = true ∧ b q = true)) →
        ∃ H, IsDiSpanner (arcs a b : Finset (Vtx ℓ β 0 × _)) H k ∧ H.card ≤ 7 * ℓ * β) ∧
      ((∃ q, a q = true ∧ b q = true) →
        ∀ H, IsDiSpanner (arcs a b : Finset (Vtx ℓ β 0 × _)) H k → β ^ 2 ≤ (H ∩ dArcs).card) := by
  refine ⟨fun h => ⟨nonD a b, nonD_isDiSpanner h hk, (card_nonD_le a b).trans ?_⟩,
    fun ⟨q, hq⟩ H hH => ?_⟩
  · have : ℓ * ℓ ≤ ℓ * β := Nat.mul_le_mul_left _ hℓβ
    have : ℓ ≤ ℓ * β := by rcases Nat.eq_zero_or_pos ℓ with h | h <;> nlinarith
    nlinarith
  · have h1 : 1 ≤ (inter a b).card := card_pos.2 ⟨q, by simp [inter, hq]⟩
    have := card_inter_D_ge hH
    nlinarith

/-- **Lemma 2.6** (`β ≤ ℓ`, no padding). If the inputs are disjoint, `G(ℓ, β)` has a `k`-spanner
with at most `7ℓ²` arcs; if they are far from disjoint (`ℓ² ≤ 12 · |a ∩ b|`), every `k`-spanner
contains at least `β²ℓ²/12` arcs of `D`. -/
theorem lemma_2_6 {a b : Inp ℓ} (hβℓ : β ≤ ℓ) {k : ℕ} (hk : 5 ≤ k) :
    ((∀ q, ¬(a q = true ∧ b q = true)) →
        ∃ H, IsDiSpanner (arcs a b : Finset (Vtx ℓ β 0 × _)) H k ∧ H.card ≤ 7 * ℓ ^ 2) ∧
      (ℓ ^ 2 ≤ 12 * (inter a b).card →
        ∀ H, IsDiSpanner (arcs a b : Finset (Vtx ℓ β 0 × _)) H k →
          β ^ 2 * ℓ ^ 2 ≤ 12 * (H ∩ dArcs).card) := by
  refine ⟨fun h => ⟨nonD a b, nonD_isDiSpanner h hk, (card_nonD_le a b).trans ?_⟩,
    fun hfar H hH => ?_⟩
  · have : ℓ * β ≤ ℓ * ℓ := Nat.mul_le_mul_left _ hβℓ
    have : ℓ ≤ ℓ * ℓ := by rcases Nat.eq_zero_or_pos ℓ with h | h <;> nlinarith
    nlinarith
  · have := card_inter_D_ge hH
    calc β ^ 2 * ℓ ^ 2 ≤ β ^ 2 * (12 * (inter a b).card) := Nat.mul_le_mul_left _ hfar
      _ = 12 * (β ^ 2 * (inter a b).card) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ this

/-! ### The network -/

lemma adj_of_arc {a b : Inp ℓ} {u v : Vtx ℓ β p} (h : arc a b u v = true) :
    (net (arcs a b)).Adj u v :=
  ⟨fun huv => (by subst huv; rw [arc_irrefl] at h; cases h), Or.inl (by simp [h])⟩

/-- The digraph has no loops. -/
lemma not_mem_arcs_self (a b : Inp ℓ) (v : Vtx ℓ β p) : (v, v) ∉ arcs a b := by
  simp [arc_irrefl]

/-- The underlying network of `G(ℓ, β)` (with padding) is connected for all inputs, if `ℓ, β ≥ 1`. -/
theorem net_connected (a b : Inp ℓ) (hℓ : 0 < ℓ) (hβ : 0 < β) :
    (net (arcs a b : Finset (Vtx ℓ β p × _))).Connected := by
  set G := net (arcs a b : Finset (Vtx ℓ β p × _))
  let i0 : Fin ℓ := ⟨0, hℓ⟩
  let j0 : Fin β := ⟨0, hβ⟩
  have rA : ∀ {u v}, arc a b u v = true → G.Reachable u v := fun h => (adj_of_arc h).reachable
  have hyb : ∀ r s, G.Reachable (xb i0 j0) (yb r s) := fun r s => rA (by simp [arc])
  have hxb : ∀ i j, G.Reachable (xb i0 j0) (xb i j) := fun i j =>
    (hyb i0 j0).trans (rA (u := xb i j) (v := yb i0 j0) (by simp [arc])).symm
  have hx1 : ∀ i, G.Reachable (xb i0 j0) (x1 i) := fun i =>
    (hxb i j0).trans (rA (by simp [arc]))
  have hy3 : ∀ i, G.Reachable (xb i0 j0) (y3 i) := fun i =>
    (hyb i j0).trans (rA (u := y3 i) (v := yb i j0) (by simp [arc])).symm
  have hy2 : ∀ i, G.Reachable (xb i0 j0) (y2 i) := fun i =>
    (hy3 i).trans (rA (u := y2 i) (v := y3 i) (by simp [arc])).symm
  have hx2 : ∀ i, G.Reachable (xb i0 j0) (x2 i) := fun i =>
    (hy2 i).trans (rA (u := x2 i) (v := y2 i) (by simp [arc])).symm
  have hy1 : ∀ i, G.Reachable (xb i0 j0) (y1 i) := fun i =>
    (hx1 i).trans (rA (by simp [arc]))
  have hpad : ∀ q, G.Reachable (xb i0 j0) (pad q) := fun q =>
    (hx1 i0).trans (rA (u := pad q) (v := x1 i0) (by simp [arc, i0])).symm
  have hall : ∀ v, G.Reachable (xb i0 j0) v := by
    intro v; cases v <;> simp_all
  have : Nonempty (Vtx ℓ β p) := ⟨xb i0 j0⟩
  exact ⟨fun u v => (hall u).symm.trans (hall v)⟩

end Podc.SpannerApproximation
