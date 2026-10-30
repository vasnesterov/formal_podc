import Papers.PODC2020.MISInapproxCongest.Quadratic
import Papers.PODC2020.MISInapproxCongest.Reduction
import Papers.PODC2020.MISInapproxCongest.Code

/-!
# The constructions as `t`-party families of lower bound graphs; sizes of the cuts

* `linFamily c W`: the family `G_x̄` of Section 4 (player `i` simulates the copy `H^i`; only the
  weights depend on the input). `card_linFamily_Ecut`: it has exactly `t(t-1) · M · q(q-1)` cut
  arcs (`M` positions, alphabet of size `q`), i.e. `(t choose 2) · M · q(q-1)` cut edges.
* `quadFamily c W`: the family `F_x̄` of Section 5 (player `i` simulates `V^{(i,1)} ∪ V^{(i,2)}`);
  `card_quadFamily_Ecut`: `2 t(t-1) · M · q(q-1)` cut arcs.
* `paper_cut_edges`: with the paper's Reed–Solomon parameters (`M = q = ℓ + α`, `k = q^α`), `G_x̄`
  has `(t choose 2) · q² (q - 1)` cut edges — cubic in `q = ℓ + α ≈ log k`, not `t² log² k` as
  claimed in the proofs of Theorems 1 and 2.
-/

set_option linter.unusedSectionVars false

namespace Podc.MISInapproxCongest

open Finset Cslib Cslib.Congest Cslib.CommunicationComplexity

variable {t : ℕ} {K P A : Type*} [DecidableEq K] [DecidableEq P] [DecidableEq A] [Fintype K]
  [Fintype P] [Fintype A]

/-- The family `G_x̄` of Section 4 as a `t`-party family of lower bound graphs (Definition 4). -/
def linFamily (c : K → P → A) (W : ℕ) :
    MPFamily (Fin t) (fun _ => K → Bool) (Node t K P A) ℕ where
  G _ := graph c
  inp x := weight W x
  part v := v.1
  Ecut := univ.filter fun p => p.1.1 ≠ p.2.1 ∧ (graph c).Adj p.1 p.2
  Ecut_sub p hp := (mem_filter.1 hp).2.1
  adj_cut x a b hab h := mem_filter.2 ⟨mem_univ _, hab, h⟩
  adj_local _ _ _ _ _ _ := Iff.rfl
  adj_fixed _ _ _ _ _ := Iff.rfl
  inp_local x x' v h := by
    rcases v with ⟨i, m | hr⟩
    · simp only [weight]; rw [show x i = x' i from h]
    · rfl

instance (c : K → P → A) (W : ℕ) (x : Fin t → K → Bool) :
    DecidableRel ((linFamily c W).G x).Adj :=
  inferInstanceAs (DecidableRel (graph c).Adj)

/-- The cut of `G_x̄`: arcs between code nodes of different copies with equal position and
different symbols. -/
theorem card_linFamily_Ecut (c : K → P → A) (W : ℕ) :
    ((linFamily (t := t) c W).Ecut).card =
      (t * t - t) * (Fintype.card P * (Fintype.card A * Fintype.card A - Fintype.card A)) := by
  classical
  let f : (Fin t × Fin t) × P × (A × A) → Node t K P A × Node t K P A :=
    fun q => ((q.1.1, .inr (q.2.1, q.2.2.1)), (q.1.2, .inr (q.2.1, q.2.2.2)))
  have hf : Function.Injective f := by
    rintro ⟨⟨i, j⟩, h, r, r'⟩ ⟨⟨i', j'⟩, h', s, s'⟩ e
    simp only [f, Prod.mk.injEq, Sum.inr.injEq] at e
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, -, rfl⟩ := e
    rfl
  have : (linFamily (t := t) c W).Ecut =
      ((univ : Finset (Fin t)).offDiag ×ˢ (univ : Finset P) ×ˢ (univ : Finset A).offDiag).image f := by
    ext ⟨⟨i, u⟩, ⟨j, v⟩⟩
    simp only [linFamily, mem_filter, mem_univ, true_and, mem_image, mem_product, mem_offDiag,
      Prod.exists, f, Prod.mk.injEq]
    constructor
    · rintro ⟨hij, h⟩
      rcases u with m | ⟨h₁, r⟩ <;> rcases v with m' | ⟨h₂, r'⟩
      · exact absurd h.1 hij
      · exact absurd h.1 hij
      · exact absurd h.1 hij
      · obtain ⟨rfl, hr⟩ := h
        exact ⟨i, j, h₁, r, r', ⟨hij, hr⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
    · rintro ⟨i', j', h, r, r', ⟨hij, hr⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
      exact ⟨hij, by simpa using hr⟩
  rw [this, card_image_of_injective _ hf, card_product, card_product, offDiag_card, offDiag_card,
    card_univ, card_univ, card_univ, Fintype.card_fin]

/-- The family `F_x̄` of Section 5 as a `t`-party family of lower bound graphs. -/
def quadFamily (c : K → P → A) (W : ℕ) :
    MPFamily (Fin t) (fun _ => K × K → Bool) (Node2 t K P A) ℕ where
  G x := graph2 c x
  inp _ := weight2 W
  part v := v.1
  Ecut := univ.filter fun p => p.1.1 ≠ p.2.1 ∧ p.1.2.1 = p.2.2.1 ∧
    (graph c).Adj (p.1.1, p.1.2.2) (p.2.1, p.2.2.2)
  Ecut_sub p hp := (mem_filter.1 hp).2.1
  adj_cut x a b hab h := by
    rcases h with ⟨hb, h⟩ | ⟨-, h, -⟩
    · exact mem_filter.2 ⟨mem_univ _, hab, hb, h⟩
    · exact absurd h hab
  adj_local x x' a b hab hx := by
    change fAdj c x a b ↔ fAdj c x' a b
    unfold fAdj
    have key : ∀ (b : Bool) (u v : K ⊕ P × A), crossEdge x a.1 b u v ↔ crossEdge x' a.1 b u v := by
      intro b u v
      rcases b <;> rcases u <;> rcases v <;> simp [crossEdge, hx]
    rw [key]
  adj_fixed x x' a b hab := by
    change fAdj c x a b ↔ fAdj c x' a b
    unfold fAdj
    constructor <;> rintro (h | ⟨-, h, -⟩)
    · exact Or.inl h
    · exact absurd h hab
    · exact Or.inl h
    · exact absurd h hab
  inp_local _ _ _ _ := rfl

instance (c : K → P → A) (W : ℕ) (x : Fin t → K × K → Bool) :
    DecidableRel ((quadFamily c W).G x).Adj :=
  inferInstanceAs (DecidableRel (graph2 c x).Adj)

/-- The cut of `F_x̄`: in each of the two copies, the cut of `G`. -/
theorem card_quadFamily_Ecut (c : K → P → A) (W : ℕ) :
    ((quadFamily (t := t) c W).Ecut).card =
      2 * ((t * t - t) * (Fintype.card P * (Fintype.card A * Fintype.card A - Fintype.card A))) := by
  classical
  let f : (Fin t × Fin t) × Bool × P × (A × A) → Node2 t K P A × Node2 t K P A :=
    fun q => ((q.1.1, q.2.1, .inr (q.2.2.1, q.2.2.2.1)), (q.1.2, q.2.1, .inr (q.2.2.1, q.2.2.2.2)))
  have hf : Function.Injective f := by
    rintro ⟨⟨i, j⟩, b, h, r, r'⟩ ⟨⟨i', j'⟩, b', h', s, s'⟩ e
    simp only [f, Prod.mk.injEq, Sum.inr.injEq] at e
    obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, -, -, rfl⟩ := e
    rfl
  have : (quadFamily (t := t) c W).Ecut = ((univ : Finset (Fin t)).offDiag ×ˢ (univ : Finset Bool) ×ˢ
      (univ : Finset P) ×ˢ (univ : Finset A).offDiag).image f := by
    ext ⟨⟨i, b, u⟩, ⟨j, b', v⟩⟩
    simp only [quadFamily, mem_filter, mem_univ, true_and, mem_image, mem_product, mem_offDiag,
      Prod.exists, f, Prod.mk.injEq]
    constructor
    · rintro ⟨hij, rfl, h⟩
      rcases u with m | ⟨h₁, r⟩ <;> rcases v with m' | ⟨h₂, r'⟩
      · exact absurd h.1 hij
      · exact absurd h.1 hij
      · exact absurd h.1 hij
      · obtain ⟨rfl, hr⟩ := h
        exact ⟨i, j, b, h₁, r, r', ⟨hij, hr⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
    · rintro ⟨i', j', b'', h, r, r', ⟨hij, hr⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
      exact ⟨hij, rfl, by simpa using hr⟩
  rw [this, card_image_of_injective _ hf, card_product, card_product, card_product, offDiag_card,
    offDiag_card, card_univ, card_univ, card_univ, card_univ, Fintype.card_fin, Fintype.card_bool]
  ring

/-- **The cut of the paper's construction.** With the Reed–Solomon code over `ZMod q`
(`q = ℓ + α` prime, `k = q^α` messages, `q` positions) the family `G_x̄` of Section 4 has
`2 · (t choose 2) · q² (q - 1)` cut arcs, i.e. `(t choose 2) · q² (q - 1)` cut edges, which is
`Θ(t² log³ k)` for the paper's `q = ℓ + α = log k` (the proof of Theorem 1 uses
`|cut(G_x̄)| = t² log² k`). -/
theorem paper_cut_edges (q α W : ℕ) [Fact q.Prime] :
    ((linFamily (t := t) (rsCode q α q le_rfl) W).Ecut).card =
      2 * (t.choose 2 * (q ^ 2 * (q - 1))) := by
  rw [card_linFamily_Ecut, Fintype.card_fin, ZMod.card]
  have h2 := two_mul_choose_two t
  have e1 : t * t - t = t * (t - 1) := by
    rcases t with _ | t
    · simp
    · simp [Nat.mul_succ]
  have e2 : q * (q * q - q) = q ^ 2 * (q - 1) := by
    rcases q with _ | q
    · simp
    · have : (q + 1) * (q + 1) - (q + 1) = (q + 1) * q := by
        rw [Nat.mul_succ]; omega
      rw [this, Nat.add_sub_cancel]; ring
  rw [e1, e2, ← h2]; ring

/-- With the Reed–Solomon code of Theorem 4 (`q = ℓ + α` prime, messages `(ZMod q)^α`), distinct
codewords agree in at most `α` positions (the hypothesis of Property 3; in fact `≤ α - 1`). -/
theorem rsCode_agree_le (q α : ℕ) [Fact q.Prime] {m m' : Fin α → ZMod q} (h : m ≠ m') :
    agree (rsCode q α q le_rfl m) (rsCode q α q le_rfl m') ≤ α :=
  (rsCode_agree q α q le_rfl h).trans (Nat.sub_le _ _)

/-- **Lemma 2 for the paper's construction**: with the Reed–Solomon code over `ZMod q`,
`q = ℓ + α` prime, `t > 2` copies and `α t ≤ ε ℓ`, the family `G_x̄` is a `(1/2 + ε)`-approximate
MaxIS family. -/
theorem lemma2_paper {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ, 2 < t ∧ ∀ (q ℓ α : ℕ) [Fact q.Prime], q = ℓ + α → 1 ≤ ℓ → 1 ≤ α →
      (α : ℝ) * t ≤ ε * ℓ → ∀ x : Fin t → (Fin α → ZMod q) → Bool,
      (CommonElement x → ∃ I, IsIndep (graph (rsCode q α q le_rfl)) I ∧
        t * (2 * ℓ + α) ≤ wsum (weight ℓ x) I) ∧
      (PairwiseDisjoint x → ∀ I, IsIndep (graph (rsCode q α q le_rfl)) I →
        (wsum (weight ℓ x) I : ℝ) ≤ (1 / 2 + ε) * ((t * (2 * ℓ + α) : ℕ) : ℝ)) := by
  obtain ⟨t, ht, h⟩ := lemma2 hε
  refine ⟨t, ht, fun q ℓ α _ hq hℓ hα hαℓ x => ?_⟩
  exact h (by simp [hq]) (fun m m' hm => rsCode_agree_le q α hm) hℓ hα hαℓ x

/-- **Lemma 3 for the paper's construction** (Reed–Solomon code, `q = ℓ + α` prime). -/
theorem lemma3_paper {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ, 2 < t ∧ ∀ (q ℓ α : ℕ) [Fact q.Prime], q = ℓ + α →
      3 * (α : ℝ) * t ^ 2 ≤ 2 * ε * ℓ → ∀ x : Fin t → (Fin α → ZMod q) × (Fin α → ZMod q) → Bool,
      (CommonElement x → ∃ I, IsIndep (graph2 (rsCode q α q le_rfl) x) I ∧
        4 * t * ℓ + 2 * α * t ≤ wsum (weight2 ℓ) I) ∧
      (PairwiseDisjoint x → ∀ I, IsIndep (graph2 (rsCode q α q le_rfl) x) I →
        (wsum (weight2 ℓ) I : ℝ) ≤ (3 / 4 + ε) * ((4 * t * ℓ + 2 * α * t : ℕ) : ℝ)) := by
  obtain ⟨t, ht, h⟩ := lemma3 hε
  refine ⟨t, ht, fun q ℓ α _ hq hαℓ x => ?_⟩
  exact h (by simp [hq]) (fun m m' hm => rsCode_agree_le q α hm) hαℓ x

end Podc.MISInapproxCongest
