import Mathlib

/-!
# `(H, F)`-lower bound graphs (Section 3.2 of Drucker–Kuhn–Oshman, PODC 2014)

A. Drucker, F. Kuhn, R. Oshman, *On the Power of the Congested Clique Model*, PODC 2014.

* `LowerBoundGraph H F G'` — Definition 10: two vertex-disjoint copies `F_A = φA(F)`,
  `F_B = φB(F)` of `F` inside `G'` such that (I) every edge `e` of `F` lies on a copy of `H` whose
  edges include `φA(e)` and `φB(e)` and whose vertices in `V_A ∪ V_B` are exactly the four endpoints
  of `φA(e)`, `φB(e)`, and (II) every copy of `H` in `G'` is of this form.
* `LowerBoundGraph.observation_11` — Observation 11: a subgraph `G ≤ G'` containing all edges of
  `G'` outside `E_A ∪ E_B` contains `H` iff `φA(e), φB(e) ∈ E(G)` for some edge `e` of `F`.
* `LowerBoundGraph.IsSparse` — Definition 12 (`δ`-sparse).

Copies of `H` are Mathlib's `SimpleGraph.Copy` (injective homomorphisms), i.e. not necessarily
induced subgraphs isomorphic to `H`, as in the paper ("`G'` contains a subgraph `H'` isomorphic to
`H`").
-/

namespace Podc.CongestedCliquePower

open SimpleGraph

variable {VH VF V : Type*} {H : SimpleGraph VH} {F : SimpleGraph VF} {G' : SimpleGraph V}

/-- `{x, y}` is an edge of the copy `f` of `H` (the image of an edge of `H`). -/
def CopyAdj (f : H.Copy G') (x y : V) : Prop :=
  ∃ a b, H.Adj a b ∧ f a = x ∧ f b = y

lemma CopyAdj.adj {f : H.Copy G'} {x y : V} (h : CopyAdj f x y) : G'.Adj x y := by
  obtain ⟨a, b, hab, rfl, rfl⟩ := h
  exact f.toHom.map_adj hab

lemma CopyAdj.symm {f : H.Copy G'} {x y : V} (h : CopyAdj f x y) : CopyAdj f y x := by
  obtain ⟨a, b, hab, rfl, rfl⟩ := h
  exact ⟨b, a, hab.symm, rfl, rfl⟩

/-- The two copies of `F` of Definition 10: injective homomorphisms `φA, φB : F → G'` with disjoint
images `V_A`, `V_B`. -/
structure LBData (H : SimpleGraph VH) (F : SimpleGraph VF) (G' : SimpleGraph V) where
  /-- The copy `F_A` of `F` (Alice's side). -/
  φA : F.Copy G'
  /-- The copy `F_B` of `F` (Bob's side). -/
  φB : F.Copy G'
  /-- `F_A` and `F_B` are vertex-disjoint. -/
  disjoint : ∀ a b, φA a ≠ φB b

namespace LBData

variable (D : LBData H F G')

/-- Conditions (b) and (c) of Definition 10 for the copy `f` of `H` and the edge `{u, v}` of `F`:
`φA(u)φA(v)` and `φB(u)φB(v)` are edges of the copy, and the vertices of the copy in `V_A ∪ V_B` are
exactly `φA(u), φA(v), φB(u), φB(v)`. -/
def Fits (f : H.Copy G') (u v : VF) : Prop :=
  F.Adj u v ∧ CopyAdj f (D.φA u) (D.φA v) ∧ CopyAdj f (D.φB u) (D.φB v) ∧
    ∀ x, (x ∈ Set.range f ∧ (x ∈ Set.range D.φA ∨ x ∈ Set.range D.φB)) ↔
      (x = D.φA u ∨ x = D.φA v ∨ x = D.φB u ∨ x = D.φB v)

/-- `x y` is an edge of `F_A` (an image `φA(e)` of an edge `e` of `F`). -/
def EA (x y : V) : Prop := ∃ u v, F.Adj u v ∧ D.φA u = x ∧ D.φA v = y

/-- `x y` is an edge of `F_B`. -/
def EB (x y : V) : Prop := ∃ u v, F.Adj u v ∧ D.φB u = x ∧ D.φB v = y

end LBData

/-- **Definition 10.** `G'` is an `(H, F)`-lower bound graph: it contains vertex-disjoint copies
`F_A`, `F_B` of `F` such that (I) for every edge `{u, v}` of `F` there is a copy of `H` satisfying
(b) and (c), and (II) every copy of `H` in `G'` satisfies (b) and (c) for some edge of `F`. -/
structure LowerBoundGraph (H : SimpleGraph VH) (F : SimpleGraph VF) (G' : SimpleGraph V)
    extends LBData H F G' where
  /-- Condition I: every edge of `F` is witnessed by a copy of `H`. -/
  exists_copy : ∀ u v, F.Adj u v → ∃ f : H.Copy G', toLBData.Fits f u v
  /-- Condition II: these are the only copies of `H`. -/
  fits_of_copy : ∀ f : H.Copy G', ∃ u v, toLBData.Fits f u v

namespace LowerBoundGraph

variable (L : LowerBoundGraph H F G')

/-- **Observation 11.** Let `G ≤ G'` contain every edge of `G'` that is not an edge of `F_A` or
`F_B`. Then `G` contains a copy of `H` iff for some edge `e = {u, v}` of `F` both `φA(e)` and
`φB(e)` are edges of `G`. -/
theorem observation_11 (G : SimpleGraph V) (hle : G ≤ G')
    (hfix : ∀ x y, G'.Adj x y → ¬ L.EA x y → ¬ L.EB x y → G.Adj x y) :
    H ⊑ G ↔ ∃ u v, F.Adj u v ∧ G.Adj (L.φA u) (L.φA v) ∧ G.Adj (L.φB u) (L.φB v) := by
  constructor
  · rintro ⟨f⟩
    obtain ⟨u, v, huv, hA, hB, -⟩ := L.fits_of_copy ((Copy.ofLE G G' hle).comp f)
    refine ⟨u, v, huv, ?_, ?_⟩
    · obtain ⟨a, b, hab, ha, hb⟩ := hA
      rw [← ha, ← hb]
      exact f.toHom.map_adj hab
    · obtain ⟨a, b, hab, ha, hb⟩ := hB
      rw [← ha, ← hb]
      exact f.toHom.map_adj hab
  · rintro ⟨u, v, huv, hA, hB⟩
    obtain ⟨f, -, -, -, hc⟩ := L.exists_copy u v huv
    -- every edge of the copy is an edge of `G`
    refine ⟨⟨⟨f, fun {a b} hab => ?_⟩, f.injective⟩⟩
    have hG' : G'.Adj (f a) (f b) := f.toHom.map_adj hab
    by_cases hEA : L.EA (f a) (f b)
    · -- an `F_A`-edge of the copy must be `φA(u)φA(v)`
      obtain ⟨p, q, hpq, hp, hq⟩ := hEA
      have hpa := (hc (f a)).1 ⟨⟨a, rfl⟩, Or.inl ⟨p, hp⟩⟩
      have hqb := (hc (f b)).1 ⟨⟨b, rfl⟩, Or.inl ⟨q, hq⟩⟩
      have hAinj := L.φA.injective
      have hne : ∀ w, L.φA p ≠ L.φB w := fun w => L.disjoint p w
      have hne' : ∀ w, L.φA q ≠ L.φB w := fun w => L.disjoint q w
      rw [← hp] at hpa
      rw [← hq] at hqb
      have hp' : p = u ∨ p = v := by
        rcases hpa with h | h | h | h
        · exact Or.inl (hAinj h)
        · exact Or.inr (hAinj h)
        · exact absurd h (hne u)
        · exact absurd h (hne v)
      have hq' : q = u ∨ q = v := by
        rcases hqb with h | h | h | h
        · exact Or.inl (hAinj h)
        · exact Or.inr (hAinj h)
        · exact absurd h (hne' u)
        · exact absurd h (hne' v)
      rw [← hp, ← hq]
      rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
      · exact absurd hpq (F.irrefl)
      · exact hA
      · exact hA.symm
      · exact absurd hpq (F.irrefl)
    by_cases hEB : L.EB (f a) (f b)
    · obtain ⟨p, q, hpq, hp, hq⟩ := hEB
      have hpa := (hc (f a)).1 ⟨⟨a, rfl⟩, Or.inr ⟨p, hp⟩⟩
      have hqb := (hc (f b)).1 ⟨⟨b, rfl⟩, Or.inr ⟨q, hq⟩⟩
      have hBinj := L.φB.injective
      rw [← hp] at hpa
      rw [← hq] at hqb
      have hp' : p = u ∨ p = v := by
        rcases hpa with h | h | h | h
        · exact absurd h.symm (L.disjoint u p)
        · exact absurd h.symm (L.disjoint v p)
        · exact Or.inl (hBinj h)
        · exact Or.inr (hBinj h)
      have hq' : q = u ∨ q = v := by
        rcases hqb with h | h | h | h
        · exact absurd h.symm (L.disjoint u q)
        · exact absurd h.symm (L.disjoint v q)
        · exact Or.inl (hBinj h)
        · exact Or.inr (hBinj h)
      rw [← hp, ← hq]
      rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
      · exact absurd hpq (F.irrefl)
      · exact hB
      · exact hB.symm
      · exact absurd hpq (F.irrefl)
    exact hfix _ _ hG' hEA hEB

/-- **Definition 12.** An `(H, F)`-lower bound graph is `δ`-sparse if there is a partition
`(A, B)` of `V'` (here `A = {v | inA v}`) with `V_A ⊆ A`, `V_B ⊆ B`, and at most `δ · |V'|` edges of
`G'` between `A` and `B`. -/
def IsSparse [Fintype V] [DecidableRel G'.Adj] (δ : ℝ) : Prop :=
  ∃ inA : V → Bool, (∀ a, inA (L.φA a) = true) ∧ (∀ b, inA (L.φB b) = false) ∧
    ((Finset.univ.filter fun p : V × V => inA p.1 = true ∧ inA p.2 = false ∧ G'.Adj p.1 p.2).card
      : ℝ) ≤ δ * Fintype.card V

end LowerBoundGraph

end Podc.CongestedCliquePower
