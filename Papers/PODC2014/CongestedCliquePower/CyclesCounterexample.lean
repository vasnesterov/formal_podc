import Papers.PODC2014.CongestedCliquePower.CyclesLemma18

/-!
# Lemma 18 of Drucker–Kuhn–Oshman (PODC 2014) is false as stated

For odd `ℓ` the proof of Lemma 18 takes `F = K_{N/2,N/2}`, claiming `ex(N, C_ℓ) = N²/4`. This
holds only for `N` large enough. Smallest failure: `ℓ = 5`, `N = 4`. Every graph on `4 < 5`
vertices is `C₅`-free, so the only extremal `C₅`-free graph on `4` vertices is `K₄`
(`eq_top_of_isExtremal`), and there is **no** `(C₅, K₄)`-lower bound graph on any vertex set
(`no_lowerBoundGraph_C5_K4`):

* for an edge `{u, v}` of `K₄`, the copy of `C₅` given by condition I has exactly four vertices
  `A_u, A_v, B_u, B_v` in `V_A ∪ V_B`; going around the cycle, two of them that are consecutive lie
  on different sides, so `G'` has an edge `A_x B_y` with `x, y ∈ {u, v}` (`exists_cross_edge`);
* doing this for the disjoint edges `{0, 1}` and `{2, 3}` gives edges `A_x B_y` and `A_p B_q`, and
  then `A_x – A_z – A_p – B_q – B_y – A_x` (`z ∉ {x, p}`) is a copy of `C₅` with three vertices in
  `V_A`, contradicting condition II (which allows exactly two).

Hence `lemma_18_false : ¬ Lemma18Concl 5 4 n` for every `n` (in particular `n ≥ ℓ · N/2 = 10`),
and `not_lemma18Statement`.
-/

namespace Podc.CongestedCliquePower

open SimpleGraph
open scoped Finset

/-- `K₄` is `C₅`-free (it has only four vertices). -/
lemma top_fin4_free : (cycleGraph 5).Free (⊤ : SimpleGraph (Fin 4)) := by
  rintro ⟨f⟩
  have := Fintype.card_le_of_injective f f.injective
  simp at this

/-- `K₄` is an extremal `C₅`-free graph on `4` vertices. -/
lemma isExtremal_top_fin4 : (⊤ : SimpleGraph (Fin 4)).IsExtremal (cycleGraph 5).Free :=
  ⟨top_fin4_free, fun _ _ _ => Finset.card_le_card (edgeFinset_subset_edgeFinset.2 le_top)⟩

/-- `K₄` is the only extremal `C₅`-free graph on `4` vertices. -/
lemma eq_top_of_isExtremal (F : SimpleGraph (Fin 4)) [DecidableRel F.Adj]
    (h : F.IsExtremal (cycleGraph 5).Free) : F = ⊤ :=
  (h.le_iff_eq top_fin4_free).1 le_top

section

variable {V : Type*} {G' : SimpleGraph V} {VF : Type*} {F : SimpleGraph VF} {ℓ : ℕ}

/-- In a copy of `H` satisfying (b), (c) for `{u, v}`, the only vertices of `V_A` are `A_u, A_v`. -/
lemma LBData.Fits.mem_A {D : LBData (cycleGraph ℓ) F G'} {f : (cycleGraph ℓ).Copy G'} {u v : VF}
    (h : D.Fits f u v) {a : VF} (ha : D.φA a ∈ Set.range f) : a = u ∨ a = v := by
  rcases (h.2.2.2 (D.φA a)).1 ⟨ha, Or.inl ⟨a, rfl⟩⟩ with h | h | h | h
  · exact Or.inl (D.φA.injective h)
  · exact Or.inr (D.φA.injective h)
  · exact absurd h (D.disjoint a u)
  · exact absurd h (D.disjoint a v)

end

/-- Four distinct positions on a `5`-cycle, two labelled `A` and two labelled `B`: some `A` and
some `B` are consecutive. -/
lemma cycle5_cross : ∀ a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    (cycleGraph 5).Adj a c ∨ (cycleGraph 5).Adj a d ∨ (cycleGraph 5).Adj b c ∨
      (cycleGraph 5).Adj b d := by
  decide

variable {V : Type*} {G' : SimpleGraph V} (L : LowerBoundGraph (cycleGraph 5) (⊤ : SimpleGraph (Fin 4)) G')

/-- Condition I for the edge `{u, v}` forces a direct edge `A_x B_y`, `x, y ∈ {u, v}`. -/
lemma exists_cross_edge {u v : Fin 4} (huv : u ≠ v) :
    ∃ x y, (x = u ∨ x = v) ∧ (y = u ∨ y = v) ∧ G'.Adj (L.φA x) (L.φB y) := by
  obtain ⟨f, -, -, -, hc⟩ := L.exists_copy u v ((top_adj u v).2 huv)
  obtain ⟨⟨a, ha⟩, -⟩ := (hc (L.φA u)).2 (Or.inl rfl)
  obtain ⟨⟨b, hb⟩, -⟩ := (hc (L.φA v)).2 (Or.inr (Or.inl rfl))
  obtain ⟨⟨c, hc'⟩, -⟩ := (hc (L.φB u)).2 (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨⟨d, hd⟩, -⟩ := (hc (L.φB v)).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hAB : ∀ s t, L.φA s ≠ L.φB t := L.disjoint
  have hAi : L.φA u ≠ L.φA v := fun h => huv (L.φA.injective h)
  have hBi : L.φB u ≠ L.φB v := fun h => huv (L.φB.injective h)
  have ne : ∀ {s t : Fin 5} {p q : V}, f s = p → f t = q → p ≠ q → s ≠ t := by
    rintro s t p q rfl rfl hpq rfl
    exact hpq rfl
  have adj : ∀ {s t : Fin 5}, (cycleGraph 5).Adj s t → G'.Adj (f s) (f t) :=
    fun h => f.toHom.map_adj h
  rcases cycle5_cross a b c d (ne ha hb hAi) (ne ha hc' (hAB _ _)) (ne ha hd (hAB _ _))
      (ne hb hc' (hAB _ _)) (ne hb hd (hAB _ _)) (ne hc' hd hBi) with h | h | h | h
  · exact ⟨u, u, Or.inl rfl, Or.inl rfl, ha ▸ hc' ▸ adj h⟩
  · exact ⟨u, v, Or.inl rfl, Or.inr rfl, ha ▸ hd ▸ adj h⟩
  · exact ⟨v, u, Or.inr rfl, Or.inl rfl, hb ▸ hc' ▸ adj h⟩
  · exact ⟨v, v, Or.inr rfl, Or.inr rfl, hb ▸ hd ▸ adj h⟩

/-- Two cross edges `A_x B_y`, `A_p B_q` close a `5`-cycle `A_x A_z A_p B_q B_y` with three vertices
in `V_A`, contradicting condition II. -/
lemma false_of_cross_edges (x z p q y : Fin 4) (hxz : x ≠ z) (hzp : z ≠ p) (hxp : x ≠ p)
    (hqy : q ≠ y) (h1 : G'.Adj (L.φA p) (L.φB q)) (h2 : G'.Adj (L.φA x) (L.φB y)) : False := by
  let w : Fin 5 → V := ![L.φA x, L.φA z, L.φA p, L.φB q, L.φB y]
  have hA : ∀ s t : Fin 4, s ≠ t → G'.Adj (L.φA s) (L.φA t) :=
    fun s t h => L.φA.toHom.map_adj ((top_adj s t).2 h)
  have hB : ∀ s t : Fin 4, s ≠ t → G'.Adj (L.φB s) (L.φB t) :=
    fun s t h => L.φB.toHom.map_adj ((top_adj s t).2 h)
  have hstep : ∀ k : Fin 5, G'.Adj (w k) (w (k + 1)) := by
    intro k
    fin_cases k
    · exact hA _ _ hxz
    · exact hA _ _ hzp
    · exact h1
    · exact hB _ _ hqy
    · exact h2.symm
  have hcyc : ∀ s t : Fin 5, (cycleGraph 5).Adj s t → t = s + 1 ∨ s = t + 1 := by decide
  have hAinj := L.φA.injective
  have hBinj := L.φB.injective
  have hAB : ∀ s t, L.φA s ≠ L.φB t := L.disjoint
  have hinj : Function.Injective w := by
    intro s t h
    fin_cases s <;> fin_cases t <;>
      first
      | rfl
      | (exfalso; simp only [w] at h
         first
         | exact hxz (hAinj h) | exact hxz (hAinj h).symm
         | exact hzp (hAinj h) | exact hzp (hAinj h).symm
         | exact hxp (hAinj h) | exact hxp (hAinj h).symm
         | exact hqy (hBinj h) | exact hqy (hBinj h).symm
         | exact hAB _ _ h | exact hAB _ _ h.symm)
  let g : (cycleGraph 5).Copy G' :=
    ⟨⟨w, fun {s t} h => by
      rcases hcyc s t h with rfl | rfl
      · exact hstep s
      · exact (hstep t).symm⟩, hinj⟩
  obtain ⟨u, v, hfit⟩ := L.fits_of_copy g
  have m0 := hfit.mem_A (a := x) ⟨0, rfl⟩
  have m1 := hfit.mem_A (a := z) ⟨1, rfl⟩
  have m2 := hfit.mem_A (a := p) ⟨2, rfl⟩
  rcases m0 with rfl | rfl <;> rcases m1 with rfl | rfl <;> rcases m2 with rfl | rfl <;>
    simp_all

/-- **There is no `(C₅, K₄)`-lower bound graph**, on any vertex set. -/
theorem no_lowerBoundGraph_C5_K4 (V : Type*) (G' : SimpleGraph V) :
    IsEmpty (LowerBoundGraph (cycleGraph 5) (⊤ : SimpleGraph (Fin 4)) G') := by
  refine ⟨fun L => ?_⟩
  obtain ⟨x, y, hx, hy, h2⟩ := exists_cross_edge L (u := 0) (v := 1) (by decide)
  obtain ⟨p, q, hp, hq, h1⟩ := exists_cross_edge L (u := 2) (v := 3) (by decide)
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hp with rfl | rfl <;>
    rcases hq with rfl | rfl <;>
    first
    | exact false_of_cross_edges L 0 1 _ _ _ (by decide) (by decide) (by decide) (by decide) h1 h2
    | exact false_of_cross_edges L 1 0 _ _ _ (by decide) (by decide) (by decide) (by decide) h1 h2

/-- **Lemma 18 is false** for `ℓ = 5`, `N = 4` and every `n` (in particular for `n ≥ ℓ · N/2`). -/
theorem lemma_18_false (n : ℕ) : ¬ Lemma18Concl 5 4 n := by
  rintro ⟨F, hdec, hext, G', ⟨L⟩⟩
  obtain rfl := eq_top_of_isExtremal F hext
  exact (no_lowerBoundGraph_C5_K4 (Fin n) G').false L

/-- The paper's Lemma 18 (`Lemma18Statement`) does not hold. -/
theorem not_lemma18Statement : ¬ Lemma18Statement := fun h =>
  lemma_18_false 10 (h 5 4 10 (by norm_num) (by decide) (by norm_num))

end Podc.CongestedCliquePower
