import Cslib.Foundations.Combinatorics.SimpleGraph.Minor
import Mathlib

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/Depth1Minor.lean

/-!
# Depth-1 minors (star contractions)

A graph `H` is a *depth-1 minor* of `G` if it is obtained from a subgraph of `G` by contracting
pairwise disjoint stars (shallow minors of depth 1, the `r = 1` level of bounded expansion).
Staged for Amiri–Schmid–Siebertz (PODC 2016, `Papers/PODC2016/BoundedGenusMDS/`).

## Main definitions

* `SimpleGraph.Depth1Model H G`: branch sets that are pairwise disjoint stars (with centers), and
  every edge of `H` is realized by an edge of `G` between the two branch sets.
* `SimpleGraph.IsDepth1Minor H G`.
* `SimpleGraph.Depth1DensityLE G c`: every finite depth-1 minor `H` has `|E(H)| ≤ c · |V(H)|`
  (i.e. `∇₁(G) ≤ c`).
* `SimpleGraph.ExcludesKt3 G t`: `K_{t,3}` is not a depth-1 minor of `G`.

## Main results

* `SimpleGraph.Depth1DensityLE.card_le_of_touch`: a family of pairwise disjoint stars has at most
  `2c · |I|` ordered pairs of distinct touching stars; `card_le_of_adj`: at most `2c|S|` ordered
  adjacent pairs inside a vertex set `S`.
* `SimpleGraph.ExcludesKt3.card_lt`, `card_lt_two_singletons`: fewer than `t` vertices outside
  three disjoint stars see all three of them.
* `SimpleGraph.Depth1Model.toMinorModel`, `SimpleGraph.MinorDensityLE.depth1DensityLE`: depth-1
  minors are minors, so CSLib's minor density bounds the depth-1 density.
* `SimpleGraph.depth1_of_cover_two`: a graph with a vertex cover of size two has
  `Depth1DensityLE G 2` and excludes `K_{3,3}` as a depth-1 minor (handy for small examples).
-/

open Finset

namespace SimpleGraph

variable {W : Type*}

section Defs

variable {V : Type*}

/-- A depth-1 minor model of `H` in `G`: every vertex `w` of `H` is
represented by a star `branch w` with center `center w` (every other vertex of the branch is
adjacent to the center), the branches are pairwise disjoint, and every edge of `H` is realized by
an edge of `G` between the two branches. -/
structure Depth1Model (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch set (a star) of a vertex of `H`. -/
  branch : W → Set V
  /-- The center of the star. -/
  center : W → V
  center_mem : ∀ w, center w ∈ branch w
  adj_center : ∀ w, ∀ x ∈ branch w, x ≠ center w → G.Adj (center w) x
  disjoint : ∀ w w', w ≠ w' → Disjoint (branch w) (branch w')
  edge : ∀ w w', H.Adj w w' → ∃ x ∈ branch w, ∃ y ∈ branch w', G.Adj x y

/-- `H` is a depth-1 minor of `G`: it is obtained from a subgraph of `G` by star contractions. -/
def IsDepth1Minor (H : SimpleGraph W) (G : SimpleGraph V) : Prop := Nonempty (Depth1Model H G)

/-- All depth-1 minors `H` of `G` have edge density `ε(H) = |E(H)|/|V(H)| ≤ c`
(the depth-1 density `∇₁(G) ≤ c`). -/
def Depth1DensityLE (G : SimpleGraph V) (c : ℕ) : Prop :=
  ∀ (W : Type) [Finite W] (H : SimpleGraph W), IsDepth1Minor H G →
    H.edgeSet.ncard ≤ c * Nat.card W

/-- `G` excludes `K_{t,3}` as a depth-1 minor . -/
def ExcludesKt3 (G : SimpleGraph V) (t : ℕ) : Prop :=
  ¬ IsDepth1Minor (completeBipartiteGraph (Fin t) (Fin 3)) G

end Defs

/-! ### Counting tools -/

section Tools

open Classical

variable {V : Type} {G : SimpleGraph V}

/-- A finite family of pairwise disjoint stars of a graph with `Depth1DensityLE G c` has at most
`2c · |I|` ordered pairs of distinct touching stars (the contracted depth-1 minor has at most
`c|I|` edges). -/
theorem Depth1DensityLE.card_touch_le {c : ℕ} (hG : Depth1DensityLE G c) {ι : Type}
    (I : Finset ι) (ctr : ι → V) (br : ι → Finset V) (hctr : ∀ i ∈ I, ctr i ∈ br i)
    (hstar : ∀ i ∈ I, ∀ x ∈ br i, x ≠ ctr i → G.Adj (ctr i) x)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (br i) (br j)) :
    ((I ×ˢ I).filter fun p => p.1 ≠ p.2 ∧ ∃ x ∈ br p.1, ∃ y ∈ br p.2, G.Adj x y).card
      ≤ 2 * c * I.card := by
  set T : ι → ι → Prop := fun i j => i ≠ j ∧ ∃ x ∈ br i, ∃ y ∈ br j, G.Adj x y with hT
  let H : SimpleGraph I :=
    { Adj := fun a b => T a.1 b.1
      symm := ⟨fun a b ⟨hne, x, hx, y, hy, hxy⟩ => ⟨Ne.symm hne, y, hy, x, hx, hxy.symm⟩⟩
      loopless := ⟨fun a h => h.1 rfl⟩ }
  have hmodel : IsDepth1Minor H G :=
    ⟨{ branch := fun a => (br a.1 : Set V)
       center := fun a => ctr a.1
       center_mem := fun a => hctr a.1 a.2
       adj_center := fun a x hx hne => hstar a.1 a.2 x hx hne
       disjoint := fun a b hab => by
         rw [Finset.disjoint_coe]
         exact hdisj a.1 a.2 b.1 b.2 (fun h => hab (Subtype.ext h))
       edge := fun a b h => by
         obtain ⟨_, x, hx, y, hy, hxy⟩ := h
         exact ⟨x, hx, y, hy, hxy⟩ }⟩
  have hE := hG I H hmodel
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hE
  -- `2|E(H)| = Σ deg = #ordered adjacent pairs`
  have h2 : ∑ a : I, H.degree a = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  have hcardE : H.edgeFinset.card = H.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  have hsum : ((I ×ˢ I).filter fun p => T p.1 p.2).card = ∑ a : I, H.degree a := by
    rw [card_filter, sum_product, ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    symm
    rw [← card_filter]
    -- both sides count the `b ∈ I` with `T a b`
    refine Finset.card_bij (fun b _ => b.1) ?_ ?_ ?_
    · intro b hb
      simp only [SimpleGraph.mem_neighborFinset] at hb
      simp only [mem_filter]
      exact ⟨b.2, hb⟩
    · intro b _ b' _ h; exact Subtype.ext h
    · intro y hy
      simp only [mem_filter] at hy
      exact ⟨⟨y, hy.1⟩, by simpa [SimpleGraph.mem_neighborFinset] using hy.2, rfl⟩
  show ((I ×ˢ I).filter fun p => T p.1 p.2).card ≤ 2 * c * I.card
  rw [hsum, h2, hcardE]
  nlinarith

/-- Instance-robust form of `card_touch_le`: any finset of ordered pairs of distinct touching
stars has at most `2c|I|` elements. -/
theorem Depth1DensityLE.card_le_of_touch {c : ℕ} (hG : Depth1DensityLE G c) {ι : Type}
    (I : Finset ι) (ctr : ι → V) (br : ι → Finset V) (hctr : ∀ i ∈ I, ctr i ∈ br i)
    (hstar : ∀ i ∈ I, ∀ x ∈ br i, x ≠ ctr i → G.Adj (ctr i) x)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (br i) (br j)) (P : Finset (ι × ι))
    (hP : ∀ p ∈ P, p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≠ p.2 ∧ ∃ x ∈ br p.1, ∃ y ∈ br p.2, G.Adj x y) :
    P.card ≤ 2 * c * I.card := by
  refine le_trans (card_le_card fun p hp => ?_) (hG.card_touch_le I ctr br hctr hstar hdisj)
  obtain ⟨h1, h2, h3⟩ := hP p hp
  exact mem_filter.2 ⟨mem_product.2 ⟨h1, h2⟩, h3⟩

/-- Instance-robust form of `card_adj_le`. -/
theorem Depth1DensityLE.card_le_of_adj {c : ℕ} (hG : Depth1DensityLE G c) [Fintype V]
    (S : Finset V) (Q : Finset (V × V)) (hQ : ∀ p ∈ Q, p.1 ∈ S ∧ p.2 ∈ S ∧ G.Adj p.1 p.2) :
    Q.card ≤ 2 * c * S.card := by
  refine hG.card_le_of_touch S id (fun v => {v}) (by simp) (by simp)
    (by intro i _ j _ h; simpa using h) Q fun p hp => ?_
  obtain ⟨h1, h2, h3⟩ := hQ p hp
  exact ⟨h1, h2, h3.ne, p.1, by simp, p.2, by simp, h3⟩

/-- Singleton stars: a graph with `Depth1DensityLE G c` has at most `2c|S|` ordered adjacent pairs
inside any vertex set `S` (subgraphs are depth-1 minors). -/
theorem Depth1DensityLE.card_adj_le {c : ℕ} (hG : Depth1DensityLE G c) [Fintype V]
    (S : Finset V) :
    ((S ×ˢ S).filter fun p => G.Adj p.1 p.2).card ≤ 2 * c * S.card := by
  have := hG.card_touch_le S id (fun v => {v}) (by simp) (by simp) (by
    intro i _ j _ h; simpa using h)
  refine le_trans (le_of_eq ?_) this
  congr 1
  ext p
  simp only [mem_filter, mem_product, mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.ne, h2⟩
  · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩

/-- If `G` excludes `K_{t,3}` as a depth-1 minor, then for three pairwise disjoint stars
`S 0, S 1, S 2` (centers `z k`), fewer than `t` vertices outside the stars have a neighbour in each
of the three stars. -/
theorem ExcludesKt3.card_lt {t : ℕ} (ht : ExcludesKt3 G t) (S : Fin 3 → Finset V)
    (z : Fin 3 → V) (hz : ∀ k, z k ∈ S k) (hS : ∀ k, ∀ x ∈ S k, x ≠ z k → G.Adj (z k) x)
    (hdisj : ∀ k l, k ≠ l → Disjoint (S k) (S l)) (U : Finset V)
    (hU : ∀ u ∈ U, ∀ k, u ∉ S k) (hadj : ∀ u ∈ U, ∀ k, ∃ y ∈ S k, G.Adj u y) :
    U.card < t := by
  by_contra hlt
  push Not at hlt
  obtain ⟨U', hU'U, hU'⟩ := Finset.exists_subset_card_eq hlt
  let e : Fin t ≃ U' := (U'.equivFin.trans (finCongr hU')).symm
  apply ht
  refine ⟨{ branch := Sum.elim (fun i => {(e i).1}) (fun k => (S k : Set V))
            center := Sum.elim (fun i => (e i).1) z
            center_mem := ?_
            adj_center := ?_
            disjoint := ?_
            edge := ?_ }⟩
  · rintro (i | k)
    · simp
    · simpa using hz k
  · rintro (i | k) x hx hne
    · simp at hx; exact absurd hx hne
    · exact hS k x hx hne
  · rintro (i | k) (i' | k') hne
    · simp only [Sum.elim_inl, Set.disjoint_singleton]
      intro h; apply hne; congr 1; exact e.injective (Subtype.ext h)
    · simp only [Sum.elim_inl, Sum.elim_inr, Set.disjoint_singleton_left, Finset.mem_coe]
      exact hU _ (hU'U (e i).2) k'
    · simp only [Sum.elim_inl, Sum.elim_inr, Set.disjoint_singleton_right, Finset.mem_coe]
      exact hU _ (hU'U (e i').2) k
    · simp only [Sum.elim_inr, Finset.disjoint_coe]
      exact hdisj k k' (fun h => hne (by rw [h]))
  · rintro (i | k) (i' | k') h
    · simp at h
    · obtain ⟨y, hy, hadj'⟩ := hadj _ (hU'U (e i).2) k'
      exact ⟨(e i).1, by simp, y, by simpa using hy, hadj'⟩
    · obtain ⟨y, hy, hadj'⟩ := hadj _ (hU'U (e i').2) k
      exact ⟨y, by simpa using hy, (e i').1, by simp, hadj'.symm⟩
    · simp at h

/-- Specialization of `ExcludesKt3.card_lt` to two singleton branch sets `{a}`, `{b}` and one star
`S` with center `z`. -/
theorem ExcludesKt3.card_lt_two_singletons {t : ℕ} (ht : ExcludesKt3 G t) {a b z : V}
    {S : Finset V} (hab : a ≠ b) (haS : a ∉ S) (hbS : b ∉ S) (hz : z ∈ S)
    (hS : ∀ x ∈ S, x ≠ z → G.Adj z x) (U : Finset V)
    (hU : ∀ u ∈ U, u ≠ a ∧ u ≠ b ∧ u ∉ S)
    (hadj : ∀ u ∈ U, G.Adj u a ∧ G.Adj u b ∧ ∃ y ∈ S, G.Adj u y) : U.card < t := by
  refine ht.card_lt ![{a}, {b}, S] ![a, b, z] ?_ ?_ ?_ U ?_ ?_
  · intro k; fin_cases k <;> simp [hz]
  · intro k x hx hne; fin_cases k
    · simp at hx; exact absurd hx hne
    · simp at hx; exact absurd hx hne
    · exact hS x hx hne
  · intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all [Finset.disjoint_singleton_left, Ne.symm hab]
  · intro u hu k; obtain ⟨h1, h2, h3⟩ := hU u hu
    fin_cases k <;> simp [h1, h2, h3]
  · intro u hu k; obtain ⟨h1, h2, h3⟩ := hadj u hu
    fin_cases k
    · exact ⟨a, by simp, h1⟩
    · exact ⟨b, by simp, h2⟩
    · exact h3

end Tools

/-! ### Depth-1 minors are minors -/

section Bridge

variable {V : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- A star induces a connected subgraph. -/
lemma induce_connected_of_star {s : Set V} {z : V} (hz : z ∈ s)
    (hs : ∀ x ∈ s, x ≠ z → G.Adj z x) : (G.induce s).Connected := by
  have hreach : ∀ x : s, (G.induce s).Reachable x ⟨z, hz⟩ := by
    intro x
    by_cases hx : (x : V) = z
    · have : x = ⟨z, hz⟩ := Subtype.ext hx
      exact this ▸ Reachable.refl _
    · exact (SimpleGraph.Adj.reachable (by simpa using (hs x x.2 hx).symm))
  have : Nonempty s := ⟨⟨z, hz⟩⟩
  exact ⟨fun x y => (hreach x).trans (hreach y).symm⟩

/-- A depth-1 minor model is a minor model. -/
def Depth1Model.toMinorModel (μ : Depth1Model H G) : MinorModel H G where
  branch := μ.branch
  connected w := induce_connected_of_star (μ.center_mem w) (μ.adj_center w)
  disjoint a b h := μ.disjoint a b h
  adj := μ.edge

lemma IsDepth1Minor.isMinor (h : IsDepth1Minor H G) : IsMinor H G := ⟨h.some.toMinorModel⟩

/-- A bound on the minor density bounds the depth-1 density. -/
theorem MinorDensityLE.depth1DensityLE {δ : ℝ} {c : ℕ} (hG : G.MinorDensityLE δ)
    (hδ : δ ≤ c) : Depth1DensityLE G c := by
  intro W _ H hH
  have h := hG W H hH.isMinor
  have : (H.edgeSet.ncard : ℝ) ≤ c * Nat.card W :=
    h.trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _))
  exact_mod_cast this

end Bridge

section Cover

variable {V : Type*} {G : SimpleGraph V}

/-- If every edge of `G` has an endpoint in `{p, q}`, then in every depth-1 minor model the
branch sets meeting `{p, q}` form a vertex cover of `H` with at most two vertices. -/
lemma depth1Model_cover_two [Finite W] {p q : V}
    (hpq : ∀ x y, G.Adj x y → x = p ∨ x = q ∨ y = p ∨ y = q) {H : SimpleGraph W} (μ : Depth1Model H G) :
    let Sp : Set W := {w | p ∈ μ.branch w ∨ q ∈ μ.branch w}
    Sp.ncard ≤ 2 ∧ ∀ w w', H.Adj w w' → w ∈ Sp ∨ w' ∈ Sp := by
  intro Sp
  constructor
  · have h1 : {w | p ∈ μ.branch w}.Subsingleton := fun w hw w' hw' => by
      by_contra h; exact Set.disjoint_left.1 (μ.disjoint w w' h) hw hw'
    have h2 : {w | q ∈ μ.branch w}.Subsingleton := fun w hw w' hw' => by
      by_contra h; exact Set.disjoint_left.1 (μ.disjoint w w' h) hw hw'
    calc Sp.ncard = ({w | p ∈ μ.branch w} ∪ {w | q ∈ μ.branch w}).ncard := rfl
      _ ≤ {w | p ∈ μ.branch w}.ncard + {w | q ∈ μ.branch w}.ncard := Set.ncard_union_le _ _
      _ ≤ 1 + 1 := Nat.add_le_add ((Set.ncard_le_one_iff (Set.toFinite _)).2 fun ha hb => h1 ha hb)
          ((Set.ncard_le_one_iff (Set.toFinite _)).2 fun ha hb => h2 ha hb)
  · intro w w' h
    obtain ⟨x, hx, y, hy, hxy⟩ := μ.edge w w' h
    rcases hpq x y hxy with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr hy)

/-- A graph with a vertex cover `{p, q}` has all depth-1 minors of density at most `2` and
excludes `K_{3,3}` as a depth-1 minor. -/
theorem depth1_of_cover_two {p q : V} (hpq : ∀ x y, G.Adj x y → x = p ∨ x = q ∨ y = p ∨ y = q) :
    Depth1DensityLE G 2 ∧ ExcludesKt3 G 3 := by
  constructor
  · intro W _ H ⟨μ⟩
    obtain ⟨hSp, hcov⟩ := depth1Model_cover_two hpq μ
    set Sp : Set W := {w | p ∈ μ.branch w ∨ q ∈ μ.branch w}
    have hsub : H.edgeSet ⊆ (fun r : W × W => s(r.1, r.2)) '' (Sp ×ˢ Set.univ) := by
      intro e he
      induction e using Sym2.ind with
      | h w w' =>
        rw [SimpleGraph.mem_edgeSet] at he
        rcases hcov w w' he with h | h
        · exact ⟨(w, w'), ⟨h, trivial⟩, rfl⟩
        · exact ⟨(w', w), ⟨h, trivial⟩, Sym2.eq_swap⟩
    calc H.edgeSet.ncard ≤ ((fun r : W × W => s(r.1, r.2)) '' (Sp ×ˢ Set.univ)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (Sp ×ˢ (Set.univ : Set W)).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = Sp.ncard * Nat.card W := by rw [Set.ncard_prod, Set.ncard_univ]
      _ ≤ 2 * Nat.card W := Nat.mul_le_mul_right _ hSp
  · rintro ⟨μ⟩
    obtain ⟨hSp, hcov⟩ := depth1Model_cover_two hpq μ
    set Sp : Set (Fin 3 ⊕ Fin 3) := {w | p ∈ μ.branch w ∨ q ∈ μ.branch w}
    -- some vertex `inl i` lies outside the cover; then its three neighbours lie in the cover
    have hfin : Sp.Finite := Set.toFinite _
    by_cases hall : ∀ i : Fin 3, Sum.inl i ∈ Sp
    · have : (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ Fin 3)) ⊆ Sp := by
        rintro _ ⟨i, rfl⟩; exact hall i
      have h3 := Set.ncard_le_ncard this hfin
      rw [Set.ncard_range_of_injective Sum.inl_injective] at h3
      simp at h3; omega
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      have : (Set.range (Sum.inr : Fin 3 → Fin 3 ⊕ Fin 3)) ⊆ Sp := by
        rintro _ ⟨k, rfl⟩
        rcases hcov (Sum.inl i) (Sum.inr k) (by simp) with h | h
        · exact absurd h hi
        · exact h
      have h3 := Set.ncard_le_ncard this hfin
      rw [Set.ncard_range_of_injective Sum.inr_injective] at h3
      simp at h3; omega

end Cover

end SimpleGraph
