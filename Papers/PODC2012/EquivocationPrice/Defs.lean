import Mathlib

/-!
# Definitions: f-tolerance, h-disjointness, the numbers `Tₙ(h)` and `Uₙ(h)`

Jaffe, Moscibroda, Sen, *On the Price of Equivocation in Byzantine Agreement*, PODC 2012.

A system of `n` processors with 3-processor partial broadcast channels is a 3-uniform hypergraph
on the processors. We represent a hypergraph on a finite vertex type `V` by its edge set
`E : Finset (Finset V)`; it is 3-uniform (`Uniform3 E`) when every edge has three vertices. The
paper writes a hyperedge as a triple `(x, y, z)`; here it is the set `{x, y, z}` (the vertices
are always distinct where the paper uses it, since they come from disjoint sets).

* `Rainbow E A B C`: some hyperedge has one vertex in each of `A`, `B`, `C` (trichromatic edge).
* `FTolerant E f`: Definition 1 (`f`-tolerance).
* `HDisjoint E h`: Definition 2 (`h`-disjointness), with `n = Fintype.card V`; the size
  condition `|A| + |B| + |C| ≥ (n + 3h)/2` is written `n + 3h ≤ 2(|A| + |B| + |C|)`.
* `crossing A B C`: the triples `{x, y, z}` with `x ∈ A, y ∈ B, z ∈ C` (`|A||B||C|` of them when
  the sets are disjoint, `card_crossing`); `Rainbow E A B C ↔ ¬ Disjoint E (crossing A B C)`.
* `T n h`, `U n h`: Definitions 3 and 7 (minimum number of hyperedges of an `h`-disjoint
  hypergraph; minimum number of hyperedges forcing `h`-disjointness), on the vertex type `Fin n`.
-/

namespace Podc.EquivocationPrice

variable {V : Type*} [DecidableEq V]

/-- A hypergraph (given by its edge set) is 3-uniform if every edge has exactly three vertices. -/
def Uniform3 (E : Finset (Finset V)) : Prop := ∀ e ∈ E, e.card = 3

/-- Some hyperedge of `E` is trichromatic for the (partial) colouring `A, B, C`:
`∃ x ∈ A, y ∈ B, z ∈ C, (x, y, z) ∈ E`. -/
def Rainbow (E : Finset (Finset V)) (A B C : Finset V) : Prop :=
  ∃ x ∈ A, ∃ y ∈ B, ∃ z ∈ C, ({x, y, z} : Finset V) ∈ E

variable [Fintype V]

/-- **Definition 1** (`f`-tolerance). For all vertex sets `S ≠ T` and `Z` with `|Z| ≤ f`,
`|S|, |T| ≥ n - f` and `S ∩ T ⊆ Z ⊂ S ∪ T` there are `x ∈ S \ Z`, `y ∈ T \ Z`, `z ∈ S ∩ T` with
`(x, y, z) ∈ E`. (`Z ⊂ S ∪ T` is strict, as in the paper; `|S| ≥ n - f` is written
`n ≤ |S| + f`.) -/
def FTolerant (E : Finset (Finset V)) (f : ℕ) : Prop :=
  ∀ S T Z : Finset V, S ≠ T → Z.card ≤ f → Fintype.card V ≤ S.card + f →
    Fintype.card V ≤ T.card + f → S ∩ T ⊆ Z → Z ⊂ S ∪ T →
    ∃ x ∈ S \ Z, ∃ y ∈ T \ Z, ∃ z ∈ S ∩ T, ({x, y, z} : Finset V) ∈ E

/-- The colourings quantified over in Definition 2: pairwise disjoint `A, B, C` with
`|A|, |B|, |C| ≥ h` and `|A| + |B| + |C| ≥ (n + 3h)/2`. -/
def ValidColoring (h : ℕ) (A B C : Finset V) : Prop :=
  Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ h ≤ A.card ∧ h ≤ B.card ∧ h ≤ C.card ∧
    Fintype.card V + 3 * h ≤ 2 * (A.card + B.card + C.card)

/-- **Definition 2** (`h`-disjointness). Every valid partial colouring `A, B, C` has a
trichromatic hyperedge. -/
def HDisjoint (E : Finset (Finset V)) (h : ℕ) : Prop :=
  ∀ A B C : Finset V, ValidColoring h A B C → Rainbow E A B C

/-! ### Basic facts: symmetry, crossing triples -/

omit [Fintype V] in
/-- `Rainbow` is symmetric in its three colour classes. -/
theorem rainbow_swap12 {E : Finset (Finset V)} {A B C : Finset V} :
    Rainbow E A B C → Rainbow E B A C := by
  rintro ⟨x, hx, y, hy, z, hz, he⟩
  exact ⟨y, hy, x, hx, z, hz, by rwa [Finset.insert_comm]⟩

omit [Fintype V] in
theorem rainbow_swap23 {E : Finset (Finset V)} {A B C : Finset V} :
    Rainbow E A B C → Rainbow E A C B := by
  rintro ⟨x, hx, y, hy, z, hz, he⟩
  exact ⟨x, hx, z, hz, y, hy, by rwa [Finset.pair_comm]⟩

omit [DecidableEq V] in
theorem validColoring_swap12 {h : ℕ} {A B C : Finset V} :
    ValidColoring h A B C → ValidColoring h B A C := by
  rintro ⟨hAB, hAC, hBC, ha, hb, hc, hs⟩
  exact ⟨hAB.symm, hBC, hAC, hb, ha, hc, by omega⟩

omit [DecidableEq V] in
theorem validColoring_swap23 {h : ℕ} {A B C : Finset V} :
    ValidColoring h A B C → ValidColoring h A C B := by
  rintro ⟨hAB, hAC, hBC, ha, hb, hc, hs⟩
  exact ⟨hAC, hAB, hBC.symm, ha, hc, hb, by omega⟩

/-- The triples crossing `A, B, C`: all `{x, y, z}` with `x ∈ A, y ∈ B, z ∈ C`. -/
def crossing (A B C : Finset V) : Finset (Finset V) :=
  (A ×ˢ B ×ˢ C).image fun p => ({p.1, p.2.1, p.2.2} : Finset V)

omit [Fintype V] in
theorem mem_crossing {A B C : Finset V} {e : Finset V} :
    e ∈ crossing A B C ↔ ∃ x ∈ A, ∃ y ∈ B, ∃ z ∈ C, ({x, y, z} : Finset V) = e := by
  simp [crossing, and_assoc]

omit [Fintype V] in
theorem rainbow_iff {E : Finset (Finset V)} {A B C : Finset V} :
    Rainbow E A B C ↔ ¬ Disjoint E (crossing A B C) := by
  rw [Finset.not_disjoint_iff]
  constructor
  · rintro ⟨x, hx, y, hy, z, hz, he⟩
    exact ⟨_, he, mem_crossing.2 ⟨x, hx, y, hy, z, hz, rfl⟩⟩
  · rintro ⟨e, he, hc⟩
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := mem_crossing.1 hc
    exact ⟨x, hx, y, hy, z, hz, he⟩

omit [Fintype V] in
theorem card_crossing {A B C : Finset V} (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) : (crossing A B C).card = A.card * B.card * C.card := by
  rw [crossing, Finset.card_image_of_injOn, Finset.card_product, Finset.card_product, mul_assoc]
  rintro ⟨x, y, z⟩ hp ⟨x', y', z'⟩ hp' he
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
  simp only at he
  obtain ⟨hx, hy, hz⟩ := hp
  obtain ⟨hx', hy', hz'⟩ := hp'
  have nAB := Finset.disjoint_left.1 hAB
  have nAC := Finset.disjoint_left.1 hAC
  have nBC := Finset.disjoint_left.1 hBC
  have mx : x ∈ ({x', y', z'} : Finset V) := he ▸ by simp
  have my : y ∈ ({x', y', z'} : Finset V) := he ▸ by simp
  have mz : z ∈ ({x', y', z'} : Finset V) := he ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at mx my mz
  have ex : x = x' := by
    rcases mx with h | h | h
    · exact h
    · exact absurd (h ▸ hy') (nAB hx)
    · exact absurd (h ▸ hz') (nAC hx)
  have ey : y = y' := by
    rcases my with h | h | h
    · exact absurd (h ▸ hx') (nAB · hy)
    · exact h
    · exact absurd (h ▸ hz') (nBC hy)
  have ez : z = z' := by
    rcases mz with h | h | h
    · exact absurd (h ▸ hx') (nAC · hz)
    · exact absurd (h ▸ hy') (nBC · hz)
    · exact h
  simp [ex, ey, ez]

omit [Fintype V] in
theorem crossing_subset {A B C : Finset V} (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (U : Finset V) :
    crossing A B C ⊆ U.powersetCard 3 ∨ ¬ (A ∪ B ∪ C ⊆ U) := by
  by_cases hU : A ∪ B ∪ C ⊆ U
  · left
    intro e he
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := mem_crossing.1 he
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> apply hU <;> simp [*]
    · have hxy : x ≠ y := fun h => Finset.disjoint_left.1 hAB hx (h ▸ hy)
      have hxz : x ≠ z := fun h => Finset.disjoint_left.1 hAC hx (h ▸ hz)
      have hyz : y ≠ z := fun h => Finset.disjoint_left.1 hBC hy (h ▸ hz)
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  · exact Or.inr hU

/-- The crossing triples of a colouring are 3-sets. -/
theorem crossing_subset_univ {A B C : Finset V} (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) : crossing A B C ⊆ (Finset.univ : Finset V).powersetCard 3 :=
  (crossing_subset hAB hAC hBC Finset.univ).resolve_right (by simp)

end Podc.EquivocationPrice

namespace Podc.EquivocationPrice

/-- **Definition 3.** `Tₙ(h)`: the minimum number of edges of an `h`-disjoint 3-uniform
hypergraph on `n` vertices (`0` if there is none, by the convention `sInf ∅ = 0`). -/
noncomputable def T (n h : ℕ) : ℕ :=
  sInf {m | ∃ E : Finset (Finset (Fin n)), Uniform3 E ∧ HDisjoint E h ∧ E.card = m}

/-- **Definition 7.** `Uₙ(h)`: the minimum integer `m` such that every 3-uniform hypergraph on
`n` vertices with at least `m` edges is `h`-disjoint. -/
noncomputable def U (n h : ℕ) : ℕ :=
  sInf {m | ∀ E : Finset (Finset (Fin n)), Uniform3 E → m ≤ E.card → HDisjoint E h}

end Podc.EquivocationPrice
