import Mathlib

/-!
# Problems and the speedup operators (Brandt, PODC 2019, §3 and §4.1–4.2)

A *problem* (§3) is given by a set of output labels `O`, and for every maximum degree `Δ`
* `f Δ ⊆ O` (the labels allowed for degree `Δ`; finite in the paper),
* `g Δ`, a set of 2-element multisets of labels (edge configurations),
* `h Δ`, a set of multisets of at most `Δ` labels (node configurations).

We keep `f`, `g`, `h` as arbitrary sets; the well-formedness conditions of the paper are collected
in `Problem.WF` and are preserved by the operators (`WF.edgeStep`, `WF.nodeStep`), but none of the
speedup theorems needs them.

The derived problems of §4.1:
* `P.edgeStep` is `Π_{1/2}`: labels are sets `Y ⊆ f Δ`, an edge `{Y, Z}` is good if *every*
  `{y, z}` with `y ∈ Y`, `z ∈ Z` is good (Property 1), a node is good if *some* choice of one label
  per set is good (Property 2);
* `P.nodeStep` is the dual step (Properties 3 and 4): edges existential, nodes universal;
* `P.speedup = P.edgeStep.nodeStep` is `Π_1`.

The simplified problems of §4.2 (Properties 5 and 6) are `edgeStepMax`, `nodeStepMax` and
`speedupMax = P.edgeStepMax.nodeStepMax` (`Π'_1`).
-/

-- CSLib candidate (problems and round-elimination operators)
namespace AutomaticSpeedup

/-- A problem in the sense of §3 (for all maximum degrees `Δ` at once). -/
structure Problem (L : Type*) where
  /-- `f Δ`: the output labels usable in graphs of maximum degree `Δ`. -/
  f : ℕ → Set L
  /-- `g Δ`: the allowed edge configurations (2-element multisets). -/
  g : ℕ → Set (Multiset L)
  /-- `h Δ`: the allowed node configurations (multisets with at most `Δ` elements). -/
  h : ℕ → Set (Multiset L)

namespace Problem

variable {L : Type*}

/-- The well-formedness conditions of §3, items 2–4. -/
structure WF (P : Problem L) : Prop where
  f_finite : ∀ Δ, (P.f Δ).Finite
  g_card : ∀ Δ, ∀ m ∈ P.g Δ, Multiset.card m = 2
  g_sub : ∀ Δ, ∀ m ∈ P.g Δ, ∀ x ∈ m, x ∈ P.f Δ
  h_card : ∀ Δ, ∀ m ∈ P.h Δ, Multiset.card m ≤ Δ
  h_sub : ∀ Δ, ∀ m ∈ P.h Δ, ∀ x ∈ m, x ∈ P.f Δ

/-- Property 1 of §4.1 (universal edge condition) for a pair of sets of labels. -/
def EdgeAll (P : Problem L) (Δ : ℕ) (Y Z : Set L) : Prop :=
  Y ⊆ P.f Δ ∧ Z ⊆ P.f Δ ∧ ∀ y ∈ Y, ∀ z ∈ Z, ({y, z} : Multiset L) ∈ P.g Δ

/-- Property 3 of §4.1 (existential edge condition) for a pair of sets of labels. -/
def EdgeEx (P : Problem L) (Δ : ℕ) (Y Z : Set L) : Prop :=
  Y ⊆ P.f Δ ∧ Z ⊆ P.f Δ ∧ ∃ y ∈ Y, ∃ z ∈ Z, ({y, z} : Multiset L) ∈ P.g Δ

/-- Property 2 of §4.1 (existential node condition): the multiset `m` of sets of labels has at most
`Δ` elements, all of them subsets of `f Δ`, and one can choose one element from each set so that
the resulting multiset is in `h Δ`. A *choice* is a multiset `m'` related to `m` by `∈`
elementwise (`Multiset.Rel`). -/
def NodeEx (P : Problem L) (Δ : ℕ) (m : Multiset (Set L)) : Prop :=
  Multiset.card m ≤ Δ ∧ (∀ Y ∈ m, Y ⊆ P.f Δ) ∧
    ∃ m', Multiset.Rel (· ∈ ·) m' m ∧ m' ∈ P.h Δ

/-- Property 4 of §4.1 (universal node condition). -/
def NodeAll (P : Problem L) (Δ : ℕ) (m : Multiset (Set L)) : Prop :=
  Multiset.card m ≤ Δ ∧ (∀ Y ∈ m, Y ⊆ P.f Δ) ∧
    ∀ m', Multiset.Rel (· ∈ ·) m' m → m' ∈ P.h Δ

/-- `Π_{1/2}` (§4.1, Properties 1 and 2). -/
def edgeStep (P : Problem L) : Problem (Set L) where
  f Δ := {Y | Y ⊆ P.f Δ}
  g Δ := {m | ∃ Y Z, m = {Y, Z} ∧ P.EdgeAll Δ Y Z}
  h Δ := {m | P.NodeEx Δ m}

/-- The second half step `Π_{1/2} ↦ Π_1` (§4.1, Properties 3 and 4). -/
def nodeStep (P : Problem L) : Problem (Set L) where
  f Δ := {Y | Y ⊆ P.f Δ}
  g Δ := {m | ∃ Y Z, m = {Y, Z} ∧ P.EdgeEx Δ Y Z}
  h Δ := {m | P.NodeAll Δ m}

/-- The speedup `Π ↦ Π_1` of §4.1. -/
def speedup (P : Problem L) : Problem (Set (Set L)) := P.edgeStep.nodeStep

/-- Property 5 of §4.2: Property 1, and both sets are maximal with this property. -/
def EdgeAllMax (P : Problem L) (Δ : ℕ) (Y Z : Set L) : Prop :=
  P.EdgeAll Δ Y Z ∧ (∀ Y', Y ⊂ Y' → ¬ P.EdgeAll Δ Y' Z) ∧ (∀ Z', Z ⊂ Z' → ¬ P.EdgeAll Δ Y Z')

/-- Property 6 of §4.2: Property 4, and no set of the multiset can be enlarged. -/
def NodeAllMax (P : Problem L) (Δ : ℕ) (m : Multiset (Set L)) : Prop :=
  P.NodeAll Δ m ∧ ∀ Y ∈ m, ∀ Y', Y ⊂ Y' → ¬ P.NodeAll Δ (Y' ::ₘ m.erase Y)

/-- `Π'_{1/2}`: `Π_{1/2}` with Property 1 replaced by Property 5 (§4.2). -/
def edgeStepMax (P : Problem L) : Problem (Set L) where
  f Δ := {Y | Y ⊆ P.f Δ}
  g Δ := {m | ∃ Y Z, m = {Y, Z} ∧ P.EdgeAllMax Δ Y Z}
  h Δ := {m | P.NodeEx Δ m}

/-- The simplified second half step: Property 4 replaced by Property 6 (§4.2). -/
def nodeStepMax (P : Problem L) : Problem (Set L) where
  f Δ := {Y | Y ⊆ P.f Δ}
  g Δ := {m | ∃ Y Z, m = {Y, Z} ∧ P.EdgeEx Δ Y Z}
  h Δ := {m | P.NodeAllMax Δ m}

/-- `Π'_1 = (Π'_{1/2})'_1` (§4.2). -/
def speedupMax (P : Problem L) : Problem (Set (Set L)) := P.edgeStepMax.nodeStepMax

/-- Iterated speedup `Π_k` (label type `Set (Set ⋯ L)`, `2k` times). -/
def IterLabel (L : Type*) : ℕ → Type _
  | 0 => L
  | k + 1 => Set (Set (IterLabel L k))

/-- `Π_k` of §4.1 (`Π_0 = Π`, `Π_{k+1} = (Π_k)_1`). -/
def iter (P : Problem L) : (k : ℕ) → Problem (IterLabel L k)
  | 0 => P
  | k + 1 => (P.iter k).speedup

/-! ### Basic API -/

theorem pair_eq_pair_iff {α : Type*} {a b c d : α} :
    ({a, b} : Multiset α) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a ∈ ({c, d} : Multiset α) := h ▸ by simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · left; refine ⟨rfl, ?_⟩
      simpa using h
    · right; refine ⟨rfl, ?_⟩
      rw [Multiset.pair_comm c a] at h
      simpa using h
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Multiset.pair_comm _ _

theorem EdgeAll.symm {P : Problem L} {Δ : ℕ} {Y Z : Set L} (h : P.EdgeAll Δ Y Z) :
    P.EdgeAll Δ Z Y :=
  ⟨h.2.1, h.1, fun z hz y hy => Multiset.pair_comm y z ▸ h.2.2 y hy z hz⟩

theorem edgeAll_comm {P : Problem L} {Δ : ℕ} {Y Z : Set L} : P.EdgeAll Δ Y Z ↔ P.EdgeAll Δ Z Y :=
  ⟨EdgeAll.symm, EdgeAll.symm⟩

theorem EdgeEx.symm {P : Problem L} {Δ : ℕ} {Y Z : Set L} (h : P.EdgeEx Δ Y Z) :
    P.EdgeEx Δ Z Y := by
  obtain ⟨h1, h2, y, hy, z, hz, h3⟩ := h
  exact ⟨h2, h1, z, hz, y, hy, Multiset.pair_comm y z ▸ h3⟩

theorem EdgeAllMax.symm {P : Problem L} {Δ : ℕ} {Y Z : Set L} (h : P.EdgeAllMax Δ Y Z) :
    P.EdgeAllMax Δ Z Y :=
  ⟨h.1.symm, fun Z' hZ hZ' => h.2.2 Z' hZ hZ'.symm, fun Y' hY hY' => h.2.1 Y' hY hY'.symm⟩

theorem edgeStep_g_iff {P : Problem L} {Δ : ℕ} {Y Z : Set L} :
    ({Y, Z} : Multiset (Set L)) ∈ P.edgeStep.g Δ ↔ P.EdgeAll Δ Y Z := by
  refine ⟨?_, fun h => ⟨Y, Z, rfl, h⟩⟩
  rintro ⟨Y', Z', he, h⟩
  rcases pair_eq_pair_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [h, h.symm]

theorem edgeStepMax_g_iff {P : Problem L} {Δ : ℕ} {Y Z : Set L} :
    ({Y, Z} : Multiset (Set L)) ∈ P.edgeStepMax.g Δ ↔ P.EdgeAllMax Δ Y Z := by
  refine ⟨?_, fun h => ⟨Y, Z, rfl, h⟩⟩
  rintro ⟨Y', Z', he, h⟩
  rcases pair_eq_pair_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [h, h.symm]

theorem nodeStep_g_iff {P : Problem L} {Δ : ℕ} {Y Z : Set L} :
    ({Y, Z} : Multiset (Set L)) ∈ P.nodeStep.g Δ ↔ P.EdgeEx Δ Y Z := by
  refine ⟨?_, fun h => ⟨Y, Z, rfl, h⟩⟩
  rintro ⟨Y', Z', he, h⟩
  rcases pair_eq_pair_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [h, h.symm]

theorem nodeStepMax_g_iff {P : Problem L} {Δ : ℕ} {Y Z : Set L} :
    ({Y, Z} : Multiset (Set L)) ∈ P.nodeStepMax.g Δ ↔ P.EdgeEx Δ Y Z :=
  nodeStep_g_iff (P := P)

/-- The simplified problems are restrictions of the unsimplified ones. -/
theorem edgeStepMax_g_subset (P : Problem L) (Δ : ℕ) : P.edgeStepMax.g Δ ⊆ P.edgeStep.g Δ := by
  rintro m ⟨Y, Z, rfl, h⟩; exact ⟨Y, Z, rfl, h.1⟩

theorem nodeStepMax_h_subset (P : Problem L) (Δ : ℕ) : P.nodeStepMax.h Δ ⊆ P.nodeStep.h Δ :=
  fun _ h => h.1

/-! ### Well-formedness is preserved -/

theorem WF.edgeStep {P : Problem L} (hP : P.WF) : P.edgeStep.WF where
  f_finite Δ := (hP.f_finite Δ).powerset
  g_card Δ m := by rintro ⟨Y, Z, rfl, -⟩; simp
  g_sub Δ m := by
    rintro ⟨Y, Z, rfl, hY, hZ, -⟩ x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  h_card Δ m hm := hm.1
  h_sub Δ m hm := hm.2.1

theorem WF.nodeStep {P : Problem L} (hP : P.WF) : P.nodeStep.WF where
  f_finite Δ := (hP.f_finite Δ).powerset
  g_card Δ m := by rintro ⟨Y, Z, rfl, -⟩; simp
  g_sub Δ m := by
    rintro ⟨Y, Z, rfl, hY, hZ, -⟩ x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  h_card Δ m hm := hm.1
  h_sub Δ m hm := hm.2.1

theorem WF.speedup {P : Problem L} (hP : P.WF) : P.speedup.WF := hP.edgeStep.nodeStep

/-! ### Choices for port-indexed configurations

A node of degree `d` with outputs `Y 0, …, Y (d-1)` has the node configuration
`(Multiset.range d).map Y`. Choices of one element per set are then port-indexed functions. -/

theorem rel_mem_map_range_of_exists {Y : ℕ → Set L} {d : ℕ} {y : ℕ → L}
    (hy : ∀ i < d, y i ∈ Y i) :
    Multiset.Rel (· ∈ ·) ((Multiset.range d).map y) ((Multiset.range d).map Y) := by
  rw [Multiset.rel_map]
  exact Multiset.rel_refl_of_refl_on fun i hi => hy i (Multiset.mem_range.1 hi)

theorem rel_mem_map_range [Nonempty L] {Y : ℕ → Set L} {d : ℕ} {m : Multiset L} :
    Multiset.Rel (· ∈ ·) m ((Multiset.range d).map Y) ↔
      ∃ y : ℕ → L, (∀ i < d, y i ∈ Y i) ∧ m = (Multiset.range d).map y := by
  induction d generalizing m with
  | zero => simp only [Multiset.range_zero, Multiset.map_zero, Multiset.rel_zero_right]
            exact ⟨fun h => ⟨Classical.ofNonempty, by simp, h⟩, fun ⟨_, _, h⟩ => h⟩
  | succ d ih =>
    rw [Multiset.range_succ, Multiset.map_cons, Multiset.rel_cons_right]
    constructor
    · rintro ⟨a, m', ha, hm', rfl⟩
      obtain ⟨y, hy, rfl⟩ := ih.1 hm'
      refine ⟨Function.update y d a, fun i hi => ?_, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · rw [Function.update_of_ne hi.ne]; exact hy i hi
        · simpa using ha
      · rw [Multiset.map_cons, Function.update_self]
        congr 1
        refine Multiset.map_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Multiset.mem_range.1 hi).ne]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y d, (Multiset.range d).map y, hy d (Nat.lt_succ_self d),
        ih.2 ⟨y, fun i hi => hy i (Nat.lt_succ_of_lt hi), rfl⟩, by simp⟩

theorem nodeEx_map_range [Nonempty L] {P : Problem L} {Δ d : ℕ} {Y : ℕ → Set L} :
    P.NodeEx Δ ((Multiset.range d).map Y) ↔
      d ≤ Δ ∧ (∀ i < d, Y i ⊆ P.f Δ) ∧
        ∃ y : ℕ → L, (∀ i < d, y i ∈ Y i) ∧ (Multiset.range d).map y ∈ P.h Δ := by
  simp only [NodeEx, Multiset.card_map, Multiset.card_range, Multiset.mem_map, Multiset.mem_range,
    forall_exists_index, and_imp, rel_mem_map_range]
  constructor
  · rintro ⟨h1, h2, m', ⟨y, hy, rfl⟩, hm⟩
    exact ⟨h1, fun i hi => h2 _ i hi rfl, y, hy, hm⟩
  · rintro ⟨h1, h2, y, hy, hm⟩
    exact ⟨h1, fun _ i hi he => he ▸ h2 i hi, _, ⟨y, hy, rfl⟩, hm⟩

theorem nodeAll_map_range [Nonempty L] {P : Problem L} {Δ d : ℕ} {Y : ℕ → Set L} :
    P.NodeAll Δ ((Multiset.range d).map Y) ↔
      d ≤ Δ ∧ (∀ i < d, Y i ⊆ P.f Δ) ∧
        ∀ y : ℕ → L, (∀ i < d, y i ∈ Y i) → (Multiset.range d).map y ∈ P.h Δ := by
  simp only [NodeAll, Multiset.card_map, Multiset.card_range, Multiset.mem_map, Multiset.mem_range,
    forall_exists_index, and_imp, rel_mem_map_range]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun i hi => h2 _ i hi rfl, fun y hy => h3 _ y hy rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun _ i hi he => he ▸ h2 i hi, fun _ y hy he => he ▸ h3 y hy⟩

theorem nodeEx_map_range_of {P : Problem L} {Δ d : ℕ} {Y : ℕ → Set L} (hd : d ≤ Δ)
    (hsub : ∀ i < d, Y i ⊆ P.f Δ) (y : ℕ → L) (hy : ∀ i < d, y i ∈ Y i)
    (hh : (Multiset.range d).map y ∈ P.h Δ) : P.NodeEx Δ ((Multiset.range d).map Y) := by
  refine ⟨by simpa using hd, ?_, _, rel_mem_map_range_of_exists hy, hh⟩
  simp only [Multiset.mem_map, Multiset.mem_range, forall_exists_index, and_imp]
  rintro _ i hi rfl; exact hsub i hi

theorem NodeAll.map_range {P : Problem L} {Δ d : ℕ} {Y : ℕ → Set L}
    (h : P.NodeAll Δ ((Multiset.range d).map Y)) (y : ℕ → L) (hy : ∀ i < d, y i ∈ Y i) :
    (Multiset.range d).map y ∈ P.h Δ :=
  h.2.2 _ (rel_mem_map_range_of_exists hy)

end Problem

end AutomaticSpeedup
