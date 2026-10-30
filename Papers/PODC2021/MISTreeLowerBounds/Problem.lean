import Mathlib

/-!
# Problems in the round-elimination formalism and the operators `R`, `R̄` (§2.2–2.3)

A problem on `Δ`-regular graphs (§2.2) is given by
* a set of *node configurations* `node : Set (Fin Δ → Λ)` (a node writes one label on each of its
  `Δ` incident half-edges; the paper's configurations are unordered words, i.e. `node` is meant to
  be permutation invariant, but nothing below needs this), and
* a symmetric *edge constraint* `edge : Λ → Λ → Prop` (the unordered edge configurations).

The alphabet of a problem is the whole label type `Λ`.

The operators of §2.3:
* `P.R` (the paper's `R(Π)`): labels are nonempty sets of labels; edge configurations are the
  *maximal* pairs `A₁A₂` such that every `a₁a₂ ∈ A₁ × A₂` is an edge configuration of `P`
  (`edgeMax`); the alphabet `Σ_{R(Π)}` consists of the sets occurring in these configurations
  (`alphR`); node configurations are the tuples of sets of `Σ_{R(Π)}` admitting a choice in `P.node`.
* `P.Rbar` (the paper's `R̄(Π)`): node configurations are the *maximal* tuples `B₁ … B_Δ` of nonempty
  sets such that every choice lies in `P.node` (`nodeMax`); the alphabet consists of the sets
  occurring in these configurations (`alphRbar`); `A₁A₂` is an edge configuration iff both sets are
  in the alphabet and some choice is an edge configuration of `P`.

Since node constraints are universal in `R̄`, a set containing a label outside `Σ_{R(Π)}` never
occurs in a node configuration of `R̄(R(Π))`, so taking all nonempty sets of `Finset Λ` instead of
`2^{Σ_{R(Π)}}` gives the same problem.

We also define 0-round reductions (`ZeroRoundReduction`): "`Π'` can be solved in 0 rounds given a
solution of `Π`" in the port-numbering model in which the port numbers are the colours of a given
`Δ`-edge colouring (the model of `Model.lean`): each node maps its own `Π`-configuration (indexed
by colours) to a `Π'`-configuration, and the edge of colour `c` joins the half-edges of colour `c`
of its endpoints.
-/

-- CSLib candidate (round elimination on the oriented Δ-edge-coloured Δ-regular tree)
namespace Podc.MISTreeLowerBounds

/-- A locally checkable problem on `Δ`-regular graphs in the node-edge formalism (§2.2). -/
structure Problem (Δ : ℕ) (Λ : Type*) where
  /-- Node configurations, indexed by the ports (= colours) `Fin Δ`. -/
  node : Set (Fin Δ → Λ)
  /-- Edge configurations (unordered, hence symmetric). -/
  edge : Λ → Λ → Prop
  edge_symm : ∀ a b, edge a b → edge b a

variable {Δ : ℕ} {Λ Λ' Λ'' : Type*}

namespace Problem

/-! ### The edge step `R` -/

/-- `A₁A₂` with `A₁, A₂` nonempty and every `a₁a₂ ∈ A₁ × A₂` an edge configuration (the collection
`A` in the definition of `R(Π)`). -/
def EdgeAll (P : Problem Δ Λ) (A B : Finset Λ) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧ ∀ a ∈ A, ∀ b ∈ B, P.edge a b

/-- `A₁A₂` is a maximal (i.e. not non-maximal) configuration of `A`. -/
def edgeMax (P : Problem Δ Λ) (A B : Finset Λ) : Prop :=
  P.EdgeAll A B ∧ ∀ A' B', A ⊆ A' → B ⊆ B' → P.EdgeAll A' B' → A' = A ∧ B' = B

/-- `Σ_{R(Π)}`: the sets occurring in the edge configurations of `R(Π)`. -/
def alphR (P : Problem Δ Λ) : Set (Finset Λ) := {A | ∃ B, P.edgeMax A B}

theorem EdgeAll.symm {P : Problem Δ Λ} {A B : Finset Λ} (h : P.EdgeAll A B) : P.EdgeAll B A :=
  ⟨h.2.1, h.1, fun b hb a ha => P.edge_symm _ _ (h.2.2 a ha b hb)⟩

theorem edgeMax.symm {P : Problem Δ Λ} {A B : Finset Λ} (h : P.edgeMax A B) : P.edgeMax B A :=
  ⟨h.1.symm, fun B' A' hB hA h' => (h.2 A' B' hA hB h'.symm).symm⟩

/-- `R(Π)` (§2.3). -/
def R (P : Problem Δ Λ) : Problem Δ (Finset Λ) where
  node := {Y | (∀ i, Y i ∈ P.alphR) ∧ ∃ y : Fin Δ → Λ, (∀ i, y i ∈ Y i) ∧ y ∈ P.node}
  edge := P.edgeMax
  edge_symm _ _ h := h.symm

/-! ### The node step `R̄` -/

/-- `B₁ … B_Δ` with all `Bᵢ` nonempty and every choice a node configuration (the collection `B`
in the definition of `R̄(Π)`). -/
def NodeAll (P : Problem Δ Λ) (Y : Fin Δ → Finset Λ) : Prop :=
  (∀ i, (Y i).Nonempty) ∧ ∀ y : Fin Δ → Λ, (∀ i, y i ∈ Y i) → y ∈ P.node

/-- `B₁ … B_Δ` is a maximal configuration of `B`. -/
def nodeMax (P : Problem Δ Λ) (Y : Fin Δ → Finset Λ) : Prop :=
  P.NodeAll Y ∧ ∀ Y' : Fin Δ → Finset Λ, (∀ i, Y i ⊆ Y' i) → P.NodeAll Y' → Y' = Y

/-- `Σ_{R̄(Π)}`: the sets occurring in the node configurations of `R̄(Π)`. -/
def alphRbar (P : Problem Δ Λ) : Set (Finset Λ) := {B | ∃ Y, P.nodeMax Y ∧ ∃ i, Y i = B}

/-- `R̄(Π)` (§2.3). -/
def Rbar (P : Problem Δ Λ) : Problem Δ (Finset Λ) where
  node := P.nodeMax
  edge A B := A ∈ P.alphRbar ∧ B ∈ P.alphRbar ∧ ∃ a ∈ A, ∃ b ∈ B, P.edge a b
  edge_symm A B := by
    rintro ⟨hA, hB, a, ha, b, hb, h⟩
    exact ⟨hB, hA, b, hb, a, ha, P.edge_symm _ _ h⟩

/-! ### Maximal extensions exist (finite label sets) -/

theorem EdgeAll.mono {P : Problem Δ Λ} {A B A' B' : Finset Λ} (h : P.EdgeAll A' B')
    (hA : A ⊆ A') (hB : B ⊆ B') (hA0 : A.Nonempty) (hB0 : B.Nonempty) : P.EdgeAll A B :=
  ⟨hA0, hB0, fun a ha b hb => h.2.2 a (hA ha) b (hB hb)⟩

theorem EdgeAll.exists_edgeMax [Finite Λ] {P : Problem Δ Λ} {A B : Finset Λ} (h : P.EdgeAll A B) :
    ∃ A' B', A ⊆ A' ∧ B ⊆ B' ∧ P.edgeMax A' B' := by
  classical
  have : Fintype Λ := Fintype.ofFinite Λ
  let S : Finset (Finset Λ × Finset Λ) :=
    Finset.univ.filter fun p => A ⊆ p.1 ∧ B ⊆ p.2 ∧ P.EdgeAll p.1 p.2
  have hS : (A, B) ∈ S := by simp [S, h]
  obtain ⟨p, hp, hmax⟩ := S.exists_max_image (fun p => p.1.card + p.2.card) ⟨_, hS⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  refine ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2, fun A' B' hA hB h' => ?_⟩
  have hle := hmax (A', B') (by simp [S, hp.1.trans hA, hp.2.1.trans hB, h'])
  have h1 := Finset.card_le_card hA
  have h2 := Finset.card_le_card hB
  exact ⟨(Finset.eq_of_subset_of_card_le hA (by simp at hle; omega)).symm,
    (Finset.eq_of_subset_of_card_le hB (by simp at hle; omega)).symm⟩

theorem NodeAll.exists_nodeMax [Finite Λ] {P : Problem Δ Λ} {Y : Fin Δ → Finset Λ}
    (h : P.NodeAll Y) : ∃ Y', (∀ i, Y i ⊆ Y' i) ∧ P.nodeMax Y' := by
  classical
  have : Fintype Λ := Fintype.ofFinite Λ
  let S : Finset (Fin Δ → Finset Λ) :=
    Finset.univ.filter fun Z => (∀ i, Y i ⊆ Z i) ∧ P.NodeAll Z
  have hS : Y ∈ S := by simp [S, h]
  obtain ⟨Z, hZ, hmax⟩ := S.exists_max_image (fun Z => ∑ i, (Z i).card) ⟨_, hS⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hZ
  refine ⟨Z, hZ.1, hZ.2, fun Z' hZZ' h' => ?_⟩
  have hle := hmax Z' (by simp [S, fun i => (hZ.1 i).trans (hZZ' i), h'])
  have hcard : ∀ i, (Z i).card ≤ (Z' i).card := fun i => Finset.card_le_card (hZZ' i)
  have heq : ∀ i, (Z i).card = (Z' i).card := by
    intro i
    by_contra hne
    have hlt : (Z i).card < (Z' i).card := lt_of_le_of_ne (hcard i) hne
    have := Finset.sum_lt_sum (s := Finset.univ) (fun j _ => hcard j) ⟨i, Finset.mem_univ _, hlt⟩
    omega
  funext i
  exact (Finset.eq_of_subset_of_card_le (hZZ' i) (heq i).ge).symm

/-! ### Observation 4: labels of `R̄` are right-closed

A label `ℓ'` is *at least as strong as* `ℓ` w.r.t. the node constraint if replacing one occurrence
of `ℓ` by `ℓ'` in a node configuration gives a node configuration. Every label of `R̄(Π)` is
right-closed for this relation (Observation 4 of the paper, imported there from [5]). -/

/-- `ℓ'` is at least as strong as `ℓ` according to the node constraint of `P` (§2.3). -/
def NodeStronger (P : Problem Δ Λ) (ℓ ℓ' : Λ) : Prop :=
  ∀ y ∈ P.node, ∀ i, y i = ℓ → Function.update y i ℓ' ∈ P.node

/-- Observation 4 (second half): the sets in the node configurations of `R̄(Π)` are right-closed
w.r.t. the node constraint of `Π`. -/
theorem nodeMax.mem_of_stronger [DecidableEq Λ] {P : Problem Δ Λ} {Y : Fin Δ → Finset Λ}
    (h : P.nodeMax Y) {i : Fin Δ} {ℓ ℓ' : Λ} (hℓ : ℓ ∈ Y i) (hs : P.NodeStronger ℓ ℓ') :
    ℓ' ∈ Y i := by
  classical
  let Y' := Function.update Y i (insert ℓ' (Y i))
  have hY' : P.NodeAll Y' := by
    refine ⟨fun j => ?_, fun y hy => ?_⟩
    · by_cases hj : j = i
      · subst hj; simp [Y']
      · simp only [Y', Function.update_of_ne hj]; exact h.1.1 j
    · by_cases hyi : y i = ℓ'
      · have hy' : Function.update y i ℓ ∈ P.node := by
          refine h.1.2 _ fun j => ?_
          by_cases hj : j = i
          · subst hj; simpa using hℓ
          · have := hy j
            simp only [Y', Function.update_of_ne hj] at this
            simpa [Function.update_of_ne hj] using this
        have := hs _ hy' i (by simp)
        simpa [← hyi] using this
      · refine h.1.2 _ fun j => ?_
        have := hy j
        by_cases hj : j = i
        · subst hj
          simp only [Y', Function.update_self, Finset.mem_insert] at this
          exact this.resolve_left hyi
        · simpa [Y', Function.update_of_ne hj] using this
  have := h.2 Y' (fun j => by
    by_cases hj : j = i
    · subst hj; simp [Y']
    · simp [Y', Function.update_of_ne hj]) hY'
  have h2 : ℓ' ∈ Y' i := by simp [Y']
  rwa [this] at h2

/-- Observation 4 (second half), for the alphabet of `R̄(Π)`. -/
theorem mem_of_mem_alphRbar [DecidableEq Λ] {P : Problem Δ Λ} {B : Finset Λ}
    (hB : B ∈ P.alphRbar) {ℓ ℓ' : Λ} (hℓ : ℓ ∈ B) (hs : P.NodeStronger ℓ ℓ') : ℓ' ∈ B := by
  obtain ⟨Y, hY, i, rfl⟩ := hB
  exact hY.mem_of_stronger hℓ hs

/-- In `R(Π)`, a larger label (of the alphabet) is at least as strong according to the node
constraint: this is how the node diagram of `R(Π)` arises (Figure 5). -/
theorem R_nodeStronger [DecidableEq Λ] {P : Problem Δ Λ} {S S' : Finset Λ} (hSS' : S ⊆ S')
    (hS' : S' ∈ P.alphR) : P.R.NodeStronger S S' := by
  rintro Y ⟨hY, y, hy, hyN⟩ i rfl
  refine ⟨fun j => ?_, y, fun j => ?_, hyN⟩
  · by_cases hj : j = i
    · subst hj; simpa using hS'
    · simpa [Function.update_of_ne hj] using hY j
  · by_cases hj : j = i
    · subst hj; simpa using hSS' (hy j)
    · simpa [Function.update_of_ne hj] using hy j

end Problem

/-! ### 0-round reductions -/

/-- `Π'` can be solved in 0 rounds given a solution of `Π` (in the port-numbering model whose port
numbers are the colours of a `Δ`-edge colouring): a map `f` from `Π`-configurations to
`Π'`-configurations such that the configurations of `Π` go to configurations of `Π'`, and an edge
configuration of `Π` on the edge of colour `c` goes to one of `Π'`. -/
def ZeroRoundReduction (P : Problem Δ Λ) (P' : Problem Δ Λ') : Prop :=
  ∃ f : (Fin Δ → Λ) → (Fin Δ → Λ'), (∀ σ ∈ P.node, f σ ∈ P'.node) ∧
    ∀ σ ∈ P.node, ∀ τ ∈ P.node, ∀ c, P.edge (σ c) (τ c) → P'.edge (f σ c) (f τ c)

namespace ZeroRoundReduction

theorem refl (P : Problem Δ Λ) : ZeroRoundReduction P P :=
  ⟨id, fun _ h => h, fun _ _ _ _ _ h => h⟩

theorem trans {P : Problem Δ Λ} {P' : Problem Δ Λ'} {P'' : Problem Δ Λ''}
    (h : ZeroRoundReduction P P') (h' : ZeroRoundReduction P' P'') : ZeroRoundReduction P P'' := by
  obtain ⟨f, hf1, hf2⟩ := h
  obtain ⟨g, hg1, hg2⟩ := h'
  exact ⟨g ∘ f, fun σ hσ => hg1 _ (hf1 σ hσ),
    fun σ hσ τ hτ c he => hg2 _ (hf1 σ hσ) _ (hf1 τ hτ) c (hf2 σ hσ τ hτ c he)⟩

/-- A relabelling `g : Λ → Λ'` of the labels that maps node configurations to node configurations
and edge configurations to edge configurations is a 0-round reduction (it does not even use the
colours). -/
theorem of_labelMap {P : Problem Δ Λ} {P' : Problem Δ Λ'} (g : Λ → Λ')
    (hn : ∀ σ ∈ P.node, g ∘ σ ∈ P'.node) (he : ∀ a b, P.edge a b → P'.edge (g a) (g b)) :
    ZeroRoundReduction P P' :=
  ⟨fun σ => g ∘ σ, hn, fun _ _ _ _ c h => he _ _ h⟩

end ZeroRoundReduction

end Podc.MISTreeLowerBounds
