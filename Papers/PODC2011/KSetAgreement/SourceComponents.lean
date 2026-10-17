import Mathlib
import Podc.Digraph.Walk

/-!
# Source components of finite digraphs (Lemmas 6 and 7 of [BRS11])

Biely, Robinson, Schmid, *Easy Impossibility Proofs for k-Set Agreement in Message Passing
Systems*, PODC 2011 (arXiv 1103.3671v2), Section VI.

A digraph is a relation `E : α → α → Prop` on a finite type (`E u v` = edge `u → v`). A *source
component* is a strongly connected component with no incoming edges from outside
(`IsSourceComponent`, the library notion `Digraph.IsSourceComponent` of `Podc.Digraph.Walk` for the
digraph `⟨E⟩`); equivalently (`isSourceComponent_iff`) a nonempty, strongly connected set of
vertices closed under in-neighbours.

* `IsRoot E v`: every ancestor of `v` is a descendant of `v`; the source components are exactly
  the ancestor sets `anc E v` of roots `v` (`isSourceComponent_anc`, `IsSourceComponent.eq_anc`).
* `exists_isRoot`: every vertex has a root ancestor
  (`Digraph.exists_isSourceComponent_subset`).
* `exists_sourceComponent` (**Lemma 6**) and `exists_sourceComponent_anc` (**Lemma 7**).
* `IsSourceComponent.eq_or_disjoint`, `card_sourceComponents_le`: distinct source components are
  disjoint, so there are at most `⌊n / (δ + 1)⌋` of size `≥ δ + 1`.
-/

-- CSLib candidate: `IsRoot`, `exists_isRoot` and the counting lemmas (the rest is the library
-- theory of `Podc.Digraph.Walk`, specialized to finsets of vertices).

namespace KSetAgreement.SourceComp

open Relation Finset

variable {α : Type*} (E : α → α → Prop)

/-- `C` is a *source component* of the digraph `E`: a strongly connected component with no
incoming edges from outside, i.e. a source of the condensation DAG (`Digraph.IsSourceComponent`
for the digraph with arcs `E`). See `isSourceComponent_iff` for the elementary characterization. -/
def IsSourceComponent (C : Finset α) : Prop :=
  (Digraph.mk E).IsSourceComponent (C : Set α)

/-- `v` is a *root*: every vertex with a path to `v` is reachable from `v`, i.e. `v` lies in a
source component. -/
def IsRoot (v : α) : Prop := ∀ u, ReflTransGen E u v → ReflTransGen E v u

open Classical in
/-- The ancestors of `v` (vertices with a directed path to `v`, including `v`). -/
noncomputable def anc [Fintype α] (v : α) : Finset α := univ.filter (fun u => ReflTransGen E u v)

variable {E}

@[simp] theorem mem_anc [Fintype α] {u v : α} : u ∈ anc E v ↔ ReflTransGen E u v := by
  classical
  simp [anc]

/-- A source component is a nonempty strongly connected set of vertices closed under
in-neighbours. -/
theorem isSourceComponent_iff {C : Finset α} : IsSourceComponent E C ↔
    C.Nonempty ∧ (∀ u ∈ C, ∀ v ∈ C, ReflTransGen E u v) ∧ ∀ u v, E u v → v ∈ C → u ∈ C := by
  refine ⟨fun hC => ⟨Finset.coe_nonempty.1 hC.nonempty, fun u hu v hv => hC.reachable hu hv,
    fun u v huv hv => hC.closed v hv u huv⟩, fun ⟨⟨r, hr⟩, hsc, hcl⟩ => ?_⟩
  have hcl' : ∀ v ∈ (C : Set α), ∀ u, E u v → u ∈ (C : Set α) := fun v hv u huv => hcl u v huv hv
  refine Digraph.isSourceComponent_iff.2 ⟨r, Set.ext fun u => ⟨fun hu => hsc u hu r hr,
    fun hu => Digraph.mem_of_reachable_of_closed hcl' hu hr⟩, fun u hu => ?_⟩
  exact hsc r hr u (Digraph.mem_of_reachable_of_closed hcl' hu hr)

theorem IsSourceComponent.mem_of_rtg {C : Finset α} (hC : IsSourceComponent E C) {u v : α}
    (hv : v ∈ C) (h : ReflTransGen E u v) : u ∈ C :=
  Digraph.mem_of_reachable_of_closed (G := ⟨E⟩) hC.closed h hv

theorem IsSourceComponent.isRoot {C : Finset α} (hC : IsSourceComponent E C) {v : α}
    (hv : v ∈ C) : IsRoot E v :=
  fun _ hu => Digraph.IsSourceComponent.reachable hC hv (hC.mem_of_rtg hv hu)

theorem coe_anc [Fintype α] (v : α) : (anc E v : Set α) = {u | (Digraph.mk E).Reachable u v} :=
  Set.ext fun _ => mem_anc

/-- The ancestor set of a root is a source component. -/
theorem isSourceComponent_anc [Fintype α] {v : α} (h : IsRoot E v) :
    IsSourceComponent E (anc E v) :=
  Digraph.isSourceComponent_iff.2 ⟨v, coe_anc v, h⟩

/-- A source component is the ancestor set of any of its vertices. -/
theorem IsSourceComponent.eq_anc [Fintype α] {C : Finset α} (hC : IsSourceComponent E C) {v : α}
    (hv : v ∈ C) : C = anc E v :=
  Finset.coe_injective ((Digraph.IsSourceComponent.eq_setOf_reachable hC hv).trans (coe_anc v).symm)

/-- Two source components are equal or disjoint. -/
theorem IsSourceComponent.eq_or_disjoint {C D : Finset α} (hC : IsSourceComponent E C)
    (hD : IsSourceComponent E D) : C = D ∨ Disjoint C D := by
  by_cases h : C = D
  · exact Or.inl h
  · exact Or.inr (Finset.disjoint_coe.1
      (Digraph.IsSourceComponent.disjoint hC hD (Finset.coe_injective.ne h)))

/-- A source component containing a vertex `v` without self-loop contains `v` and all of its
in-neighbours. -/
theorem IsSourceComponent.card_ge [Fintype α] [DecidableRel E] {C : Finset α}
    (hC : IsSourceComponent E C) {v : α} (hv : v ∈ C) (hloop : ¬ E v v) :
    #{u | E u v} + 1 ≤ C.card := by
  classical
  have hsub : insert v ({u | E u v} : Finset α) ⊆ C := by
    intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · exact hv
    · exact hC.mem_of_rtg hv (.single (Finset.mem_filter.1 hu).2)
  have hnot : v ∉ ({u | E u v} : Finset α) := by simpa using hloop
  simpa [Finset.card_insert_of_notMem hnot] using Finset.card_le_card hsub

/-- Every vertex has a root ancestor (a vertex of a source component among its ancestors). -/
theorem exists_isRoot [Finite α] (v : α) : ∃ r, ReflTransGen E r v ∧ IsRoot E r := by
  obtain ⟨S, hS, hSv⟩ := (Digraph.mk E).exists_isSourceComponent_subset v
  obtain ⟨r, hr⟩ := hS.nonempty
  exact ⟨r, hSv hr, fun u hu =>
    hS.reachable hr (Digraph.mem_of_reachable_of_closed hS.closed hu hr)⟩

/-- **Lemma 6 of [BRS11].** Every finite digraph without self-loops in which every vertex has
in-degree at least `δ` has a source component of size at least `δ + 1`.

(The paper assumes `δ > 0`; this is not needed. Instead we need the graph to be nonempty, which
the paper leaves implicit.) -/
theorem exists_sourceComponent [Fintype α] [Nonempty α] [DecidableRel E]
    (hloop : ∀ v, ¬ E v v) (δ : ℕ) (hdeg : ∀ v, δ ≤ #{u | E u v}) :
    ∃ C : Finset α, IsSourceComponent E C ∧ δ + 1 ≤ C.card := by
  obtain ⟨r, -, hr⟩ := exists_isRoot (E := E) (Classical.arbitrary α)
  have hC := isSourceComponent_anc hr
  exact ⟨_, hC, (Nat.add_le_add_right (hdeg r) 1).trans
    (hC.card_ge (mem_anc.2 ReflTransGen.refl) (hloop r))⟩

/-- **Lemma 7 of [BRS11].** In a finite digraph without self-loops in which every vertex has
in-degree at least `δ`, every vertex `v` is reachable from all vertices of some source component
of size at least `δ + 1`; in particular this source component lies in the weakly connected
component of `v`. -/
theorem exists_sourceComponent_anc [Fintype α] [DecidableRel E]
    (hloop : ∀ v, ¬ E v v) (δ : ℕ) (hdeg : ∀ v, δ ≤ #{u | E u v}) (v : α) :
    ∃ C : Finset α, IsSourceComponent E C ∧ δ + 1 ≤ C.card ∧
      (∀ u ∈ C, ReflTransGen E u v) ∧
      ∀ u ∈ C, ReflTransGen (fun a b => E a b ∨ E b a) u v := by
  obtain ⟨r, hrv, hr⟩ := exists_isRoot (E := E) v
  have hC := isSourceComponent_anc hr
  have hpath : ∀ u ∈ anc E r, ReflTransGen E u v := fun u hu => (mem_anc.1 hu).trans hrv
  refine ⟨_, hC, (Nat.add_le_add_right (hdeg r) 1).trans
    (hC.card_ge (mem_anc.2 ReflTransGen.refl) (hloop r)), hpath, fun u hu => ?_⟩
  exact ReflTransGen.mono (fun a b h => Or.inl h) _ _ (hpath u hu)

/-- Pairwise disjoint sets of size at least `δ + 1` in a type with `n` elements number at most
`n / (δ + 1)` (multiplicative form). -/
theorem card_mul_le_of_pairwiseDisjoint [Fintype α] [DecidableEq α] (𝒞 : Finset (Finset α))
    (hd : (𝒞 : Set (Finset α)).PairwiseDisjoint id) (δ : ℕ) (hc : ∀ C ∈ 𝒞, δ + 1 ≤ C.card) :
    𝒞.card * (δ + 1) ≤ Fintype.card α := by
  have h1 : #(𝒞.biUnion id) = ∑ C ∈ 𝒞, #C := Finset.card_biUnion hd
  have h2 : 𝒞.card • (δ + 1) ≤ ∑ C ∈ 𝒞, #C := Finset.card_nsmul_le_sum _ _ _ hc
  have h3 : #(𝒞.biUnion id) ≤ Fintype.card α := Finset.card_le_univ _
  simp only [smul_eq_mul] at h2
  omega

/-- Distinct source components are disjoint, so a digraph on `n` vertices has at most
`⌊n / (δ + 1)⌋` source components of size at least `δ + 1` (Section VI of [BRS11]). -/
theorem card_sourceComponents_le [Fintype α] [DecidableEq α] (𝒞 : Finset (Finset α)) (δ : ℕ)
    (h : ∀ C ∈ 𝒞, IsSourceComponent E C ∧ δ + 1 ≤ C.card) :
    𝒞.card ≤ Fintype.card α / (δ + 1) := by
  rw [Nat.le_div_iff_mul_le (Nat.succ_pos δ)]
  refine card_mul_le_of_pairwiseDisjoint 𝒞 ?_ δ (fun C hC => (h C hC).2)
  intro C hC D hD hne
  exact ((h C hC).1.eq_or_disjoint (h D hD).1).resolve_left hne

/-! ### Ancestor-closed sets -/

/-- Two digraphs with the same in-edges into an in-closed set `S` have the same ancestors of the
elements of `S`. -/
theorem rtg_iff_of_inClosed {E' : α → α → Prop} {S : Set α} (hE : ∀ r ∈ S, ∀ u, E' u r ↔ E u r)
    (hS : ∀ r ∈ S, ∀ u, E u r → u ∈ S) {u r : α} (hr : r ∈ S) :
    ReflTransGen E' u r ↔ ReflTransGen E u r := by
  have hS' : ∀ r ∈ S, ∀ u, E' u r → u ∈ S := fun r hr u h => hS r hr u ((hE r hr u).1 h)
  constructor
  · intro h
    induction h using ReflTransGen.head_induction_on with
    | refl => exact ReflTransGen.refl
    | head huw hw ih =>
      have hwS := Digraph.mem_of_reachable_of_closed (G := ⟨E'⟩) hS' hw hr
      exact ReflTransGen.head ((hE _ hwS _).1 huw) ih
  · intro h
    induction h using ReflTransGen.head_induction_on with
    | refl => exact ReflTransGen.refl
    | head huw hw ih =>
      have hwS := Digraph.mem_of_reachable_of_closed (G := ⟨E⟩) hS hw hr
      exact ReflTransGen.head ((hE _ hwS _).2 huw) ih

/-- Ancestors of a root are roots. -/
theorem IsRoot.of_rtg {m u : α} (hm : IsRoot E m) (hu : ReflTransGen E u m) : IsRoot E u :=
  fun w hw => hu.trans (hm w (hw.trans hu))

end KSetAgreement.SourceComp
