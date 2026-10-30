import Mathlib

/-!
# Clique covers and connectors (Section 2 of Barenboim–Elkin–Maimon, PODC 2017)

The paper works with a graph `G` of *diversity* `D` (every vertex lies in at most `D` maximal
cliques, or more generally in at most `D` cliques of a "consistent clique identification") and
maximal clique size `S`. We model the identified cliques as a **clique cover** `𝒬`: a finite family
of cliques of `G` covering every edge, every vertex lying in at most `D` members, every member of
size at most `S` (`IsCliqueCover`). The family of all maximal cliques is one (`maximalCliques`).

The **connector** `G'` (Section 2) splits every clique `Q ∈ 𝒬` into consecutive blocks of `t`
vertices (by identifier) and joins two vertices iff they lie in the same block of some `Q`.

## Main results

* `ncard_neighborSet_le_of_isCliqueCover`: a clique cover gives max degree `≤ D · (S - 1)`.
* `connector_degree_le` (**Lemma 2.1**): the connector has max degree `≤ D · (t - 1)`.
* `isCliqueCover_refine` (**Lemmas 2.2 and 2.3**): for a proper colouring `φ` of the connector,
  the colour-class subgraphs `G_i` (all together: `sameColor G φ`) have the clique cover
  `refine 𝒬 φ` with diversity `≤ D` and clique size `≤ ⌈S/t⌉`; hence max degree
  `≤ D · (⌈S/t⌉ - 1)` (`lemma_2_2`).
* `diversity_sameColor_le` (**Lemma 2.3 (ii)** for maximal cliques): the diversity of an induced
  subgraph is at most the diversity of the graph.
-/

open Finset

namespace Podc.DeltaEdgeColoring

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Black-box vertex colouring -/

/-- Specification of the `(Δ+1)`-vertex-colouring subroutine (the algorithm of
Fraigniaud–Heinrich–Kosowski [17] used in lines 3 and 12 of Algorithm 1): called on a graph `H` and
a degree bound `Δ` that is valid for `H`, it returns a proper colouring with colours `0, …, Δ`. -/
def IsDeltaColorer (col : SimpleGraph V → ℕ → V → ℕ) : Prop :=
  ∀ (H : SimpleGraph V) (Δ : ℕ), (∀ v, (H.neighborSet v).ncard ≤ Δ) →
    (∀ ⦃u v⦄, H.Adj u v → col H Δ u ≠ col H Δ v) ∧ ∀ v, col H Δ v ≤ Δ

/-! ### Clique covers -/

/-- A clique cover of `G` (a "consistent identification" of cliques): every member is a clique,
every edge lies in some member, every vertex lies in at most `D` members (diversity `≤ D`), and
every member has at most `S` vertices. -/
structure IsCliqueCover (G : SimpleGraph V) (𝒬 : Finset (Finset V)) (D S : ℕ) : Prop where
  isClique : ∀ Q ∈ 𝒬, G.IsClique (Q : Set V)
  cover : ∀ ⦃u v⦄, G.Adj u v → ∃ Q ∈ 𝒬, u ∈ Q ∧ v ∈ Q
  diversity : ∀ v, #{Q ∈ 𝒬 | v ∈ Q} ≤ D
  card_le : ∀ Q ∈ 𝒬, #Q ≤ S

/-- Every nonempty clique of `G` is contained in a member of `𝒬` (true for the family of all
maximal cliques). Then the clique size of `G` is bounded by the sizes of the members. -/
def CoversCliques (G : SimpleGraph V) (𝒬 : Finset (Finset V)) : Prop :=
  ∀ K : Finset V, K.Nonempty → G.IsClique (K : Set V) → ∃ Q ∈ 𝒬, K ⊆ Q

lemma CoversCliques.card_le {G : SimpleGraph V} {𝒬 : Finset (Finset V)} {D S : ℕ}
    (h : CoversCliques G 𝒬) (hc : IsCliqueCover G 𝒬 D S) {K : Finset V}
    (hK : G.IsClique (K : Set V)) : #K ≤ S := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨Q, hQ, hKQ⟩ := h K hne hK
  exact (card_le_card hKQ).trans (hc.card_le Q hQ)

/-- The neighbours of `v` lie in the members of `𝒬` containing `v`. -/
lemma neighborSet_subset {G : SimpleGraph V} {𝒬 : Finset (Finset V)} {D S : ℕ}
    (hc : IsCliqueCover G 𝒬 D S) (v : V) :
    G.neighborSet v ⊆ ↑(({Q ∈ 𝒬 | v ∈ Q}).biUnion fun Q => Q.erase v) := by
  intro u hu
  obtain ⟨Q, hQ, hv, hu'⟩ := hc.cover hu
  simp only [coe_biUnion, coe_filter, Set.mem_iUnion, Set.mem_ofPred_eq, coe_erase,
    Set.mem_sdiff, mem_coe, Set.mem_singleton_iff, exists_prop]
  exact ⟨Q, ⟨hQ, hv⟩, hu', (G.ne_of_adj hu).symm⟩

/-- A graph with a clique cover of diversity `D` and clique size `S` has max degree
`≤ D · (S - 1)` (used in Lemma 2.2, Theorem 2.6 and line 12 of Algorithm 1). -/
lemma ncard_neighborSet_le_of_isCliqueCover {G : SimpleGraph V} {𝒬 : Finset (Finset V)}
    {D S : ℕ} (hc : IsCliqueCover G 𝒬 D S) (v : V) :
    (G.neighborSet v).ncard ≤ D * (S - 1) := by
  refine (Set.ncard_le_ncard (neighborSet_subset hc v) (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  refine card_biUnion_le.trans ?_
  calc ∑ Q ∈ 𝒬 with v ∈ Q, #(Q.erase v) ≤ ∑ Q ∈ 𝒬 with v ∈ Q, (S - 1) := by
        refine sum_le_sum fun Q hQ => ?_
        rw [mem_filter] at hQ
        rw [card_erase_of_mem hQ.2]
        exact Nat.sub_le_sub_right (hc.card_le Q hQ.1) 1
    _ = #{Q ∈ 𝒬 | v ∈ Q} * (S - 1) := by rw [sum_const, smul_eq_mul]
    _ ≤ D * (S - 1) := Nat.mul_le_mul_right _ (hc.diversity v)

/-! ### Maximal cliques -/

open Classical in
/-- The family of all maximal cliques of `G`. -/
noncomputable def maximalCliques (G : SimpleGraph V) : Finset (Finset V) :=
  univ.filter fun Q => Maximal (fun K : Finset V => G.IsClique (K : Set V)) Q

open Classical in
/-- The diversity of `v` in `G`: the number of maximal cliques containing `v`. -/
noncomputable def diversity (G : SimpleGraph V) (v : V) : ℕ :=
  #{Q ∈ maximalCliques G | v ∈ Q}

lemma mem_maximalCliques {G : SimpleGraph V} {Q : Finset V} :
    Q ∈ maximalCliques G ↔ Maximal (fun K : Finset V => G.IsClique (K : Set V)) Q := by
  classical
  simp [maximalCliques]

/-- Every clique is contained in a maximal clique. -/
lemma exists_maximal_clique {G : SimpleGraph V} {K : Finset V} (hK : G.IsClique (K : Set V)) :
    ∃ Q ∈ maximalCliques G, K ⊆ Q := by
  obtain ⟨Q, hKQ, hQ⟩ := (Set.toFinite {K' : Finset V | G.IsClique (K' : Set V)}).exists_le_maximal
    (a := K) hK
  exact ⟨Q, mem_maximalCliques.2 hQ, hKQ⟩

lemma coversCliques_maximalCliques (G : SimpleGraph V) : CoversCliques G (maximalCliques G) :=
  fun _ _ hK => exists_maximal_clique hK

/-- The maximal cliques form a clique cover with diversity `D` (if every vertex has diversity at
most `D`) and clique size `S` (if every clique has at most `S` vertices). -/
lemma isCliqueCover_maximalCliques {G : SimpleGraph V} {D S : ℕ}
    (hD : ∀ v, diversity G v ≤ D) (hS : ∀ K : Finset V, G.IsClique (K : Set V) → #K ≤ S) :
    IsCliqueCover G (maximalCliques G) D S where
  isClique Q hQ := (mem_maximalCliques.1 hQ).prop
  cover u v huv := by
    have hK : G.IsClique (({u, v} : Finset V) : Set V) := by
      rw [coe_pair]; exact SimpleGraph.isClique_pair.2 fun _ => huv
    obtain ⟨Q, hQ, hsub⟩ := exists_maximal_clique hK
    exact ⟨Q, hQ, hsub (by simp), hsub (by simp)⟩
  diversity v := by classical exact hD v
  card_le Q hQ := hS Q (mem_maximalCliques.1 hQ).prop

/-! ### Colour classes -/

/-- The union of the colour-class subgraphs `G_i = G[φ⁻¹(i)]` (all classes processed "in
parallel"): `u ~ v` iff `u ~_G v` and `φ u = φ v`. -/
def sameColor (G : SimpleGraph V) (φ : V → ℕ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ φ u = φ v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

@[simp] lemma sameColor_adj {G : SimpleGraph V} {φ : V → ℕ} {u v : V} :
    (sameColor G φ).Adj u v ↔ G.Adj u v ∧ φ u = φ v := Iff.rfl

/-- The clique cover of the colour classes: the traces `Q ∩ φ⁻¹(i)` of the members of `𝒬`. -/
def refine (𝒬 : Finset (Finset V)) (φ : V → ℕ) : Finset (Finset V) :=
  𝒬.biUnion fun Q => Q.image fun v => Q.filter (φ · = φ v)

lemma mem_refine {𝒬 : Finset (Finset V)} {φ : V → ℕ} {R : Finset V} :
    R ∈ refine 𝒬 φ ↔ ∃ Q ∈ 𝒬, ∃ v ∈ Q, Q.filter (φ · = φ v) = R := by
  simp [refine]

/-- **Lemma 2.3 (ii)**, for maximal cliques: the diversity of `v` in the colour class
`G[φ⁻¹(φ v)]` is at most its diversity in `G`. -/
lemma diversity_sameColor_le (G : SimpleGraph V) (φ : V → ℕ) (v : V) :
    diversity (sameColor G φ) v ≤ diversity G v := by
  classical
  unfold diversity
  refine le_trans (card_le_card ?_) (card_image_le (f := fun Q : Finset V => Q.filter (φ · = φ v))
    (s := {Q ∈ maximalCliques G | v ∈ Q}))
  intro C hC
  simp only [mem_filter, mem_maximalCliques] at hC
  obtain ⟨hCmax, hvC⟩ := hC
  -- all vertices of `C` have colour `φ v`
  have hcol : ∀ w ∈ C, φ w = φ v := by
    intro w hw
    by_cases hwv : w = v
    · rw [hwv]
    · exact ((hCmax.prop (mem_coe.2 hw) (mem_coe.2 hvC) hwv)).2
  have hCG : G.IsClique (C : Set V) := fun a ha b hb hab => (hCmax.prop ha hb hab).1
  obtain ⟨Q, hQ, hCQ⟩ := exists_maximal_clique hCG
  have hQG := (mem_maximalCliques.1 hQ).prop
  -- `Q ∩ φ⁻¹(φ v)` is a clique of the colour class containing `C`, hence equal to `C`
  have hEq : Q.filter (φ · = φ v) = C := by
    refine (hCmax.eq_of_le (y := Q.filter (φ · = φ v)) ?_ ?_).symm
    · intro a ha b hb hab
      simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
      exact ⟨hQG ha.1 hb.1 hab, ha.2.trans hb.2.symm⟩
    · intro w hw
      exact mem_filter.2 ⟨hCQ hw, hcol w hw⟩
  simp only [mem_image, mem_filter]
  exact ⟨Q, ⟨hQ, hCQ hvC⟩, hEq⟩

/-! ### The connector -/

/-- The rank of `v` in `Q` by identifier: the number of members of `Q` with a smaller ID. -/
def rank [LinearOrder V] (Q : Finset V) (v : V) : ℕ := #{u ∈ Q | u < v}

/-- The block of `v` in `Q`: `Q` is split into consecutive blocks `V_1, V_2, …` of `t` vertices
each (by identifier), the last one possibly smaller. -/
def block [LinearOrder V] (t : ℕ) (Q : Finset V) (v : V) : ℕ := rank Q v / t

variable [LinearOrder V]

lemma rank_lt_card {Q : Finset V} {v : V} (hv : v ∈ Q) : rank Q v < #Q := by
  unfold rank
  refine card_lt_card ⟨filter_subset _ _, fun h => ?_⟩
  simpa using h hv

lemma rank_injOn (Q : Finset V) : Set.InjOn (rank Q) (Q : Set V) := by
  intro u hu v hv huv
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : rank Q u < rank Q v := by
      refine card_lt_card ⟨fun w hw => ?_, fun hsub => ?_⟩
      · simp only [mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.trans h⟩
      · have := hsub (show u ∈ {w ∈ Q | w < v} by simp [mem_coe.1 hu, h])
        simp at this
    omega
  · have : rank Q v < rank Q u := by
      refine card_lt_card ⟨fun w hw => ?_, fun hsub => ?_⟩
      · simp only [mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.trans h⟩
      · have := hsub (show v ∈ {w ∈ Q | w < u} by simp [mem_coe.1 hv, h])
        simp at this
    omega

/-- Every block has at most `t` vertices. -/
lemma card_block_le {t : ℕ} (ht : 0 < t) (Q : Finset V) (i : ℕ) :
    #{u ∈ Q | block t Q u = i} ≤ t := by
  have hmaps : Set.MapsTo (rank Q) ({u ∈ Q | block t Q u = i} : Finset V) (Ico (i * t) (i * t + t)) := by
    intro u hu
    have hu' : u ∈ Q ∧ rank Q u / t = i := mem_filter.1 (mem_coe.1 hu)
    simp only [coe_Ico, Set.mem_Ico]
    have h1 := Nat.div_add_mod (rank Q u) t
    have h2 := Nat.mod_lt (rank Q u) ht
    rw [hu'.2, Nat.mul_comm] at h1
    constructor <;> omega
  have := card_le_card_of_injOn (rank Q) hmaps ((rank_injOn Q).mono (fun x hx => by
    exact mem_coe.2 (mem_filter.1 (mem_coe.1 hx)).1))
  simpa using this

/-- The blocks of `Q` are indexed by `0, …, ⌈|Q|/t⌉ - 1`. -/
lemma block_lt {t : ℕ} (ht : 0 < t) {Q : Finset V} {v : V} (hv : v ∈ Q) :
    block t Q v < #Q ⌈/⌉ t := by
  unfold block
  have h1 := rank_lt_card hv
  have h2 : #Q ≤ t * (#Q ⌈/⌉ t) := le_smul_ceilDiv ht
  rw [Nat.div_lt_iff_lt_mul ht]
  nlinarith

/-- The connector `G'` of `𝒬` with parameter `t`: `u ~ v` iff they lie in the same block of some
member of `𝒬`. -/
def connector (t : ℕ) (𝒬 : Finset (Finset V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ Q ∈ 𝒬, u ∈ Q ∧ v ∈ Q ∧ block t Q u = block t Q v
  symm := ⟨fun _ _ h => ⟨h.1.symm, by
    obtain ⟨Q, hQ, hu, hv, hb⟩ := h.2
    exact ⟨Q, hQ, hv, hu, hb.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **Lemma 2.1.** The connector has max degree at most `D · (t - 1)`. -/
theorem connector_degree_le {G : SimpleGraph V} {𝒬 : Finset (Finset V)} {D S t : ℕ} (ht : 0 < t)
    (hc : IsCliqueCover G 𝒬 D S) (v : V) :
    ((connector t 𝒬).neighborSet v).ncard ≤ D * (t - 1) := by
  have hsub : (connector t 𝒬).neighborSet v ⊆
      ↑(({Q ∈ 𝒬 | v ∈ Q}).biUnion fun Q => ({u ∈ Q | block t Q u = block t Q v}).erase v) := by
    intro u hu
    obtain ⟨hne, Q, hQ, hv, hu', hb⟩ := hu
    simp only [coe_biUnion, coe_filter, Set.mem_iUnion, Set.mem_ofPred_eq, coe_erase,
      Set.mem_sdiff, Set.mem_singleton_iff, exists_prop]
    exact ⟨Q, ⟨hQ, hv⟩, ⟨hu', hb.symm⟩, hne.symm⟩
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  refine card_biUnion_le.trans ?_
  calc ∑ Q ∈ 𝒬 with v ∈ Q, #(({u ∈ Q | block t Q u = block t Q v}).erase v)
        ≤ ∑ Q ∈ 𝒬 with v ∈ Q, (t - 1) := by
        refine sum_le_sum fun Q hQ => ?_
        rw [mem_filter] at hQ
        rw [card_erase_of_mem (by simp [hQ.2])]
        exact Nat.sub_le_sub_right (card_block_le ht Q _) 1
    _ = #{Q ∈ 𝒬 | v ∈ Q} * (t - 1) := by rw [sum_const, smul_eq_mul]
    _ ≤ D * (t - 1) := Nat.mul_le_mul_right _ (hc.diversity v)

/-- **Lemmas 2.2 and 2.3.** If `φ` is a proper colouring of the connector, then the colour classes
(`sameColor G φ`) have the clique cover `refine 𝒬 φ` with diversity `≤ D` and clique size
`≤ ⌈S/t⌉`: inside a clique `Q`, the vertices of one colour lie in distinct blocks. -/
theorem isCliqueCover_refine {G : SimpleGraph V} {𝒬 : Finset (Finset V)} {D S t : ℕ}
    (ht : 0 < t) (hc : IsCliqueCover G 𝒬 D S) {φ : V → ℕ}
    (hφ : ∀ ⦃u v⦄, (connector t 𝒬).Adj u v → φ u ≠ φ v) :
    IsCliqueCover (sameColor G φ) (refine 𝒬 φ) D (S ⌈/⌉ t) where
  isClique R hR := by
    obtain ⟨Q, hQ, w, -, rfl⟩ := mem_refine.1 hR
    intro a ha b hb hab
    simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
    exact ⟨hc.isClique Q hQ ha.1 hb.1 hab, ha.2.trans hb.2.symm⟩
  cover u v huv := by
    obtain ⟨Q, hQ, hu, hv⟩ := hc.cover huv.1
    exact ⟨Q.filter (φ · = φ u), mem_refine.2 ⟨Q, hQ, u, hu, rfl⟩, by simp [hu],
      by simp [hv, huv.2]⟩
  diversity v := by
    refine le_trans (card_le_card ?_) ((card_image_le (f := fun Q : Finset V =>
      Q.filter (φ · = φ v)) (s := {Q ∈ 𝒬 | v ∈ Q})).trans (hc.diversity v))
    intro R hR
    simp only [mem_filter] at hR
    obtain ⟨Q, hQ, w, -, rfl⟩ := mem_refine.1 hR.1
    simp only [mem_filter] at hR
    simp only [mem_image, mem_filter]
    exact ⟨Q, ⟨hQ, hR.2.1⟩, by rw [hR.2.2]⟩
  card_le R hR := by
    obtain ⟨Q, hQ, w, -, rfl⟩ := mem_refine.1 hR
    have hmaps : Set.MapsTo (block t Q) (Q.filter (φ · = φ w) : Finset V) (range (#Q ⌈/⌉ t)) := by
      intro u hu
      simp only [coe_filter, Set.mem_ofPred_eq] at hu
      simpa using block_lt ht hu.1
    have hinj : Set.InjOn (block t Q) (Q.filter (φ · = φ w) : Finset V) := by
      intro a ha b hb hab
      simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
      by_contra hne
      exact hφ ⟨hne, Q, hQ, ha.1, hb.1, hab⟩ (ha.2.trans hb.2.symm)
    refine (card_le_card_of_injOn _ hmaps hinj).trans ?_
    rw [card_range]
    exact Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right (hc.card_le Q hQ) _) _)

/-- **Lemma 2.2.** Every colour class `G_i` has max degree at most `D · (⌈S/t⌉ - 1)`. -/
theorem lemma_2_2 {G : SimpleGraph V} {𝒬 : Finset (Finset V)} {D S t : ℕ}
    (ht : 0 < t) (hc : IsCliqueCover G 𝒬 D S) {φ : V → ℕ}
    (hφ : ∀ ⦃u v⦄, (connector t 𝒬).Adj u v → φ u ≠ φ v) (v : V) :
    ((sameColor G φ).neighborSet v).ncard ≤ D * (S ⌈/⌉ t - 1) :=
  ncard_neighborSet_le_of_isCliqueCover (isCliqueCover_refine ht hc hφ) v

/-- The refined cover still contains every clique of the colour classes. -/
lemma CoversCliques.refine {G : SimpleGraph V} {𝒬 : Finset (Finset V)} (h : CoversCliques G 𝒬)
    (φ : V → ℕ) : CoversCliques (sameColor G φ) (refine 𝒬 φ) := by
  intro K hne hK
  obtain ⟨w, hw⟩ := hne
  have hKG : G.IsClique (K : Set V) := fun a ha b hb hab => (hK ha hb hab).1
  obtain ⟨Q, hQ, hKQ⟩ := h K ⟨w, hw⟩ hKG
  refine ⟨Q.filter (φ · = φ w), mem_refine.2 ⟨Q, hQ, w, hKQ hw, rfl⟩, fun u hu => ?_⟩
  simp only [mem_filter]
  refine ⟨hKQ hu, ?_⟩
  by_cases huw : u = w
  · rw [huw]
  · exact (hK (mem_coe.2 hu) (mem_coe.2 hw) huw).2

/-- **Lemma 2.3 (i).** Every clique of a colour class `G_i` has at most `⌈S/t⌉` vertices (when `𝒬`
contains every clique, e.g. for the maximal cliques). -/
theorem lemma_2_3_i {G : SimpleGraph V} {𝒬 : Finset (Finset V)} {D S t : ℕ}
    (ht : 0 < t) (hc : IsCliqueCover G 𝒬 D S) (hall : CoversCliques G 𝒬) {φ : V → ℕ}
    (hφ : ∀ ⦃u v⦄, (connector t 𝒬).Adj u v → φ u ≠ φ v) {K : Finset V}
    (hK : (sameColor G φ).IsClique (K : Set V)) : #K ≤ S ⌈/⌉ t :=
  (hall.refine φ).card_le (isCliqueCover_refine ht hc hφ) hK

end Podc.DeltaEdgeColoring
