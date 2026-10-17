import Papers.PODC2022.DominatingSetArboricity.Basic

/-!
# The lower bound reduction (Theorem 1.4, Section 5)

Theorem 1.4 reduces the Kuhn–Moscibroda–Wattenhofer (KMW) lower bound for approximating the
minimum *fractional vertex cover* (MFVC) to approximating the minimum dominating set (MDS) on
graphs of arboricity `2`. The KMW lower bound itself (an `Ω(log Δ / log log Δ)`-round bound for
polylogarithmic MFVC approximation in LOCAL) is **not** formalized; we formalize the combinatorial
content of the reduction:

* the graph `H = lbGraph G K` (`K` copies of `G` with every edge subdivided by a "middle" node,
  plus one node `t_u` per vertex `u` of `G`, adjacent to all copies of `u`);
* `lbGraph_arboricityLE_two`: `H` has arboricity at most `2`;
* `lbGraph_degree_le`: every degree of `H` is at most `max K (max (Δ+1) 2)` (so `Δ_H = Δ²` for the
  paper's `K = Δ² ≥ Δ + 1`, `Δ ≥ 2`);
* `exists_dominating_lbGraph`: `OPT_MDS(H) ≤ K · |C| + n` for every vertex cover `C` of `G`;
* `fracCover_of_dominating`: every dominating set `S` of `H` yields a fractional vertex cover `y`
  of `G` (computed locally: `y_u` is the number of copies `i` such that the copy of `u` in `S`
  or a middle node of `S` was "moved" to `u`, divided by `K`) with `∑ y ≤ |S| / K`;
* `host_adj`/`edist_host_le`: the simulation map `H → G` sends adjacent nodes to equal or adjacent
  nodes, so `R` rounds on `H` are simulated by `R` rounds on `G`;
* `reduction`: if `S` is a `c`-approximate dominating set of `H` with `K = Δ²` and `G` has no
  isolated vertices, then `y` is a `2c(1 + 1/Δ)`-approximate fractional vertex cover of `G`.
  (The paper gets `c(1 + 1/Δ)` using that the KMW graph is bipartite and has `m ≥ n`; we use the
  general facts `OPT_VC ≤ 2 OPT_FVC` and `n ≤ (Δ+1) · ∑ z` (no isolated vertices), as suggested in the paper's footnote 3.)
-/

set_option linter.unusedSectionVars false

namespace DominatingSetArboricity

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Nodes of the lower-bound graph `H`. -/
inductive LBNode (V E : Type*) (K : ℕ)
  /-- the copy of `u` in the `i`-th copy of `G` -/
  | copy : Fin K → V → LBNode V E K
  /-- the middle node of edge `e` in the `i`-th copy of `G` -/
  | mid : Fin K → E → LBNode V E K
  /-- the extra node `t_u` -/
  | tn : V → LBNode V E K
  deriving DecidableEq

namespace LBNode

variable {E : Type*} {K : ℕ}

/-- `LBNode V E K ≃ (Fin K × V) ⊕ (Fin K × E) ⊕ V`. -/
def equivSum : LBNode V E K ≃ (Fin K × V) ⊕ (Fin K × E) ⊕ V where
  toFun
    | copy i u => .inl (i, u)
    | mid i e => .inr (.inl (i, e))
    | tn u => .inr (.inr u)
  invFun
    | .inl (i, u) => copy i u
    | .inr (.inl (i, e)) => mid i e
    | .inr (.inr u) => tn u
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨i, u⟩ | ⟨i, e⟩ | u <;> rfl

instance [Fintype E] : Fintype (LBNode V E K) := Fintype.ofEquiv _ equivSum.symm

end LBNode

open LBNode

/-- The (oriented) edge relation of `H`. -/
def lbRel (K : ℕ) : LBNode V G.edgeSet K → LBNode V G.edgeSet K → Prop
  | copy _ u, tn u' => u = u'
  | mid i e, copy j u => i = j ∧ u ∈ (e : Sym2 V)
  | _, _ => False

/-- The lower-bound graph `H`. -/
def lbGraph (K : ℕ) : SimpleGraph (LBNode V G.edgeSet K) := SimpleGraph.fromRel (lbRel G K)

noncomputable instance (K : ℕ) : DecidableRel (lbGraph G K).Adj := Classical.decRel _

variable {G}

theorem lbGraph_adj {K : ℕ} {a b : LBNode V G.edgeSet K} :
    (lbGraph G K).Adj a b ↔ a ≠ b ∧ (lbRel G K a b ∨ lbRel G K b a) := Iff.rfl

/-! ### Arboricity -/

/-- The orientation: middle nodes point to their two endpoints, copies point to `t_u`. -/
noncomputable def lbOut {K : ℕ} : LBNode V G.edgeSet K → Finset (LBNode V G.edgeSet K)
  | copy _ u => {tn u}
  | mid i e => (univ.filter fun a => a ∈ (e : Sym2 V)).image (copy i)
  | tn _ => ∅

theorem card_filter_mem_sym2_le_two (e : Sym2 V) : (univ.filter fun a => a ∈ e).card ≤ 2 := by
  rw [show (univ.filter fun a => a ∈ e) = e.toFinset by ext; simp, Sym2.card_toFinset]
  split <;> omega

theorem mem_lbOut {K : ℕ} {a b : LBNode V G.edgeSet K} : b ∈ lbOut a ↔ lbRel G K a b := by
  cases a <;> cases b <;> (simp [lbOut, lbRel, eq_comm]; try tauto)

/-- An orientation of `H` with out-degree `≤ 2`. -/
noncomputable def lbOrientation (K : ℕ) : (lbGraph G K).OutOrientation 2 where
  out := lbOut
  adj_of_mem {a b} h := by
    rw [mem_lbOut] at h
    refine ⟨fun hab => ?_, Or.inl h⟩
    subst hab; cases a <;> simp [lbRel] at h
  mem_or_mem {a b} h := by
    rcases h.2 with h | h
    · exact Or.inl (mem_lbOut.2 h)
    · exact Or.inr (mem_lbOut.2 h)
  card_out_le a := by
    cases a with
    | copy i u => simp [lbOut]
    | mid i e => exact card_image_le.trans (card_filter_mem_sym2_le_two _)
    | tn u => simp [lbOut]

/-- A rank strictly decreasing along the orientation (`mid > copy > t`). -/
def lbRank {K : ℕ} : LBNode V G.edgeSet K → ℕ
  | copy _ _ => 1
  | mid _ _ => 2
  | tn _ => 0

/-- `H` has arboricity at most `2`. -/
theorem lbGraph_arboricityLE_two (K : ℕ) : (lbGraph G K).ArboricityLE 2 :=
  (lbOrientation K).arboricityLE_of_rank lbRank fun a b h => by
    have := mem_lbOut.1 h
    cases a <;> cases b <;> simp_all [lbRel, lbRank]

/-! ### Upper bound on `OPT_MDS(H)` -/

variable (G) in
/-- A vertex cover (Mathlib's `SimpleGraph.IsVertexCover` for a `Finset`). -/
abbrev IsVertexCover (C : Finset V) : Prop := G.IsVertexCover ↑C

variable (G) in
/-- A fractional vertex cover. -/
def IsFracVertexCover (y : V → ℝ) : Prop :=
  (∀ u, 0 ≤ y u) ∧ ∀ ⦃u v⦄, G.Adj u v → 1 ≤ y u + y v

/-- `T ∪ ⋃_i C_i` is a dominating set of `H`; hence `OPT_MDS(H) ≤ K · OPT_VC(G) + n`
(inequality (2) of the paper). -/
theorem exists_dominating_lbGraph (K : ℕ) {C : Finset V} (hC : IsVertexCover G C) :
    ∃ D : Finset (LBNode V G.edgeSet K), IsDominating (lbGraph G K) D ∧
      D.card ≤ K * C.card + Fintype.card V := by
  classical
  refine ⟨(univ ×ˢ C).image (fun p => copy p.1 p.2) ∪ univ.image tn, fun a => ?_, ?_⟩
  · cases a with
    | copy i u =>
      exact ⟨tn u, mem_union_right _ (mem_image_of_mem _ (mem_univ _)),
        mem_cnbr.2 (Or.inr ⟨by simp, Or.inl rfl⟩)⟩
    | tn u => exact ⟨tn u, mem_union_right _ (mem_image_of_mem _ (mem_univ _)), self_mem_cnbr _⟩
    | mid i e =>
      obtain ⟨e, he⟩ := e
      induction e using Sym2.ind with
      | h a b =>
        have hab : G.Adj a b := he
        rcases hC hab with h | h <;> rw [Finset.mem_coe] at h
        · exact ⟨copy i a, mem_union_left _ (mem_image.2 ⟨(i, a), by simp [h], rfl⟩),
            mem_cnbr.2 (Or.inr ⟨by simp, Or.inl ⟨rfl, by simp⟩⟩)⟩
        · exact ⟨copy i b, mem_union_left _ (mem_image.2 ⟨(i, b), by simp [h], rfl⟩),
            mem_cnbr.2 (Or.inr ⟨by simp, Or.inl ⟨rfl, by simp⟩⟩)⟩
  · refine (card_union_le _ _).trans (add_le_add ?_ ?_)
    · exact card_image_le.trans (by simp)
    · exact card_image_le.trans (by simp)

/-! ### From dominating sets of `H` to fractional vertex covers of `G` -/

/-- An endpoint of an edge (where a middle node of the dominating set is moved). -/
noncomputable def pick (e : Sym2 V) : V := (Quot.out e).1

theorem pick_mem (e : Sym2 V) : pick e ∈ e := by
  unfold pick
  generalize hq : Quot.out e = q
  have : e = s(q.1, q.2) := by rw [← hq]; exact (Quot.out_eq e).symm
  rw [this]; exact Sym2.mem_mk_left _ _

/-- The simulation map `H → G`: every node of `H` is simulated by a node of `G`. -/
noncomputable def host {K : ℕ} : LBNode V G.edgeSet K → V
  | copy _ u => u
  | mid _ e => pick (e : Sym2 V)
  | tn u => u

/-- `S_i`: the vertex cover of the `i`-th copy obtained from `S` (middle nodes moved to an
endpoint). -/
noncomputable def coverOf {K : ℕ} (S : Finset (LBNode V G.edgeSet K)) (i : Fin K) : Finset V :=
  univ.filter fun u => copy i u ∈ S ∨ ∃ e, mid i e ∈ S ∧ pick (e : Sym2 V) = u

/-- `y_u = |{i : u ∈ S_i}| / K`. -/
noncomputable def fracOf {K : ℕ} (S : Finset (LBNode V G.edgeSet K)) (u : V) : ℝ :=
  ((univ.filter fun i => u ∈ coverOf S i).card : ℝ) / K

theorem isVertexCover_coverOf {K : ℕ} {S : Finset (LBNode V G.edgeSet K)}
    (hS : IsDominating (lbGraph G K) S) (i : Fin K) : IsVertexCover G (coverOf S i) := by
  intro a b hab
  obtain ⟨z, hzS, hz⟩ := hS (mid i ⟨s(a, b), hab⟩)
  rcases mem_cnbr.1 hz with rfl | hz
  · have hp := pick_mem s(a, b)
    rcases Sym2.mem_iff.1 hp with h | h
    · exact Or.inl (by simp [coverOf]; exact Or.inr ⟨_, ⟨hab, hzS⟩, h⟩)
    · exact Or.inr (by simp [coverOf]; exact Or.inr ⟨_, ⟨hab, hzS⟩, h⟩)
  · rcases hz.2 with h | h
    · cases z <;> simp [lbRel] at h
      obtain ⟨rfl, hc⟩ := h
      rcases hc with rfl | rfl
      · exact Or.inl (by simp [coverOf, hzS])
      · exact Or.inr (by simp [coverOf, hzS])
    · cases z <;> simp [lbRel] at h

theorem sum_card_coverOf_le {K : ℕ} (S : Finset (LBNode V G.edgeSet K)) :
    ∑ i, (coverOf S i).card ≤ S.card := by
  classical
  let g : LBNode V G.edgeSet K → Option (Fin K × V)
    | copy i u => some (i, u)
    | mid i e => some (i, pick (e : Sym2 V))
    | tn _ => none
  let P : Finset (Fin K × V) := univ.filter fun p => p.2 ∈ coverOf S p.1
  have hP : P.image some ⊆ S.image g := by
    intro x hx
    obtain ⟨⟨i, u⟩, hp, rfl⟩ := mem_image.1 hx
    simp only [P, coverOf, mem_filter, mem_univ, true_and] at hp
    rcases hp with h | ⟨e, he, rfl⟩
    · exact mem_image.2 ⟨copy i u, h, rfl⟩
    · exact mem_image.2 ⟨mid i e, he, rfl⟩
  have h1 : P.card ≤ S.card := by
    rw [← card_image_of_injective P (Option.some_injective _)]
    exact (card_le_card hP).trans card_image_le
  have h2 : ∑ i, (coverOf S i).card = P.card := by
    rw [card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => ?_
    show _ = ∑ y, if y ∈ coverOf S i then 1 else 0
    rw [card_eq_sum_ones, sum_ite_mem, univ_inter]
  omega

/-- Every dominating set `S` of `H` gives a fractional vertex cover `y` of `G` with
`∑ y ≤ |S| / K` (for `K ≥ 1`). -/
theorem fracCover_of_dominating {K : ℕ} (hK : 1 ≤ K) {S : Finset (LBNode V G.edgeSet K)}
    (hS : IsDominating (lbGraph G K) S) :
    IsFracVertexCover G (fracOf S) ∧ ∑ u, fracOf S u ≤ S.card / K := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  refine ⟨⟨fun u => by unfold fracOf; positivity, fun a b hab => ?_⟩, ?_⟩
  · unfold fracOf
    rw [← add_div, le_div_iff₀ hK', one_mul]
    have : (univ : Finset (Fin K)) ⊆ (univ.filter fun i => a ∈ coverOf S i) ∪
        (univ.filter fun i => b ∈ coverOf S i) := by
      intro i _
      rcases isVertexCover_coverOf hS i hab with h | h <;> simp [Finset.mem_coe.1 h]
    have := (card_le_card this).trans (card_union_le _ _)
    simp only [card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  · unfold fracOf
    rw [← sum_div, div_le_div_iff_of_pos_right hK']
    have h := sum_card_coverOf_le S
    have : ∑ u, (univ.filter fun i => u ∈ coverOf S i).card = ∑ i, (coverOf S i).card := by
      simp only [card_eq_sum_ones, sum_filter]
      rw [sum_comm]
      simp [coverOf]
    exact_mod_cast this ▸ h

/-! ### Locality of the simulation -/

/-- Adjacent nodes of `H` are simulated by equal or adjacent nodes of `G`. -/
theorem host_adj {K : ℕ} {a b : LBNode V G.edgeSet K} (h : (lbGraph G K).Adj a b) :
    host a = host b ∨ G.Adj (host a) (host b) := by
  have key : ∀ {a b : LBNode V G.edgeSet K}, lbRel G K a b →
      host a = host b ∨ G.Adj (host a) (host b) := by
    intro a b h
    cases a <;> cases b <;> simp only [lbRel] at h
    · exact Or.inl h
    · rename_i i e j u
      obtain ⟨-, hu⟩ := h
      obtain ⟨e, he⟩ := e
      simp only [host]
      by_cases hpu : pick e = u
      · exact Or.inl hpu
      · right
        have hp := pick_mem e
        induction e using Sym2.ind with
        | h x y =>
          have hxy : G.Adj x y := he
          rcases Sym2.mem_iff.1 hp with h1 | h1 <;> rcases Sym2.mem_iff.1 hu with h2 | h2 <;>
            simp_all [G.adj_comm]
  rcases h.2 with h | h
  · exact key h
  · rcases key h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm

/-- Distances do not increase under the simulation map, so the radius-`R` view of a node of `H`
is contained in the radius-`R` view of its simulating node in `G`. -/
theorem edist_host_le {K : ℕ} (a b : LBNode V G.edgeSet K) :
    G.edist (host a) (host b) ≤ (lbGraph G K).edist a b := by
  suffices ∀ {a b : LBNode V G.edgeSet K} (p : (lbGraph G K).Walk a b),
      ∃ q : G.Walk (host a) (host b), q.length ≤ p.length by
    by_cases h : (lbGraph G K).Reachable a b
    · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_edist
      obtain ⟨q, hq⟩ := this p
      rw [← hp]
      exact (edist_le q).trans (by exact_mod_cast hq)
    · rw [edist_eq_top_of_not_reachable h]; exact le_top
  intro a b p
  induction p with
  | nil => exact ⟨Walk.nil, le_rfl⟩
  | cons hab p ih =>
    obtain ⟨q, hq⟩ := ih
    rcases host_adj hab with h | h
    · exact ⟨q.copy h.symm rfl, by simp; omega⟩
    · exact ⟨Walk.cons h q, by simp; omega⟩

/-! ### Degrees of `H` -/

theorem lbGraph_degree_le (K : ℕ) (a : LBNode V G.edgeSet K) :
    (lbGraph G K).degree a ≤ max K (max (G.maxDegree + 1) 2) := by
  classical
  rw [← card_neighborFinset_eq_degree]
  cases a with
  | tn u =>
    have : (lbGraph G K).neighborFinset (tn u) ⊆ univ.image fun i => copy i u := by
      intro b hb
      rw [mem_neighborFinset, lbGraph_adj] at hb
      cases b <;> simp_all [lbRel]
    exact (card_le_card this).trans (card_image_le.trans (by simp))
  | mid i e =>
    have : (lbGraph G K).neighborFinset (mid i e) ⊆
        (univ.filter fun a => a ∈ (e : Sym2 V)).image (copy i) := by
      intro b hb
      rw [mem_neighborFinset, lbGraph_adj] at hb
      cases b <;> simp_all [lbRel]
    exact (card_le_card this).trans (card_image_le.trans
      ((card_filter_mem_sym2_le_two _).trans (by omega)))
  | copy i u =>
    have : (lbGraph G K).neighborFinset (copy i u) ⊆
        insert (tn u) ((G.incidenceFinset u).attach.image fun e =>
          mid i ⟨e.1, G.incidenceSet_subset u (G.mem_incidenceFinset.1 e.2)⟩) := by
      intro b hb
      rw [mem_neighborFinset, lbGraph_adj] at hb
      cases b with
      | copy j v => simp [lbRel] at hb
      | tn v => simp [lbRel] at hb; subst hb; simp
      | mid j e =>
        simp only [lbRel] at hb
        obtain ⟨-, h | ⟨rfl, hu⟩⟩ := hb
        · exact absurd h id
        · refine mem_insert_of_mem (mem_image.2 ⟨⟨e.1, ?_⟩, mem_attach _ _, rfl⟩)
          exact G.mem_incidenceFinset.2 ⟨e.2, hu⟩
    refine (card_le_card this).trans ((card_insert_le _ _).trans ?_)
    have := card_image_le (s := (G.incidenceFinset u).attach) (f := fun e =>
      (mid i ⟨e.1, G.incidenceSet_subset u (G.mem_incidenceFinset.1 e.2)⟩ :
        LBNode V G.edgeSet K))
    rw [card_attach, card_incidenceFinset_eq_degree] at this
    have := G.degree_le_maxDegree u
    omega

/-! ### The approximation transfer -/

/-- Rounding: `{u : z_u ≥ 1/2}` is a vertex cover of size `≤ 2 ∑ z`. -/
theorem isVertexCover_round {z : V → ℝ} (hz : IsFracVertexCover G z) :
    IsVertexCover G (univ.filter fun u => 1 / 2 ≤ z u) ∧
      ((univ.filter fun u => 1 / 2 ≤ z u).card : ℝ) ≤ 2 * ∑ u, z u := by
  refine ⟨fun a b h => ?_, ?_⟩
  · have := hz.2 h
    by_contra hc
    simp only [mem_coe, mem_filter, mem_univ, true_and, not_or, not_le] at hc
    linarith [hc.1, hc.2]
  · calc ((univ.filter fun u => 1 / 2 ≤ z u).card : ℝ)
        = ∑ u ∈ univ.filter (fun u => 1 / 2 ≤ z u), 2 * (1 / 2) := by simp
      _ ≤ ∑ u ∈ univ.filter (fun u => 1 / 2 ≤ z u), 2 * z u :=
          sum_le_sum fun u hu => by have := (mem_filter.1 hu).2; linarith
      _ ≤ ∑ u, 2 * z u := sum_le_sum_of_subset_of_nonneg (subset_univ _)
          fun u _ _ => by have := hz.1 u; linarith
      _ = 2 * ∑ u, z u := by rw [mul_sum]

/-- Without isolated vertices, `n ≤ (Δ + 1) ∑ z` for every fractional vertex cover `z`. -/
theorem card_le_of_fracCover (hiso : ∀ u, ∃ v, G.Adj u v) {z : V → ℝ}
    (hz : IsFracVertexCover G z) : (Fintype.card V : ℝ) ≤ (G.maxDegree + 1) * ∑ u, z u := by
  choose nb hnb using hiso
  have h1 : (Fintype.card V : ℝ) ≤ ∑ u, (z u + z (nb u)) := by
    calc (Fintype.card V : ℝ) = ∑ _u : V, (1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum fun u _ => hz.2 (hnb u)
  have h2 : ∑ u, z (nb u) ≤ G.maxDegree * ∑ u, z u := by
    rw [sum_comp, mul_sum]
    refine (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun v _ _ => ?_).trans
      (sum_le_sum fun v _ => ?_)
    · exact smul_nonneg (Nat.cast_nonneg _) (hz.1 v)
    · rw [nsmul_eq_mul]
      gcongr
      · exact hz.1 v
      · have : (univ.filter fun u => nb u = v) ⊆ G.neighborFinset v := fun u hu => by
          rw [mem_filter] at hu; rw [mem_neighborFinset, ← hu.2]; exact (hnb u).symm
        exact_mod_cast (card_le_card this).trans
          ((card_neighborFinset_eq_degree G v).le.trans (G.degree_le_maxDegree v))
  rw [sum_add_distrib] at h1
  linarith

/-- **The reduction of Theorem 1.4.** Let `G` have maximum degree `Δ ≥ 1` and no isolated
vertices, `H = lbGraph G Δ²`, and let `S` be a `c`-approximate dominating set of `H`. Then the
locally computed `y = fracOf S` is a fractional vertex cover of `G` with
`∑ y ≤ 2c(1 + 1/Δ) · ∑ z` for every fractional vertex cover `z` of `G`. -/
theorem reduction (hΔ : 1 ≤ G.maxDegree) (hiso : ∀ u, ∃ v, G.Adj u v) {c : ℝ} (hc : 0 ≤ c)
    {S : Finset (LBNode V G.edgeSet (G.maxDegree ^ 2))}
    (hS : IsDominating (lbGraph G (G.maxDegree ^ 2)) S)
    (happrox : ∀ D, IsDominating (lbGraph G (G.maxDegree ^ 2)) D → (S.card : ℝ) ≤ c * D.card)
    {z : V → ℝ} (hz : IsFracVertexCover G z) :
    IsFracVertexCover G (fracOf S) ∧
      ∑ u, fracOf S u ≤ 2 * c * (1 + 1 / G.maxDegree) * ∑ u, z u := by
  have hK : 1 ≤ G.maxDegree ^ 2 := Nat.one_le_pow _ _ hΔ
  obtain ⟨hy, hsum⟩ := fracCover_of_dominating hK hS
  refine ⟨hy, ?_⟩
  obtain ⟨hC, hCcard⟩ := isVertexCover_round hz
  obtain ⟨D, hD, hDcard⟩ := exists_dominating_lbGraph (G.maxDegree ^ 2) hC
  have hn := card_le_of_fracCover hiso hz
  have hΔr : (1 : ℝ) ≤ G.maxDegree := by exact_mod_cast hΔ
  have hZ : 0 ≤ ∑ u, z u := sum_nonneg fun u _ => hz.1 u
  have hK' : (0 : ℝ) < ((G.maxDegree ^ 2 : ℕ) : ℝ) := by exact_mod_cast hK
  have hD' : (D.card : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * (2 * ∑ u, z u) +
      (G.maxDegree + 1) * ∑ u, z u := by
    have : (D.card : ℝ) ≤ ((G.maxDegree ^ 2 : ℕ) : ℝ) *
        ((univ.filter fun u => 1 / 2 ≤ z u).card : ℝ) + Fintype.card V := by
      exact_mod_cast hDcard
    push_cast at this
    nlinarith
  have h1 : (S.card : ℝ) ≤ c * ((G.maxDegree : ℝ) ^ 2 * (2 * ∑ u, z u) +
      (G.maxDegree + 1) * ∑ u, z u) :=
    (happrox D hD).trans (mul_le_mul_of_nonneg_left hD' hc)
  have h3 : ((G.maxDegree : ℝ) + 1) ≤ 2 * G.maxDegree := by linarith
  have h4 : (S.card : ℝ) ≤ (2 * c * (1 + 1 / G.maxDegree) * ∑ u, z u) * (G.maxDegree : ℝ) ^ 2 := by
    refine h1.trans (le_of_le_of_eq (b := c * ((G.maxDegree : ℝ) ^ 2 * (2 * ∑ u, z u) +
      2 * G.maxDegree * ∑ u, z u)) (by gcongr) ?_)
    field_simp
  calc ∑ u, fracOf S u ≤ (S.card : ℝ) / ((G.maxDegree ^ 2 : ℕ) : ℝ) := hsum
    _ ≤ 2 * c * (1 + 1 / G.maxDegree) * ∑ u, z u := by
        rw [div_le_iff₀ hK']; push_cast; exact h4

end DominatingSetArboricity
