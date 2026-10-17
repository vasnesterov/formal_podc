import Papers.PODC2010.EdgeDominatingSets.Basic

/-!
# Theorem 5 of Suomela (PODC 2010): the combinatorial core of the analysis

Suomela, *Distributed algorithms for edge dominating sets*, PODC 2010, §7.3–§7.8.

The algorithm `A(Δ)` of §7.1 (odd `Δ = 2k + 1 ≥ 3`) outputs `D = M ∪ P`, where `M` and `P` satisfy
the properties (a), (b), (c) of §7.3 (`Props`). Here we prove, purely graph-theoretically, that any
such pair satisfies `|M ∪ P| ≤ (4 - 1/k)|D*|` for every edge dominating set `D*`
(`card_le_of_props`, `card_le_edgeDomNum_of_props`).

The proof is the integer (doubled) version of the paper's cost/weight double counting:

* `internal Dstar`: the nodes covered by `D*` (`|I| ≤ 2|D*|`); every edge has an internal endpoint.
* `cost y z`: twice the cost that the `D`-edge `{y, z}` charges to the internal node `y`
  (`2` if `z` is external, `1` if `z` is internal); `∑_{y ∈ I} ∑_z cost y z = 2|D|` (`sum_cost`).
* `weight y z`: the weight of the edge `{y, z}` seen from `y` when `z` is an external `P`-node
  (`2 - deg z` if `{y, z} ∈ P`, `2` otherwise); the total is `≥ 0` (`sum_weight_nonneg`, §7.7).
* `node_bound`: for every internal `y`, `(Δ - 1)·x(y) + w(y) ≤ 4Δ - 6` (§7.7 case analysis).

The paper takes `D*` to be a minimum maximal matching; the argument only uses that `D*` is an edge
dominating set (to get `|I| ≤ 2|D*|` and that every edge has an internal endpoint), so it applies
to a minimum edge dominating set directly and the Yannakakis–Gavril theorem is not needed. The
paper's auxiliary edge set `C` is not needed either.
-/

namespace Podc.EdgeDominatingSets

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Properties (a), (b), (c) of §7.3 of the sets `M` and `P` constructed by the algorithm of §7.1:
(a) `M` is a matching, `P` is a 2-matching, and `M`, `P` are node-disjoint; (b) every node of odd
degree is covered by `M` or has a neighbour covered by `M`; (c) the two endpoints of a `P`-edge
have the same degree. -/
structure Props (M P : Finset (Sym2 V)) : Prop where
  M_sub : ∀ e ∈ M, e ∈ G.edgeSet
  P_sub : ∀ e ∈ P, e ∈ G.edgeSet
  /-- (a) `M` is a matching. -/
  M_matching : ∀ v, (M.filter (v ∈ ·)).card ≤ 1
  /-- (a) `P` is a 2-matching. -/
  P_two : ∀ v, (P.filter (v ∈ ·)).card ≤ 2
  /-- (a) `M` and `P` are node-disjoint. -/
  disj : ∀ v, ∀ e ∈ M, v ∈ e → ∀ e' ∈ P, v ∉ e'
  /-- (b) -/
  odd : ∀ v, Odd (G.degree v) → (∃ e ∈ M, v ∈ e) ∨ ∃ u, G.Adj v u ∧ ∃ e ∈ M, u ∈ e
  /-- (c) -/
  P_deg : ∀ u v, s(u, v) ∈ P → G.degree u = G.degree v

namespace Thm5

variable {G}

/-! ### Counting lemmas -/

theorem card_filter_mk_mem (E : Finset (Sym2 V)) (y : V) :
    (univ.filter fun z => s(y, z) ∈ E).card = (E.filter (y ∈ ·)).card := by
  rw [← card_image_of_injective _ (fun a b h => Sym2.congr_right.1 h : Function.Injective
    fun z => s(y, z))]
  congr 1
  ext e
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨hz, Sym2.mem_mk_left _ _⟩
  · rintro ⟨he, hy⟩
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.1 hy
    exact ⟨z, he, rfl⟩

/-- Handshake lemma for a set of non-loop edges. -/
theorem sum_card_filter_mk_mem (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    ∑ y, (univ.filter fun z => s(y, z) ∈ E).card = 2 * E.card := by
  simp_rw [card_filter_mk_mem, card_filter]
  rw [sum_comm]
  simp_rw [← card_filter]
  rw [sum_congr rfl fun e he => (show (univ.filter (· ∈ e)).card = 2 by
    rw [show univ.filter (· ∈ e) = e.toFinset by ext; simp]
    exact Sym2.card_toFinset_of_not_isDiag e (hE e he))]
  simp [mul_comm]

omit [Fintype V] in
/-- Splitting off a few special elements: the others contribute at most `2` each. -/
theorem sum_le_of_subset {N Z : Finset V} (hZ : Z ⊆ N) (f : V → ℤ)
    (hf : ∀ z ∈ N, z ∉ Z → f z ≤ 2) :
    ∑ z ∈ N, f z ≤ ∑ z ∈ Z, f z + 2 * ((N.card : ℤ) - Z.card) := by
  rw [← sum_sdiff hZ]
  have h1 : ∑ z ∈ N \ Z, f z ≤ ∑ _z ∈ N \ Z, (2 : ℤ) := sum_le_sum fun z hz => by
    rw [mem_sdiff] at hz; exact hf z hz.1 hz.2
  have h2 : ((N \ Z).card : ℤ) = N.card - Z.card := by
    rw [card_sdiff_of_subset hZ, Nat.cast_sub (card_le_card hZ)]
  rw [sum_const, nsmul_eq_mul, h2] at h1
  linarith

omit [Fintype V] in
theorem sum_le_one {N : Finset V} (f : V → ℤ) {a : V} (ha : a ∈ N)
    (hf : ∀ z ∈ N, z ≠ a → f z ≤ 2) : ∑ z ∈ N, f z ≤ f a + 2 * ((N.card : ℤ) - 1) := by
  have := sum_le_of_subset (Z := {a}) (by simpa using ha) f (fun z hz hZ => hf z hz (by simpa
    using hZ))
  simpa using this

omit [Fintype V] in
theorem sum_le_two {N : Finset V} (f : V → ℤ) {a b : V} (ha : a ∈ N) (hb : b ∈ N) (hab : a ≠ b)
    (hf : ∀ z ∈ N, z ≠ a → z ≠ b → f z ≤ 2) :
    ∑ z ∈ N, f z ≤ f a + f b + 2 * ((N.card : ℤ) - 2) := by
  have := sum_le_of_subset (Z := {a, b}) (by simp [insert_subset_iff, ha, hb]) f
    (fun z hz hZ => hf z hz (by simp_all) (by simp_all))
  rw [sum_pair hab, card_pair hab] at this
  simpa using this

omit [Fintype V] in
theorem sum_le_three {N : Finset V} (f : V → ℤ) {a b c : V} (ha : a ∈ N) (hb : b ∈ N)
    (hc : c ∈ N) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hf : ∀ z ∈ N, z ≠ a → z ≠ b → z ≠ c → f z ≤ 2) :
    ∑ z ∈ N, f z ≤ f a + f b + f c + 2 * ((N.card : ℤ) - 3) := by
  have := sum_le_of_subset (Z := {a, b, c}) (by simp [insert_subset_iff, ha, hb, hc]) f
    (fun z hz hZ => hf z hz (by simp_all) (by simp_all) (by simp_all))
  have hnot : a ∉ ({b, c} : Finset V) := by simp [hab, hac]
  rw [sum_insert hnot, sum_pair hbc, card_insert_of_notMem hnot, card_pair hbc] at this
  push_cast at this
  linarith

/-! ### Internal nodes, costs and weights -/

variable {M P Dstar : Finset (Sym2 V)}

/-- The internal nodes: the nodes covered by `D*`. -/
def internal (Dstar : Finset (Sym2 V)) : Finset V := univ.filter fun v => ∃ e ∈ Dstar, v ∈ e

theorem mem_internal {v : V} : v ∈ internal Dstar ↔ ∃ e ∈ Dstar, v ∈ e := by simp [internal]

omit [DecidableRel G.Adj] in
theorem internal_or (hD : IsEDS G Dstar) {y z : V} (h : G.Adj y z) :
    y ∈ internal Dstar ∨ z ∈ internal Dstar := by
  obtain ⟨e', he', v, hv, hve'⟩ := hD.2 s(y, z) h
  rcases Sym2.mem_iff.1 hv with rfl | rfl
  · exact Or.inl (mem_internal.2 ⟨e', he', hve'⟩)
  · exact Or.inr (mem_internal.2 ⟨e', he', hve'⟩)

omit [DecidableRel G.Adj] in
theorem exists_partner (hD : IsEDS G Dstar) {y : V} (hy : y ∈ internal Dstar) :
    ∃ u, G.Adj y u ∧ u ∈ internal Dstar := by
  obtain ⟨e, he, hye⟩ := mem_internal.1 hy
  obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hye
  exact ⟨u, hD.1 _ he, mem_internal.2 ⟨_, he, Sym2.mem_mk_right _ _⟩⟩

theorem card_internal_le : (internal Dstar).card ≤ 2 * Dstar.card := by
  calc (internal Dstar).card ≤ (Dstar.biUnion Sym2.toFinset).card := by
        apply card_le_card
        intro v hv
        obtain ⟨e, he, hve⟩ := mem_internal.1 hv
        exact mem_biUnion.2 ⟨e, he, Sym2.mem_toFinset.2 hve⟩
    _ ≤ ∑ e ∈ Dstar, e.toFinset.card := card_biUnion_le
    _ ≤ ∑ _e ∈ Dstar, 2 := sum_le_sum fun e _ => by rw [Sym2.card_toFinset]; split_ifs <;> omega
    _ = 2 * Dstar.card := by simp [mul_comm]

/-- Twice the cost that the edge `{y, z} ∈ D = M ∪ P` charges to `y` (§7.5). -/
def cost (M P Dstar : Finset (Sym2 V)) (y z : V) : ℤ :=
  if s(y, z) ∈ M ∪ P then (if z ∈ internal Dstar then 1 else 2) else 0

variable (G) in
/-- The weight of the edge `{y, z}` if `z` is an external `P`-node (§7.6), else `0`. -/
def weight (P Dstar : Finset (Sym2 V)) (y z : V) : ℤ :=
  if G.Adj y z ∧ (∃ e ∈ P, z ∈ e) ∧ z ∉ internal Dstar then
    (if s(y, z) ∈ P then 2 - G.degree z else 2) else 0

omit [DecidableRel G.Adj] in
/-- §7.5: the total cost of the internal nodes is `|D|` (doubled). -/
theorem sum_cost (hM : ∀ e ∈ M, e ∈ G.edgeSet) (hP : ∀ e ∈ P, e ∈ G.edgeSet)
    (hD : IsEDS G Dstar) :
    ∑ y ∈ internal Dstar, ∑ z, cost M P Dstar y z = 2 * ((M ∪ P).card : ℤ) := by
  set I := internal Dstar with hI
  set h : V → V → ℤ := fun y z => if y ∈ I then cost M P Dstar y z else 0 with hh
  have hsym : ∀ y z, h y z + h z y = if s(y, z) ∈ M ∪ P then 2 else 0 := by
    intro y z
    simp only [hh, cost, Sym2.eq_swap (a := z) (b := y)]
    by_cases hyz : s(y, z) ∈ M ∪ P
    · have hadj : G.Adj y z := by
        rcases mem_union.1 hyz with h1 | h1
        exacts [hM _ h1, hP _ h1]
      have := internal_or hD hadj
      by_cases hy : y ∈ I <;> by_cases hz : z ∈ I <;> simp_all
    · simp [hyz]
  have h1 : ∑ y, ∑ z, h y z = ∑ y ∈ I, ∑ z, cost M P Dstar y z := by
    rw [← univ_inter I, ← sum_ite_mem]
    refine sum_congr rfl fun y _ => ?_
    split_ifs with hy <;> simp [hh, hy]
  have h2 : ∑ y, ∑ z, (h y z + h z y) = 2 * ∑ y, ∑ z, h y z := by
    simp only [sum_add_distrib]
    rw [sum_comm (f := fun y z => h z y)]
    ring
  have hdiag : ∀ e ∈ M ∪ P, ¬ e.IsDiag := fun e he => G.not_isDiag_of_mem_edgeSet
    (by rcases mem_union.1 he with h1 | h1; exacts [hM _ h1, hP _ h1])
  have h3 : ∑ y, ∑ z, (h y z + h z y) = 2 * (2 * ((M ∪ P).card : ℤ)) := by
    simp_rw [hsym]
    simp_rw [← sum_filter, sum_const, nsmul_eq_mul]
    rw [← sum_mul, ← Nat.cast_sum, sum_card_filter_mk_mem _ hdiag]
    push_cast; ring
  linarith

/-- §7.6–7.7: the total weight is non-negative (double counting over external `P`-nodes). -/
theorem sum_weight_nonneg (hP2 : ∀ v, (P.filter (v ∈ ·)).card ≤ 2) (hD : IsEDS G Dstar) :
    0 ≤ ∑ y ∈ internal Dstar, ∑ z, weight G P Dstar y z := by
  have h1 : ∑ y ∈ internal Dstar, ∑ z, weight G P Dstar y z =
      ∑ y, ∑ z, weight G P Dstar y z := by
    apply sum_subset (subset_univ _)
    intro y _ hy
    apply sum_eq_zero
    intro z _
    simp only [weight]
    rw [ite_eq_right]
    rintro ⟨hadj, -, hz⟩
    rcases internal_or hD hadj with h | h <;> contradiction
  rw [h1, sum_comm]
  apply sum_nonneg
  intro z _
  by_cases hz : (∃ e ∈ P, z ∈ e) ∧ z ∉ internal Dstar
  · have h2 : ∑ y, weight G P Dstar y z = ∑ y ∈ G.neighborFinset z,
        (if s(y, z) ∈ P then 2 - (G.degree z : ℤ) else 2) := by
      symm
      apply sum_subset_zero_on_sdiff (subset_univ _)
      · intro y hy
        have : ¬ G.Adj y z := fun h => (mem_sdiff.1 hy).2 (by simpa using h.symm)
        simp [weight, this]
      · intro y hy
        have : G.Adj y z := G.adj_symm (by simpa using hy)
        simp [weight, this, hz.1, hz.2]
    rw [h2, sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hc : ((G.neighborFinset z).filter fun y => s(y, z) ∈ P).card ≤ 2 := by
      refine le_trans (card_le_card ?_) ((card_filter_mk_mem P z).le.trans (hP2 z))
      intro y hy
      simp only [mem_filter] at hy ⊢
      exact ⟨mem_univ _, by rw [Sym2.eq_swap]; exact hy.2⟩
    have hsum := card_filter_add_card_filter_not (s := G.neighborFinset z) (fun y => s(y, z) ∈ P)
    rw [G.card_neighborFinset_eq_degree] at hsum
    set c := ((G.neighborFinset z).filter fun y => s(y, z) ∈ P).card
    set c' := ((G.neighborFinset z).filter fun y => ¬ s(y, z) ∈ P).card
    have hc' : (c : ℤ) + c' = G.degree z := by exact_mod_cast hsum
    have hc2 : (c : ℤ) ≤ 2 := by exact_mod_cast hc
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℤ) (G.degree z)) (sub_nonneg.2 hc2)]
  · apply le_of_eq
    symm
    apply sum_eq_zero
    intro y _
    simp only [weight]
    rw [ite_eq_right]
    rintro ⟨-, h1, h2⟩
    exact hz ⟨h1, h2⟩

/-- §7.7: the per-node bound `(Δ - 1)·x(y) + w(y) ≤ 4Δ - 6` for `Δ = 2k + 1`, where
`x(y) = ∑_z cost y z` and `w(y) = ∑_z weight y z`. -/
theorem node_bound (h : Props G M P) (hD : IsEDS G Dstar) {k : ℕ} (hk : 1 ≤ k)
    (hΔ : ∀ v, G.degree v ≤ 2 * k + 1) {y : V} (hy : y ∈ internal Dstar) :
    2 * (k : ℤ) * ∑ z, cost M P Dstar y z + ∑ z, weight G P Dstar y z ≤ 8 * k - 2 := by
  set I := internal Dstar with hI
  set t : V → ℤ := fun z => 2 * (k : ℤ) * cost M P Dstar y z + weight G P Dstar y z with ht
  set N := G.neighborFinset y with hN
  have hDadj : ∀ z, s(y, z) ∈ M ∪ P → G.Adj y z := fun z hz => by
    rcases mem_union.1 hz with h1 | h1
    exacts [h.M_sub _ h1, h.P_sub _ h1]
  have hsum : 2 * (k : ℤ) * ∑ z, cost M P Dstar y z + ∑ z, weight G P Dstar y z =
      ∑ z ∈ N, t z := by
    rw [mul_sum, ← sum_add_distrib]
    symm
    apply sum_subset (subset_univ _)
    intro z _ hz
    have hadj : ¬ G.Adj y z := by simpa [hN] using hz
    have h1 : s(y, z) ∉ M ∪ P := fun hm => hadj (hDadj z hm)
    simp only [ht, cost, weight, ite_eq_right h1]
    simp [hadj]
  rw [hsum]
  have hNd : (N.card : ℤ) = G.degree y := by simp [hN]
  have hd : (G.degree y : ℤ) ≤ 2 * k + 1 := by exact_mod_cast hΔ y
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have memN : ∀ z, G.Adj y z → z ∈ N := fun z hz => by simpa [hN] using hz
  -- the values of `t` on the neighbours of `y`
  have T0 : ∀ z, z ∈ I → s(y, z) ∉ M ∪ P → t z = 0 := by
    intro z hz hyz
    simp only [ht, cost, weight, ite_eq_right hyz, ← hI]
    simp [hz]
  have T0' : ∀ z, (∃ e ∈ M, z ∈ e) → s(y, z) ∉ M ∪ P → t z = 0 := by
    rintro z ⟨e, he, hze⟩ hyz
    have : ¬ ∃ e ∈ P, z ∈ e := fun ⟨e', he', hze'⟩ => h.disj z e he hze e' he' hze'
    simp only [ht, cost, weight, ite_eq_right hyz]
    simp [this]
  have T1 : ∀ z, s(y, z) ∉ M ∪ P → t z ≤ 2 := by
    intro z hyz
    have hP : s(y, z) ∉ P := fun hp => hyz (mem_union_right _ hp)
    simp only [ht, cost, weight, ite_eq_right hyz, ite_eq_right hP]
    split_ifs <;> norm_num
  have T2 : ∀ z, s(y, z) ∈ M ∪ P → z ∈ I → t z = 2 * k := by
    intro z hyz hz
    simp only [ht, cost, weight, ite_eq_left hyz, ← hI]
    simp [hz]
  have T3 : ∀ z, s(y, z) ∈ P → z ∉ I → t z = 4 * k + 2 - G.degree y := by
    intro z hyz hz
    have hadj : G.Adj y z := h.P_sub _ hyz
    have hzP : ∃ e ∈ P, z ∈ e := ⟨_, hyz, Sym2.mem_mk_right _ _⟩
    have hdeg := h.P_deg y z hyz
    simp only [ht, cost, weight, ite_eq_left (mem_union_right _ hyz), ← hI]
    simp [hyz, hz, hadj, hzP, hdeg]; ring
  have T4 : ∀ z, s(y, z) ∈ M → z ∉ I → t z = 4 * k := by
    intro z hyz hz
    have : ¬ ∃ e ∈ P, z ∈ e := fun ⟨e', he', hze'⟩ =>
      h.disj z _ hyz (Sym2.mem_mk_right _ _) e' he' hze'
    simp only [ht, cost, weight, ite_eq_left (mem_union_left _ hyz), ← hI]
    simp [hz, this]; ring
  obtain ⟨u, hyu, hu⟩ := exists_partner hD hy
  -- `y` has exactly one `D`-neighbour `p`
  have single : ∀ p, s(y, p) ∈ M ∪ P → (∀ z, s(y, z) ∈ M ∪ P → z = p) →
      ∑ z ∈ N, t z ≤ 8 * k - 2 := by
    intro p hp hDp
    have hpN := memN p (hDadj p hp)
    have hout : ∀ z ∈ N, z ≠ p → t z ≤ 2 := fun z _ hzp => T1 z (fun hz => hzp (hDp z hz))
    by_cases hpI : p ∈ I
    · have := sum_le_one t hpN hout
      rw [T2 p hp hpI, hNd] at this
      linarith
    · have hup : u ≠ p := fun e => hpI (e ▸ hu)
      have h2 := sum_le_two t (memN u hyu) hpN hup (fun z hz _ h2 => hout z hz h2)
      have hcard : 2 ≤ N.card := by
        rw [← card_pair hup]; exact card_le_card (by simp [insert_subset_iff, memN u hyu, hpN])
      have htu : t u = 0 := T0 u hu (fun h => hup (hDp u h))
      have htp : t p ≤ 4 * k := by
        rcases mem_union.1 hp with hm | hm
        · rw [T4 p hm hpI]
        · rw [T3 p hm hpI]
          have : (2 : ℤ) ≤ G.degree y := by rw [← hNd]; exact_mod_cast hcard
          linarith
      rw [htu, hNd] at h2
      linarith
  -- `y` has two `P`-neighbours, an external one `a` and an internal one `b`
  have mixed : ∀ a b, a ≠ b → s(y, a) ∈ P → s(y, b) ∈ P →
      (∀ z, s(y, z) ∈ M ∪ P → z = a ∨ z = b) → a ∉ I → b ∈ I → ∑ z ∈ N, t z ≤ 8 * k - 2 := by
    intro a b hab ha hb hDab haI hbI
    have haN := memN a (h.P_sub _ ha)
    have hbN := memN b (h.P_sub _ hb)
    have hout : ∀ z, z ≠ a → z ≠ b → t z ≤ 2 := fun z h1 h2 =>
      T1 z (fun hz => by rcases hDab z hz with h3 | h3; exacts [h1 h3, h2 h3])
    have hta := T3 a ha haI
    have htb := T2 b (mem_union_right _ hb) hbI
    by_cases hdeg : G.degree y = 2 * k + 1
    · rcases h.odd y (by rw [hdeg]; exact odd_two_mul_add_one k) with ⟨e, he, hye⟩ |
        ⟨u', hyu', e, he, hu'e⟩
      · exact (h.disj y e he hye _ ha (Sym2.mem_mk_left _ _)).elim
      · have hu'a : u' ≠ a := by
          rintro rfl; exact h.disj _ e he hu'e _ ha (Sym2.mem_mk_right _ _)
        have hu'b : u' ≠ b := by
          rintro rfl; exact h.disj _ e he hu'e _ hb (Sym2.mem_mk_right _ _)
        have htu' : t u' = 0 := T0' u' ⟨e, he, hu'e⟩
          (fun hz => by rcases hDab u' hz with h3 | h3; exacts [hu'a h3, hu'b h3])
        have := sum_le_three t haN hbN (memN u' hyu') hab hu'a.symm hu'b.symm
          (fun z _ h1 h2 _ => hout z h1 h2)
        have hd' : (G.degree y : ℤ) = 2 * k + 1 := by exact_mod_cast hdeg
        rw [hta, htb, htu', hNd] at this
        linarith
    · have hd' : (G.degree y : ℤ) ≤ 2 * k := by
        have : G.degree y ≤ 2 * k := by have := hΔ y; omega
        exact_mod_cast this
      have := sum_le_two t haN hbN hab (fun z _ h1 h2 => hout z h1 h2)
      rw [hta, htb, hNd] at this
      linarith
  by_cases hyM : ∃ e ∈ M, y ∈ e
  · -- `y` is an `M`-node: its only `D`-neighbour is its `M`-partner
    obtain ⟨e, he, hye⟩ := hyM
    obtain ⟨m, rfl⟩ := Sym2.mem_iff_exists.1 hye
    refine single m (mem_union_left _ he) fun z hz => ?_
    rcases mem_union.1 hz with hz | hz
    · have := card_le_one.1 (h.M_matching y) _ (mem_filter.2 ⟨hz, Sym2.mem_mk_left _ _⟩) _
        (mem_filter.2 ⟨he, Sym2.mem_mk_left _ _⟩)
      exact Sym2.congr_right.1 this
    · exact (h.disj y _ he (Sym2.mem_mk_left _ _) _ hz (Sym2.mem_mk_left _ _)).elim
  · have hnoM : ∀ z, s(y, z) ∉ M := fun z hz => hyM ⟨_, hz, Sym2.mem_mk_left _ _⟩
    have hDP : ∀ z, s(y, z) ∈ M ∪ P ↔ s(y, z) ∈ P := fun z => by simp [hnoM z]
    by_cases hyP : ∃ e ∈ P, y ∈ e
    · -- `y` is a `P`-node with one or two `P`-neighbours
      set Q := univ.filter fun z => s(y, z) ∈ P with hQ
      have hQ2 : Q.card ≤ 2 := (card_filter_mk_mem P y).le.trans (h.P_two y)
      obtain ⟨e, he, hye⟩ := hyP
      obtain ⟨p, rfl⟩ := Sym2.mem_iff_exists.1 hye
      have hpQ : p ∈ Q := by simp [hQ, he]
      have hQ0 : Q.card ≠ 0 := card_ne_zero_of_mem hpQ
      have hmemQ : ∀ z, z ∈ Q ↔ s(y, z) ∈ M ∪ P := fun z => by simp [hQ, hDP]
      rcases (by omega : Q.card = 1 ∨ Q.card = 2) with hc | hc
      · obtain ⟨a, ha⟩ := card_eq_one.1 hc
        have haQ : a ∈ Q := by simp [ha]
        refine single a ((hmemQ a).1 haQ) fun z hz => ?_
        have := (hmemQ z).2 hz
        rw [ha] at this; simpa using this
      · obtain ⟨a, b, hab, hQab⟩ := card_eq_two.1 hc
        have hDab : ∀ z, s(y, z) ∈ M ∪ P → z = a ∨ z = b := fun z hz => by
          have := (hmemQ z).2 hz; rw [hQab] at this; simpa using this
        have ha : s(y, a) ∈ P := by
          have : a ∈ Q := by simp [hQab]
          simpa [hQ] using this
        have hb : s(y, b) ∈ P := by
          have : b ∈ Q := by simp [hQab]
          simpa [hQ] using this
        have haN := memN a (h.P_sub _ ha)
        have hbN := memN b (h.P_sub _ hb)
        have hout : ∀ z ∈ N, z ≠ a → z ≠ b → t z ≤ 2 := fun z _ h1 h2 =>
          T1 z (fun hz => by rcases hDab z hz with h3 | h3; exacts [h1 h3, h2 h3])
        by_cases haI : a ∈ I <;> by_cases hbI : b ∈ I
        · have := sum_le_two t haN hbN hab hout
          rw [T2 a (mem_union_right _ ha) haI, T2 b (mem_union_right _ hb) hbI, hNd] at this
          linarith
        · exact mixed b a (Ne.symm hab) hb ha (fun z hz => (hDab z hz).symm) hbI haI
        · exact mixed a b hab ha hb hDab haI hbI
        · have hua : u ≠ a := fun e => haI (e ▸ hu)
          have hub : u ≠ b := fun e => hbI (e ▸ hu)
          have := sum_le_three t haN hbN (memN u hyu) hab (Ne.symm hua) (Ne.symm hub)
            (fun z hz h1 h2 _ => hout z hz h1 h2)
          rw [T3 a ha haI, T3 b hb hbI, T0 u hu
            (fun hz => by rcases hDab u hz with h3 | h3; exacts [hua h3, hub h3]), hNd] at this
          linarith
    · -- `y` is not covered by `D`
      have hnoD : ∀ z, s(y, z) ∉ M ∪ P := fun z hz =>
        hyP ⟨_, (hDP z).1 hz, Sym2.mem_mk_left _ _⟩
      have := sum_le_one t (memN u hyu) (fun z _ _ => T1 z (hnoD z))
      rw [T0 u hu (hnoD u), hNd] at this
      linarith

end Thm5

open Thm5 in
/-- **Theorem 5** of [Suomela, PODC 2010], combinatorial core (§7.4–7.8): if `M`, `P` satisfy the
properties (a), (b), (c) of §7.3 in a graph of maximum degree `≤ Δ = 2k + 1` (`k ≥ 1`), then
`|M ∪ P| ≤ (4 - 1/k)|D*|` for every edge dominating set `D*`; in integer form
`2k·|M ∪ P| ≤ (8k - 2)·|D*|`, i.e. `(Δ - 1)|D| ≤ (4Δ - 6)|D*|`. -/
theorem card_le_of_props {k : ℕ} (hk : 1 ≤ k) (hΔ : ∀ v, G.degree v ≤ 2 * k + 1)
    {M P : Finset (Sym2 V)} (h : Props G M P) {Dstar : Finset (Sym2 V)} (hD : IsEDS G Dstar) :
    2 * k * (M ∪ P).card ≤ (8 * k - 2) * Dstar.card := by
  have hsum := sum_le_sum fun y hy => node_bound h hD hk hΔ (y := y) hy
  rw [sum_add_distrib, ← mul_sum, sum_cost h.M_sub h.P_sub hD, sum_const, nsmul_eq_mul] at hsum
  have hw := sum_weight_nonneg h.P_two hD
  have hI : ((internal Dstar).card : ℤ) ≤ 2 * Dstar.card := by exact_mod_cast card_internal_le
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have h8 := mul_le_mul_of_nonneg_right hI (show (0 : ℤ) ≤ 8 * k - 2 by linarith)
  zify [show 2 ≤ 8 * k by omega]
  linarith

/-- **Theorem 5** of [Suomela, PODC 2010], combinatorial core, real form: under the properties
(a), (b), (c) of §7.3 and maximum degree `≤ Δ = 2k + 1` (`k ≥ 1`),
`|M ∪ P| ≤ (4 - 1/k) · γ'(G)`, where `γ'(G)` is the edge domination number. -/
theorem card_le_edgeDomNum_of_props {k : ℕ} (hk : 1 ≤ k) (hΔ : ∀ v, G.degree v ≤ 2 * k + 1)
    {M P : Finset (Sym2 V)} (h : Props G M P) :
    ((M ∪ P).card : ℝ) ≤ (4 - 1 / k) * edgeDomNum G := by
  obtain ⟨D, hD, hcard⟩ := exists_isEDS_card_eq G
  have h1 := card_le_of_props G hk hΔ h hD
  rw [hcard] at h1
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h' : (2 * k * (M ∪ P).card : ℝ) ≤ (8 * k - 2) * edgeDomNum G := by
    have := (Nat.cast_le (α := ℝ)).2 h1
    push_cast [show 2 ≤ 8 * k by omega] at this
    exact this
  rw [show (4 - 1 / (k : ℝ)) = (8 * k - 2) / (2 * k) by field_simp; ring, div_mul_eq_mul_div,
    le_div_iff₀ (by positivity)]
  linarith

end Podc.EdgeDominatingSets
