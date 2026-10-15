import Papers.PODC2026.SinklessOrientation.Basic

/-!
# Lemma 2.2: balls without low-degree nodes and cycles are large

Lemma 2.2 of *Brief Announcement: Sinkless Orientation Made Trivial* (A. Nolin, PODC 2026).

* `hasBackEdges_of_containsCycle`, `containsCycle_of_hasBackEdges`: the ball `cball G s r`
  contains a cycle iff some node `x` of the ball has two distinct neighbours that are not farther
  from `s` than `x` (`HasBackEdges G s r`), i.e. iff the BFS layering of the ball is not a tree.
* `card_cball_ge_of_not_hasBackEdges`: if every node at distance `< r` from `s` has degree `≥ δ`
  and there are no back edges, then the ball has at least `1 + δ((δ-1)^r - 1)/(δ-2)` nodes
  (the size of the complete `δ`-regular tree of depth `r`), by counting BFS levels.
* `lemma_2_2` (and the slightly stronger `lemma_2_2'`): Lemma 2.2 of the paper.
* `lemma_2_2_of_card_le`, `lemma_2_2_clog`: the "in particular" part of Lemma 2.2: in an
  `n`-node graph the distance-`⌈log_{δ-1} n⌉` ball of any node contains a node of degree `< δ` or a
  cycle (the paper writes "degree `δ`", a typo for "degree `< δ`").

The paper's hypothesis `r ≥ 1` is redundant (harmless): for `r = 0` the bound is `1`.
-/

namespace SinklessOrientation

open SimpleGraph Finset

variable {V : Type*}

section Aux

/-- `e ≤ j + 1` and `¬ e ≤ j` force `e = j + 1` in `ℕ∞`. -/
private lemma enat_eq_succ_of {e : ℕ∞} {j : ℕ} (h1 : e ≤ (j : ℕ∞) + 1) (h2 : ¬ e ≤ j) :
    e = ((j + 1 : ℕ) : ℕ∞) := by
  have hne : e ≠ ⊤ := ne_top_of_le_ne_top (by simp) h1
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 hne
  have h1' : m ≤ j + 1 := by exact_mod_cast h1
  have h2' : ¬ m ≤ j := by exact_mod_cast h2
  congr 1; omega

private lemma deg_eq_card_filter [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    deg G x = (univ.filter (G.Adj x)).card := by
  have : G.neighborSet x = ↑(univ.filter (G.Adj x)) := by ext; simp
  rw [deg, this, Set.ncard_coe_finset]

end Aux

/-! ### Cycles in a ball versus back edges -/

section Cycles

variable {G : SimpleGraph V} {s : V} {r : ℕ}

-- CSLib candidate
/-- If the ball `cball G s r` contains a cycle, then the vertex of the cycle farthest from `s` has
two distinct neighbours (on the cycle) that are not farther from `s` than itself. -/
theorem hasBackEdges_of_containsCycle (h : ContainsCycle G (cball G s r)) :
    HasBackEdges G s r := by
  classical
  obtain ⟨x, c, hc, hcB⟩ := h
  obtain ⟨z, hz, hmax⟩ :=
    c.support.toFinset.exists_max_image (fun w => G.edist s w) ⟨x, by simp⟩
  rw [List.mem_toFinset] at hz
  have hc' : (c.rotate z hz).IsCycle := hc.rotate hz
  have hmem : ∀ w ∈ (c.rotate z hz).support, w ∈ c.support :=
    fun w hw => (c.mem_support_rotate_iff z hz).1 hw
  have hnil := hc'.not_nil
  refine ⟨z, (c.rotate z hz).snd, (c.rotate z hz).penultimate, hcB z hz, Walk.adj_snd hnil,
    (Walk.adj_penultimate hnil).symm, hc'.snd_ne_penultimate, hmax _ ?_, hmax _ ?_⟩
  · exact List.mem_toFinset.2 (hmem _ (Walk.getVert_mem_support _ _))
  · exact List.mem_toFinset.2 (hmem _ (Walk.getVert_mem_support _ _))

-- CSLib candidate
/-- Conversely, back edges in the ball `cball G s r` yield a cycle inside the ball: the two
shortest paths from `s` to the two "back" neighbours `y ≠ y'` of `x`, extended by the edges to
`x`, are two distinct paths from `s` to `x` inside the ball. -/
theorem containsCycle_of_hasBackEdges (h : HasBackEdges G s r) :
    ContainsCycle G (cball G s r) := by
  classical
  obtain ⟨x, y, y', hx, hxy, hxy', hyy', hy, hy'⟩ := h
  -- a path from `s` to a back neighbour `z` of `x`, inside the ball and avoiding `x`
  have key : ∀ z, G.Adj x z → G.edist s z ≤ G.edist s x →
      ∃ p : G.Walk s z, p.IsPath ∧ x ∉ p.support ∧ ∀ w ∈ p.support, w ∈ cball G s r := by
    intro z hxz hz
    have hzr : G.edist s z ≤ r := hz.trans hx
    have hdz := edist_eq_coe_dist_of_le hzr
    have hdx := edist_eq_coe_dist_of_le hx
    obtain ⟨q, hq⟩ := exists_walk_of_edist_eq_coe hdz
    have hzx : G.dist s z ≤ G.dist s x := by rw [hdz, hdx] at hz; exact_mod_cast hz
    refine ⟨q.bypass, q.bypass_isPath, ?_, ?_⟩
    · intro hxq
      have h1 := Walk.length_takeUntil_lt_length hxq hxz.ne
      have h2 : G.edist s x ≤ (q.bypass.takeUntil x hxq).length := edist_le _
      have h3 := q.length_bypass_le_length
      rw [hdx] at h2
      have h2' : G.dist s x ≤ (q.bypass.takeUntil x hxq).length := by exact_mod_cast h2
      omega
    · intro w hw
      have hw' := q.support_bypass_subset_support hw
      have h2 : G.edist s w ≤ (q.takeUntil w hw').length := edist_le _
      have h3 := q.length_takeUntil_le_length hw'
      have hxr : G.dist s x ≤ r := dist_le_of_edist_le hx
      simp only [mem_cball]
      exact h2.trans (by exact_mod_cast (by omega : (q.takeUntil w hw').length ≤ r))
  obtain ⟨p, hp, hxp, hpB⟩ := key y hxy hy
  obtain ⟨p', hp', hxp', hpB'⟩ := key y' hxy' hy'
  -- the graph `H`: `G` restricted to the ball
  let B := cball G s r
  let H : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ a ∈ B ∧ b ∈ B
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun _ h => h.1.ne rfl⟩ }
  have hHG : H ≤ G := fun _ _ h => h.1
  have toH : ∀ {a b : V} (p : G.Walk a b), (∀ w ∈ p.support, w ∈ B) →
      ∀ e ∈ p.edges, e ∈ H.edgeSet := by
    intro a b p hp e he
    induction e using Sym2.ind with
    | _ c d =>
      exact ⟨p.adj_of_mem_edges he, hp _ (p.fst_mem_support_of_mem_edges he),
        hp _ (p.snd_mem_support_of_mem_edges he)⟩
  have hxB : x ∈ B := hx
  have hyB : y ∈ B := hy.trans hx
  have hyB' : y' ∈ B := hy'.trans hx
  let P : H.Walk s x := (p.transfer H (toH p hpB)).concat (show H.Adj y x from ⟨hxy.symm, hyB, hxB⟩)
  let P' : H.Walk s x :=
    (p'.transfer H (toH p' hpB')).concat (show H.Adj y' x from ⟨hxy'.symm, hyB', hxB⟩)
  have hP : P.IsPath := (hp.transfer _).concat (by simpa [Walk.support_transfer] using hxp) _
  have hP' : P'.IsPath := (hp'.transfer _).concat (by simpa [Walk.support_transfer] using hxp') _
  have hnac : ¬ H.IsAcyclic := by
    intro hac
    have h1 := (isAcyclic_iff_subsingleton_path.1 hac s x).elim ⟨P, hP⟩ ⟨P', hP'⟩
    obtain ⟨hv, -⟩ := Walk.concat_inj (congrArg Subtype.val h1)
    exact hyy' hv
  simp only [IsAcyclic] at hnac
  push Not at hnac
  obtain ⟨v, c, hc⟩ := hnac
  refine ⟨v, c.mapLe hHG, hc.mapLe hHG, ?_⟩
  rw [Walk.support_mapLe_eq_support]
  have hsupp : ∀ {a b : V} (c : H.Walk a b), a ∈ B → ∀ w ∈ c.support, w ∈ B := by
    intro a b c ha
    induction c with
    | nil => simpa using ha
    | cons h q ih =>
      intro w hw
      rw [Walk.support_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ha
      · exact ih h.2.2 w hw
  cases c with
  | nil => exact absurd hc Walk.not_isCycle_nil
  | cons h q => exact hsupp _ h.2.1

end Cycles

/-! ### Counting BFS levels -/

section Counting

variable {G : SimpleGraph V} {s : V} {r δ : ℕ}

-- CSLib candidate
/-- Counting core of Lemma 2.2, as a geometric sum: if every node at distance `< r` from `s` has
degree `≥ δ` and there are no back edges in the ball, then the BFS levels `1, …, r` have at least
`δ, δ(δ-1), …, δ(δ-1)^(r-1)` nodes. -/
theorem card_cball_ge_sum_of_not_hasBackEdges [Finite V]
    (hdeg : ∀ x, G.edist s x < r → δ ≤ deg G x) (hnb : ¬ HasBackEdges G s r) :
    1 + δ * ∑ k ∈ range r, (δ - 1) ^ k ≤ (cball G s r).ncard := by
  classical
  have := Fintype.ofFinite V
  -- BFS levels
  let L : ℕ → Finset V := fun i => univ.filter (fun x => G.edist s x = (i : ℕ∞))
  have hL : ∀ i x, x ∈ L i ↔ G.edist s x = (i : ℕ∞) := fun i x => by simp [L]
  -- one level to the next
  have step : ∀ j, 1 ≤ j → j < r → (L j).card * (δ - 1) ≤ (L (j + 1)).card := by
    intro j hj1 hjr
    let C : V → Finset V := fun x =>
      univ.filter (fun y => G.Adj x y ∧ G.edist s y = ((j + 1 : ℕ) : ℕ∞))
    -- every node of level `j` has at least `δ - 1` children
    have hC : ∀ x ∈ L j, δ - 1 ≤ (C x).card := by
      intro x hx
      rw [hL] at hx
      let D := univ.filter (fun y => G.Adj x y ∧ G.edist s y ≤ (j : ℕ∞))
      have hD : D.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [D, mem_filter, mem_univ, true_and] at ha hb
        by_contra hab
        exact hnb ⟨x, a, b, by rw [hx]; exact_mod_cast hjr.le, ha.1, hb.1, hab,
          by rw [hx]; exact ha.2, by rw [hx]; exact hb.2⟩
      have hsub : univ.filter (G.Adj x) ⊆ C x ∪ D := by
        intro y hy
        simp only [mem_filter, mem_univ, true_and] at hy
        simp only [C, D, mem_union, mem_filter, mem_univ, true_and, hy]
        by_cases hyj : G.edist s y ≤ (j : ℕ∞)
        · exact Or.inr hyj
        · left
          have h1 := edist_le_add_one_of_adj (u := s) hy
          rw [hx] at h1
          exact enat_eq_succ_of h1 hyj
      have hdx : δ ≤ deg G x := hdeg x (by rw [hx]; exact_mod_cast hjr)
      rw [deg_eq_card_filter] at hdx
      have := (card_le_card hsub).trans (card_union_le _ _)
      omega
    -- children of distinct nodes are distinct
    have hdisj : (L j : Set V).PairwiseDisjoint C := by
      intro x hx x' hx' hxx'
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, L] at hx hx'
      rw [Function.onFun, Finset.disjoint_left]
      intro y hy hy'
      simp only [C, mem_filter, mem_univ, true_and] at hy hy'
      have hle : G.edist s x ≤ G.edist s y := by
        rw [hx, hy.2]; exact_mod_cast (by omega : j ≤ j + 1)
      have hle' : G.edist s x' ≤ G.edist s y := by
        rw [hx', hy.2]; exact_mod_cast (by omega : j ≤ j + 1)
      exact hnb ⟨y, x, x', by rw [hy.2]; exact_mod_cast hjr, hy.1.symm, hy'.1.symm, hxx',
        hle, hle'⟩
    have hsub : (L j).biUnion C ⊆ L (j + 1) := by
      intro y hy
      simp only [mem_biUnion, C, mem_filter, mem_univ, true_and] at hy
      obtain ⟨_, _, _, hy⟩ := hy
      rw [hL]; exact hy
    calc (L j).card * (δ - 1) = ∑ _x ∈ L j, (δ - 1) := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ L j, (C x).card := sum_le_sum hC
      _ = ((L j).biUnion C).card := (card_biUnion hdisj).symm
      _ ≤ (L (j + 1)).card := card_le_card hsub
  -- sizes of the levels
  have level : ∀ i, i < r → δ * (δ - 1) ^ i ≤ (L (i + 1)).card := by
    intro i
    induction i with
    | zero =>
      intro hr
      have hds : δ ≤ deg G s := hdeg s (by simp; exact_mod_cast hr)
      rw [deg_eq_card_filter] at hds
      have hsub : univ.filter (G.Adj s) ⊆ L 1 := by
        intro y hy
        simp only [mem_filter, mem_univ, true_and] at hy
        rw [hL, Nat.cast_one]; exact edist_eq_one_iff_adj.2 hy
      simpa using hds.trans (card_le_card hsub)
    | succ i ih =>
      intro hr
      have h1 := ih (by omega)
      have h2 := step (i + 1) (by omega) hr
      calc δ * (δ - 1) ^ (i + 1) = δ * (δ - 1) ^ i * (δ - 1) := by ring
        _ ≤ (L (i + 1)).card * (δ - 1) := Nat.mul_le_mul_right _ h1
        _ ≤ _ := h2
  -- the ball contains the disjoint union of the levels `0, …, r`
  have hdisjL : ((range (r + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint L := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hi hj
    rw [hL] at hi hj
    rw [hi] at hj
    exact hij (by exact_mod_cast hj)
  have hsubB : (((range (r + 1)).biUnion L : Finset V) : Set V) ⊆ cball G s r := by
    intro x hx
    simp only [coe_biUnion, coe_range, Set.mem_Iio, Set.mem_iUnion, mem_coe, hL,
      exists_prop] at hx
    obtain ⟨i, hi, hx⟩ := hx
    simp only [mem_cball, hx]; exact_mod_cast (by omega : i ≤ r)
  have hL0 : 1 ≤ (L 0).card := card_pos.2 ⟨s, by simp [hL]⟩
  calc 1 + δ * ∑ k ∈ range r, (δ - 1) ^ k = 1 + ∑ k ∈ range r, δ * (δ - 1) ^ k := by
        rw [mul_sum]
    _ ≤ (L 0).card + ∑ k ∈ range r, (L (k + 1)).card := by
        gcongr with k hk
        exact level k (mem_range.1 hk)
    _ = ∑ i ∈ range (r + 1), (L i).card := by rw [sum_range_succ']; ring
    _ = ((range (r + 1)).biUnion L).card := (card_biUnion hdisjL).symm
    _ = (((range (r + 1)).biUnion L : Finset V) : Set V).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (cball G s r).ncard := Set.ncard_le_ncard hsubB (Set.toFinite _)

/-- The closed form of the geometric bound: for `δ ≥ 3`,
`δ (1 + (δ-1) + … + (δ-1)^(r-1)) = δ((δ-1)^r - 1)/(δ-2)` (exact division). -/
lemma mul_geomSum_eq {δ : ℕ} (hδ : 3 ≤ δ) (r : ℕ) :
    δ * ∑ k ∈ range r, (δ - 1) ^ k = δ * ((δ - 1) ^ r - 1) / (δ - 2) := by
  have h2 : δ - 2 = δ - 1 - 1 := by omega
  rw [Nat.geomSum_eq (by omega) r, h2,
    Nat.mul_div_assoc _ (Nat.sub_one_dvd_pow_sub_one _ _)]

-- CSLib candidate
/-- Counting core of Lemma 2.2: if every node at distance `< r` from `s` has degree `≥ δ` and the
ball `cball G s r` has no back edges, it has at least `1 + δ((δ-1)^r - 1)/(δ-2)` nodes (the size of
the complete tree of depth `r` with root degree `δ` and inner degree `δ`). For `δ ≤ 2` the
right-hand side is `1` (division by zero is zero in `ℕ`), so no hypothesis on `δ` is needed. -/
theorem card_cball_ge_of_not_hasBackEdges [Finite V]
    (hdeg : ∀ x, G.edist s x < r → δ ≤ deg G x) (hnb : ¬ HasBackEdges G s r) :
    1 + δ * ((δ - 1) ^ r - 1) / (δ - 2) ≤ (cball G s r).ncard := by
  by_cases hδ : 3 ≤ δ
  · rw [← mul_geomSum_eq hδ]
    exact card_cball_ge_sum_of_not_hasBackEdges hdeg hnb
  · have h0 : δ - 2 = 0 := by omega
    rw [h0, Nat.div_zero, add_zero, Nat.one_le_iff_ne_zero, ne_eq,
      Set.ncard_eq_zero (Set.toFinite _)]
    exact Set.nonempty_iff_ne_empty.1 ⟨s, by simp⟩

end Counting

/-! ### Lemma 2.2 -/

section Lemma22

variable [Finite V]

/-- Lemma 2.2 of [Nolin, PODC'26], slightly strengthened: the node of degree `< δ` in (i) can be
taken at distance `< r` from `v`, the bound in (iii) is stated as the geometric sum
`1 + δ(1 + (δ-1) + … + (δ-1)^(r-1))`, and no hypothesis on `r` and `δ` is needed. -/
theorem lemma_2_2' (G : SimpleGraph V) (δ : ℕ) (v : V) (r : ℕ) :
    (∃ u, G.edist v u < r ∧ deg G u < δ) ∨ ContainsCycle G (cball G v r) ∨
      1 + δ * ∑ k ∈ range r, (δ - 1) ^ k ≤ (cball G v r).ncard := by
  by_cases h1 : ∃ u, G.edist v u < r ∧ deg G u < δ
  · exact Or.inl h1
  right
  by_cases h2 : HasBackEdges G v r
  · exact Or.inl (containsCycle_of_hasBackEdges h2)
  right
  push Not at h1
  exact card_cball_ge_sum_of_not_hasBackEdges h1 h2

/-- **Lemma 2.2** of [Nolin, PODC'26]: for any node `v`, integers `r` and `δ ≥ 3`, the inclusive
distance-`r` neighbourhood of `v` contains (i) a node of degree `< δ`, or (ii) a cycle, or
(iii) at least `1 + δ((δ-1)^r - 1)/(δ-2)` nodes. (The paper assumes `r ≥ 1`; this is not needed.
The hypothesis `δ ≥ 3` makes the closed form meaningful; see `lemma_2_2'` for a version without it.)
-/
theorem lemma_2_2 (G : SimpleGraph V) {δ : ℕ} (hδ : 3 ≤ δ) (v : V) (r : ℕ) :
    (∃ u ∈ cball G v r, deg G u < δ) ∨ ContainsCycle G (cball G v r) ∨
      1 + δ * ((δ - 1) ^ r - 1) / (δ - 2) ≤ (cball G v r).ncard := by
  rcases lemma_2_2' G δ v r with ⟨u, hu, hdu⟩ | h | h
  · exact Or.inl ⟨u, by simp only [mem_cball]; exact hu.le, hdu⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by rwa [← mul_geomSum_eq hδ]))

end Lemma22

section InParticular

variable [Fintype V]

/-- The "in particular" part of Lemma 2.2 of [Nolin, PODC'26], for any radius `r` with
`n ≤ (δ-1)^r` (`n` the number of nodes): the distance-`r` neighbourhood of every node contains a
node of degree `< δ` or a cycle. -/
theorem lemma_2_2_of_card_le (G : SimpleGraph V) {δ : ℕ} (hδ : 3 ≤ δ) (v : V) {r : ℕ}
    (hr : Fintype.card V ≤ (δ - 1) ^ r) :
    (∃ u ∈ cball G v r, deg G u < δ) ∨ ContainsCycle G (cball G v r) := by
  -- a one-node graph: `v` itself has degree `0`
  by_cases hn : Fintype.card V ≤ 1
  · left
    refine ⟨v, by simp, ?_⟩
    have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.1 hn
    have : G.neighborSet v = ∅ := by
      ext u; simp only [mem_neighborSet, Set.mem_empty_iff_false, iff_false]
      intro h; exact h.ne (Subsingleton.elim _ _)
    rw [deg, this, Set.ncard_empty]; omega
  rcases lemma_2_2 G hδ v r with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  exfalso
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr; omega
  have hball : (cball G v r).ncard ≤ Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  obtain ⟨d, rfl⟩ : ∃ d, δ = d + 3 := ⟨δ - 3, by omega⟩
  have e1 : d + 3 - 1 = d + 2 := by omega
  have e2 : d + 3 - 2 = d + 1 := by omega
  rw [e1] at hr h
  rw [e2] at h
  obtain ⟨q, hq⟩ : d + 1 ∣ (d + 2) ^ r - 1 := by
    simpa using Nat.sub_one_dvd_pow_sub_one (d + 2) r
  rw [hq, Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by omega)] at h
  have hpow : d + 2 ≤ (d + 2) ^ r := Nat.le_self_pow hr0 _
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · simp at hq; omega
    · exact hq0
  have e3 : (d + 3) * q = (d + 1) * q + 2 * q := by ring
  omega

/-- The "in particular" part of Lemma 2.2 of [Nolin, PODC'26] (with the paper's typo "a node of
degree `δ`" corrected to "a node of degree `< δ`"): in an `n`-node graph, the inclusive
distance-`⌈log_{δ-1} n⌉` neighbourhood of every node contains a node of degree `< δ` or a cycle. -/
theorem lemma_2_2_clog (G : SimpleGraph V) {δ : ℕ} (hδ : 3 ≤ δ) (v : V) :
    (∃ u ∈ cball G v (Nat.clog (δ - 1) (Fintype.card V)), deg G u < δ) ∨
      ContainsCycle G (cball G v (Nat.clog (δ - 1) (Fintype.card V))) :=
  lemma_2_2_of_card_le G hδ v (Nat.le_pow_clog (by omega) _)

end InParticular

end SinklessOrientation
