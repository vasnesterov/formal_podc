import Papers.PODC2016.PowerLawLabeling.Defs

/-!
# Realizing a degree sequence around an induced subgraph (the construction of Theorem 3)

The paper's Theorem 3 builds the power-law graph by greedily adding edges between "unprocessed"
vertices (vertices whose degree is still below the target) in three phases. We replace every
greedy loop by a *maximal* graph (`exists_maximal_fill`): among all graphs between `G₀` and
`G₀ ⊔ P` respecting the degree targets, take one with the most edges; then no allowed pair of
unsaturated vertices is non-adjacent.

`realize`: given targets `t`, a graph `H₀` living on a set `A`, a set `B` of "middle" vertices
(targets in `[1, T]`), a set `L` of leaves (target `1`), all other targets `0`, enough middle
vertices and leaves, and an even target sum, there is a graph with degrees exactly `t` that
induces `H₀` on `A`. The phases are: `A`–`B` edges (`bip_phase`), `B`–`B` edges (maximal fill,
the remaining unsaturated `B`-vertices form a clique — the paper claims "at most one" remains,
which is false in general), unsaturated `B`–`L` edges, and `L`–`L` edges; parity rules out a
last unsaturated leaf.
-/

namespace Podc.PowerLawLabeling

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Allowed pairs between `X` and `Y`. -/
def bip (X Y : Finset V) : SimpleGraph V := SimpleGraph.fromRel fun a b => a ∈ X ∧ b ∈ Y

/-- All pairs inside `Z`. -/
def clq (Z : Finset V) : SimpleGraph V := SimpleGraph.fromRel fun a b => a ∈ Z ∧ b ∈ Z

theorem bip_adj {X Y : Finset V} {a b : V} :
    (bip X Y).Adj a b ↔ a ≠ b ∧ (a ∈ X ∧ b ∈ Y ∨ b ∈ X ∧ a ∈ Y) := by
  simp [bip]

theorem clq_adj {Z : Finset V} {a b : V} : (clq Z).Adj a b ↔ a ≠ b ∧ a ∈ Z ∧ b ∈ Z := by
  simp only [clq, fromRel_adj]; tauto

theorem deg_mono {G G' : SimpleGraph V} (h : G ≤ G') (v : V) : deg G v ≤ deg G' v :=
  Set.ncard_le_ncard (fun _ hw => h hw) (Set.toFinite _)

theorem deg_eq_card_neighborFinset (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    deg G v = G.degree v := by
  unfold deg
  rw [← card_neighborFinset_eq_degree, ← Set.ncard_coe_finset, coe_neighborFinset]

theorem card_filter_adj_le_deg (G : SimpleGraph V) (v : V) (S : Finset V) [DecidablePred (G.Adj v)] :
    #(S.filter (G.Adj v)) ≤ deg G v := by
  unfold deg
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun w hw => by simp at hw; exact hw.2) (Set.toFinite _)

theorem deg_sup_edge (G : SimpleGraph V) {u v : V} (huv : u ≠ v) (hn : ¬ G.Adj u v) (w : V) :
    deg (G ⊔ edge u v) w = deg G w + (if w = u ∨ w = v then 1 else 0) := by
  unfold deg
  by_cases hwu : w = u
  · subst hwu
    have : (G ⊔ edge w v).neighborSet w = insert v (G.neighborSet w) := by
      ext x; simp only [mem_neighborSet, sup_adj, edge_adj, Set.mem_insert_iff]
      by_cases hx : x = v
      · subst hx; simp [huv]
      · simp [hx]; intro h; exact absurd h huv
    rw [this, Set.ncard_insert_of_notMem (by simpa using hn) (Set.toFinite _)]
    simp
  by_cases hwv : w = v
  · subst hwv
    have : (G ⊔ edge u w).neighborSet w = insert u (G.neighborSet w) := by
      ext x; simp only [mem_neighborSet, sup_adj, edge_adj, Set.mem_insert_iff]
      by_cases hx : x = u
      · subst hx; simp [huv, hwu]
      · simp [hx]; intro h; exact absurd h huv.symm
    rw [this, Set.ncard_insert_of_notMem (by simpa [G.adj_comm] using hn) (Set.toFinite _)]
    simp
  · have : (G ⊔ edge u v).neighborSet w = G.neighborSet w := by
      ext x; simp [edge_adj, hwu, hwv]
    rw [this]; simp [hwu, hwv]

-- CSLib candidate (degree-constrained edge-maximal supergraphs)
/-- **Maximal fill.** Among the graphs `G₀ ≤ G ≤ G₀ ⊔ P` with degrees `≤ t`, one with the most
edges leaves no allowed pair of unsaturated vertices non-adjacent. (This replaces the paper's
greedy "while there exists a pair of unprocessed vertices, add an edge" loops.) -/
theorem exists_maximal_fill (G₀ P : SimpleGraph V) (t : V → ℕ) (h₀ : ∀ v, deg G₀ v ≤ t v) :
    ∃ G : SimpleGraph V, G₀ ≤ G ∧ G ≤ G₀ ⊔ P ∧ (∀ v, deg G v ≤ t v) ∧
      ∀ u v, P.Adj u v → ¬ G.Adj u v → deg G u < t u → deg G v < t v → False := by
  classical
  let S := univ.filter (fun G : SimpleGraph V => G₀ ≤ G ∧ G ≤ G₀ ⊔ P ∧ ∀ v, deg G v ≤ t v)
  have hS : G₀ ∈ S := by simp [S, h₀]
  obtain ⟨G, hG, hmax⟩ := S.exists_max_image (fun G => G.edgeSet.ncard) ⟨G₀, hS⟩
  simp only [S, mem_filter, mem_univ, true_and] at hG
  refine ⟨G, hG.1, hG.2.1, hG.2.2, fun u v hP hn hu hv => ?_⟩
  have huv : u ≠ v := hP.ne
  have hmem : G ⊔ edge u v ∈ S := by
    simp only [S, mem_filter, mem_univ, true_and]
    refine ⟨hG.1.trans le_sup_left, sup_le hG.2.1 ?_, fun w => ?_⟩
    · rw [edge_le_iff]; exact Or.inr (Or.inr hP)
    · rw [deg_sup_edge G huv hn]
      have := hG.2.2 w
      split_ifs with h
      · rcases h with rfl | rfl <;> omega
      · omega
  have h1 := hmax _ hmem
  have h2 : G.edgeSet.ncard < (G ⊔ edge u v).edgeSet.ncard :=
    Set.ncard_lt_ncard (edgeSet_ssubset_edgeSet.2 (lt_sup_edge G u v huv hn)) (Set.toFinite _)
  omega

-- CSLib candidate (degree-constrained edge-maximal supergraphs)
/-- **Bipartite phase.** If the vertices of `Y` are isolated in `G₀` and have positive targets,
and `Y` is large, a maximal fill with the pairs `X × Y` saturates all of `X`. -/
theorem bip_phase (G₀ : SimpleGraph V) (t : V → ℕ) (h₀ : ∀ v, deg G₀ v ≤ t v) (X Y : Finset V)
    (hXY : Disjoint X Y) (hY0 : ∀ y ∈ Y, ∀ w, ¬ G₀.Adj y w) (hY1 : ∀ y ∈ Y, 1 ≤ t y)
    (hbig : ∀ x ∈ X, t x + ∑ x' ∈ X, t x' ≤ #Y) :
    ∃ G, G₀ ≤ G ∧ G ≤ G₀ ⊔ bip X Y ∧ (∀ v, deg G v ≤ t v) ∧ ∀ x ∈ X, deg G x = t x := by
  classical
  obtain ⟨G, h1, h2, h3, hmax⟩ := exists_maximal_fill G₀ (bip X Y) t h₀
  refine ⟨G, h1, h2, h3, fun x hx => ?_⟩
  by_contra hne
  have hlt : deg G x < t x := lt_of_le_of_ne (h3 x) hne
  -- every `y ∈ Y` is a neighbour of `x` or saturated
  have hcover : Y ⊆ Y.filter (G.Adj x) ∪ Y.filter (fun y => deg G y = t y) := by
    intro y hy
    by_cases hadj : G.Adj x y
    · exact mem_union_left _ (mem_filter.2 ⟨hy, hadj⟩)
    · refine mem_union_right _ (mem_filter.2 ⟨hy, ?_⟩)
      by_contra hy'
      have hxy : x ≠ y := fun h => disjoint_left.1 hXY hx (h ▸ hy)
      exact hmax x y (bip_adj.2 ⟨hxy, Or.inl ⟨hx, hy⟩⟩) hadj hlt
        (lt_of_le_of_ne (h3 y) hy')
  -- neighbours of `y ∈ Y` lie in `X`
  have hnbr : ∀ y ∈ Y, ∀ w, G.Adj y w → w ∈ X := by
    intro y hy w hw
    rcases h2 hw with h | h
    · exact absurd h (hY0 y hy w)
    · rcases (bip_adj.1 h).2 with ⟨hyX, _⟩ | ⟨hwX, _⟩
      · exact absurd hy (disjoint_left.1 hXY hyX)
      · exact hwX
  have hdegY : ∀ y ∈ Y, deg G y = #(X.filter (G.Adj y)) := by
    intro y hy
    unfold deg
    rw [← Set.ncard_coe_finset]
    congr 1
    ext w; simp only [mem_neighborSet, coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨hnbr y hy w h, h⟩, fun h => h.2⟩
  have hsat : #(Y.filter (fun y => deg G y = t y)) ≤ ∑ x' ∈ X, t x' := by
    calc #(Y.filter (fun y => deg G y = t y))
        = ∑ y ∈ Y.filter (fun y => deg G y = t y), 1 := by simp
      _ ≤ ∑ y ∈ Y.filter (fun y => deg G y = t y), deg G y := by
          refine sum_le_sum fun y hy => ?_
          rw [mem_filter] at hy; rw [hy.2]; exact hY1 y hy.1
      _ ≤ ∑ y ∈ Y, deg G y := sum_le_sum_of_subset (filter_subset _ _)
      _ = ∑ y ∈ Y, #(X.filter (G.Adj y)) := sum_congr rfl hdegY
      _ = ∑ x' ∈ X, #(Y.filter (G.Adj x')) := by
          simp only [card_eq_sum_ones, sum_filter]
          rw [sum_comm]
          refine sum_congr rfl fun x' _ => sum_congr rfl fun y _ => ?_
          simp [G.adj_comm]
      _ ≤ ∑ x' ∈ X, deg G x' := sum_le_sum fun x' _ => card_filter_adj_le_deg G x' Y
      _ ≤ ∑ x' ∈ X, t x' := sum_le_sum fun x' _ => h3 x'
  have hc := card_le_card hcover
  have hu := card_union_le (Y.filter (G.Adj x)) (Y.filter (fun y => deg G y = t y))
  have hn := card_filter_adj_le_deg G x Y
  have := hbig x hx
  omega

theorem sum_deg_even (G : SimpleGraph V) : Even (∑ v, deg G v) := by
  classical
  simp only [deg_eq_card_neighborFinset]
  rw [sum_degrees_eq_twice_card_edges]
  exact even_two_mul _

/-- **Realization.** See the module docstring. -/
theorem realize (t : V → ℕ) (H₀ : SimpleGraph V) (A B L : Finset V) (T T' : ℕ)
    (hAB : Disjoint A B) (hAL : Disjoint A L) (hBL : Disjoint B L)
    (hH : ∀ u v, H₀.Adj u v → u ∈ A ∧ v ∈ A) (hHt : ∀ v, deg H₀ v ≤ t v)
    (hzero : ∀ v, v ∉ A → v ∉ B → v ∉ L → t v = 0)
    (hB : ∀ b ∈ B, 1 ≤ t b ∧ t b ≤ T) (hL : ∀ l ∈ L, t l = 1) (hA : ∀ a ∈ A, t a ≤ T')
    (hBcard : T' + #A * T' ≤ #B) (hLcard : T + T * T ≤ #L) (heven : Even (∑ v, t v)) :
    ∃ G : SimpleGraph V, H₀ ≤ G ∧ (∀ u v, u ∈ A → v ∈ A → (G.Adj u v ↔ H₀.Adj u v)) ∧
      ∀ v, deg G v = t v := by
  classical
  -- Phase 1: `A`–`B`
  obtain ⟨G1, h1a, h1b, h1c, h1d⟩ := bip_phase H₀ t hHt A B hAB
    (fun y hy w hw => disjoint_left.1 hAB (hH y w hw).1 hy) (fun y hy => (hB y hy).1)
    (fun x hx => by
      have : ∑ x' ∈ A, t x' ≤ #A * T' := by
        simpa using sum_le_sum fun x' hx' => hA x' hx'
      have := hA x hx; omega)
  -- Phase 2: `B`–`B`
  obtain ⟨G2, h2a, h2b, h2c, h2d⟩ := exists_maximal_fill G1 (clq B) t h1c
  set D := B.filter (fun b => deg G2 b < t b) with hD
  have hDclq : ∀ u ∈ D, ∀ v ∈ D, u ≠ v → G2.Adj u v := by
    intro u hu v hv huv
    rw [mem_filter] at hu hv
    by_contra h
    exact h2d u v (clq_adj.2 ⟨huv, hu.1, hv.1⟩) h hu.2 hv.2
  have hDcard : #D ≤ T := by
    rcases D.eq_empty_or_nonempty with h | ⟨d, hd⟩
    · rw [h]; simp
    · have h1 : #(D.erase d) ≤ deg G2 d := by
        refine le_trans (card_le_card fun w hw => ?_) (card_filter_adj_le_deg G2 d D)
        rw [mem_erase] at hw
        exact mem_filter.2 ⟨hw.2, hDclq d hd w hw.2 (Ne.symm hw.1)⟩
      have h2 := card_erase_of_mem hd
      have h3 := (mem_filter.1 hd).2
      have h4 := (hB d (mem_filter.1 hd).1).2
      omega
  have hDB : D ⊆ B := filter_subset _ _
  -- edges so far
  have hG2le : G2 ≤ H₀ ⊔ bip A B ⊔ clq B := by
    intro u v h
    rcases h2b h with h | h
    · rcases h1b h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hL0 : ∀ l ∈ L, ∀ w, ¬ G2.Adj l w := by
    intro l hl w hw
    have hlA : l ∉ A := fun h => disjoint_left.1 hAL h hl
    have hlB : l ∉ B := fun h => disjoint_left.1 hBL h hl
    rcases hG2le hw with (h | h) | h
    · exact hlA (hH l w h).1
    · rcases (bip_adj.1 h).2 with ⟨h', _⟩ | ⟨_, h'⟩
      · exact hlA h'
      · exact hlB h'
    · exact hlB (clq_adj.1 h).2.1
  -- Phase 3: unsaturated `B` – `L`
  obtain ⟨G3, h3a, h3b, h3c, h3d⟩ := bip_phase G2 t h2c D L
    (disjoint_of_subset_left hDB hBL) hL0 (fun l hl => (hL l hl).ge)
    (fun x hx => by
      have : ∑ x' ∈ D, t x' ≤ #D * T := by
        simpa using sum_le_sum fun x' hx' => (hB x' (hDB hx')).2
      have h5 := (hB x (hDB hx)).2
      have h6 : #D * T ≤ T * T := Nat.mul_le_mul_right T hDcard
      omega)
  -- Phase 4: `L`–`L`
  obtain ⟨G4, h4a, h4b, h4c, h4d⟩ := exists_maximal_fill G3 (clq L) t h3c
  have h14 : G1 ≤ G4 := h2a.trans (h3a.trans h4a)
  have hsat : ∀ {G : SimpleGraph V}, G ≤ G4 → ∀ v, deg G v = t v → deg G4 v = t v :=
    fun {G} hG v hv => le_antisymm (h4c v) (hv ▸ deg_mono hG v)
  -- all vertices except possibly one leaf are saturated
  have hsatA : ∀ v ∉ L, deg G4 v = t v := by
    intro v hvL
    by_cases hvA : v ∈ A
    · exact hsat h14 v (h1d v hvA)
    by_cases hvB : v ∈ B
    · by_cases hvD : v ∈ D
      · exact hsat h4a v (h3d v hvD)
      · have : deg G2 v = t v := by
          have := h2c v; rw [hD, mem_filter] at hvD; push_neg at hvD; exact le_antisymm this (hvD hvB)
        exact hsat (h3a.trans h4a) v this
    · have := hzero v hvA hvB hvL
      have := h4c v; omega
  have hLdef : ∀ l ∈ L, ∀ l' ∈ L, deg G4 l < t l → deg G4 l' < t l' → l = l' := by
    intro l hl l' hl' h h'
    by_contra hne
    refine h4d l l' (clq_adj.2 ⟨hne, hl, hl'⟩) (fun hadj => ?_) h h'
    have : deg G4 l = 0 := by have := hL l hl; omega
    unfold deg at this
    rw [Set.ncard_eq_zero (Set.toFinite _)] at this
    exact (Set.eq_empty_iff_forall_notMem.1 this) l' hadj
  have hall : ∀ v, deg G4 v = t v := by
    by_contra hall
    push_neg at hall
    obtain ⟨w, hw⟩ := hall
    have hwL : w ∈ L := by by_contra h; exact hw (hsatA w h)
    have hwlt : deg G4 w < t w := lt_of_le_of_ne (h4c w) hw
    have hdeg : ∀ v, deg G4 v + (if v = w then 1 else 0) = t v := by
      intro v
      by_cases hvw : v = w
      · subst hvw; simp only [ite_true]; have := hL v hwL; omega
      · simp only [hvw, ite_false, add_zero]
        by_cases hvL : v ∈ L
        · by_contra hne
          exact hvw (hLdef v hvL w hwL (lt_of_le_of_ne (h4c v) hne) hwlt)
        · exact hsatA v hvL
    have hsum : ∑ v, t v = ∑ v, deg G4 v + 1 := by
      rw [← sum_congr rfl fun v _ => hdeg v, sum_add_distrib]
      simp
    rw [hsum] at heven
    exact (Nat.not_even_iff_odd.2 (sum_deg_even G4).add_one) heven
  -- `G4` induces `H₀` on `A`
  have hG4le : G4 ≤ H₀ ⊔ bip A B ⊔ clq B ⊔ bip D L ⊔ clq L := by
    intro u v h
    rcases h4b h with h | h
    · rcases h3b h with h | h
      · rcases hG2le h with (h | h) | h
        · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
        · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
    · exact Or.inr h
  refine ⟨G4, (h1a.trans h14), fun u v hu hv => ⟨fun h => ?_, fun h => h14 (h1a h)⟩, hall⟩
  have huB : u ∉ B := fun h => disjoint_left.1 hAB hu h
  have hvB : v ∉ B := fun h => disjoint_left.1 hAB hv h
  have huL : u ∉ L := fun h => disjoint_left.1 hAL hu h
  have hvL : v ∉ L := fun h => disjoint_left.1 hAL hv h
  rcases hG4le h with (((h | h) | h) | h) | h
  · exact h
  · rcases (bip_adj.1 h).2 with ⟨_, h'⟩ | ⟨_, h'⟩ <;> contradiction
  · exact absurd (clq_adj.1 h).2.1 huB
  · rcases (bip_adj.1 h).2 with ⟨_, h'⟩ | ⟨_, h'⟩ <;> contradiction
  · exact absurd (clq_adj.1 h).2.1 huL

end Podc.PowerLawLabeling
