import Papers.PODC2016.ShortcutsNoEmbedding.Defs

/-!
# Lemma 1 of [HIZ16]: block parameter bounds dilation

* `lemma_1`: for a connected part `P`, a `T`-restricted shortcut `H` (tree depth `≤ D`) and two
  vertices `x, y ∈ P`, the graph `G[P] + H` contains a walk from `x` to `y` of length
  `< blockParam P H · (2D + 1)`. This is the paper's proof (contract the block components; the
  contracted graph is connected with `b` nodes; each block has diameter `≤ 2D`).
* `lemma_1_dilation`: if moreover every component of `(V, H)` touched by `H` meets `P`
  (`BlocksMeetPart`), the full dilation (diameter of `G[P] + H` on `P ∪ V(H)`) is `≤ b (2D + 1)`.
* `lemma_1_literal_false`: Lemma 1 as literally stated (dilation = diameter of `E_G[P] ∪ H` with
  `H` an arbitrary `T`-restricted edge set and block components as in Definition 5) is false:
  on the path `0 – 1 – 2` rooted at `0`, the part `{2}` with `H = {01}` has one block component
  but `E_G[P] ∪ H` is disconnected. `lemma_1_literal_false_edgeSet`: the same on the path
  `0 – … – 4` with `P = {4}`, `H = {01, 23}`, where already the edge set `{01, 23}` is disconnected
  (so the failure does not depend on whether `P` belongs to the vertex set of `E_G[P] ∪ H`).
-/

set_option linter.unusedSectionVars false

namespace ShortcutsNoEmbedding

open SimpleGraph Finset RootedTree

variable {V : Type*} {G : SimpleGraph V} {T : G.RootedTree}

/-- **Lemma 1 of [HIZ16]** (dilation between vertices of the part). Let `T` be a rooted spanning
tree of depth `≤ D`, `P` a connected part and `H` a `T`-restricted set of edges with block
parameter `b = blockParam P H` (Definition 5). Any two vertices of `P` are joined in
`G[P] + H` by a walk of length `≤ b (2D + 1) - 1`. -/
theorem lemma_1 {D : ℕ} (hT : T.DepthLE D) {P : Finset V}
    (hP : (G.induce (P : Set V)).Connected) {H : Finset (Sym2 V)} (hH : T.Restricts H) {x y : V}
    (hx : x ∈ P) (hy : y ∈ P) :
    ∃ q : (partGraph G P H).Walk x y, q.length + 1 ≤ blockParam P H * (2 * D + 1) := by
  classical
  let S : Set (blockGraph H).ConnectedComponent :=
    (blockGraph H).connectedComponentMk '' (P : Set V)
  -- The contracted graph: two blocks are adjacent if a `G`-edge inside `P` joins them.
  let Bg : SimpleGraph S := fromRel fun c c' => ∃ u ∈ P, ∃ v ∈ P, G.Adj u v ∧
    (blockGraph H).connectedComponentMk u = c.1 ∧ (blockGraph H).connectedComponentMk v = c'.1
  have hfin : S.Finite := (P.finite_toSet).image _
  have : Fintype S := hfin.fintype
  have hcard : Fintype.card S = blockParam P H := by
    rw [blockParam, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  -- Lifting a walk in the contracted graph to a walk in `G[P] + H`.
  have lift : ∀ (c c' : S) (p : Bg.Walk c c') (x y : V),
      (blockGraph H).connectedComponentMk x = c.1 →
      (blockGraph H).connectedComponentMk y = c'.1 →
      ∃ q : (partGraph G P H).Walk x y, q.length ≤ p.length * (2 * D + 1) + 2 * D := by
    intro c c' p
    induction p with
    | nil =>
      intro x y hx hy
      obtain ⟨q, hq⟩ := exists_partGraph_walk_of_reachable (P := P) hT hH
        (ConnectedComponent.exact (hx.trans hy.symm))
      exact ⟨q, by simpa using hq⟩
    | @cons c c'' c' h p ih =>
      intro x y hx hy
      rw [fromRel_adj] at h
      obtain ⟨u, hu, v, hv, huv, hcu, hcv⟩ : ∃ u ∈ P, ∃ v ∈ P, G.Adj u v ∧
          (blockGraph H).connectedComponentMk u = c.1 ∧
          (blockGraph H).connectedComponentMk v = c''.1 := by
        rcases h.2 with h | ⟨u, hu, v, hv, huv, h1, h2⟩
        · exact h
        · exact ⟨v, hv, u, hu, huv.symm, h2, h1⟩
      obtain ⟨q1, hq1⟩ := exists_partGraph_walk_of_reachable (P := P) hT hH
        (ConnectedComponent.exact (hx.trans hcu.symm))
      obtain ⟨q2, hq2⟩ := ih v y hcv hy
      have hadj : (partGraph G P H).Adj u v := ⟨huv, Or.inl ⟨hu, hv⟩⟩
      refine ⟨q1.append (Walk.cons hadj q2), ?_⟩
      simp only [Walk.length_append, Walk.length_cons]
      have : (p.length + 1) * (2 * D + 1) = p.length * (2 * D + 1) + 2 * D + 1 := by ring
      omega
  -- The contracted graph is connected since `G[P]` is.
  let f : ↥(P : Set V) → S := fun a => ⟨(blockGraph H).connectedComponentMk a.1, a.1, a.2, rfl⟩
  have conn : ∀ a b : ↥(P : Set V), Bg.Reachable (f a) (f b) := by
    intro a b
    obtain ⟨p⟩ := hP.preconnected a b
    induction p with
    | nil => rfl
    | @cons a c b h p ih =>
      refine Reachable.trans ?_ ih
      by_cases hac : f a = f c
      · rw [hac]
      · apply Adj.reachable
        rw [fromRel_adj]
        exact ⟨hac, Or.inl ⟨a.1, a.2, c.1, c.2, by simpa using h, rfl, rfl⟩⟩
  obtain ⟨p⟩ := conn ⟨x, hx⟩ ⟨y, hy⟩
  have hlen : p.bypass.length < Fintype.card S := p.bypass_isPath.length_lt
  obtain ⟨q, hq⟩ := lift _ _ p.bypass x y rfl rfl
  refine ⟨q, ?_⟩
  rw [← hcard]
  calc q.length + 1 ≤ (p.bypass.length + 1) * (2 * D + 1) := by
        have : (p.bypass.length + 1) * (2 * D + 1) = p.bypass.length * (2 * D + 1) + 2 * D + 1 :=
          by ring
        omega
    _ ≤ Fintype.card S * (2 * D + 1) := Nat.mul_le_mul_right _ hlen

/-- **Lemma 1 of [HIZ16]** (dilation `< b (2D + 1)` between part vertices, as a distance bound). -/
theorem lemma_1_dist {D : ℕ} (hT : T.DepthLE D) {P : Finset V}
    (hP : (G.induce (P : Set V)).Connected) {H : Finset (Sym2 V)} (hH : T.Restricts H) {x y : V}
    (hx : x ∈ P) (hy : y ∈ P) :
    (partGraph G P H).Reachable x y ∧
      (partGraph G P H).dist x y < blockParam P H * (2 * D + 1) := by
  obtain ⟨q, hq⟩ := lemma_1 hT hP hH hx hy
  exact ⟨q.reachable, by have := dist_le q; omega⟩

/-- **Lemma 1 of [HIZ16]** (full dilation): if every component of `(V, H)` touched by `H` contains
a vertex of `P` (always achievable by dropping the other components, which does not change the
block parameter), the dilation of `H` — the diameter of `G[P] + H` on `P ∪ V(H)` — is at most
`b (2D + 1)`. -/
theorem lemma_1_dilation [DecidableEq V] {D : ℕ} (hT : T.DepthLE D) {P : Finset V}
    (hP : (G.induce (P : Set V)).Connected) {H : Finset (Sym2 V)} (hH : T.Restricts H)
    (hB : BlocksMeetPart P H) {b : ℕ} (hb : blockParam P H ≤ b) :
    G.DilationLE P H (b * (2 * D + 1)) := by
  have := dilationLE_of_numBlocks_le hT hP hH hB
    (b := b) (by rw [← blockParam_eq_numBlocks hB]; exact_mod_cast hb)
  exact_mod_cast this

/-! ### The literal statement fails -/

/-- The path `0 - 1 - 2` rooted at `0`. -/
def pathTree : (pathGraph 3).RootedTree where
  root := 0
  parent := ![0, 0, 1]
  depth v := v.val
  parent_root := rfl
  depth_root := rfl
  depth_parent := by decide
  adj_parent v hv := by
    fin_cases v <;> simp_all [pathGraph_adj]

/-- **Lemma 1 of [HIZ16] is false as literally stated.** Definition 4 allows a `T`-restricted
`H_i` to contain tree edges far from `P_i`, and Definition 5 counts only the components of
`(V, H_i)` containing a vertex of `P_i`. On the path `0 – 1 – 2` rooted at `0` (depth `2`), the
part `P = {2}` with `H = {01}` has block parameter `1`, but `E_G[P] ∪ H` does not connect `2` with
the endpoints of `H`, so its diameter (the dilation) is infinite, not `≤ 1 · (2·2 + 1)`. -/
theorem lemma_1_literal_false :
    (pathGraph 3).Connected ∧ pathTree.DepthLE 2 ∧
      ((pathGraph 3).induce (({2} : Finset (Fin 3)) : Set (Fin 3))).Connected ∧
      pathTree.Restricts {s(0, 1)} ∧ blockParam ({2} : Finset (Fin 3)) {s(0, 1)} = 1 ∧
      ∀ d : ℝ, ¬ (pathGraph 3).DilationLE {2} {s(0, 1)} d := by
  have hp2 : ∀ w, ¬ (partGraph (pathGraph 3) {2} {s(0, 1)}).Adj 2 w := by
    rintro w ⟨h1, h2⟩
    fin_cases w <;> simp_all [pathGraph_adj]
  have hpr : ¬ (partGraph (pathGraph 3) {2} {s(0, 1)}).Reachable 0 2 := by
    rintro ⟨p⟩
    cases p.reverse with
    | cons h _ => exact hp2 _ h
  have h0 : (0 : Fin 3) ∈ partVerts {2} {s(0, 1)} := Or.inr ⟨s(0, 1), by simp, by simp⟩
  have h2 : (2 : Fin 3) ∈ partVerts {2} {s(0, 1)} := Or.inl (by simp)
  refine ⟨pathGraph_connected 2, fun v => by fin_cases v <;> decide, ?_, ?_, ?_, ?_⟩
  · rw [Finset.coe_singleton, induce_singleton_eq_top]
    exact connected_top
  · intro e he
    rw [Finset.mem_singleton] at he
    exact ⟨1, by decide, by rw [he]; exact Sym2.eq_swap⟩
  · rw [blockParam, Finset.coe_singleton, Set.image_singleton, Set.ncard_singleton]
  · intro d h
    exact hpr (h 0 h0 2 h2).1

/-- The path `0 – 1 – 2 – 3 – 4` rooted at `0`. -/
def pathTree5 : (pathGraph 5).RootedTree where
  root := 0
  parent := ![0, 0, 1, 2, 3]
  depth v := v.val
  parent_root := rfl
  depth_root := rfl
  depth_parent := by decide
  adj_parent v hv := by
    fin_cases v <;> simp_all [pathGraph_adj]

/-- **Lemma 1 of [HIZ16] is false as literally stated, under any reading of "diameter of
`E_G[P_i] ∪ H_i`".** On the path `0 – 1 – 2 – 3 – 4` rooted at `0` (depth `4`), the part
`P = {4}` with `H = {01, 23}` has block parameter `1`, but the edge set `E_G[P] ∪ H = {01, 23}`
is disconnected: its endpoints `0` and `2` are not connected, whether or not the vertex set of
the graph is taken to include `P`. (In `lemma_1_literal_false` the disconnection only appears when
`P` is part of the vertex set.) -/
theorem lemma_1_literal_false_edgeSet :
    (pathGraph 5).Connected ∧ pathTree5.DepthLE 4 ∧
      ((pathGraph 5).induce (({4} : Finset (Fin 5)) : Set (Fin 5))).Connected ∧
      pathTree5.Restricts {s(0, 1), s(2, 3)} ∧
      blockParam ({4} : Finset (Fin 5)) {s(0, 1), s(2, 3)} = 1 ∧
      ¬ (partGraph (pathGraph 5) {4} {s(0, 1), s(2, 3)}).Reachable 0 2 ∧
      ∀ d : ℝ, ¬ (pathGraph 5).DilationLE {4} {s(0, 1), s(2, 3)} d := by
  have key : ∀ u v, (partGraph (pathGraph 5) {4} {s(0, 1), s(2, 3)}).Adj u v →
      (u.val ≤ 1 ↔ v.val ≤ 1) := by
    intro u v ⟨h1, h2⟩
    fin_cases u <;> fin_cases v <;> simp_all [pathGraph_adj]
  have hpr : ¬ (partGraph (pathGraph 5) {4} {s(0, 1), s(2, 3)}).Reachable 0 2 := by
    rintro ⟨p⟩
    have : ∀ u v (q : (partGraph (pathGraph 5) {4} {s(0, 1), s(2, 3)}).Walk u v),
        (u.val ≤ 1 ↔ v.val ≤ 1) := by
      intro u v q
      induction q with
      | nil => rfl
      | cons h _ ih => exact (key _ _ h).trans ih
    have := this _ _ p
    simp at this
  have h0 : (0 : Fin 5) ∈ partVerts {4} {s(0, 1), s(2, 3)} := Or.inr ⟨s(0, 1), by simp, by simp⟩
  have h2 : (2 : Fin 5) ∈ partVerts {4} {s(0, 1), s(2, 3)} := Or.inr ⟨s(2, 3), by simp, by simp⟩
  refine ⟨pathGraph_connected 4, fun v => by fin_cases v <;> decide, ?_, ?_, ?_, hpr,
    fun d h => hpr (h 0 h0 2 h2).1⟩
  · rw [Finset.coe_singleton, induce_singleton_eq_top]
    exact connected_top
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact ⟨1, by decide, Sym2.eq_swap⟩
    · exact ⟨3, by decide, Sym2.eq_swap⟩
  · rw [blockParam, Finset.coe_singleton, Set.image_singleton, Set.ncard_singleton]

end ShortcutsNoEmbedding
