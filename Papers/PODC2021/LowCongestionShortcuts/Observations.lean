import Cslib.Foundations.Combinatorics.SimpleGraph.ShortcutDilation
import Mathlib

/-!
# Observations 2.6 and 2.7 of [GH21]

[GH21] M. Ghaffari, B. Haeupler. *Low-Congestion Shortcuts for Graphs Excluding Dense Minors.*
PODC 2021 (arXiv:2008.03091).

* `LowCongestionShortcuts.observation_2_6`: a `T`-restricted shortcut with `≤ b` blocks has
  dilation `≤ b (2D + 1)`, provided each block meets its part (`BlocksMeetPart`).
* `LowCongestionShortcuts.observation_2_6_counterexample`: without `BlocksMeetPart` (i.e. as
  literally stated in the paper, with blocks being the components of `(P ∪ V(H), H)`) the
  observation is false: the shortcut graph `G[P] + H` may even be disconnected.
* `LowCongestionShortcuts.observation_2_7`: partial shortcuts give full shortcuts with congestion
  multiplied by `⌊log₂ n⌋ + 1` (the paper says `log₂ n`).
-/

namespace LowCongestionShortcuts

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Observation 2.6 -/

/-- Observation 2.6 of [GH21]: a `T`-restricted shortcut `H` for a connected part `P` with at most
`b` blocks has dilation at most `b (2D + 1)`, where `D` bounds the depth of the rooted spanning
tree `T`. We additionally assume that every block contains a vertex of `P` (`BlocksMeetPart`);
without it the statement is false, see `observation_2_6_counterexample`. -/
theorem observation_2_6 [DecidableEq V] (T : G.RootedTree) {D : ℕ} (hT : T.DepthLE D)
    (P : Finset V) (hP : (G.induce (P : Set V)).Connected) (H : Finset (Sym2 V))
    (hH : T.Restricts H) (hB : BlocksMeetPart P H) {b : ℝ} (hb : (numBlocks P H : ℝ) ≤ b) :
    G.DilationLE P H (b * (2 * D + 1)) :=
  RootedTree.dilationLE_of_numBlocks_le hT hP hH hB hb

/-! ### Counterexample to the literal statement of Observation 2.6 -/

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

/-- Observation 2.6 of [GH21] is false as literally stated (blocks = components of
`(P ∪ V(H), H)`, with no requirement that they meet the part): in the path `0 - 1 - 2` rooted at
`0` (depth `2`, diameter `2`), the part `P = {2}` with the tree-restricted shortcut `H = {01}` has
`2` blocks, but `G[P] + H` does not connect `P ∪ V(H) = {0, 1, 2}`, so its dilation is infinite.
(The block `{0, 1}` does not contain a vertex of `P`.) -/
theorem observation_2_6_counterexample :
    (pathGraph 3).Connected ∧ pathTree.DepthLE 2 ∧
      ((pathGraph 3).induce (({2} : Finset (Fin 3)) : Set (Fin 3))).Connected ∧
      pathTree.Restricts {s(0, 1)} ∧ numBlocks ({2} : Finset (Fin 3)) {s(0, 1)} = 2 ∧
      ¬ BlocksMeetPart ({2} : Finset (Fin 3)) {s(0, 1)} ∧
      ∀ d : ℝ, ¬ (pathGraph 3).DilationLE {2} {s(0, 1)} d := by
  -- In `blockGraph H` and in `G[P] + H`, the vertex `2` is isolated.
  have hb2 : ∀ w, ¬ (blockGraph ({s(0, 1)} : Finset (Sym2 (Fin 3)))).Adj 2 w := by
    intro w h
    rw [blockGraph, fromEdgeSet_adj] at h
    fin_cases w <;> simp_all
  have hp2 : ∀ w, ¬ (partGraph (pathGraph 3) {2} {s(0, 1)}).Adj 2 w := by
    rintro w ⟨h1, h2⟩
    fin_cases w <;> simp_all [pathGraph_adj]
  have hbr : ¬ (blockGraph ({s(0, 1)} : Finset (Sym2 (Fin 3)))).Reachable 0 2 := by
    rintro ⟨p⟩
    cases p.reverse with
    | cons h _ => exact hb2 _ h
  have hpr : ¬ (partGraph (pathGraph 3) {2} {s(0, 1)}).Reachable 0 2 := by
    rintro ⟨p⟩
    cases p.reverse with
    | cons h _ => exact hp2 _ h
  have h0 : (0 : Fin 3) ∈ partVerts {2} {s(0, 1)} := Or.inr ⟨s(0, 1), by simp, by simp⟩
  have h1 : (1 : Fin 3) ∈ partVerts {2} {s(0, 1)} := Or.inr ⟨s(0, 1), by simp, by simp⟩
  have h2 : (2 : Fin 3) ∈ partVerts {2} {s(0, 1)} := Or.inl (by simp)
  refine ⟨pathGraph_connected 2, fun v => by fin_cases v <;> decide, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.coe_singleton, induce_singleton_eq_top]
    exact connected_top
  · intro e he
    rw [Finset.mem_singleton] at he
    exact ⟨1, by decide, by rw [he]; exact Sym2.eq_swap⟩
  · have h01 : (blockGraph ({s(0, 1)} : Finset (Sym2 (Fin 3)))).Adj 0 1 := by
      rw [blockGraph, fromEdgeSet_adj]; simp
    have himg : (blockGraph ({s(0, 1)} : Finset (Sym2 (Fin 3)))).connectedComponentMk ''
        partVerts {2} {s(0, 1)} = {(blockGraph _).connectedComponentMk 0,
          (blockGraph _).connectedComponentMk 2} := by
      ext c
      constructor
      · rintro ⟨z, -, rfl⟩
        fin_cases z
        · exact Or.inl rfl
        · exact Or.inl (ConnectedComponent.eq.2 h01.reachable.symm)
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨0, h0, rfl⟩
        · exact ⟨2, h2, rfl⟩
    rw [numBlocks, himg, Set.ncard_pair]
    exact fun h => hbr (ConnectedComponent.eq.1 h)
  · intro h
    obtain ⟨y, hy, hr⟩ := h 0 h0
    rw [Finset.mem_singleton] at hy
    subst hy
    exact hbr hr
  · intro d h
    exact hpr (h 0 h0 2 h2).1

/-! ### Observation 2.7 -/

/-- Number of parts in a collection of parts is at most the number of vertices. -/
theorem card_le_of_isParts [Fintype V] {ι : Type*} [Fintype ι] {P : ι → Finset V}
    (hP : G.IsParts P) : Fintype.card ι ≤ Fintype.card V := by
  have hne : ∀ i, ∃ v, v ∈ P i := fun i => by
    obtain ⟨⟨v, hv⟩⟩ := (hP.connected i).nonempty
    exact ⟨v, hv⟩
  choose f hf using hne
  refine Fintype.card_le_of_injective f fun i j hij => ?_
  by_contra hne
  exact Finset.disjoint_left.1 (hP.disjoint hne) (hf i) (hij ▸ hf j)

/-- The induction behind Observation 2.7: for `k` parts, iterating partial shortcuts gives a full
shortcut of congestion `≤ c (⌊log₂ k⌋ + 1)`. -/
theorem observation_2_7_aux [DecidableEq V] {D : ℕ} {c b : ℝ}
    (h : G.AdmitsPartialTreeShortcuts D c b) (hc : 0 ≤ c) (T : G.RootedTree)
    (hT : T.DepthLE D) (k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset V)
    (hP : G.IsParts P) (hk : Fintype.card ι = k) :
    ∃ H : ι → Finset (Sym2 V), (∀ i, T.Restricts (H i)) ∧
      G.CongestionLE Finset.univ H (c * (Nat.log 2 k + 1)) ∧
      ∀ i, (numBlocks (P i) (H i) : ℝ) ≤ b ∧ BlocksMeetPart (P i) (H i) := by
  induction k using Nat.strong_induction_on generalizing ι with
  | _ k ih =>
  by_cases hk0 : k = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (hk.trans hk0)
    refine ⟨fun _ => ∅, fun i => isEmptyElim i, ?_, fun i => isEmptyElim i⟩
    intro e _
    simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨J, hJ, H1, hH1r, hH1c, hH1b⟩ := h T hT P hP
  let P' : {i // i ∉ J} → Finset V := fun i => P i.1
  have hP' : G.IsParts P' :=
    ⟨fun i j hij => hP.disjoint fun h => hij (Subtype.ext h), fun i => hP.connected i.1⟩
  have hk' : Fintype.card {i // i ∉ J} = k - J.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hk]
  set m := Fintype.card {i // i ∉ J} with hm
  have hlt : m < k := by omega
  obtain ⟨H2, hH2r, hH2c, hH2b⟩ := ih m hlt P' hP' rfl
  let H : ι → Finset (Sym2 V) := fun i => if hi : i ∈ J then H1 i else H2 ⟨i, hi⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ J
    · simp only [H, hi, ↓reduceDIte]; exact hH1r i hi
    · simp only [H, hi, ↓reduceDIte]; exact hH2r _
  · intro e he
    have hsub : Finset.univ.filter (fun i => e ∈ H i) ⊆ J.filter (fun i => e ∈ H1 i) ∪
        (Finset.univ.filter (fun i : {i // i ∉ J} => e ∈ H2 i)).map
          (Function.Embedding.subtype _) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_cases hiJ : i ∈ J
      · simp only [H, hiJ, ↓reduceDIte] at hi
        exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hiJ, hi⟩)
      · simp only [H, hiJ, ↓reduceDIte] at hi
        exact Finset.mem_union_right _ (Finset.mem_map.2 ⟨⟨i, hiJ⟩, by simpa using hi, rfl⟩)
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_map] at hcard
    have e1 := hH1c e he
    have e2 := hH2c e he
    have hlog : (1 : ℝ) ≤ Nat.log 2 k + 1 := by
      have : (0 : ℝ) ≤ Nat.log 2 k := Nat.cast_nonneg _
      linarith
    by_cases hm0 : m = 0
    · have : (Finset.univ.filter (fun i : {i // i ∉ J} => e ∈ H2 i)).card = 0 := by
        apply Nat.eq_zero_of_le_zero
        calc _ ≤ (Finset.univ : Finset {i // i ∉ J}).card := Finset.card_filter_le _ _
          _ = 0 := by rw [Finset.card_univ, ← hm, hm0]
      rw [this, add_zero] at hcard
      calc _ ≤ ((J.filter fun i => e ∈ H1 i).card : ℝ) := by exact_mod_cast hcard
        _ ≤ c := e1
        _ = c * 1 := (mul_one c).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog hc
    · have hlogm : Nat.log 2 m + 1 ≤ Nat.log 2 k := by
        rw [← Nat.log_mul_base (by norm_num) hm0]
        exact Nat.log_mono_right (by omega)
      have hlogm' : ((Nat.log 2 m : ℕ) : ℝ) + 1 ≤ Nat.log 2 k := by exact_mod_cast hlogm
      calc _ ≤ ((J.filter fun i => e ∈ H1 i).card : ℝ) +
            ((Finset.univ.filter (fun i : {i // i ∉ J} => e ∈ H2 i)).card : ℝ) := by
            exact_mod_cast hcard
        _ ≤ c + c * (Nat.log 2 m + 1) := add_le_add e1 e2
        _ = c * ((Nat.log 2 m + 1) + 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hc
  · intro i
    by_cases hi : i ∈ J
    · simp only [H, hi, ↓reduceDIte]; exact hH1b i hi
    · simp only [H, hi, ↓reduceDIte]; exact hH2b ⟨i, hi⟩

/-- Observation 2.7 of [GH21]: if an `n`-vertex graph `G` admits tree-restricted `c`-congestion
`b`-block partial shortcuts (for trees of depth `≤ D`), then it admits tree-restricted
`c (⌊log₂ n⌋ + 1)`-congestion `b`-block shortcuts. (The paper states congestion `c log₂ n`; the
number of halving rounds needed for `k` parts is `⌊log₂ k⌋ + 1`, e.g. one round for `k = 1`.) -/
theorem observation_2_7 [Fintype V] [DecidableEq V] {D : ℕ} {c b : ℝ}
    (h : G.AdmitsPartialTreeShortcuts D c b) (hc : 0 ≤ c) :
    G.AdmitsTreeShortcuts D (c * (Nat.log 2 (Fintype.card V) + 1)) b := by
  intro T hT ι _ _ P hP
  obtain ⟨H, h1, h2, h3⟩ := observation_2_7_aux h hc T hT _ P hP rfl
  refine ⟨H, h1, fun e he => (h2 e he).trans ?_, h3⟩
  have : ((Nat.log 2 (Fintype.card ι) : ℕ) : ℝ) ≤ Nat.log 2 (Fintype.card V) := by
    exact_mod_cast Nat.log_mono_right (card_le_of_isParts hP)
  exact mul_le_mul_of_nonneg_left (by linarith) hc

end LowCongestionShortcuts
