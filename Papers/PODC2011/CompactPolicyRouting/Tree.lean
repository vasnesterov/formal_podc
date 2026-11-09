import Papers.PODC2011.CompactPolicyRouting.Paths
import Cslib.Foundations.Combinatorics.SimpleGraph.GreedySpanner

/-!
# Mapping to a tree (Lemma 4.10)

An algebra `A` *maps to a tree* if every connected weighted graph has a spanning tree whose (unique) tree paths
are all preferred paths. Lemma 4.10: monotone + selective algebras map to a tree, and conversely (the paper
assumes delimitedness for the converse; we show it is not needed).

* Sufficiency (`exists_preferred_spanningTree`, `lemma_4_10_mapsToTree`): with `⊕ = max` a minimum spanning
  tree works. Instead of formalizing Kruskal we reuse CSLib's greedy spanner with a huge stretch (which *is*
  Kruskal's algorithm), run on integer ranks of the weights: it outputs a spanning tree with the cycle property
  (every graph edge `uv` is bypassed by a tree walk of no heavier edges). Every tree path is then dominated
  edgewise by any other path between its endpoints.
* Necessity (`lemma_4_10_converse`): on the triangle, every spanning tree misses one edge, and three choices of
  edge weights (Fig. 4.1) refute non-monotone and non-selective algebras.
-/

namespace Podc.CompactPolicyRouting

open SimpleGraph RoutingAlgebra
open scoped NNReal

universe u

variable {W : Type u} [LinearOrder W]

/-- `A` maps to a tree: every connected (finite) weighted graph has a spanning tree in which, for all `s, t`,
the unique `s – t` tree path is a preferred `s – t` path of the graph. -/
def RoutingAlgebra.MapsToTree (A : RoutingAlgebra W) : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V), G.Connected → ∀ wt : Sym2 V → W,
    ∃ T : SimpleGraph V, ∃ hT : T ≤ G, T.IsTree ∧
      ∀ (s t : V) (p : T.Walk s t), p.IsPath → IsPreferred A wt (p.mapLe hT)

variable {A : RoutingAlgebra W}

/-! ### Composition as maximum -/

/-- In a monotone selective algebra, composition of extended weights is the maximum. -/
theorem mul_eq_max (hM : A.IsMonotone) (hS : A.IsSelective) (x y : A.Ext) : x * y = max x y := by
  rcases Ext.cases x with rfl | ⟨a, rfl⟩
  · rw [one_mul, max_eq_right (one_le y)]
  rcases Ext.cases y with rfl | ⟨b, rfl⟩
  · rw [mul_one, max_eq_left (one_le _)]
  · rw [emb_mul_emb, op_eq_max hM hS]
    exact Monotone.map_max (fun _ _ h => emb_le_emb.2 h)

theorem list_prod_le (hM : A.IsMonotone) (hS : A.IsSelective) {l : List A.Ext} {c : A.Ext}
    (h : ∀ x ∈ l, x ≤ c) : l.prod ≤ c := by
  induction l with
  | nil => exact one_le c
  | cons x l ih =>
    rw [List.prod_cons, mul_eq_max hM hS]
    exact max_le (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

theorem le_list_prod (hM : A.IsMonotone) {l : List A.Ext} {x : A.Ext} (hx : x ∈ l) : x ≤ l.prod := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    rw [List.prod_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hM.le_mul' _ _
    · exact (ih hx).trans (hM.le_mul _ _)

/-- With `⊕ = max`: if every edge of `p` is not heavier than some edge of `q`, then `w(p) ⪯ w(q)`. -/
theorem weight_le_of_forall_exists (hM : A.IsMonotone) (hS : A.IsSelective) {V : Type*} {wt : Sym2 V → W}
    {G H : SimpleGraph V} {s t s' t' : V} (p : G.Walk s t) (q : H.Walk s' t')
    (h : ∀ e ∈ p.edges, ∃ f ∈ q.edges, wt e ≤ wt f) : weight A wt p ≤ weight A wt q := by
  unfold weight
  refine list_prod_le hM hS fun x hx => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  obtain ⟨f, hf, hef⟩ := h e he
  exact (emb_le_emb.2 hef).trans (le_list_prod hM (List.mem_map.2 ⟨f, hf, rfl⟩))

/-! ### Minimum spanning trees with the cycle property -/

-- CSLib candidate
/-- Every finite connected graph with edge weights in a linear order has a spanning tree with the cycle
property: every edge `uv` of the graph is bypassed by a tree walk all of whose edges are not heavier than `uv`.
(A Kruskal tree; obtained from CSLib's greedy spanner with stretch `2|V| - 1` on integer ranks of the weights.) -/
theorem exists_isTree_forall_walk {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected)
    {α : Type*} [LinearOrder α] (wt : Sym2 V → α) :
    ∃ T ≤ G, T.IsTree ∧ ∀ u v, G.Adj u v → ∃ p : T.Walk u v, ∀ f ∈ p.edges, wt f ≤ wt s(u, v) := by
  classical
  have := Fintype.ofFinite V
  let S : Finset α := Finset.univ.image wt
  let r : Sym2 V → ℕ := fun e => (S.filter (· < wt e)).card
  have hr : ∀ e f, r f ≤ r e → wt f ≤ wt e := by
    intro e f hfe
    by_contra hlt
    rw [not_le] at hlt
    refine absurd hfe (not_le.2 (Finset.card_lt_card ?_))
    refine (Finset.ssubset_iff_of_subset ?_).2 ⟨wt e, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans hlt⟩
    · simp [S, hlt]
    · simp
  let w : Sym2 V → ℝ≥0 := fun e => (r e : ℝ≥0)
  set n := Fintype.card V
  have hn : 1 ≤ n := Fintype.card_pos_iff.2 hG.nonempty
  obtain ⟨H, hH⟩ := exists_isGreedySpanner G w ((2 * n - 1 : ℕ) : ℝ≥0)
  have hsp := hH.isWSpanner (Nat.one_le_cast.2 (by omega))
  obtain ⟨hHG, hwalk⟩ := hH.forall_walk
  have hcyc := hH.noShortCycles (k := n) le_rfl
  refine ⟨H, hHG, ⟨?_, ?_⟩, ?_⟩
  · have := hG.nonempty
    exact Connected.mk fun u v => hsp.reachable (hG.preconnected u v)
  · intro v c hc
    have hlen := hcyc v c hc
    cases c with
    | nil => exact hc.ne_nil rfl
    | cons h p =>
      have hp := ((Walk.cons_isCycle_iff p h).1 hc).1
      have := hp.length_lt
      simp only [Walk.length_cons] at hlen
      omega
  · intro u v huv
    by_cases hH' : H.Adj u v
    · exact ⟨Walk.cons hH' Walk.nil, by simp⟩
    · obtain ⟨p, hp⟩ := hwalk u v huv hH'
      exact ⟨p, fun f hf => hr _ _ (Nat.cast_le.1 (hp f hf))⟩

/-! ### Sufficiency -/

/-- Lemma 4.10 (sufficiency), graph-level form: for a monotone selective algebra, every finite connected
weighted graph has a spanning tree all of whose tree paths are preferred paths. -/
theorem exists_preferred_spanningTree (hM : A.IsMonotone) (hS : A.IsSelective) {V : Type*} [Finite V]
    {G : SimpleGraph V} (hG : G.Connected) (wt : Sym2 V → W) :
    ∃ T : SimpleGraph V, ∃ hT : T ≤ G, T.IsTree ∧
      ∀ (s t : V) (p : T.Walk s t), p.IsPath → IsPreferred A wt (p.mapLe hT) := by
  classical
  obtain ⟨T, hTG, hT, hcyc⟩ := exists_isTree_forall_walk hG wt
  refine ⟨T, hTG, hT, fun s t p hp => ⟨hp.mapLe hTG, fun q _ => ?_⟩⟩
  rw [weight_mapLe]
  have key : ∀ {x y : V} (q : G.Walk x y),
      ∃ r : T.Walk x y, ∀ e ∈ r.edges, ∃ f ∈ q.edges, wt e ≤ wt f := by
    intro x y q
    induction q with
    | nil => exact ⟨Walk.nil, by simp⟩
    | cons h q ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨r₀, hr₀⟩ := hcyc _ _ h
      refine ⟨r₀.append r, fun e he => ?_⟩
      rw [Walk.edges_append, List.mem_append] at he
      rcases he with he | he
      · exact ⟨_, by simp, hr₀ e he⟩
      · obtain ⟨f, hf, hef⟩ := hr e he
        exact ⟨f, by simp [hf], hef⟩
  obtain ⟨r, hr⟩ := key q
  have hpr : p = r.bypass :=
    congrArg Subtype.val ((hT.isAcyclic.subsingleton_path s t).elim ⟨p, hp⟩ ⟨r.bypass, r.bypass_isPath⟩)
  subst hpr
  exact weight_le_of_forall_exists hM hS _ q fun e he => hr e (r.edges_bypass_subset_edges he)

/-- Lemma 4.10 (sufficiency) of [paper]. If `A` is monotone and selective, then `A` maps to a tree. -/
theorem lemma_4_10_mapsToTree (hM : A.IsMonotone) (hS : A.IsSelective) : A.MapsToTree :=
  fun _ _ _ hG wt => exists_preferred_spanningTree hM hS hG wt

/-! ### Necessity: the triangle -/

/-- Triangle weights on `Fin 3`: edge `01 ↦ x`, `12 ↦ y`, `02 ↦ z`. -/
def triWt (x y z : W) (e : Sym2 (Fin 3)) : W :=
  if e = s(0, 1) then x else if e = s(1, 2) then y else z

/-- If `A` maps to a tree, the triangle with weights `01 ↦ x`, `12 ↦ y`, `02 ↦ z` has a spanning tree missing
one edge whose tree paths are preferred; each choice of the missing edge yields two inequalities. -/
theorem triangle_cases (h : A.MapsToTree) (x y z : W) :
    (A.op x y ≤ z ∧ x ≤ A.op z y) ∨ (A.op y z ≤ x ∧ z ≤ A.op x y) ∨
      (A.op x z ≤ y ∧ z ≤ A.op x y) := by
  obtain ⟨T, hT, hTt, hP⟩ := h (Fin 3) ⊤ connected_top (triWt x y z)
  have key : ∀ {s t : Fin 3} (p : T.Walk s t) (q : (⊤ : SimpleGraph (Fin 3)).Walk s t),
      p.IsPath → q.IsPath → weight A (triWt x y z) p ≤ weight A (triWt x y z) q := by
    intro s t p q hp hq
    have := (hP _ _ p hp).2 q hq
    rwa [weight_mapLe] at this
  have iso : ∀ u w : Fin 3, u ≠ w → (∀ v, ¬ T.Adj u v) → False := by
    intro u w huw hu
    obtain ⟨c⟩ := hTt.connected.preconnected u w
    cases c with
    | nil => exact huw rfl
    | cons h _ => exact hu _ h
  have a : ∀ i j : Fin 3, i ≠ j → (⊤ : SimpleGraph (Fin 3)).Adj i j := fun i j h => h
  by_cases h01 : T.Adj 0 1 <;> by_cases h12 : T.Adj 1 2 <;> by_cases h02 : T.Adj 0 2
  · exfalso
    exact hTt.isAcyclic (Walk.cons h01 (Walk.cons h12 (Walk.cons h02.symm Walk.nil)))
      (by simp [Walk.cons_isCycle_iff])
  · left
    constructor
    · have := key (Walk.cons h01 (Walk.cons h12 Walk.nil)) (Walk.cons (a 0 2 (by decide)) Walk.nil)
        (by simp) (by simp)
      simpa [triWt, Sym2.eq_iff] using this
    · have := key (Walk.cons h01 Walk.nil)
        (Walk.cons (a 0 2 (by decide)) (Walk.cons (a 2 1 (by decide)) Walk.nil)) (by simp) (by simp)
      simpa [triWt, Sym2.eq_iff] using this
  · right; right
    constructor
    · have := key (Walk.cons h01.symm (Walk.cons h02 Walk.nil)) (Walk.cons (a 1 2 (by decide)) Walk.nil)
        (by simp) (by simp)
      simpa [triWt, Sym2.eq_iff] using this
    · have := key (Walk.cons h02 Walk.nil)
        (Walk.cons (a 0 1 (by decide)) (Walk.cons (a 1 2 (by decide)) Walk.nil)) (by simp) (by simp)
      simpa [triWt, Sym2.eq_iff] using this
  · exfalso
    exact iso 2 0 (by decide) fun v hv => by
      fin_cases v
      · exact h02 hv.symm
      · exact h12 hv.symm
      · exact hv.ne rfl
  · right; left
    constructor
    · have := key (Walk.cons h12 (Walk.cons h02.symm Walk.nil))
        (Walk.cons (a 1 0 (by decide)) Walk.nil) (by simp) (by simp)
      simpa [triWt, Sym2.eq_iff] using this
    · have := key (Walk.cons h02 Walk.nil)
        (Walk.cons (a 0 1 (by decide)) (Walk.cons (a 1 2 (by decide)) Walk.nil)) (by simp) (by simp)
      simpa [triWt, Sym2.eq_iff] using this
  · exfalso
    exact iso 0 1 (by decide) fun v hv => by
      fin_cases v
      · exact hv.ne rfl
      · exact h01 hv
      · exact h02 hv
  · exfalso
    exact iso 1 0 (by decide) fun v hv => by
      fin_cases v
      · exact h01 hv.symm
      · exact hv.ne rfl
      · exact h12 hv
  · exfalso
    exact iso 0 1 (by decide) fun v hv => by
      fin_cases v
      · exact hv.ne rfl
      · exact h01 hv
      · exact h02 hv

/-- Lemma 4.10 (necessity of monotonicity). If `w₂ ⊕ w₁ ≺ w₁` for some `w₁, w₂`, then `A` does not map to a
tree (triangle with weights `w₁, w₂, w₁`). -/
theorem not_mapsToTree_of_not_monotone {a b : W} (h : A.op b a < a) : ¬ A.MapsToTree := fun hT => by
  rw [A.op_comm] at h
  rcases triangle_cases hT a b a with ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩ <;> exact absurd h1 (not_le.2 h)

/-- Lemma 4.10, Fig. 4.1(a): a violation `w ≺ w ⊕ w` of auto-selectivity prevents mapping to a tree
(triangle with all weights `w`). -/
theorem not_mapsToTree_of_lt_op_self {a : W} (h : a < A.op a a) : ¬ A.MapsToTree := fun hT => by
  rcases triangle_cases hT a a a with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact absurd h1 (not_le.2 h)

/-- Lemma 4.10, Fig. 4.1(b): if `w₁ ≺ w₂ ≺ w₁ ⊕ w₂`, then `A` does not map to a tree (triangle with weights
`w₁, w₂, w₂`). -/
theorem not_mapsToTree_of_lt_op {a b : W} (hab : a < b) (h : b < A.op a b) : ¬ A.MapsToTree :=
  fun hT => by
  rcases triangle_cases hT a b b with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd h1 (not_le.2 h)
  · exact not_mapsToTree_of_not_monotone (lt_of_le_of_lt h1 hab) hT
  · exact absurd h1 (not_le.2 h)

/-- Lemma 4.10 (necessity), without the delimitedness assumption of the paper: an algebra that maps to a tree
is monotone and selective. -/
theorem lemma_4_10_converse (h : A.MapsToTree) : A.IsMonotone ∧ A.IsSelective := by
  have hM : A.IsMonotone := fun a b => by
    by_contra hc
    exact not_mapsToTree_of_not_monotone (not_le.1 hc) h
  refine ⟨hM, fun a b => ?_⟩
  by_contra hc
  push Not at hc
  rcases lt_trichotomy a b with hab | rfl | hab
  · refine not_mapsToTree_of_lt_op hab (lt_of_le_of_ne ?_ (Ne.symm hc.2)) h
    exact hM b a
  · exact not_mapsToTree_of_lt_op_self (lt_of_le_of_ne (hM a a) (Ne.symm hc.1)) h
  · refine not_mapsToTree_of_lt_op hab (lt_of_le_of_ne (hM a b) ?_) h
    rw [A.op_comm]; exact Ne.symm hc.1

/-- Lemma 4.10 (necessity) of [paper], as stated: if `A` is delimited and maps to a tree, then `A` is monotone
and selective. (Delimitedness is not needed, see `lemma_4_10_converse`.) -/
theorem lemma_4_10_converse' (_hD : A.IsDelimited) (h : A.MapsToTree) : A.IsMonotone ∧ A.IsSelective :=
  lemma_4_10_converse h

/-- Lemma 4.10 as an equivalence: `A` maps to a tree iff it is monotone and selective. -/
theorem mapsToTree_iff : A.MapsToTree ↔ A.IsMonotone ∧ A.IsSelective :=
  ⟨lemma_4_10_converse, fun h => lemma_4_10_mapsToTree h.1 h.2⟩

end Podc.CompactPolicyRouting
