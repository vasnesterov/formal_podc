import Podc.Foundations.Combinatorics.SimpleGraph.EdgeColoring.Basic

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/EdgeColoring/Vizing.lean

/-!
# Vizing's and Fournier's theorems

We prove **Fournier's theorem** (1973): if a finite simple graph has maximum degree at most `k`
and the vertices of degree `k` form an independent set, then its edges can be properly coloured
with `k` colours. As a corollary we get **Vizing's theorem**: every finite simple graph has a
proper edge colouring with `Δ + 1` colours.

The proof is the classical one via Vizing fans and Kempe chains: remove an edge `xy` where every
neighbour of `x` has degree `< k`, colour the rest by induction, build a maximal fan at `x`
starting at `y`, and either rotate the fan or swap an `αβ`-Kempe chain to free a colour.

## Main definitions

* `SimpleGraph.kempeGraph H c α β`: the subgraph of `H` of edges coloured `α` or `β`.
* `SimpleGraph.kempeSwap c K α β`: swap the colours `α` and `β` on the edges meeting `K`.

## Main results

* `SimpleGraph.not_reachable_of_ncard_neighborSet_le_two`: in a graph of maximum degree `≤ 2`,
  three distinct vertices of degree `≤ 1` are not in one connected component.
* `SimpleGraph.IsProperEdgeColoring.kempeSwap`: Kempe swaps preserve proper edge colourings.
* `SimpleGraph.exists_isProperEdgeColoring_of_ncard_le`: Fournier's theorem.
* `SimpleGraph.exists_isProperEdgeColoring_maxDegree_add_one`: Vizing's theorem.
* `SimpleGraph.exists_isProperEdgeColoring_maxDegree`: Fournier's theorem with `maxDegree`.
* `SimpleGraph.IsProperEdgeColoring.lineGraph_colorable`,
  `SimpleGraph.lineGraph_colorable_of_ncard_le`: the statements for vertex colourings of the
  line graph.
-/

namespace SimpleGraph

variable {V : Type*}

/-! ### Components of graphs of maximum degree two -/

open Finset in
/-- In a graph of maximum degree at most `2`, three distinct vertices of degree at most `1` cannot
lie in one connected component (a connected graph on `n` vertices has `≥ n - 1` edges, while the
degree sum would be `≤ 2n - 3`). -/
lemma not_reachable_of_ncard_neighborSet_le_two [Finite V] (F : SimpleGraph V)
    (h2 : ∀ v, (F.neighborSet v).ncard ≤ 2) {x a b : V} (hxa : x ≠ a) (hxb : x ≠ b)
    (hab : a ≠ b) (hx : (F.neighborSet x).ncard ≤ 1) (ha : (F.neighborSet a).ncard ≤ 1)
    (hb : (F.neighborSet b).ncard ≤ 1) (ra : F.Reachable x a) :
    ¬ F.Reachable x b := by
  intro rb
  classical
  set C := F.connectedComponentMk x
  have hxC : x ∈ C := rfl
  have haC : a ∈ C := (ConnectedComponent.eq.mpr ra).symm
  have hbC : b ∈ C := (ConnectedComponent.eq.mpr rb).symm
  have hconn := C.connected_toSimpleGraph
  have hcard := hconn.card_vert_le_card_edgeSet_add_one
  have := Fintype.ofFinite C
  have hdeg : ∀ v : C, C.toSimpleGraph.degree v ≤ (F.neighborSet v).ncard := by
    intro v
    rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective (fun w => (⟨w.1.1, w.2⟩ : F.neighborSet v))
      (fun w w' h => by
        have h' : w.1.1 = w'.1.1 := congrArg (fun z : F.neighborSet v => z.1) h
        exact Subtype.ext (Subtype.ext h'))
  have hsum := C.toSimpleGraph.sum_degrees_eq_twice_card_edges
  rw [edgeFinset_card, ← Nat.card_eq_fintype_card] at hsum
  set S : Finset C := {⟨x, hxC⟩, ⟨a, haC⟩, ⟨b, hbC⟩}
  have hS : #S = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨_, _, _, by simpa using hxa, by simpa using hxb, by simpa using hab, rfl⟩
  have hle : ∀ v : C, C.toSimpleGraph.degree v + (if v ∈ S then 1 else 0) ≤ 2 := by
    intro v
    have := (hdeg v).trans (h2 v)
    split_ifs with hv
    · simp only [S, mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · have : C.toSimpleGraph.degree ⟨x, hxC⟩ ≤ 1 := (hdeg _).trans hx
        omega
      · have : C.toSimpleGraph.degree ⟨a, haC⟩ ≤ 1 := (hdeg _).trans ha
        omega
      · have : C.toSimpleGraph.degree ⟨b, hbC⟩ ≤ 1 := (hdeg _).trans hb
        omega
    · omega
  have hsum2 := Finset.sum_le_sum (s := univ) (fun v _ => hle v)
  rw [Finset.sum_add_distrib, Finset.sum_boole, hsum] at hsum2
  simp only [Finset.filter_mem_eq_inter, univ_inter, Nat.cast_id, sum_const, card_univ,
    smul_eq_mul, hS] at hsum2
  rw [Nat.card_eq_fintype_card] at hcard
  omega

/-- If a predicate `P` is closed under `F`-adjacency, it is closed under `F`-reachability. -/
lemma Reachable.of_closed {F : SimpleGraph V} {P : V → Prop}
    (hP : ∀ ⦃u v⦄, P u → F.Adj u v → P v) {u w : V} (h : F.Reachable u w) (hu : P u) : P w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons h _ ih => exact ih (hP hu h)

/-! ### Kempe chains -/

variable {G H : SimpleGraph V} {c : Sym2 V → ℕ} {k : ℕ}

/-- The subgraph of `H` formed by the edges of colour `α` or `β` under `c`. -/
def kempeGraph (H : SimpleGraph V) (c : Sym2 V → ℕ) (α β : ℕ) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ (c s(u, v) = α ∨ c s(u, v) = β)
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => H.irrefl h.1⟩

lemma kempeGraph_adj {α β : ℕ} {u v : V} :
    (H.kempeGraph c α β).Adj u v ↔ H.Adj u v ∧ (c s(u, v) = α ∨ c s(u, v) = β) := Iff.rfl

/-- If all edges at `v` have colours in a finite set `S`, then `v` has at most `|S|` neighbours. -/
lemma ncard_neighborSet_le_of_forall_mem [Finite V] (hc : H.IsEdgeColoring c) {v : V}
    {S : Set ℕ} (hS : S.Finite) (h : ∀ w, H.Adj v w → c s(v, w) ∈ S) :
    (H.neighborSet v).ncard ≤ S.ncard :=
  Set.ncard_le_ncard_of_injOn (fun w => c s(v, w)) (fun w hw => h w hw)
    (fun _ hw _ hw' he => hc hw hw' he) hS

lemma ncard_neighborSet_kempeGraph_le_two [Finite V] (hc : H.IsEdgeColoring c) (α β : ℕ)
    (v : V) : ((H.kempeGraph c α β).neighborSet v).ncard ≤ 2 := by
  have hc' : (H.kempeGraph c α β).IsEdgeColoring c := hc.mono fun _ _ h => h.1
  calc _ ≤ ({α, β} : Set ℕ).ncard :=
        ncard_neighborSet_le_of_forall_mem hc' (Set.toFinite _) fun w hw => hw.2
    _ ≤ ({β} : Set ℕ).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by simp

lemma ncard_neighborSet_kempeGraph_le_one_left [Finite V] (hc : H.IsEdgeColoring c) {α β : ℕ}
    {v : V} (hv : H.EdgeColorMissing c v α) :
    ((H.kempeGraph c α β).neighborSet v).ncard ≤ 1 := by
  have hc' : (H.kempeGraph c α β).IsEdgeColoring c := hc.mono fun _ _ h => h.1
  calc _ ≤ ({β} : Set ℕ).ncard :=
        ncard_neighborSet_le_of_forall_mem hc' (Set.toFinite _) fun w hw =>
          hw.2.resolve_left (hv hw.1)
    _ = 1 := by simp

lemma ncard_neighborSet_kempeGraph_le_one_right [Finite V] (hc : H.IsEdgeColoring c) {α β : ℕ}
    {v : V} (hv : H.EdgeColorMissing c v β) :
    ((H.kempeGraph c α β).neighborSet v).ncard ≤ 1 := by
  have hc' : (H.kempeGraph c α β).IsEdgeColoring c := hc.mono fun _ _ h => h.1
  calc _ ≤ ({α} : Set ℕ).ncard :=
        ncard_neighborSet_le_of_forall_mem hc' (Set.toFinite _) fun w hw =>
          hw.2.resolve_right (hv hw.1)
    _ = 1 := by simp

open Classical in
/-- Swap the colours `α` and `β` on all edges with an endpoint in `K`. -/
noncomputable def kempeSwap (c : Sym2 V → ℕ) (K : Set V) (α β : ℕ) : Sym2 V → ℕ :=
  fun e => if ∃ v ∈ K, v ∈ e then Equiv.swap α β (c e) else c e

section KempeSwap

variable {K : Set V} {α β : ℕ}

lemma kempeSwap_of_mem {u : V} (hu : u ∈ K) (v : V) :
    kempeSwap c K α β s(u, v) = Equiv.swap α β (c s(u, v)) := by
  have h : ∃ w ∈ K, w ∈ s(u, v) := ⟨u, hu, Sym2.mem_mk_left u v⟩
  simp only [kempeSwap, h, ↓reduceIte]

lemma kempeSwap_of_notMem (hK : ∀ ⦃u v⦄, u ∈ K → (H.kempeGraph c α β).Adj u v → v ∈ K)
    {u v : V} (huv : H.Adj u v) (hu : u ∉ K) : kempeSwap c K α β s(u, v) = c s(u, v) := by
  unfold kempeSwap
  split_ifs with h
  · obtain ⟨w, hw, hwe⟩ := h
    rcases Sym2.mem_iff.mp hwe with rfl | rfl
    · exact absurd hw hu
    · have hα : c s(u, w) ≠ α := fun h' =>
        hu (hK hw ⟨huv.symm, by rw [Sym2.eq_swap]; exact Or.inl h'⟩)
      have hβ : c s(u, w) ≠ β := fun h' =>
        hu (hK hw ⟨huv.symm, by rw [Sym2.eq_swap]; exact Or.inr h'⟩)
      exact Equiv.swap_apply_of_ne_of_ne hα hβ
  · rfl

/-- A **Kempe swap** on a set `K` closed under `αβ`-edges preserves proper edge colourings. -/
lemma IsProperEdgeColoring.kempeSwap (hc : H.IsProperEdgeColoring c k) (hα : α < k)
    (hβ : β < k) (hK : ∀ ⦃u v⦄, u ∈ K → (H.kempeGraph c α β).Adj u v → v ∈ K) :
    H.IsProperEdgeColoring (kempeSwap c K α β) k := by
  constructor
  · intro u v huv
    by_cases hu : u ∈ K
    · rw [kempeSwap_of_mem hu, Equiv.swap_apply_def]
      split_ifs
      · exact hβ
      · exact hα
      · exact hc.1 huv
    · rw [kempeSwap_of_notMem hK huv hu]
      exact hc.1 huv
  · intro u v w huv huw he
    by_cases hu : u ∈ K
    · rw [kempeSwap_of_mem hu, kempeSwap_of_mem hu] at he
      exact hc.2 huv huw ((Equiv.swap α β).injective he)
    · rw [kempeSwap_of_notMem hK huv hu, kempeSwap_of_notMem hK huw hu] at he
      exact hc.2 huv huw he

/-- Outside `K`, a Kempe swap does not change the colours at a vertex. -/
lemma EdgeColorMissing.kempeSwap_of_notMem
    (hK : ∀ ⦃u v⦄, u ∈ K → (H.kempeGraph c α β).Adj u v → v ∈ K) {v : V} (hv : v ∉ K) {γ : ℕ}
    (h : H.EdgeColorMissing c v γ) : H.EdgeColorMissing (kempeSwap c K α β) v γ :=
  fun _ hw => by rw [SimpleGraph.kempeSwap_of_notMem hK hw hv]; exact h hw

/-- Inside `K`, a Kempe swap applies the transposition `(α β)` to the colours at a vertex. -/
lemma EdgeColorMissing.kempeSwap_of_mem {v : V} (hv : v ∈ K) {γ : ℕ}
    (h : H.EdgeColorMissing c v (Equiv.swap α β γ)) :
    H.EdgeColorMissing (kempeSwap c K α β) v γ :=
  fun _ hw he => h hw (by
    rw [SimpleGraph.kempeSwap_of_mem hv] at he; rw [← he, Equiv.swap_apply_self])

end KempeSwap

/-- Colouring an uncoloured edge `uv` with a colour `α < k` missing at both ends extends a proper
`k`-edge-colouring. -/
lemma IsProperEdgeColoring.insertEdge {u v : V} {α : ℕ}
    (hc : (G.deleteEdges {s(u, v)}).IsProperEdgeColoring c k) (hα : α < k)
    (hu : (G.deleteEdges {s(u, v)}).EdgeColorMissing c u α)
    (hv : (G.deleteEdges {s(u, v)}).EdgeColorMissing c v α) :
    G.IsProperEdgeColoring (recolorEdge c s(u, v) α) k := by
  refine ⟨fun a b hab => ?_, hc.2.insertEdge hu hv⟩
  by_cases hb : s(a, b) = s(u, v)
  · rw [hb, recolorEdge_self]; exact hα
  · rw [recolorEdge_of_ne _ _ hb]; exact hc.1 (by simp [hab, hb])

/-! ### Vizing fans -/

namespace Vizing

variable {x y : V} {m : V → ℕ} {f : ℕ → V} {n : ℕ}

/-- `f 0 = y, f 1, …, f n` is a **Vizing fan** at `x` of length `n`, for the colouring `c` of
`G - xy` and the choice `m z` of a missing colour at each neighbour `z` of `x`: each edge
`x (f (l + 1))` is coloured `m (f l)`, and the `f l` are distinct. -/
structure IsFan (G : SimpleGraph V) (c : Sym2 V → ℕ) (x y : V) (m : V → ℕ) (f : ℕ → V)
    (n : ℕ) : Prop where
  zero : f 0 = y
  adj : ∀ l < n, (G.deleteEdges {s(x, y)}).Adj x (f (l + 1))
  color : ∀ l < n, c s(x, f (l + 1)) = m (f l)
  inj : ∀ i ≤ n, ∀ j ≤ n, f i = f j → i = j

lemma IsFan.gadj (hxy : G.Adj x y) (hf : IsFan G c x y m f n) : ∀ l ≤ n, G.Adj x (f l)
  | 0, _ => hf.zero ▸ hxy
  | l + 1, hl => deleteEdges_le _ (hf.adj l hl)

lemma IsFan.ne (hxy : G.Adj x y) (hf : IsFan G c x y m f n) {l : ℕ} (hl : l ≤ n) : f l ≠ x :=
  (hf.gadj hxy l hl).ne'

/-- A fan that cannot be extended: either its last missing colour is missing at `x`, or it is
the missing colour of an earlier fan vertex. -/
lemma exists_fan [Finite V] (G : SimpleGraph V) (c : Sym2 V → ℕ) (x y : V) (m : V → ℕ) :
    ∃ f n, IsFan G c x y m f n ∧ ((G.deleteEdges {s(x, y)}).EdgeColorMissing c x (m (f n)) ∨
      ∃ i < n, m (f i) = m (f n)) := by
  by_contra hcon
  push Not at hcon
  have hnot : ¬ (G.deleteEdges {s(x, y)}).Adj x y := by simp
  have key : ∀ n, ∃ f, IsFan G c x y m f n := by
    intro n
    induction n with
    | zero =>
      exact ⟨fun _ => y, rfl, fun l hl => absurd hl (Nat.not_lt_zero _),
        fun l hl => absurd hl (Nat.not_lt_zero _), fun i hi j hj _ => by omega⟩
    | succ n ih =>
      obtain ⟨f, hf⟩ := ih
      obtain ⟨hmiss, hdist⟩ := hcon f n hf
      simp only [EdgeColorMissing, not_forall, not_not] at hmiss
      obtain ⟨w, hw, hwc⟩ := hmiss
      have hwf : ∀ j ≤ n, w ≠ f j := by
        intro j hj hwj
        rcases j with _ | j
        · exact hnot (by rw [hwj, hf.zero] at hw; exact hw)
        · exact hdist j (by omega) (by rw [← hf.color j (by omega), ← hwj, hwc])
      refine ⟨fun l => if l = n + 1 then w else f l, by simp [hf.zero], fun l hl => ?_,
        fun l hl => ?_, fun i hi j hj hij => ?_⟩
      · by_cases h : l = n
        · subst h; simpa using hw
        · simpa [h] using hf.adj l (by omega)
      · by_cases h : l = n
        · subst h; simpa using hwc
        · simpa [h, show l ≠ n + 1 by omega] using hf.color l (by omega)
      · split_ifs at hij with h1 h2 h2
        · omega
        · exact absurd hij (hwf j (by omega))
        · exact absurd hij.symm (hwf i (by omega))
        · exact hf.inj i (by omega) j (by omega) hij
  obtain ⟨f, hf⟩ := key (Nat.card V)
  have := Nat.card_le_card_of_injective (fun i : Fin (Nat.card V + 1) => f i)
    (fun i j h => Fin.ext (hf.inj i (by omega) j (by omega) h))
  simp at this

/-- Rotating the fan up to `t`: the edges `x (f l)`, `l < t`, get the colours `m (f l)`. -/
noncomputable def rotate (c : Sym2 V → ℕ) (x : V) (m : V → ℕ) (f : ℕ → V) : ℕ → Sym2 V → ℕ
  | 0 => c
  | t + 1 => recolorEdge (rotate c x m f t) s(x, f t) (m (f t))

lemma rotate_of_ne (e : Sym2 V) : ∀ t, (∀ l < t, e ≠ s(x, f l)) → rotate c x m f t e = c e
  | 0, _ => rfl
  | t + 1, h => by
      rw [rotate, recolorEdge_of_ne _ _ (h t t.lt_succ_self)]
      exact rotate_of_ne e t fun l hl => h l (by omega)

lemma IsFan.rotate_fan (hf : IsFan G c x y m f n) :
    ∀ t ≤ n, ∀ l < t, rotate c x m f t s(x, f l) = m (f l)
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero _)
  | t + 1, ht, l, hl => by
      rw [rotate]
      by_cases h : l = t
      · subst h; exact recolorEdge_self _ _ _
      · rw [recolorEdge_of_ne _ _ fun he =>
          h (hf.inj l (by omega) t (by omega) (Sym2.congr_right.mp he))]
        exact hf.rotate_fan t (by omega) l (by omega)

/-- The edges of `G - x (f t)` are the rotated edges and edges of `G - xy` with unchanged
colour. -/
lemma IsFan.rotate_edge (hf : IsFan G c x y m f n) {t : ℕ} {u v : V}
    (huv : (G.deleteEdges {s(x, f t)}).Adj u v) :
    (∃ l < t, s(u, v) = s(x, f l)) ∨ ((∀ l < t, s(u, v) ≠ s(x, f l)) ∧
      (G.deleteEdges {s(x, y)}).Adj u v ∧ rotate c x m f t s(u, v) = c s(u, v)) := by
  by_cases h : ∃ l < t, s(u, v) = s(x, f l)
  · exact Or.inl h
  · push Not at h
    refine Or.inr ⟨h, ?_, rotate_of_ne _ t h⟩
    rw [deleteEdges_adj] at huv ⊢
    refine ⟨huv.1, ?_⟩
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · rw [hf.zero] at huv; exact huv.2
    · rw [Set.mem_singleton_iff, ← hf.zero]; exact h 0 ht0

section Rotation

variable (hxy : G.Adj x y) (hc : (G.deleteEdges {s(x, y)}).IsProperEdgeColoring c k)
  (hm : ∀ z, G.Adj x z → m z < k ∧ (G.deleteEdges {s(x, y)}).EdgeColorMissing c z (m z))
  (hf : IsFan G c x y m f n)
include hxy hc hm hf

/-- The rotated colouring is a proper `k`-edge-colouring of `G - x (f t)`. -/
lemma rotate_proper {t : ℕ} (ht : t ≤ n) :
    (G.deleteEdges {s(x, f t)}).IsProperEdgeColoring (rotate c x m f t) k := by
  have hgadj := hf.gadj hxy
  have hrot := hf.rotate_fan
  refine ⟨fun u v huv => ?_, ?_⟩
  · rcases hf.rotate_edge huv with ⟨l, hl, he⟩ | ⟨-, hH, hce⟩
    · rw [he, hrot t ht l hl]; exact (hm _ (hgadj l (by omega))).1
    · rw [hce]; exact hc.1 hH
  have key : ∀ ⦃u v w : V⦄, (G.deleteEdges {s(x, f t)}).Adj u v →
      (G.deleteEdges {s(x, f t)}).Adj u w →
      rotate c x m f t s(u, v) = rotate c x m f t s(u, w) →
      (∃ l < t, s(u, v) = s(x, f l)) → v = w := by
    intro u v w huv huw he ⟨l, hl, hel⟩
    rw [hel, hrot t ht l hl] at he
    rcases Sym2.eq_iff.mp hel with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · subst hu hv
      rcases hf.rotate_edge huw with ⟨l', hl', hel'⟩ | ⟨hnr, hH, hce⟩
      · rw [hel', hrot t ht l' hl'] at he
        rcases Sym2.eq_iff.mp hel' with ⟨-, hw⟩ | ⟨hx, -⟩
        · subst hw
          rw [← hf.color l (by omega), ← hf.color l' (by omega)] at he
          have h1 := hf.inj _ (by omega) _ (by omega) (hc.2 (hf.adj l (by omega))
            (hf.adj l' (by omega)) he)
          rw [show l = l' by omega]
        · exact absurd hx.symm (hf.ne hxy (by omega))
      · rw [hce, ← hf.color l (by omega)] at he
        have hw := hc.2 (hf.adj l (by omega)) hH he
        subst hw
        by_cases hlt : l + 1 < t
        · exact absurd rfl (hnr (l + 1) hlt)
        · rw [show l + 1 = t by omega] at huw
          simp at huw
    · subst hu hv
      rcases hf.rotate_edge huw with ⟨l', hl', hel'⟩ | ⟨-, hH, hce⟩
      · rcases Sym2.eq_iff.mp hel' with ⟨hx, -⟩ | ⟨-, hw⟩
        · exact absurd hx (hf.ne hxy (by omega))
        · exact hw.symm
      · rw [hce] at he
        exact absurd he.symm ((hm _ (hgadj l (by omega))).2 hH)
  intro u v w huv huw he
  by_cases h1 : ∃ l < t, s(u, v) = s(x, f l)
  · exact key huv huw he h1
  by_cases h2 : ∃ l < t, s(u, w) = s(x, f l)
  · exact (key huw huv he.symm h2).symm
  rcases hf.rotate_edge huv with h | ⟨-, hH1, hc1⟩
  · exact absurd h h1
  rcases hf.rotate_edge huw with h | ⟨-, hH2, hc2⟩
  · exact absurd h h2
  rw [hc1, hc2] at he
  exact hc.2 hH1 hH2 he

omit hxy hc hm in
/-- Rotation does not create new colours at `x`. -/
lemma rotate_missing_x {t : ℕ} (ht : t ≤ n) {γ : ℕ}
    (hγ : (G.deleteEdges {s(x, y)}).EdgeColorMissing c x γ) :
    (G.deleteEdges {s(x, f t)}).EdgeColorMissing (rotate c x m f t) x γ := by
  intro w hw he
  rcases hf.rotate_edge hw with ⟨l, hl, hel⟩ | ⟨-, hH, hce⟩
  · rw [hel, hf.rotate_fan t ht l hl, ← hf.color l (by omega)] at he
    exact hγ (hf.adj l (by omega)) he
  · rw [hce] at he; exact hγ hH he

omit hc in
/-- After rotating up to `t`, the vertex `f t` misses `m (f t)`. -/
lemma rotate_missing_last {t : ℕ} (ht : t ≤ n) :
    (G.deleteEdges {s(x, f t)}).EdgeColorMissing (rotate c x m f t) (f t) (m (f t)) := by
  intro w hw he
  rcases hf.rotate_edge hw with ⟨l, hl, hel⟩ | ⟨-, hH, hce⟩
  · rcases Sym2.eq_iff.mp hel with ⟨h, -⟩ | ⟨h, -⟩
    · exact hf.ne hxy ht h
    · exact absurd (hf.inj t ht l (by omega) h) (by omega)
  · rw [hce] at he; exact (hm _ (hf.gadj hxy t ht)).2 hH he

/-- The fan ends with a colour missing at `x`: rotate and colour the last edge. -/
lemma fan_success (hmiss : (G.deleteEdges {s(x, y)}).EdgeColorMissing c x (m (f n))) :
    ∃ c', G.IsProperEdgeColoring c' k :=
  ⟨_, (rotate_proper hxy hc hm hf le_rfl).insertEdge (hm _ (hf.gadj hxy n le_rfl)).1
    (rotate_missing_x hf le_rfl hmiss) (rotate_missing_last hxy hm hf le_rfl)⟩

/-- The fan ends with a repeated colour `β = m (f i) = m (f n)`: use an `αβ`-Kempe chain. -/
lemma fan_kempe [Finite V] {α : ℕ} (hα : α < k)
    (hαx : (G.deleteEdges {s(x, y)}).EdgeColorMissing c x α)
    {i : ℕ} (hi : i < n)
    (hβ : m (f i) = m (f n)) : ∃ c', G.IsProperEdgeColoring c' k := by
  classical
  set β := m (f n) with hβdef
  have hβk : β < k := (hm _ (hf.gadj hxy n le_rfl)).1
  set F := (G.deleteEdges {s(x, y)}).kempeGraph c α β
  have hdist : ¬ (F.Reachable x (f i) ∧ F.Reachable x (f n)) := by
    rintro ⟨r1, r2⟩
    refine not_reachable_of_ncard_neighborSet_le_two F
      (ncard_neighborSet_kempeGraph_le_two hc.2 α β) (hf.ne hxy hi.le).symm
      (hf.ne hxy le_rfl).symm (fun h => ?_) (ncard_neighborSet_kempeGraph_le_one_left hc.2 hαx)
      (ncard_neighborSet_kempeGraph_le_one_right hc.2 (hβ ▸ (hm _ (hf.gadj hxy i hi.le)).2))
      (ncard_neighborSet_kempeGraph_le_one_right hc.2 (hm _ (hf.gadj hxy n le_rfl)).2) r1 r2
    have := hf.inj i hi.le n le_rfl h
    omega
  obtain ⟨t, htn, hft, hmt, hit⟩ : ∃ t ≤ n, ¬ F.Reachable x (f t) ∧ m (f t) = β ∧
      (i < t → F.Reachable x (f i)) := by
    by_cases h : F.Reachable x (f i)
    · exact ⟨n, le_rfl, fun h' => hdist ⟨h, h'⟩, rfl, fun _ => h⟩
    · exact ⟨i, hi.le, h, hβ, fun h' => absurd h' (lt_irrefl _)⟩
  have hψ := rotate_proper hxy hc hm hf htn
  set F' := (G.deleteEdges {s(x, f t)}).kempeGraph (rotate c x m f t) α β
  have hclosed : ∀ ⦃u v⦄, F.Reachable x u → F'.Adj u v → F.Reachable x v := by
    intro u v hu huv
    rcases hf.rotate_edge huv.1 with ⟨l, hl, hel⟩ | ⟨-, hHuv, hce⟩
    · have hcol := huv.2
      rw [hel, hf.rotate_fan t htn l hl, ← hf.color l (by omega)] at hcol
      rcases hcol with hcol | hcol
      · exact absurd hcol (hαx (hf.adj l (by omega)))
      · rw [← hβ, ← hf.color i hi] at hcol
        have h2 := hf.inj _ (by omega) _ (by omega) (hc.2 (hf.adj l (by omega)) (hf.adj i hi) hcol)
        have hli : l = i := by omega
        subst hli
        have hxi : F.Reachable x (f l) := hit hl
        rcases Sym2.eq_iff.mp hel with ⟨_, hv⟩ | ⟨_, hv⟩
        · rw [hv]; exact hxi
        · rw [hv]
    · exact hu.trans (Adj.reachable ⟨hHuv, hce ▸ huv.2⟩)
  have hftK : ¬ F'.Reachable x (f t) := fun h =>
    hft (Reachable.of_closed hclosed h (Reachable.refl x))
  have hKcl : ∀ ⦃u v⦄, u ∈ {w | F'.Reachable x w} → F'.Adj u v → v ∈ {w | F'.Reachable x w} :=
    fun _ _ hu huv => hu.trans huv.reachable
  refine ⟨_, (hψ.kempeSwap hα hβk hKcl).insertEdge hβk ?_ ?_⟩
  · refine EdgeColorMissing.kempeSwap_of_mem (K := {w | F'.Reachable x w})
      (show x ∈ {w | F'.Reachable x w} from Reachable.refl x) ?_
    rw [Equiv.swap_apply_right]
    exact rotate_missing_x hf htn hαx
  · exact EdgeColorMissing.kempeSwap_of_notMem hKcl hftK (hmt ▸ rotate_missing_last hxy hm hf htn)

end Rotation

/-- **Vizing's fan lemma.** Let `xy` be an edge of `G` and `c` a proper `k`-edge-colouring of
`G - xy` such that `x` misses a colour `α < k` and every neighbour `z` of `x` misses a colour
`m z < k`. Then `G` has a proper `k`-edge-colouring. -/
theorem exists_isProperEdgeColoring_of_fan [Finite V] (hxy : G.Adj x y)
    (hc : (G.deleteEdges {s(x, y)}).IsProperEdgeColoring c k) {α : ℕ} (hα : α < k)
    (hαx : (G.deleteEdges {s(x, y)}).EdgeColorMissing c x α)
    (hm : ∀ z, G.Adj x z → m z < k ∧ (G.deleteEdges {s(x, y)}).EdgeColorMissing c z (m z)) :
    ∃ c', G.IsProperEdgeColoring c' k := by
  obtain ⟨f, n, hf, hstop⟩ := exists_fan G c x y m
  by_cases hmiss : (G.deleteEdges {s(x, y)}).EdgeColorMissing c x (m (f n))
  · exact fan_success hxy hc hm hf hmiss
  · obtain ⟨i, hi, hβ⟩ := hstop.resolve_left hmiss
    exact fan_kempe hxy hc hm hf hα hαx hi hβ

end Vizing

/-! ### Fournier's and Vizing's theorems -/

/-- **Fournier's theorem** (1973). If every vertex of a finite graph `G` has degree at most `k`
and the vertices of degree exactly `k` form an independent set, then `G` has a proper edge
colouring with `k` colours. -/
theorem exists_isProperEdgeColoring_of_ncard_le [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k)
    (hind : ∀ ⦃u v⦄, G.Adj u v → (G.neighborSet u).ncard < k ∨ (G.neighborSet v).ncard < k) :
    ∃ c : Sym2 V → ℕ, G.IsProperEdgeColoring c k := by
  classical
  induction hn : G.edgeSet.ncard using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  by_cases hE : G.edgeSet = ∅
  · refine ⟨fun _ => 0, fun u v huv => ?_, fun u v w huv => ?_⟩ <;>
      exact absurd (G.mem_edgeSet.mpr huv) (by rw [hE]; exact Set.notMem_empty _)
  obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr hE
  induction e using Sym2.ind with
  | _ u v =>
  have huv : G.Adj u v := he
  obtain ⟨x, y, hxy, hx, hz⟩ : ∃ x y, G.Adj x y ∧ (G.neighborSet x).ncard ≤ k ∧
      ∀ z, G.Adj x z → (G.neighborSet z).ncard < k := by
    by_cases hk : ∃ x, (G.neighborSet x).ncard = k
    · obtain ⟨x, hx⟩ := hk
      have hpos : 0 < k := by
        have := hdeg u
        have : 0 < (G.neighborSet u).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨v, huv⟩
        omega
      obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero (s := G.neighborSet x) (by omega)
      exact ⟨x, y, hy, hx.le, fun z hz => (hind hz).resolve_left (by omega)⟩
    · push Not at hk
      exact ⟨u, v, huv, hdeg u, fun z _ => lt_of_le_of_ne (hdeg z) (hk z)⟩
  have hle : G.deleteEdges {s(x, y)} ≤ G := deleteEdges_le _
  have hsub : ∀ w, ((G.deleteEdges {s(x, y)}).neighborSet w).ncard ≤ (G.neighborSet w).ncard :=
    fun w => Set.ncard_le_ncard (neighborSet_deleteEdges_subset _ w)
  obtain ⟨c, hc⟩ := ih _ (hn ▸ ncard_edgeSet_deleteEdges_lt (G.mem_edgeSet.mpr hxy))
    (G.deleteEdges {s(x, y)}) (fun w => (hsub w).trans (hdeg w))
    (fun a b hab => (hind (hle hab)).imp (fun h => (hsub a).trans_lt h)
      (fun h => (hsub b).trans_lt h)) rfl
  have hx' : ((G.deleteEdges {s(x, y)}).neighborSet x).ncard < k := by
    have := ncard_neighborSet_deleteEdges_self hxy
    omega
  obtain ⟨α, hα, hαx⟩ := exists_edgeColorMissing c hx'
  have : ∀ z, ∃ γ, G.Adj x z → γ < k ∧ (G.deleteEdges {s(x, y)}).EdgeColorMissing c z γ := by
    intro z
    by_cases hz' : G.Adj x z
    · obtain ⟨γ, h1, h2⟩ := exists_edgeColorMissing c ((hsub z).trans_lt (hz z hz'))
      exact ⟨γ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hz'⟩
  choose m hm using this
  exact Vizing.exists_isProperEdgeColoring_of_fan hxy hc hα hαx hm

/-- **Vizing's theorem.** Every finite simple graph has a proper edge colouring with
`Δ(G) + 1` colours. -/
theorem exists_isProperEdgeColoring_maxDegree_add_one [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ∃ c : Sym2 V → ℕ, G.IsProperEdgeColoring c (G.maxDegree + 1) :=
  G.exists_isProperEdgeColoring_of_ncard_le _
    (fun v => by rw [ncard_neighborSet]; exact (G.degree_le_maxDegree v).trans (Nat.le_succ _))
    (fun u _ _ => Or.inl (by
      rw [ncard_neighborSet]; exact Nat.lt_succ_of_le (G.degree_le_maxDegree u)))

/-- **Fournier's theorem** with `degree`: if all degrees are `≤ k` and the vertices of degree `k`
are pairwise non-adjacent, then `k` colours suffice. -/
theorem exists_isProperEdgeColoring_of_degree_le [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hdeg : ∀ v, G.degree v ≤ k)
    (hind : ∀ ⦃u v⦄, G.Adj u v → G.degree u < k ∨ G.degree v < k) :
    ∃ c : Sym2 V → ℕ, G.IsProperEdgeColoring c k :=
  G.exists_isProperEdgeColoring_of_ncard_le k (fun v => by rw [ncard_neighborSet]; exact hdeg v)
    (fun u v huv => by rw [ncard_neighborSet, ncard_neighborSet]; exact hind huv)

/-- **Fournier's theorem** with `maxDegree`: if no two vertices of maximum degree are adjacent,
then `G` has a proper edge colouring with `Δ(G)` colours. -/
theorem exists_isProperEdgeColoring_maxDegree [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hind : ∀ ⦃u v⦄, G.Adj u v → G.degree u < G.maxDegree ∨ G.degree v < G.maxDegree) :
    ∃ c : Sym2 V → ℕ, G.IsProperEdgeColoring c G.maxDegree :=
  G.exists_isProperEdgeColoring_of_degree_le _ G.degree_le_maxDegree hind

/-- A proper `k`-edge-colouring of `G` gives a proper `k`-colouring of its line graph. -/
lemma IsProperEdgeColoring.lineGraph_colorable (hc : G.IsProperEdgeColoring c k) :
    G.lineGraph.Colorable k := by
  have hlt : ∀ e : G.edgeSet, c e < k := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v => exact hc.1 he
  refine ⟨Coloring.mk (fun e => ⟨c e, hlt e⟩) fun {e₁ e₂} hadj heq => ?_⟩
  obtain ⟨hne, w, hw₁, hw₂⟩ := lineGraph_adj_iff_exists.mp hadj
  obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.mp hw₁
  obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp hw₂
  have h1 : G.Adj w a := by rw [← mem_edgeSet, ← ha]; exact e₁.2
  have h2 : G.Adj w b := by rw [← mem_edgeSet, ← hb]; exact e₂.2
  have hcol : c s(w, a) = c s(w, b) := by
    rw [← ha, ← hb]; exact congrArg Fin.val heq
  exact hne (Subtype.ext (by rw [ha, hb, hc.2 h1 h2 hcol]))

/-- **Fournier's theorem** for the line graph: under the hypotheses of
`exists_isProperEdgeColoring_of_ncard_le`, the line graph of `G` is `k`-colourable. -/
theorem lineGraph_colorable_of_ncard_le [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ k)
    (hind : ∀ ⦃u v⦄, G.Adj u v → (G.neighborSet u).ncard < k ∨ (G.neighborSet v).ncard < k) :
    G.lineGraph.Colorable k :=
  (G.exists_isProperEdgeColoring_of_ncard_le k hdeg hind).choose_spec.lineGraph_colorable

end SimpleGraph
