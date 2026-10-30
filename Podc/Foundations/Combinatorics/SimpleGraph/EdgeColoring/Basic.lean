import Mathlib

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/EdgeColoring/Basic.lean

/-!
# Proper edge colourings

Edge colourings of a simple graph are represented as functions `c : Sym2 V → ℕ`; only the values
on edges matter. This representation makes it easy to modify a colouring on a few edges and to
restrict a colouring to a subgraph.

## Main definitions

* `SimpleGraph.IsEdgeColoring G c`: two distinct edges of `G` at a common vertex get distinct
  colours.
* `SimpleGraph.IsProperEdgeColoring G c k`: moreover every edge gets a colour `< k`.
* `SimpleGraph.EdgeColorMissing G c v α`: no edge of `G` at `v` has colour `α`.

## Main results

* `IsEdgeColoring.mono`, `IsProperEdgeColoring.mono`: restriction to subgraphs.
* `exists_edgeColorMissing`: a vertex with fewer than `k` edges misses a colour `< k`.
* `IsEdgeColoring.insertEdge`: colour an uncoloured edge with a colour missing at both ends.
* `exists_listEdgeColoring`: greedy list edge colouring — if every edge `uv` has a list of more
  than `(deg u - 1) + (deg v - 1)` colours, the edges can be coloured from their lists.
-/

namespace SimpleGraph

variable {V : Type*}

/-- `c` is a (proper) edge colouring of `G`: two distinct edges of `G` at a common vertex get
distinct colours. Colours of non-edges are irrelevant. -/
def IsEdgeColoring (G : SimpleGraph V) (c : Sym2 V → ℕ) : Prop :=
  ∀ ⦃u v w : V⦄, G.Adj u v → G.Adj u w → c s(u, v) = c s(u, w) → v = w

/-- `c` is a proper edge colouring of `G` with the colours `0, …, k - 1`. -/
def IsProperEdgeColoring (G : SimpleGraph V) (c : Sym2 V → ℕ) (k : ℕ) : Prop :=
  (∀ ⦃u v : V⦄, G.Adj u v → c s(u, v) < k) ∧ G.IsEdgeColoring c

/-- The colour `α` is missing at `v` (with respect to `G` and `c`): no edge of `G` at `v` has
colour `α`. -/
def EdgeColorMissing (G : SimpleGraph V) (c : Sym2 V → ℕ) (v : V) (α : ℕ) : Prop :=
  ∀ ⦃w : V⦄, G.Adj v w → c s(v, w) ≠ α

variable {G H : SimpleGraph V} {c c' : Sym2 V → ℕ} {k k' : ℕ}

lemma IsEdgeColoring.mono (h : G.IsEdgeColoring c) (hle : H ≤ G) : H.IsEdgeColoring c :=
  fun _ _ _ huv huw he => h (hle huv) (hle huw) he

lemma IsProperEdgeColoring.mono (h : G.IsProperEdgeColoring c k) (hle : H ≤ G) (hk : k ≤ k') :
    H.IsProperEdgeColoring c k' :=
  ⟨fun _ _ huv => (h.1 (hle huv)).trans_le hk, h.2.mono hle⟩

lemma IsEdgeColoring.congr (h : G.IsEdgeColoring c)
    (hcc : ∀ ⦃u v : V⦄, G.Adj u v → c' s(u, v) = c s(u, v)) : G.IsEdgeColoring c' :=
  fun _ _ _ huv huw he => h huv huw (by rwa [← hcc huv, ← hcc huw])

lemma IsProperEdgeColoring.congr (h : G.IsProperEdgeColoring c k)
    (hcc : ∀ ⦃u v : V⦄, G.Adj u v → c' s(u, v) = c s(u, v)) : G.IsProperEdgeColoring c' k :=
  ⟨fun _ _ huv => by rw [hcc huv]; exact h.1 huv, h.2.congr hcc⟩

lemma EdgeColorMissing.mono (h : G.EdgeColorMissing c v α) (hle : H ≤ G) :
    H.EdgeColorMissing c v α :=
  fun _ hw => h (hle hw)

/-- Symmetric form of `IsEdgeColoring`: at a common vertex `u`, edges `vu` and `wu`. -/
lemma IsEdgeColoring.eq_of_adj_left (h : G.IsEdgeColoring c) {u v w : V} (huv : G.Adj v u)
    (huw : G.Adj w u) (he : c s(v, u) = c s(w, u)) : v = w :=
  h huv.symm huw.symm (by rwa [Sym2.eq_swap, Sym2.eq_swap (a := u)])

/-- A vertex of `G` with fewer than `k` neighbours misses some colour `< k`. -/
lemma exists_edgeColorMissing [Finite V] (c : Sym2 V → ℕ) {v : V}
    (hdeg : (G.neighborSet v).ncard < k) : ∃ α < k, G.EdgeColorMissing c v α := by
  have himg : ((fun w => c s(v, w)) '' G.neighborSet v).ncard < (Set.Iio k).ncard := by
    have hk : (Set.Iio k).ncard = k := by simp
    rw [hk]
    exact (Set.ncard_image_le (Set.toFinite _)).trans_lt hdeg
  obtain ⟨α, hα, hnot⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard himg (Set.toFinite _)
  exact ⟨α, hα, fun w hw he => hnot ⟨w, hw, he⟩⟩

open Classical in
/-- Colour the edge `uv` with `α`, keeping all other colours. -/
noncomputable def recolorEdge (c : Sym2 V → ℕ) (e : Sym2 V) (α : ℕ) : Sym2 V → ℕ :=
  fun f => if f = e then α else c f

@[simp] lemma recolorEdge_self (c : Sym2 V → ℕ) (e : Sym2 V) (α : ℕ) :
    recolorEdge c e α e = α := by simp [recolorEdge]

lemma recolorEdge_of_ne (c : Sym2 V → ℕ) {e f : Sym2 V} (α : ℕ) (h : f ≠ e) :
    recolorEdge c e α f = c f := by simp [recolorEdge, h]

/-- Colouring an uncoloured edge `uv` with a colour missing at `u` and at `v` gives an edge
colouring of the larger graph. -/
lemma IsEdgeColoring.insertEdge {u v : V} {α : ℕ}
    (hc : (G.deleteEdges {s(u, v)}).IsEdgeColoring c)
    (hu : (G.deleteEdges {s(u, v)}).EdgeColorMissing c u α)
    (hv : (G.deleteEdges {s(u, v)}).EdgeColorMissing c v α) :
    G.IsEdgeColoring (recolorEdge c s(u, v) α) := by
  intro a b d hab had he
  by_cases hb : s(a, b) = s(u, v) <;> by_cases hd : s(a, d) = s(u, v)
  · rw [← hd] at hb
    exact Sym2.congr_right.mp hb
  · rw [recolorEdge_of_ne _ _ hd, hb, recolorEdge_self] at he
    have had' : (G.deleteEdges {s(u, v)}).Adj a d := by simp [had, hd]
    rcases Sym2.eq_iff.mp hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd he.symm (hu had')
    · exact absurd he.symm (hv had')
  · rw [recolorEdge_of_ne _ _ hb, hd, recolorEdge_self] at he
    have hab' : (G.deleteEdges {s(u, v)}).Adj a b := by simp [hab, hb]
    rcases Sym2.eq_iff.mp hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd he (hu hab')
    · exact absurd he (hv hab')
  · rw [recolorEdge_of_ne _ _ hb, recolorEdge_of_ne _ _ hd] at he
    exact hc (by simp [hab, hb]) (by simp [had, hd]) he

lemma neighborSet_deleteEdges_self {u v : V} (h : G.Adj u v) :
    (G.deleteEdges {s(u, v)}).neighborSet u = G.neighborSet u \ {v} := by
  ext w
  simp only [mem_neighborSet, deleteEdges_adj, Set.mem_singleton_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hw => h2 (by rw [hw])⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun he => h2 ?_⟩
    rcases Sym2.eq_iff.mp he with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (G.irrefl h).elim

lemma ncard_neighborSet_deleteEdges_self [Finite V] {u v : V} (h : G.Adj u v) :
    ((G.deleteEdges {s(u, v)}).neighborSet u).ncard + 1 = (G.neighborSet u).ncard := by
  rw [neighborSet_deleteEdges_self h]
  exact Set.ncard_sdiff_singleton_add_one h (Set.toFinite _)

lemma neighborSet_deleteEdges_subset (s : Set (Sym2 V)) (u : V) :
    (G.deleteEdges s).neighborSet u ⊆ G.neighborSet u :=
  fun _ hw => (deleteEdges_le s) hw

lemma ncard_edgeSet_deleteEdges_lt [Finite V] {e : Sym2 V} (he : e ∈ G.edgeSet) :
    (G.deleteEdges {e}).edgeSet.ncard < G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  exact Set.ncard_sdiff_singleton_lt_of_mem he (Set.toFinite _)

/-- **Greedy list edge colouring.** If every edge `uv` of a finite graph has a list `L s(u, v)`
of more than `(deg u - 1) + (deg v - 1)` colours, then the edges can be coloured properly with
every edge receiving a colour from its list. -/
theorem exists_listEdgeColoring [Finite V] (G : SimpleGraph V) (L : Sym2 V → Finset ℕ)
    (hL : ∀ ⦃u v : V⦄, G.Adj u v →
      (G.neighborSet u).ncard + (G.neighborSet v).ncard < (L s(u, v)).card + 2) :
    ∃ c : Sym2 V → ℕ, (∀ ⦃u v : V⦄, G.Adj u v → c s(u, v) ∈ L s(u, v)) ∧ G.IsEdgeColoring c := by
  induction hn : G.edgeSet.ncard using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  by_cases hE : G.edgeSet = ∅
  · refine ⟨fun _ => 0, fun u v huv => ?_, fun u v w huv => ?_⟩ <;>
      exact absurd (G.mem_edgeSet.mpr huv) (by rw [hE]; exact Set.notMem_empty _)
  obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr hE
  induction e using Sym2.ind with
  | _ u v =>
  have huv : G.Adj u v := he
  set G' := G.deleteEdges {s(u, v)} with hG'
  have hle : G' ≤ G := deleteEdges_le _
  obtain ⟨c, hcL, hc⟩ := ih _ (hn ▸ ncard_edgeSet_deleteEdges_lt he) G' (fun a b hab =>
    lt_of_le_of_lt (Nat.add_le_add (Set.ncard_le_ncard (neighborSet_deleteEdges_subset _ a))
      (Set.ncard_le_ncard (neighborSet_deleteEdges_subset _ b))) (hL (hle hab))) rfl
  set F : Set ℕ := (fun w => c s(u, w)) '' G'.neighborSet u ∪ (fun w => c s(v, w)) '' G'.neighborSet v
  have hF : F.ncard < ((L s(u, v) : Finset ℕ) : Set ℕ).ncard := by
    rw [Set.ncard_coe_finset]
    have h1 := ncard_neighborSet_deleteEdges_self huv
    have h2 : ((G.deleteEdges {s(v, u)}).neighborSet v).ncard + 1 = (G.neighborSet v).ncard :=
      ncard_neighborSet_deleteEdges_self huv.symm
    rw [Sym2.eq_swap] at h2
    rw [← hG'] at h1 h2
    have := hL huv
    calc F.ncard ≤ ((fun w => c s(u, w)) '' G'.neighborSet u).ncard
          + ((fun w => c s(v, w)) '' G'.neighborSet v).ncard := Set.ncard_union_le _ _
      _ ≤ (G'.neighborSet u).ncard + (G'.neighborSet v).ncard :=
          Nat.add_le_add (Set.ncard_image_le (Set.toFinite _)) (Set.ncard_image_le (Set.toFinite _))
      _ < _ := by omega
  obtain ⟨α, hαL, hαF⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hF (Set.toFinite _)
  refine ⟨recolorEdge c s(u, v) α, fun a b hab => ?_, hc.insertEdge (fun w hw he => hαF ?_)
    (fun w hw he => hαF ?_)⟩
  · by_cases hb : s(a, b) = s(u, v)
    · rw [hb, recolorEdge_self]; exact hαL
    · rw [recolorEdge_of_ne _ _ hb]; exact hcL (by simp [hG', hab, hb])
  · exact Or.inl ⟨w, hw, he⟩
  · exact Or.inr ⟨w, hw, he⟩

end SimpleGraph
