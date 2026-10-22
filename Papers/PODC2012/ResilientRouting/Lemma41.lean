import Papers.PODC2012.ResilientRouting.Model

/-!
# Lemma 4.1, repaired

Lemma 4.1 of the paper: *"For any edge `e_uv`, if `v` has any working path to the destination
which does not use the edge `e_vu`, then `v` must not send a packet traveling `u → v` back to `u`."*

The proof fails all links of `u` other than `uv` and needs `v` to keep its path to `d` in that
scenario; a path that merely avoids the *edge* `vu` may pass through `u` and be destroyed. As
stated the lemma is false (`Counterexamples.lemma_4_1_false`); the correct hypothesis is that `v` reaches `d`
after the other links of `u` fail (`lemma_4_1`). The core of the argument, for a node `u` whose
only live link is `uv`, is `lemma_4_1_core`; with a node `v` that has exactly two live links it
forces `v` to pass packets through (`pass_through`).
-/

namespace Podc.ResilientRouting

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {d : V} {f : Pattern G} {F : Set (Sym2 V)}

/-- Core of Lemma 4.1: if `u ≠ d` is connected to `d` and its only live link is `uv` (`v ≠ d`),
then `v` must forward a packet coming from `u` over a live link other than `vu`. -/
theorem lemma_4_1_core (hgood : Good G d f F) {u v : V} (hu : u ≠ d) (hv : v ≠ d)
    (hr : (G.deleteEdges F).Reachable u d) (hu1 : ∀ y, Live G F u y → y = v) :
    f.next v (view G F v) u ≠ u ∧ Live G F v (f.next v (view G F v) u) := by
  by_contra hcon
  refine not_good_of_trap (f := f) {(u, v), (v, u)} ?_ hu hr
    (fun y hy => by simp [hu1 y hy]) hgood
  intro δ hδ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
  rcases hδ with rfl | rfl
  · refine ⟨hv, fun hl => ?_⟩
    have : f.next v (view G F v) u = u := by
      by_contra hne; exact hcon ⟨hne, hl⟩
    simp [nxt, this]
  · refine ⟨hu, fun hl => ?_⟩
    have : f.next u (view G F u) v = v := hu1 _ hl
    simp [nxt, this]

/-- A node `v ≠ d` whose live links are exactly `vu` and `vw` must forward packets from `u` to `w`,
if `u ≠ d` is connected to `d` and its only live link is `uv`. -/
theorem pass_through (hgood : Good G d f F) {u v w : V} (hu : u ≠ d) (hv : v ≠ d)
    (hr : (G.deleteEdges F).Reachable u d) (hu1 : ∀ y, Live G F u y → y = v)
    (hv2 : ∀ y, Live G F v y → y = u ∨ y = w) : f.next v (view G F v) u = w := by
  obtain ⟨h1, h2⟩ := lemma_4_1_core hgood hu hv hr hu1
  exact (hv2 _ h2).resolve_left h1

/-- **Lemma 4.1** of the paper, with the hypothesis repaired: if `v` still reaches `d` when all
links of `u` other than `uv` fail, then a perfectly resilient pattern does not send a packet
travelling `u → v` back to `u`. -/
theorem lemma_4_1 (hf : PerfectlyResilient G d f) (hF : F ⊆ G.edgeSet) {u v : V}
    (huv : Live G F u v) (hu : u ≠ d) (hv : v ≠ d)
    (hr : (G.deleteEdges (F ∪ {e | e ∈ G.edgeSet ∧ u ∈ e ∧ e ≠ s(u, v)})).Reachable v d) :
    f.next v (view G F v) u ≠ u := by
  set F' := F ∪ {e | e ∈ G.edgeSet ∧ u ∈ e ∧ e ≠ s(u, v)}
  have hF' : F' ⊆ G.edgeSet := Set.union_subset hF fun _ h => h.1
  have hne : u ≠ v := huv.1.ne
  have hview : view G F' v = view G F v := by
    ext y
    simp only [view, Live, F', Set.mem_ofPred_eq, Set.mem_union, not_or, not_and, not_not]
    constructor
    · exact fun h => ⟨h.1, h.2.1⟩
    · refine fun h => ⟨h.1, h.2, fun _ hu' => ?_⟩
      rcases Sym2.mem_iff.1 hu' with h' | h'
      · exact absurd h' hne
      · rw [h', Sym2.eq_swap]
  have hlive : Live G F' u v := ⟨huv.1, by
    simp only [F', Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not]
    exact ⟨huv.2, fun _ _ => trivial⟩⟩
  have hu1 : ∀ y, Live G F' u y → y = v := by
    intro y hy
    have h2 := hy.2
    simp only [F', Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at h2
    have := h2.2 hy.1 (Sym2.mem_mk_left u y)
    rcases Sym2.eq_iff.1 this with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hne
  have hru : (G.deleteEdges F').Reachable u d :=
    (deleteEdges_adj.2 hlive).reachable.trans hr
  have := (lemma_4_1_core (hf F' hF') hu hv hru hu1).1
  rwa [hview] at this

end Podc.ResilientRouting
