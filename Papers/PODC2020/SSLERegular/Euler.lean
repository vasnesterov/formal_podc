import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Euler's theorem (existence of Eulerian circuits)

Mathlib defines `SimpleGraph.Walk.IsEulerian` and proves the necessary degree conditions
(`SimpleGraph.Walk.IsEulerian.even_degree_iff`), but not the existence direction. We prove it:

* `SSLERegular.exists_isEulerian_of_even_degree`: a connected finite graph all of whose degrees
  are even has an Eulerian circuit.
* `SSLERegular.exists_euler_cyclic_seq`: the same, as a cyclic vertex sequence
  `p : Fin #E → V` whose consecutive pairs (indices mod `#E`) enumerate every edge exactly once.

Proof: take a trail of maximal length (`exists_isTrail_forall_isTrail_length_le_length`).
It is closed, since otherwise its first vertex has odd trail-degree, hence an unused incident
edge, and prepending it gives a longer trail. Every edge incident to its support is used, since
otherwise rotating the circuit to that vertex and prepending the edge gives a longer trail.
By connectivity its support is everything, so it uses every edge.
-/

namespace SSLERegular

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

/-- In a graph with all degrees even, if a trail uses every edge at its start vertex `u`, then
the trail is closed. -/
lemma isTrail_closed_of_forall_adj_mem_edges [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v)) {u v : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hall : ∀ w, G.Adj u w → s(u, w) ∈ p.edges) : u = v := by
  by_contra huv
  have hodd := (hp.even_countP_edges_iff u).not.2 (by simp [huv])
  apply hodd
  rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
  have : Multiset.filter (fun e => u ∈ e) (p.edges : Multiset (Sym2 V))
      = (G.incidenceFinset u).val := by
    rw [incidenceFinset_eq_filter]
    change Multiset.filter (fun e => u ∈ e) hp.edgesFinset.val = _
    rw [← Finset.filter_val]
    congr 1
    ext e
    simp only [mem_filter, mem_edgeFinset]
    constructor
    · rintro ⟨he, hue⟩
      exact ⟨p.edges_subset_edgeSet he, hue⟩
    · rintro ⟨he, hue⟩
      refine ⟨?_, hue⟩
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hue
      exact hall w he
  rw [this, ← Finset.card_def, card_incidenceFinset_eq_degree]
  exact heven u

-- CSLib candidate
/-- Euler: a connected finite graph in which every vertex has even degree has an Eulerian
circuit. -/
theorem exists_isEulerian_of_even_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v)) : ∃ u, ∃ w : G.Walk u u, w.IsEulerian := by
  have : Nonempty V := hconn.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isTrail_forall_isTrail_length_le_length G
  -- the maximal trail is closed
  have huv : u = v := by
    refine isTrail_closed_of_forall_adj_mem_edges heven hp fun w hw => ?_
    by_contra hnot
    have := hmax w v (Walk.cons hw.symm p) (hp.cons hw.symm (by rwa [Sym2.eq_swap]))
    simp at this
  subst huv
  -- every edge at a vertex of the support is used
  have hloc : ∀ a ∈ p.support, ∀ b, G.Adj a b → s(a, b) ∈ p.edges := by
    intro a ha b hab
    by_contra hnot
    have hrot : (p.rotate a ha).IsTrail := hp.rotate ha
    have hnot' : s(b, a) ∉ (p.rotate a ha).edges := by
      rw [(p.rotate_edges a ha).perm.mem_iff, Sym2.eq_swap]; exact hnot
    have := hmax b a (Walk.cons hab.symm (p.rotate a ha)) (hrot.cons hab.symm hnot')
    simp at this
  -- by connectivity the support is everything
  have hsupp : ∀ x, x ∈ p.support := by
    have key : ∀ {a x : V} (q : G.Walk a x), a ∈ p.support → x ∈ p.support := by
      intro a x q
      induction q with
      | nil => exact id
      | cons hab q ih =>
        intro ha
        exact ih (p.snd_mem_support_of_mem_edges (hloc _ ha _ hab))
    intro x
    exact key (hconn.preconnected u x).some p.start_mem_support
  refine ⟨u, p, hp.isEulerian_of_forall_mem fun e he => ?_⟩
  induction e using Sym2.ind with
  | _ a b => exact hloc a (hsupp a) b he

-- CSLib candidate
/-- Cyclic-sequence form of Euler's theorem: listing the vertices of an Euler circuit as
`p 0, p 1, …, p (M-1)` (indices mod `M = #edges`), consecutive vertices are adjacent and every
edge is traversed exactly once (injective form). -/
theorem exists_euler_cyclic_seq_injective {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v)) :
    ∃ p : Fin G.edgeFinset.card → V,
      (∀ t, G.Adj (p t) (p (finRotate _ t))) ∧
      Function.Injective (fun t => s(p t, p (finRotate _ t))) := by
  obtain ⟨u, w, hw⟩ := exists_isEulerian_of_even_degree G hconn heven
  have hlen : w.length = G.edgeFinset.card := by
    rw [← Walk.length_edges, ← hw.edgesFinset_eq]
    rfl
  set M := G.edgeFinset.card with hM
  -- the vertex after position `t` (mod `M`) is `w.getVert (t + 1)`
  have hnext : ∀ t : Fin M, w.getVert (finRotate M t : ℕ) = w.getVert ((t : ℕ) + 1) := by
    intro t
    have hv : (finRotate M t : ℕ) = ((t : ℕ) + 1) % M := by
      have := t.neZero
      rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
    rw [hv]
    rcases Nat.lt_or_ge ((t : ℕ) + 1) M with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have : (t : ℕ) + 1 = M := by have := t.2; omega
      rw [this, Nat.mod_self, Walk.getVert_zero, ← hlen, Walk.getVert_length]
  refine ⟨fun t => w.getVert t, fun t => ?_, fun t₁ t₂ h => ?_⟩
  · simp only
    rw [hnext]
    exact w.adj_getVert_succ (by omega)
  · simp only [hnext] at h
    have h1 : (t₁ : ℕ) < w.edges.length := by rw [Walk.length_edges]; omega
    have h2 : (t₂ : ℕ) < w.edges.length := by rw [Walk.length_edges]; omega
    rw [← Walk.getElem_edges h1, ← Walk.getElem_edges h2] at h
    exact Fin.ext ((hw.isTrail.edges_nodup.getElem_inj_iff).1 h)

-- CSLib candidate
/-- Cyclic-sequence form of Euler's theorem: listing the vertices of an Euler circuit as
`p 0, p 1, …, p (M-1)` (indices mod `M = #edges`), consecutive vertices are adjacent and every
edge is traversed exactly once, i.e. `t ↦ s(p t, p (t + 1))` is a bijection onto the edge set. -/
theorem exists_euler_cyclic_seq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v)) :
    ∃ p : Fin G.edgeFinset.card → V, ∃ hadj : ∀ t, G.Adj (p t) (p (finRotate _ t)),
      Function.Bijective
        (fun t => (⟨s(p t, p (finRotate _ t)), (G.mem_edgeSet).2 (hadj t)⟩ : G.edgeSet)) := by
  obtain ⟨p, hadj, hinj⟩ := exists_euler_cyclic_seq_injective G hconn heven
  refine ⟨p, hadj, (Fintype.bijective_iff_injective_and_card _).2 ⟨fun t₁ t₂ h => ?_, ?_⟩⟩
  · exact hinj (congrArg Subtype.val h)
  · simp [edgeFinset_card]

end SSLERegular
