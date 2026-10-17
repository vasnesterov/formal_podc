import Papers.PODC2012.IterativeApproxBC.Condition

/-!
# Applications of the condition (Section 6 of Vaidya–Tseng–Liang, PODC 2012)

We check the condition of Theorem 1 (`Condition G f`) on the specific networks of Section 6
of [VTL12].

* `condition_complete_iff` — the complete graph satisfies the condition iff `n > 3f`
  (for `n ≥ 2`).
* `IsCoreNetwork` (Definition 4) and `IsCoreNetwork.condition` (Section 6.1: "it is easy to show
  that a core network satisfies the necessary condition"); `isCoreNetwork_example` is a
  non-complete core network on 5 nodes.
* `hypercube` and `not_condition_hypercube` (Section 6.2): the `d`-dimensional binary hypercube
  violates the condition for every `f ≥ 1` (cut along one dimension).
* `chord` (Definition 5), `not_condition_chord_7_2` (Section 6.3: the chord network with
  `n = 7`, `f = 2` violates the condition) and `condition_chord_5_1` (the chord network with
  `n = 5`, `f = 1` satisfies it).

Concrete graphs are handled by `inNbrs_eq_filter` (a decidable description of the classical
`inNbrs`) and `condition_of_labelings`, which reduces the condition to a decidable statement
about labelings `V → Fin 4` (label `0, 1, 2, 3` for `F, L, C, R`), checked by `decide +kernel`.
-/

open Finset Cslib.ApproxConsensus

namespace IterativeApproxBC

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} {f : ℕ}

/-! ## Generic counting helpers -/

/-- If `A ⇏ B` and `v ∈ B`, then any set of in-neighbours of `v` inside `A` has at most `f`
elements. -/
theorem card_le_of_not_arrow {A B S : Finset V} {v : V} (h : ¬ Arrow G f A B) (hv : v ∈ B)
    (hS : S ⊆ inNbrs G v) (hSA : S ⊆ A) : #S ≤ f := by
  by_contra hc
  exact h ⟨v, hv, (Nat.succ_le_of_lt (not_le.mp hc)).trans
    (card_le_card (subset_inter hS hSA))⟩

/-- `n ≤ |F| + |L ∪ C| + |C ∪ R|` for a cover `F ∪ L ∪ C ∪ R` of `V`. -/
theorem card_le_of_cover {F L C R : Finset V} (hU : F ∪ L ∪ C ∪ R = univ) :
    Fintype.card V ≤ #F + #(L ∪ C) + #(C ∪ R) := by
  rw [← card_univ, ← hU]
  calc #(F ∪ L ∪ C ∪ R) ≤ #(F ∪ (L ∪ C) ∪ (C ∪ R)) :=
        card_le_card fun x => by simp only [mem_union]; tauto
    _ ≤ #(F ∪ (L ∪ C)) + #(C ∪ R) := card_union_le _ _
    _ ≤ #F + #(L ∪ C) + #(C ∪ R) := by have := card_union_le F (L ∪ C); omega

/-- A sufficient criterion: if every node of `L` hears all of `C ∪ R` and every node of `R`
hears all of `L ∪ C` (e.g. in the complete graph), the failure of both arrows forces
`n ≤ 3f`. -/
theorem card_le_of_not_arrows {F L C R : Finset V} {v w : V} (hU : F ∪ L ∪ C ∪ R = univ)
    (hF : #F ≤ f) (h1 : ¬ Arrow G f (C ∪ R) L) (h2 : ¬ Arrow G f (L ∪ C) R) (hv : v ∈ L)
    (hw : w ∈ R) (hvN : C ∪ R ⊆ inNbrs G v) (hwN : L ∪ C ⊆ inNbrs G w) :
    Fintype.card V ≤ 3 * f := by
  have a := card_le_of_not_arrow h1 hv hvN subset_rfl
  have b := card_le_of_not_arrow h2 hw hwN subset_rfl
  have := card_le_of_cover hU
  omega

/-! ## The complete graph -/

/-- Section 6 of [VTL12] (and the discussion after Corollary 2): the complete graph satisfies the
condition when `n > 3f`. -/
theorem condition_complete (h : 3 * f < Fintype.card V) : Condition (⊤ : Digraph V) f := by
  intro F L C R hFL hFC hFR hLC hLR hCR hU hF ⟨v, hv⟩ ⟨w, hw⟩
  by_contra hcon
  rw [not_or] at hcon
  have := card_le_of_not_arrows hU hF hcon.1 hcon.2 hv hw
    (fun x hx => mem_inNbrs.mpr ⟨trivial, fun hxv => by
      subst hxv; simp only [mem_union] at hx
      exact hx.elim (disjoint_left.mp hLC hv) (disjoint_left.mp hLR hv)⟩)
    (fun x hx => mem_inNbrs.mpr ⟨trivial, fun hxw => by
      subst hxw; simp only [mem_union] at hx
      exact hx.elim (disjoint_right.mp hLR hw) (disjoint_right.mp hCR hw)⟩)
  omega

/-- The complete graph on `n ≥ 2` nodes satisfies the condition iff `n > 3f` (the converse is
Corollary 2 of [VTL12]). -/
theorem condition_complete_iff (hn : 2 ≤ Fintype.card V) :
    Condition (⊤ : Digraph V) f ↔ 3 * f < Fintype.card V :=
  ⟨fun h => h.three_mul_lt_card hn, condition_complete⟩

/-! ## Core networks (Section 6.1) -/

/-- Definition 4 of [VTL12] (core network): `n > 3f`, `G` contains a clique on a set `K` of
`2f + 1` nodes, and every node outside `K` is linked in both directions to every node of `K`.
Other edges are allowed. -/
def IsCoreNetwork (G : Digraph V) (f : ℕ) (K : Finset V) : Prop :=
  3 * f < Fintype.card V ∧ #K = 2 * f + 1 ∧ (∀ i ∈ K, ∀ j ∈ K, i ≠ j → G.Adj i j) ∧
    ∀ v ∉ K, ∀ u ∈ K, G.Adj v u ∧ G.Adj u v

/-- Section 6.1 of [VTL12]: a core network satisfies the condition of Theorem 1. -/
theorem IsCoreNetwork.condition {K : Finset V} (hG : IsCoreNetwork G f K) : Condition G f := by
  obtain ⟨hn, hK, hclique, hout⟩ := hG
  -- a node of `K` hears every other node; a node outside `K` hears all of `K`
  have hinK : ∀ v ∈ K, ∀ S : Finset V, v ∉ S → S ⊆ inNbrs G v := fun v hv S hvS x hx => by
    refine mem_inNbrs.mpr ⟨?_, fun h => hvS (h ▸ hx)⟩
    by_cases hxK : x ∈ K
    · exact hclique x hxK v hv fun h => hvS (h ▸ hx)
    · exact (hout x hxK v hv).1
  have hout' : ∀ v ∉ K, K ⊆ inNbrs G v := fun v hv u hu =>
    mem_inNbrs.mpr ⟨(hout v hv u hu).2, fun h => hv (h ▸ hu)⟩
  intro F L C R hFL hFC hFR hLC hLR hCR hU hF ⟨v, hv⟩ ⟨w, hw⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hmem : ∀ x, x ∈ F ∨ x ∈ L ∨ x ∈ C ∨ x ∈ R := fun x => by
    have := hU ▸ mem_univ x; simp only [mem_union] at this; tauto
  -- if `K` misses `B ∈ {L, R}`, a node of `B` hears all of `K`, but at most `f` of `K \ F`
  have key : ∀ (A B : Finset V) (b : V), b ∈ B → ¬ Arrow G f A B → Disjoint K B →
      (∀ x ∈ K, x ∉ F → x ∈ A) → False := by
    intro A B b hb hAB hKB hKA
    have hbK : b ∉ K := fun h => disjoint_left.mp hKB h hb
    have := card_le_of_not_arrow (S := K \ F) hAB hb (sdiff_subset.trans (hout' b hbK))
      fun x hx => hKA x (mem_sdiff.mp hx).1 (mem_sdiff.mp hx).2
    have := le_card_sdiff F K
    omega
  by_cases hKL : Disjoint K L
  · exact key _ _ v hv h1 hKL fun x hxK hxF => by
      rcases hmem x with h | h | h | h
      · exact absurd h hxF
      · exact absurd h (disjoint_left.mp hKL hxK)
      · exact mem_union_left _ h
      · exact mem_union_right _ h
  by_cases hKR : Disjoint K R
  · exact key _ _ w hw h2 hKR fun x hxK hxF => by
      rcases hmem x with h | h | h | h
      · exact absurd h hxF
      · exact mem_union_left _ h
      · exact mem_union_right _ h
      · exact absurd h (disjoint_left.mp hKR hxK)
  obtain ⟨v', hv'K, hv'L⟩ := not_disjoint_iff.mp hKL
  obtain ⟨w', hw'K, hw'R⟩ := not_disjoint_iff.mp hKR
  have := card_le_of_not_arrows hU hF h1 h2 hv'L hw'R
    (hinK v' hv'K _ fun h => by
      simp only [mem_union] at h
      exact h.elim (disjoint_left.mp hLC hv'L) (disjoint_left.mp hLR hv'L))
    (hinK w' hw'K _ fun h => by
      simp only [mem_union] at h
      exact h.elim (disjoint_right.mp hLR hw'R) (disjoint_right.mp hCR hw'R))
  omega

/-- A core network that is not complete: 5 nodes, `f = 1`, `K = {0, 1, 2}`; the two nodes
`3, 4` outside `K` are not linked to each other. -/
def coreExample : Digraph (Fin 5) where
  Adj i j := i ≠ j ∧ ((i : ℕ) < 3 ∨ (j : ℕ) < 3)

instance : DecidableRel coreExample.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ((i : ℕ) < 3 ∨ (j : ℕ) < 3)))

/-- Definition 4 is not vacuous: `coreExample` is a core network (with `f = 1`), hence satisfies
the condition, although it lacks the edges `3 → 4`, `4 → 3`. -/
theorem isCoreNetwork_example : IsCoreNetwork coreExample 1 {0, 1, 2} := by
  unfold IsCoreNetwork; decide

example : Condition coreExample 1 ∧ ¬ coreExample.Adj 3 4 :=
  ⟨isCoreNetwork_example.condition, by decide⟩

/-! ## The hypercube (Section 6.2) -/

/-- The `d`-dimensional binary hypercube (as a symmetric digraph): two nodes are adjacent iff
they differ in exactly one coordinate. -/
def hypercube (d : ℕ) : Digraph (Fin d → Bool) where
  Adj x y := #(univ.filter fun k => x k ≠ y k) = 1

/-- In the hypercube, a node `v` has at most one in-neighbour differing from it in a given
coordinate `i`. -/
theorem hypercube_card_inNbrs_inter_le {d : ℕ} (v : Fin d → Bool) (i : Fin d)
    (S : Finset (Fin d → Bool)) (hS : ∀ u ∈ S, u i ≠ v i) :
    #(inNbrs (hypercube d) v ∩ S) ≤ 1 := by
  -- an in-neighbour differing at `i` agrees with `v` everywhere else
  have agree : ∀ u ∈ inNbrs (hypercube d) v ∩ S, ∀ k, k ≠ i → u k = v k := by
    intro u hu k hk
    obtain ⟨hN, huS⟩ := mem_inter.mp hu
    have hadj : #(univ.filter fun k => u k ≠ v k) = 1 := (mem_inNbrs.mp hN).1
    by_contra huk
    have : ({i, k} : Finset (Fin d)) ⊆ univ.filter fun k => u k ≠ v k := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · simpa using hS u huS
      · simpa using huk
    have := card_le_card this
    rw [card_pair (Ne.symm hk)] at this
    omega
  refine card_le_one.mpr fun a ha b hb => funext fun k => ?_
  by_cases hk : k = i
  · subst hk
    have h1 := hS a (mem_inter.mp ha).2
    have h2 := hS b (mem_inter.mp hb).2
    revert h1 h2; cases a k <;> cases b k <;> cases v k <;> simp
  · rw [agree a ha k hk, agree b hb k hk]

/-- Section 6.2 of [VTL12]: for `d ≥ 1` and `f ≥ 1`, the `d`-dimensional hypercube does not
satisfy the condition of Theorem 1, although its connectivity `d` may exceed `2f`: cut it along
one dimension (`F = C = ∅`); every node has exactly one in-neighbour on the other side. -/
theorem not_condition_hypercube {d : ℕ} (hd : 1 ≤ d) (hf : 1 ≤ f) :
    ¬ Condition (hypercube d) f := by
  intro h
  set i : Fin d := ⟨0, hd⟩
  set L := univ.filter fun x : Fin d → Bool => x i = false
  set R := univ.filter fun x : Fin d → Bool => x i = true
  have hLR : Disjoint L R := disjoint_filter.mpr fun x _ h1 h2 => by simp_all
  rcases h ∅ L ∅ R (disjoint_empty_left _) (disjoint_empty_left _) (disjoint_empty_left _)
    (disjoint_empty_right _) hLR (disjoint_empty_left _)
    (by ext x; cases hx : x i <;> simp [L, R, hx]) (by simp)
    ⟨fun _ => false, by simp [L]⟩ ⟨fun _ => true, by simp [R]⟩ with ⟨v, hv, hc⟩ | ⟨v, hv, hc⟩
  · rw [empty_union] at hc
    have := hypercube_card_inNbrs_inter_le v i R fun u hu => by
      simp only [L, R, mem_filter, mem_univ, true_and] at hu hv; simp [hu, hv]
    omega
  · rw [union_empty] at hc
    have := hypercube_card_inNbrs_inter_le v i L fun u hu => by
      simp only [L, R, mem_filter, mem_univ, true_and] at hu hv; simp [hu, hv]
    omega

/-! ## Decidable descriptions for concrete graphs -/

/-- The condition of Theorem 1 in terms of labelings `lab : V → Fin 4` (`0, 1, 2, 3` meaning
`F, L, C, R`); for a concrete finite graph the hypothesis is decidable. -/
theorem condition_of_labelings [DecidableRel G.Adj]
    (h : ∀ lab : V → Fin 4, #(univ.filter fun x => lab x = 0) ≤ f → (∃ v, lab v = 1) →
      (∃ v, lab v = 3) →
      (∃ v, lab v = 1 ∧ f + 1 ≤ #(univ.filter fun j => G.Adj j v ∧ j ≠ v ∧ 2 ≤ lab j)) ∨
      (∃ v, lab v = 3 ∧ f + 1 ≤ #(univ.filter fun j => G.Adj j v ∧ j ≠ v ∧ 1 ≤ lab j ∧ lab j ≤ 2))) :
    Condition G f := by
  intro F L C R hFL hFC hFR hLC hLR hCR hU hF hL hR
  let lab : V → Fin 4 := fun x => if x ∈ F then 0 else if x ∈ L then 1 else if x ∈ C then 2 else 3
  have hmem : ∀ x, x ∈ F ∨ x ∈ L ∨ x ∈ C ∨ x ∈ R := fun x => by
    have := hU ▸ mem_univ x; simp only [mem_union] at this; tauto
  have hlab : ∀ x, (lab x = 0 ↔ x ∈ F) ∧ (lab x = 1 ↔ x ∈ L) ∧ (lab x = 3 ↔ x ∈ R) ∧
      (2 ≤ lab x ↔ x ∈ C ∪ R) ∧ (1 ≤ lab x ∧ lab x ≤ 2 ↔ x ∈ L ∪ C) := fun x => by
    rcases hmem x with hx | hx | hx | hx
    · simp [lab, hx, disjoint_left.mp hFL hx, disjoint_left.mp hFC hx, disjoint_left.mp hFR hx]
    · simp [lab, hx, disjoint_right.mp hFL hx, disjoint_left.mp hLC hx, disjoint_left.mp hLR hx]
    · simp [lab, hx, disjoint_right.mp hFC hx, disjoint_right.mp hLC hx, disjoint_left.mp hCR hx]
    · simp [lab, hx, disjoint_right.mp hFR hx, disjoint_right.mp hLR hx, disjoint_right.mp hCR hx]
  have h0 x := (hlab x).1
  have h1 x := (hlab x).2.1
  have h3 x := (hlab x).2.2.1
  have h2 x := (hlab x).2.2.2.1
  have h12 x := (hlab x).2.2.2.2
  have eF : (univ.filter fun x => lab x = 0) = F := by ext x; simp [h0]
  obtain ⟨v, hv⟩ := hL
  obtain ⟨w, hw⟩ := hR
  rcases h lab (eF ▸ hF) ⟨v, (h1 v).mpr hv⟩ ⟨w, (h3 w).mpr hw⟩ with ⟨u, hu, hc⟩ | ⟨u, hu, hc⟩
  · refine Or.inl ⟨u, (h1 u).mp hu, hc.trans_eq (congrArg card ?_)⟩
    ext j; simp [h2, and_assoc]
  · refine Or.inr ⟨u, (h3 u).mp hu, hc.trans_eq (congrArg card ?_)⟩
    ext j; simp [h12, and_assoc]

/-! ## Chord networks (Section 6.3) -/

/-- Definition 5 of [VTL12] (chord network): nodes `0, …, n - 1`, and `(i, j)` is an edge iff
`j = i + k mod n` for some `1 ≤ k ≤ 2f + 1`. (The paper also requires `n > 3f`; it is not part
of the graph.) -/
def chord (n f : ℕ) : Digraph (Fin n) where
  Adj i j := ∃ k, 1 ≤ k ∧ k ≤ 2 * f + 1 ∧ (j : ℕ) = (i + k) % n

theorem chord_adj_iff {n f : ℕ} {i j : Fin n} :
    (chord n f).Adj i j ↔ ∃ k : Fin (2 * f + 1), (j : ℕ) = (i + (k + 1)) % n := by
  constructor
  · rintro ⟨k, hk1, hk2, h⟩
    exact ⟨⟨k - 1, by omega⟩, by rw [h]; congr 2; simp; omega⟩
  · rintro ⟨k, h⟩
    exact ⟨k + 1, by omega, by omega, h⟩

instance {n f : ℕ} : DecidableRel (chord n f).Adj := fun _ _ =>
  decidable_of_iff _ chord_adj_iff.symm

/-- Section 6.3 of [VTL12]: the chord network with `n = 7`, `f = 2` does not satisfy the
condition of Theorem 1. Witness (from the paper): `F = {5, 6}`, `L = {0, 2}`, `C = ∅`,
`R = {1, 3, 4}`; `L ⇏ R` since `|L| < 3`, and `R ⇏ L` since `N₀⁻ ∩ R = {3, 4}` and
`N₂⁻ ∩ R = {1, 4}`. -/
theorem not_condition_chord_7_2 : ¬ Condition (chord 7 2) 2 := by
  intro h
  rcases h {5, 6} {0, 2} ∅ {1, 3, 4} (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) with h | h
  · revert h
    simp only [Arrow, inNbrs_eq_filter]
    decide
  · exact not_arrow_of_card_le (by decide) h

/-- Section 6.3 of [VTL12]: the chord network with `n = 5`, `f = 1` satisfies the condition of
Theorem 1 (checked over all `4⁵` labelings by kernel computation). -/
theorem condition_chord_5_1 : Condition (chord 5 1) 1 :=
  condition_of_labelings (by decide +kernel)

end IterativeApproxBC
