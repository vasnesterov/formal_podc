import Papers.PODC2014.CongestedCliquePower.Circuit

/-!
# Assigning the gates of a circuit to the players (proof of Theorem 2 of [DKO14])

The weight of a gate is `w(G) = |in(G)| + |out(G)| + [G is an input gate]`. The total weight is
at most `2N + |X| ≤ n² (2s + 1) = n M` for `N ≤ n² s` wires, `|X| ≤ n²` inputs and
`M = n (2s + 1)`. A gate is heavy iff `w(G) ≥ M`; hence there are at most `n` heavy gates, and
they can be given to distinct players. The light gates are assigned greedily so that the total
weight of the light gates of every player is at most `2M`.

The paper uses `w(G) = |in(G)| + |out(G)|` and the threshold `n s`; its counting forgets that every
wire is counted twice in the total weight (see `heavy_count_counterexample`). The weight `+1` for
input gates is needed to bound the number of input gates a player owns.

## Main statements

* `exists_greedy_assign`: greedy load balancing (`-- CSLib candidate`).
* `Circuit.exists_assignment`: the assignment `I : C → V` (properties (1), (2) of the paper with
  the repaired constants).
-/

namespace Podc.CongestedCliquePower

open Finset

-- CSLib candidate (Foundations/Combinatorics): greedy load balancing.
/-- **Greedy load balancing.** Items of weight at most `M` and total weight at most `|V| M` can be
distributed among the bins `V` so that every bin has load at most `2M`. -/
theorem exists_greedy_assign {ι V : Type} [DecidableEq ι] [Fintype V] [DecidableEq V] [Nonempty V]
    (w : ι → ℕ) (M : ℕ) (S : Finset ι) (hw : ∀ i ∈ S, w i ≤ M)
    (hS : ∑ i ∈ S, w i ≤ Fintype.card V * M) :
    ∃ f : ι → V, ∀ v, ∑ i ∈ S with f i = v, w i ≤ 2 * M := by
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.arbitrary V, fun v => by simp⟩
  | insert a S ha ih =>
    rw [Finset.sum_insert ha] at hS
    obtain ⟨f, hf⟩ := ih (fun i hi => hw i (Finset.mem_insert_of_mem hi)) (by omega)
    obtain ⟨v, hv⟩ : ∃ v, ∑ i ∈ S with f i = v, w i ≤ M := by
      by_contra hcon
      simp only [not_exists, not_le] at hcon
      have h1 : ∑ _v : V, M < ∑ v : V, ∑ i ∈ S with f i = v, w i :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun v _ => hcon v)
      rw [Finset.sum_fiberwise] at h1
      simp only [sum_const, card_univ, smul_eq_mul] at h1
      omega
    refine ⟨Function.update f a v, fun v' => ?_⟩
    rw [Finset.filter_insert]
    have hS' : ∑ i ∈ S with Function.update f a v i = v', w i = ∑ i ∈ S with f i = v', w i := by
      apply Finset.sum_congr ?_ (fun _ _ => rfl)
      apply Finset.filter_congr
      intro i hi
      rw [Function.update_of_ne (by rintro rfl; exact ha hi)]
    split_ifs with h
    · rw [Finset.sum_insert (by simp [ha]), hS']
      simp only [Function.update_self] at h
      subst h
      have := hw a (Finset.mem_insert_self a S)
      omega
    · rw [hS']; exact hf v'

-- CSLib candidate (Foundations/Combinatorics): double counting.
/-- **Double counting.** If the sets `S b` are contained in `s` and every `a ∈ s` lies in at most
`c a` of them, then `∑ b, |S b| ≤ ∑ a ∈ s, c a`. -/
theorem sum_card_le_sum {α β : Type} [DecidableEq α] [Fintype β] (S : β → Finset α) (s : Finset α)
    (c : α → ℕ) (hS : ∀ b, S b ⊆ s) (hc : ∀ a ∈ s, #{b | a ∈ S b} ≤ c a) :
    ∑ b, #(S b) ≤ ∑ a ∈ s, c a := by
  classical
  have h1 : ∀ b, #(S b) = ∑ a ∈ s, if a ∈ S b then 1 else 0 := fun b => by
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hS b)]
  simp only [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  rw [← Finset.card_filter]
  exact hc a ha

namespace Circuit

open Classical

variable {X C : Type} [Fintype C] (Γ : Circuit X C)

/-- The in-degree `|in(G)|`. -/
noncomputable def indeg (G : C) : ℕ := #{g | Γ.wire g G}

/-- The out-degree `|out(G)|`. -/
noncomputable def outdeg (G : C) : ℕ := #{h | Γ.wire G h}

/-- The weight `w(G) = |in(G)| + |out(G)| + [G is an input gate]`. -/
noncomputable def weight (G : C) : ℕ :=
  Γ.indeg G + Γ.outdeg G + if (Γ.src G).isSome then 1 else 0

/-- `G` is heavy for the threshold `M`. -/
def Heavy (M : ℕ) (G : C) : Prop := M ≤ Γ.weight G

lemma numWires_eq : Γ.numWires = #{p : C × C | Γ.wire p.1 p.2} := by
  rw [numWires, Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma sum_indeg : ∑ G, Γ.indeg G = Γ.numWires := by
  rw [numWires_eq, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [indeg, Finset.card_filter]

lemma sum_outdeg : ∑ G, Γ.outdeg G = Γ.numWires := by
  rw [numWires_eq, Finset.card_filter, Fintype.sum_prod_type]
  simp only [outdeg, Finset.card_filter]

lemma card_inputs [Fintype X] : #{G | (Γ.src G).isSome} ≤ Fintype.card X := by
  rw [← Fintype.card_subtype]
  refine Fintype.card_le_of_injective (fun G => (Γ.src G.1).get G.2) fun G G' h => ?_
  have h' : (Γ.src G.1).get G.2 = (Γ.src G'.1).get G'.2 := h
  apply Subtype.ext
  exact Γ.src_inj _ _ ((Γ.src G'.1).get G'.2) (by rw [← h']; simp) (by simp)

lemma sum_weight [Fintype X] : ∑ G, Γ.weight G ≤ 2 * Γ.numWires + Fintype.card X := by
  have h := Γ.card_inputs
  rw [Finset.card_filter] at h
  simp only [weight, Finset.sum_add_distrib, sum_indeg, sum_outdeg]
  omega

/-- **Construction of `I`** (proof of Theorem 2 of [DKO14], repaired constants): with
`M = n (2s + 1)`, (1) distinct heavy gates go to distinct players and (2) the light gates of every
player have total weight at most `2M`. -/
theorem exists_assignment [Fintype X] {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (s : ℕ)
    (hX : Fintype.card X ≤ Fintype.card V ^ 2) (hN : Γ.numWires ≤ Fintype.card V ^ 2 * s) :
    ∃ I : C → V,
      (∀ G G', Γ.Heavy (Fintype.card V * (2 * s + 1)) G →
        Γ.Heavy (Fintype.card V * (2 * s + 1)) G' → I G = I G' → G = G') ∧
      ∀ v, ∑ G ∈ {G | ¬ Γ.Heavy (Fintype.card V * (2 * s + 1)) G ∧ I G = v}, Γ.weight G ≤
        2 * (Fintype.card V * (2 * s + 1)) := by
  set n := Fintype.card V with hn_def
  set M := n * (2 * s + 1) with hM
  have hn : 0 < n := Fintype.card_pos
  have hMpos : 0 < M := Nat.mul_pos hn (by omega)
  have htot : ∑ G, Γ.weight G ≤ n * M := by
    have h1 := Γ.sum_weight
    have h2 : n * M = 2 * (n ^ 2 * s) + n ^ 2 := by rw [hM]; ring
    omega
  -- heavy gates
  have hH : Fintype.card {G // Γ.Heavy M G} ≤ n := by
    rw [Fintype.card_subtype]
    have h1 : #{G | Γ.Heavy M G} • M ≤ ∑ G ∈ {G | Γ.Heavy M G}, Γ.weight G :=
      Finset.card_nsmul_le_sum _ _ _ fun G hG => (Finset.mem_filter.mp hG).2
    have h2 : ∑ G ∈ {G | Γ.Heavy M G}, Γ.weight G ≤ ∑ G, Γ.weight G :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [smul_eq_mul] at h1
    exact Nat.le_of_mul_le_mul_right (by omega : #{G | Γ.Heavy M G} * M ≤ n * M) hMpos
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hH
  -- light gates
  obtain ⟨f, hf⟩ := exists_greedy_assign (V := V) Γ.weight M {G | ¬ Γ.Heavy M G}
    (fun G hG => le_of_lt (not_le.mp (Finset.mem_filter.mp hG).2))
    (le_trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _)) htot)
  refine ⟨fun G => if h : Γ.Heavy M G then e ⟨G, h⟩ else f G, ?_, fun v => ?_⟩
  · intro G G' hG hG' h
    simp only [hG, hG', ↓reduceDIte] at h
    exact congrArg Subtype.val (e.injective h)
  · convert hf v using 2
    ext G
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa only [h1, ↓reduceDIte] using h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa only [h1, ↓reduceDIte] using h2⟩

end Circuit

end Podc.CongestedCliquePower
