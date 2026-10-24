import Papers.PODC2010.ArbdefectiveColoring.LocalTools

/-!
# H-partitions (Lemma 2.3, from Barenboim–Elkin PODC'08)

The H-partition algorithm: in every round, every still active vertex with at most `A` active
neighbours becomes inactive; `H_i` is the set of vertices removed in round `i + 1` (we index the
sets from `0`). We prove:

* `active_card_mul_le`: if `G` has an orientation with out-degree `≤ a` (e.g. arboricity `≤ a`,
  CSLib's `ArboricityLE.hasOutDegLE`), then `|S_{i+1}| · (A + 1) ≤ 2a · |S_i|` for the sets `S_i` of
  active vertices, so after `L` rounds no vertex is active once `n · (2a)^L < (A + 1)^L`
  (`not_active_of_lt`); for `A = ⌊(2+ε)a⌋` this is `L = O(log n / ε)` (see `Asymptotics.lean`).
* `hPartition` (**Lemma 2.3**): the H-index `hIdx G A L v ∈ [0, L)` (the number of rounds `v`
  survives) defines a partition `H_0, …, H_{L-1}` of degree at most `A`: every vertex has at most
  `A` neighbours of H-index at least its own. It is computed in `L` rounds (`hIdx_isLocal`).
-/

open Finset Cslib.Local

namespace Podc.ArbdefectiveColoring

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

-- CSLib candidate: `Cslib/Foundations/Combinatorics/SimpleGraph/HPartition.lean` (H-partition / peeling)
/-- `Active G A i v`: `v` is still active after `i` rounds of the H-partition algorithm. -/
def Active (G : SimpleGraph V) (A : ℕ) : ℕ → V → Prop
  | 0 => fun _ => True
  | i + 1 => fun v => Active G A i v ∧ A < #{u | G.Adj v u ∧ Active G A i u}

/-- The H-index of `v`: the number of rounds among the first `L` that `v` survives. -/
noncomputable def hIdx (G : SimpleGraph V) (A L : ℕ) (v : V) : ℕ :=
  #{i ∈ range L | Active G A (i + 1) v}

variable {G : SimpleGraph V} {A : ℕ}

@[simp] lemma active_zero (v : V) : Active G A 0 v := trivial

lemma active_succ {i : ℕ} {v : V} :
    Active G A (i + 1) v ↔ Active G A i v ∧ A < #{u | G.Adj v u ∧ Active G A i u} := Iff.rfl

lemma Active.anti {i j : ℕ} {v : V} (hij : i ≤ j) (h : Active G A j v) : Active G A i v := by
  induction hij with
  | refl => exact h
  | step _ ih => exact ih h.1

/-- Once the peeling is finished after `L` rounds, `v` is active after `i` rounds iff
`i ≤ hIdx v`. -/
lemma active_iff_le_hIdx {L : ℕ} (hL : ∀ v, ¬ Active G A L v) (i : ℕ) (v : V) :
    Active G A i v ↔ i ≤ hIdx G A L v := by
  have hex : ∃ k, ¬ Active G A (k + 1) v := by
    rcases L with _ | L
    · exact absurd trivial (hL v)
    · exact ⟨L, hL v⟩
  set k := Nat.find hex
  have hk : ∀ j, Active G A (j + 1) v ↔ j < k := by
    intro j
    constructor
    · intro hj
      by_contra hjk
      exact Nat.find_spec hex (hj.anti (by omega))
    · intro hj
      by_contra hn
      exact Nat.find_min hex hj hn
  have hkL : k < L := by
    by_contra hkL
    rcases L with _ | L
    · exact hL v trivial
    · exact hL v ((hk L).2 (by omega))
  have hidx : hIdx G A L v = k := by
    rw [hIdx, show (range L).filter (fun i => Active G A (i + 1) v) = range k from ?_]
    · simp
    ext j
    simp only [mem_filter, mem_range, hk]
    omega
  rw [hidx]
  rcases i with _ | i
  · exact ⟨fun _ => Nat.zero_le _, fun _ => trivial⟩
  · rw [hk]; omega

/-- **Locality of the H-partition algorithm**: whether `v` is active after `i` rounds depends only
on the radius-`i` ball around `v`. -/
lemma active_congr {G' : SimpleGraph V} (i : ℕ) :
    ∀ v, GAgree G G' v i → (Active G A i v ↔ Active G' A i v) := by
  induction i with
  | zero => simp
  | succ i ih =>
    intro v hv
    rw [active_succ, active_succ, ih v (hv.mono_radius (by omega))]
    refine and_congr_right' ?_
    have : filter (fun u => G.Adj v u ∧ Active G A i u) univ =
        filter (fun u => G'.Adj v u ∧ Active G' A i u) univ := by
      ext u
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        have hu : G.edist v u ≤ 1 := by rw [SimpleGraph.edist_eq_one_iff_adj.2 h1]
        exact ⟨(hv.adj_iff (by omega) u).1 h1, (ih u (hv.mono hu (by omega))).1 h2⟩
      · rintro ⟨h1, h2⟩
        have h1' := (hv.adj_iff (by omega) u).2 h1
        have hu : G.edist v u ≤ 1 := by rw [SimpleGraph.edist_eq_one_iff_adj.2 h1']
        exact ⟨h1', (ih u (hv.mono hu (by omega))).2 h2⟩
    rw [this]

/-- The H-partition algorithm runs in `L` rounds. -/
theorem hIdx_isLocal (A L : ℕ) : IsLocalG (V := V) L (fun G v => hIdx G A L v) := by
  intro G _ G' _ v hv
  simp only [hIdx]
  congr 1
  exact filter_congr fun i hi => active_congr (i + 1) v
    (hv.1.mono_radius (by simp only [mem_range] at hi; omega))

/-! ### The number of rounds -/

/-- Double counting: in a graph with an orientation of out-degree `≤ a`, the degrees inside any
vertex set `S` sum to at most `2a|S|`. -/
lemma sum_card_adj_le {a : ℕ} (o : G.OutOrientation a) (S : Finset V) :
    ∑ v ∈ S, #{u ∈ S | G.Adj v u} ≤ 2 * a * #S := by
  have h1 : ∀ v ∈ S, #{u ∈ S | G.Adj v u} ≤ #{u ∈ S | u ∈ o.out v} + #{u ∈ S | v ∈ o.out u} := by
    intro v _
    refine (card_le_card fun u hu => ?_).trans (card_union_le _ _)
    simp only [mem_filter, mem_union] at hu ⊢
    rcases o.mem_or_mem hu.2 with h | h
    · exact Or.inl ⟨hu.1, h⟩
    · exact Or.inr ⟨hu.1, h⟩
  have h2 : ∑ v ∈ S, #{u ∈ S | v ∈ o.out u} = ∑ u ∈ S, #{v ∈ S | v ∈ o.out u} :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun v u => v ∈ o.out u)
  have h3 : ∀ v, #{u ∈ S | u ∈ o.out v} ≤ a :=
    fun v => (card_le_card (fun u hu => (mem_filter.1 hu).2)).trans (o.card_out_le v)
  calc ∑ v ∈ S, #{u ∈ S | G.Adj v u}
      ≤ ∑ v ∈ S, (#{u ∈ S | u ∈ o.out v} + #{u ∈ S | v ∈ o.out u}) := sum_le_sum h1
    _ = ∑ v ∈ S, #{u ∈ S | u ∈ o.out v} + ∑ u ∈ S, #{v ∈ S | v ∈ o.out u} := by
        rw [sum_add_distrib, h2]
    _ ≤ ∑ _v ∈ S, a + ∑ _u ∈ S, a := add_le_add (sum_le_sum fun v _ => h3 v)
        (sum_le_sum fun u _ => h3 u)
    _ = 2 * a * #S := by simp; ring

/-- One round of the H-partition algorithm: `|S_{i+1}| · (A+1) ≤ 2a · |S_i|`. -/
lemma active_card_mul_le {a : ℕ} (hG : G.HasOutDegLE a) (i : ℕ) :
    #{v | Active G A (i + 1) v} * (A + 1) ≤ 2 * a * #{v | Active G A i v} := by
  obtain ⟨o⟩ := hG
  set S : Finset V := {v | Active G A i v}
  set S' : Finset V := {v | Active G A (i + 1) v}
  have hS' : S' ⊆ S := fun v hv => by
    simp only [S, S', mem_filter, mem_univ, true_and] at hv ⊢; exact hv.1
  have hdeg : ∀ v ∈ S', A + 1 ≤ #{u ∈ S | G.Adj v u} := by
    intro v hv
    simp only [S', mem_filter, mem_univ, true_and, active_succ] at hv
    calc A + 1 ≤ #{u | G.Adj v u ∧ Active G A i u} := hv.2
      _ = #{u ∈ S | G.Adj v u} := by congr 1; ext u; simp [S, and_comm]
  calc #S' * (A + 1) = ∑ _v ∈ S', (A + 1) := by simp
    _ ≤ ∑ v ∈ S', #{u ∈ S | G.Adj v u} := sum_le_sum hdeg
    _ ≤ ∑ v ∈ S, #{u ∈ S | G.Adj v u} := sum_le_sum_of_subset hS'
    _ ≤ 2 * a * #S := sum_card_adj_le o S

/-- After `i` rounds: `|S_i| · (A+1)^i ≤ (2a)^i · n`. -/
lemma active_card_mul_pow_le {a : ℕ} (hG : G.HasOutDegLE a) (i : ℕ) :
    #{v | Active G A i v} * (A + 1) ^ i ≤ (2 * a) ^ i * Fintype.card V := by
  induction i with
  | zero => simp [card_univ]
  | succ i ih =>
    calc #{v | Active G A (i + 1) v} * (A + 1) ^ (i + 1)
        = (#{v | Active G A (i + 1) v} * (A + 1)) * (A + 1) ^ i := by ring
      _ ≤ (2 * a * #{v | Active G A i v}) * (A + 1) ^ i :=
          Nat.mul_le_mul_right _ (active_card_mul_le hG i)
      _ = 2 * a * (#{v | Active G A i v} * (A + 1) ^ i) := by ring
      _ ≤ 2 * a * ((2 * a) ^ i * Fintype.card V) := Nat.mul_le_mul_left _ ih
      _ = (2 * a) ^ (i + 1) * Fintype.card V := by ring

/-- After `L` rounds with `n · (2a)^L < (A+1)^L`, no vertex is active. -/
lemma not_active_of_lt {a L : ℕ} (hG : G.HasOutDegLE a)
    (hL : Fintype.card V * (2 * a) ^ L < (A + 1) ^ L) (v : V) : ¬ Active G A L v := by
  intro hv
  have h1 := active_card_mul_pow_le (A := A) hG L
  have h2 : 1 ≤ #{v | Active G A L v} := card_pos.2 ⟨v, by simp [hv]⟩
  have : (A + 1) ^ L ≤ #{v | Active G A L v} * (A + 1) ^ L := Nat.le_mul_of_pos_left _ h2
  rw [mul_comm (Fintype.card V)] at hL
  omega

/-- **Lemma 2.3** (H-partition). Let `G` have an orientation with out-degree `≤ a` (e.g. arboricity
`≤ a`), and let `n · (2a)^L < (A+1)^L`. After `L` rounds the H-partition algorithm has assigned to
every vertex an H-index `hIdx v < L`, and every vertex has at most `A` neighbours whose H-index is
at least its own (the H-partition has degree `≤ A`). The algorithm runs in `L` rounds
(`hIdx_isLocal`). -/
theorem hPartition {a L : ℕ} (hG : G.HasOutDegLE a)
    (hL : Fintype.card V * (2 * a) ^ L < (A + 1) ^ L) :
    (∀ v, hIdx G A L v < L) ∧ ∀ v, #{u | G.Adj v u ∧ hIdx G A L v ≤ hIdx G A L u} ≤ A := by
  have hna := not_active_of_lt (A := A) hG hL
  have hiff := active_iff_le_hIdx hna
  refine ⟨fun v => ?_, fun v => ?_⟩
  · by_contra h
    exact hna v ((hiff L v).2 (by omega))
  · set i := hIdx G A L v
    have hi : Active G A i v := (hiff i v).2 le_rfl
    have hi1 : ¬ Active G A (i + 1) v := fun h => by have := (hiff (i + 1) v).1 h; omega
    rw [active_succ] at hi1
    push Not at hi1
    refine le_trans (le_of_eq ?_) (hi1 hi)
    congr 1
    ext u
    simp only [mem_filter, mem_univ, true_and, hiff i u]

end Podc.ArbdefectiveColoring
