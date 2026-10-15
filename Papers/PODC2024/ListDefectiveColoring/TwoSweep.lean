import Papers.PODC2024.ListDefectiveColoring.SubsetSelection

/-!
# The Two-Sweep algorithm (Algorithm 1 of [FK24]): sequential specification

Fix out-neighbourhoods `out : V → Finset V`, an initial colouring `c : V → ℕ` that is proper along
out-edges (`u ∈ out v → c u ≠ c v`), an OLDC instance `I` and an integer `p ≥ 1`.

* `N_<(v)` / `N_>(v)`: out-neighbours with smaller / larger initial colour.
* Phase I (ascending initial colours): `v` picks `S_v`, a best `min(p, |L_v|)`-subset of `L_v` for
  the score `d_v(x) − k_v(x)`, where `k_v(x) = #{u ∈ N_<(v) | x ∈ S_u}` (`kCount`).
* Phase II (descending initial colours): `v` picks `x_v ∈ S_v` with
  `k_v(x_v) + r_v(x_v) ≤ d_v(x_v)`, where `r_v(x) = #{u ∈ N_>(v) | x_u = x}` (`rCount`), eq. (5).

`IsPhaseI` / `IsPhaseII` state these specifications for the final outputs `S` and `col`; the
distributed implementation in `Distributed.lean` produces outputs satisfying them.

## Main results

* `IsPhaseI.eq3_eq4`: every `S_v` chosen in Phase I satisfies (3) and (4) (Lemma 3.1).
* `exists_phaseII_color` (Lemma 3.2, first part): a colour satisfying (5) exists.
* `IsPhaseII.isOLDC` (Lemma 3.2, second part): the result is an oriented list defective
  colouring.
-/

open Finset

namespace FK24

variable {V α : Type*} [DecidableEq α]

/-- `k_v(x)`: the number of out-neighbours `u ∈ N_<(v)` (smaller initial colour) with `x ∈ S_u`. -/
def kCount (out : V → Finset V) (c : V → ℕ) (S : V → Finset α) (v : V) (x : α) : ℕ :=
  #{u ∈ out v | c u < c v ∧ x ∈ S u}

/-- `r_v(x)`: the number of out-neighbours `u ∈ N_>(v)` (larger initial colour) with final colour
`x`. -/
def rCount (out : V → Finset V) (c : V → ℕ) (col : V → α) (v : V) (x : α) : ℕ :=
  #{u ∈ out v | c v < c u ∧ col u = x}

/-- Phase I of Algorithm 1: every `S_v` is a best `min(p, |L_v|)`-subset of `L_v` for the score
`d_v(x) − k_v(x)` (the paper sorts `L_v` by this score and takes the first `p` colours). -/
def IsPhaseI (I : ListInstance V α) (out : V → Finset V) (c : V → ℕ) (p : ℕ)
    (S : V → Finset α) : Prop :=
  ∀ v, IsBestSubset (I.L v) (min p (I.L v).card)
    (fun x => (I.d v x : ℤ) - kCount out c S v x) (S v)

/-- Phase II of Algorithm 1: every node picks `x_v ∈ S_v` with
`k_v(x_v) + r_v(x_v) ≤ d_v(x_v)` (eq. (5)). -/
def IsPhaseII (I : ListInstance V α) (out : V → Finset V) (c : V → ℕ) (S : V → Finset α)
    (col : V → α) : Prop :=
  ∀ v, col v ∈ S v ∧ kCount out c S v (col v) + rCount out c col v (col v) ≤ I.d v (col v)

/-- `∑_{x ∈ L} #{u ∈ A | x ∈ S u} ≤ ∑_{u ∈ A} |S u|`. -/
theorem sum_card_filter_mem_le (L : Finset α) (A : Finset V) (S : V → Finset α) :
    ∑ x ∈ L, #{u ∈ A | x ∈ S u} ≤ ∑ u ∈ A, (S u).card := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [← Finset.card_filter]
  exact Finset.card_le_card fun x hx => (Finset.mem_filter.1 hx).2

/-- `∑_{x ∈ L} #{u ∈ A | f u = x} ≤ |A|` (fibres of `f` over distinct colours are disjoint). -/
theorem sum_card_filter_eq_le (L : Finset α) (A : Finset V) (f : V → α) :
    ∑ x ∈ L, #{u ∈ A | f u = x} ≤ A.card := by
  have := sum_card_filter_mem_le L A (fun u => {f u})
  simp only [Finset.mem_singleton, Finset.card_singleton, Finset.sum_const, smul_eq_mul,
    mul_one] at this
  simpa [eq_comm] using this

/-- The out-degree splits into `|N_<(v)| + |N_>(v)|` if `c` is proper along out-edges. -/
theorem card_lt_add_card_gt {out : V → Finset V} {c : V → ℕ}
    (hc : ∀ v, ∀ u ∈ out v, c u ≠ c v) (v : V) :
    #{u ∈ out v | c u < c v} + #{u ∈ out v | c v < c u} = (out v).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext u
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro hu
      rcases lt_or_gt_of_ne (hc v u hu) with h | h
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr ⟨hu, h⟩
  · rw [Finset.disjoint_filter]
    intro u _ h1 h2
    omega

/-- **Lemma 3.1** of [FK24], for the sets produced by Phase I: if the slack condition (2) holds at
`v` (in the natural-number form `max(p², |L_v|) · β_v < p · ∑_{x ∈ L_v} (d_v(x)+1)`), then
`|S_v| ≤ p` (3) and `|N_>(v)| + ∑_{x ∈ S_v} k_v(x) < ∑_{x ∈ S_v} (d_v(x) + 1)` (4). -/
theorem IsPhaseI.eq3_eq4 {I : ListInstance V α} {out : V → Finset V} {c : V → ℕ} {p : ℕ}
    {S : V → Finset α} (hS : IsPhaseI I out c p S) (hp : 1 ≤ p)
    (hc : ∀ v, ∀ u ∈ out v, c u ≠ c v) (v : V)
    (hslack : max (p ^ 2) (I.L v).card * beta out v < p * I.weight v) :
    (S v).card ≤ p ∧
      #{u ∈ out v | c v < c u} + ∑ x ∈ S v, kCount out c S v x <
        ∑ x ∈ S v, (I.d v x + 1) := by
  refine (hS v).lemma_3_1 (nlt := #{u ∈ out v | c u < c v}) hp ?_ ?_ hslack
  · rw [card_lt_add_card_gt hc]; exact card_out_le_beta out v
  · -- ∑_x k_v(x) ≤ ∑_{u ∈ N_<} |S_u| ≤ |N_<| p
    have h1 := sum_card_filter_mem_le (I.L v) {u ∈ out v | c u < c v} S
    have h2 : ∑ u ∈ out v with c u < c v, (S u).card ≤ #{u ∈ out v | c u < c v} * p := by
      rw [← smul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun u _ => ?_
      have := (Finset.mem_powersetCard.1 (hS u).1).2
      rw [this]; exact min_le_left _ _
    refine le_trans (le_of_eq ?_) (h1.trans h2)
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold kCount
    rw [Finset.filter_filter]

/-- **Lemma 3.2** of [FK24], first part: if `S_v` satisfies (4) then, whatever colours the nodes
in `N_>(v)` have chosen, some `x ∈ S_v` satisfies (5): `k_v(x) + r_v(x) ≤ d_v(x)`. -/
theorem exists_phaseII_color {I : ListInstance V α} {out : V → Finset V} {c : V → ℕ}
    {S : V → Finset α} (col : V → α) (v : V)
    (h4 : #{u ∈ out v | c v < c u} + ∑ x ∈ S v, kCount out c S v x <
        ∑ x ∈ S v, (I.d v x + 1)) :
    ∃ x ∈ S v, kCount out c S v x + rCount out c col v x ≤ I.d v x := by
  by_contra hne
  push Not at hne
  have hr : ∑ x ∈ S v, rCount out c col v x ≤ #{u ∈ out v | c v < c u} := by
    have := sum_card_filter_eq_le (S v) {u ∈ out v | c v < c u} col
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold rCount; rw [Finset.filter_filter]
  have hsum : ∑ x ∈ S v, (I.d v x + 1) ≤
      ∑ x ∈ S v, (kCount out c S v x + rCount out c col v x) :=
    Finset.sum_le_sum fun x hx => hne x hx
  have hsum2 : ∑ x ∈ S v, (kCount out c S v x + rCount out c col v x) =
      ∑ x ∈ S v, kCount out c S v x + ∑ x ∈ S v, rCount out c col v x :=
    Finset.sum_add_distrib
  omega

/-- **Lemma 3.2** of [FK24], second part: after Phase II every node `v` has at most
`d_v(x_v)` out-neighbours of its colour `x_v`, i.e. Algorithm 1 computes an oriented list
defective colouring (the correctness part of Lemma 3.3). -/
theorem IsPhaseII.isOLDC {I : ListInstance V α} {out : V → Finset V} {c : V → ℕ} {p : ℕ}
    {S : V → Finset α} {col : V → α} (hI : IsPhaseI I out c p S) (hII : IsPhaseII I out c S col)
    (hc : ∀ v, ∀ u ∈ out v, c u ≠ c v) : IsOLDC I out col := by
  classical
  intro v
  obtain ⟨hmem, hle⟩ := hII v
  have hSL : S v ⊆ I.L v := (Finset.mem_powersetCard.1 (hI v).1).1
  refine ⟨hSL hmem, le_trans ?_ hle⟩
  -- split the out-neighbours of colour `col v` by initial colour
  have hsplit : {u ∈ out v | col u = col v} ⊆
      {u ∈ out v | c u < c v ∧ col v ∈ S u} ∪ {u ∈ out v | c v < c u ∧ col u = col v} := by
    intro u hu
    simp only [Finset.mem_filter] at hu
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases lt_or_gt_of_ne (hc v u hu.1) with h | h
    · left; refine ⟨hu.1, h, ?_⟩
      rw [← hu.2]; exact (hII u).1
    · right; exact ⟨hu.1, h, hu.2⟩
  exact (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)

end FK24
