import Papers.PODC2024.ListDefectiveColoring.Basic
import Papers.PODC2024.ListDefectiveColoring.NeighborhoodIndependence

/-!
# Section 4.1 of [FK24]: from list arbdefective to list defective colouring

Fuchs, Kuhn. *Simpler and More General Distributed Coloring Based on Simple List Defective
Coloring Algorithms* (PODC 2024; arXiv:2405.04648), cited as [FK24].

The algorithm of Section 4.1 solves a list defective colouring instance on a graph of
neighbourhood independence `θ` by `⌈log Δ⌉ + 1` calls of an arbitrary list *arbdefective*
colouring algorithm `A` (solving `P_A(S, C)`). Iterations are numbered `top, top - 1, …, 0`
(`top = ⌈log Δ⌉`), so a *larger* index means an *earlier* iteration. In iteration `i`:

* `aCount G it col v x i` (`a_v(x, i)`): neighbours of `v` coloured with `x` in iterations `> i`;
* `uncolCount G it v i` (`deg(v) - deg~(v, i)`): neighbours of `v` not coloured in iterations `> i`;
* `dI i = 2^i - 1` (`d_i`);
* `Cond` (eq. (12)): `d_i ≤ d'_v(x) - a_v(x, i)`;
* `InL` (`x ∈ L_{v,i}`): `x ∈ L_v`, eq. (12) holds in iteration `i` but in no earlier iteration;
* `InH` (`v ∈ H_i`, eq. (13)): `v` is uncoloured and
  `∑_{x ∈ L_{v,i}} (d_i + 1) > S · (deg(v) - deg~(v, i))`.

All nodes of `H_i` are coloured in iteration `i` by `A` with the lists `L_{v,i}` and the uniform
defect `d_i`. We do not fix `A`: a *run* (`IsRun`) is any assignment of iterations `it` and
colours `col` such that every node is coloured exactly in the iteration in which it lies in `H_i`,
with a colour of `L_{v,i}`, and the colouring of each `H_i` is `d_i`-arbdefective (this is exactly
the output specification of `P_A(S, C)` on `H_i`: the instance has slack `S` there, since the
`H_i`-degree of `v` is at most `deg(v) - deg~(v, i)`; see `Section41Exists.lean`). The round
complexity `(⌈log Δ⌉ + 1) · T_A(S, C)` is not modelled.

The defect function `d'` used to define the lists is a parameter of the model. The paper's
choice (eq. (10)) `d'_v(x) = ⌊(d_v(x) + 1) / (7θ)⌋ - 1` is negative when `d_v(x) + 1 < 7θ`, which
breaks the algorithm (see `Section41Counterexample.lean`); we use the corrected
`dPrime I θ v x = ⌊d_v(x) / (7θ)⌋` (`= ⌈(d_v(x) + 1)/(7θ)⌉ - 1`).

## Main results
* `lemma_4_2`: every node is coloured in some iteration `≤ top`;
* `lemma_4_3`, `lemma_4_3_sharp`: a node coloured with `x` has fewer than `max 1 (7θ · d'_v(x))`
  (in fact at most `4θ · d'_v(x)`) coloured neighbours of colour `x`;
* `theorem_1_4`, `theorem_1_4_paper_slack`: Theorem 1.4 (correctness part).
-/

open Finset SimpleGraph
open scoped Classical

namespace FK24

namespace Sec41

variable {V α : Type*} (G : SimpleGraph V) [G.LocallyFinite]

/-! ### The model -/

/-- `u` has been coloured before iteration `i`, i.e. in some iteration `j > i` (iterations run
from `top` down to `0`). -/
def ColoredBefore (it : V → Option ℕ) (u : V) (i : ℕ) : Prop := ∃ j, it u = some j ∧ i < j

/-- The paper's `a_v(x, i)`: the number of neighbours of `v` coloured with `x` before iteration
`i`. -/
noncomputable def aCount (it : V → Option ℕ) (col : V → α) (v : V) (x : α) (i : ℕ) : ℕ :=
  #{u ∈ G.neighborFinset v | ColoredBefore it u i ∧ col u = x}

/-- The paper's `deg(v) - deg~(v, i)`: the number of neighbours of `v` that are not coloured
before iteration `i`. -/
noncomputable def uncolCount (it : V → Option ℕ) (v : V) (i : ℕ) : ℕ :=
  #{u ∈ G.neighborFinset v | ¬ ColoredBefore it u i}

/-- The round specific defect `d_i = 2^i - 1` of [FK24, Section 4.1]. -/
def dI (i : ℕ) : ℕ := 2 ^ i - 1

/-- Equation (12) of [FK24]: `d'_v(x) - a_v(x, i) ≥ d_i`. -/
def Cond (d' : V → α → ℤ) (it : V → Option ℕ) (col : V → α) (v : V) (x : α) (i : ℕ) : Prop :=
  (dI i : ℤ) ≤ d' v x - aCount G it col v x i

/-- `x ∈ L_{v,i}`: `x ∈ L_v` satisfies eq. (12) in iteration `i` and in no earlier iteration
`j ∈ (i, top]`. -/
def InL (I : ListInstance V α) (d' : V → α → ℤ) (top : ℕ) (it : V → Option ℕ) (col : V → α)
    (v : V) (x : α) (i : ℕ) : Prop :=
  x ∈ I.L v ∧ Cond G d' it col v x i ∧ ∀ j, i < j → j ≤ top → ¬ Cond G d' it col v x j

/-- The list `L_{v,i}`. -/
noncomputable def listAt (I : ListInstance V α) (d' : V → α → ℤ) (top : ℕ) (it : V → Option ℕ)
    (col : V → α) (v : V) (i : ℕ) : Finset α :=
  {x ∈ I.L v | InL G I d' top it col v x i}

/-- `v ∈ H_i` (equation (13) of [FK24]): `v` is not coloured before iteration `i` and
`∑_{x ∈ L_{v,i}} (d_i + 1) > S · (deg(v) - deg~(v, i))`. -/
def InH (I : ListInstance V α) (d' : V → α → ℤ) (S : ℝ) (top : ℕ) (it : V → Option ℕ)
    (col : V → α) (v : V) (i : ℕ) : Prop :=
  ¬ ColoredBefore it v i ∧
    S * (uncolCount G it v i : ℝ) < ∑ _x ∈ listAt G I d' top it col v i, ((dI i : ℝ) + 1)

/-- A run of the algorithm of [FK24, Section 4.1] with modified defects `d'`, slack parameter `S`
of the arbdefective subroutine and iterations `top, …, 0`. `it v = some i` means that `v` is
coloured (with `col v`) in iteration `i`, `it v = none` that `v` is never coloured.

In iteration `i` the subroutine `A` (any algorithm solving `P_A(S, C)`) colours exactly the nodes
of `H_i`, with colours from the lists `L_{v,i}`, such that the colouring of `H_i` is
`d_i`-arbdefective. Running it takes `(top + 1) · T_A(S, C)` rounds. -/
structure IsRun (I : ListInstance V α) (d' : V → α → ℤ) (S : ℝ) (top : ℕ)
    (it : V → Option ℕ) (col : V → α) : Prop where
  /-- A node coloured in iteration `i` lies in `H_i` and gets a colour of `L_{v,i}`. -/
  colored_spec : ∀ v i, it v = some i →
    i ≤ top ∧ InH G I d' S top it col v i ∧ InL G I d' top it col v (col v) i
  /-- Every node of `H_i` is coloured in iteration `i`. -/
  colored_of_inH : ∀ v i, i ≤ top → InH G I d' S top it col v i → it v = some i
  /-- The colouring computed in iteration `i` is `d_i`-arbdefective on `H_i`. -/
  arbdefective : ∀ i, ∃ O : V → V → Prop,
    (∀ ⦃u w⦄, G.Adj u w → it u = some i → it w = some i → col u = col w → O u w ∨ O w u) ∧
    ∀ u, it u = some i →
      #{w ∈ G.neighborFinset u | O u w ∧ it w = some i ∧ col w = col u} ≤ dI i

/-! ### Elementary facts -/

theorem dI_add_one (i : ℕ) : dI i + 1 = 2 ^ i := Nat.sub_add_cancel Nat.one_le_two_pow

@[simp] theorem dI_zero : dI 0 = 0 := rfl

theorem dI_succ (i : ℕ) : dI (i + 1) = 2 * dI i + 1 := by
  have h1 := dI_add_one i
  have h2 := dI_add_one (i + 1)
  rw [pow_succ] at h2
  omega

/-- `∑_{j ≤ i} (2 d_j + 1) = 2^{i+2} - i - 3`. -/
theorem sum_range_two_dI_add_one (i : ℕ) :
    ∑ j ∈ range (i + 1), (2 * dI j + 1) + i + 3 = 2 ^ (i + 2) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sum_range_succ, dI_succ, pow_succ]
    have := dI_add_one i
    have h2 : 2 ^ (i + 2) = 4 * 2 ^ i := by ring
    omega

/-- For `i ≥ 1`: `∑_{j ≤ i} (2 d_j + 1) ≤ 4 d_i`. -/
theorem sum_range_two_dI_add_one_le {i : ℕ} (hi : 1 ≤ i) :
    ∑ j ∈ range (i + 1), (2 * dI j + 1) ≤ 4 * dI i := by
  have h := sum_range_two_dI_add_one i
  have h1 := dI_add_one i
  have h2 : 2 ^ (i + 2) = 4 * 2 ^ i := by ring
  omega

/-- The colours of distinct colour classes are disjoint, so the class sizes add up to at most the
size of the whole set. -/
theorem sum_card_filter_and_eq_le {β γ : Type*} (s : Finset β) (t : Finset γ) (P : β → Prop)
    (f : β → γ) : ∑ x ∈ t, #{u ∈ s | P u ∧ f u = x} ≤ #{u ∈ s | P u} := by
  rw [← card_biUnion]
  · refine card_le_card fun u hu => ?_
    simp only [mem_biUnion, mem_filter] at hu ⊢
    obtain ⟨_, _, hu, hP, _⟩ := hu
    exact ⟨hu, hP⟩
  · intro x _ y _ hxy
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro u hu hu'
    simp only [mem_filter] at hu hu'
    exact hxy (hu.2.2.symm.trans hu'.2.2)

variable {G}

theorem ColoredBefore.of_succ {it : V → Option ℕ} {u : V} {i : ℕ}
    (h : ColoredBefore it u (i + 1)) : ColoredBefore it u i := by
  obtain ⟨j, hj, hij⟩ := h
  exact ⟨j, hj, by omega⟩

theorem aCount_succ_le (it : V → Option ℕ) (col : V → α) (v : V) (x : α) (i : ℕ) :
    aCount G it col v x (i + 1) ≤ aCount G it col v x i := by
  unfold aCount
  refine card_le_card fun u hu => ?_
  simp only [mem_filter] at hu ⊢
  exact ⟨hu.1, hu.2.1.of_succ, hu.2.2⟩

theorem sum_aCount_le (it : V → Option ℕ) (col : V → α) (v : V) (t : Finset α) (i : ℕ) :
    ∑ x ∈ t, aCount G it col v x i ≤ #{u ∈ G.neighborFinset v | ColoredBefore it u i} :=
  sum_card_filter_and_eq_le _ _ _ _

theorem card_coloredBefore_add_uncolCount (it : V → Option ℕ) (v : V) (i : ℕ) :
    #{u ∈ G.neighborFinset v | ColoredBefore it u i} + uncolCount G it v i = G.degree v := by
  unfold uncolCount
  rw [card_filter_add_card_filter_not, card_neighborFinset_eq_degree]

/-! ### Lemma 4.2 -/

section Lemma42

variable {I : ListInstance V α} {d' : V → α → ℤ} {S : ℝ} {top : ℕ} {it : V → Option ℕ}
  {col : V → α}

/-- A colour of `L_v` that lies in no `L_{v,i}` (`i ≤ top`) satisfies eq. (12) in no iteration. -/
theorem not_cond_of_forall_not_inL {v : V} {x : α} (hx : x ∈ I.L v)
    (hL : ∀ i ≤ top, ¬ InL G I d' top it col v x i) {j : ℕ} (hj : j ≤ top) :
    ¬ Cond G d' it col v x j := by
  intro hc
  obtain ⟨T, hTmem⟩ : ∃ T : Finset ℕ, ∀ k, k ∈ T ↔ k ≤ top ∧ Cond G d' it col v x k :=
    ⟨(range (top + 1)).filter (fun k => Cond G d' it col v x k), fun k => by
      simp⟩
  have hne : T.Nonempty := ⟨j, (hTmem j).2 ⟨hj, hc⟩⟩
  have hm := (hTmem _).1 (T.max'_mem hne)
  refine hL (T.max' hne) hm.1 ⟨hx, hm.2, fun k hk hktop hck => ?_⟩
  have := T.le_max' k ((hTmem k).2 ⟨hktop, hck⟩)
  omega

/-- The key estimate of the proof of Lemma 4.2: for `x ∈ L_{v,i}`, `d'_v(x) - a_v(x, i) ≤ 2 d_i`. -/
theorem sub_aCount_le_two_dI (hd'top : ∀ v, ∀ x ∈ I.L v, d' v x ≤ 2 * dI top) {v : V} {x : α}
    {i : ℕ} (hi : i ≤ top) (hx : InL G I d' top it col v x i) :
    d' v x - aCount G it col v x i ≤ 2 * dI i := by
  rcases hi.lt_or_eq with hi | rfl
  · have h := hx.2.2 (i + 1) (by omega) (by omega)
    simp only [Cond, not_le, dI_succ] at h
    have := aCount_succ_le (G := G) it col v x i
    push_cast at h
    omega
  · have := hd'top v x hx.1
    omega

/-- If `v` is not in `H_i`, then `∑_{x ∈ L_{v,i}} (d'_v(x) + 1) ≤ 2 S deg(v)`. -/
theorem sum_listAt_le (hS : 1 ≤ S)
    (hd'top : ∀ v, ∀ x ∈ I.L v, d' v x ≤ 2 * dI top) {v : V} {i : ℕ} (hi : i ≤ top)
    (hnot : ¬ ColoredBefore it v i) (hH : ¬ InH G I d' S top it col v i) :
    ∑ x ∈ listAt G I d' top it col v i, ((d' v x : ℝ) + 1) ≤ 2 * S * G.degree v := by
  have hH' : ∑ _x ∈ listAt G I d' top it col v i, ((dI i : ℝ) + 1) ≤
      S * (uncolCount G it v i : ℝ) := by
    simp only [InH, not_and, not_lt] at hH
    exact hH hnot
  have hpt : ∀ x ∈ listAt G I d' top it col v i,
      (d' v x : ℝ) + 1 ≤ 2 * ((dI i : ℝ) + 1) + (aCount G it col v x i : ℝ) := by
    intro x hx
    simp only [listAt, mem_filter] at hx
    have h := sub_aCount_le_two_dI hd'top hi hx.2
    have h' : (d' v x : ℝ) - (aCount G it col v x i : ℝ) ≤ 2 * (dI i : ℝ) := by exact_mod_cast h
    linarith
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib (f := fun _ => 2 * ((dI i : ℝ) + 1)), ← mul_sum] at hsum
  have ha : ∑ x ∈ listAt G I d' top it col v i, (aCount G it col v x i : ℝ) ≤
      (#{u ∈ G.neighborFinset v | ColoredBefore it u i} : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast sum_aCount_le (G := G) it col v _ i
  have hdeg : (#{u ∈ G.neighborFinset v | ColoredBefore it u i} : ℝ) +
      (uncolCount G it v i : ℝ) = G.degree v := by
    exact_mod_cast card_coloredBefore_add_uncolCount (G := G) it v i
  have h0 : (0 : ℝ) ≤ #{u ∈ G.neighborFinset v | ColoredBefore it u i} := Nat.cast_nonneg _
  nlinarith

omit [G.LocallyFinite] in
theorem not_coloredBefore_of_uncolored (hrun' : ∀ v i, it v = some i → i ≤ top) {v : V}
    (hv : ¬ ∃ i ≤ top, it v = some i) (i : ℕ) : ¬ ColoredBefore it v i := by
  rintro ⟨j, hj, -⟩
  exact hv ⟨j, hrun' v j hj, hj⟩

/-- Lemma 4.2 of [FK24]: every node is coloured in some iteration `i ∈ {0, …, top}`.

Hypotheses: `S ≥ 1`; the modified defects satisfy `0 ≤ d'_v(x) ≤ 2 d_top` on `L_v` (the paper
derives the upper bound from `d_v(x) ≤ Δ ≤ 2^{⌈log Δ⌉}`), and the slack condition (11)
`∑_{x ∈ L_v} (d'_v(x) + 1) > 3 (top + 1) S deg(v)`. -/
theorem lemma_4_2 (hrun : IsRun G I d' S top it col) (hS : 1 ≤ S)
    (hd'0 : ∀ v, ∀ x ∈ I.L v, 0 ≤ d' v x) (hd'top : ∀ v, ∀ x ∈ I.L v, d' v x ≤ 2 * dI top)
    (hslack : ∀ v, 3 * (top + 1) * S * G.degree v < ∑ x ∈ I.L v, ((d' v x : ℝ) + 1))
    (v : V) : ∃ i ≤ top, it v = some i := by
  by_contra hv
  have hcb := not_coloredBefore_of_uncolored (fun v i h => (hrun.colored_spec v i h).1) hv
  have hH : ∀ i ≤ top, ¬ InH G I d' S top it col v i := fun i hi h =>
    hv ⟨i, hi, hrun.colored_of_inH v i hi h⟩
  set f : α → ℝ := fun x => (d' v x : ℝ) + 1 with hf
  have hf0 : ∀ x ∈ I.L v, 0 ≤ f x := fun x hx => by
    have := hd'0 v x hx
    simp only [f]
    have : (0 : ℝ) ≤ d' v x := by exact_mod_cast this
    linarith
  -- colours never considered
  set Lstar := {x ∈ I.L v | ∀ i ≤ top, ¬ InL G I d' top it col v x i} with hLstar
  have hstar : ∑ x ∈ Lstar, f x ≤ G.degree v := by
    have hpt : ∀ x ∈ Lstar, f x ≤ (aCount G it col v x 0 : ℝ) := by
      intro x hx
      simp only [Lstar, mem_filter] at hx
      have h := not_cond_of_forall_not_inL hx.1 hx.2 (Nat.zero_le top)
      simp only [Cond, dI_zero, Nat.cast_zero, sub_nonneg, not_le] at h
      simp only [f]
      have : d' v x + 1 ≤ (aCount G it col v x 0 : ℤ) := h
      exact_mod_cast this
    refine (sum_le_sum hpt).trans ?_
    rw [← Nat.cast_sum]
    have h1 := sum_aCount_le (G := G) it col v Lstar 0
    have h2 := card_coloredBefore_add_uncolCount (G := G) it v 0
    exact_mod_cast (h1.trans (by omega))
  -- colours considered in some iteration
  have hrest : ∑ x ∈ I.L v with ¬ (∀ i ≤ top, ¬ InL G I d' top it col v x i), f x ≤
      ∑ i ∈ range (top + 1), ∑ x ∈ listAt G I d' top it col v i, f x := by
    calc ∑ x ∈ I.L v with ¬ (∀ i ≤ top, ¬ InL G I d' top it col v x i), f x
        ≤ ∑ x ∈ I.L v with ¬ (∀ i ≤ top, ¬ InL G I d' top it col v x i),
            ∑ i ∈ range (top + 1), (if InL G I d' top it col v x i then f x else 0) := by
          refine sum_le_sum fun x hx => ?_
          simp only [mem_filter, not_forall, not_not] at hx
          obtain ⟨hxL, i, hi, hin⟩ := hx
          have := single_le_sum (f := fun i => if InL G I d' top it col v x i then f x else 0)
            (fun j _ => by split_ifs <;> simp [hf0 x hxL]) (mem_range.2 (Nat.lt_succ_of_le hi))
          simpa [hin] using this
      _ ≤ ∑ x ∈ I.L v,
            ∑ i ∈ range (top + 1), (if InL G I d' top it col v x i then f x else 0) := by
          refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x hx _ => ?_
          exact sum_nonneg fun j _ => by split_ifs <;> simp [hf0 x hx]
      _ = ∑ i ∈ range (top + 1), ∑ x ∈ listAt G I d' top it col v i, f x := by
          rw [sum_comm]
          refine sum_congr rfl fun i _ => ?_
          rw [listAt, sum_filter]
  have hiter : ∑ i ∈ range (top + 1), ∑ x ∈ listAt G I d' top it col v i, f x ≤
      ∑ _i ∈ range (top + 1), 2 * S * G.degree v := by
    refine sum_le_sum fun i hi => ?_
    exact sum_listAt_le hS hd'top (Nat.lt_succ_iff.1 (mem_range.1 hi)) (hcb i) (hH i
      (Nat.lt_succ_iff.1 (mem_range.1 hi)))
  rw [sum_const, card_range, nsmul_eq_mul] at hiter
  have htot := hslack v
  rw [← sum_filter_add_sum_filter_not (I.L v) (fun x => ∀ i ≤ top, ¬ InL G I d' top it col v x i)]
    at htot
  have hdeg0 : (0 : ℝ) ≤ G.degree v := Nat.cast_nonneg _
  have htop : (1 : ℝ) ≤ (top : ℝ) + 1 := by have : (0 : ℝ) ≤ top := Nat.cast_nonneg _; linarith
  have h1 : (1 : ℝ) ≤ ((top : ℝ) + 1) * S := by nlinarith
  have h2 : (G.degree v : ℝ) ≤ ((top : ℝ) + 1) * S * G.degree v := by nlinarith
  push_cast at hiter htot
  change 3 * ((top : ℝ) + 1) * S * G.degree v < ∑ x ∈ Lstar, f x +
    ∑ x ∈ I.L v with ¬ (∀ i ≤ top, ¬ InL G I d' top it col v x i), f x at htot
  nlinarith

end Lemma42

/-! ### Lemma 4.3 -/

section Lemma43

variable {I : ListInstance V α} {d' : V → α → ℤ} {S : ℝ} {top : ℕ} {it : V → Option ℕ}
  {col : V → α}

/-- Nodes coloured in the same iteration `j` with the same colour, inside `N(v)`, are few:
at most `(2 d_j + 1) θ` (Claim 4.1 applied to the colouring of `H_j`). -/
theorem card_iteration_color_le {θ : ℕ} (hθ : G.NeighborhoodIndepLE θ)
    (hrun : IsRun G I d' S top it col) (v : V) (x : α) (j : ℕ) :
    #{u ∈ G.neighborFinset v | it u = some j ∧ col u = x} ≤ (2 * dI j + 1) * θ := by
  obtain ⟨O, hO, hout⟩ := hrun.arbdefective j
  refine card_le_of_subset_neighborSet hθ (v := v) ?_ O (dI j) ?_ ?_
  · intro u hu
    simp only [coe_filter, Set.mem_ofPred_eq, mem_neighborFinset] at hu
    exact hu.1
  · intro u hu w hw huw
    simp only [mem_filter] at hu hw
    exact hO huw hu.2.1 hw.2.1 (hu.2.2.trans hw.2.2.symm)
  · intro u hu
    simp only [mem_filter] at hu
    refine le_trans (card_le_card ?_) (hout u hu.2.1)
    intro w hw
    simp only [mem_filter, mem_neighborFinset] at hw ⊢
    exact ⟨hw.2.1, hw.2.2, hw.1.2.1, hw.1.2.2.trans hu.2.2.symm⟩

/-- In the last iteration `0` (`d_0 = 0`) the colouring is proper: no neighbour of a node coloured
in iteration `0` gets the same colour in iteration `0`. -/
theorem card_iteration_zero_eq_zero (hrun : IsRun G I d' S top it col) {v : V}
    (hv : it v = some 0) : #{u ∈ G.neighborFinset v | it u = some 0 ∧ col u = col v} = 0 := by
  obtain ⟨O, hO, hout⟩ := hrun.arbdefective 0
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro u hu
  simp only [mem_filter, mem_neighborFinset] at hu
  rcases hO hu.1 hv hu.2.1 hu.2.2.symm with h | h
  · have := hout v hv
    rw [dI_zero, Nat.le_zero, card_eq_zero, eq_empty_iff_forall_notMem] at this
    exact this u (by simp [hu.1, h, hu.2.1, hu.2.2])
  · have := hout u hu.2.1
    rw [dI_zero, Nat.le_zero, card_eq_zero, eq_empty_iff_forall_notMem] at this
    exact this v (by simp [hu.1.symm, h, hv, hu.2.2])

/-- Lemma 4.3 of [FK24], sharp form: if `v` is coloured with `x = col v`, then the number `X_v` of
coloured neighbours of `v` with colour `x` satisfies `X_v ≤ 4 θ d'_v(x)`. -/
theorem lemma_4_3_sharp {θ : ℕ} (hθ : G.NeighborhoodIndepLE θ) (hθ1 : 1 ≤ θ)
    (hrun : IsRun G I d' S top it col) {v : V} {i : ℕ} (hv : it v = some i) :
    (#{u ∈ G.neighborFinset v | it u ≠ none ∧ col u = col v} : ℤ) ≤ 4 * θ * d' v (col v) := by
  set x := col v with hx
  have hcond : Cond G d' it col v x i := ((hrun.colored_spec v i hv).2.2).2.1
  simp only [Cond] at hcond
  set W : ℕ → Finset V := fun j => {u ∈ G.neighborFinset v | it u = some j ∧ col u = x}
  have hX : #{u ∈ G.neighborFinset v | it u ≠ none ∧ col u = x} ≤
      aCount G it col v x i + ∑ j ∈ range (i + 1), #(W j) := by
    refine le_trans (card_le_card (s := _)
      (t := {u ∈ G.neighborFinset v | ColoredBefore it u i ∧ col u = x} ∪
        (range (i + 1)).biUnion W) ?_) ((card_union_le _ _).trans (Nat.add_le_add_left
          card_biUnion_le _))
    intro u hu
    simp only [mem_filter] at hu
    obtain ⟨hu, hit, hcol⟩ := hu
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hit
    rcases lt_or_ge i k with hik | hik
    · exact mem_union_left _ (by simp only [mem_filter]; exact ⟨hu, ⟨k, hk, hik⟩, hcol⟩)
    · refine mem_union_right _ (mem_biUnion.2 ⟨k, mem_range.2 (by omega), ?_⟩)
      simp only [W, mem_filter]
      exact ⟨hu, hk, hcol⟩
  have hW : ∀ j, #(W j) ≤ (2 * dI j + 1) * θ := card_iteration_color_le hθ hrun v x
  have ha0 : (0 : ℤ) ≤ aCount G it col v x i := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have h0 : #(W 0) = 0 := card_iteration_zero_eq_zero hrun hv
    simp only [zero_add, range_one, sum_singleton, h0, add_zero] at hX
    simp only [dI_zero, Nat.cast_zero] at hcond
    have : (#{u ∈ G.neighborFinset v | it u ≠ none ∧ col u = x} : ℤ) ≤ aCount G it col v x 0 := by
      exact_mod_cast hX
    have hθ' : (1 : ℤ) ≤ θ := by exact_mod_cast hθ1
    nlinarith
  · have hsum : ∑ j ∈ range (i + 1), #(W j) ≤ 4 * dI i * θ := by
      calc ∑ j ∈ range (i + 1), #(W j) ≤ ∑ j ∈ range (i + 1), (2 * dI j + 1) * θ :=
            sum_le_sum fun j _ => hW j
        _ = (∑ j ∈ range (i + 1), (2 * dI j + 1)) * θ := by rw [sum_mul]
        _ ≤ 4 * dI i * θ := Nat.mul_le_mul_right _ (sum_range_two_dI_add_one_le hi)
    have h1 : (#{u ∈ G.neighborFinset v | it u ≠ none ∧ col u = x} : ℤ) ≤
        aCount G it col v x i + 4 * dI i * θ := by exact_mod_cast hX.trans (by omega)
    have hθ' : (1 : ℤ) ≤ θ := by exact_mod_cast hθ1
    nlinarith

/-- Lemma 4.3 of [FK24]: at the end of the algorithm, every node `v` coloured with `x = col v`
has `X_v < max {1, 7 θ d'_v(x)}` coloured neighbours of colour `x`. -/
theorem lemma_4_3 {θ : ℕ} (hθ : G.NeighborhoodIndepLE θ) (hθ1 : 1 ≤ θ)
    (hrun : IsRun G I d' S top it col) {v : V} {i : ℕ} (hv : it v = some i) :
    (#{u ∈ G.neighborFinset v | it u ≠ none ∧ col u = col v} : ℤ) <
      max 1 (7 * θ * d' v (col v)) := by
  have h := lemma_4_3_sharp hθ hθ1 hrun hv
  have hθ' : (1 : ℤ) ≤ θ := by exact_mod_cast hθ1
  rcases le_or_gt (d' v (col v)) 0 with hd | hd
  · have : 4 * (θ : ℤ) * d' v (col v) ≤ 0 := by nlinarith
    exact lt_of_le_of_lt (h.trans this) (lt_of_lt_of_le one_pos (le_max_left _ _))
  · have : 4 * (θ : ℤ) * d' v (col v) < 7 * θ * d' v (col v) := by nlinarith
    exact lt_of_lt_of_le (h.trans_lt this) (le_max_right _ _)

end Lemma43

/-! ### Theorem 1.4 -/

/-- The corrected modified defect `d'_v(x) = ⌊d_v(x) / (7θ)⌋ = ⌈(d_v(x) + 1) / (7θ)⌉ - 1`
(the paper's eq. (10) uses `⌊(d_v(x) + 1) / (7θ)⌋ - 1`, which can be negative). -/
def dPrime (I : ListInstance V α) (θ : ℕ) (v : V) (x : α) : ℤ := ((I.d v x / (7 * θ) : ℕ) : ℤ)

/-- `⌈log₂ Δ⌉ + 1 ≤ 2 log₂ Δ` for integers `Δ ≥ 2`: the slack `42 θ log Δ · S` of Theorem 1.4
implies the slack `21 θ (⌈log Δ⌉ + 1) S` of eq. (9). -/
theorem clog_add_one_le_two_logb {Δ : ℕ} (hΔ : 2 ≤ Δ) :
    ((Nat.clog 2 Δ : ℝ) + 1) ≤ 2 * Real.logb 2 Δ := by
  set c := Nat.clog 2 Δ with hc
  have hc1 : 1 ≤ c := Nat.clog_pos (by norm_num) (by omega)
  have hlt : 2 ^ (c - 1) < Δ := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := Δ) (by omega)
    simpa [Nat.pred_eq_sub_one] using this
  -- `2^{c+1} ≤ Δ²`
  have key : 2 ^ (c + 1) ≤ Δ ^ 2 := by
    obtain ⟨t, ht⟩ : ∃ t, t = 2 ^ (c - 1) := ⟨_, rfl⟩
    have h2c : 2 ^ (c + 1) = 4 * t := by
      rw [ht, show c + 1 = (c - 1) + 2 by omega, pow_add]
      ring
    have ht1 : 1 ≤ t := ht ▸ Nat.one_le_two_pow
    have : t + 1 ≤ Δ := by omega
    nlinarith
  have hΔpos : (0 : ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hlog : 2 * Real.logb 2 (Δ : ℝ) = Real.logb 2 ((Δ : ℝ) ^ 2) := by
    rw [Real.logb_pow]; norm_num
  rw [hlog]
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  have : ((2 : ℝ) ^ ((c : ℝ) + 1)) = ((2 ^ (c + 1) : ℕ) : ℝ) := by
    rw [show ((c : ℝ) + 1) = ((c + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    push_cast; ring
  rw [this]
  exact_mod_cast key

variable {I : ListInstance V α} {S : ℝ} {it : V → Option ℕ} {col : V → α}

/-- Theorem 1.4 of [FK24] (correctness; corrected form). Let `G` have neighbourhood independence
at most `θ ≥ 1`, let `S ≥ 1`, `Δ ≥ 2`, assume every defect satisfies `d_v(x) ≤ Δ` (the paper's
w.l.o.g. assumption, `Δ` = maximum degree) and the instance has slack
`21 θ (⌈log Δ⌉ + 1) S` (eq. (9), with the factor `deg(v)` that the paper omits). Then every run of
the algorithm of Section 4.1 with the defects `d' = ⌊d / (7θ)⌋` and `⌈log Δ⌉ + 1` iterations
colours every node, and the result is a list defective colouring. The algorithm uses
`(⌈log Δ⌉ + 1) · T_A(S, C)` rounds (not modelled). -/
theorem theorem_1_4 {θ Δ : ℕ} (hθ : G.NeighborhoodIndepLE θ) (hθ1 : 1 ≤ θ) (hS : 1 ≤ S)
    (hΔ : 2 ≤ Δ) (hdΔ : ∀ v, ∀ x ∈ I.L v, I.d v x ≤ Δ)
    (hslack : HasSlack G I (21 * θ * (Nat.clog 2 Δ + 1) * S))
    (hrun : IsRun G I (dPrime I θ) S (Nat.clog 2 Δ) it col) :
    (∀ v, ∃ i ≤ Nat.clog 2 Δ, it v = some i) ∧ IsListDefective G I col := by
  set top := Nat.clog 2 Δ with htop
  have htop1 : 1 ≤ top := Nat.clog_pos (by norm_num) (by omega)
  have hθpos : 0 < 7 * θ := by omega
  -- all nodes are coloured (Lemma 4.2)
  have hall : ∀ v, ∃ i ≤ top, it v = some i := by
    refine lemma_4_2 hrun hS (fun v x _ => Nat.cast_nonneg _) (fun v x hx => ?_) (fun v => ?_)
    · have h1 : I.d v x / (7 * θ) ≤ I.d v x := Nat.div_le_self _ _
      have h2 : Δ ≤ 2 ^ top := Nat.le_pow_clog (by norm_num) Δ
      have h3 := dI_add_one top
      have h4 : 2 ≤ 2 ^ top := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ top := Nat.pow_le_pow_right (by norm_num) htop1
      have : I.d v x / (7 * θ) ≤ 2 * dI top := by have := hdΔ v x hx; omega
      simp only [dPrime]
      exact_mod_cast this
    · have hs := hslack v
      simp only [ListInstance.weight] at hs
      push_cast at hs
      have hpt : ∀ x ∈ I.L v, ((I.d v x : ℝ) + 1) ≤ 7 * θ * ((dPrime I θ v x : ℝ) + 1) := by
        intro x _
        have := Nat.lt_div_mul_add (a := I.d v x) hθpos
        have h : I.d v x + 1 ≤ 7 * θ * (I.d v x / (7 * θ) + 1) := by nlinarith
        simp only [dPrime, Int.cast_natCast]
        exact_mod_cast h
      have hsum := sum_le_sum hpt
      rw [← mul_sum] at hsum
      have hθr : (0 : ℝ) < 7 * θ := by exact_mod_cast hθpos
      by_contra hcon
      push Not at hcon
      have : 7 * θ * (3 * ((top : ℝ) + 1) * S * G.degree v) ≥
          7 * θ * ∑ x ∈ I.L v, ((dPrime I θ v x : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hcon hθr.le
      nlinarith
  refine ⟨hall, fun v => ?_⟩
  obtain ⟨i, -, hv⟩ := hall v
  refine ⟨((hrun.colored_spec v i hv).2.2).1, ?_⟩
  have h := lemma_4_3_sharp hθ hθ1 hrun hv
  have hfil : {u ∈ G.neighborFinset v | col u = col v} =
      {u ∈ G.neighborFinset v | it u ≠ none ∧ col u = col v} := by
    refine filter_congr fun u _ => ?_
    obtain ⟨j, -, hj⟩ := hall u
    simp [hj]
  rw [hfil]
  have h2 : 4 * θ * (I.d v (col v) / (7 * θ)) ≤ I.d v (col v) := by
    have := Nat.div_mul_le_self (I.d v (col v)) (7 * θ)
    nlinarith
  simp only [dPrime] at h
  have : (#{u ∈ G.neighborFinset v | it u ≠ none ∧ col u = col v}) ≤
      4 * θ * (I.d v (col v) / (7 * θ)) := by exact_mod_cast h
  exact this.trans h2

/-- Theorem 1.4 of [FK24] with the paper's slack `42 · θ · log Δ · S` (instances of the class
`P_D(42 θ log Δ · S, C)`, `log = log₂`), under the paper's w.l.o.g. assumption `d_v(x) ≤ Δ`, with
`Δ ≥ 2`: every run of the algorithm of Section 4.1 (corrected defects `d' = ⌊d/(7θ)⌋`,
`⌈log Δ⌉ + 1` iterations) colours every node with a list defective colouring. -/
theorem theorem_1_4_paper_slack {θ Δ : ℕ} (hθ : G.NeighborhoodIndepLE θ) (hθ1 : 1 ≤ θ)
    (hS : 1 ≤ S) (hΔ : 2 ≤ Δ) (hdΔ : ∀ v, ∀ x ∈ I.L v, I.d v x ≤ Δ)
    (hslack : HasSlack G I (42 * θ * Real.logb 2 Δ * S))
    (hrun : IsRun G I (dPrime I θ) S (Nat.clog 2 Δ) it col) :
    (∀ v, ∃ i ≤ Nat.clog 2 Δ, it v = some i) ∧ IsListDefective G I col := by
  refine theorem_1_4 hθ hθ1 hS hΔ hdΔ (fun v => lt_of_le_of_lt ?_ (hslack v)) hrun
  have h := clog_add_one_le_two_logb hΔ
  have hθ0 : (0 : ℝ) ≤ θ := Nat.cast_nonneg _
  have hdeg : (0 : ℝ) ≤ G.degree v := Nat.cast_nonneg _
  have hS0 : (0 : ℝ) ≤ S := by linarith
  have : 21 * (θ : ℝ) * ((Nat.clog 2 Δ : ℝ) + 1) * S ≤ 42 * θ * Real.logb 2 Δ * S := by
    have := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 21 * θ * S by positivity)
    nlinarith
  exact mul_le_mul_of_nonneg_right this hdeg

end Sec41

end FK24
