/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Computability/Distributed/RateAllocation/MaxMinFair.lean
import Mathlib

/-!
# Max-min fair rate allocation in networks with fixed routing

A *routed network* (`Network F L`) has a finite set of flows `F` and a finite set of links `L`;
flow `f` traverses the set of links `path f` (its route is fixed) and link `ℓ` has capacity
`cap ℓ`. An *allocation* is a rate vector `a : F → ℝ`; it is *feasible* if all rates are
non-negative and the total rate over the flows traversing each link is at most the capacity of
the link.

The *sorted vector* `a↑` (`sortedRates a`) is the list of rates sorted from lowest to highest; an
allocation is *max-min fair* (`IsMaxMinFair`) if it is feasible and its sorted vector is maximum in
lexicographic order (Mathlib's `LinearOrder (List ℝ)`) over the sorted vectors of all feasible
allocations (Bertsekas–Gallager, *Data Networks*; Radunović–Le Boudec 2007).

## Main statements

* `sortedRates_lt_of_forall`: the combinatorial *leximin criterion*: if `a ≠ b` and every flow
  that gains in `b` is compensated by a flow of no larger `a`-rate that loses in `b`, then
  `b↑ < a↑`;
* `Network.isMaxMinFair_iff_hasBottlenecks` (the *bottleneck property*): a feasible allocation is
  max-min fair iff every flow has a bottleneck link (a saturated link on its path on which its rate
  is maximum);
* `Network.IsMaxMinFair.eq`: the max-min fair allocation is unique;
  `Network.sortedRates_lt_of_hasBottlenecks`: it is strictly better than every other feasible
  allocation;
* `Network.throughput_le_mul_of_isMaxMinFair` (*price of max-min fairness*): if every path has at
  most `k` links, then the throughput of every feasible allocation is at most `k` times the
  throughput of the max-min fair allocation.
-/

namespace Cslib.RateAllocation

open Finset

section Leximin

variable {F : Type*} [Fintype F]

/-- The sorted vector `a↑` of an allocation: its rates sorted from lowest to highest. -/
noncomputable def sortedRates (a : F → ℝ) : List ℝ := (univ.val.map a).sort

/-- The throughput `t(a)` of an allocation: the total rate over all flows. -/
def throughput (a : F → ℝ) : ℝ := ∑ f, a f

theorem sortedRates_coe (a : F → ℝ) : ((sortedRates a : List ℝ) : Multiset ℝ) = univ.val.map a :=
  Multiset.sort_eq _ _

/-- The throughput is the sum of the sorted vector. -/
theorem sum_sortedRates (a : F → ℝ) : (sortedRates a).sum = throughput a := by
  rw [← Multiset.sum_coe, sortedRates_coe]; rfl

/-- Allocations with the same sorted vector have the same throughput. -/
theorem throughput_eq_of_sortedRates_eq {a b : F → ℝ} (h : sortedRates a = sortedRates b) :
    throughput a = throughput b := by
  rw [← sum_sortedRates, h, sum_sortedRates]

/-- A sorted multiset of reals splits at a threshold `m` into the part below `m`, the copies of
`m`, and the part above `m`. -/
theorem sort_eq_split (s : Multiset ℝ) (m : ℝ) :
    s.sort = (s.filter (· < m)).sort ++ List.replicate (s.count m) m ++
      (s.filter (m < ·)).sort := by
  have hmem : ∀ {t : Multiset ℝ} {x : ℝ}, x ∈ t.sort → x ∈ t := fun h => (Multiset.mem_sort _).1 h
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Multiset.pairwise_sort _ _)
  · rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨Multiset.pairwise_sort _ _, List.pairwise_replicate.2 (Or.inr le_rfl), ?_⟩,
      Multiset.pairwise_sort _ _, ?_⟩
    · intro x hx y hy
      have := (Multiset.mem_filter.1 (hmem hx)).2
      rw [(List.mem_replicate.1 hy).2]; exact this.le
    · intro x hx y hy
      have hy' := (Multiset.mem_filter.1 (hmem hy)).2
      rcases List.mem_append.1 hx with hx | hx
      · have := (Multiset.mem_filter.1 (hmem hx)).2; linarith
      · rw [(List.mem_replicate.1 hx).2]; exact hy'.le
  · rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, ← Multiset.coe_add, Multiset.sort_eq,
      Multiset.sort_eq, Multiset.sort_eq, Multiset.coe_replicate, ← Multiset.filter_eq']
    conv_lhs => rw [← Multiset.filter_add_not (· < m) s]
    rw [add_assoc]
    congr 1
    rw [← Multiset.filter_add_not (· = m) (s.filter (fun x => ¬ x < m)), Multiset.filter_filter,
      Multiset.filter_filter]
    congr 1
    · exact Multiset.filter_congr fun x _ => by constructor <;> intro h <;> [exact h.1; exact
        ⟨h, by rw [h]; exact lt_irrefl m⟩]
    · exact Multiset.filter_congr fun x _ => by
        constructor
        · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne (not_lt.1 h2) (Ne.symm h1)
        · intro h; exact ⟨ne_of_gt h, not_lt.2 h.le⟩

/-- Lexicographic comparison after a common prefix. -/
theorem append_cons_lt_append_cons {P l₁ l₂ : List ℝ} {x y : ℝ} (h : x < y) :
    P ++ x :: l₁ < P ++ y :: l₂ :=
  List.Lex.append_left _ (List.Lex.rel h) P

/-- **Leximin criterion.** Let `a ≠ b` be allocations such that every flow whose rate is larger in
`b` than in `a` is compensated by a flow `g` of no larger `a`-rate whose rate is smaller in `b`.
Then `b↑ < a↑` in lexicographic order. -/
theorem sortedRates_lt_of_forall {a b : F → ℝ} (hne : a ≠ b)
    (h : ∀ f, a f < b f → ∃ g, a g ≤ a f ∧ b g < a g) : sortedRates b < sortedRates a := by
  classical
  set D := univ.filter (fun f => a f ≠ b f) with hD
  have hDne : D.Nonempty := by
    by_contra h0
    apply hne
    funext f
    by_contra hf
    exact h0 ⟨f, by simp [hD, hf]⟩
  set m := D.inf' hDne (fun f => min (a f) (b f)) with hm
  have hmle : ∀ f ∈ D, m ≤ a f ∧ m ≤ b f := fun f hf =>
    le_min_iff.1 (Finset.inf'_le _ hf)
  -- no flow of `D` has `a`-rate `m`
  have h1 : ∀ f ∈ D, m < a f := by
    intro f hf
    refine lt_of_le_of_ne (hmle f hf).1 fun heq => ?_
    have hfD : a f ≠ b f := (Finset.mem_filter.1 hf).2
    have hab : a f < b f := lt_of_le_of_ne (heq ▸ (hmle f hf).2) hfD
    obtain ⟨g, hg1, hg2⟩ := h f hab
    have hgD : g ∈ D := by simp [hD, hg2.ne']
    have := (hmle g hgD).2
    linarith
  obtain ⟨f0, hf0D, hf0⟩ := Finset.exists_mem_eq_inf' hDne (fun f => min (a f) (b f))
  have hbf0 : b f0 = m := by
    have hmf : m = min (a f0) (b f0) := hf0
    have := h1 f0 hf0D
    rcases min_choice (a f0) (b f0) with h' | h'
    · rw [h'] at hmf; linarith
    · rw [h'] at hmf; exact hmf.symm
  have hout : ∀ f, f ∉ D → a f = b f := fun f hf => by
    by_contra h'; exact hf (by simp [hD, h'])
  set A := univ.val.map a
  set B := univ.val.map b
  -- the parts below `m` coincide
  have hlow : A.filter (· < m) = B.filter (· < m) := by
    simp only [A, B, Multiset.filter_map]
    have hc : Multiset.filter ((· < m) ∘ a) univ.val = Multiset.filter ((· < m) ∘ b) univ.val :=
      Multiset.filter_congr fun f _ => by
        by_cases hf : f ∈ D
        · simp only [Function.comp]
          constructor
          · intro h'; exact absurd h' (not_lt.2 (h1 f hf).le)
          · intro h'; exact absurd h' (not_lt.2 (hmle f hf).2)
        · simp [Function.comp, hout f hf]
    rw [hc]
    refine Multiset.map_congr rfl fun f hf => ?_
    have hf' : b f < m := (Multiset.mem_filter.1 hf).2
    by_cases hfD : f ∈ D
    · exact absurd hf' (not_lt.2 (hmle f hfD).2)
    · exact hout f hfD
  -- strictly more copies of `m` in `b`
  have hcount : A.count m < B.count m := by
    simp only [A, B, Multiset.count_map]
    have e : ∀ c : F → ℝ, Multiset.filter (fun x => m = c x) univ.val =
        (univ.filter (fun x => m = c x)).val := fun c => rfl
    rw [e a, e b, Finset.card_val, Finset.card_val]
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_of_subset (fun f hf => ?_) |>.2 ⟨f0, ?_, ?_⟩
    · have hf' : m = a f := (Finset.mem_filter.1 hf).2
      have hfD : f ∉ D := fun hfD => (h1 f hfD).ne hf'
      simpa [hout f hfD] using hf'
    · simp [hbf0]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (h1 f0 hf0D).ne
  -- `a` has a rate above `m`
  have hhigh : (A.filter (m < ·)).sort ≠ [] := by
    intro h0
    have : a f0 ∈ (A.filter (m < ·)).sort :=
      (Multiset.mem_sort _).2 (Multiset.mem_filter.2 ⟨Multiset.mem_map_of_mem _ (mem_univ _),
        h1 f0 hf0D⟩)
    rw [h0] at this; simp at this
  obtain ⟨x, t, hxt⟩ := List.exists_cons_of_ne_nil hhigh
  have hx : m < x := by
    have : x ∈ (A.filter (m < ·)).sort := by rw [hxt]; simp
    exact (Multiset.mem_filter.1 ((Multiset.mem_sort _).1 this)).2
  obtain ⟨d, hd⟩ : ∃ d, B.count m = A.count m + (d + 1) := ⟨B.count m - A.count m - 1, by omega⟩
  unfold sortedRates
  rw [sort_eq_split A m, sort_eq_split B m, hxt, hd, ← hlow, List.replicate_add,
    List.replicate_succ, List.append_assoc, List.append_assoc, List.append_assoc,
    List.cons_append, ← List.append_assoc, ← List.append_assoc]
  exact append_cons_lt_append_cons hx

/-- Non-strict version of the leximin criterion. -/
theorem sortedRates_le_of_forall {a b : F → ℝ}
    (h : ∀ f, a f < b f → ∃ g, a g ≤ a f ∧ b g < a g) : sortedRates b ≤ sortedRates a := by
  by_cases hab : a = b
  · rw [hab]
  · exact (sortedRates_lt_of_forall hab h).le

end Leximin

/-- A network with fixed routing: flow `f` traverses the links `path f`, and link `ℓ` has
capacity `cap ℓ`. -/
structure Network (F L : Type*) where
  /-- The set of links traversed by each flow. -/
  path : F → Finset L
  /-- The capacity of each link. -/
  cap : L → ℝ

namespace Network

variable {F L : Type*} [Fintype F] [DecidableEq L] (N : Network F L)

/-- The total rate over all flows traversing link `ℓ`. -/
def load (a : F → ℝ) (ℓ : L) : ℝ := ∑ f ∈ univ.filter (fun f => ℓ ∈ N.path f), a f

/-- An allocation is feasible if all rates are non-negative and no link capacity is exceeded. -/
def Feasible (a : F → ℝ) : Prop := (∀ f, 0 ≤ a f) ∧ ∀ ℓ, N.load a ℓ ≤ N.cap ℓ

/-- Max-min fair allocation (Bertsekas–Gallager): feasible, and its sorted vector is maximum in
lexicographic order over the sorted vectors of all feasible allocations. -/
def IsMaxMinFair (a : F → ℝ) : Prop :=
  N.Feasible a ∧ ∀ b, N.Feasible b → sortedRates b ≤ sortedRates a

/-- Maximum-throughput allocation: feasible, of maximum throughput among feasible allocations. -/
def IsMaxThroughput (a : F → ℝ) : Prop :=
  N.Feasible a ∧ ∀ b, N.Feasible b → throughput b ≤ throughput a

/-- Link `ℓ` is a bottleneck for flow `f` under `a`: `f` traverses `ℓ`, `ℓ` is saturated, and the
rate of `f` is maximum over the flows traversing `ℓ`. -/
def IsBottleneck (a : F → ℝ) (f : F) (ℓ : L) : Prop :=
  ℓ ∈ N.path f ∧ N.load a ℓ = N.cap ℓ ∧ ∀ g, ℓ ∈ N.path g → a g ≤ a f

/-- Every flow has a bottleneck link. -/
def HasBottlenecks (a : F → ℝ) : Prop := ∀ f, ∃ ℓ, N.IsBottleneck a f ℓ

variable {N}

theorem load_eq_sum_ite (a : F → ℝ) (ℓ : L) :
    N.load a ℓ = ∑ f, if ℓ ∈ N.path f then a f else 0 := by
  rw [load, Finset.sum_filter]

theorem load_nonneg {a : F → ℝ} (ha : ∀ f, 0 ≤ a f) (ℓ : L) : 0 ≤ N.load a ℓ :=
  Finset.sum_nonneg fun f _ => ha f

theorem load_mono {a b : F → ℝ} (h : ∀ f, a f ≤ b f) (ℓ : L) : N.load a ℓ ≤ N.load b ℓ :=
  Finset.sum_le_sum fun f _ => h f

/-- The flows `e x` (`e` injective) contribute at most the load of a link. -/
theorem sum_le_load_of_injective {ι : Type*} [Fintype ι] {b : F → ℝ} (hb : ∀ f, 0 ≤ b f)
    (e : ι → F) (he : Function.Injective e) (ℓ : L) :
    ∑ x, (if ℓ ∈ N.path (e x) then b (e x) else 0) ≤ N.load b ℓ := by
  classical
  rw [load_eq_sum_ite, ← Finset.sum_image (g := e) (f := fun f => if ℓ ∈ N.path f then b f else 0)
    (fun x _ y _ h => he h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun f _ _ => by split_ifs <;> simp [hb f]

/-- If every flow traversing `ℓ` is of the form `e x` (`e` injective), the load of `ℓ` is the sum
over these flows. -/
theorem load_eq_of_injective {ι : Type*} [Fintype ι] (b : F → ℝ) (e : ι → F)
    (he : Function.Injective e) (ℓ : L) (hall : ∀ f, ℓ ∈ N.path f → ∃ x, e x = f) :
    N.load b ℓ = ∑ x, (if ℓ ∈ N.path (e x) then b (e x) else 0) := by
  classical
  rw [load_eq_sum_ite, ← Finset.sum_image (g := e) (f := fun f => if ℓ ∈ N.path f then b f else 0)
    (fun x _ y _ h => he h)]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun f _ hf => ?_
  rw [if_neg]
  intro hℓ
  obtain ⟨x, rfl⟩ := hall f hℓ
  exact hf (Finset.mem_image_of_mem _ (Finset.mem_univ x))

/-- **Bottleneck property, sufficiency** (strict form): an allocation with the bottleneck property
is strictly better (in the sorted-vector lexicographic order) than every other feasible
allocation. -/
theorem sortedRates_lt_of_hasBottlenecks {a b : F → ℝ} (ha : N.HasBottlenecks a)
    (hb : N.Feasible b) (hne : b ≠ a) : sortedRates b < sortedRates a := by
  classical
  refine sortedRates_lt_of_forall (Ne.symm hne) fun f hf => ?_
  obtain ⟨ℓ, hℓf, hsat, hmax⟩ := ha f
  -- on the bottleneck link the total `b`-rate is at most the total `a`-rate
  have hle : N.load b ℓ ≤ N.load a ℓ := hsat ▸ hb.2 ℓ
  by_contra hcon
  push Not at hcon
  have : N.load a ℓ < N.load b ℓ := by
    unfold load
    apply Finset.sum_lt_sum
    · intro g hg
      have hg' : ℓ ∈ N.path g := (Finset.mem_filter.1 hg).2
      by_contra hlt
      push Not at hlt
      exact absurd (hcon g (hmax g hg')) (not_le.2 hlt)
    · exact ⟨f, by simp [hℓf], hf⟩
  linarith

/-- **Lemma (bottleneck property, sufficiency).** A feasible allocation in which every flow has a
bottleneck link is max-min fair. -/
theorem isMaxMinFair_of_hasBottlenecks {a : F → ℝ} (hf : N.Feasible a) (ha : N.HasBottlenecks a) :
    N.IsMaxMinFair a :=
  ⟨hf, fun b hb => by
    by_cases h : b = a
    · rw [h]
    · exact (sortedRates_lt_of_hasBottlenecks ha hb h).le⟩

/-- A positive lower bound for finitely many positive numbers. -/
theorem _root_.Finset.exists_pos_le_of_pos {ι : Type*} (s : Finset ι) (φ : ι → ℝ)
    (h : ∀ i ∈ s, 0 < φ i) : ∃ δ > 0, ∀ i ∈ s, δ ≤ φ i := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · exact ⟨1, one_pos, by simp [hs]⟩
  · obtain ⟨i, hi, hi'⟩ := Finset.exists_mem_eq_inf' hs φ
    exact ⟨s.inf' hs φ, hi' ▸ h i hi, fun j hj => Finset.inf'_le _ hj⟩

/-- **Lemma (bottleneck property, necessity).** In a max-min fair allocation every flow has a
bottleneck link. -/
theorem IsMaxMinFair.hasBottlenecks {a : F → ℝ} (ha : N.IsMaxMinFair a) : N.HasBottlenecks a := by
  classical
  intro f
  by_contra hno
  push Not at hno
  set P := N.path f
  set Sat := P.filter (fun ℓ => N.load a ℓ = N.cap ℓ)
  have hG : ∀ ℓ ∈ Sat, ∃ g, ℓ ∈ N.path g ∧ a f < a g := by
    intro ℓ hℓ
    obtain ⟨hℓP, hsat⟩ := Finset.mem_filter.1 hℓ
    by_contra hc
    push Not at hc
    exact hno ℓ ⟨hℓP, hsat, hc⟩
  have : Nonempty F := ⟨f⟩
  choose! G hG using hG
  have hpos : ∀ ℓ ∈ P, 0 < (if N.load a ℓ = N.cap ℓ then a (G ℓ) - a f
      else N.cap ℓ - N.load a ℓ) := by
    intro ℓ hℓ
    split_ifs with hs
    · have := (hG ℓ (Finset.mem_filter.2 ⟨hℓ, hs⟩)).2; linarith
    · have := ha.1.2 ℓ; exact sub_pos.2 (lt_of_le_of_ne this hs)
  obtain ⟨δ, hδ, hδle⟩ := Finset.exists_pos_le_of_pos P _ hpos
  set ε := δ / (P.card + 1) with hε
  have hε0 : 0 < ε := div_pos hδ (by positivity)
  have hεδ : ε * (P.card + 1) = δ := by rw [hε]; field_simp
  set k : F → ℕ := fun g => (Sat.filter (fun ℓ => G ℓ = g)).card
  set b : F → ℝ := fun g => a g + (if g = f then ε else 0) - ε * k g
  have hkf : k f = 0 := by
    simp only [k, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ℓ hℓ hGf
    have := (hG ℓ hℓ).2; rw [hGf] at this; exact lt_irrefl _ this
  have hkle : ∀ g, (k g : ℝ) ≤ P.card := fun g => by
    exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)
  have hbf : b f = a f + ε := by simp [b, hkf]
  -- a flow that loses rate keeps a rate of at least `b f`
  have hlose : ∀ g, 0 < k g → b f ≤ b g := by
    intro g hg
    obtain ⟨ℓ, hℓ⟩ := Finset.card_pos.1 hg
    obtain ⟨hℓS, hGg⟩ := Finset.mem_filter.1 hℓ
    have hgf : g ≠ f := by rintro rfl; omega
    have h1 : δ ≤ a g - a f := by
      have := hδle ℓ (Finset.mem_filter.1 hℓS).1
      rw [ite_eq_left (Finset.mem_filter.1 hℓS).2, hGg] at this; exact this
    have h2 := hkle g
    simp only [hbf, b, ite_eq_right hgf]
    nlinarith
  have hbfeas : N.Feasible b := by
    refine ⟨fun g => ?_, fun ℓ => ?_⟩
    · by_cases hg : 0 < k g
      · have := hlose g hg; have := ha.1.1 f; linarith
      · have hk0 : k g = 0 := by omega
        have := ha.1.1 g
        simp only [b, hk0, Nat.cast_zero, mul_zero, sub_zero]
        split_ifs <;> linarith
    · have hload : N.load b ℓ = N.load a ℓ + (if ℓ ∈ P then ε else 0) -
          ε * ∑ g ∈ univ.filter (fun g => ℓ ∈ N.path g), (k g : ℝ) := by
        simp only [load, b, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 2
        rw [Finset.sum_ite_eq']
        simp [P]
      have hcap := ha.1.2 ℓ
      by_cases hℓP : ℓ ∈ P
      · by_cases hs : N.load a ℓ = N.cap ℓ
        · have hℓS : ℓ ∈ Sat := Finset.mem_filter.2 ⟨hℓP, hs⟩
          have h1 : (1 : ℝ) ≤ ∑ g ∈ univ.filter (fun g => ℓ ∈ N.path g), (k g : ℝ) := by
            have hmem : G ℓ ∈ univ.filter (fun g => ℓ ∈ N.path g) := by
              simp [(hG ℓ hℓS).1]
            have hk1 : (1 : ℝ) ≤ k (G ℓ) := by
              have : 0 < k (G ℓ) := Finset.card_pos.2 ⟨ℓ, Finset.mem_filter.2 ⟨hℓS, rfl⟩⟩
              exact_mod_cast this
            exact hk1.trans (Finset.single_le_sum (f := fun g => (k g : ℝ))
              (fun g _ => Nat.cast_nonneg _) hmem)
          rw [hload, ite_eq_left hℓP]
          nlinarith
        · have h1 := hδle ℓ hℓP
          rw [ite_eq_right hs] at h1
          have h2 : 0 ≤ ∑ g ∈ univ.filter (fun g => ℓ ∈ N.path g), (k g : ℝ) :=
            Finset.sum_nonneg fun g _ => Nat.cast_nonneg _
          have h3 : ε ≤ δ := by nlinarith
          rw [hload, ite_eq_left hℓP]
          nlinarith
      · have h2 : 0 ≤ ∑ g ∈ univ.filter (fun g => ℓ ∈ N.path g), (k g : ℝ) :=
          Finset.sum_nonneg fun g _ => Nat.cast_nonneg _
        rw [hload, ite_eq_right hℓP]
        nlinarith
  have hlt : sortedRates a < sortedRates b := by
    refine sortedRates_lt_of_forall (fun h => ?_) fun g hg => ⟨f, ?_, ?_⟩
    · have := congrFun h f; rw [hbf] at this; linarith
    · by_cases hk : 0 < k g
      · exact hlose g hk
      · have hk0 : k g = 0 := by omega
        exfalso
        simp only [b, hk0, Nat.cast_zero, mul_zero, sub_zero] at hg
        split_ifs at hg <;> linarith
    · rw [hbf]; linarith
  exact absurd (ha.2 b hbfeas) (not_le.2 hlt)

/-- **Lemma 2.2 of Ferreira–Atre–Sherry–Sobrinho (PODC 2024), after Bertsekas–Gallager.**
A feasible allocation is max-min fair if and only if every flow has a bottleneck link. -/
theorem isMaxMinFair_iff_hasBottlenecks {a : F → ℝ} :
    N.IsMaxMinFair a ↔ N.Feasible a ∧ N.HasBottlenecks a :=
  ⟨fun h => ⟨h.1, h.hasBottlenecks⟩, fun h => isMaxMinFair_of_hasBottlenecks h.1 h.2⟩

/-- The max-min fair allocation is unique. -/
theorem IsMaxMinFair.eq {a b : F → ℝ} (ha : N.IsMaxMinFair a) (hb : N.IsMaxMinFair b) :
    a = b := by
  by_contra hne
  have h1 := sortedRates_lt_of_hasBottlenecks ha.hasBottlenecks hb.1 (Ne.symm hne)
  exact absurd (hb.2 a ha.1) (not_le.2 h1)

/-- A feasible allocation that is not the max-min fair one has a strictly smaller sorted
vector. -/
theorem IsMaxMinFair.sortedRates_lt {a b : F → ℝ} (ha : N.IsMaxMinFair a) (hb : N.Feasible b)
    (hne : b ≠ a) : sortedRates b < sortedRates a :=
  sortedRates_lt_of_hasBottlenecks ha.hasBottlenecks hb hne

/-- **Price of max-min fairness.** If every path has at most `k` links, the throughput of every
feasible allocation is at most `k` times the throughput of the max-min fair allocation. -/
theorem throughput_le_mul_of_isMaxMinFair [Fintype L] {a b : F → ℝ} (ha : N.IsMaxMinFair a)
    (hb : N.Feasible b) (k : ℕ) (hk : ∀ f, (N.path f).card ≤ k) :
    throughput b ≤ k * throughput a := by
  classical
  set Sat := univ.filter (fun ℓ => N.load a ℓ = N.cap ℓ)
  have hbn := ha.hasBottlenecks
  -- every flow traverses a saturated link
  have h1 : throughput b ≤ ∑ f, ((Sat.filter (fun ℓ => ℓ ∈ N.path f)).card : ℝ) * b f := by
    unfold throughput
    refine Finset.sum_le_sum fun f _ => ?_
    obtain ⟨ℓ, hℓf, hsat, -⟩ := hbn f
    have : (1 : ℝ) ≤ (Sat.filter (fun ℓ => ℓ ∈ N.path f)).card := by
      exact_mod_cast Finset.card_pos.2 ⟨ℓ, by simp [Sat, hsat, hℓf]⟩
    nlinarith [hb.1 f]
  have h2 : ∑ f, ((Sat.filter (fun ℓ => ℓ ∈ N.path f)).card : ℝ) * b f =
      ∑ ℓ ∈ Sat, N.load b ℓ := by
    simp only [load_eq_sum_ite]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have h3 : ∑ ℓ ∈ Sat, N.load b ℓ ≤ ∑ ℓ ∈ Sat, N.load a ℓ :=
    Finset.sum_le_sum fun ℓ hℓ => (Finset.mem_filter.1 hℓ).2 ▸ hb.2 ℓ
  have h4 : ∑ ℓ ∈ Sat, N.load a ℓ ≤ ∑ ℓ, N.load a ℓ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun ℓ _ _ => load_nonneg ha.1.1 ℓ
  have h5 : ∑ ℓ, N.load a ℓ = ∑ f, ((N.path f).card : ℝ) * a f := by
    simp only [load_eq_sum_ite]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h6 : ∑ f, ((N.path f).card : ℝ) * a f ≤ k * throughput a := by
    unfold throughput
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    have : ((N.path f).card : ℝ) ≤ k := by exact_mod_cast hk f
    nlinarith [ha.1.1 f]
  linarith

end Network

end Cslib.RateAllocation
