import Mathlib

/-!
# Fence insertions for straight-line programs: the abstract setting

A straight-line program has `n` operations `0, …, n-1` (the paper numbers them `1, …, n`); gap `k`
is the place right after operation `k`. A set `ord` of *required orders* `x = (i, j)`, `i < j`, must
be preserved by fences placed in gaps `k` with `i ≤ k < j`.

* `IsIns ord need f` — a *multi-type* fence insertion `f : Fin n → Finset κ` (`f k` = the fences put
  in gap `k`) for fence instructions `κ`; order `x` needs a fence of type `c` for every
  `c ∈ need x` (`need x = none`: the order is provided by the memory model for free).
  `size f = ∑ₖ |f k|`.
* `IsIns1 ord F` — a *single-type* fence insertion `F ⊆ {gaps}` (Definition 2.2).
* `IsOptIns`, `IsOptIns1` — minimum-size insertions (`OptFI`); they exist (`exists_isOptIns`,
  `exists_isOptIns1`).

## Main statements

The abstract form of **Lemma 2.1** ("independence of fence types"): when every required order needs
fences of only one instruction, the problem decomposes into independent single-instruction problems.

* `isOptIns_biUnion` — the gap-wise union of optimal insertions of the restricted instances
  `restrict ord need c` is an optimal insertion of the whole instance.
* `IsOptIns.subset_singleton` — an optimal insertion of `restrict ord need c` uses only fence `c`.
* `IsOptIns.size_eq_sum` — the minimum size is the sum of the minimum sizes of the restrictions.
* `isOptIns_of_isOptIns1` — the same with single-type optima, as the paper uses the lemma.
-/

set_option linter.unusedSectionVars false

namespace Podc.FenceInsertionChain

open Finset

variable {n : ℕ} {κ : Type*} [DecidableEq κ]

/-- A multi-type fence insertion: `f k` is the set of fences put right after operation `k`; every
required order `x ∈ ord` gets, for the fence type `c ∈ need x` it needs, a fence of type `c` in a
gap `k` with `x.1 ≤ k < x.2`. -/
def IsIns (ord : Finset (Fin n × Fin n)) (need : Fin n × Fin n → Option κ)
    (f : Fin n → Finset κ) : Prop :=
  ∀ x ∈ ord, ∀ c ∈ need x, ∃ k, x.1 ≤ k ∧ k < x.2 ∧ c ∈ f k

instance (ord : Finset (Fin n × Fin n)) (need : Fin n × Fin n → Option κ) (f : Fin n → Finset κ) :
    Decidable (IsIns ord need f) := by
  unfold IsIns; infer_instance

/-- The size of a multi-type fence insertion: the total number of fences. -/
def size (f : Fin n → Finset κ) : ℕ := ∑ k, (f k).card

/-- A minimum-size multi-type fence insertion (an `OptFI`). -/
def IsOptIns (ord : Finset (Fin n × Fin n)) (need : Fin n × Fin n → Option κ)
    (f : Fin n → Finset κ) : Prop :=
  IsIns ord need f ∧ ∀ g, IsIns ord need g → size f ≤ size g

/-- The required orders that need fence type `c` (the paper's `→|c`). -/
def restrict (ord : Finset (Fin n × Fin n)) (need : Fin n × Fin n → Option κ) (c : κ) :
    Finset (Fin n × Fin n) :=
  ord.filter fun x => need x = some c

/-- **Definition 2.2** (single-type fence insertion): a set `F` of gaps such that every required
order `x` has a gap `k ∈ F` with `x.1 ≤ k < x.2`. -/
def IsIns1 (ord : Finset (Fin n × Fin n)) (F : Finset (Fin n)) : Prop :=
  ∀ x ∈ ord, ∃ k ∈ F, x.1 ≤ k ∧ k < x.2

/-- A minimum-size single-type fence insertion (a solution of `FenceIns`). -/
def IsOptIns1 (ord : Finset (Fin n × Fin n)) (F : Finset (Fin n)) : Prop :=
  IsIns1 ord F ∧ ∀ G, IsIns1 ord G → F.card ≤ G.card

/-! ### Existence of optima -/

/-- Putting a fence in every gap works when all required orders are increasing. -/
theorem isIns1_univ {ord : Finset (Fin n × Fin n)} (hlt : ∀ x ∈ ord, x.1 < x.2) :
    IsIns1 ord univ :=
  fun x hx => ⟨x.1, mem_univ _, le_rfl, hlt x hx⟩

/-- Single-type optima exist (for increasing required orders). -/
theorem exists_isOptIns1 (ord : Finset (Fin n × Fin n)) (hlt : ∀ x ∈ ord, x.1 < x.2) :
    ∃ F, IsOptIns1 ord F := by
  classical
  obtain ⟨F, hF, hmin⟩ := (univ.filter (IsIns1 ord)).exists_min_image card
    ⟨univ, by simpa using isIns1_univ hlt⟩
  exact ⟨F, (mem_filter.1 hF).2, fun G hG => hmin G (by simpa using hG)⟩

/-- Putting every fence in every gap works when all required orders are increasing. -/
theorem isIns_univ [Fintype κ] {ord : Finset (Fin n × Fin n)} {need : Fin n × Fin n → Option κ}
    (hlt : ∀ x ∈ ord, x.1 < x.2) : IsIns ord need fun _ => univ :=
  fun x hx _ _ => ⟨x.1, le_rfl, hlt x hx, mem_univ _⟩

/-- Multi-type optima exist (for increasing required orders). -/
theorem exists_isOptIns [Fintype κ] (ord : Finset (Fin n × Fin n))
    (need : Fin n × Fin n → Option κ) (hlt : ∀ x ∈ ord, x.1 < x.2) :
    ∃ f, IsOptIns ord need f := by
  classical
  obtain ⟨f, hf, hmin⟩ := (univ.filter (IsIns ord need)).exists_min_image size
    ⟨fun _ => univ, by simpa using isIns_univ hlt⟩
  exact ⟨f, (mem_filter.1 hf).2, fun g hg => hmin g (by simpa using hg)⟩

/-! ### Lemma 2.1, abstract form -/

/-- Keeping only the fences of type `c` turns an insertion for `ord` into one for `restrict … c`. -/
theorem IsIns.filter_eq {ord : Finset (Fin n × Fin n)} {need : Fin n × Fin n → Option κ}
    {h : Fin n → Finset κ} (hh : IsIns ord need h) (c : κ) :
    IsIns (restrict ord need c) need fun k => (h k).filter (· = c) := by
  intro x hx d hd
  obtain ⟨hx, hc⟩ := mem_filter.1 hx
  rw [hc, Option.mem_some_iff] at hd
  subst hd
  obtain ⟨k, h1, h2, h3⟩ := hh x hx c (by simp [hc])
  exact ⟨k, h1, h2, mem_filter.2 ⟨h3, rfl⟩⟩

/-- Splitting an insertion by fence type does not change its size. -/
theorem size_eq_sum_filter [Fintype κ] (h : Fin n → Finset κ) :
    size h = ∑ c, size fun k => (h k).filter (· = c) := by
  unfold size
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact card_eq_sum_card_fiberwise (f := id) (t := univ) fun _ _ => mem_coe.2 (mem_univ _)

/-- **Lemma 2.1** (abstract form): the gap-wise union of optimal insertions of the restricted
instances is an optimal insertion. -/
theorem isOptIns_biUnion [Fintype κ] {ord : Finset (Fin n × Fin n)}
    {need : Fin n × Fin n → Option κ} {g : κ → Fin n → Finset κ}
    (hg : ∀ c, IsOptIns (restrict ord need c) need (g c)) :
    IsOptIns ord need fun k => univ.biUnion fun c => g c k := by
  refine ⟨fun x hx c hc => ?_, fun h hh => ?_⟩
  · obtain ⟨k, h1, h2, h3⟩ :=
      (hg c).1 x (mem_filter.2 ⟨hx, Option.mem_def.1 hc⟩) c hc
    exact ⟨k, h1, h2, mem_biUnion.2 ⟨c, mem_univ _, h3⟩⟩
  · calc size (fun k => univ.biUnion fun c => g c k)
        ≤ ∑ k, ∑ c, (g c k).card := Finset.sum_le_sum fun k _ => card_biUnion_le
      _ = ∑ c, size (g c) := Finset.sum_comm
      _ ≤ ∑ c, size fun k => (h k).filter (· = c) :=
          Finset.sum_le_sum fun c _ => (hg c).2 _ (hh.filter_eq c)
      _ = size h := (size_eq_sum_filter h).symm

/-- An optimal insertion of `restrict ord need c` uses only fences of type `c`. -/
theorem IsOptIns.subset_singleton {ord : Finset (Fin n × Fin n)}
    {need : Fin n × Fin n → Option κ} {c : κ} {f : Fin n → Finset κ}
    (hf : IsOptIns (restrict ord need c) need f) (k : Fin n) : f k ⊆ {c} := by
  intro d hd
  by_contra hdc
  have hval : IsIns (restrict ord need c) need fun k => (f k).filter (· = c) := by
    intro x hx e he
    obtain ⟨hx', hc⟩ := mem_filter.1 hx
    rw [hc, Option.mem_some_iff] at he
    subst he
    obtain ⟨k, h1, h2, h3⟩ := hf.1 x hx c (by simp [hc])
    exact ⟨k, h1, h2, mem_filter.2 ⟨h3, rfl⟩⟩
  have hlt : size (fun k => (f k).filter (· = c)) < size f := by
    refine Finset.sum_lt_sum (fun k _ => card_le_card (filter_subset _ _)) ⟨k, mem_univ _, ?_⟩
    refine card_lt_card ⟨filter_subset _ _, fun hsub => hdc ?_⟩
    simpa using (mem_filter.1 (hsub hd)).2
  exact absurd (hf.2 _ hval) (not_le.2 hlt)

/-- **Lemma 2.1** (sizes): the minimum size of a fence insertion is the sum over fence types of
the minimum sizes for the restricted instances. -/
theorem IsOptIns.size_eq_sum [Fintype κ] {ord : Finset (Fin n × Fin n)}
    {need : Fin n × Fin n → Option κ} {f : Fin n → Finset κ} (hf : IsOptIns ord need f)
    {g : κ → Fin n → Finset κ} (hg : ∀ c, IsOptIns (restrict ord need c) need (g c)) :
    size f = ∑ c, size (g c) := by
  have hu := isOptIns_biUnion hg
  have h1 : size f = size fun k => univ.biUnion fun c => g c k :=
    le_antisymm (hf.2 _ hu.1) (hu.2 _ hf.1)
  rw [h1]
  unfold size
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => card_biUnion fun c _ d _ hcd => ?_
  exact disjoint_left.2 fun e he he' =>
    hcd ((mem_singleton.1 ((hg c).subset_singleton k he)).symm.trans
      (mem_singleton.1 ((hg d).subset_singleton k he')))

/-- Counting the pairs `(k, c)` with `P k c` row by row or column by column. -/
theorem sum_card_filter_comm {α β : Type*} [Fintype α] [Fintype β] (P : α → β → Prop)
    [∀ a b, Decidable (P a b)] :
    ∑ a, (univ.filter fun b => P a b).card = ∑ b, (univ.filter fun a => P a b).card := by
  simp only [card_filter]
  exact Finset.sum_comm

/-- **Lemma 2.1** in the form the paper uses it: single-type optima `F c` of the restricted
instances give an optimal multi-type insertion (put fence `c` in gap `k` iff `k ∈ F c`), whose size
is `∑ c, |F c|`. -/
theorem isOptIns_of_isOptIns1 [Fintype κ] {ord : Finset (Fin n × Fin n)}
    {need : Fin n × Fin n → Option κ} {F : κ → Finset (Fin n)}
    (hF : ∀ c, IsOptIns1 (restrict ord need c) (F c)) :
    IsOptIns ord need (fun k => univ.filter fun c => k ∈ F c) ∧
      size (fun k => univ.filter fun c => k ∈ F c) = ∑ c, (F c).card := by
  have hsize : size (fun k => univ.filter fun c => k ∈ F c) = ∑ c, (F c).card := by
    unfold size
    rw [sum_card_filter_comm (fun k c => k ∈ F c)]
    simp
  refine ⟨⟨fun x hx c hc => ?_, fun h hh => ?_⟩, hsize⟩
  · obtain ⟨k, hk, h1, h2⟩ := (hF c).1 x (mem_filter.2 ⟨hx, Option.mem_def.1 hc⟩)
    exact ⟨k, h1, h2, by simpa using hk⟩
  · rw [hsize]
    have hG : ∀ c, IsIns1 (restrict ord need c) (univ.filter fun k => c ∈ h k) := by
      intro c x hx
      obtain ⟨hx', hc⟩ := mem_filter.1 hx
      obtain ⟨k, h1, h2, h3⟩ := hh x hx' c (by simp [hc])
      exact ⟨k, by simpa using h3, h1, h2⟩
    calc ∑ c, (F c).card ≤ ∑ c, (univ.filter fun k => c ∈ h k).card :=
          Finset.sum_le_sum fun c _ => (hF c).2 _ (hG c)
      _ = size h := by
          unfold size
          rw [← sum_card_filter_comm (fun k c => c ∈ h k)]
          simp

end Podc.FenceInsertionChain
