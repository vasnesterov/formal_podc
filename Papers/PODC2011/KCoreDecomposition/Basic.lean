import Mathlib

/-!
# k-cores, coreness, the locality theorem and `computeIndex`

Montresor, De Pellegrini, Miorandi, *Distributed k-Core Decomposition*, PODC 2011
(arXiv 1103.5320v2).

* `IsCoreSet G k S`: every vertex of `S` has at least `k` neighbours in `S`.
* `IsKCore G k C` (Definition 1): `G(C)` has minimum degree `≥ k` and is the maximum such subgraph.
  `kCore G k` is the (unique) `k`-core: `isKCore_kCore`, `IsKCore.eq_kCore`.
* `coreness G u` (Definition 2): `coreness_eq_iff` — `u` is in the `k`-core but not in the
  `(k+1)`-core.
* `hIndex G e u`: the largest `i` such that `u` has at least `i` neighbours `v` with `i ≤ e v`
  (estimates are in `ℕ∞`, `⊤` = the paper's `+∞`).
* `theorem_1` (Locality) and its functional form `coreness_eq_hIndex`.
* `le_coreness_of_le_hIndex`: every "post-fixpoint" `c ≤ hIndex c` is below the coreness — the
  key fact behind liveness.
* `computeIndex` — Algorithm 2, written as in the paper (counting array with `min(k, est[v])`,
  suffix sums, `while` loop), and `computeIndex_eq`: it returns `0` if `k = 0` and
  `max 1 (min k (hIndex e u))` otherwise.
-/

open Finset

set_option linter.unusedSectionVars false

namespace KCoreDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### k-cores and coreness -/

-- CSLib candidate: `IsCoreSet`, `kCore`, `coreness` and their API (k-core decomposition of a
-- finite simple graph), together with `hIndex` and the locality theorem below.

/-- `G(S)` has minimum degree at least `k`. -/
def IsCoreSet (k : ℕ) (S : Finset V) : Prop :=
  ∀ u ∈ S, k ≤ #{v ∈ S | G.Adj u v}

instance (k : ℕ) : DecidablePred (IsCoreSet G k) := fun _ => by
  unfold IsCoreSet; infer_instance

/-- Definition 1 of the paper: `G(C)` is a `k`-core iff all its vertices have degree `≥ k` in
`G(C)` and it is the maximum subgraph with this property. -/
def IsKCore (k : ℕ) (C : Finset V) : Prop :=
  IsCoreSet G k C ∧ ∀ S, IsCoreSet G k S → S ⊆ C

/-- The `k`-core: union of all vertex sets inducing minimum degree `≥ k`. -/
def kCore (k : ℕ) : Finset V :=
  univ.filter fun u => ∃ S : Finset V, IsCoreSet G k S ∧ u ∈ S

variable {G}

theorem mem_kCore {k : ℕ} {u : V} : u ∈ kCore G k ↔ ∃ S, IsCoreSet G k S ∧ u ∈ S := by
  simp [kCore]

theorem subset_kCore {k : ℕ} {S : Finset V} (h : IsCoreSet G k S) : S ⊆ kCore G k :=
  fun _ hu => mem_kCore.2 ⟨S, h, hu⟩

theorem card_filter_adj_mono {S T : Finset V} (h : S ⊆ T) (u : V) :
    #{v ∈ S | G.Adj u v} ≤ #{v ∈ T | G.Adj u v} :=
  card_le_card (filter_subset_filter _ h)

variable (G) in
theorem isCoreSet_kCore (k : ℕ) : IsCoreSet G k (kCore G k) := by
  intro u hu
  obtain ⟨S, hS, huS⟩ := mem_kCore.1 hu
  exact (hS u huS).trans (card_filter_adj_mono (subset_kCore hS) u)

variable (G) in
theorem isKCore_kCore (k : ℕ) : IsKCore G k (kCore G k) :=
  ⟨isCoreSet_kCore G k, fun _ hS => subset_kCore hS⟩

/-- The `k`-core of Definition 1 is unique. -/
theorem IsKCore.eq_kCore {k : ℕ} {C : Finset V} (h : IsKCore G k C) : C = kCore G k :=
  Subset.antisymm (subset_kCore h.1) (h.2 _ (isCoreSet_kCore G k))

theorem kCore_anti {k k' : ℕ} (h : k ≤ k') : kCore G k' ⊆ kCore G k :=
  subset_kCore fun u hu => h.trans (isCoreSet_kCore G k' u hu)

variable (G) in
@[simp] theorem kCore_zero : kCore G 0 = univ :=
  eq_univ_of_forall fun u => subset_kCore (S := univ) (fun _ _ => Nat.zero_le _) (mem_univ u)

theorem card_filter_adj_le_degree (S : Finset V) (u : V) : #{v ∈ S | G.Adj u v} ≤ G.degree u := by
  rw [← G.card_neighborFinset_eq_degree]
  exact card_le_card fun v hv => (G.mem_neighborFinset u v).2 (mem_filter.1 hv).2

theorem le_degree_of_mem_kCore {k : ℕ} {u : V} (hu : u ∈ kCore G k) : k ≤ G.degree u :=
  (isCoreSet_kCore G k u hu).trans (card_filter_adj_le_degree _ u)

variable (G) in
/-- The coreness of `u` (Definition 2): the largest `k` such that `u` belongs to the `k`-core. -/
def coreness (u : V) : ℕ :=
  Nat.findGreatest (fun k => u ∈ kCore G k) (G.degree u)

theorem le_coreness_iff {k : ℕ} {u : V} : k ≤ coreness G u ↔ u ∈ kCore G k := by
  constructor
  · intro h
    have : u ∈ kCore G (coreness G u) :=
      Nat.findGreatest_spec (P := fun k => u ∈ kCore G k) (Nat.zero_le _) (by simp)
    exact kCore_anti h this
  · intro h
    exact Nat.le_findGreatest (le_degree_of_mem_kCore h) h

theorem mem_kCore_coreness (u : V) : u ∈ kCore G (coreness G u) := le_coreness_iff.1 le_rfl

/-- Definition 2 of the paper: `u` has coreness `k` iff it belongs to the `k`-core but not to the
`(k+1)`-core. -/
theorem coreness_eq_iff {k : ℕ} {u : V} :
    coreness G u = k ↔ u ∈ kCore G k ∧ u ∉ kCore G (k + 1) := by
  rw [← le_coreness_iff, ← le_coreness_iff]; omega

theorem coreness_le_degree (u : V) : coreness G u ≤ G.degree u := Nat.findGreatest_le _

theorem le_coreness_of_isCoreSet {k : ℕ} {S : Finset V} {u : V} (hS : IsCoreSet G k S)
    (hu : u ∈ S) : k ≤ coreness G u :=
  le_coreness_iff.2 (subset_kCore hS hu)

/-- A vertex with a neighbour has coreness at least `1`. -/
theorem one_le_coreness_of_adj {u v : V} (h : G.Adj u v) : 1 ≤ coreness G u := by
  refine le_coreness_of_isCoreSet (S := {u, v}) ?_ (mem_insert_self _ _)
  intro w hw
  rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero, filter_eq_empty_iff, not_forall]
  rcases mem_insert.1 hw with rfl | hw
  · exact ⟨v, by simp [h]⟩
  · rw [mem_singleton] at hw; subst hw; exact ⟨u, by simp [h.symm]⟩

/-! ### h-index of the neighbours' estimates -/

variable (G) in
/-- Number of neighbours `v` of `u` whose estimate is at least `i`. -/
def nbrCount (e : V → ℕ∞) (u : V) (i : ℕ) : ℕ :=
  #{v ∈ G.neighborFinset u | (i : ℕ∞) ≤ e v}

variable (G) in
/-- The largest `i` such that at least `i` neighbours of `u` have estimate `≥ i`. -/
def hIndex (e : V → ℕ∞) (u : V) : ℕ :=
  Nat.findGreatest (fun i => i ≤ nbrCount G e u i) (G.degree u)

theorem nbrCount_le_degree (e : V → ℕ∞) (u : V) (i : ℕ) : nbrCount G e u i ≤ G.degree u := by
  rw [← G.card_neighborFinset_eq_degree]; exact card_filter_le _ _

theorem nbrCount_anti {e : V → ℕ∞} {u : V} {i j : ℕ} (h : i ≤ j) :
    nbrCount G e u j ≤ nbrCount G e u i :=
  card_le_card <| monotone_filter_right _ fun _ _ hv => le_trans (by exact_mod_cast h) hv

theorem nbrCount_mono {e e' : V → ℕ∞} {u : V} (h : ∀ v, G.Adj u v → e v ≤ e' v) (i : ℕ) :
    nbrCount G e u i ≤ nbrCount G e' u i := by
  refine card_le_card fun v hv => ?_
  simp only [mem_filter, SimpleGraph.mem_neighborFinset] at hv ⊢
  exact ⟨hv.1, hv.2.trans (h v hv.1)⟩

theorem nbrCount_congr {e e' : V → ℕ∞} {u : V} (h : ∀ v, G.Adj u v → e v = e' v) (i : ℕ) :
    nbrCount G e u i = nbrCount G e' u i :=
  le_antisymm (nbrCount_mono (fun v hv => (h v hv).le) i)
    (nbrCount_mono (fun v hv => (h v hv).ge) i)

theorem le_hIndex_iff {e : V → ℕ∞} {u : V} {i : ℕ} :
    i ≤ hIndex G e u ↔ i ≤ nbrCount G e u i := by
  constructor
  · intro h
    have hs := Nat.findGreatest_spec (P := fun i => i ≤ nbrCount G e u i) (m := 0) (n := G.degree u)
      (Nat.zero_le _) (Nat.zero_le _)
    exact h.trans (hs.trans (nbrCount_anti h))
  · intro h
    exact Nat.le_findGreatest (h.trans (nbrCount_le_degree e u i)) h

theorem hIndex_le_degree (e : V → ℕ∞) (u : V) : hIndex G e u ≤ G.degree u :=
  Nat.findGreatest_le _

theorem hIndex_mono {e e' : V → ℕ∞} {u : V} (h : ∀ v, G.Adj u v → e v ≤ e' v) :
    hIndex G e u ≤ hIndex G e' u :=
  le_hIndex_iff.2 ((le_hIndex_iff.1 le_rfl).trans (nbrCount_mono h _))

theorem hIndex_congr {e e' : V → ℕ∞} {u : V} (h : ∀ v, G.Adj u v → e v = e' v) :
    hIndex G e u = hIndex G e' u :=
  le_antisymm (hIndex_mono fun v hv => (h v hv).le) (hIndex_mono fun v hv => (h v hv).ge)

/-- `∃ W ⊆ N(u), |W| = j ∧ ∀ v ∈ W, j ≤ c v` is the same as `j ≤ nbrCount c u j`. -/
theorem exists_subset_iff_le_nbrCount (c : V → ℕ) (u : V) (j : ℕ) :
    (∃ W ⊆ G.neighborFinset u, #W = j ∧ ∀ v ∈ W, j ≤ c v) ↔
      j ≤ nbrCount G (fun v => (c v : ℕ∞)) u j := by
  constructor
  · rintro ⟨W, hW, rfl, hc⟩
    refine card_le_card fun v hv => ?_
    simp only [mem_filter, Nat.cast_le]
    exact ⟨hW hv, hc v hv⟩
  · intro h
    obtain ⟨W, hW, hcard⟩ := exists_subset_card_eq h
    refine ⟨W, hW.trans (filter_subset _ _), hcard, fun v hv => ?_⟩
    have := (mem_filter.1 (hW hv)).2
    exact Nat.cast_le.1 this

/-! ### Theorem 1 (locality) -/

variable (G) in
/-- Locality, functional form: the coreness of `u` is the h-index of its neighbours' corenesses. -/
theorem coreness_eq_hIndex (u : V) :
    coreness G u = hIndex G (fun v => (coreness G v : ℕ∞)) u := by
  apply le_antisymm
  · rw [le_hIndex_iff]
    refine (isCoreSet_kCore G _ u (mem_kCore_coreness u)).trans (card_le_card fun v hv => ?_)
    simp only [mem_filter, SimpleGraph.mem_neighborFinset, Nat.cast_le] at hv ⊢
    exact ⟨hv.2, le_coreness_iff.2 hv.1⟩
  · set i := hIndex G (fun v => (coreness G v : ℕ∞)) u
    have hi : i ≤ nbrCount G (fun v => (coreness G v : ℕ∞)) u i := le_hIndex_iff.1 le_rfl
    refine le_coreness_of_isCoreSet (S := insert u (kCore G i)) ?_ (mem_insert_self _ _)
    intro w hw
    rcases mem_insert.1 hw with rfl | hw
    · refine hi.trans (card_le_card fun v hv => ?_)
      simp only [mem_filter, SimpleGraph.mem_neighborFinset, Nat.cast_le] at hv ⊢
      exact ⟨mem_insert_of_mem (le_coreness_iff.1 hv.2), hv.1⟩
    · exact (isCoreSet_kCore G i w hw).trans (card_filter_adj_mono (subset_insert _ _) w)

/-- **Theorem 1 (Locality).** `k(u) = k` iff (i) `u` has a set of `k` neighbours of coreness
`≥ k`, and (ii) `u` has no set of `k+1` neighbours of coreness `≥ k+1`. -/
theorem theorem_1 (u : V) (k : ℕ) :
    coreness G u = k ↔
      (∃ Vk ⊆ G.neighborFinset u, #Vk = k ∧ ∀ v ∈ Vk, k ≤ coreness G v) ∧
      ¬ ∃ Vk1 ⊆ G.neighborFinset u, #Vk1 = k + 1 ∧ ∀ v ∈ Vk1, k + 1 ≤ coreness G v := by
  rw [exists_subset_iff_le_nbrCount, exists_subset_iff_le_nbrCount, ← le_hIndex_iff,
    ← le_hIndex_iff, ← coreness_eq_hIndex]
  omega

/-- **Safety lemma.** If every neighbour's estimate is at least its coreness, then the h-index of
the estimates is at least the coreness of `u`. -/
theorem coreness_le_hIndex {e : V → ℕ∞} {u : V}
    (h : ∀ v, G.Adj u v → (coreness G v : ℕ∞) ≤ e v) : coreness G u ≤ hIndex G e u :=
  (coreness_eq_hIndex G u).le.trans (hIndex_mono h)

/-- **Fixpoint lemma (liveness).** If every node's value is at most the h-index of its neighbours'
values, then every value is at most the coreness. -/
theorem le_coreness_of_le_hIndex {c : V → ℕ}
    (h : ∀ u, c u ≤ hIndex G (fun v => (c v : ℕ∞)) u) (u : V) : c u ≤ coreness G u := by
  refine le_coreness_of_isCoreSet (S := univ.filter fun v => c u ≤ c v) ?_ (by simp)
  intro w hw
  have hw' : c u ≤ c w := (mem_filter.1 hw).2
  refine hw'.trans ((le_hIndex_iff.1 (h w)).trans (card_le_card fun v hv => ?_))
  simp only [mem_filter, SimpleGraph.mem_neighborFinset, Nat.cast_le, mem_univ,
    true_and] at hv ⊢
  exact ⟨hw'.trans hv.2, hv.1⟩

/-! ### Algorithm 2: `computeIndex` -/

/-- The `while` loop of Algorithm 2: `i ← k; while i > 1 and count[i] < i do i ← i − 1`. -/
def whileLoop (count : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | i + 2 => if count (i + 2) < i + 2 then whileLoop count (i + 1) else i + 2

variable (G) in
/-- Algorithm 2, `computeIndex(est, u, k)`. The first loop builds `count[j]` = number of
neighbours `v` with `min(k, est[v]) = j`; the backward loop turns it into suffix sums
`count[i] = Σ_{i ≤ j ≤ k} count[j]`; the `while` loop returns the largest `i ≤ k` with
`count[i] ≥ i` (or `1`). -/
noncomputable def computeIndex (e : V → ℕ∞) (u : V) (k : ℕ) : ℕ :=
  whileLoop
    (fun i => ∑ j ∈ Icc i k, #{v ∈ G.neighborFinset u | (min (k : ℕ∞) (e v)).toNat = j}) k

theorem whileLoop_eq (count : ℕ → ℕ) (k h : ℕ)
    (hc : ∀ j, 1 ≤ j → j ≤ k → (count j < j ↔ h < j)) :
    ∀ i, 1 ≤ i → i ≤ k → whileLoop count i = max 1 (min i h)
  | 0, h0, _ => absurd h0 (by omega)
  | 1, _, _ => by simp only [whileLoop]; omega
  | i + 2, _, hi => by
    rw [whileLoop]
    split_ifs with hlt
    · rw [whileLoop_eq count k h hc (i + 1) (by omega) (by omega)]
      have := (hc (i + 2) (by omega) hi).1 hlt
      omega
    · have := mt (hc (i + 2) (by omega) hi).2 hlt
      omega

theorem suffix_count_eq (e : V → ℕ∞) (u : V) {i k : ℕ} (hik : i ≤ k) :
    ∑ j ∈ Icc i k, #{v ∈ G.neighborFinset u | (min (k : ℕ∞) (e v)).toNat = j} =
      nbrCount G e u i := by
  have key : ∀ v, (i : ℕ∞) ≤ e v ↔ i ≤ (min (k : ℕ∞) (e v)).toNat := by
    intro v
    rcases le_total (k : ℕ∞) (e v) with h | h
    · rw [min_eq_left h, ENat.toNat_natCast]
      exact ⟨fun _ => hik, fun _ => le_trans (by exact_mod_cast hik) h⟩
    · rw [min_eq_right h]
      have hne : e v ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top k) h
      lift e v to ℕ using hne with n
      simp
  have hfib := card_eq_sum_card_fiberwise (s := (G.neighborFinset u).filter fun v => (i : ℕ∞) ≤ e v)
    (t := Icc i k) (f := fun v => (min (k : ℕ∞) (e v)).toNat) (by
      intro v hv
      have hv := (key v).1 (mem_filter.1 hv).2
      refine mem_Icc.2 ⟨hv, ?_⟩
      have : min (k : ℕ∞) (e v) ≤ k := min_le_left _ _
      have hne : min (k : ℕ∞) (e v) ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top k) this
      lift min (k : ℕ∞) (e v) to ℕ using hne with n hn
      simpa using this)
  rw [nbrCount, hfib]
  refine sum_congr rfl fun j hj => ?_
  congr 1
  ext v
  simp only [mem_filter]
  constructor
  · rintro ⟨hv, hj'⟩
    refine ⟨⟨hv, (key v).2 ?_⟩, hj'⟩
    rw [hj']; exact (mem_Icc.1 hj).1
  · rintro ⟨⟨hv, _⟩, hj'⟩; exact ⟨hv, hj'⟩

/-- `computeIndex` computes `max 1 (min k h)` where `h` is the h-index of the estimates
(and `0` when `k = 0`). -/
theorem computeIndex_eq (e : V → ℕ∞) (u : V) (k : ℕ) :
    computeIndex G e u k = if k = 0 then 0 else max 1 (min k (hIndex G e u)) := by
  split_ifs with hk
  · subst hk; rfl
  · refine whileLoop_eq _ k (hIndex G e u) (fun j hj hjk => ?_) k (by omega) le_rfl
    rw [suffix_count_eq e u hjk, ← not_le, ← not_le, ← le_hIndex_iff]

theorem computeIndex_le (e : V → ℕ∞) (u : V) (k : ℕ) : computeIndex G e u k ≤ k := by
  rw [computeIndex_eq]; split_ifs <;> omega

theorem computeIndex_zero (e : V → ℕ∞) (u : V) : computeIndex G e u 0 = 0 := by
  simp [computeIndex_eq]

/-- When the h-index is positive (or `k = 0`), `computeIndex` is `min k h`. -/
theorem computeIndex_eq_min {e : V → ℕ∞} {u : V} {k : ℕ} (h : 1 ≤ hIndex G e u ∨ k = 0) :
    computeIndex G e u k = min k (hIndex G e u) := by
  rw [computeIndex_eq]; split_ifs <;> omega

theorem computeIndex_mono {e e' : V → ℕ∞} {u : V} (h : ∀ v, G.Adj u v → e v ≤ e' v)
    {k k' : ℕ} (hk : k ≤ k') : computeIndex G e u k ≤ computeIndex G e' u k' := by
  have := hIndex_mono h
  rw [computeIndex_eq, computeIndex_eq]; split_ifs <;> omega

theorem computeIndex_congr {e e' : V → ℕ∞} {u : V} (h : ∀ v, G.Adj u v → e v = e' v) (k : ℕ) :
    computeIndex G e u k = computeIndex G e' u k := by
  rw [computeIndex_eq, computeIndex_eq, hIndex_congr h]

/-- Recomputing with smaller estimates after a previous computation is the same as computing
once with the smaller estimates. -/
theorem computeIndex_comp {e e' : V → ℕ∞} {u : V} (h : ∀ v, G.Adj u v → e' v ≤ e v) (k : ℕ) :
    computeIndex G e' u (computeIndex G e u k) = computeIndex G e' u k := by
  have := hIndex_mono h
  rw [computeIndex_eq e u k]
  split_ifs with hk
  · subst hk; simp [computeIndex_zero]
  · rw [computeIndex_eq, computeIndex_eq]; split_ifs <;> omega

theorem computeIndex_idem (e : V → ℕ∞) (u : V) (k : ℕ) :
    computeIndex G e u (computeIndex G e u k) = computeIndex G e u k :=
  computeIndex_comp (fun _ _ => le_rfl) k

/-- **Safety of one computation.** If `k ≥ k(u)` and all neighbours' estimates are at least their
coreness, then `computeIndex` returns at least `k(u)`. -/
theorem coreness_le_computeIndex {e : V → ℕ∞} {u : V} {k : ℕ} (hk : coreness G u ≤ k)
    (he : ∀ v, G.Adj u v → (coreness G v : ℕ∞) ≤ e v) : coreness G u ≤ computeIndex G e u k := by
  have := coreness_le_hIndex he
  rw [computeIndex_eq]; split_ifs <;> omega

/-- If `computeIndex` does not lower `k`, and the h-index is positive or `k = 0`, then `k` is at most
the h-index. -/
theorem le_hIndex_of_computeIndex_eq {e : V → ℕ∞} {u : V} {k : ℕ}
    (h : computeIndex G e u k = k) (h1 : 1 ≤ hIndex G e u ∨ k = 0) : k ≤ hIndex G e u := by
  rw [computeIndex_eq_min h1] at h; omega

/-- A node with a neighbour whose estimate is `≥ 1` has positive h-index. -/
theorem one_le_hIndex {e : V → ℕ∞} {u v : V} (huv : G.Adj u v) (hv : 1 ≤ e v) :
    1 ≤ hIndex G e u := by
  rw [le_hIndex_iff, nbrCount, Nat.one_le_iff_ne_zero, Ne, card_eq_zero, filter_eq_empty_iff,
    not_forall]
  refine ⟨v, fun h => ?_⟩
  simp only [SimpleGraph.mem_neighborFinset, huv, Nat.cast_one, true_implies] at h
  exact h hv

end KCoreDecomposition
