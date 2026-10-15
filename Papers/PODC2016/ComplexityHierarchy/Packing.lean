import Mathlib

/-!
# `k`-packings

Pure combinatorics of `k`-packings from Section 7 of
F. Ellen, R. Gelashvili, N. Shavit, L. Zhu,
*A Complexity-Based Hierarchy for Multiprocessor Synchronization*, PODC 2016.

-- CSLib candidate

Processes `P` cover locations `Loc` according to a relation `cov : P → Loc → Prop` (a process may
cover several locations). A `k`-packing of a finite set `S` of processes assigns to each process of
`S` a location it covers, with at most `k` processes per location. A location `r` is *fully
`k`-packed* by `S` if every `k`-packing of `S` packs exactly `k` processes into `r`.

## Main results

* `fullyPacked_of_cov` (Lemma 7.2): a process packed (by some packing) into a fully packed location
  only covers fully packed locations.
* `isPacking_insert`, `card_le_of_isPacking`, `card_lt_of_not_fullyPacked`, `exists_blocks`,
  `isPacking_congr`, `fullyPacked_congr`: auxiliary facts used in the paper's Section 7.
* `lemma71_trail_counterexample`: the re-packing step of the paper's proof of Lemma 7.1 (along a
  maximal trail) does not always decrease the number of processes packed in the start location of
  the re-packed suffix when the trail revisits a location.

## Implementation notes

Instead of the paper's Eulerian-trail argument (Lemma 7.1) we use an augmenting-path argument on
the *residual relation* `resid cov S π x y` ("some process packed into `x` by `π` covers `y`"):
* if every location reachable from `r` is full, all of them are fully packed (counting);
* if `x` reaches an under-full location, then re-packing along a shortest path gives a packing in
  which `x` is under-full.
-/

namespace Cslib.SharedMemory.ComplexityHierarchy

open Finset

variable {P Loc : Type*} [DecidableEq Loc]

/-- Number of processes of `S` packed into `r` by `π`. -/
def packCount (S : Finset P) (π : P → Loc) (r : Loc) : ℕ := (S.filter (fun p => π p = r)).card

/-- `π` is a `k`-packing of `S`: every process of `S` is packed into a location it covers, at most
`k` per location (Section 7 of the paper). -/
def IsPacking (cov : P → Loc → Prop) (k : ℕ) (S : Finset P) (π : P → Loc) : Prop :=
  (∀ p ∈ S, cov p (π p)) ∧ ∀ r, packCount S π r ≤ k

/-- `r` is fully `k`-packed by `S`: every `k`-packing of `S` packs exactly `k` processes into `r`
(Section 7 of the paper). -/
def FullyPacked (cov : P → Loc → Prop) (k : ℕ) (S : Finset P) (r : Loc) : Prop :=
  ∀ π, IsPacking cov k S π → packCount S π r = k

/-! ### Length-indexed walks -/

/-- Walks of length `n` from `x` to `y` along a relation `R`, built by appending edges. -/
inductive LWalk {α : Type*} (R : α → α → Prop) : ℕ → α → α → Prop
  | refl (x : α) : LWalk R 0 x x
  | tail {n : ℕ} {x z y : α} : LWalk R n x z → R z y → LWalk R (n + 1) x y

namespace LWalk

variable {α : Type*} {R R' : α → α → Prop}

theorem mono (h : ∀ a b, R a b → R' a b) {n : ℕ} {x y : α} (w : LWalk R n x y) :
    LWalk R' n x y := by
  induction w with
  | refl x => exact .refl x
  | tail _ hr ih => exact .tail ih (h _ _ hr)

/-- Either a walk avoids `t` as the source of an edge, or a prefix of it reaches `t` while avoiding
`t` as a source. -/
theorem cut (t : α) {n : ℕ} {x y : α} (w : LWalk R n x y) :
    LWalk (fun a b => R a b ∧ a ≠ t) n x y ∨
      ∃ m ≤ n, LWalk (fun a b => R a b ∧ a ≠ t) m x t := by
  induction w with
  | refl x => exact Or.inl (.refl x)
  | @tail n x z y _ hr ih =>
    rcases ih with h | ⟨m, hm, h⟩
    · by_cases hz : z = t
      · subst hz; exact Or.inr ⟨n, by omega, h⟩
      · exact Or.inl (.tail h ⟨hr, hz⟩)
    · exact Or.inr ⟨m, by omega, h⟩

/-- A walk to `z` can be shortened to one that never leaves `z`. -/
theorem cut_self {n : ℕ} {x z : α} (w : LWalk R n x z) :
    ∃ m ≤ n, LWalk (fun a b => R a b ∧ a ≠ z) m x z := by
  rcases w.cut z with h | h
  · exact ⟨n, le_rfl, h⟩
  · exact h

end LWalk

/-! ### Residual relation and augmenting paths -/

/-- Residual relation of a packing: some process of `S` packed into `x` by `π` covers `y`. -/
def resid (cov : P → Loc → Prop) (S : Finset P) (π : P → Loc) (x y : Loc) : Prop :=
  ∃ q ∈ S, π q = x ∧ cov q y

variable {cov : P → Loc → Prop} {k : ℕ} {S : Finset P}

theorem packCount_update [DecidableEq P] {π : P → Loc} {q : P} (hq : q ∈ S) (y r : Loc) :
    packCount S (Function.update π q y) r + (if π q = r then 1 else 0) =
      packCount S π r + (if y = r then 1 else 0) := by
  unfold packCount
  rw [← Finset.insert_erase hq]
  have hne : q ∉ S.erase q := Finset.notMem_erase q S
  have hcongr : (S.erase q).filter (fun p => Function.update π q y p = r) =
      (S.erase q).filter (fun p => π p = r) := by
    apply Finset.filter_congr
    intro p hp
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hp)]
  rw [Finset.filter_insert, Finset.filter_insert, Function.update_self, hcongr]
  by_cases h1 : y = r <;> by_cases h2 : π q = r <;>
    simp [h1, h2, Finset.card_insert_of_notMem, hne]

/-- Augmenting paths: if `x` reaches an under-full location in the residual relation of a
packing `π`, then some packing packs fewer than `k` processes into `x`. -/
theorem exists_packing_lt_of_walk :
    ∀ (n : ℕ) (π : P → Loc) (x y : Loc), IsPacking cov k S π →
      LWalk (resid cov S π) n x y → packCount S π y < k →
        ∃ σ, IsPacking cov k S σ ∧ packCount S σ x < k := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro π x y hπ w hy
  cases w with
  | refl => exact ⟨π, hπ, hy⟩
  | @tail m _ z _ w hzy =>
    obtain ⟨q, hqS, hqz, hqy⟩ := hzy
    have hcount := fun r => packCount_update (π := π) hqS y r
    set σ := Function.update π q y with hσdef
    have hσ : IsPacking cov k S σ := by
      refine ⟨fun p hp => ?_, fun r => ?_⟩
      · by_cases hpq : p = q
        · subst hpq; simp [σ, hqy]
        · simp [σ, Function.update_of_ne hpq, hπ.1 p hp]
      · have h1 := hcount r
        have h2 := hπ.2 r
        by_cases hyr : y = r
        · subst hyr; split_ifs at h1 <;> omega
        · split_ifs at h1 <;> omega
    have hσz : packCount S σ z < k := by
      have h1 := hcount z
      have h2 := hπ.2 z
      by_cases hyz : y = z
      · subst hyz; simp only [hqz, ite_true] at h1; omega
      · simp only [hqz, hyz, ite_true, ite_false] at h1; omega
    obtain ⟨m', hm', w'⟩ := w.cut_self
    have w'' : LWalk (resid cov S σ) m' x z := by
      refine w'.mono (fun a b hab => ?_)
      obtain ⟨⟨q', hq'S, hq'a, hq'b⟩, ha⟩ := hab
      have hq' : q' ≠ q := by
        rintro rfl
        exact ha (hq'a.symm.trans hqz)
      exact ⟨q', hq'S, by simp [σ, Function.update_of_ne hq', hq'a], hq'b⟩
    exact ih m' (by omega) σ x z hσ w'' hσz

/-- Counting: if a set `Z` of locations is closed under the residual relation of `π` and every
location of `Z` holds exactly `k` processes under `π`, then every packing packs exactly `k`
processes into each location of `Z`. -/
theorem packCount_eq_of_closed {π σ : P → Loc} {Z : Finset Loc}
    (hclosed : ∀ q ∈ S, π q ∈ Z → ∀ y, cov q y → y ∈ Z)
    (hfull : ∀ z ∈ Z, packCount S π z = k) (hσ : IsPacking cov k S σ) :
    ∀ z ∈ Z, packCount S σ z = k := by
  classical
  set A := S.filter (fun q => π q ∈ Z) with hAdef
  have hA1 : A.card = ∑ z ∈ Z, packCount S π z := by
    rw [card_eq_sum_card_fiberwise (s := A) (f := π) (t := Z) (fun q hq => (mem_filter.1 hq).2)]
    refine sum_congr rfl (fun z hz => ?_)
    unfold packCount
    congr 1
    ext q
    simp only [A, mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hz⟩, h3⟩
  have hA2 : A.card ≤ ∑ z ∈ Z, packCount S σ z := by
    rw [card_eq_sum_card_fiberwise (s := A) (f := σ) (t := Z) (fun q hq =>
      hclosed q (mem_filter.1 hq).1 (mem_filter.1 hq).2 _ (hσ.1 q (mem_filter.1 hq).1))]
    refine sum_le_sum (fun z _ => card_le_card ?_)
    intro q
    simp only [A, mem_filter]
    rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, h3⟩
  have hle : ∀ z ∈ Z, packCount S σ z ≤ k := fun z _ => hσ.2 z
  rw [sum_congr rfl hfull] at hA1
  have hsum : ∑ z ∈ Z, packCount S σ z = ∑ z ∈ Z, k :=
    le_antisymm (sum_le_sum hle) (hA1 ▸ hA2)
  exact (sum_eq_sum_iff_of_le hle).1 hsum

/-- **Lemma 7.2** of the paper (core statement): if `π` is a `k`-packing of `S` packing a process
`p ∈ S` into a fully `k`-packed location, then every location covered by `p` is fully `k`-packed.

The paper derives this from Lemma 7.1 (re-packing along a maximal trail); we use an
augmenting-path argument instead. -/
theorem fullyPacked_of_cov [Fintype Loc] {π : P → Loc} {p : P} {r : Loc}
    (hπ : IsPacking cov k S π) (hp : p ∈ S) (ha : FullyPacked cov k S (π p)) (hr : cov p r) :
    FullyPacked cov k S r := by
  classical
  set Z := univ.filter (fun z => ∃ n, LWalk (resid cov S π) n (π p) z) with hZ
  by_cases hall : ∀ z ∈ Z, packCount S π z = k
  · intro σ hσ
    refine packCount_eq_of_closed (π := π) (Z := Z) ?_ hall hσ r ?_
    · intro q hq hqZ y hy
      obtain ⟨n, w⟩ := (mem_filter.1 hqZ).2
      exact mem_filter.2 ⟨mem_univ _, n + 1, w.tail ⟨q, hq, rfl, hy⟩⟩
    · exact mem_filter.2 ⟨mem_univ _, 1, (LWalk.refl _).tail ⟨p, hp, rfl, hr⟩⟩
  · push Not at hall
    obtain ⟨z, hz, hne⟩ := hall
    obtain ⟨n, w⟩ := (mem_filter.1 hz).2
    have hlt : packCount S π z < k := lt_of_le_of_ne (hπ.2 z) hne
    obtain ⟨σ, hσ, hlt'⟩ := exists_packing_lt_of_walk n π _ z hπ w hlt
    have := ha σ hσ
    omega

/-! ### Auxiliary facts -/

/-- Adding a new process `z` to `S` and packing it into a location `r` that it covers and that is
under-full in `σ` gives a packing of `insert z S`. -/
theorem isPacking_insert [DecidableEq P] {σ : P → Loc} {r : Loc} {z : P}
    (hσ : IsPacking cov k S σ) (hr : packCount S σ r < k) (hz : z ∉ S) (hcov : cov z r) :
    IsPacking cov k (insert z S) (Function.update σ z r) := by
  have hcongr : ∀ r', S.filter (fun p => Function.update σ z r p = r') =
      S.filter (fun p => σ p = r') := by
    intro r'
    apply Finset.filter_congr
    intro p hp
    rw [Function.update_of_ne (by rintro rfl; exact hz hp)]
  refine ⟨fun p hp => ?_, fun r' => ?_⟩
  · rcases Finset.mem_insert.1 hp with rfl | hpS
    · simpa using hcov
    · have hpz : p ≠ z := by rintro rfl; exact hz hpS
      rw [Function.update_of_ne hpz]
      exact hσ.1 p hpS
  · unfold packCount
    rw [Finset.filter_insert, Function.update_self, hcongr]
    have hnot : z ∉ S.filter (fun p => σ p = r') := fun h => hz (Finset.mem_filter.1 h).1
    by_cases h : r = r'
    · subst h
      simp only [ite_true]
      rw [Finset.card_insert_of_notMem hnot]
      exact hr
    · simp only [h, ite_false]
      exact hσ.2 r'

/-- The number of processes equals the sum of the numbers of processes packed per location. -/
theorem card_eq_sum_packCount [Fintype Loc] (S : Finset P) (π : P → Loc) :
    S.card = ∑ r, packCount S π r :=
  card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)

/-- A `k`-packing packs at most `k * |Loc|` processes. -/
theorem card_le_of_isPacking [Fintype Loc] {π : P → Loc} (hπ : IsPacking cov k S π) :
    S.card ≤ k * Fintype.card Loc := by
  rw [card_eq_sum_packCount S π]
  calc ∑ r, packCount S π r ≤ ∑ _r : Loc, k := sum_le_sum (fun r _ => hπ.2 r)
    _ = k * Fintype.card Loc := by simp [mul_comm]

/-- If some location is not fully `k`-packed by `S` (in particular some `k`-packing of `S`
exists), then `S` has fewer than `k * |Loc|` processes. -/
theorem card_lt_of_not_fullyPacked [Fintype Loc] {r : Loc} (h : ¬ FullyPacked cov k S r) :
    S.card + 1 ≤ k * Fintype.card Loc := by
  simp only [FullyPacked, not_forall] at h
  obtain ⟨σ, hσ, hne⟩ := h
  have hlt : packCount S σ r < k := lt_of_le_of_ne (hσ.2 r) hne
  rw [card_eq_sum_packCount S σ, Nat.add_one_le_iff]
  calc ∑ r, packCount S σ r < ∑ _r : Loc, k :=
        sum_lt_sum (fun r _ => hσ.2 r) ⟨r, mem_univ _, hlt⟩
    _ = k * Fintype.card Loc := by simp [mul_comm]

/-- Splitting the processes packed into fully packed locations into two disjoint blocks with
`ℓ` and `k - ℓ` processes in each fully packed location. -/
theorem exists_blocks [Fintype Loc] {π : P → Loc} {ℓ : ℕ} (hπ : IsPacking cov k S π)
    (hℓ : ℓ ≤ k) :
    ∃ T1 T2 : Finset P, T1 ⊆ S ∧ T2 ⊆ S ∧ Disjoint T1 T2 ∧
      (∀ p ∈ T1, FullyPacked cov k S (π p)) ∧ (∀ p ∈ T2, FullyPacked cov k S (π p)) ∧
      ∀ r, FullyPacked cov k S r →
        (T1.filter (fun p => π p = r)).card = ℓ ∧ (T2.filter (fun p => π p = r)).card = k - ℓ := by
  classical
  set F := univ.filter (fun r => FullyPacked cov k S r) with hF
  have hex : ∀ r, ∃ t ⊆ S.filter (fun p => π p = r), r ∈ F → t.card = ℓ := by
    intro r
    by_cases hr : r ∈ F
    · have hk : packCount S π r = k := (mem_filter.1 hr).2 π hπ
      obtain ⟨t, ht, htc⟩ := exists_subset_card_eq (s := S.filter (fun p => π p = r)) (n := ℓ)
        (by unfold packCount at hk; omega)
      exact ⟨t, ht, fun _ => htc⟩
    · exact ⟨∅, empty_subset _, fun h => absurd h hr⟩
  choose c hcsub hccard using hex
  set T1 := F.biUnion c with hT1
  set T2 := (S.filter (fun p => π p ∈ F)) \ T1 with hT2
  have hT1mem : ∀ p, p ∈ T1 ↔ π p ∈ F ∧ p ∈ c (π p) := by
    intro p
    simp only [T1, mem_biUnion]
    constructor
    · rintro ⟨r, hr, hp⟩
      have := mem_filter.1 (hcsub r hp)
      rw [this.2]
      exact ⟨hr, hp⟩
    · rintro ⟨h1, h2⟩
      exact ⟨π p, h1, h2⟩
  have hT1S : T1 ⊆ S := fun p hp => (mem_filter.1 (hcsub _ ((hT1mem p).1 hp).2)).1
  have hfib1 : ∀ r ∈ F, T1.filter (fun p => π p = r) = c r := by
    intro r hr
    ext p
    rw [mem_filter, hT1mem]
    constructor
    · rintro ⟨⟨_, h⟩, rfl⟩
      exact h
    · intro hp
      have := (mem_filter.1 (hcsub r hp)).2
      subst this
      exact ⟨⟨hr, hp⟩, rfl⟩
  refine ⟨T1, T2, hT1S, fun p hp => (mem_filter.1 (mem_sdiff.1 hp).1).1,
    disjoint_sdiff, fun p hp => (mem_filter.1 ((hT1mem p).1 hp).1).2,
    fun p hp => (mem_filter.1 (mem_filter.1 (mem_sdiff.1 hp).1).2).2, ?_⟩
  · intro r hr
    have hrF : r ∈ F := mem_filter.2 ⟨mem_univ _, hr⟩
    have hk : packCount S π r = k := hr π hπ
    refine ⟨by rw [hfib1 r hrF]; exact hccard r hrF, ?_⟩
    have hfib2 : T2.filter (fun p => π p = r) = S.filter (fun p => π p = r) \ c r := by
      ext p
      simp only [T2, mem_filter, mem_sdiff, hT1mem]
      constructor
      · rintro ⟨⟨⟨h1, _⟩, h3⟩, rfl⟩
        exact ⟨⟨h1, rfl⟩, fun h => h3 ⟨hrF, h⟩⟩
      · rintro ⟨⟨h1, rfl⟩, h2⟩
        exact ⟨⟨⟨h1, hrF⟩, fun h => h2 h.2⟩, rfl⟩
    rw [hfib2, card_sdiff_of_subset (hcsub r), hccard r hrF]
    unfold packCount at hk
    rw [hk]

/-- Packings only depend on the covering relation restricted to the processes of `S`. -/
theorem isPacking_congr {cov' : P → Loc → Prop} {π : P → Loc}
    (h : ∀ p ∈ S, ∀ r, cov p r ↔ cov' p r) :
    IsPacking cov k S π ↔ IsPacking cov' k S π := by
  unfold IsPacking
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp => (h p hp _).1 (h1 p hp), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp => (h p hp _).2 (h1 p hp), h2⟩

/-- Full packedness only depends on the covering relation restricted to the processes of `S`. -/
theorem fullyPacked_congr {cov' : P → Loc → Prop} {r : Loc}
    (h : ∀ p ∈ S, ∀ r, cov p r ↔ cov' p r) :
    FullyPacked cov k S r ↔ FullyPacked cov' k S r := by
  unfold FullyPacked
  exact forall_congr' fun π => imp_congr_left (isPacking_congr h)

/-! ### The re-packing step of the paper's proof of Lemma 7.1

The proof of Lemma 7.1 takes a *maximal* trail `r₁ → ⋯ → r_t` in the multigraph with an edge
`g p → h p` for every process `p`, and claims that, for every `1 ≤ j < t`, re-packing `pᵢ` from `rᵢ`
to `rᵢ₊₁` for `j ≤ i < t` packs one process less than `g` in `r_j` and one more in `r_t`. This
fails when the trail revisits `r_t` (i.e. `r_j = r_t` for some `j < t`). Example: locations
`A, B, C` (`0, 1, 2`), processes `p₁, p₂, p₃` (`0, 1, 2`), `g = (A, B, C)`, `h = (B, C, B)`, each
process covering its `g`- and its `h`-location, `k = 2`. The unique maximal trail from `A` is
`A →p₁ B →p₂ C →p₃ B` (`t = 4`), and re-packing from `j = 2` gives `g' = (A, C, B)`, which packs
as many processes as `g` into `r₂ = B`. (The statement of Lemma 7.1 itself is still true: a shortest
path, which has no repeated locations, works; this is what `exists_packing_lt_of_walk` does.) -/

namespace Lemma71Example

/-- The packing `g = (A, B, C)`. -/
def g : Fin 3 → Fin 3 := ![0, 1, 2]
/-- The packing `h = (B, C, B)`. -/
def h : Fin 3 → Fin 3 := ![1, 2, 1]
/-- Every process covers its `g`- and its `h`-location. -/
def exCov (p r : Fin 3) : Prop := r = g p ∨ r = h p

instance : DecidableRel exCov := fun p r => inferInstanceAs (Decidable (r = g p ∨ r = h p))

/-- The result of re-packing from `j = 2` along the trail `A → B → C → B`: `g' = (A, C, B)`. -/
def g' : Fin 3 → Fin 3 := ![0, 2, 1]

end Lemma71Example

open Lemma71Example in
/-- Counterexample to the re-packing claim in the proof of Lemma 7.1 (see the section docstring):
`g` and `h` are `2`-packings, `g` packs more processes than `h` into `A`, the trail
`A →p₁ B →p₂ C →p₃ B` is maximal (all edges out of `A`, `B`, `C` are used) and ends in `B`, where `h`
packs more processes than `g`; re-packing `p₂, p₃` (i.e. from `j = 2`, where `r₂ = B = r₄`) gives
the `2`-packing `g'`, which packs as many processes into `r₂ = B` as `g` does. -/
theorem lemma71_trail_counterexample :
    IsPacking exCov 2 univ g ∧ IsPacking exCov 2 univ h ∧ IsPacking exCov 2 univ g' ∧
      packCount univ h 0 < packCount univ g 0 ∧
      -- the trail `A →p₁ B →p₂ C →p₃ B`: `g pᵢ = rᵢ`, `h pᵢ = rᵢ₊₁`; it uses every edge (every
      -- process), hence is maximal
      (g 0 = 0 ∧ h 0 = 1 ∧ g 1 = 1 ∧ h 1 = 2 ∧ g 2 = 2 ∧ h 2 = 1) ∧
      -- `h` packs more processes than `g` into the end `r₄ = B`
      packCount univ g 1 < packCount univ h 1 ∧
      -- re-packing from `j = 2` does not decrease the count in `r₂ = B`
      packCount univ g' 1 = packCount univ g 1 := by
  unfold IsPacking packCount
  decide

end Cslib.SharedMemory.ComplexityHierarchy
