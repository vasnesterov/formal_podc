import Papers.PODC2019.ConcurrentSketches.Sketch
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Fast Concurrent Data Sketches (PODC 2019): the composable Θ sketch (Algorithm 1)

The paper's running example, the KMV ("`k` minimum values") Θ sketch, as a `Composable` sketch.

Model (derandomised, Section 4: the hash function `hash : E → ℝ` is fixed by the oracle; the
paper's hash values lie in `[0, 1]`). We read Algorithm 1 with **set semantics**:
"`sampleSet, init k 1's`" is the set `{1}`, so

* `Θ = max(sampleSet)` (`theta`), initially `1`;
* `update(a)` (lines 9–13): if `h(a) ≥ Θ` do nothing, else insert `h(a)` and keep the `k`
  smallest samples (`kSmallest`);
* `query() = est = (|sampleSet| - 1) / Θ` (lines 7, 13);
* `merge` (lines 15–18): keep the `k` smallest samples of the union;
* `snapshot` copies `est`, `calcHint = Θ`, `shouldAdd(H, a) = (h(a) < H)` (lines 19–26).

With set semantics the estimate is the exact number of distinct hash values while fewer than `k`
of them have been seen, and the KMV estimator `(k - 1)/Θ` afterwards.

Main declarations:

* `kSmallest k s`: the `k` smallest elements of a finset of a linear order (via `rank`), with
  `card_kSmallest`, `kSmallest_union_left`, `kSmallest_union`, `kSmallest_insert_of_le_rank`.
* `thetaSketch k hash`: the sequential sketch; `thetaSketch_run`: `run A` is the set of the `k`
  smallest elements of `{1} ∪ h(A)`.
* `theta_run_append_le`: Θ is monotonically non-increasing along a stream.
* `thetaSketch_run_filter`: the pre-filtering law (if `h(a) ≥ Θ(run A)`, `a` can be dropped from
  any later point of the stream).
* `thetaComposable k hash`: Algorithm 1 as a `Composable` sketch.
* Accuracy (Section 5.3): `thetaSketch_query_exact` (exact while fewer than `k` distinct hash
  values have been seen), `thetaSketch_query_of_le` (`(k - 1)/Θ` once `k` or more have been
  seen), and `thetaSketch_not_exact_k` (with exactly `k` distinct values the answer need not be
  exact: the paper's "perfect accuracy in streams with up to `k` unique elements" holds for this
  pseudocode only up to `k - 1`).
-/

namespace Podc.ConcurrentSketches

/-! ## The `k` smallest elements of a finset -/

-- CSLib candidate: `rank`, `kSmallest` and their lemmas (general finset combinatorics).

section KSmallest

variable {α : Type*} [LinearOrder α]

/-- The number of elements of `s` strictly below `x`. -/
def rank (s : Finset α) (x : α) : ℕ := (s.filter (· < x)).card

/-- The `k` smallest elements of `s`: those with fewer than `k` elements of `s` below them. -/
def kSmallest (k : ℕ) (s : Finset α) : Finset α := s.filter (fun x => rank s x < k)

variable {k : ℕ} {s t : Finset α} {x y : α}

lemma mem_kSmallest : x ∈ kSmallest k s ↔ x ∈ s ∧ rank s x < k := Finset.mem_filter

lemma kSmallest_subset : kSmallest k s ⊆ s := Finset.filter_subset _ _

lemma rank_mono (h : s ⊆ t) (x : α) : rank s x ≤ rank t x :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma rank_mono_right (s : Finset α) (h : x ≤ y) : rank s x ≤ rank s y :=
  Finset.card_le_card (Finset.monotone_filter_right s fun _ _ hz => lt_of_lt_of_le hz h)

lemma rank_lt_rank (hy : y ∈ s) (h : y < x) : rank s y < rank s x := by
  apply Finset.card_lt_card
  refine ⟨Finset.monotone_filter_right s fun _ _ hz => hz.trans h, fun hsub => ?_⟩
  have := hsub (Finset.mem_filter.2 ⟨hy, h⟩)
  exact lt_irrefl _ (Finset.mem_filter.1 this).2

lemma rank_lt_card (hx : x ∈ s) : rank s x < s.card := by
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
  exact lt_irrefl _ (Finset.mem_filter.1 (hsub hx)).2

lemma rank_injOn (s : Finset α) : Set.InjOn (rank s) s := by
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (rank_lt_rank ha h).ne hab
  · exact (rank_lt_rank hb h).ne hab.symm

lemma image_rank (s : Finset α) : s.image (rank s) = Finset.range s.card := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hn
    exact Finset.mem_range.2 (rank_lt_card ha)
  · rw [Finset.card_range, Finset.card_image_of_injOn (rank_injOn s)]

/-- `kSmallest k s` has `min k |s|` elements. -/
lemma card_kSmallest (k : ℕ) (s : Finset α) : (kSmallest k s).card = min k s.card := by
  have h1 : (kSmallest k s).card = ((kSmallest k s).image (rank s)).card :=
    (Finset.card_image_of_injOn ((rank_injOn s).mono (by simp [kSmallest_subset]))).symm
  have h2 : (kSmallest k s).image (rank s) = Finset.range (min k s.card) := by
    rw [kSmallest, ← Finset.filter_image (p := (· < k)), image_rank]
    ext n; simp [lt_min_iff, and_comm]
  rw [h1, h2, Finset.card_range]

lemma kSmallest_eq_self (h : s.card ≤ k) : kSmallest k s = s :=
  Finset.filter_true_of_mem fun _ hx => (rank_lt_card hx).trans_le h

/-- If `k` elements of `s` lie below `x`, then all `k` smallest elements of `s` do. -/
lemma le_rank_kSmallest (h : k ≤ rank s x) : k ≤ rank (kSmallest k s) x := by
  have hsub : kSmallest k s ⊆ (kSmallest k s).filter (· < x) := by
    intro y hy
    refine Finset.mem_filter.2 ⟨hy, ?_⟩
    by_contra hxy
    have := rank_mono_right s (not_lt.1 hxy)
    have := (mem_kSmallest.1 hy).2
    omega
  have hc := Finset.card_le_card hsub
  have hcs : k ≤ s.card := h.trans (Finset.card_le_card (Finset.filter_subset _ _))
  rw [card_kSmallest, min_eq_left hcs] at hc
  exact hc

/-- Dropping elements that are not among the `k` smallest does not change the `k` smallest. -/
lemma kSmallest_eq_of_subset (hts : t ⊆ s) (hkt : kSmallest k s ⊆ t) :
    kSmallest k t = kSmallest k s := by
  ext x
  simp only [mem_kSmallest]
  constructor
  · rintro ⟨hxt, hr⟩
    refine ⟨hts hxt, ?_⟩
    by_contra hge
    have := (le_rank_kSmallest (not_lt.1 hge)).trans (rank_mono hkt x)
    omega
  · rintro ⟨hxs, hr⟩
    exact ⟨hkt (mem_kSmallest.2 ⟨hxs, hr⟩), (rank_mono hts x).trans_lt hr⟩

lemma kSmallest_union_left (k : ℕ) (X Y : Finset α) :
    kSmallest k (kSmallest k X ∪ Y) = kSmallest k (X ∪ Y) := by
  refine kSmallest_eq_of_subset (Finset.union_subset_union kSmallest_subset le_rfl) ?_
  intro x hx
  obtain ⟨hxXY, hr⟩ := mem_kSmallest.1 hx
  rcases Finset.mem_union.1 hxXY with hX | hY
  · exact Finset.mem_union_left _
      (mem_kSmallest.2 ⟨hX, (rank_mono Finset.subset_union_left x).trans_lt hr⟩)
  · exact Finset.mem_union_right _ hY

/-- Merging the `k` smallest of `X` with the `k` smallest of `Y` gives the `k` smallest of
`X ∪ Y`. -/
lemma kSmallest_union (k : ℕ) (X Y : Finset α) :
    kSmallest k (kSmallest k X ∪ kSmallest k Y) = kSmallest k (X ∪ Y) := by
  rw [kSmallest_union_left, Finset.union_comm, kSmallest_union_left, Finset.union_comm]

lemma kSmallest_insert (k : ℕ) (v : α) (X : Finset α) :
    kSmallest k (insert v (kSmallest k X)) = kSmallest k (insert v X) := by
  rw [← Finset.union_singleton, kSmallest_union_left, Finset.union_singleton]

/-- Inserting an element with at least `k` smaller elements does not change the `k` smallest. -/
lemma kSmallest_insert_of_le_rank {v : α} {X : Finset α} (h : k ≤ rank X v) :
    kSmallest k (insert v X) = kSmallest k X := by
  refine (kSmallest_eq_of_subset (Finset.subset_insert v X) ?_).symm
  intro x hx
  obtain ⟨hx, hr⟩ := mem_kSmallest.1 hx
  rcases Finset.mem_insert.1 hx with rfl | hX
  · have := rank_mono (Finset.subset_insert x X) x
    omega
  · exact hX

end KSmallest

/-! ## The Θ sketch -/

/-- `Θ = max(sampleSet)` (line 12); `1` on the empty set (never reached from `init` if `0 < k`). -/
noncomputable def theta (s : Finset ℝ) : ℝ := if h : s.Nonempty then s.max' h else 1

/-- `est = (|sampleSet| - 1) / Θ` (line 13). -/
noncomputable def est (s : Finset ℝ) : ℝ := ((s.card : ℝ) - 1) / theta s

lemma theta_eq_max' {s : Finset ℝ} (h : s.Nonempty) : theta s = s.max' h := by
  exact dite_eq_left h

lemma le_theta {s : Finset ℝ} {x : ℝ} (hx : x ∈ s) : x ≤ theta s := by
  rw [theta_eq_max' ⟨x, hx⟩]; exact s.le_max' x hx

lemma theta_eq_one {s : Finset ℝ} (h1 : (1 : ℝ) ∈ s) (hs : ∀ x ∈ s, x ≤ 1) : theta s = 1 := by
  rw [theta_eq_max' ⟨1, h1⟩]
  exact le_antisymm (Finset.max'_le _ _ _ hs) (s.le_max' 1 h1)

lemma theta_le_one {s : Finset ℝ} (hs : ∀ x ∈ s, x ≤ 1) : theta s ≤ 1 := by
  unfold theta; split_ifs with h
  · exact Finset.max'_le _ _ _ hs
  · exact le_rfl

variable {E : Type}

/-- The derandomised sequential KMV Θ sketch (Algorithm 1, lines 1–13) with parameter `k` and
hash function `hash` (fixed by the oracle). The sample set is a set of reals, initially `{1}`. -/
noncomputable abbrev thetaSketch (k : ℕ) (hash : E → ℝ) : Sketch where
  State := Finset ℝ
  Elem := E
  Arg := Unit
  Val := ℝ
  init := {1}
  update s a := if theta s ≤ hash a then s else kSmallest k (insert (hash a) s)
  query s _ := est s

/-- The hash values seen in `A`, together with the initial sample `1`. -/
noncomputable def hashes (hash : E → ℝ) (A : List E) : Finset ℝ := insert 1 (A.map hash).toFinset

lemma one_mem_hashes (hash : E → ℝ) (A : List E) : (1 : ℝ) ∈ hashes hash A :=
  Finset.mem_insert_self _ _

lemma hashes_le_one {hash : E → ℝ} (hle : ∀ a, hash a ≤ 1) (A : List E) :
    ∀ x ∈ hashes hash A, x ≤ 1 := by
  intro x hx
  simp only [hashes, Finset.mem_insert, List.mem_toFinset, List.mem_map] at hx
  rcases hx with rfl | ⟨a, -, rfl⟩
  · exact le_rfl
  · exact hle a

lemma hashes_append (hash : E → ℝ) (A B : List E) :
    hashes hash (A ++ B) = hashes hash A ∪ hashes hash B := by
  ext x; simp [hashes]

lemma hashes_cons (hash : E → ℝ) (a : E) (B : List E) :
    hashes hash (a :: B) = insert (hash a) (hashes hash B) := by
  ext x; simp [hashes]; tauto

lemma hashes_concat (hash : E → ℝ) (A : List E) (a : E) :
    hashes hash (A ++ [a]) = insert (hash a) (hashes hash A) := by
  ext x; simp [hashes]; tauto

/-- Key fact behind both the update rule and the filter: if `v ≤ 1` and `Θ(kSmallest X) ≤ v`,
where `1 ∈ X`, then `v` is not among the `k` smallest of any `Y ⊇ X`. -/
lemma kSmallest_insert_of_theta_le {k : ℕ} {X Y : Finset ℝ} {v : ℝ} (h1 : (1 : ℝ) ∈ X)
    (hv : v ≤ 1) (hθ : theta (kSmallest k X) ≤ v) (hXY : X ⊆ Y) :
    kSmallest k (insert v Y) = kSmallest k Y := by
  by_cases hvY : v ∈ Y
  · rw [Finset.insert_eq_of_mem hvY]
  apply kSmallest_insert_of_le_rank
  have h1k : (1 : ℝ) ∉ kSmallest k X := by
    intro h
    have := le_theta h
    have hv1 : v ≠ 1 := fun h' => hvY (hXY (h' ▸ h1))
    exact hv1 (le_antisymm hv (this.trans hθ))
  have hk : k ≤ rank X 1 := by
    by_contra hlt
    exact h1k (mem_kSmallest.2 ⟨h1, not_le.1 hlt⟩)
  refine (le_rank_kSmallest hk).trans (Finset.card_le_card ?_)
  intro z hz
  obtain ⟨hzK, -⟩ := Finset.mem_filter.1 hz
  refine Finset.mem_filter.2 ⟨hXY (kSmallest_subset hzK), ?_⟩
  refine lt_of_le_of_ne ((le_theta hzK).trans hθ) ?_
  rintro rfl
  exact hvY (hXY (kSmallest_subset hzK))

section Run

variable {k : ℕ} {hash : E → ℝ}

/-- The state of the Θ sketch after ingesting `A`: the `k` smallest elements of `{1} ∪ h(A)`. -/
theorem thetaSketch_run (hk : 0 < k) (hle : ∀ a, hash a ≤ 1) (A : List E) :
    (thetaSketch k hash).run A = kSmallest k (hashes hash A) := by
  induction A using List.reverseRecOn with
  | nil =>
    show ({1} : Finset ℝ) = _
    rw [kSmallest_eq_self] <;> simp [hashes]; omega
  | append_singleton A a ih =>
    rw [Sketch.run_concat, ih, hashes_concat]
    show (if theta _ ≤ hash a then _ else _) = _
    split_ifs with h
    · exact (kSmallest_insert_of_theta_le (one_mem_hashes hash A) (hle a) h
        le_rfl).symm
    · exact kSmallest_insert k _ _

/-- Θ is monotonically non-increasing: ingesting more elements never increases it. -/
theorem theta_run_append_le (hk : 0 < k) (hle : ∀ a, hash a ≤ 1) (A B : List E) :
    theta ((thetaSketch k hash).run (A ++ B)) ≤ theta ((thetaSketch k hash).run A) := by
  rw [thetaSketch_run hk hle, thetaSketch_run hk hle]
  have hXY : hashes hash A ⊆ hashes hash (A ++ B) := by
    rw [hashes_append]; exact Finset.subset_union_left
  set X := hashes hash A
  set Y := hashes hash (A ++ B)
  have hY1 : ∀ y ∈ Y, y ≤ 1 := hashes_le_one hle _
  -- every element of `kSmallest k Y` is at most `Θ(kSmallest k X)`
  have key : ∀ y ∈ kSmallest k Y, y ≤ theta (kSmallest k X) := by
    intro y hy
    by_contra hlt
    rw [not_le] at hlt
    have h1 : (1 : ℝ) ∉ kSmallest k X := fun h =>
      absurd ((le_theta h).trans_lt hlt) (not_lt.2 (hY1 y (kSmallest_subset hy)))
    have hk1 : k ≤ rank X 1 := by
      by_contra h'
      exact h1 (mem_kSmallest.2 ⟨one_mem_hashes hash A, not_le.1 h'⟩)
    have : k ≤ rank Y y := by
      refine (le_rank_kSmallest hk1).trans (Finset.card_le_card ?_)
      intro z hz
      obtain ⟨hzK, -⟩ := Finset.mem_filter.1 hz
      exact Finset.mem_filter.2 ⟨hXY (kSmallest_subset hzK), (le_theta hzK).trans_lt hlt⟩
    have := (mem_kSmallest.1 hy).2
    omega
  have hne : (kSmallest k Y).Nonempty := by
    rw [← Finset.card_pos, card_kSmallest]
    have : 0 < Y.card := Finset.card_pos.2 ⟨1, one_mem_hashes hash _⟩
    omega
  rw [theta_eq_max' hne]
  exact Finset.max'_le _ _ _ key

/-- The pre-filtering law of the Θ sketch: if `h(a) ≥ Θ` in a sketch summarising `A`, then `a`
can be dropped from any later point of the stream. -/
theorem thetaSketch_run_filter (hk : 0 < k) (hle : ∀ a, hash a ≤ 1) (A : List E) (a : E)
    (ha : theta ((thetaSketch k hash).run A) ≤ hash a) (B₁ B₂ : List E) :
    (thetaSketch k hash).run (A ++ B₁ ++ a :: B₂) = (thetaSketch k hash).run (A ++ B₁ ++ B₂) := by
  rw [thetaSketch_run hk hle] at ha ⊢
  rw [thetaSketch_run hk hle]
  have e1 : hashes hash (A ++ B₁ ++ a :: B₂) = insert (hash a) (hashes hash (A ++ B₁ ++ B₂)) := by
    simp only [hashes_append, hashes_cons]
    ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
  rw [e1]
  refine kSmallest_insert_of_theta_le (one_mem_hashes hash A) (hle a) ha ?_
  rw [hashes_append, hashes_append]
  exact Finset.subset_union_left.trans Finset.subset_union_left

end Run

/-- Algorithm 1: the composable KMV Θ sketch. `merge` keeps the `k` smallest samples of the
union, `snapshot` copies `est`, `calcHint` returns `Θ`, and `shouldAdd(H, a) = (h(a) < H)`.
The hash values must lie in `(-∞, 1]` (the paper: `[0, 1]`). -/
noncomputable def thetaComposable (k : ℕ) (hk : 0 < k) (hash : E → ℝ) (hle : ∀ a, hash a ≤ 1) :
    Composable where
  toSketch := thetaSketch k hash
  merge s t := kSmallest k (s ∪ t)
  Snap := ℝ
  snapshot s := est s
  snapQuery x _ := x
  Hint := ℝ
  calcHint := theta
  shouldAdd θ a := decide (hash a < θ)
  merge_run A B := by
    change kSmallest k ((thetaSketch k hash).run A ∪ (thetaSketch k hash).run B) =
      (thetaSketch k hash).run (A ++ B)
    rw [thetaSketch_run hk hle, thetaSketch_run hk hle, thetaSketch_run hk hle, kSmallest_union,
      hashes_append]
  snapQuery_snapshot _ _ := rfl
  shouldAdd_spec A a h B₁ B₂ := by
    simp only [decide_eq_false_iff_not, not_lt] at h
    exact thetaSketch_run_filter hk hle A a h B₁ B₂

/-! ## Accuracy on small streams (Section 5.3) -/

section Accuracy

variable {k : ℕ} {hash : E → ℝ}

/-- Section 5.3: the sequential Θ sketch answers with perfect accuracy while **fewer than `k`**
distinct hash values (all `< 1`) have been seen: the estimate is the number of distinct hash
values of the stream. -/
theorem thetaSketch_query_exact (hk : 0 < k) (hle : ∀ a, hash a ≤ 1) (A : List E)
    (hA : ∀ a ∈ A, hash a < 1) (hn : (A.map hash).toFinset.card < k) :
    (thetaSketch k hash).query ((thetaSketch k hash).run A) () = (A.map hash).toFinset.card := by
  have h1 : (1 : ℝ) ∉ (A.map hash).toFinset := by
    simp only [List.mem_toFinset, List.mem_map, not_exists, not_and]
    exact fun a ha h => (hA a ha).ne h
  have hc : (hashes hash A).card = (A.map hash).toFinset.card + 1 := Finset.card_insert_of_notMem h1
  change est ((thetaSketch k hash).run A) = _
  rw [thetaSketch_run hk hle, kSmallest_eq_self (by omega), est,
    theta_eq_one (one_mem_hashes hash A) (hashes_le_one hle A), hc]
  push_cast; ring

/-- Once at least `k` distinct hash values (all `< 1`) have been seen, the sample set holds `k`
values and the estimate is the KMV estimator `(k - 1)/Θ`, where `Θ` is the `k`-th smallest
hash value. -/
theorem thetaSketch_query_of_le (hk : 0 < k) (hle : ∀ a, hash a ≤ 1) (A : List E)
    (hA : ∀ a ∈ A, hash a < 1) (hn : k ≤ (A.map hash).toFinset.card) :
    ((thetaSketch k hash).run A).card = k ∧ (1 : ℝ) ∉ (thetaSketch k hash).run A ∧
    (thetaSketch k hash).query ((thetaSketch k hash).run A) () =
      ((k : ℝ) - 1) / theta ((thetaSketch k hash).run A) := by
  have h1 : (1 : ℝ) ∉ (A.map hash).toFinset := by
    simp only [List.mem_toFinset, List.mem_map, not_exists, not_and]
    exact fun a ha h => (hA a ha).ne h
  have hc : (hashes hash A).card = (A.map hash).toFinset.card + 1 := Finset.card_insert_of_notMem h1
  have hcard : ((thetaSketch k hash).run A).card = k := by
    rw [thetaSketch_run hk hle, card_kSmallest, hc]; omega
  refine ⟨hcard, ?_, ?_⟩
  · rw [thetaSketch_run hk hle, mem_kSmallest, not_and, not_lt]
    intro _
    -- all `(A.map hash).toFinset` lies below `1`
    have : (A.map hash).toFinset ⊆ (hashes hash A).filter (· < 1) := by
      intro x hx
      refine Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem hx, ?_⟩
      simp only [List.mem_toFinset, List.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact hA a ha
    exact hn.trans (Finset.card_le_card this)
  · change est _ = _
    rw [est, hcard]

/-- The paper's claim "the sequential Θ sketch answers queries with perfect accuracy in streams
with up to `k` unique elements" fails for Algorithm 1 at exactly `k` unique elements: with
`k = 1` and one element hashed to `1/2`, the estimate is `0`, not `1`. -/
theorem thetaSketch_not_exact_k :
    let hash : Unit → ℝ := fun _ => 1 / 2
    (([()].map hash).toFinset.card = 1) ∧
      (thetaSketch 1 hash).query ((thetaSketch 1 hash).run [()]) () = 0 := by
  intro hash
  have hle : ∀ a, hash a ≤ 1 := fun _ => by norm_num [hash]
  have hA : ∀ a ∈ [()], hash a < 1 := fun _ _ => by norm_num [hash]
  have hc : ([()].map hash).toFinset.card = 1 := by simp
  refine ⟨hc, ?_⟩
  rw [(thetaSketch_query_of_le (k := 1) one_pos hle [()] hA hc.ge).2.2]
  simp

end Accuracy

end Podc.ConcurrentSketches
