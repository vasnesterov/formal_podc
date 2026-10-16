import Papers.PODC2025.BAWithPredictions.Defs

/-!
# Byzantine Agreement with Predictions — classification (Section 6)

* `classify`: Algorithm 2 (majority vote on the received prediction vectors) as a function of the
  vectors received in the voting round; `card_mis_mul_le`: **Lemma 1** in exact form
  `k_A · (⌈n/2⌉ - f) ≤ B` (Observations 1 and 2 are `obs1`, `obs2`).
* `pos c j`: the position of `j` in the ordering `π(c)` (1-indexed): processes classified honest
  first, then those classified faulty, each group by increasing identifier.
* Lemmas 2–6 and Corollary 1 of the paper: `pos_mem_Icc` (positions of properly classified
  honest processes), `pos_gt_of_false` / `corollary1`, `lemma4`, `lemma5` (core sets),
  `lemma6`; `exists_clean_block` (Lemmas 15 and 19: a block of positions in which no honest process
  has a faulty process).

All statements are about an arbitrary family of classification vectors `c i` (only those of honest
processes `i ∉ F` matter) and the set `mis F c` of processes misclassified by some honest process
(`k_A = |mis F c|`).

The proofs avoid the paper's index manipulations: with `U` the properly classified honest
processes and `W = U ∪ mis` (honest or misclassified), for every honest `i` and every `j`
classified honest by `i`, `rank U j ≤ pos (c i) j ≤ rank W j`, where `rank X j = |{x ∈ X | x ≤ j}|`.
-/

set_option linter.unusedSectionVars false

namespace BAWithPredictions

open Finset

variable {P : Type*} [Fintype P] [LinearOrder P]

/-! ### Ranks -/

/-- `rank X j`: the number of elements of `X` that are `≤ j`. -/
def rank (X : Finset P) (j : P) : ℕ := (X.filter (· ≤ j)).card

theorem rank_mono {X Y : Finset P} (h : X ⊆ Y) (j : P) : rank X j ≤ rank Y j :=
  card_le_card (filter_subset_filter _ h)

theorem rank_pos {X : Finset P} {j : P} (hj : j ∈ X) : 1 ≤ rank X j :=
  card_pos.mpr ⟨j, mem_filter.mpr ⟨hj, le_rfl⟩⟩

theorem rank_le_card (X : Finset P) (j : P) : rank X j ≤ X.card :=
  card_le_card (filter_subset _ _)

theorem rank_lt_rank {X : Finset P} {x y : P} (_hx : x ∈ X) (hy : y ∈ X) (hxy : x < y) :
    rank X x < rank X y := by
  refine card_lt_card ⟨fun z hz => ?_, fun h => ?_⟩
  · simp only [mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.trans hxy.le⟩
  · have := (mem_filter.mp (h (mem_filter.mpr ⟨hy, le_rfl⟩))).2
    exact absurd hxy (not_lt.mpr this)

theorem rank_injOn (X : Finset P) : Set.InjOn (rank X) X := by
  intro x hx y hy h
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact absurd h (rank_lt_rank hx hy hxy).ne
  · exact hxy
  · exact absurd h (rank_lt_rank hy hx hxy).ne'

/-- At most `r` elements of `X` have rank `≤ r`. -/
theorem card_rank_le (X : Finset P) (r : ℕ) : (X.filter fun x => rank X x ≤ r).card ≤ r := by
  have h : ((X.filter fun x => rank X x ≤ r).image (rank X)) ⊆ Icc 1 r := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    rw [mem_filter] at hx
    exact mem_Icc.mpr ⟨rank_pos hx.1, hx.2⟩
  rw [← card_image_of_injOn ((rank_injOn X).mono fun x hx => (mem_filter.mp hx).1)]
  simpa using card_le_card h

/-- At most `|X| - r` elements of `X` have rank `> r`. -/
theorem card_rank_gt (X : Finset P) (r : ℕ) :
    (X.filter fun x => r < rank X x).card ≤ X.card - r := by
  have h : ((X.filter fun x => r < rank X x).image (rank X)) ⊆ Icc (r + 1) X.card := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    rw [mem_filter] at hx
    exact mem_Icc.mpr ⟨hx.2, rank_le_card X x⟩
  rw [← card_image_of_injOn ((rank_injOn X).mono fun x hx => (mem_filter.mp hx).1)]
  simpa using card_le_card h

/-! ### Positions in `π(c)` -/

/-- The set of processes classified honest by `c`. -/
def ones (c : P → Bool) : Finset P := univ.filter fun j => c j = true

/-- The position of `j` in `π(c)` (1-indexed): the processes classified honest by `c`, in
increasing order, followed by the processes classified faulty, in increasing order. -/
def pos (c : P → Bool) (j : P) : ℕ :=
  if c j = true then rank (ones c) j
  else (ones c).card + rank (univ.filter fun j => c j = false) j

theorem pos_of_true {c : P → Bool} {j : P} (h : c j = true) : pos c j = rank (ones c) j := by
  simp [pos, h]

theorem pos_of_false {c : P → Bool} {j : P} (h : c j = false) :
    (ones c).card < pos c j := by
  simp only [pos, h, Bool.false_eq_true, ↓reduceIte]
  have := rank_pos (X := univ.filter fun j => c j = false) (j := j) (by simp [h])
  omega

theorem pos_injective (c : P → Bool) : Function.Injective (pos c) := by
  intro x y hxy
  cases hx : c x <;> cases hy : c y
  · simp only [pos, hx, hy, Bool.false_eq_true, ↓reduceIte, Nat.add_left_cancel_iff] at hxy
    exact rank_injOn _ (by simp [hx]) (by simp [hy]) hxy
  · have h1 := pos_of_false hx
    have h2 : pos c y ≤ (ones c).card := by rw [pos_of_true hy]; exact rank_le_card _ _
    omega
  · have h1 := pos_of_false hy
    have h2 : pos c x ≤ (ones c).card := by rw [pos_of_true hx]; exact rank_le_card _ _
    omega
  · rw [pos_of_true hx, pos_of_true hy] at hxy
    exact rank_injOn _ (by simp [ones, hx]) (by simp [ones, hy]) hxy

theorem one_le_pos (c : P → Bool) (j : P) : 1 ≤ pos c j := by
  cases h : c j
  · have := pos_of_false h; omega
  · rw [pos_of_true h]; exact rank_pos (by simp [ones, h])

theorem pos_le_card (c : P → Bool) (j : P) : pos c j ≤ Fintype.card P := by
  cases h : c j
  · simp only [pos, h, Bool.false_eq_true, ↓reduceIte]
    have h1 := rank_le_card (univ.filter fun j => c j = false) j
    have h2 := card_filter_add_card_filter_not (s := (univ : Finset P)) (fun j => c j = true)
    simp only [Bool.not_eq_true] at h2
    rw [card_univ] at h2
    unfold ones; omega
  · rw [pos_of_true h]; exact (rank_le_card _ _).trans (card_le_univ _)

/-! ### Misclassification -/

variable (F : Finset P) (c : P → P → Bool)

/-- The processes misclassified by at least one honest process (`∪ M_i`); `k_A = |mis F c|`. -/
def mis : Finset P := univ.filter fun j => ∃ i ∉ F, c i j ≠ correctPred F j

/-- Honest processes properly classified by every honest process. -/
def goodH : Finset P := univ.filter fun j => j ∉ F ∧ j ∉ mis F c

/-- Honest processes and misclassified (faulty) processes. -/
def hw : Finset P := univ.filter fun j => j ∉ F ∨ j ∈ mis F c

variable {F c}

theorem true_of_goodH {i j : P} (hi : i ∉ F) (hj : j ∈ goodH F c) : c i j = true := by
  simp only [goodH, mis, mem_filter, mem_univ, true_and, not_exists, not_and, not_not] at hj
  have := hj.2 i hi
  simpa [hj.1] using this

theorem mem_hw_of_true {i j : P} (hi : i ∉ F) (h : c i j = true) : j ∈ hw F c := by
  simp only [hw, mis, mem_filter, mem_univ, true_and]
  by_cases hj : j ∈ F
  · exact Or.inr ⟨i, hi, by simp [h, hj]⟩
  · exact Or.inl hj

theorem goodH_subset_ones {i : P} (hi : i ∉ F) : goodH F c ⊆ ones (c i) := fun j hj => by
  simp [ones, true_of_goodH hi hj]

theorem ones_subset_hw {i : P} (hi : i ∉ F) : ones (c i) ⊆ hw F c := fun j hj => by
  simp only [ones, mem_filter, mem_univ, true_and] at hj
  exact mem_hw_of_true hi hj

theorem goodH_subset_hw : goodH F c ⊆ hw F c := fun j hj => by
  simp only [goodH, hw, mem_filter, mem_univ, true_and] at hj ⊢; exact Or.inl hj.1

theorem card_hw_eq : (hw F c).card = (goodH F c).card + (mis F c).card := by
  rw [← card_union_of_disjoint]
  · congr 1; ext j; by_cases h1 : j ∈ F <;> by_cases h2 : j ∈ mis F c <;> simp [hw, goodH, h1, h2]
  · rw [disjoint_left]; intro j h1 h2; simp only [goodH, mem_filter] at h1; exact h1.2.2 h2

theorem card_goodH_ge : Fintype.card P - F.card - (mis F c).card ≤ (goodH F c).card := by
  have h1 : (univ.filter fun j => j ∉ F) ⊆ goodH F c ∪ mis F c := by
    intro j hj
    by_cases h : j ∈ mis F c
    · exact mem_union_right _ h
    · exact mem_union_left _ (by simp only [mem_filter, mem_univ, true_and] at hj; simp [goodH, hj, h])
  have h2 := card_le_card h1
  have h3 := card_union_le (goodH F c) (mis F c)
  have h4 : (univ.filter fun j => j ∉ F).card = Fintype.card P - F.card := by
    rw [filter_not, card_sdiff_of_subset (subset_univ _)]; simp
  omega

/-- **Positions of processes classified honest** (the key estimate behind Lemmas 2–6): if honest
`i` classifies `j` as honest, then `rank U j ≤ pos (c i) j ≤ rank W j`. -/
theorem pos_mem_Icc {i j : P} (hi : i ∉ F) (hj : c i j = true) :
    rank (goodH F c) j ≤ pos (c i) j ∧ pos (c i) j ≤ rank (hw F c) j := by
  rw [pos_of_true hj]
  exact ⟨rank_mono (goodH_subset_ones hi) j, rank_mono (ones_subset_hw hi) j⟩

/-- A process classified faulty by an honest process comes after all properly classified honest
processes. -/
theorem pos_gt_of_false {i j : P} (hi : i ∉ F) (hj : c i j = false) :
    (goodH F c).card < pos (c i) j :=
  lt_of_le_of_lt (card_le_card (goodH_subset_ones hi)) (pos_of_false hj)

/-- **Corollary 1** (from Lemma 3). If the faulty process `j` is in one of the first
`n - t - k_A` positions of `π(c_i)` for an honest `i` (with `|F| ≤ t`), then `i` misclassifies
`j` (as honest). -/
theorem corollary1 {t : ℕ} (hF : F.card ≤ t) {i j : P} (hi : i ∉ F)
    (hpos : pos (c i) j ≤ Fintype.card P - t - (mis F c).card) : c i j = true := by
  by_contra h
  have := pos_gt_of_false hi (Bool.eq_false_iff.mpr h)
  have := card_goodH_ge (F := F) (c := c)
  omega

/-- **Lemma 4** (in the form used by Lemma 15). If an honest process misclassifies the faulty
process `j` as honest, the position of `j` in its ordering lies in the interval
`[rank U j + 1, rank U j + k_A]`, which does not depend on the honest process. -/
theorem lemma4 {i j : P} (hi : i ∉ F) (hjF : j ∈ F) (hj : c i j = true) :
    rank (goodH F c) j + 1 ≤ pos (c i) j ∧ pos (c i) j ≤ rank (goodH F c) j + (mis F c).card := by
  rw [pos_of_true hj]
  have hjU : j ∉ goodH F c := by simp [goodH, hjF]
  constructor
  · have : insert j ((goodH F c).filter (· ≤ j)) ⊆ (ones (c i)).filter (· ≤ j) := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · simp [ones, hj]
      · simp only [mem_filter] at hx ⊢; exact ⟨goodH_subset_ones hi hx.1, hx.2⟩
    have h := card_le_card this
    rw [card_insert_of_notMem (by simp [hjU])] at h
    exact h
  · have h1 := rank_mono (ones_subset_hw (c := c) hi) j
    have h2 : (hw F c).filter (· ≤ j) ⊆ (goodH F c).filter (· ≤ j) ∪ mis F c := by
      intro x hx
      simp only [mem_filter, mem_union, hw, goodH, mem_univ, true_and] at hx ⊢
      by_cases h : x ∈ mis F c
      · exact Or.inr h
      · exact Or.inl ⟨⟨hx.1.resolve_right h, h⟩, hx.2⟩
    have h3 := card_le_card h2
    have h4 := card_union_le ((goodH F c).filter (· ≤ j)) (mis F c)
    unfold rank at h1 ⊢
    omega

/-- Two honest processes that both misclassify the faulty `j` place it at positions differing by
less than `k_A` (**Lemma 4**). -/
theorem lemma4' {i i' j : P} (hi : i ∉ F) (hi' : i' ∉ F) (hjF : j ∈ F) (hj : c i j = true)
    (hj' : c i' j = true) : pos (c i) j ≤ pos (c i') j + ((mis F c).card - 1) := by
  have := lemma4 hi hjF hj
  have := lemma4 hi' hjF hj'
  omega

/-- **Lemma 5 (core sets).** For positions `ℓ ≤ r ≤ n - |F|`, there is a set `G` of honest
processes, of size at least `r - ℓ + 1 - k_A`, which lie in positions `ℓ … r` of `π(c_i)` for
every honest `i`. (The paper assumes `ℓ + k_A - 1 < r ≤ n - t - k_A`.) -/
theorem lemma5 {ℓ r : ℕ} (hℓ : 1 ≤ ℓ) (hr : r + F.card ≤ Fintype.card P) :
    ∃ G : Finset P, (∀ j ∈ G, j ∉ F) ∧ r + 1 - ℓ - (mis F c).card ≤ G.card ∧
      ∀ i ∉ F, ∀ j ∈ G, ℓ ≤ pos (c i) j ∧ pos (c i) j ≤ r := by
  refine ⟨(goodH F c).filter fun j => ℓ ≤ rank (goodH F c) j ∧ rank (hw F c) j ≤ r,
    fun j hj => ?_, ?_, fun i hi j hj => ?_⟩
  · exact (mem_filter.mp (mem_filter.mp hj).1).2.1
  · have h1 : goodH F c ⊆
        ((goodH F c).filter fun j => ℓ ≤ rank (goodH F c) j ∧ rank (hw F c) j ≤ r) ∪
        (((goodH F c).filter fun j => rank (goodH F c) j ≤ ℓ - 1) ∪
          ((hw F c).filter fun j => r < rank (hw F c) j)) := by
      intro j hj
      by_cases h1 : ℓ ≤ rank (goodH F c) j
      · by_cases h2 : rank (hw F c) j ≤ r
        · exact mem_union_left _ (mem_filter.mpr ⟨hj, h1, h2⟩)
        · exact mem_union_right _ (mem_union_right _
            (mem_filter.mpr ⟨goodH_subset_hw hj, by omega⟩))
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hj, by omega⟩))
    have h2 := card_le_card h1
    have h3 := card_union_le
        ((goodH F c).filter fun j => ℓ ≤ rank (goodH F c) j ∧ rank (hw F c) j ≤ r)
        (((goodH F c).filter fun j => rank (goodH F c) j ≤ ℓ - 1) ∪
          ((hw F c).filter fun j => r < rank (hw F c) j))
    have h4 := card_union_le ((goodH F c).filter fun j => rank (goodH F c) j ≤ ℓ - 1)
        ((hw F c).filter fun j => r < rank (hw F c) j)
    have h5 := card_rank_le (goodH F c) (ℓ - 1)
    have h6 := card_rank_gt (hw F c) r
    have h7 : (hw F c).card = (goodH F c).card + (mis F c).card := card_hw_eq
    have h8 : Fintype.card P - F.card ≤ (hw F c).card := by
      have : (univ.filter fun j => j ∉ F) ⊆ hw F c := fun j hj => by
        simp only [mem_filter, mem_univ, true_and] at hj; simp [hw, hj]
      have h := card_le_card this
      rw [filter_not, card_sdiff_of_subset (subset_univ _)] at h; simpa using h
    omega
  · simp only [mem_filter] at hj
    have := pos_mem_Icc hi (true_of_goodH hi hj.1)
    omega

/-- **Lemma 6** (in the form used in Theorem 5 and Lemma 24). If `r ≤ n - |F| - k_A`, at most
`r + k_H` honest processes occur among the first `r` positions of `π(c_i)` for some honest `i`
(`k_H ≤ k_A`). The paper's hypothesis `r ≤ n - t - k_H` (kept as `_hr`) is not needed. -/
theorem lemma6 {r : ℕ} (_hr : r + F.card + (mis F c).card ≤ Fintype.card P) :
    (univ.filter fun j => j ∉ F ∧ ∃ i ∉ F, pos (c i) j ≤ r).card ≤
      r + ((mis F c).filter (· ∉ F)).card := by
  have hU := card_goodH_ge (F := F) (c := c)
  have h1 : (univ.filter fun j => j ∉ F ∧ ∃ i ∉ F, pos (c i) j ≤ r) ⊆
      ((goodH F c).filter fun j => rank (goodH F c) j ≤ r) ∪ (mis F c).filter (· ∉ F) := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    obtain ⟨hjF, i, hi, hp⟩ := hj
    by_cases hm : j ∈ mis F c
    · exact mem_union_right _ (mem_filter.mpr ⟨hm, hjF⟩)
    · have hjU : j ∈ goodH F c := by simp [goodH, hjF, hm]
      have := (pos_mem_Icc hi (true_of_goodH hi hjU)).1
      exact mem_union_left _ (mem_filter.mpr ⟨hjU, by omega⟩)
  exact (card_le_card h1).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_rank_le _ _) _))

/-- **Lemmas 15 and 19.** Split the first `m · s` positions into `m` consecutive blocks of `s`
positions. If `2 |mis F c ∩ F| < m`, `k_A ≤ s` and `m s ≤ n - t - k_A`, then there is a block
`φ < m` such that no honest process has a faulty process in the positions of block `φ`. -/
theorem exists_clean_block {t s m : ℕ} (hF : F.card ≤ t)
    (hm : 2 * ((mis F c).filter (· ∈ F)).card < m)
    (hks : (mis F c).card ≤ s) (hms : m * s ≤ Fintype.card P - t - (mis F c).card) :
    ∃ φ < m, ∀ i ∉ F, ∀ j ∈ F, ¬ (φ * s + 1 ≤ pos (c i) j ∧ pos (c i) j ≤ φ * s + s) := by
  classical
  -- the blocks a misclassified faulty process can occupy
  obtain ⟨bad, hbad_eq⟩ : ∃ bad : Finset ℕ, bad =
      ((mis F c).filter (· ∈ F)).image (fun j => rank (goodH F c) j / s) ∪
      ((mis F c).filter (· ∈ F)).image (fun j => rank (goodH F c) j / s + 1) := ⟨_, rfl⟩
  have hbad : bad.card < m := by
    have h1 := card_union_le (((mis F c).filter (· ∈ F)).image (fun j => rank (goodH F c) j / s))
      (((mis F c).filter (· ∈ F)).image (fun j => rank (goodH F c) j / s + 1))
    have h2 := card_image_le (s := (mis F c).filter (· ∈ F)) (f := fun j => rank (goodH F c) j / s)
    have h3 := card_image_le (s := (mis F c).filter (· ∈ F))
      (f := fun j => rank (goodH F c) j / s + 1)
    rw [← hbad_eq] at h1
    omega
  obtain ⟨φ, hφ, hφbad⟩ : ∃ φ ∈ range m, φ ∉ bad := by
    by_contra h
    push Not at h
    have := card_le_card h
    simp at this; omega
  refine ⟨φ, mem_range.mp hφ, fun i hi j hj hpos => ?_⟩
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; omega
    · exact h
  have hφm := mem_range.mp hφ
  have hle : pos (c i) j ≤ Fintype.card P - t - (mis F c).card := by
    have : φ * s + s ≤ m * s := by
      have := Nat.mul_le_mul_right s (Nat.succ_le_of_lt hφm); rw [Nat.succ_mul] at this; exact this
    omega
  have htrue := corollary1 hF hi hle
  have hjM : j ∈ (mis F c).filter (· ∈ F) := by
    simp only [mis, mem_filter, mem_univ, true_and]
    exact ⟨⟨i, hi, by simp [htrue, hj]⟩, hj⟩
  obtain ⟨h1, h2⟩ := lemma4 hi hj htrue
  generalize ha : rank (goodH F c) j = a at h1 h2
  have hq1 := Nat.div_mul_le_self a s
  have hq2 : a < a / s * s + s := Nat.lt_div_mul_add hs
  have e1 : φ * s < (a / s + 2) * s := by rw [Nat.add_mul]; omega
  have e2 : a / s * s < (φ + 1) * s := by rw [Nat.add_mul, one_mul]; omega
  have f1 := Nat.lt_of_mul_lt_mul_right e1
  have f2 := Nat.lt_of_mul_lt_mul_right e2
  apply hφbad
  rw [hbad_eq]
  rcases (by omega : φ = a / s ∨ φ = a / s + 1) with h | h
  · exact mem_union_left _ (mem_image.mpr ⟨j, hjM, by rw [ha, h]⟩)
  · exact mem_union_right _ (mem_image.mpr ⟨j, hjM, by rw [ha, h]⟩)

/-! ### Algorithm 2 and Lemma 1 -/

/-- **Algorithm 2** (classification by majority vote), for one process: given the prediction
vectors received from every process (`none` if nothing was received), classify `j` as honest iff at
least `⌈(n+1)/2⌉` received vectors predict that `j` is honest. -/
def classify (rcv : P → Option (P → Bool)) (j : P) : Bool :=
  decide ((Fintype.card P + 2) / 2 ≤ (univ.filter fun s => ∃ a, rcv s = some a ∧ a j = true).card)

/-- A reception of the voting round is *honest-consistent* if every honest sender's vector was
received correctly. -/
def VoteRcv (F : Finset P) (a : P → P → Bool) (rcv : P → Option (P → Bool)) : Prop :=
  ∀ s ∉ F, rcv s = some (a s)

/-- The honest processes whose prediction about `j` is incorrect. -/
def wrongAbout (F : Finset P) (a : P → P → Bool) (j : P) : Finset P :=
  univ.filter fun s => s ∉ F ∧ a s j ≠ correctPred F j

theorem card_honest (F : Finset P) : (univ.filter fun j => j ∉ F).card = Fintype.card P - F.card := by
  rw [filter_not, card_sdiff_of_subset (subset_univ _)]; simp

/-- **Observations 1 and 2.** If some honest process misclassifies `j` after Algorithm 2, then at
least `⌈n/2⌉ - f` honest processes received an incorrect prediction about `j`. -/
theorem obs12 {a : P → P → Bool} {rcv : P → P → Option (P → Bool)}
    (hrcv : ∀ i ∉ F, VoteRcv F a (rcv i)) {i j : P} (hi : i ∉ F)
    (hmis : classify (rcv i) j ≠ correctPred F j) :
    (Fintype.card P + 1) / 2 - F.card ≤ (wrongAbout F a j).card := by
  classical
  set n := Fintype.card P
  set S := univ.filter fun s => ∃ b, rcv i s = some b ∧ b j = true
  by_cases hjF : j ∈ F
  · -- Observation 1: `j` faulty classified honest
    have hc : (n + 2) / 2 ≤ S.card := by
      simp only [classify, correctPred, hjF, not_true_eq_false, decide_false, ne_eq,
        decide_eq_false_iff_not, not_not] at hmis
      exact hmis
    have h1 : S ⊆ wrongAbout F a j ∪ F := by
      intro s hs
      by_cases hsF : s ∈ F
      · exact mem_union_right _ hsF
      · refine mem_union_left _ ?_
        simp only [S, mem_filter, mem_univ, true_and] at hs
        obtain ⟨b, hb, hbj⟩ := hs
        rw [hrcv i hi s hsF] at hb
        cases hb
        simp [wrongAbout, hsF, hjF, hbj]
    have := (card_le_card h1).trans (card_union_le _ _)
    omega
  · -- Observation 2: `j` honest classified faulty
    have hc : S.card < (n + 2) / 2 := by
      simp only [classify, correctPred, hjF, not_false_eq_true, decide_true, ne_eq,
        decide_eq_true_eq, not_le] at hmis
      exact hmis
    have h1 : univ.filter (fun s => s ∉ F) ⊆ S ∪ wrongAbout F a j := by
      intro s hs
      simp only [mem_filter, mem_univ, true_and] at hs
      cases hb : a s j
      · exact mem_union_right _ (by simp [wrongAbout, hs, hjF, hb])
      · exact mem_union_left _ (by simp only [S, mem_filter, mem_univ, true_and]; exact ⟨a s, hrcv i hi s hs, hb⟩)
    have := (card_le_card h1).trans (card_union_le _ _)
    rw [card_honest] at this
    omega

theorem sum_card_wrongAbout (F : Finset P) (a : P → P → Bool) :
    ∑ j, (wrongAbout F a j).card = wrongBits F a := by
  classical
  unfold wrongBits wrongBitsOf wrongAbout
  simp only [card_filter]
  rw [Finset.sum_comm, sum_filter]
  refine sum_congr rfl fun s _ => ?_
  by_cases hs : s ∈ F <;> simp [hs]

/-- **Lemma 1** (exact form). After Algorithm 2, the number `k_A` of processes misclassified by
some honest process satisfies `k_A · (⌈n/2⌉ - f) ≤ B`. Hence, if `f ≤ (1/2 - ε) n`, then
`k_A ≤ B / (ε n) = O(B/n)`. -/
theorem card_mis_mul_le {a : P → P → Bool} {rcv : P → P → Option (P → Bool)}
    (hrcv : ∀ i ∉ F, VoteRcv F a (rcv i)) :
    (mis F (fun i => classify (rcv i))).card * ((Fintype.card P + 1) / 2 - F.card) ≤
      wrongBits F a := by
  rw [← sum_card_wrongAbout, ← smul_eq_mul, ← sum_const]
  calc ∑ _j ∈ mis F (fun i => classify (rcv i)), ((Fintype.card P + 1) / 2 - F.card)
      ≤ ∑ j ∈ mis F (fun i => classify (rcv i)), (wrongAbout F a j).card := by
        refine sum_le_sum fun j hj => ?_
        simp only [mis, mem_filter, mem_univ, true_and] at hj
        obtain ⟨i, hi, h⟩ := hj
        exact obs12 hrcv hi h
    _ ≤ ∑ j, (wrongAbout F a j).card := sum_le_sum_of_subset (subset_univ _)

end BAWithPredictions
