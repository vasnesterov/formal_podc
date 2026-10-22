import Papers.PODC2015.RingColoringAverage.Lemma3
import Papers.PODC2015.RingColoringAverage.Linial
import Papers.PODC2015.RingColoringAverage.Minimal

/-!
# Theorem 1: the average complexity of 3-colouring a ring is `Ω(log* n)`

Paper, Theorem 1 and its proof (end of §3). Given a minimal 4-colouring algorithm `A` and a
radius `R` with `tower (2R) ≤ n / 2`, we build the permutation `π` of the identifiers
`{0, …, n - 1}` as in the paper (`exists_slices`): while more than `n / 2` identifiers remain,
Linial's bound (`Alg.exists_lt_radAt_four`) gives a ring on the remaining identifiers with a node of
radius `≥ R`; its slice of `2R + 1` identifiers (the `R`-ball around that node) is appended to `π`
and removed. The rest of the identifiers follow in increasing order. In the ring `π`, the centre
of each slice still has radius `≥ R` (same `R`-ball), so by Lemma 3 the slice contributes
`≥ R + ⌊R/2⌋ (R - ⌊R/2⌋) ≥ (2R + 1) R / 8` to the total radius, and the slices cover at least
`n / 2` nodes.

* `sum_radAt_ge_of_isMinimal`: `n R ≤ 16 ∑_v r(v)` for minimal 4-colouring algorithms;
* `theorem_1_four`, `theorem_1_three`: for every valid 4- (resp. 3-)colouring algorithm and every
  `n ≥ 3` there is an identifier assignment (a permutation of `{0, …, n-1}`) on the `n`-ring with
  `n · ⌊(log*(n/2) - 1)/2⌋ ≤ 16 ∑_v r(v)`;
* `theorem_1`: the same with `n (log* n - 3) ≤ 32 ∑_v r(v)`, and `theorem_1_average` the average
  form `(log* n - 3) / 32 ≤ (∑_v r(v)) / n`, i.e. the average radius is `Ω(log* n)`.
-/

namespace Podc.RingColoringAverage

/-- The view of position `p` of a list of identifiers (offset `j` carries `L[p + j]`, `0` outside
the list). -/
def posView (L : List ℕ) (p : ℕ) : ℤ → ℕ := fun j => L.getD ((p : ℤ) + j).toNat 0

/-- Position `p` of `L` is *slow* for `A`: `A` does not stop before radius `R` there. -/
def Slow (A : Alg (Fin 4)) (R : ℕ) (L : List ℕ) (p : ℕ) : Prop :=
  ∀ s < R, A.out s (posView L p) = none

theorem le_tower (k : ℕ) : k + 1 ≤ Nat.tower k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.tower_succ]
    have := Nat.lt_two_pow_self (n := Nat.tower k)
    omega

theorem slow_append {A : Alg (Fin 4)} {R : ℕ} {w L : List ℕ} {p : ℕ} (hp : R ≤ p)
    (h : Slow A R L p) : Slow A R (w ++ L) (w.length + p) := by
  intro s hs
  rw [← h s hs]
  apply A.out_congr
  intro j hj
  rw [abs_le] at hj
  simp only [posView]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

theorem lt_rad_of_slow {A : Alg (Fin 4)} {R : ℕ} {f : ℤ → ℕ} (hf : A.Stops f)
    (h : ∀ t < R, A.out t f = none) : R ≤ A.rad f := by
  by_contra hlt
  have := Alg.rad_spec hf
  rw [h _ (not_le.1 hlt)] at this
  simp at this

/-- The slicing construction of the proof of Theorem 1: from a set `S` of identifiers, as long as
more than `m₀` identifiers remain, cut out a slice of `2R + 1` identifiers whose centre is slow. -/
theorem exists_slices {A : Alg (Fin 4)} (hA : A.Valid) {R m₀ : ℕ} (hR : 1 ≤ R)
    (hm₀ : Nat.tower (2 * R) ≤ m₀) (S : Finset ℕ) :
    ∃ (L : List ℕ) (q : ℕ), L.Nodup ∧ (∀ a ∈ L, a ∈ S) ∧ L.length = q * (2 * R + 1) ∧
      S.card ≤ m₀ + q * (2 * R + 1) ∧ ∀ i < q, Slow A R L (i * (2 * R + 1) + R) := by
  induction hc : S.card using Nat.strong_induction_on generalizing S with
  | _ c ih =>
  by_cases hS : S.card ≤ m₀
  · exact ⟨[], 0, by simp, by simp, by simp, by omega, by simp⟩
  rw [not_le] at hS
  obtain ⟨Rg, hn, hids, v, hv⟩ :=
    A.exists_lt_radAt_four hA S (R - 1) (by rw [show 2 * (R - 1) + 2 = 2 * R by omega]; omega)
  have h2R : 2 * R + 1 ≤ S.card := (le_tower (2 * R)).trans (hm₀.trans hS.le) |>.trans' le_rfl
    |> fun h => by have := le_tower (2 * R); omega
  let w : List ℕ := List.ofFn (fun i : Fin (2 * R + 1) => Rg.id (v - R + i))
  have hwnd : w.Nodup := by
    rw [List.nodup_ofFn]
    intro i i' he
    by_contra hne
    refine Rg.id_ne_of_lt (i := v - R + i) (j := v - R + i') ?_ ?_ he
    · intro h; apply hne; ext; omega
    · rw [abs_lt]; constructor <;> omega
  have hwS : w.toFinset ⊆ S := by
    intro a ha
    simp only [List.mem_toFinset, w, List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact hids _
  have hwl : w.length = 2 * R + 1 := by simp [w]
  set S' := S \ w.toFinset with hS'
  have hcard : S'.card + (2 * R + 1) = S.card := by
    rw [Finset.card_sdiff_of_subset hwS, List.toFinset_card_of_nodup hwnd, hwl]; omega
  obtain ⟨L', q', hnd', hsub', hlen', hcard', hslow'⟩ := ih S'.card (by omega) S' rfl
  refine ⟨w ++ L', q' + 1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hwnd, hnd', ?_⟩
    intro a ha b hb hab
    subst hab
    have := hsub' _ hb
    simp [S', ha] at this
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hwS (List.mem_toFinset.2 ha)
    · exact (Finset.mem_sdiff.1 (hsub' a ha)).1
  · simp [hwl, hlen']; ring
  · rw [← hc, ← hcard]; nlinarith
  · intro i hi
    rcases i with _ | i
    · -- the new slice: same `R - 1`-view as node `v` of `Rg`
      intro s hs
      have hnone : A.out s (Rg.view v) = none := Alg.out_eq_none_of_lt (by unfold Alg.radAt at hv; omega)
      rw [← hnone]
      apply A.out_congr
      intro j hj
      rw [abs_le] at hj
      simp only [posView, zero_mul, zero_add]
      have hlt : ((R : ℤ) + j).toNat < w.length := by rw [hwl]; omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt]
      simp only [w, List.getElem_ofFn, IdRing.view_apply]
      congr 1; omega
    · have := slow_append (w := w) (by omega : R ≤ i * (2 * R + 1) + R) (hslow' i (by omega))
      rw [hwl] at this
      convert this using 1; ring

/-- Arithmetic: `(2R + 1) R ≤ 8 (R + ⌊R/2⌋ (R - ⌊R/2⌋))`. -/
theorem eight_mul_bound (r : ℕ) : (2 * r + 1) * r ≤ 8 * (r + r / 2 * (r - r / 2)) := by
  obtain ⟨h, rfl | rfl⟩ := Nat.even_or_odd' r
  · have : 2 * h / 2 = h := by omega
    rw [this, show 2 * h - h = h by omega]; nlinarith
  · have : (2 * h + 1) / 2 = h := by omega
    rw [this, show 2 * h + 1 - h = h + 1 by omega]; nlinarith

theorem ofList_id_lt (l : List ℕ) (hl : l.Nodup) (h3 : 3 ≤ l.length) (n : ℕ)
    (hn : ∀ a ∈ l, a < n) (j : ℤ) : (IdRing.ofList l hl h3).id j < n := by
  have hpos : (0 : ℤ) < l.length := by omega
  have hi : (j % l.length).toNat < l.length := by
    have := Int.emod_lt_of_pos j hpos; have := Int.emod_nonneg j hpos.ne'; omega
  simp only [IdRing.ofList, List.getD_eq_getElem _ _ hi]
  exact hn _ (List.getElem_mem _)

variable {A : Alg (Fin 4)}

/-- Core of the proof of **Theorem 1** for a minimal 4-colouring algorithm: if
`tower (2R) ≤ n / 2`, some permutation of the identifiers `{0, …, n - 1}` on the `n`-ring has
total radius at least `n R / 16`. -/
theorem sum_radAt_ge_of_isMinimal (hA : A.IsMinimal) (n : ℕ) (hn : 3 ≤ n) (R : ℕ)
    (hR : Nat.tower (2 * R) ≤ n / 2) :
    ∃ Rg : IdRing, Rg.n = n ∧ (∀ j, Rg.id j < n) ∧
      n * R ≤ 16 * ∑ v ∈ Finset.Ico (0 : ℤ) n, A.radAt Rg v := by
  rcases Nat.eq_zero_or_pos R with rfl | hR1
  · refine ⟨IdRing.ofList (List.range n) (List.nodup_range) (by simpa), by simp, ?_, by simp⟩
    exact ofList_id_lt _ _ _ n (fun a ha => List.mem_range.1 ha)
  obtain ⟨L, q, hnd, hsub, hlen, hcard, hslow⟩ :=
    exists_slices hA.1 hR1 hR (Finset.range n)
  simp only [Finset.card_range] at hcard
  have hLn : ∀ a ∈ L, a < n := fun a ha => Finset.mem_range.1 (hsub a ha)
  set π := L ++ (List.range n).filter (fun a => a ∉ L) with hπ
  have hπnd : π.Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, List.nodup_range.filter _, fun a ha b hb hab => ?_⟩
    subst hab; simp [ha] at hb
  have hπmem : ∀ a, a ∈ π ↔ a < n := by
    intro a
    simp only [π, List.mem_append, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro (h | h); exacts [hLn a h, h.1]
    · intro h; by_cases ha : a ∈ L; exacts [Or.inl ha, Or.inr ⟨h, ha⟩]
  have hπlen : π.length = n := by
    have hperm : π.Perm (List.range n) :=
      (List.perm_ext_iff_of_nodup hπnd List.nodup_range).2 fun a => by
        rw [hπmem, List.mem_range]
    rw [hperm.length_eq, List.length_range]
  have hLlen : L.length ≤ n := by
    rw [← hπlen, hπ, List.length_append]; omega
  let Rg := IdRing.ofList π hπnd (by omega)
  have hRn : 2 * R + 1 ≤ n := by
    have := le_tower (2 * R); omega
  refine ⟨Rg, hπlen, ofList_id_lt _ _ _ n (fun a ha => (hπmem a).1 ha), ?_⟩
  set h := R / 2
  -- the centres of the slices are slow in `Rg`
  have hcentre : ∀ i < q, R ≤ A.radAt Rg ((i * (2 * R + 1) + R : ℕ) : ℤ) := by
    intro i hi
    refine lt_rad_of_slow (hA.1.stops Rg _) fun s hs => ?_
    rw [← hslow i hi s hs]
    apply A.out_congr
    intro j hj
    rw [abs_le] at hj
    have hq : i * (2 * R + 1) + R + R < q * (2 * R + 1) := by
      have := Nat.mul_le_mul_right (2 * R + 1) (Nat.succ_le_of_lt hi); rw [Nat.succ_mul] at this
      omega
    have hidx : ((i * (2 * R + 1) + R : ℕ) + j : ℤ).toNat < L.length := by
      rw [hlen]
      generalize i * (2 * R + 1) + R = P at hq ⊢
      generalize q * (2 * R + 1) = Q at hq ⊢
      omega
    have hidxπ : ((i * (2 * R + 1) + R : ℕ) + j : ℤ).toNat < π.length := by
      rw [hπ, List.length_append]; omega
    simp only [IdRing.view_apply, posView]
    rw [show ((i * (2 * R + 1) + R : ℕ) : ℤ) + j =
        (((i * (2 * R + 1) + R : ℕ) + j : ℤ).toNat : ℤ) by omega]
    rw [IdRing.ofList_id _ _ _ _ hidxπ, Int.toNat_natCast, List.getD_eq_getElem _ _ hidx]
    simp only [π, List.getElem_append_left hidx]
  -- the windows of radius `h` around the centres
  let W : ℕ → Finset ℤ := fun i =>
    (Finset.Icc (-(h : ℤ)) h).image (fun j => ((i * (2 * R + 1) + R : ℕ) : ℤ) + j)
  have hW : ∀ i < q, R + h * (R - h) ≤ ∑ v ∈ W i, A.radAt Rg v := by
    intro i hi
    rw [Finset.sum_image (fun a _ b _ hab => by simpa using hab)]
    exact lemma_3_sum hA Rg _ R (hcentre i hi) (by show 2 * R + 1 ≤ π.length; rw [hπlen]; exact hRn)
  have hWsub : ∀ i < q, W i ⊆ Finset.Ico (0 : ℤ) n := by
    intro i hi v hv
    simp only [W, Finset.mem_image, Finset.mem_Icc] at hv
    obtain ⟨j, ⟨hj1, hj2⟩, rfl⟩ := hv
    have hq : i * (2 * R + 1) + R + R < q * (2 * R + 1) := by
      have := Nat.mul_le_mul_right (2 * R + 1) (Nat.succ_le_of_lt hi); rw [Nat.succ_mul] at this
      omega
    have hhR : h ≤ R := Nat.div_le_self R 2
    have hPR : R ≤ i * (2 * R + 1) + R := Nat.le_add_left _ _
    rw [← hlen] at hq
    simp only [Finset.mem_Ico]
    generalize i * (2 * R + 1) + R = P at hq hPR ⊢
    omega
  have hWrange : ∀ i, ∀ v ∈ W i, (i * (2 * R + 1) : ℤ) ≤ v ∧ v < (i + 1) * (2 * R + 1) := by
    intro i v hv
    simp only [W, Finset.mem_image, Finset.mem_Icc] at hv
    obtain ⟨j, ⟨hj1, hj2⟩, rfl⟩ := hv
    have : (h : ℤ) ≤ R := by exact_mod_cast Nat.div_le_self R 2
    push_cast; constructor <;> nlinarith
  have hdisj : (↑(Finset.range q) : Set ℕ).PairwiseDisjoint W := by
    intro i _ i' _ hii'
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨a1, a2⟩ := hWrange i v hv
    obtain ⟨b1, b2⟩ := hWrange i' v hv'
    rcases lt_or_gt_of_ne hii' with hlt | hlt
    · have : ((i + 1 : ℕ) : ℤ) * (2 * R + 1) ≤ (i' : ℤ) * (2 * R + 1) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hlt) (by positivity)
      push_cast at this; linarith
    · have : ((i' + 1 : ℕ) : ℤ) * (2 * R + 1) ≤ (i : ℤ) * (2 * R + 1) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hlt) (by positivity)
      push_cast at this; linarith
  have hsum : q * (R + h * (R - h)) ≤ ∑ v ∈ Finset.Ico (0 : ℤ) n, A.radAt Rg v := by
    calc q * (R + h * (R - h)) = ∑ i ∈ Finset.range q, (R + h * (R - h)) := by simp
      _ ≤ ∑ i ∈ Finset.range q, ∑ v ∈ W i, A.radAt Rg v :=
          Finset.sum_le_sum fun i hi => hW i (Finset.mem_range.1 hi)
      _ = ∑ v ∈ (Finset.range q).biUnion W, A.radAt Rg v := (Finset.sum_biUnion hdisj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.biUnion_subset.2 fun i hi =>
          hWsub i (Finset.mem_range.1 hi))
  have h8 := eight_mul_bound R
  have : n ≤ 2 * (q * (2 * R + 1)) := by omega
  calc n * R ≤ 2 * (q * (2 * R + 1)) * R := Nat.mul_le_mul_right _ this
    _ = 2 * q * ((2 * R + 1) * R) := by ring
    _ ≤ 2 * q * (8 * (R + h * (R - h))) := Nat.mul_le_mul_left _ h8
    _ = 16 * (q * (R + h * (R - h))) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hsum

/-- **Theorem 1** of [Feuilloley, PODC 2015] for 4-colouring algorithms, explicit form: for every
valid 4-colouring algorithm and every `n ≥ 3` there is a permutation of the identifiers
`{0, …, n - 1}` on the `n`-ring such that the total radius is at least
`n ⌊(log*(n/2) - 1)/2⌋ / 16`. -/
theorem theorem_1_four (A : Alg (Fin 4)) (hA : A.Valid) (n : ℕ) (hn : 3 ≤ n) :
    ∃ Rg : IdRing, Rg.n = n ∧ (∀ j, Rg.id j < n) ∧
      n * ((Nat.logStar (n / 2) - 1) / 2) ≤ 16 * ∑ v ∈ Finset.Ico (0 : ℤ) n, A.radAt Rg v := by
  obtain ⟨B, hB, hBA⟩ := A.exists_isMinimal_le hA
  have hR : Nat.tower (2 * ((Nat.logStar (n / 2) - 1) / 2)) ≤ n / 2 :=
    (Nat.le_logStar_iff (by omega)).1 (by omega)
  obtain ⟨Rg, h1, h2, h3⟩ := sum_radAt_ge_of_isMinimal hB n hn _ hR
  exact ⟨Rg, h1, h2, h3.trans (Nat.mul_le_mul_left _ (Finset.sum_le_sum fun v _ => hBA Rg v))⟩

/-- **Theorem 1** of [Feuilloley, PODC 2015], explicit form, for 3-colouring algorithms. -/
theorem theorem_1_three (A : Alg (Fin 3)) (hA : A.Valid) (n : ℕ) (hn : 3 ≤ n) :
    ∃ Rg : IdRing, Rg.n = n ∧ (∀ j, Rg.id j < n) ∧
      n * ((Nat.logStar (n / 2) - 1) / 2) ≤ 16 * ∑ v ∈ Finset.Ico (0 : ℤ) n, A.radAt Rg v := by
  obtain ⟨Rg, h1, h2, h3⟩ :=
    theorem_1_four (A.map Fin.castSucc) (hA.map (Fin.castSucc_injective 3)) n hn
  exact ⟨Rg, h1, h2, by simpa only [Alg.radAt, Alg.rad_map] using h3⟩

theorem two_mul_le_two_pow (x : ℕ) : 2 * x ≤ 2 ^ x := by
  induction x with
  | zero => simp
  | succ x ih =>
    rcases x with _ | x
    · simp
    · have := Nat.one_le_two_pow (n := x + 1)
      rw [pow_succ]; omega

/-- `log* n ≤ log* (n / 2) + 1`. -/
theorem logStar_le_logStar_half_add_one (n : ℕ) : Nat.logStar n ≤ Nat.logStar (n / 2) + 1 := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [Nat.logStar_of_le_one (by omega)]; omega
  rw [Nat.logStar_of_one_lt (by omega)]
  have : Nat.log 2 n ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have h1 := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have h2 := two_mul_le_two_pow (Nat.log 2 n)
    omega
  have := Nat.logStar_mono this
  omega

/-- **Theorem 1** of [Feuilloley, PODC 2015]: for every valid 3-colouring algorithm (not knowing
`n`) and every `n ≥ 3`, some permutation of the identifiers `{0, …, n - 1}` on the `n`-ring
gives total radius at least `n (log* n - 3) / 32`. -/
theorem theorem_1 (A : Alg (Fin 3)) (hA : A.Valid) (n : ℕ) (hn : 3 ≤ n) :
    ∃ Rg : IdRing, Rg.n = n ∧ (∀ j, Rg.id j < n) ∧
      n * (Nat.logStar n - 3) ≤ 32 * ∑ v ∈ Finset.Ico (0 : ℤ) n, A.radAt Rg v := by
  obtain ⟨Rg, h1, h2, h3⟩ := theorem_1_three A hA n hn
  refine ⟨Rg, h1, h2, ?_⟩
  have := logStar_le_logStar_half_add_one n
  have : Nat.logStar n - 3 ≤ 2 * ((Nat.logStar (n / 2) - 1) / 2) := by omega
  calc n * (Nat.logStar n - 3) ≤ n * (2 * ((Nat.logStar (n / 2) - 1) / 2)) :=
        Nat.mul_le_mul_left _ this
    _ = 2 * (n * ((Nat.logStar (n / 2) - 1) / 2)) := by ring
    _ ≤ _ := by omega

/-- **Theorem 1** of [Feuilloley, PODC 2015], average form: the worst-case (over identifier
assignments) average radius of a 3-colouring algorithm on the `n`-ring is at least
`(log* n - 3) / 32`, hence `Ω(log* n)`. -/
theorem theorem_1_average (A : Alg (Fin 3)) (hA : A.Valid) (n : ℕ) (hn : 3 ≤ n) :
    ∃ Rg : IdRing, Rg.n = n ∧ (∀ j, Rg.id j < n) ∧
      ((Nat.logStar n : ℚ) - 3) / 32 ≤
        (∑ v ∈ Finset.Ico (0 : ℤ) n, A.radAt Rg v : ℕ) / (n : ℚ) := by
  obtain ⟨Rg, h1, h2, h3⟩ := theorem_1 A hA n hn
  refine ⟨Rg, h1, h2, ?_⟩
  have hn' : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [div_le_div_iff₀ (by norm_num) hn']
  have hle : ((Nat.logStar n : ℚ) - 3) ≤ ((Nat.logStar n - 3 : ℕ) : ℚ) := by
    rcases Nat.lt_or_ge (Nat.logStar n) 3 with h | h
    · have : (Nat.logStar n : ℚ) < 3 := by exact_mod_cast h
      rw [Nat.sub_eq_zero_of_le h.le]; simp; linarith
    · push_cast [h]; linarith
  have h3' : ((n * (Nat.logStar n - 3) : ℕ) : ℚ) ≤
      ((32 * ∑ v ∈ Finset.Ico (0 : ℤ) n, A.radAt Rg v : ℕ) : ℚ) := by
    exact_mod_cast h3
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat] at h3'
  have := mul_le_mul_of_nonneg_right hle hn'.le
  linarith

end Podc.RingColoringAverage
