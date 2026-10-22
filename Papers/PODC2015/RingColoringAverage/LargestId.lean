import Papers.PODC2015.RingColoringAverage.Model

/-!
# Section 2: the largest-ID problem on a ring

Paper: [Feuilloley, *Brief Announcement: Average Complexity for the LOCAL Model*, PODC 2015],
§2 "Algorithm for the largest ID in a cycle". In the *largest-ID* problem every node outputs
`Yes` (`true`) iff it carries the largest identifier of the ring (`LargestId.Correct`).

* **Worst case is linear** (`LargestId.half_le_radAt_of_max`, `LargestId.worst_case`): for every
  correct algorithm, on every ring the node with the largest identifier has radius `≥ ⌊n/2⌋`:
  if its window `[-r, r]` with `2r + 1 < n` misses a node, giving that node a larger identifier
  produces a ring where the same view must answer `No`.
* **Logarithmic average** (`LargestId.straightforward`, `LargestId.straightforward_correct`,
  `LargestId.sum_radAt_straightforward_le`): the straightforward algorithm — increase the radius
  until a larger identifier is seen (answer `No`) or until the whole ring has been seen, detected
  by a repeated identifier in the window (answer `Yes`) — is correct, and on every ring of size
  `n` its total radius is at most `n (⌊log₂ n⌋ + 1)`, i.e. its average radius is `O(log n)`.

The paper argues the `O(n log n)` total via the recurrence
`a(p) = max_{1 ≤ k ≤ ⌈p/2⌉} {k + a(k-1) + a(p-k)}` and OEIS A000788 (`a(p) = Θ(p log p)`),
without proof. We only define the recurrence (`segA`) and check that its first values are those of
A000788 (`segA_eq_A000788`); we do **not** formalize the claim that `a(p)` is the maximal total
radius on a segment, nor its asymptotics. Instead we prove the bound directly: two nodes of radius
`≥ d` are at cyclic distance `≥ d` (each is the maximum of its window of radius `d - 1`), so at
most `n / d` nodes have radius `≥ d`, and `∑_v r(v) = ∑_{d ≥ 1} #{v | r(v) ≥ d} ≤ ∑_{d=1}^{n} n/d`,
which a dyadic grouping bounds by `n (⌊log₂ n⌋ + 1)`.
-/

namespace Podc.RingColoringAverage

namespace LargestId

/-- An algorithm solves the *largest-ID* problem: it stops at every node of every ring, and a
node outputs `true` (Yes) iff its identifier is the largest of the ring. -/
structure Correct (A : Alg Bool) : Prop where
  stops : ∀ (R : IdRing) (v : ℤ), A.Stops (R.view v)
  spec : ∀ (R : IdRing) (v : ℤ), A.outAt R v = true ↔ ∀ w, R.id w ≤ R.id v

/-! ### Ring lemmas -/

theorem id_eq_emod (R : IdRing) (w : ℤ) : R.id w = R.id ((w % R.n).toNat) := by
  have hn : (0 : ℤ) < R.n := by exact_mod_cast R.n_pos
  rw [R.id_eq_iff, Int.toNat_of_nonneg (Int.emod_nonneg _ hn.ne')]
  exact ⟨w / R.n, by have := Int.emod_add_mul_ediv w R.n; linarith⟩

/-- An upper bound on all identifiers of a ring. -/
noncomputable def bound (R : IdRing) : ℕ := (Finset.range R.n).sup fun j => R.id j

theorem id_le_bound (R : IdRing) (w : ℤ) : R.id w ≤ bound R := by
  have hn : (0 : ℤ) < R.n := by exact_mod_cast R.n_pos
  rw [id_eq_emod]
  exact Finset.le_sup (f := fun j : ℕ => R.id j)
    (Finset.mem_range.2 (by have := Int.emod_lt_of_pos w hn; omega))

/-- Every ring has a node with the largest identifier. -/
theorem exists_max (R : IdRing) : ∃ v, ∀ w, R.id w ≤ R.id v := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image (Finset.range R.n) (fun j : ℕ => R.id j)
    ⟨0, Finset.mem_range.2 R.n_pos⟩
  have hn : (0 : ℤ) < R.n := by exact_mod_cast R.n_pos
  refine ⟨j, fun w => ?_⟩
  rw [id_eq_emod]
  exact hj _ (Finset.mem_range.2 (by have := Int.emod_lt_of_pos w hn; omega))

/-- The ring `R` where the node at position `k` (and its translates by multiples of `n`) gets the
identifier `bound R + 1`, larger than every identifier of `R`. -/
noncomputable def raise (R : IdRing) (k : ℤ) : IdRing where
  n := R.n
  three_le := R.three_le
  id j := if (R.n : ℤ) ∣ j - k then bound R + 1 else R.id j
  periodic j := by
    have : j + (R.n : ℤ) - k = (j - k) + R.n := by ring
    simp only [this, dvd_add_self_right, R.periodic j]
  inj i j h := by
    by_cases hi : (R.n : ℤ) ∣ i - k <;> by_cases hj : (R.n : ℤ) ∣ j - k <;>
      simp only [hi, hj, ↓reduceIte] at h
    · have := dvd_sub hi hj
      rwa [show i - k - (j - k) = i - j by ring] at this
    · exact absurd h (by have := id_le_bound R j; omega)
    · exact absurd h (by have := id_le_bound R i; omega)
    · exact R.inj i j h

theorem raise_id (R : IdRing) (k j : ℤ) :
    (raise R k).id j = if (R.n : ℤ) ∣ j - k then bound R + 1 else R.id j := rfl

/-! ### Worst case: the maximum node needs radius `⌊n/2⌋` -/

/-- §2 of the paper ("the vertex with the maximum identifier needs `n/2` rounds"): for every
correct largest-ID algorithm, the node with the largest identifier of any ring of size `n` has
radius at least `⌊n/2⌋`. -/
theorem half_le_radAt_of_max {A : Alg Bool} (hA : Correct A) (R : IdRing) (v : ℤ)
    (hv : ∀ w, R.id w ≤ R.id v) : R.n / 2 ≤ A.radAt R v := by
  by_contra hlt
  rw [not_le] at hlt
  set r := A.radAt R v with hr
  have h2r : 2 * r + 2 ≤ R.n := by omega
  set R' := raise R (v + r + 1)
  -- `R'` agrees with `R` on the window `[-r, r]` of `v`
  have hagree : AgreeOn r (R.view v) (R'.view v) := by
    intro j hj
    rw [abs_le] at hj
    have hnd : ¬ (R.n : ℤ) ∣ v + j - (v + r + 1) := by
      intro hd
      have h0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; omega)
      omega
    simp only [IdRing.view_apply, R', raise_id, hnd, ↓reduceIte]
  have hout : A.output (R'.view v) = A.output (R.view v) :=
    Alg.output_eq_of_agreeOn hagree (hA.stops R v) le_rfl
  have hyes : A.outAt R' v = true := by
    simp only [Alg.outAt, hout]
    exact (hA.spec R v).2 hv
  have hmax := (hA.spec R' v).1 hyes (v + r + 1)
  have hnd : ¬ (R.n : ℤ) ∣ v - (v + r + 1) := by
    intro hd
    have h0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; omega)
    omega
  simp only [R', raise_id, sub_self, dvd_zero, hnd, ↓reduceIte] at hmax
  have := id_le_bound R v
  omega

/-- §2 of the paper: the largest-ID problem has linear worst-case complexity. For every correct
algorithm and every `n ≥ 3` there is a ring of size `n` with a node of radius `≥ ⌊n/2⌋`. -/
theorem worst_case {A : Alg Bool} (hA : Correct A) (n : ℕ) (hn : 3 ≤ n) :
    ∃ R : IdRing, R.n = n ∧ ∃ v, n / 2 ≤ A.radAt R v := by
  let R := IdRing.ofList (List.range n) (List.nodup_range) (by simpa using hn)
  obtain ⟨v, hv⟩ := exists_max R
  exact ⟨R, by simp [R], v, by simpa [R] using half_le_radAt_of_max hA R v hv⟩

/-! ### The straightforward algorithm -/

/-- Within radius `r`, the view `f` shows an identifier larger than the node's own. -/
def SeesLarger (r : ℕ) (f : ℤ → ℕ) : Prop := ∃ j : ℤ, |j| ≤ r ∧ f 0 < f j

/-- Within radius `r`, the view `f` shows some identifier twice, so the window covers the whole
ring. -/
def SeesRepeat (r : ℕ) (f : ℤ → ℕ) : Prop :=
  ∃ a b : ℤ, -(r : ℤ) ≤ a ∧ a < b ∧ b ≤ r ∧ f a = f b

open Classical in
/-- §2 of the paper, the straightforward algorithm: increase the radius until a larger identifier
is seen (answer No) or until the whole ring has been seen, i.e. an identifier repeats in the
window (answer Yes). -/
noncomputable def straightforward : Alg Bool where
  out r f := if SeesLarger r f then some false else if SeesRepeat r f then some true else none
  out_congr r f g h := by
    have h0 : f 0 = g 0 := h 0 (by simp)
    have h1 : SeesLarger r f ↔ SeesLarger r g := by
      constructor
      · rintro ⟨j, hj, hl⟩; exact ⟨j, hj, by rwa [← h0, ← h j hj]⟩
      · rintro ⟨j, hj, hl⟩; exact ⟨j, hj, by rwa [h0, h j hj]⟩
    have h2 : SeesRepeat r f ↔ SeesRepeat r g := by
      constructor
      · rintro ⟨a, b, ha, hab, hb, he⟩
        exact ⟨a, b, ha, hab, hb, by
          rwa [← h a (by rw [abs_le]; omega), ← h b (by rw [abs_le]; omega)]⟩
      · rintro ⟨a, b, ha, hab, hb, he⟩
        exact ⟨a, b, ha, hab, hb, by
          rwa [h a (by rw [abs_le]; omega), h b (by rw [abs_le]; omega)]⟩
    by_cases hf1 : SeesLarger r f
    · have hg1 := h1.1 hf1
      simp only [hf1, hg1, ↓reduceIte]
    · have hg1 : ¬ SeesLarger r g := fun hg => hf1 (h1.2 hg)
      by_cases hf2 : SeesRepeat r f
      · have hg2 := h2.1 hf2
        simp only [hf1, hg1, hf2, hg2, ↓reduceIte]
      · have hg2 : ¬ SeesRepeat r g := fun hg => hf2 (h2.2 hg)
        simp only [hf1, hg1, hf2, hg2, ↓reduceIte]

theorem straightforward_out_isSome {r : ℕ} {f : ℤ → ℕ} :
    (straightforward.out r f).isSome ↔ SeesLarger r f ∨ SeesRepeat r f := by
  simp only [straightforward]
  by_cases h1 : SeesLarger r f
  · simp only [h1, ↓reduceIte, Option.isSome_some, true_or]
  · by_cases h2 : SeesRepeat r f
    · simp only [h1, h2, ↓reduceIte, Option.isSome_some, or_true]
    · simp only [h1, h2, ↓reduceIte, Option.isSome_none, or_false]; decide

theorem seesRepeat_n (R : IdRing) (v : ℤ) : SeesRepeat R.n (R.view v) :=
  ⟨0, R.n, by omega, by exact_mod_cast R.n_pos, le_rfl, by simpa using (R.id_add_mul v 1).symm⟩

theorem straightforward_stops (R : IdRing) (v : ℤ) : straightforward.Stops (R.view v) :=
  ⟨R.n, straightforward_out_isSome.2 (Or.inr (seesRepeat_n R v))⟩

theorem radAt_straightforward_le (R : IdRing) (v : ℤ) : straightforward.radAt R v ≤ R.n :=
  Alg.rad_le (straightforward_out_isSome.2 (Or.inr (seesRepeat_n R v)))

/-- A repeated identifier in the window `[-r, r]` means the window covers the whole ring; if
moreover no larger identifier is seen, the node has the largest identifier. -/
theorem le_of_seesRepeat (R : IdRing) (v : ℤ) {r : ℕ} (hrep : SeesRepeat r (R.view v))
    (hlar : ¬ SeesLarger r (R.view v)) (w : ℤ) : R.id w ≤ R.id v := by
  obtain ⟨a, b, ha, hab, hb, he⟩ := hrep
  simp only [IdRing.view_apply] at he
  obtain ⟨m, hm⟩ := R.id_eq_iff.1 he.symm
  have hn : (0 : ℤ) < R.n := by exact_mod_cast R.n_pos
  have hm1 : 1 ≤ m := by
    by_contra hc
    have : (R.n : ℤ) * m ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hn.le (by omega)
    omega
  have hba : (R.n : ℤ) ≤ b - a := by
    have : (v + b) - (v + a) = b - a := by ring
    nlinarith
  set j := a + (w - v - a) % R.n
  have hj0 := Int.emod_nonneg (w - v - a) hn.ne'
  have hj1 := Int.emod_lt_of_pos (w - v - a) hn
  have hw : R.id w = R.id (v + j) := by
    rw [R.id_eq_iff]
    exact ⟨(w - v - a) / R.n, by have := Int.emod_add_mul_ediv (w - v - a) R.n; simp only [j]; linarith⟩
  rw [hw]
  by_contra hc
  exact hlar ⟨j, by rw [abs_le]; omega, by simpa using (not_le.1 hc)⟩

/-- §2 of the paper: the straightforward algorithm solves the largest-ID problem. -/
theorem straightforward_correct : Correct straightforward where
  stops := straightforward_stops
  spec R v := by
    have hs := Alg.rad_spec (straightforward_stops R v)
    unfold Alg.outAt Alg.output
    revert hs
    generalize straightforward.rad (R.view v) = r
    intro hs
    by_cases h1 : SeesLarger r (R.view v)
    · have : straightforward.out r (R.view v) = some false := by
        simp only [straightforward, h1, ↓reduceIte]
      rw [this]
      obtain ⟨j, -, hj⟩ := h1
      simp only [Option.getD_some, Bool.false_eq_true, false_iff, not_forall, not_le]
      exact ⟨v + j, by simpa using hj⟩
    · have h2 : SeesRepeat r (R.view v) := (straightforward_out_isSome.1 hs).resolve_left h1
      have : straightforward.out r (R.view v) = some true := by
        simp only [straightforward, h1, h2, ↓reduceIte]
      rw [this]
      simp only [Option.getD_some, true_iff]
      exact le_of_seesRepeat R v h2 h1

/-! ### The average radius of the straightforward algorithm is logarithmic -/

theorem radAt_congr (A : Alg Bool) (R : IdRing) {u w : ℤ} (h : (R.n : ℤ) ∣ u - w) :
    A.radAt R u = A.radAt R w := by
  have : R.view u = R.view w := by
    funext j
    simp only [IdRing.view_apply, R.id_eq_iff]
    rwa [show u + j - (w + j) = u - w by ring]
  simp [Alg.radAt, this]

/-- If the straightforward algorithm runs to radius `≥ d` at `v`, then it neither sees a larger
identifier nor a repeated identifier within radius `d - 1`. -/
theorem not_sees_of_le_radAt (R : IdRing) {v : ℤ} {d : ℕ} (hd : 1 ≤ d)
    (h : d ≤ straightforward.radAt R v) :
    ¬ SeesLarger (d - 1) (R.view v) ∧ ¬ SeesRepeat (d - 1) (R.view v) := by
  have := (Alg.lt_rad_iff (straightforward_stops R v)).1 (show d - 1 < _ by unfold Alg.radAt at h; omega)
    (d - 1) le_rfl
  rw [← not_or, ← straightforward_out_isSome, this]
  simp

/-- Two nodes at offset `k ∈ [1, d)` cannot both have radius `≥ d`: each would be the maximum of
the other's window. -/
theorem not_both_le_radAt (R : IdRing) {v : ℤ} {d k : ℕ} (hk : 1 ≤ k) (hkd : k < d)
    (hv : d ≤ straightforward.radAt R v) (hw : d ≤ straightforward.radAt R (v + k)) : False := by
  obtain ⟨hl1, hr1⟩ := not_sees_of_le_radAt R (by omega) hv
  obtain ⟨hl2, -⟩ := not_sees_of_le_radAt R (by omega) hw
  have e1 : ¬ R.id v < R.id (v + k) := fun h =>
    hl1 ⟨k, by rw [abs_le]; omega, by simpa using h⟩
  have e2 : ¬ R.id (v + k) < R.id v := fun h =>
    hl2 ⟨-k, by rw [abs_le]; omega, by simpa using h⟩
  exact hr1 ⟨0, k, by omega, by omega, by omega, by simp only [IdRing.view_apply, add_zero]; omega⟩

/-- At most `n / d` nodes have radius `≥ d`. -/
theorem card_mul_le (R : IdRing) (d : ℕ) :
    ((Finset.Ico (0 : ℤ) R.n).filter (fun v => d ≤ straightforward.radAt R v)).card * d
      ≤ R.n := by
  set S := (Finset.Ico (0 : ℤ) R.n).filter (fun v => d ≤ straightforward.radAt R v)
  have hn : (0 : ℤ) < R.n := by exact_mod_cast R.n_pos
  have key := Finset.card_le_card_of_injOn (s := S ×ˢ Finset.range d) (t := Finset.Ico (0 : ℤ) R.n)
    (fun p => (p.1 + p.2) % R.n) (fun p _ => by
      simp only [Finset.coe_Ico, Set.mem_Ico]
      exact ⟨Int.emod_nonneg _ hn.ne', Int.emod_lt_of_pos _ hn⟩) (by
      rintro ⟨s, t⟩ hst ⟨s', t'⟩ hst' he
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, S, Finset.mem_filter,
        Finset.mem_Ico, Finset.coe_range, Set.mem_Iio] at hst hst' he
      obtain ⟨⟨⟨hs0, hs1⟩, hsd⟩, ht⟩ := hst
      obtain ⟨⟨⟨hs0', hs1'⟩, hsd'⟩, ht'⟩ := hst'
      have hdvd : (R.n : ℤ) ∣ (s + t) - (s' + t') := Int.ModEq.dvd he.symm
      rcases lt_trichotomy t t' with htt | htt | htt
      · exfalso
        refine not_both_le_radAt R (v := s') (k := t' - t) (by omega) (by omega) hsd' ?_
        rwa [radAt_congr _ R (w := s) (by
          have : s' + ((t' - t : ℕ) : ℤ) - s = -((s + t) - (s' + t')) := by
            push_cast [Nat.cast_sub htt.le]; ring
          rw [this]; exact dvd_neg.2 hdvd)]
      · subst htt
        have h0 := Int.eq_zero_of_abs_lt_dvd (show (R.n : ℤ) ∣ s - s' by
          rwa [show s + (t : ℤ) - (s' + t) = s - s' by ring] at hdvd) (by rw [abs_lt]; omega)
        simp only [Prod.mk.injEq, and_true]; omega
      · exfalso
        refine not_both_le_radAt R (v := s) (k := t - t') (by omega) (by omega) hsd ?_
        rwa [radAt_congr _ R (w := s') (by
          have : s + ((t - t' : ℕ) : ℤ) - s' = (s + t) - (s' + t') := by
            push_cast [Nat.cast_sub htt.le]; ring
          rw [this]; exact hdvd)])
  simpa [Finset.card_product] using key

/-- Dyadic bound on harmonic-type sums: if `a d * d ≤ n` for all `d ≥ 1`, then
`∑_{d=1}^{N} a d ≤ n (⌊log₂ N⌋ + 1)`. -/
theorem sum_Ioc_le_log (n : ℕ) (a : ℕ → ℕ) (ha : ∀ d, 1 ≤ d → a d * d ≤ n) (N : ℕ) :
    ∑ d ∈ Finset.Ioc 0 N, a d ≤ n * (Nat.log 2 N + 1) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.lt_or_ge N 2 with hN | hN
    · interval_cases N
      · simp
      · simpa using ha 1 le_rfl
    · have hsplit := Finset.sum_Ioc_consecutive a (Nat.zero_le (N / 2)) (Nat.div_le_self N 2)
      rw [← hsplit]
      have h1 := ih (N / 2) (by omega)
      have h2 : ∑ d ∈ Finset.Ioc (N / 2) N, a d ≤ n := by
        have hle : ∀ d ∈ Finset.Ioc (N / 2) N, a d ≤ n / (N / 2 + 1) := by
          intro d hd
          rw [Finset.mem_Ioc] at hd
          have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).2 (ha d (by omega))
          exact this.trans (Nat.div_le_div_left (by omega) (by omega))
        calc ∑ d ∈ Finset.Ioc (N / 2) N, a d
            ≤ (Finset.Ioc (N / 2) N).card • (n / (N / 2 + 1)) := Finset.sum_le_card_nsmul _ _ _ hle
          _ = (N - N / 2) * (n / (N / 2 + 1)) := by simp
          _ ≤ (N / 2 + 1) * (n / (N / 2 + 1)) := Nat.mul_le_mul_right _ (by omega)
          _ ≤ n := Nat.mul_div_le n _
      have hlog : Nat.log 2 (N / 2) + 1 = Nat.log 2 N := by
        rw [Nat.log_div_base]
        have : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
        omega
      calc ∑ d ∈ Finset.Ioc 0 (N / 2), a d + ∑ d ∈ Finset.Ioc (N / 2) N, a d
          ≤ n * (Nat.log 2 (N / 2) + 1) + n := Nat.add_le_add h1 h2
        _ = n * (Nat.log 2 N + 1) := by rw [← hlog]; ring

/-- §2 of the paper: the total radius of the straightforward algorithm on any ring of size `n` is
at most `n (⌊log₂ n⌋ + 1)`, so its average radius is `O(log n)` — exponentially smaller than the
linear worst case (`worst_case`). -/
theorem sum_radAt_straightforward_le (R : IdRing) :
    ∑ v ∈ Finset.Ico (0 : ℤ) R.n, straightforward.radAt R v ≤ R.n * (Nat.log 2 R.n + 1) := by
  -- layer-cake: `r(v) = #{d ∈ (0, n] | d ≤ r(v)}` since `r(v) ≤ n`
  have hlayer : ∀ v, straightforward.radAt R v =
      ∑ d ∈ Finset.Ioc 0 R.n, if d ≤ straightforward.radAt R v then 1 else 0 := by
    intro v
    rw [Finset.sum_boole, Nat.cast_id]
    have : (Finset.Ioc 0 R.n).filter (fun d => d ≤ straightforward.radAt R v) =
        Finset.Ioc 0 (straightforward.radAt R v) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      have := radAt_straightforward_le R v
      omega
    rw [this, Nat.card_Ioc, Nat.sub_zero]
  rw [Finset.sum_congr rfl (fun v _ => hlayer v), Finset.sum_comm]
  simp_rw [Finset.sum_boole, Nat.cast_id]
  refine (Finset.sum_le_sum fun d hd => le_refl _).trans (sum_Ioc_le_log R.n
    (fun d => ((Finset.Ico (0 : ℤ) R.n).filter (fun v => d ≤ straightforward.radAt R v)).card)
    (fun d _ => card_mul_le R d) R.n)

/-- §2 of the paper, average form: the average radius of the straightforward algorithm on a ring
of size `n` is at most `⌊log₂ n⌋ + 1`. -/
theorem average_radAt_straightforward_le (R : IdRing) :
    (∑ v ∈ Finset.Ico (0 : ℤ) R.n, (straightforward.radAt R v : ℝ)) / R.n
      ≤ Nat.log 2 R.n + 1 := by
  have hn : (0 : ℝ) < R.n := by exact_mod_cast R.n_pos
  rw [div_le_iff₀ hn]
  have := sum_radAt_straightforward_le R
  calc (∑ v ∈ Finset.Ico (0 : ℤ) R.n, (straightforward.radAt R v : ℝ))
      = ((∑ v ∈ Finset.Ico (0 : ℤ) R.n, straightforward.radAt R v : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ((R.n * (Nat.log 2 R.n + 1) : ℕ) : ℝ) := by exact_mod_cast this
    _ = _ := by push_cast; ring

/-! ### The paper's recurrence (definition and small values only) -/

/-- Table `[a(0), …, a(p)]` of the paper's recurrence (§2)
`a(p) = max_{1 ≤ k ≤ ⌈p/2⌉} {k + a(k - 1) + a(p - k)}`, `a(0) = 0`, computed by course-of-values
recursion (the index `k' = k - 1` ranges over `[0, ⌈p/2⌉)`). -/
def segATable : ℕ → List ℕ
  | 0 => [0]
  | p + 1 =>
    let L := segATable p
    L ++ [(List.range ((p + 2) / 2)).foldr
      (fun k m => max m ((k + 1) + L.getD k 0 + L.getD (p - k) 0)) 0]

/-- The paper's sequence `a(p)` (§2), claimed there to be the maximal total radius of the
straightforward algorithm on a segment of `p` non-maximal vertices. Only the definition is
formalized, not that claim. -/
def segA (p : ℕ) : ℕ := (segATable p).getD p 0

/-- The first values of the paper's recurrence agree with OEIS A000788, as the paper says. -/
theorem segA_eq_A000788 : (List.range 16).map segA =
    [0, 1, 2, 4, 5, 7, 9, 12, 13, 15, 17, 20, 22, 25, 28, 32] := by decide

end LargestId

end Podc.RingColoringAverage
