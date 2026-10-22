import Papers.PODC2017.PPVerification.Defs

/-!
# Lemma 21: non-silent executions and rational flow cycles

A set of transitions `T` has a non-silent execution iff there is a nonnegative, nonzero rational
vector `x` on the non-silent transitions of `T` with `∑ₜ x(t) · (post(t) − pre(t)) = 0`
(the claim made in the proof of Proposition 6). The paper's statement writes `x(q) ≥ 0` for every
`q ∈ Q` and `x(q) > 0` for some `q`; the indices must be transitions.
-/

namespace Podc.PPVerification

open Cslib.PopulationProtocol Cslib.TransitionSystem

variable {Q Λ : Type*} [DecidableEq Q] [Fintype Q]


section Lemma21Helpers

omit [Fintype Q]

theorem delta_eq_zero_of_silent {t : Transition Q} (ht : t.Silent) (q : Q) : t.delta q = 0 := by
  simp [Transition.delta, show t.pre = t.post from ht]

/-- A firing sequence of silent transitions does not change the configuration. -/
theorem firesSeq_eq_of_silent {w : List (Transition Q)} {C C' : Multiset Q}
    (h : FiresSeq w C C') (hs : ∀ t ∈ w, t.Silent) : C' = C := by
  induction w generalizing C with
  | nil => exact h
  | cons t w ih =>
    obtain ⟨C₁, h₁, hw⟩ := h
    rw [ih hw fun s hs' => hs s (by simp [hs']), h₁.eq_of_silent (hs t (by simp))]

/-- A nonempty firing sequence of non-silent transitions of `T` is a cycle of
configuration-changing steps. -/
theorem firesSeq_transGen {T : Set (Transition Q)} {w : List (Transition Q)} {C C' : Multiset Q}
    (h : FiresSeq w C C') (hw : w ≠ []) (hT : ∀ t ∈ w, t ∈ T ∧ ¬ t.Silent) :
    Relation.TransGen (fun a b => MStep T a b ∧ b ≠ a) C C' := by
  induction w generalizing C with
  | nil => exact absurd rfl hw
  | cons t w ih =>
    obtain ⟨C₁, h₁, hrest⟩ := h
    have hstep : MStep T C C₁ ∧ C₁ ≠ C := by
      refine ⟨⟨t, (hT t (by simp)).1, h₁⟩, fun he => (hT t (by simp)).2 ?_⟩
      subst he; exact h₁.silent_of_eq
    cases w with
    | nil =>
      have : C' = C₁ := hrest
      subst this; exact .single hstep
    | cons s w =>
      exact .head hstep (ih hrest (List.cons_ne_nil _ _) fun s hs => hT s (by simp [hs]))

/-- A sequence `w` can fire from any configuration with at least `2 |w|` agents in every state. -/
theorem exists_firesSeq_of_le (w : List (Transition Q)) {C : Multiset Q}
    (hC : ∀ q, 2 * w.length ≤ C.count q) : ∃ C', FiresSeq w C C' := by
  induction w generalizing C with
  | nil => exact ⟨C, rfl⟩
  | cons t w ih =>
    have hpre : ∀ q, t.pre.count q ≤ 2 := fun q =>
      (Multiset.count_le_card q t.pre).trans (by simp)
    have hle : t.pre ≤ C := Multiset.le_iff_count.2 fun q => by
      have := hC q; have := hpre q; simp at *; omega
    obtain ⟨C', hC'⟩ := ih (C := C - t.pre + t.post) fun q => by
      have := hC q; have := hpre q
      simp only [List.length_cons, Multiset.count_add, Multiset.count_sub] at *
      omega
    exact ⟨C', _, ⟨hle, rfl⟩, hC'⟩

/-- The configuration segment of a run between times `i` and `i + n` is a firing sequence. -/
theorem firesSeq_of_run {T : Set (Transition Q)} (E : Run (MStep T)) (τ : ℕ → Transition Q)
    (hτ : ∀ s, (τ s).Fires (E.st s) (E.st (s + 1))) (i n : ℕ) :
    FiresSeq ((List.range' i n).map τ) (E.st i) (E.st (i + n)) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    refine ⟨E.st (i + 1), hτ i, ?_⟩
    have := ih (i + 1)
    rwa [show i + 1 + n = i + (n + 1) by omega] at this

/-- Clearing denominators of a nonnegative rational vector. -/
theorem exists_nat_vector {ι : Type*} [Fintype ι] (x : ι → ℚ) (hx : ∀ i, 0 ≤ x i) :
    ∃ N : ℕ, 0 < N ∧ ∃ y : ι → ℕ, ∀ i, (y i : ℚ) = N * x i := by
  classical
  have hd : ∀ i, ∃ k, ∏ j, (x j).den = (x i).den * k := fun i =>
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  choose k hk using hd
  refine ⟨∏ i, (x i).den, Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ =>
    (x i).den_ne_zero), fun i => k i * (x i).num.toNat, fun i => ?_⟩
  have hnum : ((x i).num.toNat : ℚ) = (x i).num := by
    have := Rat.num_nonneg.2 (hx i)
    exact_mod_cast Int.toNat_of_nonneg this
  rw [hk i, Nat.cast_mul, Nat.cast_mul, hnum, ← Rat.mul_den_eq_num]
  ring

end Lemma21Helpers

/-- **Lemma 21** (for an arbitrary set of transitions `T`). -/
theorem lemma_21_set (T : Set (Transition Q)) :
    (∃ E : Run (MStep T), ¬ E.Silent) ↔
    ∃ x : Transition Q → ℚ, (∀ t, x t ≠ 0 → t ∈ T ∧ ¬ t.Silent) ∧ (∀ t, 0 ≤ x t) ∧
      (∃ t, 0 < x t) ∧ ∀ q, ∑ t, x t * (t.delta q : ℚ) = 0 := by
  classical
  constructor
  · rintro ⟨E, hE⟩
    obtain ⟨C, hC⟩ := E.exists_frequently_eq_of_finite (MReach.finite (T := T) (E.st 0))
    rw [Filter.frequently_atTop] at hC
    obtain ⟨i, -, hi⟩ := hC 0
    have hti : ∃ t ≥ i, E.st t ≠ E.st i := by
      by_contra h; push Not at h; exact hE ⟨i, h⟩
    obtain ⟨t, hti, ht⟩ := hti
    obtain ⟨j, hjt, hj⟩ := hC t
    choose τ hτT hτ using E.step
    set w := (List.range' i (j - i)).map τ with hw
    have hfw : FiresSeq w C C := by
      have := firesSeq_of_run E τ hτ i (j - i)
      rwa [show i + (j - i) = j by omega, hi, hj] at this
    have hns : ∃ s ∈ w, ¬ s.Silent := by
      by_contra h; push Not at h
      have h1 := firesSeq_of_run E τ hτ i (t - i)
      rw [show i + (t - i) = t by omega] at h1
      refine ht (firesSeq_eq_of_silent h1 fun s hs => h s ?_)
      simp only [hw, List.mem_map, List.mem_range'_1] at hs ⊢
      obtain ⟨a, ha, rfl⟩ := hs
      exact ⟨a, by omega, rfl⟩
    have hwT : ∀ s ∈ w, s ∈ T := by
      intro s hs; simp only [hw, List.mem_map] at hs; obtain ⟨a, -, rfl⟩ := hs; exact hτT a
    have hflow := hfw.flowEq
    refine ⟨fun s => if s.Silent then 0 else (w.count s : ℚ), ?_, ?_, ?_, ?_⟩
    · intro s hs
      by_cases hss : s.Silent
      · simp [hss] at hs
      · simp only [hss, ite_false, ne_eq, Nat.cast_eq_zero, List.count_eq_zero, not_not] at hs
        exact ⟨hwT s hs, hss⟩
    · intro s; dsimp only; split_ifs <;> positivity
    · obtain ⟨s, hs, hss⟩ := hns
      refine ⟨s, ?_⟩
      simp only [hss, ite_false]
      exact_mod_cast List.count_pos_iff.2 hs
    · intro q
      have h0 : ∑ s, (w.count s : ℤ) * s.delta q = 0 := by have := hflow q; linarith
      have hc : ∑ s, (if s.Silent then 0 else (w.count s : ℚ)) * (s.delta q : ℚ) =
          ∑ s, (((w.count s : ℤ) * s.delta q : ℤ) : ℚ) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs with hss
        · simp [delta_eq_zero_of_silent hss q]
        · push_cast; rfl
      dsimp only
      rw [hc, ← Int.cast_sum, h0, Int.cast_zero]
  · rintro ⟨x, hxT, hx0, ⟨t₀, ht₀⟩, hsum⟩
    obtain ⟨N, hN, y, hy⟩ := exists_nat_vector x hx0
    let M : Multiset (Transition Q) := ∑ t, Multiset.replicate (y t) t
    let w := M.toList
    have hcount : ∀ t, w.count t = y t := by
      intro t
      rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum']
      simp [Multiset.count_replicate]
    have hmem : ∀ t ∈ w, t ∈ T ∧ ¬ t.Silent := by
      intro t ht
      refine hxT t fun h => ?_
      have h1 := hy t
      rw [h, mul_zero, Nat.cast_eq_zero, ← hcount] at h1
      exact (List.count_pos_iff.2 ht).ne' h1
    have hne : w ≠ [] := by
      intro h
      have h1 : (0 : ℚ) < y t₀ := by rw [hy]; positivity
      have h2 : 0 < w.count t₀ := by rw [hcount]; exact_mod_cast h1
      rw [h] at h2; simp at h2
    let C : Multiset Q := (2 * w.length) • (Finset.univ : Finset Q).val
    obtain ⟨C', hC'⟩ := exists_firesSeq_of_le w (C := C) fun q => by
      simp [C, Multiset.count_nsmul]
    have hCC : C' = C := by
      ext q
      have h := hC'.flowEq q
      have h0 : ∑ t, ((w.count t : ℕ) : ℤ) * t.delta q = 0 := by
        simp only [hcount]
        have : ((∑ t, (y t : ℤ) * t.delta q : ℤ) : ℚ) = N * ∑ t, x t * t.delta q := by
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hy]; ring
        rw [hsum q, mul_zero] at this
        exact_mod_cast this
      simp only at h
      omega
    subst hCC
    obtain ⟨E, -, hE⟩ := exists_not_silent_of_cycle (firesSeq_transGen hC' hne hmem)
    exact ⟨E, hE⟩

/-- **Lemma 21.** A protocol `P` has a non-silent execution iff some nonnegative nonzero rational
vector `x` on its non-silent transitions satisfies `∑ₜ x(t) · (post(t)(q) − pre(t)(q)) = 0` for
every state `q`. -/
theorem lemma_21 (P : MProtocol Q Λ) :
    (∃ E : Run P.Step, ¬ E.Silent) ↔
    ∃ x : Transition Q → ℚ, (∀ t, x t ≠ 0 → t ∈ P.T ∧ ¬ t.Silent) ∧ (∀ t, 0 ≤ x t) ∧
      (∃ t, 0 < x t) ∧ ∀ q, ∑ t, x t * (t.delta q : ℚ) = 0 :=
  lemma_21_set P.T

end Podc.PPVerification
