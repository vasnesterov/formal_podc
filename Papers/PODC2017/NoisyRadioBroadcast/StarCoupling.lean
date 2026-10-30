import Papers.PODC2017.NoisyRadioBroadcast.Prob

/-!
# Routing on the star: the per-message coupling

For an adaptive routing schedule on the star `star n` (source `none`), the `j`-th transmission of
message `i` by the source is coupled with its own column of coins `z (some i, j) : V → Bool`
(`sel`, an adaptive fresh selection in the sense of `Coupling.lean`). On the coupled coin sequence
`couple (sel …) z`, a leaf knows `mᵢ` before round `r` only if one of its coins
`z (some i, j)`, `j < cnt i r`, is clean (`know_leaf_imp`), where `cnt i r` is the number of rounds
`< r` in which the source broadcasts `mᵢ`; if the leaves never broadcast this is an equivalence
(`know_leaf_iff`).
-/

namespace Podc.NoisyRadioBroadcast

open Finset

variable {n k : ℕ}

section Star

variable {X : Type*}

theorem star_adj_leaf (v : Fin n) (w : Option (Fin n)) : (star n).Adj (some v) w ↔ w = none := by
  simp [star]

theorem star_hears_leaf (a : Option (Fin n) → Option X) (v : Fin n) (w : Option (Fin n)) :
    Hears (star n) a (some v) w ↔ a (some v) = none ∧ w = none ∧ (a none).isSome := by
  unfold Hears
  simp only [star_adj_leaf]
  constructor
  · rintro ⟨h1, rfl, h3, -⟩; exact ⟨h1, rfl, h3⟩
  · rintro ⟨h1, rfl, h3⟩; exact ⟨h1, rfl, h3, fun w' hw' _ => hw'⟩

theorem star_heard_leaf (a : Option (Fin n) → Option X) (c : Option (Fin n) → Bool) (v : Fin n)
    (x : X) :
    heard (star n) .receiver a c (some v) = some x ↔
      a (some v) = none ∧ a none = some x ∧ c (some v) = true := by
  rw [heard_eq_some_iff]
  simp only [star_hears_leaf, faultCoin]
  constructor
  · rintro ⟨w, ⟨h1, rfl, -⟩, h3, h4⟩; exact ⟨h1, h4, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨none, ⟨h1, rfl, by simp [h2]⟩, h3, h2⟩

end Star

variable (sch : AdaptiveSchedule (Option (Fin n)) k)

/-- Knowledge in the star run (receiver faults, source `none`). -/
noncomputable abbrev starRun (ω : ℕ → Option (Fin n) → Bool) (r : ℕ) : Know (Option (Fin n)) k :=
  run (star n) none .receiver sch ω r

/-- The effective action of the source in round `r`. -/
noncomputable def srcAct (ω : ℕ → Option (Fin n) → Bool) (r : ℕ) : Option (Fin k) :=
  effective (starRun sch ω r) (sch r (starRun sch ω r)) none

/-- The number of rounds `< r` in which the source broadcasts message `i`. -/
noncomputable def cnt (ω : ℕ → Option (Fin n) → Bool) (i : Fin k) (r : ℕ) : ℕ :=
  #((range r).filter fun r' => srcAct sch ω r' = some i)

/-- The coin column used in round `r`: `(some i, j)` for the `j`-th transmission of `mᵢ`, and
`(none, r)` for a round in which the source is silent. -/
noncomputable def sel (M : ℕ) (hM : 0 < M) (r : ℕ) (ω : ℕ → Option (Fin n) → Bool) :
    Option (Fin k) × Fin M :=
  match srcAct sch ω r with
  | some i => (some i, ⟨cnt sch ω i r % M, Nat.mod_lt _ hM⟩)
  | none => (none, ⟨r % M, Nat.mod_lt _ hM⟩)

theorem sel_of_some (M : ℕ) (hM : 0 < M) {ω : ℕ → Option (Fin n) → Bool} {r : ℕ} {i : Fin k}
    (h : srcAct sch ω r = some i) :
    sel sch M hM r ω = (some i, ⟨cnt sch ω i r % M, Nat.mod_lt _ hM⟩) := by
  unfold sel; rw [h]

theorem srcAct_congr {ω ω' : ℕ → Option (Fin n) → Bool} {r : ℕ} (h : ∀ r' < r, ω r' = ω' r') :
    srcAct sch ω r = srcAct sch ω' r := by
  unfold srcAct starRun
  rw [run_congr _ _ _ _ h]

theorem cnt_congr {ω ω' : ℕ → Option (Fin n) → Bool} {r : ℕ} (h : ∀ r' < r, ω r' = ω' r')
    (i : Fin k) : cnt sch ω i r = cnt sch ω' i r := by
  unfold cnt
  congr 1
  refine filter_congr fun r' hr' => ?_
  rw [srcAct_congr sch fun r'' hr'' => h r'' (hr''.trans (mem_range.1 hr'))]

theorem sel_causal (M : ℕ) (hM : 0 < M) : Causal (sel sch M hM) := by
  intro r ω ω' h
  unfold sel
  rw [srcAct_congr sch h]
  cases srcAct sch ω' r with
  | none => rfl
  | some i => simp only [cnt_congr sch h i]

theorem cnt_le (ω : ℕ → Option (Fin n) → Bool) (i : Fin k) (r : ℕ) : cnt sch ω i r ≤ r :=
  (card_filter_le _ _).trans (card_range r).le

theorem cnt_succ (ω : ℕ → Option (Fin n) → Bool) (i : Fin k) (r : ℕ) :
    cnt sch ω i (r + 1) = cnt sch ω i r + if srcAct sch ω r = some i then 1 else 0 := by
  unfold cnt
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem cnt_lt_of_lt {ω : ℕ → Option (Fin n) → Bool} {i : Fin k} {r r' : ℕ} (hrr' : r < r')
    (h : srcAct sch ω r = some i) : cnt sch ω i r < cnt sch ω i r' := by
  unfold cnt
  refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, mem_range] at hx ⊢; exact ⟨hx.1.trans hrr', hx.2⟩
  · have := hsub (mem_filter.2 ⟨mem_range.2 hrr', h⟩)
    simp at this

theorem sel_fresh (M : ℕ) (hM : 0 < M) {R : ℕ} (hRM : R ≤ M) : FreshUpTo (sel sch M hM) R := by
  intro ω r r' hr hr' h
  unfold sel at h
  have hcr : ∀ i r, r < R → cnt sch ω i r % M = cnt sch ω i r := fun i r hr =>
    Nat.mod_eq_of_lt ((cnt_le sch ω i r).trans_lt (hr.trans_le hRM))
  rcases h1 : srcAct sch ω r with _ | i <;> rcases h2 : srcAct sch ω r' with _ | i' <;>
    simp only [h1, h2, Prod.mk.injEq, reduceCtorEq, false_and, Option.some.injEq, Fin.mk.injEq,
      true_and] at h
  · rwa [Nat.mod_eq_of_lt (hr.trans_le hRM), Nat.mod_eq_of_lt (hr'.trans_le hRM)] at h
  · obtain ⟨rfl, h⟩ := h
    rw [hcr _ _ hr, hcr _ _ hr'] at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (cnt_lt_of_lt sch hlt h1).ne h
    · exact (cnt_lt_of_lt sch hlt h2).ne h.symm

/-- The total number of transmissions of the source is at most the number of rounds. -/
theorem sum_cnt_le (ω : ℕ → Option (Fin n) → Bool) (R : ℕ) : ∑ i, cnt sch ω i R ≤ R := by
  unfold cnt
  calc ∑ i, #((range R).filter fun r' => srcAct sch ω r' = some i)
      = #((univ : Finset (Fin k)).biUnion fun i =>
          (range R).filter fun r' => srcAct sch ω r' = some i) := by
        rw [card_biUnion]
        intro i _ j _ hij
        refine disjoint_left.2 fun r hr hr' => hij ?_
        simp only [mem_filter] at hr hr'
        exact Option.some.inj (hr.2.symm.trans hr'.2)
    _ ≤ #(range R) := card_le_card (biUnion_subset.2 fun i _ => filter_subset _ _)
    _ = R := card_range R

/-! ### Knowledge of a leaf on the coupled coin sequence -/

section Know

variable (M : ℕ) (hM : 0 < M) (z : Option (Fin k) × Fin M → Option (Fin n) → Bool)

/-- The coupled coin sequence. -/
noncomputable abbrev cpl : ℕ → Option (Fin n) → Bool := couple (sel sch M hM) (fun _ => true) z

theorem source_know (ω : ℕ → Option (Fin n) → Bool) (r : ℕ) :
    starRun sch ω r none = univ := by
  induction r with
  | zero => simp [starRun, run, initKnow]
  | succ r ih =>
    simp only [starRun, run, stepKnow] at ih ⊢
    split <;> simp_all

theorem srcAct_eq (ω : ℕ → Option (Fin n) → Bool) (r : ℕ) :
    srcAct sch ω r = sch r (starRun sch ω r) none := by
  unfold srcAct effective
  rw [source_know]
  cases sch r (starRun sch ω r) none <;> simp

theorem run_succ_leaf (ω : ℕ → Option (Fin n) → Bool) (r : ℕ) (v : Fin n) (i : Fin k) :
    i ∈ starRun sch ω (r + 1) (some v) ↔ i ∈ starRun sch ω r (some v) ∨
      (effective (starRun sch ω r) (sch r (starRun sch ω r)) (some v) = none ∧
        srcAct sch ω r = some i ∧ ω r (some v) = true) := by
  simp only [starRun, run, stepKnow]
  rcases hh : heard (star n) .receiver (effective (run (star n) none .receiver sch ω r)
    (sch r (run (star n) none .receiver sch ω r))) (ω r) (some v) with _ | i'
  · refine ⟨Or.inl, ?_⟩
    rintro (h | ⟨h1, h2, h3⟩)
    · exact h
    · have := (star_heard_leaf _ _ v i).2 ⟨h1, h2, h3⟩
      rw [hh] at this; simp at this
  · rw [star_heard_leaf] at hh
    obtain ⟨h1, h2, h3⟩ := hh
    simp only [mem_insert]
    constructor
    · rintro (rfl | h)
      · exact Or.inr ⟨h1, h2, h3⟩
      · exact Or.inl h
    · rintro (h | ⟨-, h, -⟩)
      · exact Or.inr h
      · left; unfold srcAct starRun at h; rw [h2] at h; exact (Option.some.inj h).symm

theorem cpl_eq (r : ℕ) (hr : r < M) (i : Fin k) (h : srcAct sch (cpl sch M hM z) r = some i) :
    cpl sch M hM z r = z (some i, ⟨cnt sch (cpl sch M hM z) i r, (cnt_le _ _ _ _).trans_lt hr⟩) := by
  change srcAct sch (couple (sel sch M hM) (fun _ => true) z) r = some i at h
  change couple (sel sch M hM) (fun _ => true) z r = _
  have hs : sel sch M hM r (couple (sel sch M hM) (fun _ => true) z) =
      (some i, ⟨cnt sch (couple (sel sch M hM) (fun _ => true) z) i r, (cnt_le _ _ _ _).trans_lt hr⟩) := by
    rw [sel_of_some sch M hM h]
    congr 3
    exact Nat.mod_eq_of_lt ((cnt_le _ _ _ _).trans_lt hr)
  rw [couple_eq (sel_causal sch M hM), hs]

/-- A leaf that knows `mᵢ` has a clean coin among the columns of the transmissions of `mᵢ`. -/
theorem know_leaf_imp (r : ℕ) (hr : r ≤ M) (v : Fin n) (i : Fin k)
    (h : i ∈ starRun sch (cpl sch M hM z) r (some v)) :
    ∃ j : Fin M, j.val < cnt sch (cpl sch M hM z) i r ∧ z (some i, j) (some v) = true := by
  induction r with
  | zero => simp [starRun, run, initKnow] at h
  | succ r ih =>
    rw [run_succ_leaf] at h
    rcases h with h | ⟨-, h2, h3⟩
    · obtain ⟨j, hj, hz⟩ := ih (Nat.le_of_succ_le hr) h
      exact ⟨j, hj.trans_le (by rw [cnt_succ]; omega), hz⟩
    · rw [cpl_eq sch M hM z r hr i h2] at h3
      refine ⟨_, ?_, h3⟩
      simp only [cnt_succ, ite_eq_left h2]
      omega

/-- If the leaves never broadcast, a leaf knows `mᵢ` iff one of its coins in the columns of the
transmissions of `mᵢ` is clean. -/
theorem know_leaf_iff (hsil : ∀ r K v, sch r K (some v) = none) (r : ℕ) (hr : r ≤ M) (v : Fin n)
    (i : Fin k) :
    i ∈ starRun sch (cpl sch M hM z) r (some v) ↔
      ∃ j : Fin M, j.val < cnt sch (cpl sch M hM z) i r ∧ z (some i, j) (some v) = true := by
  refine ⟨know_leaf_imp sch M hM z r hr v i, ?_⟩
  induction r with
  | zero => rintro ⟨j, hj, -⟩; simp [cnt] at hj
  | succ r ih =>
    rintro ⟨j, hj, hz⟩
    rw [run_succ_leaf]
    rw [cnt_succ] at hj
    by_cases hlt : j.val < cnt sch (cpl sch M hM z) i r
    · exact Or.inl (ih (Nat.le_of_succ_le hr) ⟨j, hlt, hz⟩)
    · have h2 : srcAct sch (cpl sch M hM z) r = some i := by
        by_contra h2; rw [ite_eq_right h2] at hj; omega
      rw [ite_eq_left h2] at hj
      have hj' : j.val = cnt sch (cpl sch M hM z) i r := by omega
      refine Or.inr ⟨by simp [effective, hsil], h2, ?_⟩
      rw [cpl_eq sch M hM z r hr i h2]
      convert hz using 3
      exact Fin.ext hj'.symm

end Know

end Podc.NoisyRadioBroadcast
