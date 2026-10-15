import Papers.PODC2016.DynamicMIS.Alg2Basic

/-!
# Algorithm 2: the round bound (Lemma 11)

Let `X` be a finite set containing every participating node that is ever outside `M`/`M̄`
(for Algorithm 2 this will be the set `S` of influenced nodes). Then:

* `C`-entries happen at times `t ≤ #{w ∈ X | w before v}` (`entry_le`): a `C`-entry at `t + 1` is
  triggered by an earlier-ranked node of `X` with a `C`-entry at `t`;
* `R`-entries happen at times `≤ |X| + 1 + #{w ∈ X | w after v}` (`readyEntry_le`): an `R`-entry
  later than two rounds after the `C`-entry waits for a later-ranked neighbour's `R`-entry;
* exits from `R` happen at times `≤ 2|X| + 1 + #{w ∈ X | w before v}` (`finalize_le`);
* progress: after time `2|X|` no node is in `C` (the latest-ranked one would enter `R`), after time
  `3|X|` no node is in `R` (the earliest-ranked one would leave it): every participating node is in
  `M`/`M̄` at time `3|X|` (`isFinal_run_three_mul`) and the run is stable from then on
  (`stableFrom_three_mul`).

The paper's bound `3|S| + 2` counts rounds from `1` with the initial `C`-changes in round `1`; our
time `0` is the configuration after that round.
-/

open Finset

namespace DynamicMIS

namespace Alg2

variable {V : Type*}

/-- Number of nodes of `X` ranked before `v`. -/
def cntLow (X : Finset V) (r : V → ℕ) (v : V) : ℕ := #{w ∈ X | r w < r v}

/-- Number of nodes of `X` ranked after `v`. -/
def cntHigh (X : Finset V) (r : V → ℕ) (v : V) : ℕ := #{w ∈ X | r v < r w}

section Count

variable {X : Finset V} {r : V → ℕ} {u v : V}

theorem cntLow_lt (hu : u ∈ X) (h : r u < r v) : cntLow X r u < cntLow X r v := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun w hw => ?_).2 ⟨u, ?_, ?_⟩)
  · simp only [mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.trans h⟩
  · simp [hu, h]
  · simp

theorem cntHigh_lt (hu : u ∈ X) (h : r v < r u) : cntHigh X r u < cntHigh X r v := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun w hw => ?_).2 ⟨u, ?_, ?_⟩)
  · simp only [mem_filter] at hw ⊢; exact ⟨hw.1, h.trans hw.2⟩
  · simp [hu, h]
  · simp

theorem cntLow_add_one_le (hv : v ∈ X) : cntLow X r v + 1 ≤ #X :=
  Finset.card_lt_card (Finset.filter_ssubset.2 ⟨v, hv, lt_irrefl _⟩)

theorem cntHigh_add_one_le (hv : v ∈ X) : cntHigh X r v + 1 ≤ #X :=
  Finset.card_lt_card (Finset.filter_ssubset.2 ⟨v, hv, lt_irrefl _⟩)

end Count

section Bounds

variable {N : Net V} {c₀ : V → St} (h₀ : InitOK N c₀) {X : Finset V}
  (hX : ∀ t, ∀ v ∈ N.part, ¬ (run N c₀ t v).IsFinal → v ∈ X)
include h₀ hX

omit h₀ in
/-- **`C`-entries** happen at times `t ≤ #{w ∈ X | w before v}`, in particular `t < |X|`. -/
theorem entry_le : ∀ t, ∀ v ∈ N.part, run N c₀ t v = .changing 0 → t ≤ cntLow X N.rank v := by
  intro t
  induction t with
  | zero => intros; exact Nat.zero_le _
  | succ t ih =>
    intro v hv h
    obtain ⟨-, u, ⟨hu1, hu2, hu3⟩, hu⟩ := run_entry hv h
    have huX : u ∈ X := hX t u hu2 (by rw [hu]; simp)
    have := ih u hu2 hu
    have := cntLow_lt (r := N.rank) huX hu3
    omega

/-- **`R`-entries** happen at times `≤ |X| + 1 + #{w ∈ X | w after v}`. -/
theorem readyEntry_le : ∀ t, ∀ v ∈ N.part, (run N c₀ t v).IsChanging →
    run N c₀ (t + 1) v = .ready → t + 1 ≤ #X + 1 + cntHigh X N.rank v := by
  intro t
  induction t with
  | zero =>
    intro v hv h1 h2
    rcases step_eq_ready hv h2 with ⟨a, ha, ha1, -⟩ | ⟨h3, -⟩
    · rcases h₀ v hv with h4 | h4
      · rw [run_zero] at ha; rw [ha] at h4; exact absurd h4 (by simp)
      · rw [run_zero] at ha; rw [ha] at h4; cases h4; omega
    · rw [h3] at h1; exact absurd h1 (by simp)
  | succ t ih =>
    intro v hv h1 h2
    have hvX : v ∈ X := hX (t + 1) v hv (fun h => St.not_isChanging_of_isFinal h h1)
    rcases step_eq_ready hv h2 with ⟨a, ha, ha1, hhigh⟩ | ⟨h3, -⟩
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      obtain ⟨hb, hnot⟩ := run_changing_succ hv ha
      rcases Nat.eq_zero_or_pos b with rfl | hb1
      · have := entry_le hX t v hv hb
        have := cntLow_add_one_le (r := N.rank) hvX
        omega
      · have : ∃ u, N.Higher u v ∧ (run N c₀ t u).IsChanging := by
          by_contra hc
          push Not at hc
          exact hnot ⟨hb1, hc⟩
        obtain ⟨u, ⟨hu1, hu2, hu3⟩, hu⟩ := this
        have huX : u ∈ X := hX t u hu2 (fun h => St.not_isChanging_of_isFinal h hu)
        have hu' : run N c₀ (t + 1) u = .ready := by
          rcases step_changing_isChanging_or_ready (N := N) hu with h | h
          · exact absurd h (hhigh u ⟨hu1, hu2, hu3⟩)
          · exact h
        have := ih u hu2 hu hu'
        have := cntHigh_lt (r := N.rank) huX hu3
        omega
    · rw [h3] at h1; exact absurd h1 (by simp)

/-- **Exits from `R`** happen at times `≤ 2|X| + 1 + #{w ∈ X | w before v}`. -/
theorem finalize_le : ∀ t, ∀ v ∈ N.part, run N c₀ t v = .ready →
    (run N c₀ (t + 1) v).IsFinal → t + 1 ≤ 2 * #X + 1 + cntLow X N.rank v := by
  intro t
  induction t with
  | zero => intro v hv h; exact absurd h (run_ne_ready_zero h₀ hv)
  | succ t ih =>
    intro v hv h1 h2
    have hvX : v ∈ X := hX (t + 1) v hv (by rw [h1]; simp)
    rcases step_eq_ready hv h1 with ⟨a, ha, -, -⟩ | ⟨h3, h4⟩
    · have := readyEntry_le h₀ hX t v hv (by rw [ha]; simp) h1
      have := cntHigh_add_one_le (r := N.rank) hvX
      omega
    · have hp := run_finalize_preds hv h1 h2
      have : ∃ u, N.Pred u v ∧ ¬ (run N c₀ t u).IsFinal := by
        by_contra hc
        push Not at hc
        exact h4 hc
      obtain ⟨u, ⟨hu1, hu2, hu3⟩, hu⟩ := this
      have huX : u ∈ X := hX t u hu2 hu
      have hu' : run N c₀ t u = .ready := by
        rcases St.trichotomy (run N c₀ t u) with h | h | h
        · exact absurd h hu
        · rcases step_changing_isChanging_or_ready (N := N) h with h' | h'
          · exact absurd h' (St.not_isChanging_of_isFinal (hp u ⟨hu1, hu2, hu3⟩))
          · have := hp u ⟨hu1, hu2, hu3⟩
            rw [run_succ, h'] at this
            exact absurd this (by simp)
        · exact h
      have := ih u hu2 hu' (hp u ⟨hu1, hu2, hu3⟩)
      have := cntLow_lt (r := N.rank) huX hu3
      omega

open Classical in
/-- Progress for `C`: after time `2|X|` no participating node is in `C`. -/
theorem not_isChanging_of_le {t : ℕ} (ht : 2 * #X ≤ t) :
    ∀ v ∈ N.part, ¬ (run N c₀ t v).IsChanging := by
  by_contra hc
  push Not at hc
  obtain ⟨v₀, hv₀, hc₀⟩ := hc
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image
    (X.filter fun v => v ∈ N.part ∧ (run N c₀ t v).IsChanging) N.rank
    ⟨v₀, mem_filter.2 ⟨hX t v₀ hv₀ (fun h => St.not_isChanging_of_isFinal h hc₀), hv₀, hc₀⟩⟩
  simp only [mem_filter] at hv hmax
  obtain ⟨-, hvP, hvC⟩ := hv
  have hvX : v ∈ X := hX t v hvP (fun h => St.not_isChanging_of_isFinal h hvC)
  obtain ⟨a, ha⟩ := St.isChanging_iff.1 hvC
  obtain ⟨hat, hent⟩ := run_age h₀ hvP a t ha
  have h1 := entry_le hX (t - a) v hvP hent
  have h2 := cntLow_add_one_le (r := N.rank) hvX
  have ha1 : 1 ≤ a := by omega
  have hR : run N c₀ (t + 1) v = .ready := by
    refine step_changing_ready hvP ha ha1 fun u ⟨_, hu2, hu3⟩ hu => ?_
    exact absurd (hmax u ⟨hX t u hu2 (fun h => St.not_isChanging_of_isFinal h hu), hu2, hu⟩)
      (not_le.2 hu3)
  have := readyEntry_le h₀ hX t v hvP hvC hR
  have := cntHigh_add_one_le (r := N.rank) hvX
  omega

open Classical in
/-- Progress for `R`: after time `3|X|` no participating node is in `R`. -/
theorem ne_ready_of_le {t : ℕ} (ht : 3 * #X ≤ t) : ∀ v ∈ N.part, run N c₀ t v ≠ .ready := by
  by_contra hc
  push Not at hc
  obtain ⟨v₀, hv₀, hc₀⟩ := hc
  obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image
    (X.filter fun v => v ∈ N.part ∧ run N c₀ t v = .ready) N.rank
    ⟨v₀, mem_filter.2 ⟨hX t v₀ hv₀ (by rw [hc₀]; simp), hv₀, hc₀⟩⟩
  simp only [mem_filter] at hv hmin
  obtain ⟨-, hvP, hvR⟩ := hv
  have hvX : v ∈ X := hX t v hvP (by rw [hvR]; simp)
  have hnoC := not_isChanging_of_le h₀ hX (t := t) (by omega)
  have hfin : (run N c₀ (t + 1) v).IsFinal := by
    refine step_ready_isFinal hvP hvR fun u ⟨_, hu2, hu3⟩ => ?_
    rcases St.trichotomy (run N c₀ t u) with h | h | h
    · exact h
    · exact absurd h (hnoC u hu2)
    · exact absurd (hmin u ⟨hX t u hu2 (by rw [h]; simp), hu2, h⟩) (not_le.2 hu3)
  have := finalize_le h₀ hX t v hvP hvR hfin
  have := cntLow_add_one_le (r := N.rank) hvX
  omega

/-- **Lemma 11 (termination).** At time `3|X|` every participating node is in `M` or `M̄`. -/
theorem isFinal_run_three_mul : ∀ v ∈ N.part, (run N c₀ (3 * #X) v).IsFinal := by
  intro v hv
  rcases St.trichotomy (run N c₀ (3 * #X) v) with h | h | h
  · exact h
  · exact absurd h (not_isChanging_of_le h₀ hX (by omega) v hv)
  · exact absurd h (ne_ready_of_le h₀ hX le_rfl v hv)

/-- **Lemma 11 (stabilisation).** Nothing changes after time `3|X|`. -/
theorem stableFrom_three_mul : StableFrom N c₀ (3 * #X) := by
  have hfix := step_eq_self (isFinal_run_three_mul h₀ hX)
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, run_succ, ih (by omega), hfix]

end Bounds

end Alg2

end DynamicMIS
