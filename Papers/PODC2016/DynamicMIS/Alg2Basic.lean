import Papers.PODC2016.DynamicMIS.Alg2Defs

/-!
# Algorithm 2: basic properties of a round and of runs

* The possible transitions of a participating node in one round (`step_inM`, …,
  `step_ready_cases`); non-participating nodes are frozen (`run_of_notMem`).
* Runs started from an *admissible* configuration (`InitOK`: every participating node is in `M`,
  `M̄` or has just changed to `C`): the age of a `C` state counts the rounds since the `C`-entry
  (`run_changing_succ`, `run_age`), every `C`-entry after time `0` is triggered by a predecessor that
  entered `C` one round earlier (`run_entry`), a node leaving `R` sees only `M`/`M̄` predecessors
  (`run_finalize_preds`).
* The invariants `Inv` ((J0)–(J2)), preserved by every round (`Inv.step`); in a configuration where
  every participating node is in `M` or `M̄` they force the greedy MIS (`eq_ofSet_greedyMIS`), and
  such a configuration is a fixed point (`step_eq_self`).
-/

open Finset SimpleGraph

namespace DynamicMIS

namespace Alg2

variable {V : Type*}

namespace St

theorem isFinal_iff {s : St} : s.IsFinal ↔ s = .inM ∨ s = .outM := by
  cases s <;> simp [IsFinal]

theorem isChanging_iff {s : St} : s.IsChanging ↔ ∃ a, s = .changing a := by
  cases s <;> simp [IsChanging]

theorem trichotomy (s : St) : s.IsFinal ∨ s.IsChanging ∨ s = .ready := by
  cases s <;> simp [IsFinal, IsChanging]

@[simp] theorem isFinal_inM : St.inM.IsFinal := trivial
@[simp] theorem isFinal_outM : St.outM.IsFinal := trivial
@[simp] theorem not_isFinal_changing (a : ℕ) : ¬ (St.changing a).IsFinal := fun h => h
@[simp] theorem not_isFinal_ready : ¬ St.ready.IsFinal := fun h => h
@[simp] theorem isChanging_changing (a : ℕ) : (St.changing a).IsChanging := trivial
@[simp] theorem not_isChanging_inM : ¬ St.inM.IsChanging := fun h => h
@[simp] theorem not_isChanging_outM : ¬ St.outM.IsChanging := fun h => h
@[simp] theorem not_isChanging_ready : ¬ St.ready.IsChanging := fun h => h

theorem not_isChanging_of_isFinal {s : St} (h : s.IsFinal) : ¬ s.IsChanging := by
  cases s <;> simp_all [IsFinal, IsChanging]

end St

/-! ### One round -/

section Step

variable (N : Net V) (c : V → St) {v : V}

theorem step_of_notMem (hv : v ∉ N.part) : step N c v = c v := by
  simp [step, hv]

open Classical in
theorem step_of_inM (hv : v ∈ N.part) (h : c v = .inM) :
    step N c v = if ∃ u, N.Pred u v ∧ c u = .changing 0 then .changing 0 else .inM := by
  unfold step
  rw [ite_eq_right (not_not.2 hv), h]

open Classical in
theorem step_of_outM (hv : v ∈ N.part) (h : c v = .outM) :
    step N c v = if (∃ u, N.Pred u v ∧ c u = .changing 0) ∧ (∀ u, N.Pred u v → c u ≠ .inM)
      then .changing 0 else .outM := by
  unfold step
  rw [ite_eq_right (not_not.2 hv), h]

open Classical in
theorem step_of_changing (hv : v ∈ N.part) {a : ℕ} (h : c v = .changing a) :
    step N c v = if 1 ≤ a ∧ ∀ u, N.Higher u v → ¬ (c u).IsChanging then .ready
      else .changing (a + 1) := by
  unfold step
  rw [ite_eq_right (not_not.2 hv), h]

open Classical in
theorem step_of_ready (hv : v ∈ N.part) (h : c v = .ready) :
    step N c v = if ∀ u, N.Pred u v → (c u).IsFinal then
      (if v ∈ N.active ∧ ∀ u, N.Pred u v → c u = .outM then .inM else .outM) else .ready := by
  unfold step
  rw [ite_eq_right (not_not.2 hv), h]

variable {N c}

theorem step_inM (h : c v = .inM) : step N c v = .inM ∨ step N c v = .changing 0 := by
  by_cases hv : v ∈ N.part
  · rw [step_of_inM N c hv h]; split_ifs <;> simp
  · rw [step_of_notMem N c hv, h]; simp

theorem step_outM (h : c v = .outM) : step N c v = .outM ∨ step N c v = .changing 0 := by
  by_cases hv : v ∈ N.part
  · rw [step_of_outM N c hv h]; split_ifs <;> simp
  · rw [step_of_notMem N c hv, h]; simp

theorem step_final (h : (c v).IsFinal) :
    (step N c v).IsFinal ∨ step N c v = .changing 0 := by
  rcases St.isFinal_iff.1 h with h | h
  · rcases step_inM (N := N) h with h' | h' <;> simp [h']
  · rcases step_outM (N := N) h with h' | h' <;> simp [h']

/-- A `C` node stays `C` or becomes `R`. -/
theorem step_changing {a : ℕ} (h : c v = .changing a) :
    step N c v = .changing a ∨ step N c v = .changing (a + 1) ∨ step N c v = .ready := by
  by_cases hv : v ∈ N.part
  · rw [step_of_changing N c hv h]; split_ifs <;> simp
  · rw [step_of_notMem N c hv, h]; simp

theorem step_changing_isChanging_or_ready (h : (c v).IsChanging) :
    (step N c v).IsChanging ∨ step N c v = .ready := by
  obtain ⟨a, ha⟩ := St.isChanging_iff.1 h
  rcases step_changing (N := N) ha with h' | h' | h' <;> simp [h']

theorem step_ready (h : c v = .ready) : (step N c v).IsFinal ∨ step N c v = .ready := by
  by_cases hv : v ∈ N.part
  · rw [step_of_ready N c hv h]; split_ifs <;> simp
  · rw [step_of_notMem N c hv, h]; simp

/-- A participating node becomes `C` (age `0`) only from `M`/`M̄`, triggered by a predecessor that
has just changed to `C`. -/
theorem step_eq_changing_zero (hv : v ∈ N.part) (h : step N c v = .changing 0) :
    (c v).IsFinal ∧ ∃ u, N.Pred u v ∧ c u = .changing 0 := by
  rcases St.trichotomy (c v) with hf | hc | hr
  · rcases St.isFinal_iff.1 hf with h' | h'
    · rw [step_of_inM N c hv h'] at h
      by_cases h1 : ∃ u, N.Pred u v ∧ c u = .changing 0
      · exact ⟨hf, h1⟩
      · rw [ite_eq_right h1] at h; cases h
    · rw [step_of_outM N c hv h'] at h
      by_cases h1 : (∃ u, N.Pred u v ∧ c u = .changing 0) ∧ (∀ u, N.Pred u v → c u ≠ .inM)
      · exact ⟨hf, h1.1⟩
      · rw [ite_eq_right h1] at h; cases h
  · obtain ⟨a, ha⟩ := St.isChanging_iff.1 hc
    rw [step_of_changing N c hv ha] at h
    split_ifs at h; simp at h
  · rw [step_of_ready N c hv hr] at h
    split_ifs at h

/-- A participating `C` node of age `a + 1` had age `a` one round earlier. -/
theorem step_eq_changing_succ (hv : v ∈ N.part) {a : ℕ} (h : step N c v = .changing (a + 1)) :
    c v = .changing a ∧ ¬ (1 ≤ a ∧ ∀ u, N.Higher u v → ¬ (c u).IsChanging) := by
  rcases St.trichotomy (c v) with hf | hc | hr
  · rcases St.isFinal_iff.1 hf with h' | h'
    · rw [step_of_inM N c hv h'] at h
      split_ifs at h; simp at h
    · rw [step_of_outM N c hv h'] at h
      split_ifs at h; simp at h
  · obtain ⟨b, hb⟩ := St.isChanging_iff.1 hc
    rw [step_of_changing N c hv hb] at h
    by_cases h1 : 1 ≤ b ∧ ∀ u, N.Higher u v → ¬ (c u).IsChanging
    · rw [ite_eq_left h1] at h; cases h
    · rw [ite_eq_right h1] at h
      simp only [St.changing.injEq, Nat.add_right_cancel_iff] at h
      subst h
      exact ⟨hb, h1⟩
  · rw [step_of_ready N c hv hr] at h
    split_ifs at h

/-- A participating node becomes `R` only from `C` of age `≥ 1` without `C` higher neighbours, or
stays `R`. -/
theorem step_eq_ready (hv : v ∈ N.part) (h : step N c v = .ready) :
    (∃ a, c v = .changing a ∧ 1 ≤ a ∧ ∀ u, N.Higher u v → ¬ (c u).IsChanging) ∨
      (c v = .ready ∧ ¬ ∀ u, N.Pred u v → (c u).IsFinal) := by
  rcases St.trichotomy (c v) with hf | hc | hr
  · rcases St.isFinal_iff.1 hf with h' | h'
    · rw [step_of_inM N c hv h'] at h
      split_ifs at h
    · rw [step_of_outM N c hv h'] at h
      split_ifs at h
  · obtain ⟨b, hb⟩ := St.isChanging_iff.1 hc
    rw [step_of_changing N c hv hb] at h
    by_cases h1 : 1 ≤ b ∧ ∀ u, N.Higher u v → ¬ (c u).IsChanging
    · exact Or.inl ⟨b, hb, h1⟩
    · rw [ite_eq_right h1] at h; cases h
  · rw [step_of_ready N c hv hr] at h
    by_cases h1 : ∀ u, N.Pred u v → (c u).IsFinal
    · rw [ite_eq_left h1] at h; split_ifs at h
    · exact Or.inr ⟨hr, h1⟩

/-- A participating node in `R` becomes `M`/`M̄` only when all its predecessors are in `M`/`M̄`. -/
theorem preds_isFinal_of_step (hv : v ∈ N.part) (h : c v = .ready) (h' : (step N c v).IsFinal) :
    ∀ u, N.Pred u v → (c u).IsFinal := by
  rw [step_of_ready N c hv h] at h'
  by_contra h1
  rw [ite_eq_right h1] at h'
  exact h'

/-- An `R` node with all predecessors in `M`/`M̄` leaves `R`. -/
theorem step_ready_isFinal (hv : v ∈ N.part) (h : c v = .ready)
    (hp : ∀ u, N.Pred u v → (c u).IsFinal) : (step N c v).IsFinal := by
  rw [step_of_ready N c hv h, ite_eq_left hp]
  split_ifs <;> simp

/-- A `C` node of positive age without `C` higher neighbours becomes `R`. -/
theorem step_changing_ready (hv : v ∈ N.part) {a : ℕ} (h : c v = .changing a) (ha : 1 ≤ a)
    (hh : ∀ u, N.Higher u v → ¬ (c u).IsChanging) : step N c v = .ready := by
  rw [step_of_changing N c hv h, ite_eq_left ⟨ha, hh⟩]

/-- If every participating node is in `M`/`M̄`, nothing changes. -/
theorem step_eq_self (h : ∀ v ∈ N.part, (c v).IsFinal) : step N c = c := by
  funext v
  by_cases hv : v ∈ N.part
  · have hno : ¬ ∃ u, N.Pred u v ∧ c u = .changing 0 := by
      rintro ⟨u, hu, hu0⟩
      have := h u hu.2.1
      rw [hu0] at this
      exact this
    rcases St.isFinal_iff.1 (h v hv) with h' | h'
    · rw [step_of_inM N c hv h', ite_eq_right hno, h']
    · rw [step_of_outM N c hv h', ite_eq_right (fun h => hno h.1), h']
  · exact step_of_notMem N c hv

end Step

/-! ### Runs -/

section Run

variable {N : Net V} {c₀ : V → St}

@[simp] theorem run_zero : run N c₀ 0 = c₀ := rfl

theorem run_succ (t : ℕ) : run N c₀ (t + 1) = step N (run N c₀ t) := rfl

theorem run_of_notMem {v : V} (hv : v ∉ N.part) (t : ℕ) : run N c₀ t v = c₀ v := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, step_of_notMem _ _ hv, ih]

/-- Admissible initial configurations: participating nodes are in `M`, `M̄`, or have just changed
to `C`. -/
def InitOK (N : Net V) (c₀ : V → St) : Prop :=
  ∀ v ∈ N.part, (c₀ v).IsFinal ∨ c₀ v = .changing 0

variable (h₀ : InitOK N c₀)
include h₀

theorem run_ne_ready_zero {v : V} (hv : v ∈ N.part) : c₀ v ≠ .ready := by
  rcases h₀ v hv with h | h <;> intro h' <;> simp_all

omit h₀ in
/-- One round back, the age of a `C` state decreases by one. -/
theorem run_changing_succ {v : V} (hv : v ∈ N.part) {t a : ℕ}
    (h : run N c₀ (t + 1) v = .changing (a + 1)) : run N c₀ t v = .changing a ∧
      ¬ (1 ≤ a ∧ ∀ u, N.Higher u v → ¬ (run N c₀ t u).IsChanging) :=
  step_eq_changing_succ hv h

/-- The age of a `C` state counts the rounds since the `C`-entry. -/
theorem run_age {v : V} (hv : v ∈ N.part) :
    ∀ a t, run N c₀ t v = .changing a → a ≤ t ∧ run N c₀ (t - a) v = .changing 0 := by
  intro a
  induction a with
  | zero => intro t h; exact ⟨Nat.zero_le _, by simpa using h⟩
  | succ a ih =>
    intro t h
    cases t with
    | zero =>
      rcases h₀ v hv with h' | h'
      · simp [run_zero ▸ h] at h'
      · rw [run_zero] at h; rw [h] at h'; cases h'
    | succ t =>
      obtain ⟨h1, -⟩ := run_changing_succ hv h
      obtain ⟨h2, h3⟩ := ih t h1
      exact ⟨by omega, by rwa [Nat.add_sub_add_right]⟩

omit h₀ in
/-- Every `C`-entry after time `0` is triggered by a predecessor that entered `C` one round
earlier; the node itself was in `M`/`M̄`. -/
theorem run_entry {v : V} (hv : v ∈ N.part) {t : ℕ} (h : run N c₀ (t + 1) v = .changing 0) :
    (run N c₀ t v).IsFinal ∧ ∃ u, N.Pred u v ∧ run N c₀ t u = .changing 0 :=
  step_eq_changing_zero hv h

theorem run_ne_ready_of_zero {v : V} (hv : v ∈ N.part) {t : ℕ} (h : run N c₀ t v = .ready) :
    0 < t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact absurd h (run_ne_ready_zero h₀ hv)
  · exact ht

omit h₀ in
/-- A node leaving `R` sees only `M`/`M̄` predecessors. -/
theorem run_finalize_preds {v : V} (hv : v ∈ N.part) {t : ℕ} (h : run N c₀ t v = .ready)
    (h' : (run N c₀ (t + 1) v).IsFinal) : ∀ u, N.Pred u v → (run N c₀ t u).IsFinal :=
  preds_isFinal_of_step hv h h'

omit h₀ in
/-- A node that is not in `M`/`M̄` at time `s` but is at time `τ ≥ s` left `R` at some time in
`(s, τ]`. -/
theorem exists_finalize {v : V} {s : ℕ} (hs : ¬ (run N c₀ s v).IsFinal) :
    ∀ τ, s ≤ τ → (run N c₀ τ v).IsFinal →
      ∃ τ', s ≤ τ' ∧ τ' < τ ∧ run N c₀ τ' v = .ready ∧ (run N c₀ (τ' + 1) v).IsFinal := by
  intro τ
  induction τ with
  | zero =>
    intro h1 h2
    obtain rfl : s = 0 := by omega
    exact absurd h2 hs
  | succ τ ih =>
    intro h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact absurd h2 hs
    by_cases h3 : (run N c₀ τ v).IsFinal
    · obtain ⟨τ', h4, h5, h6, h7⟩ := ih (by omega) h3
      exact ⟨τ', h4, by omega, h6, h7⟩
    · refine ⟨τ, by omega, by omega, ?_, h2⟩
      rcases St.trichotomy (run N c₀ τ v) with h | h | h
      · exact absurd h h3
      · rcases step_changing_isChanging_or_ready (N := N) h with h' | h'
        · rw [run_succ] at h2; exact absurd h' (St.not_isChanging_of_isFinal h2)
        · rw [run_succ] at h2; rw [h'] at h2; exact absurd h2 (by simp)
      · exact h

end Run

/-! ### The invariants (J0)–(J2) and correctness at termination -/

section Inv

/-- The invariants maintained by Algorithm 2:
(J0) inactive nodes are never in `M`;
(J1) a node in `M` sees only predecessors in `M̄` or just changed to `C`;
(J2) an active node in `M̄` has a predecessor in `M` or just changed to `C`. -/
structure Inv (N : Net V) (c : V → St) : Prop where
  inactive : ∀ v ∈ N.part, v ∉ N.active → c v ≠ .inM
  inM : ∀ v ∈ N.part, c v = .inM → ∀ u, N.Pred u v → c u = .outM ∨ c u = .changing 0
  outM : ∀ v ∈ N.part, v ∈ N.active → c v = .outM →
    ∃ u, N.Pred u v ∧ (c u = .inM ∨ c u = .changing 0)

variable {N : Net V} {c : V → St}

theorem step_eq_inM_cases {v : V} (hv : v ∈ N.part) (h : step N c v = .inM) :
    (c v = .inM ∧ ¬ ∃ u, N.Pred u v ∧ c u = .changing 0) ∨
      (c v = .ready ∧ v ∈ N.active ∧ ∀ u, N.Pred u v → c u = .outM) := by
  rcases St.trichotomy (c v) with hf | hc | hr
  · rcases St.isFinal_iff.1 hf with h' | h'
    · rw [step_of_inM N c hv h'] at h
      split_ifs at h with h1
      exact Or.inl ⟨h', h1⟩
    · rw [step_of_outM N c hv h'] at h
      split_ifs at h
  · obtain ⟨b, hb⟩ := St.isChanging_iff.1 hc
    rw [step_of_changing N c hv hb] at h
    split_ifs at h
  · rw [step_of_ready N c hv hr] at h
    split_ifs at h with h1 h2
    exact Or.inr ⟨hr, h2⟩

theorem step_eq_outM_cases {v : V} (hv : v ∈ N.part) (h : step N c v = .outM) :
    (c v = .outM ∧ ¬ ((∃ u, N.Pred u v ∧ c u = .changing 0) ∧ ∀ u, N.Pred u v → c u ≠ .inM)) ∨
      (c v = .ready ∧ (∀ u, N.Pred u v → (c u).IsFinal) ∧
        ¬ (v ∈ N.active ∧ ∀ u, N.Pred u v → c u = .outM)) := by
  rcases St.trichotomy (c v) with hf | hc | hr
  · rcases St.isFinal_iff.1 hf with h' | h'
    · rw [step_of_inM N c hv h'] at h
      split_ifs at h
    · rw [step_of_outM N c hv h'] at h
      split_ifs at h with h1
      exact Or.inl ⟨h', h1⟩
  · obtain ⟨b, hb⟩ := St.isChanging_iff.1 hc
    rw [step_of_changing N c hv hb] at h
    split_ifs at h
  · rw [step_of_ready N c hv hr] at h
    split_ifs at h with h1 h2
    exact Or.inr ⟨hr, h1, h2⟩

theorem Inv.step (h : Inv N c) : Inv N (step N c) := by
  refine ⟨fun v hv hva hM => ?_, fun v hv hM u hu => ?_, fun v hv hva hM => ?_⟩
  · rcases step_eq_inM_cases hv hM with ⟨h1, -⟩ | ⟨-, h2, -⟩
    · exact h.inactive v hv hva h1
    · exact hva h2
  · have hout : c u = .outM := by
      rcases step_eq_inM_cases hv hM with ⟨h1, h2⟩ | ⟨-, -, h3⟩
      · rcases h.inM v hv h1 u hu with h4 | h4
        · exact h4
        · exact absurd ⟨u, hu, h4⟩ h2
      · exact h3 u hu
    exact step_outM (N := N) hout
  · rcases step_eq_outM_cases hv hM with ⟨h1, h2⟩ | ⟨-, h3, h4⟩
    · obtain ⟨u, hu, hu'⟩ := h.outM v hv hva h1
      by_cases hw : ∃ w, N.Pred w v ∧ c w = .inM
      · obtain ⟨w, hw, hw'⟩ := hw
        exact ⟨w, hw, step_inM (N := N) hw'⟩
      · push Not at hw
        rcases hu' with hu' | hu'
        · exact absurd hu' (hw u hu)
        · exact absurd ⟨⟨u, hu, hu'⟩, hw⟩ h2
    · have : ∃ w, N.Pred w v ∧ c w = .inM := by
        by_contra hc
        push Not at hc
        refine h4 ⟨hva, fun w hw => ?_⟩
        rcases St.isFinal_iff.1 (h3 w hw) with h5 | h5
        · exact absurd h5 (hc w hw)
        · exact h5
      obtain ⟨w, hw, hw'⟩ := this
      exact ⟨w, hw, step_inM (N := N) hw'⟩

theorem Inv.run {c₀ : V → St} (h : Inv N c₀) (t : ℕ) : Inv N (run N c₀ t) := by
  induction t with
  | zero => exact h
  | succ t ih => exact ih.step

/-- **Correctness at termination.** If the invariants hold and every participating node is in
`M` or `M̄`, the states are those of the greedy MIS of the active nodes. -/
theorem Inv.eq_ofSet (h : Inv N c) (hA : N.active ⊆ N.part) (hfin : ∀ v ∈ N.part, (c v).IsFinal) :
    ∀ v ∈ N.part, c v = ofSet (N.graph.greedyMIS N.active N.rank) v := by
  set s : Set V := {v | v ∈ N.part ∧ c v = .inM} with hs_def
  have hs : s = N.graph.greedyMIS N.active N.rank := by
    refine eq_greedyMIS_of_isGreedy _ _ _ fun v => ⟨fun ⟨hv, hM⟩ => ?_, fun ⟨hva, hpred⟩ => ?_⟩
    · refine ⟨by_contra fun hva => h.inactive v hv hva hM, fun w hw hr ⟨hwp, hwM⟩ => ?_⟩
      rcases h.inM v hv hM w ⟨hw, hwp, hr⟩ with h1 | h1
      · rw [hwM] at h1; cases h1
      · have := hfin w hwp; rw [h1] at this; exact this
    · have hv := hA hva
      refine ⟨hv, ?_⟩
      rcases St.isFinal_iff.1 (hfin v hv) with h1 | h1
      · exact h1
      · obtain ⟨u, ⟨hu, hup, hr⟩, hu'⟩ := h.outM v hv hva h1
        rcases hu' with hu' | hu'
        · exact absurd ⟨hup, hu'⟩ (hpred u hu hr)
        · have := hfin u hup; rw [hu'] at this; exact this.elim
  intro v hv
  rw [← hs]
  unfold ofSet
  by_cases hvs : v ∈ s
  · rw [ite_eq_left hvs]; exact hvs.2
  · rw [ite_eq_right hvs]
    rcases St.isFinal_iff.1 (hfin v hv) with h1 | h1
    · exact absurd ⟨hv, h1⟩ hvs
    · exact h1

end Inv

end Alg2

end DynamicMIS
