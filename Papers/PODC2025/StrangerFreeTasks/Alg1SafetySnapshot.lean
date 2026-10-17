import Papers.PODC2025.StrangerFreeTasks.Alg1SafetyBasic

/-!
# Safety of Algorithm 1: successful double collects are snapshots (Lemma B)

If a process is in the second collect with `snapshot = true` at index `j`, then there is a past
configuration `C₁` (taken right after its last first-collect read) in which registers `r < j`
held exactly the collected values, and every register `r ≥ j` that differed from the collected
value at `C₁` still differs now. Once register `r` differs from `collect r`, it differs forever,
because every later write stores a triple that is fresh (B3).

Consequently (invariant (D)): every process that decided an output of cardinality `≤ k` has a
past configuration in which every register's `seen` set equals its output.
-/

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P : Type} [DecidableEq P] {k : ℕ}

/-- `C₁` is the configuration after some prefix of `α`. -/
def Past (k : ℕ) (α : List (Label P (laObj P))) (C₁ : Cfg P k) : Prop :=
  ∃ α₁ α₂, α = α₁ ++ α₂ ∧ (alg1 k).run α₁ = some C₁

lemma Past.snoc {α : List (Label P (laObj P))} {C₁ : Cfg P k} (h : Past k α C₁)
    (ℓ : Label P (laObj P)) : Past k (α ++ [ℓ]) C₁ := by
  obtain ⟨α₁, α₂, he, hr⟩ := h
  exact ⟨α₁, α₂ ++ [ℓ], by simp [he], hr⟩

lemma Past.self {α : List (Label P (laObj P))} {C : Cfg P k} (h : (alg1 k).run α = some C) :
    Past k α C := ⟨α, [], by simp, h⟩

/-- The snapshot condition of Lemma B for a local state `l` at configuration `C`, with
witness configuration `C₁`. -/
def SnapOK (C : Cfg P k) (l : Loc P k) (C₁ : Cfg P k) : Prop :=
  (∀ r, r < l.j → C₁.mem r = l.collect r) ∧
    (∀ r, l.j ≤ r → C₁.mem r ≠ l.collect r → C.mem r ≠ l.collect r)

/-- Lemma B and invariant (D). -/
structure SInv (α : List (Label P (laObj P))) (C : Cfg P k) : Prop where
  snap : ∀ x, (C.loc x).phase = .col2 → (C.loc x).snap = true →
    ∃ C₁, Past k α C₁ ∧ SnapOK C (C.loc x) C₁
  done : ∀ x, (C.loc x).phase = .done → (C.loc x).out.card ≤ k →
    ∃ C₁, Past k α C₁ ∧ ∀ r, (C₁.mem r).seen = (C.loc x).out

lemma sInv_init : SInv (k := k) ([] : List (Label P (laObj P))) (alg1 k).initCfg where
  snap x h := by simp [Impl.initCfg, alg1, locInit] at h
  done x h := by simp [Impl.initCfg, alg1, locInit] at h

/-- A register that differs from a fresh triple keeps differing after any step. -/
lemma mem_ne_of_step {C C' : Cfg P k} {ℓ : Label P (laObj P)}
    (h : (alg1 k).step C ℓ = some C') {t : Triple P} (ht : Fresh C t) {r : Fin (k + 1)}
    (hr : C.mem r ≠ t) : C'.mem r ≠ t := by
  cases ℓ with
  | inv p o => rw [(step_inv_alg1 h).2.2.2]; exact hr
  | ret p o => rw [(step_ret_alg1 h).2.2.1]; exact hr
  | tau p =>
    obtain ⟨-, -, h3⟩ := step_tau_alg1 h
    rcases h3 with ⟨-, hm, -⟩ | ⟨-, hm, -⟩ | ⟨-, hm, -⟩
    · rw [hm]
      by_cases hri : r = (C.loc p).i
      · subst hri; simp only [Function.update_self]
        intro he
        have := ht p (by rw [← he])
        rw [← he] at this; exact lt_irrefl _ this
      · rw [Function.update_of_ne hri]; exact hr
    · rw [hm]; exact hr
    · rw [hm]; exact hr

lemma SnapOK.step {C C' C₁ : Cfg P k} {ℓ : Label P (laObj P)} {l : Loc P k}
    (h : (alg1 k).step C ℓ = some C') (hf : ∀ r, Fresh C (l.collect r)) (hs : SnapOK C l C₁) :
    SnapOK C' l C₁ :=
  ⟨hs.1, fun r hr h1 => mem_ne_of_step h (hf r) (hs.2 r hr h1)⟩

/-- A step of a process other than `x` (or a non-internal step of `x` that does not lead to
`wr`) does not change the local state of `x`. -/
lemma loc_eq_of_step {C C' : Cfg P k} {ℓ : Label P (laObj P)}
    (h : (alg1 k).step C ℓ = some C') {x : P} (hx : ℓ ≠ .tau x)
    (hph : (C'.loc x).phase ≠ .wr) : C'.loc x = C.loc x := by
  by_cases hp : ℓ.proc = x
  · cases ℓ with
    | inv p o =>
      simp only [Label.proc] at hp; subst hp
      obtain ⟨-, -, h3, -⟩ := step_inv_alg1 h
      rw [h3] at hph ⊢; simp only [Function.update_self] at hph ⊢
      split_ifs at hph ⊢ with hh
      · simp at hph
      · rfl
    | ret p o => rw [(step_ret_alg1 h).2.2.2.1]
    | tau p => simp only [Label.proc] at hp; subst hp; exact absurd rfl hx
  · exact (Impl.step_other h hp).1

theorem SInv.step {α : List (Label P (laObj P))} {C C' : Cfg P k} {ℓ : Label P (laObj P)}
    (hrun : (alg1 k).run α = some C) (hB : BInv α C) (hS : SInv α C)
    (h : (alg1 k).step C ℓ = some C') : SInv (α ++ [ℓ]) C' := by
  have hrun' : (alg1 k).run (α ++ [ℓ]) = some C' := by
    rw [Impl.run_append_of_eq _ hrun, Impl.runFrom_singleton]; exact h
  by_cases hx : ∃ x, ℓ = .tau x
  · obtain ⟨p, rfl⟩ := hx
    obtain ⟨-, -, h3⟩ := step_tau_alg1 h
    have hother : ∀ x, x ≠ p → C'.loc x = C.loc x := fun x hxp =>
      (Impl.step_other h (q := x) (by simpa [Label.proc] using Ne.symm hxp)).1
    constructor
    · intro x h1' h2'
      by_cases hxp : x = p
      · subst hxp
        rcases h3 with ⟨hph, hm, hl⟩ | ⟨hph, hm, hl⟩ | ⟨hph, hm, hl⟩
        · rw [hl] at h1'; simp at h1'
        · have hl' : C'.loc x = afterCol1 k (C.loc x) (C.mem (C.loc x).j) := by rw [hl]; simp
          rw [hl'] at h1' h2' ⊢
          rw [afterCol1_phase] at h1'
          split_ifs at h1' with hj
          · refine ⟨C', Past.self hrun', ?_, ?_⟩
            · intro r hr; rw [afterCol1_j, ite_eq_left hj] at hr; exact absurd hr (Fin.not_lt_zero r)
            · intro r _ hne; exact hne
          · rw [hph] at h1'; simp at h1'
        · have hl' : C'.loc x = afterCol2 k (C.loc x) (C.mem (C.loc x).j) := by rw [hl]; simp
          rw [hl'] at h1' h2' ⊢
          obtain ⟨hjk, hj', hsn⟩ := afterCol2_col2 _ _ hph h1'
          obtain ⟨hs1, hv⟩ := hsn h2'
          obtain ⟨C₁, hp, hs⟩ := hS.snap x hph hs1
          have hjv := fin_val_add_one hjk
          refine ⟨C₁, hp.snoc _, ?_, ?_⟩
          · intro r hr
            rw [hj'] at hr; simp only [afterCol2_collect]
            rw [Fin.lt_def, hjv] at hr
            rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | hr
            · exact hs.1 r (Fin.lt_def.2 hr)
            · have : r = (C.loc x).j := Fin.ext hr
              subst this
              by_contra hne; exact hs.2 _ le_rfl hne hv
          · intro r hr hne
            rw [hj', Fin.le_def, hjv] at hr; simp only [afterCol2_collect] at hne ⊢
            rw [hm]; exact hs.2 r (Fin.le_def.2 (by omega)) hne
      · rw [hother x hxp] at h1' h2' ⊢
        obtain ⟨C₁, hp, hs⟩ := hS.snap x h1' h2'
        exact ⟨C₁, hp.snoc _, hs.step h (hB.fresh_col x)⟩
    · intro x h1' h2'
      by_cases hxp : x = p
      · subst hxp
        rcases h3 with ⟨hph, hm, hl⟩ | ⟨hph, hm, hl⟩ | ⟨hph, hm, hl⟩
        · rw [hl] at h1'; simp at h1'
        · rw [hl] at h1'; simp only [Function.update_self, afterCol1_phase] at h1'
          split_ifs at h1'; simp_all
        · have hl' : C'.loc x = afterCol2 k (C.loc x) (C.mem (C.loc x).j) := by rw [hl]; simp
          rw [hl'] at h1' h2' ⊢
          obtain ⟨hout, hcase⟩ := afterCol2_done _ _ hph h1'
          rcases hcase with hcard | ⟨hjk, hs1, hv, hall⟩
          · rw [hout] at h2'; omega
          · obtain ⟨C₁, hp, hs⟩ := hS.snap x hph hs1
            refine ⟨C₁, hp.snoc _, fun r => ?_⟩
            have : C₁.mem r = (C.loc x).collect r := by
              by_cases hr : r < (C.loc x).j
              · exact hs.1 r hr
              · by_contra hne
                have hrj : r = (C.loc x).j := by
                  apply Fin.ext; have := r.isLt; rw [Fin.lt_def] at hr; omega
                subst hrj
                exact hs.2 _ le_rfl hne hv
            rw [this, hout, hall r]
      · rw [hother x hxp] at h1' h2' ⊢
        obtain ⟨C₁, hp, hs⟩ := hS.done x h1' h2'
        exact ⟨C₁, hp.snoc _, hs⟩
  · push Not at hx
    constructor
    · intro x h1 h2
      have he := loc_eq_of_step h (hx x) (by rw [h1]; simp)
      rw [he] at h1 h2 ⊢
      obtain ⟨C₁, hp, hs⟩ := hS.snap x h1 h2
      exact ⟨C₁, hp.snoc ℓ, hs.step h (hB.fresh_col x)⟩
    · intro x h1 h2
      have he := loc_eq_of_step h (hx x) (by rw [h1]; simp)
      rw [he] at h1 h2 ⊢
      obtain ⟨C₁, hp, hs⟩ := hS.done x h1 h2
      exact ⟨C₁, hp.snoc ℓ, hs⟩


/-- Lemma B / invariant (D) along every execution. -/
theorem sInv_of_run {α : List (Label P (laObj P))} {C : Cfg P k}
    (h : (alg1 k).run α = some C) : SInv α C := by
  refine Impl.run_induction (I := alg1 k) (Q := fun α C => SInv α C) sInv_init ?_ h
  intro α C ℓ C' hr hS hs
  exact hS.step hr (bInv_of_run hr) hs

end Cslib.SharedMemory.StrangerFree
