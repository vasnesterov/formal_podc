import Papers.PODC2018.PartialReplicationCausal.Necessity.Invariants

/-!
# Theorem 1: consequences of liveness, and closing a replica

* `T1.frozen`: if nothing is enabled at replica `r`, an update `u` sent to `r` whose dependencies
  (on registers of `X r`) are all applied at `r` must already be applied at `r`. Otherwise let the
  other replicas apply everything they can; the resulting state is terminal, and the execution that
  stops there is fair but violates liveness for `u` at `r`.
* `T1.close r s`: replica `r` repeatedly applies its enabled update of least index until nothing
  is enabled. Afterwards every issued update on a register of `X r` is applied at `r`
  (`T1.close_all`), by `frozen`.
-/

namespace Podc.PartialReplicationCausal.Necessity

open Classical

variable {ι Reg M : Type*} {X : ι → Set Reg} {A : Alg ι Reg M}

namespace T1

-- CSLib candidate: generic (`Relation.ReflTransGen` path as a function `ℕ → α`).
lemma exists_path {α : Type*} {R : α → α → Prop} {a b : α} (h : Relation.ReflTransGen R a b) :
    ∃ f : ℕ → α, ∃ m, f 0 = a ∧ f m = b ∧ ∀ t < m, R (f t) (f (t + 1)) := by
  induction h with
  | refl => exact ⟨fun _ => a, 0, rfl, rfl, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨f, m, h0, hm, hf⟩ := ih
    refine ⟨fun t => if t ≤ m then f t else c, m + 1, by simp [h0], by simp, fun t ht => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · simp [ht.le, Nat.succ_le_of_lt ht, hf t ht]
    · simp [hm, hbc]

lemma enabled_congr {s s' : St ι Reg M} {r : ι} (hn : s'.n = s.n) (hlog : s'.log = s.log)
    (hmd : s'.md r = s.md r) (happ : s'.app r = s.app r) (a : ℕ) :
    Enabled X A s' r a ↔ Enabled X A s r a := by
  unfold Enabled; rw [hn, hlog, hmd, happ]

lemma hb_congr {s s' : St ι Reg M} (hn : s'.n = s.n) (hlog : s'.log = s.log) : HB s' = HB s := by
  unfold HB; rw [hn, hlog]

/-- Number of non-applied updates, summed over replicas. -/
noncomputable def pend [Fintype ι] (s : St ι Reg M) : ℕ :=
  ∑ r, ((Finset.range s.n).filter (fun a => a ∉ s.app r)).card

lemma pend_apply_lt [Fintype ι] {s : St ι Reg M} {r : ι} {a : ℕ} (h : Enabled X A s r a) :
    pend (s.apply A r a) < pend s := by
  unfold pend
  apply Finset.sum_lt_sum
  · intro r' _
    apply Finset.card_le_card
    intro c
    simp only [Finset.mem_filter, Finset.mem_range, apply_n]
    exact fun ⟨h1, h2⟩ => ⟨h1, fun h3 => h2 (subset_apply_app _ _ _ _ h3)⟩
  · refine ⟨r, Finset.mem_univ _, Finset.card_lt_card ⟨?_, ?_⟩⟩
    · intro c
      simp only [Finset.mem_filter, Finset.mem_range, apply_n]
      exact fun ⟨h1, h2⟩ => ⟨h1, fun h3 => h2 (subset_apply_app _ _ _ _ h3)⟩
    · intro hsub
      have := hsub (Finset.mem_filter.2 ⟨Finset.mem_range.2 h.1, h.2.2.2.1⟩)
      simp at this

/-- Let all replicas other than `r` apply updates until none is enabled there. -/
lemma quiesce [Fintype ι] (r : ι) (s : St ι Reg M) :
    ∃ s', Relation.ReflTransGen (Step X A) s s' ∧ s'.n = s.n ∧ s'.log = s.log ∧
      s'.md r = s.md r ∧ s'.app r = s.app r ∧ ∀ r' ≠ r, ∀ a, ¬ Enabled X A s' r' a := by
  induction h : pend s using Nat.strong_induction_on generalizing s with
  | _ m ih =>
    by_cases hex : ∃ r' ≠ r, ∃ a, Enabled X A s r' a
    · obtain ⟨r', hr', a, ha⟩ := hex
      obtain ⟨s', h1, h2, h3, h4, h5, h6⟩ :=
        ih _ (h ▸ pend_apply_lt ha) (s.apply A r' a) rfl
      refine ⟨s', .head (Step.apply _ _ _ ha) h1, h2, h3, ?_, ?_, h6⟩
      · rw [h4, apply_md_ne _ _ _ (Ne.symm hr')]
      · rw [h5, apply_app_ne _ _ _ (Ne.symm hr')]
    · push Not at hex
      exact ⟨s, .refl, rfl, rfl, rfl, rfl, hex⟩

/-- **Frozen lemma.** Under `Implements`, if nothing is enabled at `r`, every update sent to `r`
whose dependencies on registers of `X r` are applied at `r` is itself applied at `r`. -/
theorem frozen [Fintype ι] (hA : Implements X A) {s : St ι Reg M} (hs : Reachable X A s) {r : ι}
    (hr : ∀ a, ¬ Enabled X A s r a) {u : ℕ} (hu : u < s.n) (hreg : (s.log u).reg ∈ X r)
    (happ : u ∉ s.app r) (hdep : ∀ a, (s.log a).reg ∈ X r → HB s a u → a ∈ s.app r) : False := by
  obtain ⟨s', hss', hn, hlog, hmd, happ', hen⟩ := quiesce (X := X) (A := A) r s
  have hterm : ∀ r' a, ¬ Enabled X A s' r' a := by
    intro r' a
    by_cases h : r' = r
    · subst h; rw [enabled_congr hn hlog hmd happ']; exact hr a
    · exact hen r' h a
  obtain ⟨s₀, h₀, h0s⟩ := hs
  obtain ⟨f, m, hf0, hfm, hf⟩ := exists_path (h0s.trans hss')
  have hσ : ∀ t, m ≤ t → (if t ≤ m then f t else s') = s' := by
    intro t ht
    split_ifs with h'
    · rw [show t = m by omega, hfm]
    · rfl
  let E : Execution X A :=
    { σ := fun t => if t ≤ m then f t else s'
      init := by simpa [hf0] using h₀
      step := by
        intro t
        by_cases ht : t < m
        · left; simp only [ht.le, Nat.succ_le_of_lt ht, ite_true]; exact hf t ht
        · right; rw [hσ t (by omega), hσ (t + 1) (by omega)] }
  have hfair : E.Fair := by
    intro i a t₀ h
    exfalso
    have := h (max t₀ m) (le_max_left _ _)
    simp only [E] at this
    rw [hσ _ (le_max_right _ _)] at this
    exact hterm i a this
  have hσm : E.σ m = s' := hσ m le_rfl
  have hHB : HB s' = HB s := hb_congr hn hlog
  obtain ⟨t', ht', hut'⟩ := hA.2 E hfair m u r (by rw [hσm, hn]; exact hu)
    (by rw [hσm, hlog]; exact hreg)
    (by rw [hσm, hHB, hlog, happ']; exact hdep)
  have : E.σ t' = s' := hσ t' ht'
  rw [this, happ'] at hut'
  exact happ hut'

/-- If nothing except possibly `u` is enabled at `r`, and `u` is sent to `r`, not yet applied
there and its dependencies are applied there, then `u` is enabled at `r`. -/
theorem enabled_of_unique [Fintype ι] (hA : Implements X A) {s : St ι Reg M}
    (hs : Reachable X A s) {r : ι} {u : ℕ} (hu : u < s.n) (hreg : (s.log u).reg ∈ X r)
    (happ : u ∉ s.app r) (hdep : ∀ a, (s.log a).reg ∈ X r → HB s a u → a ∈ s.app r)
    (hoth : ∀ a ≠ u, ¬ Enabled X A s r a) : Enabled X A s r u := by
  by_contra hne
  refine frozen hA hs (fun a ha => ?_) hu hreg happ hdep
  by_cases h : a = u
  · subst h; exact hne ha
  · exact hoth a h ha

/-- Applying `v` at `r` while a dependency `v'` on a register of `X r` is missing violates safety. -/
theorem not_enabled_of_dep (hA : Implements X A) {s : St ι Reg M} (hs : Reachable X A s) {r : ι}
    {v v' : ℕ} (hvv : HB s v' v) (hreg : (s.log v').reg ∈ X r) (happ : v' ∉ s.app r)
    (hne : v' ≠ v) : ¬ Enabled X A s r v := by
  intro he
  have hs' := Reachable.step hs (Step.apply _ _ _ he)
  have := hA.1 _ hs' r v (by simp) v' hreg hvv
  simp only [apply_app_self, Set.mem_insert_iff] at this
  rcases this with h | h
  · exact hne h
  · exact happ h

/-! ### Closing a replica -/

variable (X A) in
/-- Apply the enabled update of least index at `r`, if any. -/
noncomputable def stepMin (r : ι) (s : St ι Reg M) : St ι Reg M :=
  if h : ∃ a, Enabled X A s r a then s.apply A r (Nat.find h) else s

variable (X A) in
/-- Closing replica `r`: apply enabled updates (least index first) until none is enabled. -/
noncomputable def close (r : ι) (s : St ι Reg M) : St ι Reg M := (stepMin X A r)^[s.n] s

section stepMin

variable {r : ι}

lemma stepMin_n (s : St ι Reg M) : (stepMin X A r s).n = s.n := by
  unfold stepMin; split_ifs <;> rfl

lemma stepMin_log (s : St ι Reg M) : (stepMin X A r s).log = s.log := by
  unfold stepMin; split_ifs <;> rfl

lemma stepMin_md_ne (s : St ι Reg M) {r' : ι} (h : r' ≠ r) : (stepMin X A r s).md r' = s.md r' := by
  unfold stepMin; split_ifs
  · exact apply_md_ne _ _ _ h
  · rfl

lemma stepMin_app_ne (s : St ι Reg M) {r' : ι} (h : r' ≠ r) :
    (stepMin X A r s).app r' = s.app r' := by
  unfold stepMin; split_ifs
  · exact apply_app_ne _ _ _ h
  · rfl

lemma rtg_stepMin (s : St ι Reg M) : Relation.ReflTransGen (Step X A) s (stepMin X A r s) := by
  unfold stepMin; split_ifs with h
  · exact .single (Step.apply _ _ _ (Nat.find_spec h))
  · exact .refl

lemma stepMin_of_not (s : St ι Reg M) (h : ∀ a, ¬ Enabled X A s r a) : stepMin X A r s = s := by
  unfold stepMin; split_ifs with h'
  · exact absurd (Nat.find_spec h') (h _)
  · rfl

lemma iterate_stepMin_n (s : St ι Reg M) (m : ℕ) : ((stepMin X A r)^[m] s).n = s.n := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', stepMin_n, ih]

lemma iterate_stepMin_log (s : St ι Reg M) (m : ℕ) : ((stepMin X A r)^[m] s).log = s.log := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', stepMin_log, ih]

lemma iterate_stepMin_md_ne (s : St ι Reg M) (m : ℕ) {r' : ι} (h : r' ≠ r) :
    ((stepMin X A r)^[m] s).md r' = s.md r' := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', stepMin_md_ne _ h, ih]

lemma iterate_stepMin_app_ne (s : St ι Reg M) (m : ℕ) {r' : ι} (h : r' ≠ r) :
    ((stepMin X A r)^[m] s).app r' = s.app r' := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', stepMin_app_ne _ h, ih]

lemma rtg_iterate_stepMin (s : St ι Reg M) (m : ℕ) :
    Relation.ReflTransGen (Step X A) s ((stepMin X A r)^[m] s) := by
  induction m with
  | zero => exact .refl
  | succ m ih => rw [Function.iterate_succ_apply']; exact ih.trans (rtg_stepMin _)

/-- Number of updates not applied at `r`. -/
noncomputable def pendAt (r : ι) (s : St ι Reg M) : ℕ :=
  ((Finset.range s.n).filter (fun a => a ∉ s.app r)).card

lemma pendAt_le (s : St ι Reg M) : pendAt r s ≤ s.n :=
  (Finset.card_filter_le _ _).trans (by simp)

lemma pendAt_stepMin_lt (s : St ι Reg M) (h : ∃ a, Enabled X A s r a) :
    pendAt r (stepMin X A r s) < pendAt r s := by
  unfold stepMin; rw [dite_eq_left_of_eq_true (eq_true h)]
  have ha := Nat.find_spec h
  apply Finset.card_lt_card ⟨?_, ?_⟩
  · intro c
    simp only [Finset.mem_filter, Finset.mem_range, apply_n]
    exact fun ⟨h1, h2⟩ => ⟨h1, fun h3 => h2 (subset_apply_app _ _ _ _ h3)⟩
  · intro hsub
    have := hsub (Finset.mem_filter.2 ⟨Finset.mem_range.2 ha.1, ha.2.2.2.1⟩)
    simp at this

lemma pendAt_iterate (m : ℕ) : ∀ s : St ι Reg M, (∃ a, Enabled X A ((stepMin X A r)^[m] s) r a) →
    pendAt r ((stepMin X A r)^[m] s) + m ≤ pendAt r s := by
  induction m with
  | zero => intro s _; simp
  | succ m ih =>
    intro s h
    rw [Function.iterate_succ_apply] at h ⊢
    by_cases hs : ∃ a, Enabled X A s r a
    · have := ih _ h
      have := pendAt_stepMin_lt s hs
      omega
    · push Not at hs
      rw [stepMin_of_not s hs, Function.iterate_fixed (stepMin_of_not s hs)] at h
      obtain ⟨a, ha⟩ := h
      exact absurd ha (hs a)

end stepMin

section close

variable {r : ι}

lemma close_n (s : St ι Reg M) : (close X A r s).n = s.n := iterate_stepMin_n _ _
lemma close_log (s : St ι Reg M) : (close X A r s).log = s.log := iterate_stepMin_log _ _
lemma close_md_ne (s : St ι Reg M) {r' : ι} (h : r' ≠ r) : (close X A r s).md r' = s.md r' :=
  iterate_stepMin_md_ne _ _ h
lemma close_app_ne (s : St ι Reg M) {r' : ι} (h : r' ≠ r) : (close X A r s).app r' = s.app r' :=
  iterate_stepMin_app_ne _ _ h
lemma rtg_close (s : St ι Reg M) : Relation.ReflTransGen (Step X A) s (close X A r s) :=
  rtg_iterate_stepMin _ _
lemma ext_close (s : St ι Reg M) : Ext s (close X A r s) := Ext.of_rtg (rtg_close s)
lemma hb_close (s : St ι Reg M) : HB (close X A r s) = HB s := hb_congr (close_n s) (close_log s)

lemma close_noEnabled (s : St ι Reg M) (a : ℕ) : ¬ Enabled X A (close X A r s) r a := by
  intro ha
  have h1 := pendAt_iterate (X := X) (A := A) (r := r) s.n s ⟨a, ha⟩
  have h2 := pendAt_le (r := r) s
  have : 0 < pendAt r (close X A r s) := by
    apply Finset.card_pos.2
    refine ⟨a, Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, ha.2.2.2.1⟩⟩
    exact ha.1
  unfold close at this
  omega

lemma close_of_not (s : St ι Reg M) (h : ∀ a, ¬ Enabled X A s r a) : close X A r s = s :=
  Function.iterate_fixed (stepMin_of_not s h) _

/-- After closing `r`, every issued update on a register of `X r` is applied at `r`. -/
theorem close_all [Fintype ι] (hA : Implements X A) {s : St ι Reg M} (hs : Reachable X A s) :
    ∀ a < s.n, (s.log a).reg ∈ X r → a ∈ (close X A r s).app r := by
  set s' := close X A r s
  have hs' : Reachable X A s' := Reachable.rtg hs (rtg_close s)
  have hinv := Reachable.inv hs'
  by_contra hcon
  push Not at hcon
  have hP : ∃ a, a < s.n ∧ (s.log a).reg ∈ X r ∧ a ∉ s'.app r := by
    obtain ⟨a, h1, h2, h3⟩ := hcon; exact ⟨a, h1, h2, h3⟩
  obtain ⟨hu, hreg, happ⟩ := Nat.find_spec hP
  have hlog : s'.log = s.log := close_log s
  have hn : s'.n = s.n := close_n s
  refine frozen hA hs' (fun a => close_noEnabled s a) (by rw [hn]; exact hu) (by rw [hlog]; exact hreg)
    happ ?_
  intro a ha hab
  have hlt := hinv.hb_lt hab
  by_contra hna
  exact Nat.find_min hP hlt ⟨hlt.trans hu, hlog ▸ ha, hna⟩

lemma close_app_iff [Fintype ι] (hA : Implements X A) {s : St ι Reg M} (hs : Reachable X A s)
    (a : ℕ) : a ∈ (close X A r s).app r ↔ a < s.n ∧ (s.log a).reg ∈ X r := by
  have hinv := Reachable.inv (Reachable.rtg hs (rtg_close (r := r) s))
  constructor
  · intro h
    have h1 := hinv.app_lt _ _ h
    have h2 := hinv.app_reg _ _ h
    rw [close_n] at h1; rw [close_log] at h2
    exact ⟨h1, h2⟩
  · exact fun ⟨h1, h2⟩ => close_all hA hs a h1 h2

end close

end T1

end Podc.PartialReplicationCausal.Necessity
