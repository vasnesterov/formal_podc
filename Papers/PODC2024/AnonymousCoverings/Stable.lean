import Papers.PODC2024.AnonymousCoverings.Covering

/-!
# Stable views and the global stabilization time

Generic part of Section 4.2–4.3 of the paper, for any write–scan algorithm whose local data
contains a *view* (a finite set of inputs) such that

* views only grow and stay inside a fixed finite set,
* a processor writes its view (`xview (wr d) = view d`), and
* a live processor that reads a value eventually has a view containing the value's view
  (immediately for Figure 1, at the end of the scan for Figure 3).

`Exec.exists_gst`: there is a time `T₀` (a corrected *GST*, Definition 4.1) after which every view
is constant, processors that are not live take no step, and every register holds the stable view
of a live writer. The paper's GST only requires the writes of non-live processors to be
overwritten; a register may still hold an old view of a live processor, so we also wait until
every register has been rewritten after the views stabilized.

`Exec.readsOnlyFrom_minimal`: live processors whose stable view is minimal read, after `T₀`, only
from live processors with the same stable view (Lemma 4.4 applied to a source of the stable-view
graph).
-/

namespace Podc.AnonymousCoverings

open Finset

variable {P R D X V : Type*} [Fintype P] [DecidableEq P] [DecidableEq R] [Fintype R]
  [DecidableEq V]

namespace Exec

variable {A : Algo R D X} (e : Exec (P := P) A)

/-- The view hypotheses (see the module docstring). -/
structure ViewSpec (view : D → Finset V) (xview : X → Finset V) (B : Finset V) : Prop where
  mono : ∀ t p, view (e.loc t p).d ⊆ view (e.loc (t + 1) p).d
  bound : ∀ t p, view (e.loc t p).d ⊆ B
  wr : ∀ d, xview (A.wr d) = view d
  rd : ∀ t a r, e.Live a → e.act t = .read a r →
    ∃ t' > t, xview (e.reg t r).val ⊆ view (e.loc t' a).d
  h0 : ∀ r, (e.reg 0 r).writer = none

omit [Fintype P] [DecidableEq V] in
/-- A processor that is not live eventually stops moving. -/
theorem eventually_not_moves_of_not_live {p : P} (h : ¬ e.Live p) :
    ∃ T, ∀ t ≥ T, ¬ e.Moves t p := by
  unfold Live at h
  push Not at h
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun t ht ⟨r, hr⟩ => by
    rcases hr with hr | hr
    · exact (hT t ht r).1 hr
    · exact (hT t ht r).2 hr⟩

omit [Fintype P] [DecidableEq V] in
/-- If someone writes `r` before `t`, the register has a last writer at time `t`. -/
theorem writer_isSome_of_write {w t : ℕ} {q : P} {r : R} (hw : e.act w = .write q r)
    (hwt : w < t) : ∃ q', (e.reg t r).writer = some q' := by
  induction t, (show w + 1 ≤ t by omega) using Nat.le_induction with
  | base => exact ⟨q, e.writer_succ_of_write hw⟩
  | succ t ht ih =>
    obtain ⟨q', hq'⟩ := ih (by omega)
    by_cases hx : ∃ p, e.act t = .write p r
    · obtain ⟨p, hp⟩ := hx
      exact ⟨p, e.writer_succ_of_write hp⟩
    · push Not at hx
      exact ⟨q', by rw [e.reg_succ_of_not_write hx, hq']⟩

variable {e} {view : D → Finset V} {xview : X → Finset V} {B : Finset V}

omit [DecidableEq V] in
/-- **Global stabilization.** After some time `T₀`, all views are constant, non-live processors
take no step, and every register holds the stable view of a live last writer. -/
theorem exists_gst (hv : e.ViewSpec view xview B) (hlive : ∃ p, e.Live p) :
    ∃ T₀ : ℕ, (∀ p, ∀ t ≥ T₀, view (e.loc t p).d = view (e.loc T₀ p).d) ∧
      (∀ p, ¬ e.Live p → ∀ t ≥ T₀, ¬ e.Moves t p) ∧
      (∀ t ≥ T₀, ∀ r, ∃ q, e.Live q ∧ (e.reg t r).writer = some q ∧
        xview (e.reg t r).val = view (e.loc T₀ q).d) := by
  classical
  -- views stabilize, non-live processors stop
  have hp : ∀ p, ∃ T, ∀ m ≥ T, (∀ t ≥ m, view (e.loc t p).d = view (e.loc m p).d) ∧
      (¬ e.Live p → ∀ t ≥ m, ¬ e.Moves t p) := by
    intro p
    obtain ⟨T, -, hT⟩ := Finset.eventually_const_of_subset_succ (N := 0)
      (f := fun t => view (e.loc t p).d) (B := B.card)
      (fun m _ => card_le_card (hv.bound m p)) (fun m _ => hv.mono m p)
    by_cases hl : e.Live p
    · exact ⟨T, fun m hm => ⟨fun t ht => by rw [hT t (by omega), hT m hm], fun h => absurd hl h⟩⟩
    · obtain ⟨T', hT'⟩ := e.eventually_not_moves_of_not_live hl
      exact ⟨max T T', fun m hm => ⟨fun t ht => by
        rw [hT t (by omega), hT m (le_of_max_le_left hm)],
        fun _ t ht => hT' t (by have := le_of_max_le_right hm; omega)⟩⟩
  obtain ⟨T₁, -, hT₁⟩ := Nat.eventually_forall_of_finite hp 0
  -- every register is rewritten after `T₁`
  obtain ⟨p₀, hp₀⟩ := hlive
  have hr : ∀ r, ∃ T, ∀ m ≥ T, ∃ w, T₁ ≤ w ∧ w < m ∧ ∃ q, e.act w = .write q r := by
    intro r
    obtain ⟨w, hw, hw'⟩ := e.exists_write_reg_of_live hp₀ r T₁
    exact ⟨w + 1, fun m hm => ⟨w, hw, by omega, p₀, hw'⟩⟩
  obtain ⟨T₀, hT₀1, hT₀⟩ := Nat.eventually_forall_of_finite hr T₁
  have hstab : ∀ p, ∀ t ≥ T₁, view (e.loc t p).d = view (e.loc T₀ p).d := by
    intro p t ht
    rw [(hT₁ T₁ le_rfl p).1 t ht, (hT₁ T₁ le_rfl p).1 T₀ hT₀1]
  refine ⟨T₀, fun p t ht => hstab p t (by omega),
    fun p hl t ht => (hT₁ T₁ le_rfl p).2 hl t (by omega), fun t ht r => ?_⟩
  obtain ⟨w, hw1, hw2, q, hq⟩ := hT₀ t ht r
  obtain ⟨q', hq'⟩ := e.writer_isSome_of_write hq hw2
  obtain ⟨w', hw'1, hw'2, hw'3, hw'4⟩ := e.exists_last_write hq' (hv.h0 r)
  have hw'T : T₁ ≤ w' := by
    by_contra hlt
    exact hw'4 w (by omega) hw2 q hq
  have hlq : e.Live q' := by
    by_contra hl
    exact (hT₁ T₁ le_rfl q').2 hl w' hw'T ⟨r, Or.inl hw'2⟩
  refine ⟨q', hlq, hq', ?_⟩
  rw [← hw'3, (e.write_spec hw'2).2.2.2.1, hv.wr, hstab q' w' hw'T]

open Classical in
/-- **Sources read only from sources.** Let `T₀` be as in `exists_gst` and let `M` be a stable
view of a live processor that is minimal among the stable views of live processors. Then, after
`T₀`, live processors with stable view `M` read only registers last written by live processors
with stable view `M`. -/
theorem readsOnlyFrom_minimal (hv : e.ViewSpec view xview B) {T₀ : ℕ}
    (hst : ∀ p, ∀ t ≥ T₀, view (e.loc t p).d = view (e.loc T₀ p).d)
    (hreg : ∀ t ≥ T₀, ∀ r, ∃ q, e.Live q ∧ (e.reg t r).writer = some q ∧
        xview (e.reg t r).val = view (e.loc T₀ q).d)
    (M : Finset V)
    (hmin : ∀ q, e.Live q → view (e.loc T₀ q).d ⊆ M → view (e.loc T₀ q).d = M) :
    e.ReadsOnlyFrom (univ.filter fun p => e.Live p ∧ view (e.loc T₀ p).d = M) T₀ := by
  intro t ht a ha r hr
  simp only [mem_filter, mem_univ, true_and] at ha
  obtain ⟨q, hq, hwq, hvq⟩ := hreg t ht r
  obtain ⟨t', ht', hsub⟩ := hv.rd t a r ha.1 hr
  rw [hvq, hst a t' (by omega), ha.2] at hsub
  exact ⟨q, by simp [hq, hmin q hq hsub], hwq⟩

end Exec

end Podc.AnonymousCoverings
