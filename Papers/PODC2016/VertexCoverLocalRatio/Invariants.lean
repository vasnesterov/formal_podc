import Papers.PODC2016.VertexCoverLocalRatio.Algorithm

/-!
# Invariants of Algorithm 1

Hypotheses on the parameters (`Hyp`): vault factor `a > 0`, slack `σ ≥ 0` with `a + σ ≤ θ < 1`,
a response rule meeting `Rule.Spec σ`, and nonnegative weights. For the paper's algorithm
`a = θ = ε'`, `σ = 0`.

The invariant `Inv` (preserved by every iteration) records: `0 ≤ w_i ≤ w_0`; a running vertex
still has its vault (`a·w_0 ≤ w_i`); a vertex that returned `InCover` has `w ≤ θ·w_0`, one that
returned `NotInCover` has `w > θ·w_0`; and every neighbour of a `NotInCover` vertex is `InCover`.
-/

set_option linter.unusedSectionVars false

namespace VertexCoverLocalRatio

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {θ a σ : ℝ} {R : Rule V} {w0 : V → ℝ}

/-- Hypotheses on the parameters. -/
structure Hyp (θ a σ : ℝ) (R : Rule V) (w0 : V → ℝ) : Prop where
  ha : 0 < a
  hσ : 0 ≤ σ
  haσ : a + σ ≤ θ
  hθ : θ < 1
  hR : R.Spec σ
  hw0 : ∀ v, 0 ≤ w0 v

/-- The invariant of the global state. -/
structure Inv (G : SimpleGraph V) (θ a : ℝ) (w0 : V → ℝ) (s : GState V) : Prop where
  w_le : ∀ v, s.w v ≤ w0 v
  w_nonneg : ∀ v, 0 ≤ s.w v
  act : ∀ v, s.st v = .active → a * w0 v ≤ s.w v
  inC : ∀ v, s.st v = .inCover → s.w v ≤ θ * w0 v
  notC : ∀ v, s.st v = .notInCover → θ * w0 v < s.w v
  edge : ∀ u v, G.Adj u v → s.st u = .notInCover → s.st v = .inCover

theorem mem_actN {s : GState V} {v u : V} : u ∈ actN G s v ↔ G.Adj v u ∧ s.st u = .active := by
  simp [actN]

theorem actN_symm {s : GState V} {v u : V} (hv : s.st v = .active) (hu : u ∈ actN G s v) :
    v ∈ actN G s u := by
  rw [mem_actN] at hu ⊢
  exact ⟨hu.1.symm, hv⟩

section
variable (h : Hyp θ a σ R w0) {s : GState V} (hs : Inv G θ a w0 s)
include h

theorem Hyp.a_le : a ≤ θ := by linarith [h.hσ, h.haσ]

theorem req_nonneg (s : GState V) (v : V) : 0 ≤ req G a w0 s v :=
  div_nonneg (mul_nonneg h.ha.le (h.hw0 v)) (Nat.cast_nonneg _)

include hs

theorem bank_nonneg {v : V} (hv : s.st v = .active) : 0 ≤ bank a w0 s v := by
  have := hs.act v hv; unfold bank; linarith

theorem bank_le {v : V} : bank a w0 s v ≤ w0 v := by
  have := hs.w_le v; have := mul_nonneg h.ha.le (h.hw0 v); unfold bank; linarith

theorem spec_at {v : V} (hv : s.st v = .active) :
    (∀ u ∈ actN G s v, 0 ≤ bud G a R w0 s v u ∧ bud G a R w0 s v u ≤ req G a w0 s u) ∧
      given G a R w0 s v ≤ bank a w0 s v ∧
      (∀ u ∈ actN G s v, bud G a R w0 s v u < req G a w0 s u →
        bank a w0 s v - σ * w0 v ≤ given G a R w0 s v) := by
  have hr : ∀ u ∈ actN G s v, reqAt G a w0 s v u = req G a w0 s u := fun u hu => if_pos hu
  obtain ⟨h1, h2, h3⟩ := h.hR v (w0 v) (bank a w0 s v) (reqAt G a w0 s v) (actN G s v)
    (bank_nonneg h hs hv) (bank_le h hs) (fun u hu => (hr u hu).symm ▸ req_nonneg h s u)
  refine ⟨fun u hu => ?_, h2, fun u hu hlt => h3 u hu ?_⟩
  · rw [← hr u hu]; exact h1 u hu
  · rw [hr u hu]; exact hlt

theorem bud_nonneg {v u : V} (hv : s.st v = .active) (hu : u ∈ actN G s v) :
    0 ≤ bud G a R w0 s v u := ((spec_at h hs hv).1 u hu).1

theorem bud_le_req {v u : V} (hv : s.st v = .active) (hu : u ∈ actN G s v) :
    bud G a R w0 s v u ≤ req G a w0 s u := ((spec_at h hs hv).1 u hu).2

theorem given_le_bank {v : V} (hv : s.st v = .active) :
    given G a R w0 s v ≤ bank a w0 s v := (spec_at h hs hv).2.1

theorem given_ge {v u : V} (hv : s.st v = .active) (hu : u ∈ actN G s v)
    (hlt : bud G a R w0 s v u < req G a w0 s u) :
    bank a w0 s v - σ * w0 v ≤ given G a R w0 s v := (spec_at h hs hv).2.2 u hu hlt

theorem given_nonneg {v : V} (hv : s.st v = .active) : 0 ≤ given G a R w0 s v :=
  sum_nonneg fun u hu => bud_nonneg h hs hv hu

theorem recv_nonneg {v : V} (hv : s.st v = .active) : 0 ≤ recv G a R w0 s v :=
  sum_nonneg fun u hu => bud_nonneg h hs (mem_actN.1 hu).2 (actN_symm hv hu)

/-- The amounts received by `v` sum to at most its vault. -/
theorem recv_le {v : V} (hv : s.st v = .active) : recv G a R w0 s v ≤ a * w0 v := by
  have h1 : recv G a R w0 s v ≤ ∑ _u ∈ actN G s v, req G a w0 s v :=
    sum_le_sum fun u hu => bud_le_req h hs (mem_actN.1 hu).2 (actN_symm hv hu)
  rw [sum_const, nsmul_eq_mul] at h1
  have h2 : ((actN G s v).card : ℝ) * req G a w0 s v ≤ a * w0 v := by
    unfold req dg
    rcases Nat.eq_zero_or_pos (actN G s v).card with h0 | h0
    · rw [h0]; simp only [Nat.cast_zero, zero_mul]; exact mul_nonneg h.ha.le (h.hw0 v)
    · rw [mul_div_cancel₀]; exact_mod_cast h0.ne'
  linarith

theorem newW_active {v : V} (hv : s.st v = .active) :
    newW G a R w0 s v = s.w v - recv G a R w0 s v - given G a R w0 s v := by
  simp [newW, hv]

theorem newW_nonneg (v : V) : 0 ≤ newW G a R w0 s v := by
  by_cases hv : s.st v = .active
  · rw [newW_active h hs hv]
    have := recv_le h hs hv; have := given_le_bank h hs hv; unfold bank at *; linarith
  · simp only [newW, hv, if_false]; exact hs.w_nonneg v

theorem newW_le (v : V) : newW G a R w0 s v ≤ s.w v := by
  by_cases hv : s.st v = .active
  · rw [newW_active h hs hv]
    have := recv_nonneg h hs hv; have := given_nonneg h hs hv; linarith
  · simp [newW, hv]

/-- If `v` does not answer some request in full, its bank is (almost) exhausted and it returns
`InCover` in this iteration. -/
theorem partial_cov {v u : V} (hv : s.st v = .active) (hu : u ∈ actN G s v)
    (hlt : bud G a R w0 s v u < req G a w0 s u) : newW G a R w0 s v ≤ θ * w0 v := by
  rw [newW_active h hs hv]
  have := given_ge h hs hv hu hlt
  have := recv_nonneg h hs hv
  have := h.haσ
  have := h.hw0 v
  unfold bank at *
  nlinarith

end

/-! ### Status transitions -/

theorem step_w (s : GState V) (v : V) : (step G θ a R w0 s).w v = newW G a R w0 s v := rfl

open scoped Classical in
theorem step_st (s : GState V) (v : V) : (step G θ a R w0 s).st v =
    if s.st v = .active then
      if newW G a R w0 s v ≤ θ * w0 v then .inCover
      else if ∀ u ∈ actN G s v, cov G θ a R w0 s u then .notInCover
      else .active
    else s.st v := rfl

theorem step_st_of_ne {s : GState V} {v : V} (hv : s.st v ≠ .active) :
    (step G θ a R w0 s).st v = s.st v := by
  rw [step_st, if_neg hv]

theorem step_w_of_ne {s : GState V} {v : V} (hv : s.st v ≠ .active) :
    (step G θ a R w0 s).w v = s.w v := by
  simp [step_w, newW, hv]

theorem active_of_step {s : GState V} {v : V} (hv : (step G θ a R w0 s).st v = .active) :
    s.st v = .active := by
  by_contra h
  rw [step_st_of_ne h] at hv
  exact h hv

theorem step_active_iff {s : GState V} {v : V} :
    (step G θ a R w0 s).st v = .active ↔
      s.st v = .active ∧ ¬ newW G a R w0 s v ≤ θ * w0 v ∧
        ∃ u ∈ actN G s v, ¬ cov G θ a R w0 s u := by
  rw [step_st]
  split_ifs with h0 h1 h2
  · simp [h1]
  · simp only [false_iff, not_and, not_exists, not_not]
    exact fun _ _ => h2
  · push Not at h2
    simp only [h0, h1, not_false_eq_true, true_and, true_iff]
    obtain ⟨u, hu, hc⟩ := h2
    exact ⟨u, hu, hc⟩
  · simp [h0]

theorem step_inCover_iff {s : GState V} {v : V} (hv : s.st v = .active) :
    (step G θ a R w0 s).st v = .inCover ↔ newW G a R w0 s v ≤ θ * w0 v := by
  rw [step_st, if_pos hv]
  split_ifs with h1 h2 <;> simp [h1]

theorem step_notInCover_iff {s : GState V} {v : V} (hv : s.st v = .active) :
    (step G θ a R w0 s).st v = .notInCover ↔
      ¬ newW G a R w0 s v ≤ θ * w0 v ∧ ∀ u ∈ actN G s v, cov G θ a R w0 s u := by
  rw [step_st, if_pos hv]
  split_ifs with h1 h2
  · simp [h1]
  · simpa [h1] using h2
  · simp [h1, h2]

/-! ### Preservation of the invariant -/

theorem inv_init (h : Hyp θ a σ R w0) : Inv G θ a w0 (init w0) where
  w_le v := le_rfl
  w_nonneg v := h.hw0 v
  act v _ := by
    have := h.hw0 v; have := h.a_le; have := h.hθ
    show a * w0 v ≤ w0 v
    nlinarith
  inC v hv := by cases hv
  notC v hv := by cases hv
  edge u v _ hu := by cases hu

theorem inv_step (h : Hyp θ a σ R w0) {s : GState V} (hs : Inv G θ a w0 s) :
    Inv G θ a w0 (step G θ a R w0 s) where
  w_le v := (newW_le h hs v).trans (hs.w_le v)
  w_nonneg v := newW_nonneg h hs v
  act v hv := by
    obtain ⟨hv0, hn, -⟩ := step_active_iff.1 hv
    rw [step_w]
    have := h.a_le; have := h.hw0 v
    push Not at hn
    nlinarith
  inC v hv := by
    by_cases ha : s.st v = .active
    · rw [step_w]; exact (step_inCover_iff ha).1 hv
    · rw [step_st_of_ne ha] at hv; rw [step_w_of_ne ha]; exact hs.inC v hv
  notC v hv := by
    by_cases ha : s.st v = .active
    · rw [step_w]; have := ((step_notInCover_iff ha).1 hv).1; push Not at this; exact this
    · rw [step_st_of_ne ha] at hv; rw [step_w_of_ne ha]; exact hs.notC v hv
  edge u v huv hu := by
    by_cases ha : s.st u = .active
    · obtain ⟨-, hall⟩ := (step_notInCover_iff ha).1 hu
      by_cases hva : s.st v = .active
      · have hc := hall v (mem_actN.2 ⟨huv, hva⟩)
        exact (step_inCover_iff hva).2 hc.2
      · rw [step_st_of_ne hva]
        rcases hvs : s.st v with _ | _ | _
        · exact absurd hvs hva
        · rfl
        · have := hs.edge v u huv.symm hvs
          rw [this] at ha; cases ha
    · rw [step_st_of_ne ha] at hu
      have := hs.edge u v huv hu
      rw [step_st_of_ne (by rw [this]; decide), this]

theorem inv_run (h : Hyp θ a σ R w0) (i : ℕ) : Inv G θ a w0 (run G θ a R w0 i) := by
  induction i with
  | zero => exact inv_init h
  | succ i ih =>
    rw [run, Function.iterate_succ_apply']
    exact inv_step h ih

theorem run_succ (i : ℕ) : run G θ a R w0 (i + 1) = step G θ a R w0 (run G θ a R w0 i) := by
  rw [run, run, Function.iterate_succ_apply']

/-- A vertex that has returned stays returned, with the same status and weight. -/
theorem run_frozen {i : ℕ} {v : V} (hv : (run G θ a R w0 i).st v ≠ .active) (k : ℕ) :
    (run G θ a R w0 (i + k)).st v = (run G θ a R w0 i).st v ∧
      (run G θ a R w0 (i + k)).w v = (run G θ a R w0 i).w v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, run_succ]
    have hk : (run G θ a R w0 (i + k)).st v ≠ .active := ih.1 ▸ hv
    rw [step_st_of_ne hk, step_w_of_ne hk]
    exact ih

theorem active_of_le {i j : ℕ} (hij : i ≤ j) {v : V} (hv : (run G θ a R w0 j).st v = .active) :
    (run G θ a R w0 i).st v = .active := by
  by_contra h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [(run_frozen h k).1] at hv
  exact h hv

end VertexCoverLocalRatio
