import Papers.PODC2017.DelayedTimestamps.LowerBounds

/-!
# Appendix C, Theorem 2: offline vectors of length 2 are insufficient on the 4-process star

The paper proves Theorem 2 with the SMT solver Z3 on the communication diagram of Figure 4 (and
mentions an unpublished manual proof). We give a manual proof.

Figure 4 (central process `p_0` = bottom line, radial processes `p_1` = top line, `p_2`, `p_3`),
events in real-time order (positions `0 … 7`):

| pos | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| event | `E1` | `E0` | `E2` | `E3` | `E5` | `E4` | `E7` | `E6` |
| action | `p_1 → p_0` | `p_0` recv `E1` | `p_0 → p_3` | `p_3` recv `E2` | `p_2 → p_0` | `p_0` recv `E5` | `p_1 → p_0` | `p_0` recv `E7` |

The happened-before order of this diagram has order dimension `> 2`: with `d = E3`, `e = E4`,
`f = E5`, `h = E7`, both `{d, f, h}` and `{d, e, h}` are antichains; in each coordinate `h` must
lie between `d` and `f` (otherwise `E6` would be above `d`, or `E1` below `f`) and `e` between
`d` and `h` (otherwise `E6` above `d`, or `E0` below `h`), which contradicts `f < e`.
-/

namespace Podc.DelayedTimestamps

open Cslib.Causality

/-- The execution of Figure 4 on the star graph with 4 processes. -/
def fig4 : Exec (Fin 4) :=
  [.send 1 0, .recv 0 0, .send 0 3, .recv 3 2, .send 2 0, .recv 0 4, .send 1 0, .recv 0 6]

/-- The happened-before relation of Figure 4 (pairs of positions). -/
def fig4HB (i j : ℕ) : Bool :=
  (i, j) ∈ [(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 5), (1, 7),
    (2, 3), (2, 5), (2, 7), (4, 5), (4, 7), (5, 7), (6, 7)]

lemma fig4_wf : fig4.WF := by
  constructor
  · intro j p m h
    have hj : j < 8 := (List.getElem?_eq_some_iff.1 h).1
    interval_cases j <;> simp [fig4] at h <;> omega
  · intro j p m h
    have hj : j < 8 := (List.getElem?_eq_some_iff.1 h).1
    interval_cases j <;> simp [fig4] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp [fig4]
  · intro j j' p p' m h h'
    have hj : j < 8 := (List.getElem?_eq_some_iff.1 h).1
    have hj' : j' < 8 := (List.getElem?_eq_some_iff.1 h').1
    interval_cases j <;> interval_cases j' <;> simp [fig4] at h h' <;> omega

lemma fig4_onGraph : fig4.OnGraph (star 3) := by
  intro j p q h
  have hj : j < 8 := (List.getElem?_eq_some_iff.1 h).1
  interval_cases j <;> simp [fig4] at h <;> obtain ⟨rfl, rfl⟩ := h <;> rw [star_adj] <;> decide

lemma fig4_step (i j : ℕ) (h : fig4.Step i j) : fig4HB i j := by
  have hj : j < 8 := h.lt_length
  have hi : i < j := h.lt fig4_wf
  rw [Exec.step_iff] at h
  interval_cases j <;> interval_cases i <;> revert h <;> decide

lemma fig4HB_trans (i j k : ℕ) (h1 : fig4HB i j) (h2 : fig4HB j k) : fig4HB i k := by
  have hi : i < 8 := by revert h1; unfold fig4HB; simp; omega
  have hj : j < 8 := by revert h1; unfold fig4HB; simp; omega
  have hk : k < 8 := by revert h2; unfold fig4HB; simp; omega
  interval_cases i <;> interval_cases j <;> interval_cases k <;> revert h1 h2 <;> decide

/-- The happened-before relation of Figure 4 is exactly `fig4HB`. -/
lemma fig4_hb_iff (i j : ℕ) : fig4.HB i j ↔ fig4HB i j := by
  constructor
  · exact Exec.HB.le_of_step (R := fun i j => fig4HB i j = true) fig4HB_trans fig4_step
  · intro h
    have step : ∀ a b, fig4.Step a b → fig4.HB a b := fun a b h => .of_step h
    have hs : ∀ a b, (fig4.prev b = some a ∨ ∃ p, fig4[b]? = some (.recv p a)) → fig4.HB a b :=
      fun a b h => step a b (Exec.step_iff.2 h)
    have hi : i < 8 := by revert h; unfold fig4HB; simp; omega
    have hj : j < 8 := by revert h; unfold fig4HB; simp; omega
    have s01 : fig4.HB 0 1 := hs 0 1 (by decide)
    have s12 : fig4.HB 1 2 := hs 1 2 (by decide)
    have s23 : fig4.HB 2 3 := hs 2 3 (by decide)
    have s25 : fig4.HB 2 5 := hs 2 5 (by decide)
    have s45 : fig4.HB 4 5 := hs 4 5 (by decide)
    have s57 : fig4.HB 5 7 := hs 5 7 (by decide)
    have s06 : fig4.HB 0 6 := hs 0 6 (by decide)
    have s67 : fig4.HB 6 7 := hs 6 7 (by decide)
    interval_cases i <;> interval_cases j <;> revert h <;> simp [fig4HB] <;>
      first
      | assumption
      | exact s01.trans s12
      | exact (s01.trans s12).trans s23
      | exact (s01.trans s12).trans s25
      | exact ((s01.trans s12).trans s25).trans s57
      | exact s12.trans s23
      | exact s12.trans s25
      | exact (s12.trans s25).trans s57
      | exact s25.trans s57
      | exact s45.trans s57

/-- Two incomparable distinct vectors of length 2 are in "opposite" position. -/
lemma opp_of_incomp {α : Type*} [LinearOrder α] {u v : Fin 2 → α} (h1 : ¬ u < v) (h2 : ¬ v < u)
    (hne : u ≠ v) : (u 0 < v 0 ∧ v 1 < u 1) ∨ (v 0 < u 0 ∧ u 1 < v 1) := by
  have key : ∀ w z : Fin 2 → α, w 0 ≤ z 0 → w 1 ≤ z 1 → (w 0 < z 0 ∨ w 1 < z 1) → w < z :=
    fun w z h0 h1 h => Pi.lt_def.2 ⟨fun i => by fin_cases i <;> assumption,
      by rcases h with h | h; exacts [⟨0, h⟩, ⟨1, h⟩]⟩
  rcases lt_trichotomy (u 0) (v 0) with a | a | a <;>
    rcases lt_trichotomy (u 1) (v 1) with b | b | b
  · exact absurd (key u v a.le b.le (Or.inl a)) h1
  · exact absurd (key u v a.le b.le (Or.inl a)) h1
  · exact Or.inl ⟨a, b⟩
  · exact absurd (key u v a.le b.le (Or.inr b)) h1
  · exact absurd (funext fun i => by fin_cases i; exacts [a, b]) hne
  · exact absurd (key v u a.ge b.le (Or.inr b)) h2
  · exact Or.inr ⟨a, b⟩
  · exact absurd (key v u a.le b.ge (Or.inl a)) h2
  · exact absurd (key v u a.le b.le (Or.inl a)) h2

set_option maxHeartbeats 4000000 in
/-- **Theorem 2** of [Vaidya–Kulkarni] (Appendix C): on the star graph with 4 processes, the
execution of Figure 4 admits no assignment of vectors of length 2 (with entries in any linear
order, e.g. reals) such that `e → f ↔ τ(e) < τ(f)`. Hence no offline algorithm uses vectors of
length 2. (Distinctness of the timestamps is not even needed.) -/
theorem theorem_2 {α : Type*} [LinearOrder α] :
    fig4.WF ∧ fig4.OnGraph (star 3) ∧
      ∀ τ : ℕ → (Fin 2 → α), ¬ ∀ i j, i < fig4.length → j < fig4.length →
        (fig4.HB i j ↔ τ i < τ j) := by
  refine ⟨fig4_wf, fig4_onGraph, fun τ hτ => ?_⟩
  have R : ∀ i j, i < 8 → j < 8 → (fig4HB i j ↔ τ i < τ j) := fun i j hi hj => by
    rw [← fig4_hb_iff]; exact hτ i j hi hj
  have pos : ∀ i j, i < 8 → j < 8 → fig4HB i j = true → τ i < τ j :=
    fun i j hi hj h => (R i j hi hj).1 h
  have neg : ∀ i j, i < 8 → j < 8 → fig4HB i j = false → ¬ τ i < τ j :=
    fun i j hi hj h h' => by simp [(R i j hi hj).2 h'] at h
  -- a = E1 (0), b = E0 (1), d = E3 (3), f = E5 (4), e = E4 (5), h = E7 (6), g = E6 (7)
  have hFE := pos 4 5 (by omega) (by omega) rfl
  have hFG := pos 4 7 (by omega) (by omega) rfl
  have hHG := pos 6 7 (by omega) (by omega) rfl
  have hEG := pos 5 7 (by omega) (by omega) rfl
  have hAD := pos 0 3 (by omega) (by omega) rfl
  have hAH := pos 0 6 (by omega) (by omega) rfl
  have hBD := pos 1 3 (by omega) (by omega) rfl
  have hBE := pos 1 5 (by omega) (by omega) rfl
  have hDG := neg 3 7 (by omega) (by omega) rfl
  have hAF := neg 0 4 (by omega) (by omega) rfl
  have hBH := neg 1 6 (by omega) (by omega) rfl
  have incomp : ∀ i j, i < 8 → j < 8 → fig4HB i j = false → fig4HB j i = false → τ i ≠ τ j →
      (τ i 0 < τ j 0 ∧ τ j 1 < τ i 1) ∨ (τ j 0 < τ i 0 ∧ τ i 1 < τ j 1) :=
    fun i j hi hj h1 h2 hne => opp_of_incomp (neg i j hi hj h1) (neg j i hj hi h2) hne
  have hDF := incomp 3 4 (by omega) (by omega) rfl rfl (fun h => hAF (h ▸ hAD))
  have hDH := incomp 3 6 (by omega) (by omega) rfl rfl (fun h => hBH (h ▸ hBD))
  have hFH := incomp 4 6 (by omega) (by omega) rfl rfl
    (fun h => neg 6 5 (by omega) (by omega) rfl (h ▸ hFE))
  have hDE := incomp 3 5 (by omega) (by omega) rfl rfl (fun h => hDG (h ▸ hEG))
  have hEH := incomp 5 6 (by omega) (by omega) rfl rfl (fun h => hBH (h ▸ hBE))
  have le0 : ∀ {i j}, τ i < τ j → τ i 0 ≤ τ j 0 := fun h => h.le 0
  have le1 : ∀ {i j}, τ i < τ j → τ i 1 ≤ τ j 1 := fun h => h.le 1
  have cn : ∀ {i j}, ¬ τ i < τ j →
      ¬ (τ i 0 ≤ τ j 0 ∧ τ i 1 ≤ τ j 1 ∧ (τ i 0 < τ j 0 ∨ τ i 1 < τ j 1)) :=
    fun h ⟨h0, h1, h2⟩ => h (Pi.lt_def.2 ⟨fun k => by fin_cases k <;> assumption,
      by rcases h2 with h2 | h2; exacts [⟨0, h2⟩, ⟨1, h2⟩]⟩)
  have := le0 hFE; have := le1 hFE; have := le0 hFG; have := le1 hFG
  have := le0 hHG; have := le1 hHG; have := le0 hEG; have := le1 hEG
  have := le0 hAD; have := le1 hAD; have := le0 hAH; have := le1 hAH
  have := le0 hBD; have := le1 hBD; have := le0 hBE; have := le1 hBE
  have hDG' := cn hDG
  have hAF' := cn hAF
  have hBH' := cn hBH
  clear le0 le1 cn hDG hAF hBH hFE hFG hHG hEG hAD hAH hBD hBE incomp neg pos R hτ
  generalize τ 0 0 = a0 at *; generalize τ 0 1 = a1 at *
  generalize τ 1 0 = b0 at *; generalize τ 1 1 = b1 at *
  generalize τ 3 0 = d0 at *; generalize τ 3 1 = d1 at *
  generalize τ 4 0 = f0 at *; generalize τ 4 1 = f1 at *
  generalize τ 5 0 = e0 at *; generalize τ 5 1 = e1 at *
  generalize τ 6 0 = h0 at *; generalize τ 6 1 = h1 at *
  generalize τ 7 0 = g0 at *; generalize τ 7 1 = g1 at *
  rcases hDF with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases hDH with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases hFH with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases hDE with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases hEH with ⟨_, _⟩ | ⟨_, _⟩ <;>
    first
    | order
    | (refine absurd ⟨?_, ?_, Or.inl ?_⟩ hDG' <;> order)
    | (refine absurd ⟨?_, ?_, Or.inr ?_⟩ hDG' <;> order)
    | (refine absurd ⟨?_, ?_, Or.inl ?_⟩ hAF' <;> order)
    | (refine absurd ⟨?_, ?_, Or.inr ?_⟩ hAF' <;> order)
    | (refine absurd ⟨?_, ?_, Or.inl ?_⟩ hBH' <;> order)

end Podc.DelayedTimestamps
