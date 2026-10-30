import Papers.PODC2026.DistinctGathering.TwoPoint

/-!
# Two robots: gathering is trivial

Non-vacuity check of the model, and the claim of [Frei–Wada, PODC 2026] (citing Défago et al.,
Lem. 4) that "for `n = 2` robots the task is trivial: let an activated robot move toward the
opposite location".

`twoAlg` moves straight toward the other observed point. It solves Gathering of two robots from
*every* initial configuration, under *every* centralized schedule (in particular Round-Robin),
with full variable disorientation, and under non-rigid movement with any minimum movement distance
`δ > 0` unknown to the robots (`twoAlg_solves_nonrigid`) as well as rigid movement
(`twoAlg_solves_rigid`).
-/

noncomputable section

namespace Podc.DistinctGathering

open Cslib.MobileRobots

/-- The nonzero point of a view, if any. -/
def target (V : Finset ℂ) : ℂ := if h : ∃ z ∈ V, z ≠ 0 then h.choose else 0

lemma target_pair {w : ℂ} (hw : w ≠ 0) : target {0, w} = w := by
  unfold target
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h.choose_spec
    rcases Finset.mem_insert.1 h1 with h3 | h3
    · exact absurd h3 h2
    · exact Finset.mem_singleton.1 h3
  · exact absurd ⟨w, by simp, hw⟩ h

lemma target_zero : target {0, 0} = 0 := by
  unfold target
  split_ifs with h
  · exfalso
    obtain ⟨z, hz, hz0⟩ := h
    simp at hz
    exact hz0 hz
  · rfl

/-- Move straight toward the other observed point (stay if none). -/
def twoAlg : Algorithm := fun V s => (s : ℂ) * target V

/-- The variation of a straight segment `τ ↦ c + τ v` on `[0, s]` is at most `s ‖v‖`. -/
lemma eVariationOn_segment_le (c v : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    eVariationOn (fun τ : ℝ => c + (τ : ℂ) * v) (Set.Icc 0 s) ≤ ENNReal.ofReal (‖v‖ * s) := by
  have hL : LipschitzOnWith ‖v‖₊ (fun τ : ℝ => c + (τ : ℂ) * v) Set.univ := by
    refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have : c + (x : ℂ) * v - (c + (y : ℂ) * v) = ((x - y : ℝ) : ℂ) * v := by push_cast; ring
    rw [this, norm_mul, Complex.norm_real, mul_comm, coe_nnnorm]
  have h1 := hL.comp_eVariationOn_le (g := id) (s := Set.Icc 0 s) (Set.mapsTo_univ _ _)
  have h2 : eVariationOn (id : ℝ → ℝ) (Set.Icc 0 s) = ENNReal.ofReal (s - 0) := by
    have := (monotoneOn_id (s := Set.Icc (0 : ℝ) s)).eVariationOn_eq
      (a := 0) (b := s) ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩
    simp at this ⊢
  rw [h2, sub_zero] at h1
  refine h1.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  rfl

/-- Distance between the two robots. -/
def gap (P : Config 2) : ℝ := ‖P 1 - P 0‖

lemma gathered_iff_gap (P : Config 2) : Gathered P ↔ gap P = 0 := by
  rw [gap, norm_eq_zero, sub_eq_zero]
  constructor
  · intro h; exact h 1 0
  · intro h i j; fin_cases i <;> fin_cases j <;> simp [h]

/-- One step of `twoAlg` with an admissible non-rigid stop: either the robots meet, or the gap
shrinks by at least `δ`; and a zero gap stays zero. -/
lemma gap_step (δ : ℝ) (P : Config 2) (r : Fin 2) (f : Frame) (s : ℝ)
    (hadm : (Movement.nonrigid δ).Admissible (globalTraj P r f (twoAlg (view P r f))) s) :
    (gap (step twoAlg P r f s) = 0 ∨ gap (step twoAlg P r f s) ≤ gap P - δ) ∧
      (gap P = 0 → gap (step twoAlg P r f s) = 0) := by
  set r' := r.rev
  have hr' : r' ≠ r := by fin_cases r <;> decide
  have hall : ∀ i, i ≠ r → P i = P r' := by
    intro i hi; congr 1; fin_cases r <;> fin_cases i <;> simp_all [r']
  have hview := view_of_all_eq P r r' hr' hall f
  set v := P r' - P r with hv
  -- the global trajectory is the straight segment toward the other robot
  have htraj : globalTraj P r f (twoAlg (view P r f)) = fun τ : ℝ => P r + (τ : ℂ) * v := by
    funext τ
    simp only [globalTraj, twoAlg, hview]
    by_cases h0 : v = 0
    · rw [h0, Frame.toLocal_zero, target_zero, mul_zero, Frame.toGlobal_zero]
    · rw [target_pair (by simpa using h0), Frame.toGlobal_smul, Frame.toGlobal_toLocal]
  have hgapQ : gap (step twoAlg P r f s) = |1 - s| * ‖v‖ := by
    have hQr : step twoAlg P r f s r = P r + (s : ℂ) * v := by
      simp only [step, Function.update_self]; rw [htraj]
    have hQr' : step twoAlg P r f s r' = P r' := step_apply_ne _ _ _ _ hr'
    have : gap (step twoAlg P r f s) = ‖step twoAlg P r f s r' - step twoAlg P r f s r‖ := by
      unfold gap
      fin_cases r
      · rfl
      · rw [← norm_neg, neg_sub]; rfl
    rw [this, hQr, hQr']
    have : P r' - (P r + (s : ℂ) * v) = ((1 - s : ℝ) : ℂ) * v := by
      rw [hv]; push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hgapP : gap P = ‖v‖ := by
    unfold gap; rw [hv]
    fin_cases r
    · rfl
    · rw [← norm_neg, neg_sub]; rfl
  refine ⟨?_, fun h => by rw [hgapQ, ← hgapP, h, mul_zero]⟩
  rw [hgapQ, hgapP]
  rcases hadm with rfl | ⟨hs0, hs1, hvar⟩
  · left; simp
  · right
    rw [htraj] at hvar
    have hle := hvar.trans (eVariationOn_segment_le (P r) v hs0)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
    rw [abs_of_nonneg (by linarith)]
    nlinarith

/-- `twoAlg` gathers two robots from any configuration, under any centralized schedule, with
arbitrary variable disorientation and non-rigid movement with minimum distance `δ > 0` (unknown to
the robots). -/
theorem twoAlg_solves_nonrigid {δ : ℝ} (hδ : 0 < δ) :
    Solves 2 twoAlg (fun _ => True) (fun _ => True) (Movement.nonrigid δ) (fun _ => True) := by
  intro act _ P₀ _ adv hadv
  set D : ℕ → ℝ := fun t => gap (run twoAlg act adv P₀ t)
  have hD : ∀ t, D t = 0 ∨ D t ≤ D 0 - t * δ := by
    intro t
    induction t with
    | zero => right; simp
    | succ t ih =>
      have hs := gap_step δ _ (act t) _ _ (hadv t).2
      simp only [D, run_succ] at ih ⊢
      rcases ih with h | h
      · left; exact hs.2 h
      · rcases hs.1 with h' | h'
        · left; exact h'
        · right; push_cast; linarith
  obtain ⟨T, hT⟩ := exists_nat_gt (D 0 / δ)
  refine ⟨T, fun t ht => ?_⟩
  rw [gathered_iff_gap]
  rcases hD t with h | h
  · exact h
  · exfalso
    have hD0 : 0 ≤ D t := norm_nonneg _
    have : D 0 < t * δ := by
      rw [div_lt_iff₀ hδ] at hT
      have : (T : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith
    linarith

/-- `twoAlg` also solves Gathering of two robots under rigid movement. -/
theorem twoAlg_solves_rigid :
    Solves 2 twoAlg (fun _ => True) (fun _ => True) Movement.rigid (fun _ => True) :=
  (twoAlg_solves_nonrigid one_pos).mono (fun _ h => h) (fun _ h => h)
    (fun _ _ h => Or.inl h) (fun _ h => h)

/-- In particular, Distinct Gathering of two robots under Round-Robin is solvable in the default
model, so the hypotheses of the impossibility theorems are not vacuous for `n = 2`. -/
theorem distinctGathering_two_solvable {δ : ℝ} (hδ : 0 < δ) :
    ∃ A, Solves 2 A IsRoundRobin (fun _ => True) (Movement.nonrigid δ) Function.Injective :=
  ⟨twoAlg, (twoAlg_solves_nonrigid hδ).mono (fun _ _ => trivial) (fun _ h => h)
    (fun _ _ h => h) (fun _ _ => trivial)⟩

end Podc.DistinctGathering

end
