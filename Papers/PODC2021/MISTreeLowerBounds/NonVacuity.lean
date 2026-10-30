import Papers.PODC2021.MISTreeLowerBounds.Family

/-!
# Non-vacuity: `k`-outdegree dominating sets are solvable in the model

The lower bound `odsLowerBound` is not vacuous: in our model (`Δ`-regular tree, `Δ`-edge colouring,
edge orientation, deterministic) an MIS, hence a `k`-outdegree dominating set for every `k`, can be
computed in `2^Δ` rounds.

The direction bits of the `Δ` incident edges form a proper vertex colouring with `2^Δ` colours
(the endpoints of the edge of colour `c` disagree on bit `c`); the greedy MIS by increasing colour
rank (`inS`: a node joins iff no lower-ranked neighbour joins) only depends on decreasing chains of
ranks, hence on the radius-`2^Δ` view.
-/

namespace Podc.MISTreeLowerBounds

open Cslib.ColourSystem FreeCox

namespace NonVacuity

variable {Δ : ℕ}

/-- The colour of `v`: its direction bits. -/
def col (I : Orientation Δ) (v : FreeCox Δ) : Fin Δ → Bool := fun c => I.dir v c

/-- The rank of the colour of `v` in a fixed enumeration of `Fin Δ → Bool`. -/
noncomputable def rk (I : Orientation Δ) (v : FreeCox Δ) : ℕ :=
  (Fintype.equivFin (Fin Δ → Bool) (col I v)).val

theorem rk_lt (I : Orientation Δ) (v : FreeCox Δ) : rk I v < 2 ^ Δ := by
  have := (Fintype.equivFin (Fin Δ → Bool) (col I v)).isLt
  unfold rk
  convert this using 1
  simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem rk_ne (I : Orientation Δ) (v : FreeCox Δ) (c : Fin Δ) : rk I (v * gen c) ≠ rk I v := by
  intro h
  have h' := (Fintype.equivFin (Fin Δ → Bool)).injective (Fin.ext h)
  have := congrFun h' c
  simp only [col, I.anti] at this
  cases hb : I.dir v c <;> simp [hb] at this

theorem rk_shift (I : Orientation Δ) (u v : FreeCox Δ) : rk (I.shift u) v = rk I (u * v) := rfl

/-- Greedy MIS: `v` joins iff no neighbour of smaller rank joins. -/
def inS (I : Orientation Δ) (v : FreeCox Δ) : Prop :=
  ∀ c, ∀ _ : rk I (v * gen c) < rk I v, ¬ inS I (v * gen c)
termination_by rk I v

theorem inS_iff (I : Orientation Δ) (v : FreeCox Δ) :
    inS I v ↔ ∀ c, rk I (v * gen c) < rk I v → ¬ inS I (v * gen c) := by
  rw [inS]

theorem inS_shift (I : Orientation Δ) (u v : FreeCox Δ) : inS (I.shift u) v ↔ inS I (u * v) := by
  induction h : rk I (u * v) using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    rw [inS_iff, inS_iff]
    simp only [rk_shift, ← mul_assoc]
    refine forall_congr' fun c => imp_congr_right fun hc => not_congr ?_
    rw [mul_assoc]
    exact ih _ (h ▸ hc) _ (by rw [mul_assoc])

/-- Locality: `inS` at `w` only depends on the edges within distance `rk w + 1` of `w`. -/
theorem inS_congr {m : ℕ} {I J : Orientation Δ} (hIJ : AgreeOn m I J) :
    ∀ w, len w + rk I w + 1 ≤ m → (inS I w ↔ inS J w) := by
  have hrk : ∀ w, len w + 1 ≤ m → rk I w = rk J w := by
    intro w hw
    unfold rk
    rw [show col I w = col J w from funext fun c => hIJ w c (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; exact (len_mul_gen_le w c).trans hw)]
  intro w
  induction h : rk I w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    intro hw
    rw [inS_iff, inS_iff, ← hrk w (by omega)]
    refine forall_congr' fun c => ?_
    have hlen := len_mul_gen_le w c
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      constructor <;> intro _ hc <;> omega
    · rw [← hrk (w * gen c) (by omega)]
      refine imp_congr_right fun hc => not_congr ?_
      exact ih _ (h ▸ hc) _ rfl (by omega)

/-- The greedy MIS as a `k`-ODS algorithm (`S` = the MIS, no edge inside `S`). -/
noncomputable def misAlg (I : Orientation Δ) : Bool × (Fin Δ → Bool) := by
  classical
  exact (decide (inS I 1), fun _ => false)

end NonVacuity

open NonVacuity

/-- Non-vacuity of the lower bound: an MIS (a `k`-outdegree dominating set for every `k`) can be
computed in `2^Δ` rounds in our model. -/
theorem odsSolvable (Δ k : ℕ) : ODSSolvableIn Δ k (2 ^ Δ) := by
  classical
  refine ⟨misAlg, fun I J hIJ => ?_, fun I v => ?_⟩
  · simp only [misAlg, Prod.mk.injEq, and_true]
    rw [decide_eq_decide]
    exact inS_congr hIJ 1 (by have := rk_lt I 1; simp [len_one]; omega)
  · simp only [misAlg, decide_eq_true_eq, inS_shift, mul_one]
    refine ⟨?_, fun c h1 h2 => ?_, fun _ => by simp⟩
    swap
    · exfalso
      rcases lt_or_gt_of_ne (rk_ne I v c) with hlt | hlt
      · exact (inS_iff I v).1 h1 c hlt h2
      · have := (inS_iff I (v * gen c)).1 h2 c (by rwa [mul_gen_mul_gen])
        rw [mul_gen_mul_gen] at this
        exact this h1
    by_cases hv : inS I v
    · exact Or.inl hv
    · right
      rw [inS_iff] at hv
      push Not at hv
      obtain ⟨c, -, hc⟩ := hv
      exact ⟨c, hc⟩

end Podc.MISTreeLowerBounds
