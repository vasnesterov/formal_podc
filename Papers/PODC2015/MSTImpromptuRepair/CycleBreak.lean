import Cslib.Probability.Finite.Uniform
import Cslib.Foundations.Data.Fin.Cyclic

/-!
# Breaking a cycle by random unmarking (Section 4.2 / Appendix B)

In `Build ST`, the fragments' chosen edges may close a cycle `v₀, v₁, …, v_{k-1}`. Each node on the
cycle picks one of its two cycle edges at random (`c i = true`: the edge `{vᵢ, vᵢ₊₁}`, `false`:
the edge `{vᵢ₋₁, vᵢ}`); an edge picked by both of its endpoints is unmarked.

* `unmarked c i` — edge `{vᵢ, vᵢ₊₁}` is picked by both endpoints.
* `no_unmarked_iff` — no edge is unmarked iff all nodes pick the same direction;
  `uprob_no_unmarked` — **this happens with probability `1/2^(k-1)`** (Appendix B).
* `two_mul_card_unmarked_le` — **at most half of the cycle edges are unmarked**.
-/

namespace Podc.MSTImpromptuRepair.CycleBreak

open Finset Cslib.Probability

variable {k : ℕ} [NeZero k]

/-- Edge `{vᵢ, vᵢ₊₁}` is unmarked: `vᵢ` picks it (forward) and `vᵢ₊₁` picks it (backward). -/
def unmarked (c : Fin k → Bool) (i : Fin k) : Prop := c i = true ∧ c (i + 1) = false

instance (c : Fin k → Bool) : DecidablePred (unmarked c) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

theorem forall_of_not_unmarked {c : Fin k → Bool} (h : ∀ i, ¬ unmarked c i) {i : Fin k}
    (hi : c i = true) : ∀ t : ℕ, c ((· + 1)^[t] i) = true := by
  intro t
  induction t with
  | zero => simpa using hi
  | succ t ih =>
    have := h ((· + 1)^[t] i)
    unfold unmarked at this
    rw [Function.iterate_succ_apply']
    cases hc : c ((· + 1)^[t] i + 1)
    · exact absurd ⟨ih, hc⟩ this
    · rfl

/-- No edge is unmarked iff all nodes on the cycle pick the same direction. -/
theorem no_unmarked_iff (c : Fin k → Bool) :
    (∀ i, ¬ unmarked c i) ↔ c = (fun _ => true) ∨ c = (fun _ => false) := by
  constructor
  · intro h
    by_cases hex : ∃ i, c i = true
    · obtain ⟨i, hi⟩ := hex
      left; funext j
      obtain ⟨t, ht⟩ := Fin.exists_iterate_add_one_eq i j
      have := forall_of_not_unmarked h hi t
      rwa [ht] at this
    · right; funext j; push_neg at hex; simpa using hex j
  · rintro (rfl | rfl) i <;> simp [unmarked]

/-- **Appendix B**: on a cycle of `k` nodes, no edge gets unmarked with probability
`2 / 2^k = 1 / 2^(k-1)`. -/
theorem uprob_no_unmarked : uprob (fun c : Fin k → Bool => ∀ i, ¬ unmarked c i) = 2 / 2 ^ k := by
  classical
  rw [uprob_eq_card_filter]
  have : (univ.filter fun c : Fin k → Bool => ∀ i, ¬ unmarked c i) =
      {fun _ => true, fun _ => false} := by
    ext c; simp [no_unmarked_iff]
  rw [this, card_pair]
  · simp
  · intro h; have := congrFun h 0; simp at this

/-- **Appendix B**: at most half of the cycle edges are unmarked (each unmarked edge uses the picks
of both its endpoints). -/
theorem two_mul_card_unmarked_le (c : Fin k → Bool) :
    2 * #(univ.filter (unmarked c)) ≤ k := by
  classical
  set A := univ.filter (unmarked c)
  have hdisj : Disjoint A (A.image (· + 1)) := by
    rw [disjoint_left]
    intro i hi hi'
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hi'
    have h1 := (mem_filter.1 hi).2.1
    have h2 := (mem_filter.1 hj).2.2
    rw [h1] at h2; exact Bool.noConfusion h2
  have hcard : #(A.image (· + 1)) = #A := card_image_of_injective _ (add_left_injective 1)
  have := card_union_of_disjoint hdisj
  have hle : #(A ∪ A.image (· + 1)) ≤ k := by
    simpa using card_le_univ (A ∪ A.image (· + 1))
  omega

end Podc.MSTImpromptuRepair.CycleBreak
