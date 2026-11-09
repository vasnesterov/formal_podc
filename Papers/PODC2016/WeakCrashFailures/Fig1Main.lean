import Papers.PODC2016.WeakCrashFailures.Fig1Live

/-!
# Theorem 1: consensus tolerating one crash (n−1)-failure

The algorithm of Fig. 1 (model in `Fig1Model.lean`) solves consensus for every `n ≥ 2`:
agreement and validity in every execution (Theorem 2, `theorem2_agreement`,
`theorem2_validity`) and termination of every correct process when at most one process crashes,
as an `(n−1)`-failure (Theorem 3, `theorem3`). For `n = 1` the algorithm violates validity
(`fig1_invalid_n1`).
-/

namespace Podc.WeakCrashFailures.Fig1

open Cslib.SWMR

variable {n : ℕ}

/-- **Theorem 1** of [Taubenfeld, PODC'16], for `n ≥ 2`, realised by the algorithm of Fig. 1:
for all inputs (and all initial values of the `input` registers),
* (agreement) in every execution all decided values are equal,
* (validity) every decided value is the input of a participating process,
* (termination) in every infinite execution with at most one crash `(n−1)`-failure, every correct
  process decides. -/
theorem theorem1 (hn : 2 ≤ n) (x inr₀ : Fin n → ℕ) :
    (∀ (σ : ℕ → Fin n) t i j v w, (exec x inr₀ σ t).pc i = .done v →
        (exec x inr₀ σ t).pc j = .done w → v = w) ∧
    (∀ (σ : ℕ → Fin n) t i v, (exec x inr₀ σ t).pc i = .done v → ∃ k ∈ started σ t, x k = v) ∧
    (∀ σ : ℕ → Fin n, WeakAdmissible (n - 1) 1 σ →
        ∀ p, InfOften σ p → ∃ t v, (exec x inr₀ σ t).pc p = .done v) :=
  ⟨fun σ t _ _ _ _ hi hj => theorem2_agreement hn x inr₀ σ t hi hj,
   fun σ t _ _ hi => theorem2_validity hn x inr₀ σ t hi,
   fun σ hF p hp => theorem3 x inr₀ σ hF p hp⟩

/-! ### Non-vacuity of the failure assumption -/

/-- Process `0` never takes a step, the others run round-robin. -/
def skipZero (hn : 2 ≤ n) (t : ℕ) : Fin n := ⟨t % (n - 1) + 1, by
  have := Nat.mod_lt t (show 0 < n - 1 by omega); omega⟩

/-- In `skipZero`, process `0` fails initially (an `(n−1)`-failure) and all others are correct:
the schedule has exactly one crash `(n−1)`-failure, so Theorem 3 applies to it. -/
theorem skipZero_admissible (hn : 2 ≤ n) :
    WeakAdmissible (n - 1) 1 (skipZero hn) ∧ (⟨0, by omega⟩ : Fin n) ∈ Faulty (skipZero hn) := by
  have h0 : InitialFailure (skipZero hn) ⟨0, by omega⟩ := by
    intro s _ h
    simp [skipZero, Fin.ext_iff] at h
  have hinf : ∀ k : Fin n, k.val ≠ 0 → InfOften (skipZero hn) k := by
    intro k hk N
    refine ⟨(k.val - 1) + N * (n - 1), by
      have : N ≤ N * (n - 1) := Nat.le_mul_of_pos_right N (by omega)
      omega, ?_⟩
    have hk' : k.val - 1 < n - 1 := by have := k.isLt; omega
    simp only [skipZero, Fin.ext_iff]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk']
    omega
  have hF : Faulty (skipZero hn) = {⟨0, by omega⟩} := by
    ext k
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hk
      by_contra hk0
      exact hk (hinf k (fun h => hk0 (Fin.ext h)))
    · rintro rfl; exact h0.faulty
  refine ⟨⟨by rw [hF, Set.ncard_singleton], fun k hk => ?_⟩, h0.faulty⟩
  rw [hF] at hk
  rw [hk]
  exact h0.weakFailure _

end Podc.WeakCrashFailures.Fig1
