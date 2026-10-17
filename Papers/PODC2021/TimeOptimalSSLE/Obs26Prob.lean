import Papers.PODC2021.TimeOptimalSSLE.Observations
import Papers.PODC2021.TimeOptimalSSLE.RandomScheduler

/-!
# Observation 2.6: the geometric waiting time

For a deterministic protocol under the uniformly random scheduler: if `C` is silent and `C'` is
`C` with the state of `ℓ` copied to `u ≠ ℓ`, then the chain started at `C'` is still at `C'` after
`t` interactions with probability at least `(1 - 2/(n(n-1)))^t`, where `n = |A|`
(`obs26_stay_prob`). With a unique leader `ℓ` in `C`, `C'` has two leaders
(`obs26_two_leaders`), so the convergence time from `C'` dominates a geometric random variable
with success probability `1 / C(n,2)`: its expectation is at least `C(n,2)` interactions, i.e.
`(n-1)/2` parallel time — the `Ω(n)` part of Observation 2.6.
-/

open Cslib.PopulationProtocol Cslib.Probability.Markov Matrix Finset

namespace TimeOptimalSSLE.NProtocol

variable {Q A : Type*} [DecidableEq A] [Fintype A] [Fintype Q] [DecidableEq Q]

lemma card_pairs : Fintype.card (Pairs A) = Fintype.card A * (Fintype.card A - 1) := by
  classical
  rw [Fintype.card_subtype]
  have : (univ.filter fun x : A × A => x.1 ≠ x.2) = (univ : Finset A).offDiag := by
    ext x; simp [mem_offDiag]
  rw [this, offDiag_card, card_univ, Nat.mul_sub_one]

/-- **Observation 2.6 (probabilistic part).** Staying probability at the two-leader configuration
`C'`: at least `(1 - 2/(n(n-1)))^t` after `t` interactions. -/
theorem obs26_stay_prob (P : Protocol Q) (hA : 2 ≤ Fintype.card A) {C : Config A Q}
    (hC : (ofProtocol P).Silent C) {ℓ u : A} (hℓu : ℓ ≠ u) (t : ℕ) :
    (1 - 2 / ((Fintype.card A : ℝ) * (Fintype.card A - 1))) ^ t ≤
      (uniformKernel (A := A) P ^ t) (Function.update C u (C ℓ)) (Function.update C u (C ℓ)) := by
  classical
  set C' := Function.update C u (C ℓ)
  set T := uniformKernel (A := A) P
  have hT := uniformKernel_mem (Q := Q) P hA
  set N : ℝ := (Fintype.card A : ℝ) * (Fintype.card A - 1)
  have hN : (Fintype.card (Pairs A) : ℝ) = N := by
    rw [card_pairs]; simp only [N]; push_cast [Nat.cast_sub (by omega : 1 ≤ Fintype.card A)]; ring
  have hNpos : 0 < N := by
    simp only [N]
    have : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hA
    nlinarith
  -- one step: all ordered pairs except `(ℓ,u)` and `(u,ℓ)` are null at `C'`
  have hnull : ∀ ω : Pairs A, ω ∉ ({⟨(ℓ, u), hℓu⟩, ⟨(u, ℓ), hℓu.symm⟩} : Finset (Pairs A)) →
      P.interact C' ω.1.1 ω.1.2 = C' := by
    intro ω hω
    obtain ⟨⟨a, b⟩, hab⟩ := ω
    simp only [mem_insert, mem_singleton, Subtype.mk.injEq, Prod.mk.injEq, not_or] at hω
    have hne : ¬ ((a = ℓ ∧ b = u) ∨ (a = u ∧ b = ℓ)) := by tauto
    have h := obs26_null_of_ne (ofProtocol P) hC hℓu hab hne (o := P.δ (C' a) (C' b)) rfl
    funext x
    by_cases hxa : x = a
    · subst hxa; rw [Protocol.interact_self_left]; exact congrArg Prod.fst h
    · by_cases hxb : x = b
      · subst hxb; rw [Protocol.interact_self_right _ _ hab]; exact congrArg Prod.snd h
      · rw [Protocol.interact_other _ _ hxa hxb]
  have hstep : 1 - 2 / N ≤ T C' C' := by
    simp only [T, uniformKernel, randomMap]
    have hsub : ∑ ω : Pairs A, (if P.interact C' ω.1.1 ω.1.2 = C' then
        1 / (Fintype.card (Pairs A) : ℝ) else 0) ≥
        ∑ ω ∈ (univ \ ({⟨(ℓ, u), hℓu⟩, ⟨(u, ℓ), hℓu.symm⟩} : Finset (Pairs A))),
          1 / (Fintype.card (Pairs A) : ℝ) := by
      rw [← Finset.sum_sdiff (Finset.subset_univ
        ({⟨(ℓ, u), hℓu⟩, ⟨(u, ℓ), hℓu.symm⟩} : Finset (Pairs A)))]
      have h1 : ∑ ω ∈ (univ \ ({⟨(ℓ, u), hℓu⟩, ⟨(u, ℓ), hℓu.symm⟩} : Finset (Pairs A))),
          (if P.interact C' ω.1.1 ω.1.2 = C' then 1 / (Fintype.card (Pairs A) : ℝ) else 0) =
          ∑ ω ∈ (univ \ ({⟨(ℓ, u), hℓu⟩, ⟨(u, ℓ), hℓu.symm⟩} : Finset (Pairs A))),
            1 / (Fintype.card (Pairs A) : ℝ) := by
        refine sum_congr rfl fun ω hω => ?_
        rw [ite_eq_left (hnull ω (by simpa using hω))]
      rw [h1]
      have h2 : 0 ≤ ∑ ω ∈ ({⟨(ℓ, u), hℓu⟩, ⟨(u, ℓ), hℓu.symm⟩} : Finset (Pairs A)),
          (if P.interact C' ω.1.1 ω.1.2 = C' then 1 / (Fintype.card (Pairs A) : ℝ) else 0) :=
        sum_nonneg fun ω _ => by split_ifs <;> positivity
      linarith
    refine le_trans ?_ (ge_iff_le.mp hsub)
    rw [sum_const, nsmul_eq_mul, card_sdiff_of_subset (subset_univ _), card_univ, hN]
    have hcard : (({⟨(ℓ, u), hℓu⟩, ⟨(u, ℓ), hℓu.symm⟩} : Finset (Pairs A))).card = 2 := by
      rw [card_pair]; simp [Subtype.ext_iff, hℓu]
    rw [hcard]
    have h2N : 2 ≤ Fintype.card (Pairs A) := by
      rw [card_pairs]
      have h1 : 1 ≤ Fintype.card A - 1 := by omega
      calc 2 = 2 * 1 := by norm_num
        _ ≤ Fintype.card A * (Fintype.card A - 1) := Nat.mul_le_mul hA h1
    rw [Nat.cast_sub h2N, hN]
    field_simp
    exact le_refl _
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, pow_succ, mul_apply]
    have hle : (T ^ t) C' C' * T C' C' ≤ ∑ j, (T ^ t) C' j * T j C' :=
      single_le_sum (f := fun j => (T ^ t) C' j * T j C')
        (fun j _ => mul_nonneg (pow_nonneg_entry hT t _ _) (nonneg_of_mem_rowStochastic hT))
        (mem_univ C')
    have hb : 0 ≤ 1 - 2 / N := by
      rw [sub_nonneg, div_le_one hNpos]
      simp only [N]
      have : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hA
      nlinarith
    calc (1 - 2 / N) ^ t * (1 - 2 / N) ≤ (T ^ t) C' C' * T C' C' :=
          mul_le_mul ih hstep hb (pow_nonneg_entry hT t _ _)
      _ ≤ _ := hle

end TimeOptimalSSLE.NProtocol
