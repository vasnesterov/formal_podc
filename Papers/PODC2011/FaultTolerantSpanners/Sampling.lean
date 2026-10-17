import Podc.Probability.Finite.Uniform
import Mathlib

/-!
# Finite uniform probability for the sampling argument of Section 2

The conversion of Theorem 2.1 puts every vertex into the "fault set" `J` independently with
probability `p = 1 - 1/m` (the paper uses `m = r`, and `m = 2` when `r = 1`). We realise this
exactly on a *finite uniform* sample space: every vertex draws a uniform label in `Fin m` and
survives (is not in `J`) iff its label is `0`. Repeating `α` times independently is the uniform
distribution on `Fin α → V → Fin m`. Probabilities are then ratios of cardinalities (`uprob`, from
the shared finite-probability library `Podc/Probability/Finite/Uniform.lean`, with the union bound
`uprob_exists_le` and independence `uprob_pi`), and no measure theory is needed.

Main facts:
* `uprob_card_surv_gt` — a Chernoff bound for the number of survivors:
  `Pr[#{v : s v = 0} > c] ≤ (1 + 1/m)^n / 2^c`, and `uprob_card_surv_gt_two_mul` —
  `Pr[#{v : s v = 0} > 2n/m] ≤ exp(-n/(3m))` (the paper's `e^{-(1/3) n/r}`).
* `card_faultSets_le` — there are at most `(n + 1)^r` fault sets of size `≤ r`.
-/

open Finset Cslib.Probability

namespace DinitzKrauthgamer

/-! ### Survivors and a Chernoff bound -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices that survive a sample `s : V → Fin m` (label `0`), i.e. `V \ J`. -/
def surv {m : ℕ} (s : V → Fin m) [NeZero m] : Finset V := univ.filter fun v => s v = 0

/-- **Chernoff bound (counting form).** For a uniform sample `s : V → Fin m` and any real `c`,
`Pr[#survivors > c] ≤ (1 + 1/m)^n / 2^c` (`uprob_lt_card_filter_mem_le` with `B = {0}`). -/
lemma uprob_card_surv_gt (m : ℕ) [NeZero m] (c : ℝ) :
    uprob (fun s : V → Fin m => c < #(surv s)) ≤
      (1 + 1 / (m : ℝ)) ^ Fintype.card V / (2 : ℝ) ^ c := by
  simpa [surv] using uprob_lt_card_filter_mem_le (ι := V) ({0} : Finset (Fin m)) c

/-- **Chernoff bound used in Theorem 2.1.** `Pr[#survivors > 2n/m] ≤ exp(-n/(3m))`. -/
lemma uprob_card_surv_gt_two_mul (m : ℕ) [NeZero m] :
    uprob (fun s : V → Fin m => 2 * (Fintype.card V : ℝ) / m < #(surv s)) ≤
      Real.exp (-((Fintype.card V : ℝ) / (3 * m))) := by
  refine (uprob_card_surv_gt m _).trans ?_
  set n := Fintype.card V
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have h1 : (1 + 1 / (m : ℝ)) ^ n ≤ Real.exp ((n : ℝ) / m) := by
    calc (1 + 1 / (m : ℝ)) ^ n ≤ Real.exp (1 / (m : ℝ)) ^ n := by
          gcongr
          linarith [Real.add_one_le_exp (1 / (m : ℝ))]
      _ = Real.exp ((n : ℝ) / m) := by rw [← Real.exp_nat_mul]; ring_nf
  have h2 : (2 : ℝ) ^ (2 * (n : ℝ) / m) = Real.exp (2 * (n : ℝ) / m * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  rw [h2, div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  have hlog : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hn : (0 : ℝ) ≤ n / m := by positivity
  have : -((n : ℝ) / (3 * m)) + 2 * n / m * Real.log 2 = (n / m) * (2 * Real.log 2 - 1 / 3) := by
    field_simp
    ring
  rw [this]
  nlinarith

/-- The number of fault sets of size at most `r` is at most `(n + 1)^r`. -/
lemma card_faultSets_le (r : ℕ) :
    #(univ.filter fun F : Finset V => #F ≤ r) ≤ (Fintype.card V + 1) ^ r := by
  set n := Fintype.card V
  have hsub : (univ.filter fun F : Finset V => #F ≤ r) ⊆
      (range (r + 1)).biUnion fun i => powersetCard i univ := by
    intro F hF
    rw [mem_filter] at hF
    simp only [mem_biUnion, mem_range, mem_powersetCard]
    exact ⟨#F, by omega, subset_univ _, rfl⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  simp only [card_powersetCard, card_univ]
  rw [add_pow]
  refine Finset.sum_le_sum fun i hi => ?_
  simp only [one_pow, mul_one]
  have hi' : i ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hi)
  calc n.choose i ≤ n ^ i := Nat.choose_le_pow n i
    _ ≤ n ^ i * r.choose i := Nat.le_mul_of_pos_right _ (Nat.choose_pos hi')

end DinitzKrauthgamer
