import Papers.PODC2012.IterativeApproxBC.Condition
import Cslib.Computability.Distributed.ApproxConsensus.Trim
import Mathlib

/-!
# Algorithm 1 of [VTL12] (trimmed mean), validity (Theorem 2), Lemmas 3 and 4

Algorithm 1: node `i` drops the `f` smallest and the `f` largest received values (ties broken
arbitrarily) and sets its state to the average of its own state and the remaining
`|N_i⁻| - 2f` values, all with weight `a_i = 1 / (|N_i⁻| + 1 - 2f)`.

* `alg1Step G f` — Algorithm 1 as a *step relation*: any valid trimming may be used, in every
  iteration anew (so tie-breaking may be arbitrary, time-dependent and even adversarial).
* `TieBreak G f` — a deterministic tie-breaking rule; `TieBreak.alg` is then an `IterAlg`
  (a transition function `Z_i` of the paper), whose runs are runs of `alg1Step`
  (`TieBreak.isRun`). `TieBreak.nonempty`: such a rule exists if every `|N_i⁻| ≥ 2f`.
* `alg1_lower_step`, `alg1_upper_step` — Lemmas 3 and 4 (with arbitrary lower/upper bounds `ψ`,
  `Ψ` of the fault-free states), plus the "`f + 1` in-neighbours in `P`" step used in Claim 1.
* `alg1_validStep` — **Theorem 2** (validity (1)).
-/

open Finset Cslib.ApproxConsensus

namespace IterativeApproxBC

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} {f : ℕ}

/-- **Algorithm 1** of [VTL12] with arbitrary tie-breaking, as a step relation: `v'` is a
possible new state of `i` (received vector `r`, own state `v`). -/
def alg1Step (G : Digraph V) (f : ℕ) : V → (V → ℝ) → ℝ → ℝ → Prop :=
  fun i r v v' => ∃ Low Mid High, IsTrim (inNbrs G i) f r Low Mid High ∧ v' = tmean Mid r v

/-- A deterministic tie-breaking rule for Algorithm 1 (it may depend on the node, the received
vector and the own state). -/
structure TieBreak (G : Digraph V) (f : ℕ) where
  /-- Values dropped as "smallest". -/
  low : V → (V → ℝ) → ℝ → Finset V
  /-- Kept values. -/
  mid : V → (V → ℝ) → ℝ → Finset V
  /-- Values dropped as "largest". -/
  high : V → (V → ℝ) → ℝ → Finset V
  isTrim : ∀ i r v, IsTrim (inNbrs G i) f r (low i r v) (mid i r v) (high i r v)

/-- Algorithm 1 with a fixed tie-breaking rule, as an iterative algorithm `Z_i`. -/
noncomputable def TieBreak.alg (tb : TieBreak G f) : IterAlg V :=
  ⟨fun i r v => tmean (tb.mid i r v) r v⟩

theorem TieBreak.isRun (tb : TieBreak G f) (S : Scenario V) :
    IsRun G (alg1Step G f) S (tb.alg.run G S) :=
  ⟨rfl, fun _ i _ => ⟨_, _, _, tb.isTrim i _ _, rfl⟩⟩

/-- Tie-breaking rules exist as soon as every node has at least `2f` in-neighbours. -/
theorem TieBreak.nonempty (h : ∀ i, 2 * f ≤ #(inNbrs G i)) : Nonempty (TieBreak G f) := by
  have := fun i (r : V → ℝ) (_ : ℝ) => IsTrim.exists (inNbrs G i) f r (h i)
  choose low mid high hT using this
  exact ⟨⟨low, mid, high, hT⟩⟩

/-- The weight `a_i = 1 / (|N_i⁻| - 2f + 1)` of Algorithm 1. -/
noncomputable def weight (G : Digraph V) (f : ℕ) (i : V) : ℝ :=
  (((#(inNbrs G i) - 2 * f : ℕ) : ℝ) + 1)⁻¹

theorem weight_pos (i : V) : 0 < weight G f i := by unfold weight; positivity

variable {S : Scenario V} {x : ℕ → V → ℝ}

/-- One step of a run of Algorithm 1 at a fault-free node, unpacked. -/
theorem alg1_unfold (hx : IsRun G (alg1Step G f) S x) (t : ℕ) {i : V} (hi : i ∉ S.F) :
    ∃ Low Mid High, IsTrim (inNbrs G i) f (recv G S.F (S.adv t) (x t) i) Low Mid High ∧
      x (t + 1) i = tmean Mid (recv G S.F (S.adv t) (x t) i) (x t i) ∧
      ((#Mid : ℝ) + 1)⁻¹ = weight G f i :=
  by
  obtain ⟨Low, Mid, High, hT, he⟩ := hx.2 t i hi
  exact ⟨Low, Mid, High, hT, he, by rw [weight, hT.card_mid]⟩

/-- Kept values are bounded by fault-free states (Lemma 3/4, second case). -/
theorem kept_bounds (hF : #S.F ≤ f) {Low Mid High : Finset V} {t : ℕ} {i : V}
    (hT : IsTrim (inNbrs G i) f (recv G S.F (S.adv t) (x t) i) Low Mid High) {j : V}
    (hj : j ∈ Mid) :
    (∃ k ∉ S.F, x t k ≤ recv G S.F (S.adv t) (x t) i j) ∧
      (∃ k ∉ S.F, recv G S.F (S.adv t) (x t) i j ≤ x t k) := by
  obtain ⟨k, hkN, hkF, hk⟩ := hT.exists_correct_le hF hj
  obtain ⟨k', hkN', hkF', hk'⟩ := hT.exists_le_correct hF hj
  rw [recv_of_mem hkN hkF] at hk
  rw [recv_of_mem hkN' hkF'] at hk'
  exact ⟨⟨k, hkF, hk⟩, ⟨k', hkF', hk'⟩⟩

/-- **Lemma 3** of [VTL12] (in a form with an arbitrary lower bound `ψ` of the fault-free states
at time `t`): the new state of a fault-free `i` is `≥ ψ`, exceeds `ψ` by at least `a_i` times the
excess of its own old state, and — if `P` is a set of at least `f + 1` fault-free in-neighbours
(and `|N_i⁻| ≥ 2f+1` when `f > 0`) — by at least `a_i` times the excess of some `p ∈ P`. -/
theorem alg1_lower_step (hx : IsRun G (alg1Step G f) S x) (hF : #S.F ≤ f) (t : ℕ) {i : V}
    (hi : i ∉ S.F) (ψ : ℝ) (hψ : ∀ j ∉ S.F, ψ ≤ x t j) :
    ψ ≤ x (t + 1) i ∧ weight G f i * (x t i - ψ) ≤ x (t + 1) i - ψ ∧
      ∀ P ⊆ inNbrs G i \ S.F, f + 1 ≤ #P → (0 < f → 2 * f + 1 ≤ #(inNbrs G i)) →
        ∃ p ∈ P, weight G f i * (x t p - ψ) ≤ x (t + 1) i - ψ := by
  obtain ⟨Low, Mid, High, hT, he, hw⟩ := alg1_unfold hx t hi
  set r := recv G S.F (S.adv t) (x t) i
  have hr : ∀ j ∈ Mid, ψ ≤ r j := fun j hj => by
    obtain ⟨⟨k, hk, h⟩, -⟩ := kept_bounds hF hT hj
    exact (hψ k hk).trans h
  obtain ⟨h1, h2⟩ := tmean_sub_ge Mid r (x t i) ψ (hψ i hi) hr
  rw [← he, div_eq_inv_mul, hw] at h1
  have hpos := weight_pos (G := G) (f := f) i
  refine ⟨?_, h1, ?_⟩
  · nlinarith [hψ i hi]
  · intro P hP hPc hdeg
    have hPN : P ⊆ inNbrs G i := hP.trans sdiff_subset
    have hN : 2 * f + 1 ≤ #(inNbrs G i) := by
      rcases Nat.eq_zero_or_pos f with h0 | h0
      · have := card_le_card hPN; omega
      · exact hdeg h0
    obtain ⟨p, hp, w, hw', hpw⟩ := hT.exists_le_mid hN hPN hPc
    have hpF : p ∉ S.F := (mem_sdiff.mp (hP hp)).2
    rw [show r p = x t p from recv_of_mem (hPN hp) hpF] at hpw
    refine ⟨p, hp, ?_⟩
    have := h2 w hw'
    rw [← he, div_eq_inv_mul, hw] at this
    nlinarith

/-- **Lemma 4** of [VTL12]: the mirror image of `alg1_lower_step`. -/
theorem alg1_upper_step (hx : IsRun G (alg1Step G f) S x) (hF : #S.F ≤ f) (t : ℕ) {i : V}
    (hi : i ∉ S.F) (Ψ : ℝ) (hΨ : ∀ j ∉ S.F, x t j ≤ Ψ) :
    x (t + 1) i ≤ Ψ ∧ weight G f i * (Ψ - x t i) ≤ Ψ - x (t + 1) i ∧
      ∀ P ⊆ inNbrs G i \ S.F, f + 1 ≤ #P → (0 < f → 2 * f + 1 ≤ #(inNbrs G i)) →
        ∃ p ∈ P, weight G f i * (Ψ - x t p) ≤ Ψ - x (t + 1) i := by
  obtain ⟨Low, Mid, High, hT, he, hw⟩ := alg1_unfold hx t hi
  set r := recv G S.F (S.adv t) (x t) i
  have hr : ∀ j ∈ Mid, r j ≤ Ψ := fun j hj => by
    obtain ⟨-, ⟨k, hk, h⟩⟩ := kept_bounds hF hT hj
    exact h.trans (hΨ k hk)
  obtain ⟨h1, h2⟩ := sub_tmean_ge Mid r (x t i) Ψ (hΨ i hi) hr
  rw [← he, div_eq_inv_mul, hw] at h1
  have hpos := weight_pos (G := G) (f := f) i
  refine ⟨?_, h1, ?_⟩
  · nlinarith [hΨ i hi]
  · intro P hP hPc hdeg
    have hPN : P ⊆ inNbrs G i := hP.trans sdiff_subset
    have hN : 2 * f + 1 ≤ #(inNbrs G i) := by
      rcases Nat.eq_zero_or_pos f with h0 | h0
      · have := card_le_card hPN; omega
      · exact hdeg h0
    obtain ⟨p, hp, w, hw', hpw⟩ := hT.exists_mid_le hN hPN hPc
    have hpF : p ∉ S.F := (mem_sdiff.mp (hP hp)).2
    rw [show r p = x t p from recv_of_mem (hPN hp) hpF] at hpw
    refine ⟨p, hp, ?_⟩
    have := h2 w hw'
    rw [← he, div_eq_inv_mul, hw] at this
    nlinarith

/-- **Theorem 2** of [VTL12]: Algorithm 1 (with any tie-breaking) satisfies validity (1):
`μ[t-1] ≤ v_i[t] ≤ U[t-1]`. Only `|F| ≤ f` is needed (no graph condition): the runs of
`alg1Step` already presuppose that trimming is possible. -/
theorem alg1_validStep (hx : IsRun G (alg1Step G f) S x) (hF : #S.F ≤ f) :
    ValidStep S.F x := by
  classical
  intro t i hi
  have hX : (univ \ S.F).Nonempty := ⟨i, by simpa using hi⟩
  obtain ⟨j, hj, hjmin⟩ := exists_min_image (univ \ S.F) (x t) hX
  obtain ⟨k, hk, hkmax⟩ := exists_max_image (univ \ S.F) (x t) hX
  simp only [mem_sdiff, mem_univ, true_and] at hj hk hjmin hkmax
  exact ⟨⟨j, hj, (alg1_lower_step hx hF t hi _ hjmin).1⟩, ⟨k, hk, (alg1_upper_step hx hF t hi _ hkmax).1⟩⟩

end IterativeApproxBC
