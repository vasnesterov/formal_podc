/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2020.RedundantOptimization.Convex

/-!
# Theorem 1 (necessity of 2f-redundancy) and what it actually says

Admissible cost functions are the convex differentiable functions on a real inner product space `E`
(the paper: `ℝ^d`). We prove:

* `theorem1` — Theorem 1 as stated, for the class of *all* executions (every honest set of size
  `≥ n - f`, every admissible honest cost functions whose aggregate has a minimum point), with the
  paper's standing assumption `2f < n`;
* `no_resilient_allExecs` — but for `f ≥ 1` and `E ≠ 0` *no* deterministic algorithm is f-resilient
  on that class, so `theorem1` holds vacuously;
* `redundant_execution_confusable` — in the class of all executions even a 2f-redundant execution is
  confused with another one (whose honest costs have *no* common minimum point); this is why the
  literal reading is vacuous;
* `theorem1_indistinguishable` — **Theorem 1 repaired** (what Part II proves): for `f ≥ 1`, `2f < n`,
  exactly `f` faulty agents and honest costs with a common minimum point, `e` is not 2f-redundant iff
  the faulty agents can make `e` indistinguishable from an execution `e'` whose honest costs also share
  a minimum point and whose solution set is disjoint from that of `e`;
* `theorem1_indistinguishable_false_fewer_faults` — "exactly `f` faulty" is needed there;
* `sharp_necessity_false` — a stronger reading not claimed by the paper ("an algorithm that is
  f-resilient on all 2f-redundant executions cannot be f-resilient on a non-redundant one") is false;
* `theorem1_false_n_eq_one` — without `2f < n` the literal statement fails (`n = f = 1`);
* `Protocol.resilient_toAlg` — the reduction from interactive deterministic protocols to the one-shot
  model ("best case for the server").
-/

open Finset

namespace RedundantOptimization

/-- Admissible cost functions: convex and differentiable. -/
def ConvDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (q : E → ℝ) : Prop :=
  ConvexOn ℝ Set.univ q ∧ Differentiable ℝ q

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convDiff_zero : ConvDiff (fun _ : E => (0 : ℝ)) :=
  ⟨convexOn_const 0 convex_univ, differentiable_const 0⟩

lemma convDiff_sqDist (p : E) : ConvDiff (fun x : E => ‖x - p‖ ^ 2) := by
  refine ⟨?_, ?_⟩
  · have h : ConvexOn ℝ Set.univ (fun x : E => ‖x‖ ^ 2) :=
      (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
    have := h.comp_affineMap (AffineMap.const ℝ E (-p) + AffineMap.id ℝ E)
    simpa [sub_eq_neg_add, Function.comp_def] using this
  · intro x
    exact ((hasStrictFDerivAt_norm_sq (x - p)).hasFDerivAt.differentiableAt).comp x
      (differentiableAt_id.sub_const p)

omit [InnerProductSpace ℝ E] in
lemma argmin_sqDist (p : E) : argmin (fun x : E => ‖x - p‖ ^ 2) = {p} := by
  ext x
  simp only [argmin, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    have := h p
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    have h0 : ‖x - p‖ ^ 2 = 0 := le_antisymm this (by positivity)
    simpa [sub_eq_zero] using h0
  · rintro rfl v; simp

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma argmin_const (c : ℝ) : argmin (fun _ : E => c) = Set.univ := by
  ext; simp [argmin]

/-- **For `f ≥ 1` there is no f-resilient algorithm on the class of all executions.** Two agents
send `‖x‖²` and `‖x - v‖²`, all other agents send `0`; if agent 1 is faulty the honest aggregate is
minimized exactly at `0`, if agent 0 is faulty exactly at `v ≠ 0`. -/
theorem no_resilient_allExecs [Nontrivial E] {n f : ℕ} (hf : 1 ≤ f) (hn : 2 ≤ n) :
    ¬ ∃ alg : (Fin n → E → ℝ) → E, Resilient ConvDiff (AllExecs ConvDiff n f) alg := by
  classical
  rintro ⟨alg, halg⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  let C : Fin n → E → ℝ := fun i =>
    if i = i₀ then fun x => ‖x - 0‖ ^ 2 else if i = i₁ then fun x => ‖x - v‖ ^ 2 else fun _ => 0
  have hadm : ∀ i, ConvDiff (C i) := by
    intro i; simp only [C]; split_ifs
    · exact convDiff_sqDist 0
    · exact convDiff_sqDist v
    · exact convDiff_zero
  -- the minimum points of the aggregate over `univ.erase j` are those of `C i` (`i ≠ j`)
  have key : ∀ i j : Fin n, i ≠ j → (i = i₀ ∨ i = i₁) → (j = i₀ ∨ j = i₁) →
      ∀ p, argmin (C i) = {p} → argmin (agg (univ.erase j) C) = {p} := by
    intro i j hij hi hj p hp
    have hother : ∀ k ∈ univ.erase j, p ∈ argmin (C k) := by
      intro k hk
      by_cases hki : k = i
      · subst hki; rw [hp]; rfl
      · have hk0 : k ≠ i₀ := by rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
          simp_all
        have hk1 : k ≠ i₁ := by rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
          simp_all
        simp only [C, ite_eq_right hk0, ite_eq_right hk1, argmin_const]; trivial
    rw [lemma1 _ _ ⟨p, Set.mem_iInter₂.2 hother⟩]
    apply Set.Subset.antisymm
    · intro x hx
      rw [← hp]; exact Set.mem_iInter₂.1 hx i (by simp [hij])
    · rintro x rfl; exact Set.mem_iInter₂.2 hother
  have hA0 : argmin (C i₀) = {0} := by simp only [C, ite_eq_left rfl]; exact argmin_sqDist 0
  have hA1 : argmin (C i₁) = {v} := by
    simp only [C, ite_eq_right h01.symm]; exact argmin_sqDist v
  have hT1 := key i₀ i₁ h01 (Or.inl rfl) (Or.inr rfl) 0 hA0
  have hT2 := key i₁ i₀ h01.symm (Or.inr rfl) (Or.inl rfl) v hA1
  have hcard : ∀ j : Fin n, n - f ≤ (univ.erase j).card := by intro j; simp; omega
  have hmem : ∀ j : Fin n, (j = i₀ ∨ j = i₁) → ∀ p, argmin (agg (univ.erase j) C) = {p} →
      ((univ.erase j, C) : Exec n E) ∈ AllExecs ConvDiff n f := by
    intro j _ p hp
    exact ⟨⟨hcard j, fun i _ => hadm i⟩, by rw [hp]; exact Set.singleton_nonempty p⟩
  have hcons : ∀ j : Fin n, Consistent ConvDiff ((univ.erase j, C) : Exec n E) C :=
    fun j => ⟨fun _ _ => rfl, hadm⟩
  have r1 := halg _ (hmem i₁ (Or.inr rfl) 0 hT1) C (hcons i₁)
  have r2 := halg _ (hmem i₀ (Or.inl rfl) v hT2) C (hcons i₀)
  simp only at r1 r2
  rw [hT1] at r1; rw [hT2] at r2
  exact hv ((Set.mem_singleton_iff.1 r2).symm.trans (Set.mem_singleton_iff.1 r1))

/-- With at most `f = 0` faults, 2f-redundancy holds trivially. -/
lemma twoFRedundant_of_f_eq_zero {n : ℕ} {X : Type*} {H : Finset (Fin n)} {Q : Fin n → X → ℝ}
    (hH : n ≤ H.card) : TwoFRedundant n 0 H Q := by
  intro S hS hcard
  have : S = H := Finset.eq_of_subset_of_card_le hS (by
    have := Finset.card_le_univ H; simp at this; omega)
  rw [this]

/-- In the zero space every function is minimized everywhere, so 2f-redundancy holds trivially. -/
lemma twoFRedundant_of_subsingleton {n f : ℕ} {X : Type*} [Subsingleton X] {H : Finset (Fin n)}
    {Q : Fin n → X → ℝ} : TwoFRedundant n f H Q := by
  intro S _ _
  ext w
  simp only [argmin, Set.mem_ofPred_eq]
  constructor <;> intro _ v <;> rw [Subsingleton.elim v w]

/-- **Theorem 1** of the paper, read literally: if a deterministic algorithm is f-resilient (on all
executions with convex differentiable honest cost functions whose aggregate has a minimum point),
then the honest cost functions of every execution satisfy 2f-redundancy. Here `2f < n` is the
paper's standing assumption (used without being stated in Theorem 1). The proof is not the paper's:
for `f ≥ 1` and `E ≠ 0` the hypothesis is never satisfied (`no_resilient_allExecs`). -/
theorem theorem1 {n f : ℕ} (hn : 2 * f < n) (alg : (Fin n → E → ℝ) → E)
    (halg : Resilient (ConvDiff (E := E)) (AllExecs ConvDiff n f) alg) :
    ∀ e ∈ AllExecs (ConvDiff (E := E)) n f, TwoFRedundant n f e.1 e.2 := by
  intro e he
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · exact twoFRedundant_of_f_eq_zero (by simpa using he.1.1)
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact twoFRedundant_of_subsingleton
  · exact absurd ⟨alg, halg⟩ (no_resilient_allExecs hf (by omega))

/-- **Theorem 1, indistinguishability form (what Part II of the proof establishes).** Let
`1 ≤ f`, `2f < n`, and let `e` be an execution with exactly `f` faulty agents whose honest cost
functions have a common minimum point. Then `e` is *not* 2f-redundant iff the faulty agents can send
admissible functions such that some other execution `e'` (at most `f` faulty agents, honest costs
with a common minimum point) produces the same received vector and has an aggregate solution set
disjoint from that of `e` — so no deterministic algorithm is correct on both. -/
theorem theorem1_indistinguishable {n f : ℕ} (hf : 1 ≤ f) (hn : 2 * f < n) (e : Exec n E)
    (he : e ∈ Valid ConvDiff n f) (hcard : e.1.card + f = n)
    (hcommon : (⋂ i ∈ e.1, argmin (e.2 i)).Nonempty) :
    ¬ TwoFRedundant n f e.1 e.2 ↔
      ∃ (C : Fin n → E → ℝ) (e' : Exec n E), Consistent ConvDiff e C ∧ Consistent ConvDiff e' C ∧
        e' ∈ Valid ConvDiff n f ∧ (⋂ i ∈ e'.1, argmin (e'.2 i)).Nonempty ∧
        Disjoint (argmin (agg e.1 e.2)) (argmin (agg e'.1 e'.2)) := by
  classical
  obtain ⟨H, Q⟩ := e
  simp only at he hcard hcommon ⊢
  constructor
  · intro hnot
    simp only [TwoFRedundant, not_forall] at hnot
    obtain ⟨S, hSH, hScard, hSne⟩ := hnot
    have hW : argmin (agg H Q) = ⋂ i ∈ H, argmin (Q i) := lemma1 H Q hcommon
    have hsubI : (⋂ i ∈ H, argmin (Q i)) ⊆ ⋂ i ∈ S, argmin (Q i) := fun x hx =>
      Set.mem_iInter₂.2 fun i hi => Set.mem_iInter₂.1 hx i (hSH hi)
    have hWS : argmin (agg S Q) = ⋂ i ∈ S, argmin (Q i) :=
      lemma1 S Q (hcommon.mono hsubI)
    -- a common minimum point of `S` that is not a solution for `H`
    obtain ⟨ŵ, hŵS, hŵW⟩ : ∃ ŵ, ŵ ∈ ⋂ i ∈ S, argmin (Q i) ∧ ŵ ∉ ⋂ i ∈ H, argmin (Q i) := by
      by_contra hcon
      push Not at hcon
      apply hSne
      rw [hWS, hW]
      exact Set.Subset.antisymm hcon hsubI
    obtain ⟨Ŝ, hŜS, hŜcard⟩ := Finset.exists_subset_card_eq hScard
    let C : Fin n → E → ℝ := fun i => if i ∈ H then Q i else fun x => ‖x - ŵ‖ ^ 2
    have hCadm : ∀ j, ConvDiff (C j) := by
      intro j; by_cases hj : j ∈ H
      · simp only [C, hj, ite_true]; exact he.2 j hj
      · simp only [C, hj, ite_false]; exact convDiff_sqDist ŵ
    have hdisj : Disjoint Ŝ Hᶜ := Finset.disjoint_left.2 fun i hi hc =>
      (Finset.mem_compl.1 hc) (hSH (hŜS hi))
    have hcompl : Hᶜ.card = f := by
      rw [Finset.card_compl, Fintype.card_fin]; omega
    have hŵmin : ∀ i ∈ Ŝ ∪ Hᶜ, ŵ ∈ argmin (C i) := by
      intro i hi
      rcases Finset.mem_union.1 hi with hi | hi
      · have hiH := hSH (hŜS hi)
        simp only [C, hiH, ite_true]
        exact Set.mem_iInter₂.1 hŵS i (hŜS hi)
      · simp only [C, Finset.mem_compl.1 hi, ite_false, argmin_sqDist]; rfl
    refine ⟨C, (Ŝ ∪ Hᶜ, C), ⟨fun i hi => by simp [C, hi], hCadm⟩, ⟨fun _ _ => rfl, hCadm⟩,
      ⟨?_, fun i _ => hCadm i⟩, ⟨ŵ, Set.mem_iInter₂.2 hŵmin⟩, ?_⟩
    · simp only
      rw [Finset.card_union_of_disjoint hdisj, hŜcard, hcompl]; omega
    · simp only
      rw [Set.disjoint_left]
      intro x hxW hx'
      rw [lemma1 _ C ⟨ŵ, Set.mem_iInter₂.2 hŵmin⟩] at hx'
      obtain ⟨b, hb⟩ : (Hᶜ).Nonempty := Finset.card_pos.1 (by omega)
      have hxb := Set.mem_iInter₂.1 hx' b (Finset.mem_union_right _ hb)
      simp only [C, Finset.mem_compl.1 hb, ite_false, argmin_sqDist,
        Set.mem_singleton_iff] at hxb
      subst hxb
      rw [hW] at hxW
      exact hŵW hxW
  · rintro ⟨C, ⟨H', Q'⟩, ⟨hC, -⟩, ⟨hC', -⟩, ⟨hH', -⟩, ⟨w', hw'⟩, hdisj⟩ hred
    simp only at hC hC' hH' hw' hdisj
    have hS := card_inter_ge he.1 hH'
    have hw'S : w' ∈ argmin (agg (H ∩ H') Q) := by
      apply mem_argmin_agg_of_forall
      intro i hi
      rw [Finset.mem_inter] at hi
      rw [← hC i hi.1, hC' i hi.2]
      exact Set.mem_iInter₂.1 hw' i hi.2
    rw [hred _ Finset.inter_subset_left hS] at hw'S
    exact Set.disjoint_left.1 hdisj hw'S (mem_argmin_agg_of_forall fun i hi =>
      Set.mem_iInter₂.1 hw' i hi)

end General

/-! ### Concrete instances on `ℝ` and `ℝ × ℝ` -/

section Concrete

/-- Why the literal reading is vacuous: in the class of *all* executions a 2f-redundant execution is
also confused with another one. With `n = 3`, `f = 1` and received functions `x², x², (x - 2)²` on
`ℝ`, the execution with honest agents `{0, 1}` is 2f-redundant (aggregate minimum `0`), the execution
with honest agents `{1, 2}` has the aggregate minimum `1`, and no deterministic algorithm is correct
on both. The partner's honest costs `x², (x - 2)²` have no common minimum point; the partners built
in the paper's proof always have one, and against such partners only non-redundant executions are
confusable (`theorem1_indistinguishable`). -/
theorem redundant_execution_confusable :
    let C : Fin 3 → ℝ → ℝ := ![fun x => x ^ 2, fun x => x ^ 2, fun x => (x - 2) ^ 2]
    ((({0, 1}, C) : Exec 3 ℝ) ∈ RedExecs ConvDiff 3 1) ∧
    ((({1, 2}, C) : Exec 3 ℝ) ∈ AllExecs ConvDiff 3 1) ∧
    ¬ ∃ alg : (Fin 3 → ℝ → ℝ) → ℝ,
      Resilient ConvDiff {(({0, 1}, C) : Exec 3 ℝ), ({1, 2}, C)} alg := by
  intro C
  have hsq : ∀ p : ℝ, ConvDiff (fun x : ℝ => (x - p) ^ 2) := fun p => by
    simpa [Real.norm_eq_abs, sq_abs] using convDiff_sqDist (E := ℝ) p
  have hsq0 : ConvDiff (fun x : ℝ => x ^ 2) := by simpa using hsq 0
  have hadm : ∀ i, ConvDiff (C i) := by
    intro i; fin_cases i
    · exact hsq0
    · exact hsq0
    · exact hsq 2
  have hA0 : argmin (fun x : ℝ => x ^ 2) = {0} := by
    simpa [Real.norm_eq_abs, sq_abs] using argmin_sqDist (E := ℝ) 0
  have hC0 : C 0 = fun x => x ^ 2 := rfl
  have hC1 : C 1 = fun x => x ^ 2 := rfl
  have hC2 : C 2 = fun x => (x - 2) ^ 2 := rfl
  -- every nonempty `S ⊆ {0, 1}` has aggregate minimum exactly `0`
  have hsub : ∀ S ⊆ ({0, 1} : Finset (Fin 3)), S.Nonempty → argmin (agg S C) = {0} := by
    intro S hS hne
    have hall : ∀ i ∈ S, argmin (C i) = {0} := by
      intro i hi
      rcases Finset.mem_insert.1 (hS hi) with rfl | h
      · rw [hC0, hA0]
      · rw [Finset.mem_singleton.1 h, hC1, hA0]
    obtain ⟨i, hi⟩ := hne
    rw [lemma1 S C ⟨0, Set.mem_iInter₂.2 fun j hj => by rw [hall j hj]; rfl⟩]
    ext x
    simp only [Set.mem_iInter, Set.mem_singleton_iff]
    constructor
    · intro h; have := h i hi; rwa [hall i hi] at this
    · rintro rfl j hj; rw [hall j hj]; rfl
  have hA01 : argmin (agg {0, 1} C) = {0} := hsub _ subset_rfl ⟨0, by simp⟩
  have hA12 : argmin (agg {1, 2} C) = {1} := by
    have hagg : agg {1, 2} C = fun x => x ^ 2 + (x - 2) ^ 2 := by
      funext x; simp [agg_apply, Finset.sum_pair (show (1 : Fin 3) ≠ 2 by decide), hC1, hC2]
    rw [hagg]; ext x; simp only [argmin, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h; have := h 1; nlinarith [sq_nonneg (x - 1)]
    · rintro rfl v; nlinarith [sq_nonneg (v - 1)]
  have hred : TwoFRedundant 3 1 ({0, 1} : Finset (Fin 3)) C := by
    intro S hS hcard
    rw [hA01]
    exact hsub S hS (Finset.card_pos.1 (by omega))
  refine ⟨⟨⟨⟨by decide, fun i _ => hadm i⟩, by rw [hA01]; exact Set.singleton_nonempty 0⟩, hred⟩,
    ⟨⟨by decide, fun i _ => hadm i⟩, by rw [hA12]; exact Set.singleton_nonempty 1⟩, ?_⟩
  rintro ⟨alg, halg⟩
  have r1 := halg _ (Set.mem_insert _ _) C ⟨fun _ _ => rfl, hadm⟩
  have r2 := halg _ (Set.mem_insert_of_mem _ rfl) C ⟨fun _ _ => rfl, hadm⟩
  simp only at r1 r2
  rw [hA01] at r1; rw [hA12] at r2
  have := (Set.mem_singleton_iff.1 r1).symm.trans (Set.mem_singleton_iff.1 r2)
  norm_num at this

/-- The distributed-sensing execution of the counterexample: `n = 3`, `f = 1`, state space `ℝ²`,
honest agents `0` and `1` observe one coordinate each (`Q₀(x, y) = x²`, `Q₁(x, y) = y²`); agent 2 is
faulty. -/
def sensingExec : Exec 3 (ℝ × ℝ) :=
  ({0, 1}, ![fun p => p.1 ^ 2, fun p => p.2 ^ 2, fun _ => 0])

lemma convDiff_fst_sq : ConvDiff (fun p : ℝ × ℝ => p.1 ^ 2) := by
  refine ⟨?_, by fun_prop⟩
  have := (even_two.convexOn_pow (𝕜 := ℝ)).comp_linearMap (LinearMap.fst ℝ ℝ ℝ)
  simpa [Function.comp_def] using this

lemma convDiff_snd_sq : ConvDiff (fun p : ℝ × ℝ => p.2 ^ 2) := by
  refine ⟨?_, by fun_prop⟩
  have := (even_two.convexOn_pow (𝕜 := ℝ)).comp_linearMap (LinearMap.snd ℝ ℝ ℝ)
  simpa [Function.comp_def] using this

lemma sensingExec_mem : sensingExec ∈ AllExecs ConvDiff 3 1 := by
  refine ⟨⟨by decide, ?_⟩, ⟨0, ?_⟩⟩
  · intro i hi
    simp only [sensingExec, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact convDiff_fst_sq
    · exact convDiff_snd_sq
  · intro v
    simp [sensingExec, Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide)]
    positivity

lemma sensingExec_not_redundant : ¬ TwoFRedundant 3 1 sensingExec.1 sensingExec.2 := by
  intro h
  have := h {0} (by simp [sensingExec]) (by simp)
  have hmem : ((0 : ℝ), (1 : ℝ)) ∈ argmin (agg {0} sensingExec.2) := by
    intro v; simp [sensingExec]; positivity
  rw [this] at hmem
  have := hmem 0
  simp [sensingExec, Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide)] at this
  norm_num at this

lemma sensingExec_common : (⋂ i ∈ sensingExec.1, argmin (sensingExec.2 i)).Nonempty := by
  refine ⟨0, Set.mem_iInter₂.2 fun i hi => ?_⟩
  simp only [sensingExec, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> intro v <;> simp [sensingExec] <;> positivity

/-- With no faulty agent, an execution whose honest costs share a minimum point `w₀` cannot be
separated from any other execution producing the same received vector: `w₀` solves both. -/
lemma not_disjoint_of_univ {n : ℕ} {X : Type*} {Adm : (X → ℝ) → Prop} {e e' : Exec n X}
    {C : Fin n → X → ℝ} (huniv : e.1 = univ) {w₀ : X} (hw₀ : w₀ ∈ ⋂ i ∈ e.1, argmin (e.2 i))
    (hC : Consistent Adm e C) (hC' : Consistent Adm e' C) :
    w₀ ∈ argmin (agg e.1 e.2) ∧ w₀ ∈ argmin (agg e'.1 e'.2) := by
  refine ⟨mem_argmin_agg_of_forall fun i hi => Set.mem_iInter₂.1 hw₀ i hi,
    mem_argmin_agg_of_forall fun i hi => ?_⟩
  have hi' : i ∈ e.1 := by rw [huniv]; exact mem_univ i
  rw [← hC'.1 i hi, hC.1 i hi']
  exact Set.mem_iInter₂.1 hw₀ i hi'

/-- The sensing execution with all three agents honest: `x², y², x² + y²` on `ℝ²`, `n = 3`, `f = 1`. -/
def sensingAll : Exec 3 (ℝ × ℝ) :=
  (univ, ![fun p => p.1 ^ 2, fun p => p.2 ^ 2, fun p => p.1 ^ 2 + p.2 ^ 2])

/-- **`theorem1_indistinguishable` needs exactly `f` faulty agents.** With fewer faults (here none)
the execution `sensingAll` is valid, its honest costs share the minimum point `0`, it is not
2f-redundant, and yet every execution producing the same received vector has `0` as a solution. -/
theorem theorem1_indistinguishable_false_fewer_faults :
    sensingAll ∈ Valid ConvDiff 3 1 ∧ (⋂ i ∈ sensingAll.1, argmin (sensingAll.2 i)).Nonempty ∧
      ¬ TwoFRedundant 3 1 sensingAll.1 sensingAll.2 ∧
      ¬ ∃ (C : Fin 3 → ℝ × ℝ → ℝ) (e' : Exec 3 (ℝ × ℝ)), Consistent ConvDiff sensingAll C ∧
        Consistent ConvDiff e' C ∧ e' ∈ Valid ConvDiff 3 1 ∧
        (⋂ i ∈ e'.1, argmin (e'.2 i)).Nonempty ∧
        Disjoint (argmin (agg sensingAll.1 sensingAll.2)) (argmin (agg e'.1 e'.2)) := by
  have hcommon : (0 : ℝ × ℝ) ∈ ⋂ i ∈ sensingAll.1, argmin (sensingAll.2 i) := by
    refine Set.mem_iInter₂.2 fun i _ => ?_
    fin_cases i <;> intro v <;> simp [sensingAll] <;> positivity
  refine ⟨⟨by decide, fun i _ => ?_⟩, ⟨0, hcommon⟩, ?_, ?_⟩
  · fin_cases i
    · exact convDiff_fst_sq
    · exact convDiff_snd_sq
    · exact ⟨convDiff_fst_sq.1.add convDiff_snd_sq.1, by
        simp only [sensingAll]; exact convDiff_fst_sq.2.add convDiff_snd_sq.2⟩
  · intro h
    have := h {0} (by simp [sensingAll]) (by simp)
    have hmem : ((0 : ℝ), (1 : ℝ)) ∈ argmin (agg {0} sensingAll.2) := by
      intro v; simp [sensingAll]; positivity
    rw [this] at hmem
    have := hmem 0
    simp [sensingAll, Fin.sum_univ_three] at this
    norm_num at this
  · rintro ⟨C, e', hC, hC', -, -, hdisj⟩
    obtain ⟨h1, h2⟩ := not_disjoint_of_univ rfl hcommon hC hC'
    exact Set.disjoint_left.1 hdisj h1 h2

/-- **The sharp form of necessity is false.** There is a deterministic algorithm that is f-resilient
on every 2f-redundant execution and also on the non-redundant sensing execution (`n = 3`, `f = 1`,
convex differentiable costs on `ℝ²`). Hence "2f-redundancy is necessary for f-resilience" fails for
algorithms required to handle 2f-redundant inputs; 2f-redundancy is not a maximal solvable class. -/
theorem sharp_necessity_false :
    ∃ alg : (Fin 3 → ℝ × ℝ → ℝ) → ℝ × ℝ,
      Resilient ConvDiff (RedExecs ConvDiff 3 1) alg ∧
      Resilient ConvDiff {sensingExec} alg ∧
      sensingExec ∈ AllExecs ConvDiff 3 1 ∧
      ¬ TwoFRedundant 3 1 sensingExec.1 sensingExec.2 := by
  obtain ⟨alg, halg⟩ := exists_resilient_redundant_insert (n := 3) ConvDiff 1 sensingExec
    (by decide) sensingExec_common
  exact ⟨alg, halg.mono (Set.subset_insert _ _),
    halg.mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)), sensingExec_mem,
    sensingExec_not_redundant⟩

/-- The same, phrased as the negation of the would-be sharp Theorem 1. -/
theorem not_sharp_theorem1 :
    ¬ ∀ alg : (Fin 3 → ℝ × ℝ → ℝ) → ℝ × ℝ,
      Resilient ConvDiff (RedExecs ConvDiff 3 1) alg →
      ∀ e ∈ AllExecs (ConvDiff (E := ℝ × ℝ)) 3 1, Resilient ConvDiff {e} alg →
        TwoFRedundant 3 1 e.1 e.2 := by
  intro h
  obtain ⟨alg, h1, h2, h3, h4⟩ := sharp_necessity_false
  exact h4 (h alg h1 _ h3 h2)

/-- **Theorem 1 fails without `2f < n`** (degenerate case `n = f = 1`): output a minimum point of
the single received function. This is f-resilient on all executions, but the execution in which the
only agent is honest with cost `x²` is not 2f-redundant (its empty subset has `|∅| ≥ n - 2f`). -/
theorem theorem1_false_n_eq_one :
    ∃ alg : (Fin 1 → ℝ → ℝ) → ℝ, Resilient ConvDiff (AllExecs ConvDiff 1 1) alg ∧
      ∃ e ∈ AllExecs (ConvDiff (E := ℝ)) 1 1, ¬ TwoFRedundant 1 1 e.1 e.2 := by
  classical
  refine ⟨fun C => Classical.epsilon (· ∈ argmin (C 0)), ?_, ⟨{0}, fun _ x => x ^ 2⟩, ?_, ?_⟩
  · rintro ⟨H, Q⟩ ⟨⟨-, -⟩, hne⟩ C ⟨hC, -⟩
    simp only at hC hne ⊢
    rcases Finset.eq_empty_or_nonempty H with rfl | ⟨i, hi⟩
    · simp
    · have hH : H = {0} := by
        ext j; simp only [Finset.mem_singleton]; constructor
        · intro _; exact Subsingleton.elim _ _
        · rintro rfl; rwa [Subsingleton.elim i 0] at hi
      subst hH
      have h0 : C 0 = Q 0 := hC 0 (by simp)
      have hagg : agg {0} Q = Q 0 := by funext w; simp
      rw [hagg] at hne ⊢
      rw [h0]
      exact Classical.epsilon_spec hne
  · refine ⟨⟨by simp, fun i _ => ?_⟩, ⟨0, fun v => by simp; positivity⟩⟩
    simpa [Real.norm_eq_abs, sq_abs] using convDiff_sqDist (E := ℝ) 0
  · intro h
    have := h ∅ (by simp) (by simp)
    rw [argmin_agg_empty] at this
    have h1 : (1 : ℝ) ∈ argmin (agg ({0} : Finset (Fin 1)) (fun _ x => x ^ 2)) := by
      rw [← this]; trivial
    have := h1 0
    norm_num at this

end Concrete

/-! ### From interactive protocols to the one-shot model -/

/-- A deterministic protocol (e.g. server-based and iterative, like the paper's algorithm). The
behaviour of an agent is an element of `Beh` (for instance a strategy mapping the server's queries
to replies); an honest agent with cost function `q` behaves as `honest q`, a Byzantine agent may
behave arbitrarily. `run` is the server's output for a profile of behaviours. -/
structure Protocol (n : ℕ) (X : Type*) (Beh : Type*) where
  honest : (X → ℝ) → Beh
  run : (Fin n → Beh) → X

variable {n : ℕ} {X : Type*} {Beh : Type*}

/-- f-resilience of a protocol on a class `K` of executions. -/
def Protocol.Resilient (P : Protocol n X Beh) (K : Set (Exec n X)) : Prop :=
  ∀ e ∈ K, ∀ b : Fin n → Beh, (∀ i ∈ e.1, b i = P.honest (e.2 i)) →
    P.run b ∈ argmin (agg e.1 e.2)

/-- The one-shot algorithm induced by a protocol: simulate every agent honestly with the cost
function it sent. -/
def Protocol.toAlg (P : Protocol n X Beh) : (Fin n → X → ℝ) → X :=
  fun C => P.run fun i => P.honest (C i)

/-- **Best case for the server** (Section 3.1). A Byzantine agent can imitate an honest agent with
any admissible cost function, so an f-resilient protocol yields an f-resilient one-shot algorithm on
the same class. Hence all impossibility statements of this file apply to every deterministic
protocol, e.g. `no_resilient_allExecs`. -/
theorem Protocol.resilient_toAlg (Adm : (X → ℝ) → Prop) (P : Protocol n X Beh)
    (K : Set (Exec n X)) (hP : P.Resilient K) : RedundantOptimization.Resilient Adm K P.toAlg :=
  fun e he C hC => hP e he _ fun i hi => by rw [hC.1 i hi]

end RedundantOptimization
