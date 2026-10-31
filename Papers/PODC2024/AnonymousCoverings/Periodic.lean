import Papers.PODC2024.AnonymousCoverings.Model

/-!
# Concrete eventually periodic executions

To exhibit concrete infinite executions (counterexamples), we run a fixed list of actions `pre`
followed by a list `cyc` repeated forever, from a given initial configuration. If every action is
enabled during `pre` and the first round of `cyc`, and the configuration after the first round
of `cyc` equals the one before it, then the sequence is an execution (`periodicExec`).
Properties of the execution reduce to finitely many time points (`periodic_forall`), which are
checked by `decide`.
-/

namespace Podc.AnonymousCoverings

open Finset

variable {P R D X : Type*} [DecidableEq P] [DecidableEq R] [Fintype R]

/-- Enabledness of an action. -/
def Enabled (A : Algo R D X) : Act P R → Cfg P R D X → Prop
  | .write p r, c => (c.loc p).scan = none ∧ r ∉ (c.loc p).written ∧ ¬ A.stop (c.loc p).d
  | .read p r, c => (c.loc p).scan.isSome ∧ r ∉ (c.loc p).scan.getD univ
  | .idle p, c => (c.loc p).scan = none ∧ A.stop (c.loc p).d

instance (A : Algo R D X) [DecidablePred A.stop] (a : Act P R) (c : Cfg P R D X) :
    Decidable (Enabled A a c) := by
  cases a with
  | write p r => unfold Enabled; infer_instance
  | read p r => unfold Enabled; infer_instance
  | idle p => unfold Enabled; infer_instance

/-- The configuration after an action. -/
def postOf (A : Algo R D X) : Act P R → Cfg P R D X → Cfg P R D X
  | .write p r, c => writePost A c p r
  | .read p r, c => readPost A c p r
  | .idle _, c => c

theorem step_postOf (A : Algo R D X) {a : Act P R} {c : Cfg P R D X} (h : Enabled A a c) :
    Step A a c (postOf A a c) := by
  cases a with
  | write p r => exact ⟨h.1, h.2.1, h.2.2, rfl⟩
  | read p r =>
    refine ⟨?_, rfl⟩
    obtain ⟨h1, h2⟩ := h
    obtain ⟨S, hS⟩ := Option.isSome_iff_exists.1 h1
    rw [hS] at h2
    exact ⟨S, hS, h2⟩
  | idle p => exact ⟨h.1, h.2, rfl⟩

variable (pre cyc : List (Act P R)) (dflt : Act P R)

/-- The action at time `t`: `pre`, then `cyc` repeated. -/
def actOf (t : ℕ) : Act P R :=
  if t < pre.length then pre.getD t dflt else cyc.getD ((t - pre.length) % cyc.length) dflt

/-- The configurations obtained by running `actOf` from `c₀`. -/
def runOf (A : Algo R D X) (c₀ : Cfg P R D X) : ℕ → Cfg P R D X
  | 0 => c₀
  | t + 1 => postOf A (actOf pre cyc dflt t) (runOf A c₀ t)

variable {pre cyc dflt}

omit [DecidableEq P] [DecidableEq R] [Fintype R] in
theorem actOf_periodic (hc : cyc ≠ []) {t : ℕ} (ht : pre.length ≤ t) :
    actOf pre cyc dflt (t + cyc.length) = actOf pre cyc dflt t := by
  have hL : 0 < cyc.length := List.length_pos_iff.2 hc
  unfold actOf
  have h1 : ¬ (t + cyc.length < pre.length) := by omega
  have h2 : ¬ (t < pre.length) := by omega
  simp only [h1, h2, ↓reduceIte]
  congr 1
  rw [show t + cyc.length - pre.length = (t - pre.length) + cyc.length by omega, Nat.add_mod_right]

theorem runOf_periodic (A : Algo R D X) (c₀ : Cfg P R D X) (hc : cyc ≠ [])
    (hper : runOf pre cyc dflt A c₀ (pre.length + cyc.length) = runOf pre cyc dflt A c₀ pre.length)
    {t : ℕ} (ht : pre.length ≤ t) :
    runOf pre cyc dflt A c₀ (t + cyc.length) = runOf pre cyc dflt A c₀ t := by
  induction t, ht using Nat.le_induction with
  | base => exact hper
  | succ t ht ih =>
    rw [show t + 1 + cyc.length = (t + cyc.length) + 1 by omega]
    simp only [runOf]
    rw [ih, actOf_periodic hc ht]

/-- Reduction of a property of all times to the times `< |pre| + |cyc|`. -/
theorem periodic_forall (A : Algo R D X) (c₀ : Cfg P R D X) (hc : cyc ≠ [])
    (hper : runOf pre cyc dflt A c₀ (pre.length + cyc.length) = runOf pre cyc dflt A c₀ pre.length)
    (Q : Act P R → Cfg P R D X → Prop)
    (hQ : ∀ t < pre.length + cyc.length, Q (actOf pre cyc dflt t) (runOf pre cyc dflt A c₀ t)) :
    ∀ t, Q (actOf pre cyc dflt t) (runOf pre cyc dflt A c₀ t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases h : t < pre.length + cyc.length
    · exact hQ t h
    · have hL : 0 < cyc.length := List.length_pos_iff.2 hc
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + cyc.length := ⟨t - cyc.length, by omega⟩
      rw [actOf_periodic hc (by omega), runOf_periodic A c₀ hc hper (by omega)]
      exact ih t' (by omega)

/-- Reduction of a property of all times `≥ |pre|` to the times in `[|pre|, |pre| + |cyc|)`. -/
theorem periodic_forall_from (A : Algo R D X) (c₀ : Cfg P R D X) (hc : cyc ≠ [])
    (hper : runOf pre cyc dflt A c₀ (pre.length + cyc.length) = runOf pre cyc dflt A c₀ pre.length)
    (Q : Act P R → Cfg P R D X → Prop)
    (hQ : ∀ t, pre.length ≤ t → t < pre.length + cyc.length →
      Q (actOf pre cyc dflt t) (runOf pre cyc dflt A c₀ t)) :
    ∀ t ≥ pre.length, Q (actOf pre cyc dflt t) (runOf pre cyc dflt A c₀ t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    by_cases h : t < pre.length + cyc.length
    · exact hQ t ht h
    · have hL : 0 < cyc.length := List.length_pos_iff.2 hc
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + cyc.length := ⟨t - cyc.length, by omega⟩
      rw [actOf_periodic hc (by omega), runOf_periodic A c₀ hc hper (by omega)]
      exact ih t' (by omega) (by omega)

/-- The periodic execution. -/
def periodicExec (A : Algo R D X) (c₀ : Cfg P R D X) (hc : cyc ≠ [])
    (hper : runOf pre cyc dflt A c₀ (pre.length + cyc.length) = runOf pre cyc dflt A c₀ pre.length)
    (hen : ∀ t < pre.length + cyc.length,
      Enabled A (actOf pre cyc dflt t) (runOf pre cyc dflt A c₀ t)) : Exec (P := P) A where
  cfg := runOf pre cyc dflt A c₀
  act := actOf pre cyc dflt
  step t := step_postOf A (periodic_forall A c₀ hc hper (fun a c => Enabled A a c) hen t)

omit [DecidableEq P] [DecidableEq R] [Fintype R] in
/-- Times congruent to `i` modulo the period, after `pre`, are unbounded. -/
theorem exists_ge_actOf (hc : cyc ≠ []) {i : ℕ} (hi : i < cyc.length) (T : ℕ) :
    ∃ t ≥ T, actOf pre cyc dflt t = cyc.getD i dflt := by
  refine ⟨pre.length + i + T * cyc.length, ?_, ?_⟩
  · have : 0 < cyc.length := List.length_pos_iff.2 hc
    nlinarith
  · unfold actOf
    have h1 : ¬ (pre.length + i + T * cyc.length < pre.length) := by omega
    simp only [h1, ↓reduceIte]
    congr 1
    rw [show pre.length + i + T * cyc.length - pre.length = i + T * cyc.length by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

end Podc.AnonymousCoverings
