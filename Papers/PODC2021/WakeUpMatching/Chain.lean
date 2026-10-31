import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic

/-!
# Finite path spaces of time-inhomogeneous processes and the chain rule

A random process runs for `T` steps; at step `t` an input `x ∈ X` is drawn from the law `p t`,
independently of the other steps, and the state evolves by `s ↦ f t s x`. The path space is
`Fin T → X`, with the product weight `∏ i, p i (ω i)`.

The main result, `pathProb_forall_le`, is the "chain rule" bound used in the proof of Lemma 5.4
of Dani, Gupta, Hayes, Pettie, *Wake up and join me! An energy-efficient algorithm for maximal
matching in radio networks* (PODC 2021): if at every step `t ∈ I`, *whatever the current state
`s`*, the step event `Z t s` has probability at most `c t`, then the probability that the event
happens at every step of `I` is at most `∏ t ∈ I, c t`.

## Main definitions
* `pathExt`, `pathState`: the input at time `t` and the state after `t` steps of a path.
* `pathWeight`, `pathProb`, `pathStepProb`: product weight, probability of an event of paths,
  probability of an event of one step.

## Main results
* `pathProb_true`, `pathProb_nonneg`, `pathProb_le_one`, `pathProb_mono`, `pathProb_not`.
* `pathProb_exists_le`: the union bound.
* `pathProb_forall_le`: the chain-rule product bound.
-/

set_option linter.unusedSectionVars false

namespace Podc.WakeUpMatching

open Finset

variable {X S : Type*} [Fintype X] [DecidableEq X] [Inhabited X]

/-- Extend a finite path to all indices (`default` after time `T`). -/
def pathExt {T : ℕ} (ω : Fin T → X) (t : ℕ) : X := if h : t < T then ω ⟨t, h⟩ else default

/-- State after `t` steps (step `t` uses transition `f t` and input `pathExt ω t`). -/
def pathState (f : ℕ → S → X → S) (s₀ : S) {T : ℕ} (ω : Fin T → X) : ℕ → S
  | 0 => s₀
  | t + 1 => f t (pathState f s₀ ω t) (pathExt ω t)

/-- Product weight of a path, step `i` having law `p i`. -/
def pathWeight (p : ℕ → X → ℝ) {T : ℕ} (ω : Fin T → X) : ℝ := ∏ i : Fin T, p i (ω i)

/-- Probability of an event `F` of paths of length `T`, step `i` having law `p i`. -/
noncomputable def pathProb (p : ℕ → X → ℝ) (T : ℕ) (F : (Fin T → X) → Prop) : ℝ := by
  classical exact ∑ ω ∈ univ.filter F, pathWeight p ω

/-- Probability of an event `E` of the input of step `t`. -/
noncomputable def pathStepProb (p : ℕ → X → ℝ) (t : ℕ) (E : X → Prop) : ℝ := by
  classical exact ∑ x ∈ univ.filter E, p t x

variable {p : ℕ → X → ℝ} {T : ℕ}

lemma pathProb_eq_sum_ite (F : (Fin T → X) → Prop) [DecidablePred F] :
    pathProb p T F = ∑ ω, if F ω then pathWeight p ω else 0 := by
  rw [← Finset.sum_filter]; unfold pathProb; congr 1; ext; simp

lemma pathStepProb_eq_sum_ite (t : ℕ) (E : X → Prop) [DecidablePred E] :
    pathStepProb p t E = ∑ x, if E x then p t x else 0 := by
  rw [← Finset.sum_filter]; unfold pathStepProb; congr 1; ext; simp

lemma pathWeight_nonneg (hp : ∀ t x, 0 ≤ p t x) (ω : Fin T → X) : 0 ≤ pathWeight p ω :=
  Finset.prod_nonneg fun i _ => hp i (ω i)

lemma pathStepProb_nonneg (hp : ∀ t x, 0 ≤ p t x) (t : ℕ) (E : X → Prop) :
    0 ≤ pathStepProb p t E := by
  classical
  rw [pathStepProb_eq_sum_ite]
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp [hp]

lemma pathExt_snoc_lt (ω : Fin T → X) (x : X) {t : ℕ} (ht : t < T) :
    pathExt (Fin.snoc ω x : Fin (T + 1) → X) t = pathExt ω t := by
  simp [pathExt, ht, show t < T + 1 by omega, Fin.snoc]

lemma pathExt_snoc_last (ω : Fin T → X) (x : X) :
    pathExt (Fin.snoc ω x : Fin (T + 1) → X) T = x := by
  simp [pathExt, Fin.snoc]

lemma pathState_snoc (f : ℕ → S → X → S) (s₀ : S) (ω : Fin T → X) (x : X) :
    ∀ t ≤ T, pathState f s₀ (Fin.snoc ω x : Fin (T + 1) → X) t = pathState f s₀ ω t
  | 0, _ => rfl
  | t + 1, ht => by
    simp only [pathState]
    rw [pathState_snoc f s₀ ω x t (by omega), pathExt_snoc_lt ω x (by omega)]

lemma pathWeight_snoc (ω : Fin T → X) (x : X) :
    pathWeight p (Fin.snoc ω x : Fin (T + 1) → X) = pathWeight p ω * p T x := by
  simp [pathWeight, Fin.prod_univ_castSucc]

/-- Sums over paths of length `T + 1` split into a sum over the first `T` steps and the last. -/
lemma sum_paths_succ {M : Type*} [AddCommMonoid M] (g : (Fin (T + 1) → X) → M) :
    ∑ ω, g ω = ∑ ω : Fin T → X, ∑ x, g (Fin.snoc ω x) := by
  rw [← (Fin.snocEquiv fun _ => X).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma pathProb_succ (F : (Fin (T + 1) → X) → Prop) [DecidablePred F] :
    pathProb p (T + 1) F =
      ∑ ω : Fin T → X, ∑ x, if F (Fin.snoc ω x) then pathWeight p ω * p T x else 0 := by
  rw [pathProb_eq_sum_ite, sum_paths_succ]
  simp only [pathWeight_snoc]

/-- The whole path space has probability `1`. -/
theorem pathProb_true (hp1 : ∀ t, ∑ x, p t x = 1) : pathProb p T (fun _ => True) = 1 := by
  induction T with
  | zero => simp [pathProb, pathWeight]
  | succ T ih =>
    rw [pathProb_succ]
    simp only [ite_true, ← Finset.mul_sum, hp1, mul_one]
    rw [← ih, pathProb_eq_sum_ite]
    simp

/-- Probabilities are nonnegative. -/
theorem pathProb_nonneg (hp : ∀ t x, 0 ≤ p t x) (F : (Fin T → X) → Prop) :
    0 ≤ pathProb p T F := by
  classical
  rw [pathProb_eq_sum_ite]
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [pathWeight_nonneg hp]

/-- Monotonicity of probability under implication of events. -/
theorem pathProb_mono (hp : ∀ t x, 0 ≤ p t x) {F G : (Fin T → X) → Prop}
    (h : ∀ ω, F ω → G ω) : pathProb p T F ≤ pathProb p T G := by
  classical
  rw [pathProb_eq_sum_ite, pathProb_eq_sum_ite]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hF : F ω
  · simp [hF, h ω hF]
  · simp only [hF, ↓reduceIte]; split_ifs <;> simp [pathWeight_nonneg hp]

/-- Probability of the complement. -/
theorem pathProb_not (hp1 : ∀ t, ∑ x, p t x = 1) (F : (Fin T → X) → Prop) :
    pathProb p T (fun ω => ¬ F ω) = 1 - pathProb p T F := by
  classical
  rw [← pathProb_true (T := T) hp1, pathProb_eq_sum_ite, pathProb_eq_sum_ite,
    pathProb_eq_sum_ite, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hF : F ω <;> simp [hF]

/-- Probabilities are at most `1`. -/
theorem pathProb_le_one (hp : ∀ t x, 0 ≤ p t x) (hp1 : ∀ t, ∑ x, p t x = 1)
    (F : (Fin T → X) → Prop) : pathProb p T F ≤ 1 := by
  rw [← pathProb_true (T := T) hp1]
  exact pathProb_mono hp fun _ _ => trivial

/-- The union bound. -/
theorem pathProb_exists_le (hp : ∀ t x, 0 ≤ p t x) {ι : Type*} (s : Finset ι)
    (F : ι → (Fin T → X) → Prop) :
    pathProb p T (fun ω => ∃ i ∈ s, F i ω) ≤ ∑ i ∈ s, pathProb p T (F i) := by
  classical
  simp only [pathProb_eq_sum_ite]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun ω _ => ?_
  split_ifs with h
  · obtain ⟨i, hi, hFi⟩ := h
    calc pathWeight p ω = if F i ω then pathWeight p ω else 0 := by simp [hFi]
      _ ≤ ∑ j ∈ s, if F j ω then pathWeight p ω else 0 :=
        Finset.single_le_sum (f := fun j => if F j ω then pathWeight p ω else 0)
          (fun j _ => by split_ifs <;> simp [pathWeight_nonneg hp]) hi
  · exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [pathWeight_nonneg hp]

-- CSLib candidate
/-- **Chain rule bound** (used in the proof of Lemma 5.4 of Dani–Gupta–Hayes–Pettie, PODC 2021).
If at each step `t ∈ I` the step event `Z t s` has probability at most `c t` *for every* current
state `s`, then the probability that the step event occurs at every step `t ∈ I` (evaluated at the
actual state `pathState f s₀ ω t` and input `pathExt ω t`) is at most `∏ t ∈ I, c t`. -/
theorem pathProb_forall_le (hp : ∀ t x, 0 ≤ p t x) (hp1 : ∀ t, ∑ x, p t x = 1)
    (f : ℕ → S → X → S) (s₀ : S) (I : Finset ℕ) (hI : ∀ t ∈ I, t < T)
    (Z : ℕ → S → X → Prop) (c : ℕ → ℝ)
    (hc : ∀ t ∈ I, ∀ s, pathStepProb p t (Z t s) ≤ c t) :
    pathProb p T (fun ω => ∀ t ∈ I, Z t (pathState f s₀ ω t) (pathExt ω t)) ≤ ∏ t ∈ I, c t := by
  classical
  induction T generalizing I with
  | zero =>
    have hI0 : I = ∅ := Finset.eq_empty_of_forall_notMem fun t ht => by simpa using hI t ht
    subst hI0
    rw [Finset.prod_empty]
    exact pathProb_le_one hp hp1 _
  | succ T ih =>
    -- the event restricted to the first `T` steps
    set G : (Fin T → X) → Prop :=
      fun ω => ∀ t ∈ I.erase T, Z t (pathState f s₀ ω t) (pathExt ω t) with hG
    have hIG : ∀ t ∈ I.erase T, t < T := fun t ht => by
      have := hI t (Finset.mem_of_mem_erase ht); have := Finset.ne_of_mem_erase ht; omega
    have ihG : pathProb p T G ≤ ∏ t ∈ I.erase T, c t :=
      ih (I.erase T) hIG (fun t ht => hc t (Finset.mem_of_mem_erase ht))
    -- the event on paths of length `T + 1` splits into `G` and a condition on the last step
    have hiff : ∀ (ω : Fin T → X) (x : X),
        (∀ t ∈ I, Z t (pathState f s₀ (Fin.snoc ω x : Fin (T + 1) → X) t)
          (pathExt (Fin.snoc ω x : Fin (T + 1) → X) t)) ↔
        G ω ∧ (T ∈ I → Z T (pathState f s₀ ω T) x) := by
      intro ω x
      constructor
      · intro h
        refine ⟨fun t ht => ?_, fun hT => ?_⟩
        · have h1 := h t (Finset.mem_of_mem_erase ht)
          have tlt := hIG t ht
          rwa [pathState_snoc f s₀ ω x t tlt.le, pathExt_snoc_lt ω x tlt] at h1
        · have h1 := h T hT
          rwa [pathState_snoc f s₀ ω x T le_rfl, pathExt_snoc_last] at h1
      · rintro ⟨hGω, hT⟩ t ht
        by_cases htT : t = T
        · rw [htT] at ht ⊢
          rw [pathState_snoc f s₀ ω x T le_rfl, pathExt_snoc_last]
          exact hT ht
        · have tlt : t < T := by have := hI t ht; omega
          rw [pathState_snoc f s₀ ω x t tlt.le, pathExt_snoc_lt ω x tlt]
          exact hGω t (Finset.mem_erase.2 ⟨htT, ht⟩)
    -- the factor contributed by the last step
    have hdd : 0 ≤ if T ∈ I then c T else 1 := by
      split_ifs with hT
      · exact (pathStepProb_nonneg hp T _).trans (hc T hT s₀)
      · exact zero_le_one
    have key : ∀ ω : Fin T → X,
        (∑ x, if (∀ t ∈ I, Z t (pathState f s₀ (Fin.snoc ω x : Fin (T + 1) → X) t)
          (pathExt (Fin.snoc ω x : Fin (T + 1) → X) t)) then pathWeight p ω * p T x else 0) ≤
        (if G ω then pathWeight p ω else 0) * (if T ∈ I then c T else 1) := by
      intro ω
      simp only [hiff]
      by_cases hGω : G ω
      · simp only [hGω, true_and, ↓reduceIte]
        have hfac : (∑ x, if (T ∈ I → Z T (pathState f s₀ ω T) x) then pathWeight p ω * p T x
            else 0) = pathWeight p ω *
              ∑ x, if (T ∈ I → Z T (pathState f s₀ ω T) x) then p T x else 0 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp
        rw [hfac]
        refine mul_le_mul_of_nonneg_left ?_ (pathWeight_nonneg hp ω)
        by_cases hT : T ∈ I
        · simp only [hT, forall_const, ↓reduceIte]
          rw [← pathStepProb_eq_sum_ite]
          exact hc T hT _
        · simp [hT, hp1]
      · simp [hGω]
    rw [pathProb_succ]
    calc _ ≤ ∑ ω, (if G ω then pathWeight p ω else 0) * (if T ∈ I then c T else 1) :=
          Finset.sum_le_sum fun ω _ => key ω
      _ = pathProb p T G * (if T ∈ I then c T else 1) := by
          rw [pathProb_eq_sum_ite, Finset.sum_mul]
      _ ≤ (∏ t ∈ I.erase T, c t) * (if T ∈ I then c T else 1) :=
          mul_le_mul_of_nonneg_right ihG hdd
      _ = ∏ t ∈ I, c t := by
          by_cases hT : T ∈ I
          · simp only [hT, ↓reduceIte]; exact Finset.prod_erase_mul I c hT
          · simp [hT]

end Podc.WakeUpMatching
