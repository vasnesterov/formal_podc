import Mathlib

/-!
# Purely probabilistic systems, probabilistic beliefs and probabilistic constraints

Formalization of the model and the main results of

> Y. Moses, N. Zamir. *Probably Approximately Knowing.* PODC 2020 (arXiv:2007.02984v1).

A *purely probabilistic system* (pps, §2.1 of the paper) is a finite tree whose edges carry positive
transition probabilities; its runs are the root-to-leaf paths. Every result of §§3–7 only uses the
induced finite probability space on runs and the local states along the runs, so we abstract a pps to

* a finite type `Ω` of runs with positive probabilities `μ` summing to `1`;
* the length `len r` of each run (its points are `(r, t)` with `t ≤ len r`);
* the local state `loc i r t` of every agent `i` at every point, with the synchrony assumption of §2.1
  (every local state determines the current time, `PPS.sync`).

Every tree pps of the paper yields such a structure, and conversely every such structure is the
pps of a tree in which all randomness is resolved at the root (the environment's initial state
determines the run). Facts are arbitrary sets of points (`Fact`), and an action of agent `i`
is represented by the fact `does_i(α)` (`A : Fact Ω`).

Main results: Theorem 6.2 (`PPS.theorem_6_2`), Theorem 4.2 (`PPS.theorem_4_2`), Lemma 4.3(a)
(`PPS.lemma_4_3a`), Lemma 5.1 (`PPS.lemma_5_1`), Theorem 7.1 (`PPS.theorem_7_1`), Corollary 7.2
(`PPS.corollary_7_2`), Lemma B.1 (`PPS.lemma_B_1`), Lemma F.1 (`PPS.lemma_F_1`).
-/

noncomputable section

open Classical Finset

namespace Podc.ProbablyApproxKnowing

/-- A fact over a system with run type `Ω`: the set of points `(r, t)` at which it holds. -/
abbrev Fact (Ω : Type*) := Ω → ℕ → Prop

-- CSLib candidate (probabilistic beliefs over finite synchronous systems)
/-- A (finite, purely probabilistic) system: finitely many runs with positive probabilities,
run lengths, and local states of the agents, in a synchronous setting (every local state determines
the current time). -/
structure PPS (Ω : Type*) [Fintype Ω] (Agent : Type*) (L : Type*) where
  /-- The prior probability `μ_T(r)` of a run. -/
  μ : Ω → ℝ
  μ_pos : ∀ r, 0 < μ r
  sum_μ : ∑ r, μ r = 1
  /-- The points of run `r` are `(r, t)` for `t ≤ len r`. -/
  len : Ω → ℕ
  /-- The local state `r_i(t)` of agent `i` at the point `(r, t)`. -/
  loc : Agent → Ω → ℕ → L
  /-- Synchrony: a local state determines the current time. -/
  sync : ∀ i r r' t t', t ≤ len r → t' ≤ len r' → loc i r t = loc i r' t' → t = t'

namespace PPS

variable {Ω : Type*} [Fintype Ω] {Agent L : Type*} (T : PPS Ω Agent L)

/-! ### Probabilities of events (sets of runs) -/

/-- `μ_T(Q)`, the probability of a set of runs. -/
def prob (Q : Ω → Prop) : ℝ := ∑ r, if Q r then T.μ r else 0

/-- `μ_T(Q | Y)`, conditional probability (`0` if `μ_T(Y) = 0`, which never happens for
nonempty `Y`). -/
def cprob (Q Y : Ω → Prop) : ℝ := T.prob (fun r => Q r ∧ Y r) / T.prob Y

/-! ### Facts, local states and beliefs (§§2.3, 3) -/

/-- The fact about runs `ℓ_i`: agent `i` has local state `ℓ` at some point of the run. -/
def Occurs (i : Agent) (ℓ : L) (r : Ω) : Prop := ∃ t ≤ T.len r, T.loc i r t = ℓ

/-- `φ@ℓ_i`: `φ` holds when agent `i` is in local state `ℓ` in the run. -/
def At (φ : Fact Ω) (i : Agent) (ℓ : L) (r : Ω) : Prop :=
  ∃ t ≤ T.len r, T.loc i r t = ℓ ∧ φ r t

/-- Definition 3.1: the degree of belief `β_i(φ)` of agent `i` in `φ` at the point `(r, t)`,
namely `μ_T(φ@ℓ_i | ℓ_i)` for `ℓ_i = r_i(t)`. -/
def belief (i : Agent) (φ : Fact Ω) (r : Ω) (t : ℕ) : ℝ :=
  T.cprob (T.At φ i (T.loc i r t)) (T.Occurs i (T.loc i r t))

/-- The fact about runs `α`: the action (given by the fact `does_i(α)`) is performed in the run. -/
def Performs (A : Fact Ω) (r : Ω) : Prop := ∃ t ≤ T.len r, A r t

/-- §3.1: `α` is a proper action: it is performed in some run, and at most once in every run. -/
def Proper (A : Fact Ω) : Prop :=
  (∃ r, T.Performs A r) ∧ ∀ r t t', t ≤ T.len r → t' ≤ T.len r → A r t → A r t' → t = t'

/-- `φ@α`: `φ` holds when the action is performed. -/
def AtAct (φ A : Fact Ω) (r : Ω) : Prop := ∃ t ≤ T.len r, A r t ∧ φ r t

/-- The time at which the action is performed in `r` (`0` if it is not performed). -/
def actTime (A : Fact Ω) (r : Ω) : ℕ := if h : T.Performs A r then h.choose else 0

/-- `β_i(φ)@α [r]`: the belief of `i` in `φ` when it performs `α` in `r`, and `0` by convention if
`α` is not performed in `r`. -/
def beliefAt (i : Agent) (φ A : Fact Ω) (r : Ω) : ℝ :=
  if T.Performs A r then T.belief i φ r (T.actTime A r) else 0

/-- Definition 4.1: `φ` is local-state independent of `α`:
`μ(φ@ℓ_i | ℓ_i) · μ(α@ℓ_i | ℓ_i) = μ([φ ∧ α]@ℓ_i | ℓ_i)` for all local states `ℓ_i`. -/
def LocalStateIndependent (i : Agent) (φ A : Fact Ω) : Prop :=
  ∀ ℓ : L, T.cprob (T.At φ i ℓ) (T.Occurs i ℓ) * T.cprob (T.At A i ℓ) (T.Occurs i ℓ) =
    T.cprob (T.At (fun r t => φ r t ∧ A r t) i ℓ) (T.Occurs i ℓ)

/-- Definition 6.1: the expected degree of belief `E_μ(β_i(φ)@α | α) = Σ_r μ(r | α) · β_i(φ)@α[r]`. -/
def expBelief (i : Agent) (φ A : Fact Ω) : ℝ :=
  ∑ r, T.cprob (· = r) (T.Performs A) * T.beliefAt i φ A r

/-- §4: `α` is a deterministic action for `i`: whether `i` performs it is a function of its local
state. -/
def Deterministic (i : Agent) (A : Fact Ω) : Prop :=
  ∀ r r' t, t ≤ T.len r → t ≤ T.len r' → T.loc i r t = T.loc i r' t → (A r t ↔ A r' t)

/-! ### Basic facts about `prob` -/

variable {T}

theorem prob_eq_sum_filter (Q : Ω → Prop) : T.prob Q = ∑ r ∈ univ.filter Q, T.μ r := by
  rw [prob, Finset.sum_filter]

theorem prob_nonneg (Q : Ω → Prop) : 0 ≤ T.prob Q :=
  Finset.sum_nonneg fun r _ => by split_ifs <;> [exact (T.μ_pos r).le; exact le_rfl]

theorem prob_mono {Q Q' : Ω → Prop} (h : ∀ r, Q r → Q' r) : T.prob Q ≤ T.prob Q' :=
  Finset.sum_le_sum fun r _ => by
    by_cases hq : Q r
    · simp [hq, h r hq]
    · by_cases hq' : Q' r <;> simp [hq, hq', (T.μ_pos r).le]

theorem prob_congr {Q Q' : Ω → Prop} (h : ∀ r, Q r ↔ Q' r) : T.prob Q = T.prob Q' :=
  le_antisymm (prob_mono fun r => (h r).1) (prob_mono fun r => (h r).2)

theorem prob_true : T.prob (fun _ => True) = 1 := by simp [prob, T.sum_μ]

theorem prob_le_one (Q : Ω → Prop) : T.prob Q ≤ 1 :=
  prob_true (T := T) ▸ prob_mono fun _ _ => trivial

theorem prob_pos {Q : Ω → Prop} {r : Ω} (h : Q r) : 0 < T.prob Q := by
  rw [prob_eq_sum_filter]
  exact Finset.sum_pos (fun r _ => T.μ_pos r) ⟨r, by simpa using h⟩

theorem cprob_nonneg (Q Y : Ω → Prop) : 0 ≤ T.cprob Q Y :=
  div_nonneg (prob_nonneg _) (prob_nonneg _)

theorem cprob_le_one (Q Y : Ω → Prop) : T.cprob Q Y ≤ 1 :=
  div_le_one_of_le₀ (prob_mono fun _ h => h.2) (prob_nonneg _)

/-- Conditional probability of an event contained in the condition. -/
theorem cprob_of_imp {Q Y : Ω → Prop} (h : ∀ r, Q r → Y r) :
    T.cprob Q Y = T.prob Q / T.prob Y := by
  rw [cprob, prob_congr (Q := fun r => Q r ∧ Y r) (Q' := Q) fun r => ⟨And.left, fun hq => ⟨hq, h r hq⟩⟩]

theorem prob_singleton_and (r : Ω) (Y : Ω → Prop) :
    T.prob (fun r' => r' = r ∧ Y r') = if Y r then T.μ r else 0 := by
  rw [prob]
  rw [Finset.sum_eq_single r]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- Conditional probability as a weighted sum of the indicator: `μ(Q | Y) = Σ_r μ(r | Y) [Q r]`. -/
theorem cprob_eq_sum (Q Y : Ω → Prop) :
    T.cprob Q Y = ∑ r, T.cprob (· = r) Y * (if Q r then 1 else 0) := by
  simp only [cprob, prob_singleton_and, mul_ite, mul_one, mul_zero]
  rw [prob, Finset.sum_div]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hq : Q r <;> by_cases hy : Y r <;> simp [hq, hy]

theorem sum_cprob_singleton {Y : Ω → Prop} {r₀ : Ω} (h : Y r₀) :
    ∑ r, T.cprob (· = r) Y = 1 := by
  have := cprob_eq_sum (T := T) (fun _ => True) Y
  simp only [ite_true, mul_one] at this
  rw [← this, cprob, prob_congr (Q' := Y) fun r => ⟨And.right, fun hy => ⟨trivial, hy⟩⟩]
  exact div_self (prob_pos (T := T) h).ne'

theorem cprob_mono {Q Q' Y : Ω → Prop} (h : ∀ r, Q r → Q' r) : T.cprob Q Y ≤ T.cprob Q' Y :=
  div_le_div_of_nonneg_right (prob_mono fun r hr => ⟨h r hr.1, hr.2⟩) (prob_nonneg _)

/-! ### Proper actions -/

theorem actTime_spec {A : Fact Ω} {r : Ω} (h : T.Performs A r) :
    T.actTime A r ≤ T.len r ∧ A r (T.actTime A r) := by
  rw [actTime, dite_eq_left h]; exact h.choose_spec

theorem Proper.actTime_eq {A : Fact Ω} (hA : T.Proper A) {r : Ω} {t : ℕ} (ht : t ≤ T.len r)
    (h : A r t) : T.actTime A r = t :=
  have hp : T.Performs A r := ⟨t, ht, h⟩
  hA.2 r _ t (actTime_spec hp).1 ht (actTime_spec hp).2 h

theorem Proper.atAct_iff {A : Fact Ω} (hA : T.Proper A) (φ : Fact Ω) (r : Ω) :
    T.AtAct φ A r ↔ T.Performs A r ∧ φ r (T.actTime A r) := by
  constructor
  · rintro ⟨t, ht, ha, hφ⟩
    exact ⟨⟨t, ht, ha⟩, hA.actTime_eq ht ha ▸ hφ⟩
  · rintro ⟨hp, hφ⟩
    exact ⟨_, (actTime_spec hp).1, (actTime_spec hp).2, hφ⟩

/-- `[φ ∧ α]@ℓ` for a proper action: `α` is performed, at local state `ℓ`, and `φ` holds then. -/
theorem Proper.at_and_iff {A : Fact Ω} (hA : T.Proper A) (i : Agent) (φ : Fact Ω) (ℓ : L)
    (r : Ω) : T.At (fun r t => φ r t ∧ A r t) i ℓ r ↔
      T.Performs A r ∧ T.loc i r (T.actTime A r) = ℓ ∧ φ r (T.actTime A r) := by
  constructor
  · rintro ⟨t, ht, hl, hφ, ha⟩
    have := hA.actTime_eq ht ha
    exact ⟨⟨t, ht, ha⟩, this ▸ hl, this ▸ hφ⟩
  · rintro ⟨hp, hl, hφ⟩
    exact ⟨_, (actTime_spec hp).1, hl, hφ, (actTime_spec hp).2⟩

theorem Proper.at_iff {A : Fact Ω} (hA : T.Proper A) (i : Agent) (ℓ : L) (r : Ω) :
    T.At A i ℓ r ↔ T.Performs A r ∧ T.loc i r (T.actTime A r) = ℓ := by
  constructor
  · rintro ⟨t, ht, hl, ha⟩
    exact ⟨⟨t, ht, ha⟩, hA.actTime_eq ht ha ▸ hl⟩
  · rintro ⟨hp, hl⟩
    exact ⟨_, (actTime_spec hp).1, hl, (actTime_spec hp).2⟩

theorem at_imp_occurs {φ : Fact Ω} {i : Agent} {ℓ : L} {r : Ω} (h : T.At φ i ℓ r) :
    T.Occurs i ℓ r := by
  obtain ⟨t, ht, hl, -⟩ := h; exact ⟨t, ht, hl⟩

theorem cprob_at (φ : Fact Ω) (i : Agent) (ℓ : L) :
    T.cprob (T.At φ i ℓ) (T.Occurs i ℓ) = T.prob (T.At φ i ℓ) / T.prob (T.Occurs i ℓ) :=
  cprob_of_imp fun _ => at_imp_occurs

theorem belief_nonneg (i : Agent) (φ : Fact Ω) (r : Ω) (t : ℕ) : 0 ≤ T.belief i φ r t :=
  cprob_nonneg _ _

theorem belief_le_one (i : Agent) (φ : Fact Ω) (r : Ω) (t : ℕ) : T.belief i φ r t ≤ 1 :=
  cprob_le_one _ _

theorem beliefAt_nonneg (i : Agent) (φ A : Fact Ω) (r : Ω) : 0 ≤ T.beliefAt i φ A r := by
  unfold beliefAt; split_ifs <;> [exact belief_nonneg _ _ _ _; exact le_rfl]

theorem beliefAt_le_one (i : Agent) (φ A : Fact Ω) (r : Ω) : T.beliefAt i φ A r ≤ 1 := by
  unfold beliefAt; split_ifs <;> [exact belief_le_one _ _ _ _; exact zero_le_one]

/-- The weights `μ(r | α)` of runs in which `α` is performed are positive. -/
theorem cprob_singleton_pos {Y : Ω → Prop} {r : Ω} (h : Y r) : 0 < T.cprob (· = r) Y := by
  rw [cprob, prob_singleton_and, ite_eq_left h]
  exact div_pos (T.μ_pos r) (prob_pos h)

theorem cprob_singleton_of_not {Y : Ω → Prop} {r : Ω} (h : ¬ Y r) : T.cprob (· = r) Y = 0 := by
  rw [cprob, prob_singleton_and, ite_eq_right h, zero_div]

/-! ### Theorem 6.2: probability of a constraint = expected degree of belief -/

/-- The key computation: `Σ_{r ∈ R_α} μ(r) · β_i(φ)@α[r] = μ(φ@α)` (equations (10)–(23)). -/
theorem sum_mu_beliefAt {i : Agent} {φ A : Fact Ω} (hA : T.Proper A)
    (hI : T.LocalStateIndependent i φ A) :
    ∑ r ∈ univ.filter (T.Performs A), T.μ r * T.beliefAt i φ A r = T.prob (T.AtAct φ A) := by
  set s := univ.filter (T.Performs A)
  set k : Ω → L := fun r => T.loc i r (T.actTime A r)
  -- `F ℓ = μ(α@ℓ)` and `G ℓ = μ([φ ∧ α]@ℓ)` as sums over the fibre of `k` above `ℓ`
  have hF : ∀ ℓ, T.prob (T.At A i ℓ) = ∑ r ∈ s with k r = ℓ, T.μ r := by
    intro ℓ
    rw [prob_eq_sum_filter, Finset.filter_filter]
    exact Finset.sum_congr (Finset.filter_congr fun r _ => hA.at_iff i ℓ r) fun _ _ => rfl
  have hG : ∀ ℓ, T.prob (T.At (fun r t => φ r t ∧ A r t) i ℓ) =
      ∑ r ∈ s with k r = ℓ, if φ r (T.actTime A r) then T.μ r else 0 := by
    intro ℓ
    rw [prob_eq_sum_filter, Finset.filter_filter, ← Finset.sum_filter, Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun r _ => ?_) fun _ _ => rfl
    rw [hA.at_and_iff]; tauto
  -- for `r ∈ R_α`, the belief at the action is `μ(φ@ℓ | ℓ)` with `ℓ = k r`, and
  -- `μ(φ@ℓ | ℓ) · μ(α@ℓ) = μ([φ ∧ α]@ℓ)` by local-state independence
  set c : L → ℝ := fun ℓ => T.cprob (T.At φ i ℓ) (T.Occurs i ℓ)
  have hc : ∀ r ∈ s, c (k r) * T.prob (T.At A i (k r)) =
      T.prob (T.At (fun r t => φ r t ∧ A r t) i (k r)) := by
    intro r hr
    have hp : T.Performs A r := (Finset.mem_filter.1 hr).2
    have hocc : 0 < T.prob (T.Occurs i (k r)) :=
      prob_pos ⟨_, (actTime_spec hp).1, rfl⟩
    have := hI (k r)
    simp only [cprob_at] at this
    simp only [c, cprob_at]
    field_simp at this ⊢
    linarith [this]
  have hb : ∀ r ∈ s, T.beliefAt i φ A r = c (k r) := by
    intro r hr
    simp [beliefAt, (Finset.mem_filter.1 hr).2, belief, c, k]
  calc ∑ r ∈ s, T.μ r * T.beliefAt i φ A r
      = ∑ r ∈ s, T.μ r * c (k r) := Finset.sum_congr rfl fun r hr => by rw [hb r hr]
    _ = ∑ ℓ ∈ s.image k, ∑ r ∈ s with k r = ℓ, T.μ r * c (k r) :=
        (Finset.sum_fiberwise_of_maps_to (fun r hr => Finset.mem_image_of_mem k hr) _).symm
    _ = ∑ ℓ ∈ s.image k, c ℓ * T.prob (T.At A i ℓ) := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [hF, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [(Finset.mem_filter.1 hr).2, mul_comm]
    _ = ∑ ℓ ∈ s.image k, ∑ r ∈ s with k r = ℓ, if φ r (T.actTime A r) then T.μ r else 0 := by
        refine Finset.sum_congr rfl fun ℓ hℓ => ?_
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hℓ
        rw [hc r hr, hG]
    _ = ∑ r ∈ s, if φ r (T.actTime A r) then T.μ r else 0 :=
        Finset.sum_fiberwise_of_maps_to (fun r hr => Finset.mem_image_of_mem k hr) _
    _ = T.prob (T.AtAct φ A) := by
        rw [Finset.sum_filter, prob]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hA.atAct_iff]
        by_cases hp : T.Performs A r <;> by_cases hφ : φ r (T.actTime A r) <;> simp [hp, hφ]

theorem atAct_imp_performs {φ A : Fact Ω} {r : Ω} (h : T.AtAct φ A r) : T.Performs A r := by
  obtain ⟨t, ht, ha, -⟩ := h; exact ⟨t, ht, ha⟩

theorem expBelief_eq_sum {i : Agent} {φ A : Fact Ω} :
    T.expBelief i φ A =
      (∑ r ∈ univ.filter (T.Performs A), T.μ r * T.beliefAt i φ A r) / T.prob (T.Performs A) := by
  rw [expBelief, Finset.sum_filter, Finset.sum_div]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [cprob, prob_singleton_and]
  split_ifs <;> ring

/-- **Theorem 6.2** of [Moses–Zamir] (main theorem). If `α` is a proper action for `i` and `φ` is
local-state independent of `α`, then `μ_T(φ@α | α) = E_μ(β_i(φ)@α | α)`. -/
theorem theorem_6_2 {i : Agent} {φ A : Fact Ω} (hA : T.Proper A)
    (hI : T.LocalStateIndependent i φ A) :
    T.cprob (T.AtAct φ A) (T.Performs A) = T.expBelief i φ A := by
  rw [expBelief_eq_sum, sum_mu_beliefAt hA hI, cprob_of_imp fun _ => atAct_imp_performs]

/-! ### Corollaries of Theorem 6.2 -/

/-- Expected belief as a weighted average with weights `w r = μ(r | α)`. -/
private theorem weights {A : Fact Ω} (hA : T.Proper A) :
    (∀ r, 0 ≤ T.cprob (· = r) (T.Performs A)) ∧ ∑ r, T.cprob (· = r) (T.Performs A) = 1 :=
  ⟨fun _ => cprob_nonneg _ _, by obtain ⟨r, hr⟩ := hA.1; exact sum_cprob_singleton hr⟩

/-- **Theorem 4.2** of [Moses–Zamir] (sufficiency of meeting the threshold). If `α` is proper,
`φ` is local-state independent of `α`, and `β_i(φ) ≥ p` at every point at which `i` performs `α`,
then `μ_T(φ@α | α) ≥ p`. -/
theorem theorem_4_2 {i : Agent} {φ A : Fact Ω} {p : ℝ} (hA : T.Proper A)
    (hI : T.LocalStateIndependent i φ A)
    (hβ : ∀ r t, t ≤ T.len r → A r t → p ≤ T.belief i φ r t) :
    p ≤ T.cprob (T.AtAct φ A) (T.Performs A) := by
  rw [theorem_6_2 hA hI, expBelief]
  obtain ⟨hw0, hw1⟩ := weights hA
  calc p = ∑ r, T.cprob (· = r) (T.Performs A) * p := by rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun r _ => by
      by_cases hp : T.Performs A r
      · refine mul_le_mul_of_nonneg_left ?_ (hw0 r)
        rw [beliefAt, ite_eq_left hp]
        exact hβ r _ (actTime_spec hp).1 (actTime_spec hp).2
      · simp [cprob_singleton_of_not hp]

/-- **Lemma 5.1** of [Moses–Zamir]. If `α` is proper, `φ` is local-state independent of `α` and
`μ_T(φ@α | α) ≥ p`, then at some point at which `α` is performed, `β_i(φ) ≥ p`. -/
theorem lemma_5_1 {i : Agent} {φ A : Fact Ω} {p : ℝ} (hA : T.Proper A)
    (hI : T.LocalStateIndependent i φ A) (h : p ≤ T.cprob (T.AtAct φ A) (T.Performs A)) :
    ∃ r t, t ≤ T.len r ∧ A r t ∧ p ≤ T.belief i φ r t := by
  by_contra hne
  push Not at hne
  rw [theorem_6_2 hA hI, expBelief] at h
  obtain ⟨hw0, hw1⟩ := weights hA
  obtain ⟨r₀, hr₀⟩ := hA.1
  have : ∑ r, T.cprob (· = r) (T.Performs A) * T.beliefAt i φ A r <
      ∑ r, T.cprob (· = r) (T.Performs A) * p := by
    refine Finset.sum_lt_sum (fun r _ => ?_) ⟨r₀, mem_univ _, ?_⟩
    · by_cases hp : T.Performs A r
      · refine mul_le_mul_of_nonneg_left ?_ (hw0 r)
        rw [beliefAt, ite_eq_left hp]
        exact (hne r _ (actTime_spec hp).1 (actTime_spec hp).2).le
      · simp [cprob_singleton_of_not hp]
    · refine mul_lt_mul_of_pos_left ?_ (cprob_singleton_pos hr₀)
      rw [beliefAt, ite_eq_left hr₀]
      exact hne r₀ _ (actTime_spec hr₀).1 (actTime_spec hr₀).2
  rw [← Finset.sum_mul, hw1, one_mul] at this
  linarith

/-- Markov's inequality for the belief at the action (the core of Theorem 7.1):
`ε · μ(β_i(φ)@α < 1 - ε | α) ≤ 1 - μ(φ@α | α)`. -/
theorem markov_beliefAt {i : Agent} {φ A : Fact Ω} (hA : T.Proper A)
    (hI : T.LocalStateIndependent i φ A) (ε : ℝ) :
    ε * T.cprob (fun r => T.beliefAt i φ A r < 1 - ε) (T.Performs A) ≤
      1 - T.cprob (T.AtAct φ A) (T.Performs A) := by
  rw [theorem_6_2 hA hI, expBelief, cprob_eq_sum, Finset.mul_sum]
  obtain ⟨hw0, hw1⟩ := weights hA
  have hsub : (1 : ℝ) - ∑ r, T.cprob (· = r) (T.Performs A) * T.beliefAt i φ A r =
      ∑ r, (T.cprob (· = r) (T.Performs A) -
        T.cprob (· = r) (T.Performs A) * T.beliefAt i φ A r) := by
    rw [Finset.sum_sub_distrib, hw1]
  rw [hsub]
  refine Finset.sum_le_sum fun r _ => ?_
  have h1 := beliefAt_le_one (T := T) i φ A r
  have h0 := hw0 r
  split_ifs with hlt
  · nlinarith
  · nlinarith

/-- **Theorem 7.1** of [Moses–Zamir]. For `δ, ε ∈ (0, 1)`: if `μ_T(φ@α | α) ≥ 1 - δε` then
`μ_T(β_i(φ)@α ≥ 1 - ε | α) ≥ 1 - δ`. -/
theorem theorem_7_1 {i : Agent} {φ A : Fact Ω} (hA : T.Proper A)
    (hI : T.LocalStateIndependent i φ A) {δ ε : ℝ} (_hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (h : 1 - δ * ε ≤ T.cprob (T.AtAct φ A) (T.Performs A)) :
    1 - δ ≤ T.cprob (fun r => 1 - ε ≤ T.beliefAt i φ A r) (T.Performs A) := by
  have hm := markov_beliefAt hA hI ε
  -- the two conditional probabilities add up to one
  have hsum : T.cprob (fun r => T.beliefAt i φ A r < 1 - ε) (T.Performs A) +
      T.cprob (fun r => 1 - ε ≤ T.beliefAt i φ A r) (T.Performs A) = 1 := by
    rw [cprob_eq_sum, cprob_eq_sum, ← Finset.sum_add_distrib]
    conv_rhs => rw [← (weights hA).2]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hlt : T.beliefAt i φ A r < 1 - ε
    · simp [hlt, not_le.2 hlt]
    · simp [hlt, le_of_not_gt hlt]
  have : T.cprob (fun r => T.beliefAt i φ A r < 1 - ε) (T.Performs A) ≤ δ := by
    by_contra hc
    push Not at hc
    nlinarith [hε.1]
  linarith

/-- **Lemma F.1** of [Moses–Zamir]. If `μ_T(φ@α | α) = 1` then `μ_T(β_i(φ)@α = 1 | α) = 1`. -/
theorem lemma_F_1 {i : Agent} {φ A : Fact Ω} (hA : T.Proper A)
    (hI : T.LocalStateIndependent i φ A) (h : T.cprob (T.AtAct φ A) (T.Performs A) = 1) :
    T.cprob (fun r => T.beliefAt i φ A r = 1) (T.Performs A) = 1 := by
  obtain ⟨hw0, hw1⟩ := weights hA
  rw [theorem_6_2 hA hI, expBelief] at h
  -- every run of `R_α` has belief `1`
  have hall : ∀ r, T.Performs A r → T.beliefAt i φ A r = 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨r₀, hr₀, hne⟩ := hne
    have : ∑ r, T.cprob (· = r) (T.Performs A) * T.beliefAt i φ A r <
        ∑ r, T.cprob (· = r) (T.Performs A) * 1 :=
      Finset.sum_lt_sum (fun r _ => mul_le_mul_of_nonneg_left (beliefAt_le_one _ _ _ _) (hw0 r))
        ⟨r₀, mem_univ _, mul_lt_mul_of_pos_left (lt_of_le_of_ne (beliefAt_le_one _ _ _ _) hne)
          (cprob_singleton_pos hr₀)⟩
    simp only [mul_one, hw1] at this
    linarith
  rw [cprob_eq_sum]
  conv_rhs => rw [← hw1]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hp : T.Performs A r
  · simp [hall r hp]
  · simp [cprob_singleton_of_not hp]

/-- **Corollary 7.2** of [Moses–Zamir] (probably approximately knowing). For every `ε ≥ 0`: if
`μ_T(φ@α | α) ≥ 1 - ε²` then `μ_T(β_i(φ)@α ≥ 1 - ε | α) ≥ 1 - ε`. -/
theorem corollary_7_2 {i : Agent} {φ A : Fact Ω} (hA : T.Proper A)
    (hI : T.LocalStateIndependent i φ A) {ε : ℝ} (hε : 0 ≤ ε)
    (h : 1 - ε ^ 2 ≤ T.cprob (T.AtAct φ A) (T.Performs A)) :
    1 - ε ≤ T.cprob (fun r => 1 - ε ≤ T.beliefAt i φ A r) (T.Performs A) := by
  rcases hε.eq_or_lt with rfl | hε
  · have h1 : T.cprob (T.AtAct φ A) (T.Performs A) = 1 :=
      le_antisymm (cprob_le_one _ _) (by simpa using h)
    have := lemma_F_1 hA hI h1
    rw [sub_zero]
    exact this.symm.le.trans (cprob_mono fun r hr => hr.symm.le)
  rcases lt_or_ge ε 1 with h1 | h1
  · exact theorem_7_1 hA hI ⟨hε, h1⟩ ⟨hε, h1⟩ (by nlinarith)
  · exact (sub_nonpos.2 h1).trans (cprob_nonneg _ _)

/-- Remark after Corollary 7.2: to satisfy a constraint with threshold `p ≤ 1`, `φ` must be believed
with degree at least `p' = 1 - √(1 - p)` with probability at least `p'`. -/
theorem threshold_sqrt {i : Agent} {φ A : Fact Ω} (hA : T.Proper A)
    (hI : T.LocalStateIndependent i φ A) {p : ℝ} (hp : p ≤ 1)
    (h : p ≤ T.cprob (T.AtAct φ A) (T.Performs A)) :
    1 - √(1 - p) ≤
      T.cprob (fun r => 1 - √(1 - p) ≤ T.beliefAt i φ A r) (T.Performs A) :=
  corollary_7_2 hA hI (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt (by linarith)]; linarith)

/-! ### Appendix lemmas and Lemma 4.3(a) -/

/-- **Lemma B.1** of [Moses–Zamir]. For a local state `ℓ` at which `α` is performed,
`μ(φ@α | α@ℓ) = μ(φ@ℓ | ℓ)`. -/
theorem lemma_B_1 {i : Agent} {φ A : Fact Ω} (hA : T.Proper A)
    (hI : T.LocalStateIndependent i φ A) {ℓ : L} {r₀ : Ω} (hℓ : T.At A i ℓ r₀) :
    T.cprob (T.AtAct φ A) (T.At A i ℓ) = T.cprob (T.At φ i ℓ) (T.Occurs i ℓ) := by
  have hpos : 0 < T.prob (T.At A i ℓ) := prob_pos hℓ
  have hocc : 0 < T.prob (T.Occurs i ℓ) := prob_pos (at_imp_occurs hℓ)
  have h := hI ℓ
  rw [cprob_at, cprob_at, cprob_at] at h
  rw [cprob, cprob_at,
    prob_congr (Q' := T.At (fun r t => φ r t ∧ A r t) i ℓ) fun r => by
      rw [hA.atAct_iff, hA.at_iff, hA.at_and_iff]; tauto]
  field_simp at h ⊢
  linarith

/-- **Lemma 4.3(a)** of [Moses–Zamir]. If `α` is a deterministic action for `i` then every fact `φ`
is local-state independent of `α`. -/
theorem lemma_4_3a {i : Agent} {A : Fact Ω} (hD : T.Deterministic i A) (φ : Fact Ω) :
    T.LocalStateIndependent i φ A := by
  intro ℓ
  rw [cprob_at, cprob_at, cprob_at]
  by_cases hex : ∃ r₀ t₀, t₀ ≤ T.len r₀ ∧ T.loc i r₀ t₀ = ℓ ∧ A r₀ t₀
  · -- `α` is performed at every occurrence of `ℓ`
    obtain ⟨r₀, t₀, ht₀, hl₀, ha₀⟩ := hex
    have hall : ∀ r t, t ≤ T.len r → T.loc i r t = ℓ → A r t := by
      intro r t ht hl
      have := T.sync i r r₀ t t₀ ht ht₀ (hl.trans hl₀.symm)
      subst this
      exact (hD r₀ r t ht₀ ht (hl₀.trans hl.symm)).1 ha₀
    have h1 : T.prob (T.At A i ℓ) = T.prob (T.Occurs i ℓ) :=
      prob_congr fun r => ⟨at_imp_occurs, fun ⟨t, ht, hl⟩ => ⟨t, ht, hl, hall r t ht hl⟩⟩
    have h2 : T.prob (T.At (fun r t => φ r t ∧ A r t) i ℓ) = T.prob (T.At φ i ℓ) :=
      prob_congr fun r => ⟨fun ⟨t, ht, hl, hφ, _⟩ => ⟨t, ht, hl, hφ⟩,
        fun ⟨t, ht, hl, hφ⟩ => ⟨t, ht, hl, hφ, hall r t ht hl⟩⟩
    rw [h1, h2]
    have hocc : 0 < T.prob (T.Occurs i ℓ) := prob_pos ⟨t₀, ht₀, hl₀⟩
    field_simp
  · -- `α` is never performed at `ℓ`
    push Not at hex
    have h1 : T.prob (T.At A i ℓ) = 0 := by
      rw [prob_congr (Q' := fun _ => False) fun r =>
        ⟨fun ⟨t, ht, hl, ha⟩ => hex r t ht hl ha, False.elim⟩]
      simp [prob]
    have h2 : T.prob (T.At (fun r t => φ r t ∧ A r t) i ℓ) = 0 := by
      rw [prob_congr (Q' := fun _ => False) fun r =>
        ⟨fun ⟨t, ht, hl, _, ha⟩ => hex r t ht hl ha, False.elim⟩]
      simp [prob]
    simp [h1, h2]

/-- For a fact `ψ` about runs (§3.1), `μ(ψ@α | α) = μ(ψ | α)`. -/
theorem cprob_atAct_of_run_fact {ψ : Ω → Prop} {A : Fact Ω} :
    T.cprob (T.AtAct (fun r _ => ψ r) A) (T.Performs A) = T.cprob ψ (T.Performs A) := by
  unfold cprob
  congr 1
  exact prob_congr fun r => ⟨fun ⟨h, _⟩ => ⟨by obtain ⟨t, ht, ha, hψ⟩ := h; exact hψ,
    atAct_imp_performs h⟩, fun ⟨hψ, t, ht, ha⟩ => ⟨⟨t, ht, ha, hψ⟩, t, ht, ha⟩⟩

/-- §6, after Theorem 6.2: under local-state independence, the expected belief meeting the
threshold is necessary *and sufficient* for the probabilistic constraint. -/
theorem constraint_iff_expBelief {i : Agent} {φ A : Fact Ω} (hA : T.Proper A)
    (hI : T.LocalStateIndependent i φ A) (p : ℝ) :
    p ≤ T.cprob (T.AtAct φ A) (T.Performs A) ↔ p ≤ T.expBelief i φ A := by
  rw [theorem_6_2 hA hI]

/-! ### Systems whose local states are pairs (time, content) -/

/-- A pps with runs of a common length `n` whose local states are `(t, f i r t)`; synchrony holds
automatically. -/
def ofTimed {X : Type*} (μ : Ω → ℝ) (μ_pos : ∀ r, 0 < μ r) (sum_μ : ∑ r, μ r = 1) (n : ℕ)
    (f : Agent → Ω → ℕ → X) : PPS Ω Agent (ℕ × X) where
  μ := μ
  μ_pos := μ_pos
  sum_μ := sum_μ
  len _ := n
  loc i r t := (t, f i r t)
  sync _ _ _ _ _ _ _ h := congrArg Prod.fst h

section ofTimed
variable {X : Type*} {μ : Ω → ℝ} {μ_pos : ∀ r, 0 < μ r} {sum_μ : ∑ r, μ r = 1} {n : ℕ}
  {f : Agent → Ω → ℕ → X}

theorem ofTimed_occurs {i : Agent} {t₀ : ℕ} {x : X} {r : Ω} :
    (ofTimed μ μ_pos sum_μ n f).Occurs i (t₀, x) r ↔ t₀ ≤ n ∧ f i r t₀ = x := by
  simp only [Occurs, ofTimed, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, rfl, h⟩; exact ⟨ht, h⟩
  · rintro ⟨ht, h⟩; exact ⟨t₀, ht, rfl, h⟩

theorem ofTimed_at {φ : Fact Ω} {i : Agent} {t₀ : ℕ} {x : X} {r : Ω} :
    (ofTimed μ μ_pos sum_μ n f).At φ i (t₀, x) r ↔ t₀ ≤ n ∧ f i r t₀ = x ∧ φ r t₀ := by
  simp only [At, ofTimed, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, ⟨rfl, h⟩, hφ⟩; exact ⟨ht, h, hφ⟩
  · rintro ⟨ht, h, hφ⟩; exact ⟨t₀, ht, ⟨rfl, h⟩, hφ⟩

end ofTimed

end PPS

end Podc.ProbablyApproxKnowing
