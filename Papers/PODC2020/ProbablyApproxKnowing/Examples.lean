import Papers.PODC2020.ProbablyApproxKnowing.Basic

/-!
# The examples of §§4 and 6 (Figure 1) and Theorem 5.2 (Figure 2)

* `Fig1`: the system of Figure 1 — one agent, one initial state, at time 0 the agent performs `α` or
  `α'` with probability `1/2` each. With `ψ = ¬does_i(α)` it shows that Theorem 4.2 fails without
  local-state independence (`Fig1.theorem_4_2_needs_independence`); with `φ = does_i(α)` it shows
  that Theorem 6.2 fails without it (`Fig1.theorem_6_2_needs_independence`).
* `Fig2`: the system `T̂` of the proof of Theorem 5.2, and Theorem 5.2 itself (`theorem_5_2`): the
  threshold of a probabilistic constraint may be met on an arbitrarily small measure of runs.
-/

namespace Podc.ProbablyApproxKnowing

open Finset

private theorem exists_le_one {P : ℕ → Prop} : (∃ t ≤ 1, P t) ↔ P 0 ∨ P 1 := by
  constructor
  · rintro ⟨t, ht, h⟩
    interval_cases t <;> simp_all
  · rintro (h | h) <;> exact ⟨_, by norm_num, h⟩

private theorem exists_le_two {P : ℕ → Prop} : (∃ t ≤ 2, P t) ↔ P 0 ∨ P 1 ∨ P 2 := by
  constructor
  · rintro ⟨t, ht, h⟩
    interval_cases t <;> simp_all
  · rintro (h | h | h) <;> exact ⟨_, by norm_num, h⟩

/-! ## Figure 1 -/

namespace Fig1

/-- The pps of Figure 1. One agent (`Unit`), whose local state is just the current time; two runs:
`true` is the run `r` in which `α` is performed at time 0, `false` the run `r'` in which `α' ≠ α`
is performed at time 0; each has probability `1/2`. -/
noncomputable def T : PPS Bool Unit ℕ where
  μ _ := 1 / 2
  μ_pos _ := by norm_num
  sum_μ := by norm_num
  len _ := 1
  loc _ _ t := t
  sync _ _ _ _ _ _ _ h := h

/-- The fact `does_i(α)`. -/
def doesα : Fact Bool := fun r t => r = true ∧ t = 0

/-- The fact `ψ = ¬does_i(α)`. -/
def ψ : Fact Bool := fun r t => ¬ doesα r t

theorem performs_iff (r : Bool) : T.Performs doesα r ↔ r = true := by
  simp [PPS.Performs, doesα, T]

theorem proper : T.Proper doesα :=
  ⟨⟨true, (performs_iff _).2 rfl⟩, fun _ _ _ _ _ h h' => h.2.trans h'.2.symm⟩

open Classical in
theorem prob_bool (Q : Bool → Prop) :
    T.prob Q = (if Q true then 1 / 2 else 0) + (if Q false then 1 / 2 else 0) := by
  simp [PPS.prob, T, add_comm]

/-- At the initial state the agent believes `ψ` (that `α` is not performed) with degree `1/2`. -/
theorem belief_ψ : T.belief () ψ true 0 = 1 / 2 := by
  have h1 : ∀ r, T.At ψ () 0 r ↔ r = false := by
    intro r; cases r <;> simp [PPS.At, ψ, doesα, T]
  have h2 : ∀ r, T.Occurs () 0 r := fun r => ⟨0, by simp [T], rfl⟩
  simp only [PPS.belief, PPS.cprob_at]
  rw [show T.loc () true 0 = 0 from rfl, PPS.prob_congr h1,
    PPS.prob_congr (Q' := fun _ => True) fun r => ⟨fun _ => trivial, fun _ => h2 r⟩,
    prob_bool, prob_bool]
  norm_num

theorem cprob_ψ : T.cprob (T.AtAct ψ doesα) (T.Performs doesα) = 0 := by
  rw [PPS.cprob, PPS.prob_congr (Q' := fun _ => False)]
  · simp [PPS.prob]
  · intro r
    simp only [iff_false, not_and]
    rintro ⟨t, -, ha, hψ⟩ -
    exact hψ ha

/-- §4: without local-state independence, Theorem 4.2 fails: in Figure 1, `β_i(ψ) ≥ 1/2` whenever
`α` is performed, but `μ(ψ@α | α) = 0 < 1/2`. -/
theorem theorem_4_2_needs_independence :
    T.Proper doesα ∧
      (∀ r t, t ≤ T.len r → doesα r t → (1 / 2 : ℝ) ≤ T.belief () ψ r t) ∧
      T.cprob (T.AtAct ψ doesα) (T.Performs doesα) < 1 / 2 ∧
      ¬ T.LocalStateIndependent () ψ doesα := by
  refine ⟨proper, ?_, by rw [cprob_ψ]; norm_num, fun hI => ?_⟩
  · rintro r t - ⟨rfl, rfl⟩
    rw [belief_ψ]
  · have := PPS.theorem_4_2 (p := 1 / 2) proper hI (by
      rintro r t - ⟨rfl, rfl⟩; rw [belief_ψ])
    rw [cprob_ψ] at this
    norm_num at this

/-- At the initial state the agent believes `does_i(α)` with degree `1/2`. -/
theorem belief_doesα : T.belief () doesα true 0 = 1 / 2 := by
  have h1 : ∀ r, T.At doesα () 0 r ↔ r = true := by
    intro r; cases r <;> simp [PPS.At, doesα, T]
  have h2 : ∀ r, T.Occurs () 0 r := fun r => ⟨0, by simp [T], rfl⟩
  simp only [PPS.belief, PPS.cprob_at]
  rw [show T.loc () true 0 = 0 from rfl, PPS.prob_congr h1,
    PPS.prob_congr (Q' := fun _ => True) fun r => ⟨fun _ => trivial, fun _ => h2 r⟩,
    prob_bool, prob_bool]
  norm_num

/-- §6: without local-state independence, Theorem 6.2 fails: in Figure 1 with `φ = does_i(α)`,
`μ(φ@α | α) = 1` but `E(β_i(φ)@α | α) = 1/2`. -/
theorem theorem_6_2_needs_independence :
    T.cprob (T.AtAct doesα doesα) (T.Performs doesα) = 1 ∧
      T.expBelief () doesα doesα = 1 / 2 := by
  have hperf : T.prob (T.Performs doesα) = 1 / 2 := by
    rw [prob_bool]; simp [performs_iff]
  constructor
  · rw [PPS.cprob_of_imp fun _ => PPS.atAct_imp_performs,
      PPS.prob_congr (Q' := T.Performs doesα) fun r =>
        ⟨PPS.atAct_imp_performs, fun ⟨t, ht, h⟩ => ⟨t, ht, h, h⟩⟩]
    rw [hperf]; norm_num
  · rw [PPS.expBelief, Fintype.sum_bool]
    have hb : T.beliefAt () doesα doesα true = 1 / 2 := by
      rw [PPS.beliefAt, ite_eq_left ((performs_iff _).2 rfl),
        proper.actTime_eq (t := 0) (by simp [T]) ⟨rfl, rfl⟩, belief_doesα]
    rw [hb, PPS.cprob_singleton_of_not (r := false) (by simp [performs_iff]), PPS.cprob, hperf,
      PPS.prob_singleton_and, ite_eq_left ((performs_iff _).2 rfl)]
    simp [T]

end Fig1

/-! ## Figure 2 and Theorem 5.2 -/

namespace Fig2

/-- Agents of `T̂`. -/
inductive Ag | i | j
  deriving DecidableEq

/-- The pps `T̂` of the proof of Theorem 5.2, for `0 < ε < p < 1`. Runs (`Fin 3`): `0` is `r`
(`bit = 0`, `j` sends `m_j`), `1` is `r'` (`bit = 1`, `j` sends `m_j`), `2` is `r''` (`bit = 1`, `j`
sends `m'_j`); probabilities `1 - p`, `p (1 - ε/p) = p - ε` and `p · ε/p = ε`. Local states are
pairs (time, content): `j` holds its bit; `i` holds nothing at time 0 and the received message from
time 1 on (`some false` = `m_j`, `some true` = `m'_j`). Runs have length 2 (`i` acts at time 1). -/
noncomputable def T (p ε : ℝ) (hε : 0 < ε) (hεp : ε < p) (hp : p < 1) :
    PPS (Fin 3) Ag (ℕ × Option Bool) where
  μ r := ![1 - p, p - ε, ε] r
  μ_pos r := by fin_cases r <;> simp <;> linarith
  sum_μ := by simp [Fin.sum_univ_three]
  len _ := 2
  loc a r t := match a with
    | .i => (t, if t = 0 then none else some (decide (r = 2)))
    | .j => (t, some (decide (r ≠ 0)))
  sync a _ _ _ _ _ _ h := by cases a <;> exact congrArg Prod.fst h

/-- The fact `φ`: "`bit = 1`" (a fact about runs). -/
def φ : Fact (Fin 3) := fun r _ => r ≠ 0

/-- The action `α`, performed by `i` unconditionally at time 1. -/
def doesα : Fact (Fin 3) := fun _ t => t = 1

variable {p ε : ℝ} (hε : 0 < ε) (hεp : ε < p) (hp : p < 1)

theorem performs (r : Fin 3) : (T p ε hε hεp hp).Performs doesα r :=
  ⟨1, by simp [T], rfl⟩

theorem proper : (T p ε hε hεp hp).Proper doesα :=
  ⟨⟨0, performs hε hεp hp 0⟩, fun _ _ _ _ _ h h' => h.trans h'.symm⟩

theorem deterministic : (T p ε hε hεp hp).Deterministic .i doesα :=
  fun _ _ _ _ _ _ => Iff.rfl

open Classical in
theorem prob_fin3 (Q : Fin 3 → Prop) : (T p ε hε hεp hp).prob Q =
    (if Q 0 then 1 - p else 0) + (if Q 1 then p - ε else 0) + (if Q 2 then ε else 0) := by
  simp [PPS.prob, T, Fin.sum_univ_three]

theorem actTime (r : Fin 3) : (T p ε hε hεp hp).actTime doesα r = 1 :=
  (proper hε hεp hp).actTime_eq (by simp [T]) rfl

/-- `μ(φ@α | α) = p`. -/
theorem cprob_φ : (T p ε hε hεp hp).cprob ((T p ε hε hεp hp).AtAct φ doesα)
    ((T p ε hε hεp hp).Performs doesα) = p := by
  rw [PPS.cprob, prob_fin3, prob_fin3]
  have hA : ∀ r, (T p ε hε hεp hp).AtAct φ doesα r ↔ r ≠ 0 := fun r => by
    rw [(proper hε hεp hp).atAct_iff, actTime]; simp [performs hε hεp hp r, φ]
  simp only [hA, performs hε hεp hp, and_true]
  simp

/-- The belief of `i` in `φ` when it performs `α`: `(p - ε)/(1 - ε)` in `r` and `r'`, and `1`
in `r''`. -/
theorem beliefAt_eq (r : Fin 3) : (T p ε hε hεp hp).beliefAt .i φ doesα r =
    if r = 2 then 1 else (p - ε) / (1 - ε) := by
  rw [PPS.beliefAt, ite_eq_left (performs hε hεp hp r), actTime, PPS.belief, PPS.cprob_at,
    prob_fin3, prob_fin3]
  have hO : ∀ r', (T p ε hε hεp hp).Occurs .i ((T p ε hε hεp hp).loc .i r 1) r' ↔
      (r' = 2 ↔ r = 2) := fun r' => by
    simp only [PPS.Occurs, exists_le_two, T]
    simp
  have hAt : ∀ r', (T p ε hε hεp hp).At φ .i ((T p ε hε hεp hp).loc .i r 1) r' ↔
      (r' = 2 ↔ r = 2) ∧ r' ≠ 0 := fun r' => by
    simp only [PPS.At, exists_le_two, T, φ]
    simp
  simp only [hO, hAt]
  have h1 : 1 - ε ≠ 0 := by linarith
  fin_cases r <;> simp [hε.ne']

theorem beliefAt_lt (r : Fin 3) (hr : r ≠ 2) : (T p ε hε hεp hp).beliefAt .i φ doesα r < p := by
  rw [beliefAt_eq, ite_eq_right hr, div_lt_iff₀ (by linarith)]
  nlinarith

/-- `μ(β_i(φ)@α ≥ p | α) = ε`: only in `r''` (probability `ε`) the threshold is met. -/
theorem cprob_threshold : (T p ε hε hεp hp).cprob
    (fun r => p ≤ (T p ε hε hεp hp).beliefAt .i φ doesα r)
    ((T p ε hε hεp hp).Performs doesα) = ε := by
  have h : ∀ r, p ≤ (T p ε hε hεp hp).beliefAt .i φ doesα r ↔ r = 2 := fun r => by
    by_cases hr : r = 2
    · simp [hr, beliefAt_eq, hp.le]
    · simp [hr, (beliefAt_lt hε hεp hp r hr).not_ge]
  rw [PPS.cprob, prob_fin3, prob_fin3]
  simp only [h, performs hε hεp hp, and_true]
  simp

end Fig2

/-- **Theorem 5.2** of [Moses–Zamir]. For every `ε > 0` and `0 < p < 1` there is a pps `T̂`, a proper
action `α` for an agent `i` and a fact `φ` local-state independent of `α`, such that
`μ(φ@α | α) ≥ p` but `μ(β_i(φ)@α ≥ p | α) ≤ ε`. -/
theorem theorem_5_2 (ε p : ℝ) (hε : 0 < ε) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ (Ω : Type) (_ : Fintype Ω) (Agent L : Type) (T : PPS Ω Agent L) (i : Agent)
      (φ A : Fact Ω), T.Proper A ∧ T.LocalStateIndependent i φ A ∧
        p ≤ T.cprob (T.AtAct φ A) (T.Performs A) ∧
        T.cprob (fun r => p ≤ T.beliefAt i φ A r) (T.Performs A) ≤ ε := by
  -- it suffices to treat `ε' = min ε (p/2) < p`
  set ε' := min ε (p / 2)
  have hε' : 0 < ε' := lt_min hε (by linarith)
  have hε'p : ε' < p := (min_le_right _ _).trans_lt (by linarith)
  refine ⟨Fin 3, inferInstance, Fig2.Ag, ℕ × Option Bool, Fig2.T p ε' hε' hε'p hp1, .i,
    Fig2.φ, Fig2.doesα, Fig2.proper _ _ _,
    PPS.lemma_4_3a (Fig2.deterministic _ _ _) _, (Fig2.cprob_φ _ _ _).ge, ?_⟩
  rw [Fig2.cprob_threshold]
  exact min_le_left _ _

end Podc.ProbablyApproxKnowing
