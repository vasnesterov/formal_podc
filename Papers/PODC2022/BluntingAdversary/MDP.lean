import Mathlib

/-!
# Finite-horizon games against a strong adversary

A small generic layer used to define "the probability that a program reaches a set of
outcomes" (paper: `Prob[P(O) → B]`, Section 2.4) as the value of a game between a
full-information (strong) adversary and the random choices of the system.

* `MDP Q S`: in every state `s`, every process `q : Q` has one `Move`: none (`stop`), a
  deterministic step, or a step that picks one of `m + 1` successors uniformly at random.
* `MDP.val pay n s`: the optimal expected payoff with at most `n` steps (the adversary picks the
  process that moves; a run that has not terminated after `n` steps pays `0`; a terminal state
  pays `pay s`).
* `MDP.opt pay s = ⨆ n, val pay n s`: the optimal expected payoff of a terminating run. Since
  the adversary sees the whole state, this is the supremum over all (history-dependent) strong
  adversaries; `MDP.valS σ` is the value of a fixed positional adversary `σ`.

Main tools: `val_le_of_super` (a *supersolution* bounds the value), `opt_det`, `opt_rand`
(lower bounds along the adversary's moves), `opt_add_le`, `opt_mono`.
-/

set_option linter.unusedSectionVars false

-- CSLib candidate (generic infrastructure for randomized programs over shared objects)
namespace Podc.BluntingAdversary

/-- A move of a process: none, deterministic, or uniform over `m + 1` successors. -/
inductive Move (S : Type*) where
  | stop
  | det (s : S)
  | rand (m : ℕ) (g : Fin (m + 1) → S)

namespace Move

variable {S : Type*}

/-- Expected value of `v` after the move (`0` for `stop`). -/
noncomputable def ev (v : S → ℝ) : Move S → ℝ
  | stop => 0
  | det s => v s
  | rand m g => (∑ i, v (g i)) / (m + 1)

@[simp] lemma ev_stop (v : S → ℝ) : (stop : Move S).ev v = 0 := rfl
@[simp] lemma ev_det (v : S → ℝ) (s : S) : (det s).ev v = v s := rfl
@[simp] lemma ev_rand (v : S → ℝ) (m : ℕ) (g : Fin (m + 1) → S) :
    (rand m g).ev v = (∑ i, v (g i)) / (m + 1) := rfl

lemma ev_mono {v w : S → ℝ} (h : ∀ s, v s ≤ w s) (μ : Move S) : μ.ev v ≤ μ.ev w := by
  cases μ with
  | stop => simp
  | det s => exact h s
  | rand m g =>
    simp only [ev_rand]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => h _) (by positivity)

lemma ev_nonneg {v : S → ℝ} (h : ∀ s, 0 ≤ v s) (μ : Move S) : 0 ≤ μ.ev v := by
  cases μ with
  | stop => simp
  | det s => exact h s
  | rand m g => exact div_nonneg (Finset.sum_nonneg fun i _ => h _) (by positivity)

lemma ev_le_one {v : S → ℝ} (h : ∀ s, v s ≤ 1) (μ : Move S) : μ.ev v ≤ 1 := by
  cases μ with
  | stop => simp
  | det s => exact h s
  | rand m g =>
    simp only [ev_rand]
    rw [div_le_one (by positivity)]
    calc ∑ i, v (g i) ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := Finset.sum_le_sum fun i _ => h _
      _ = m + 1 := by simp

lemma ev_add (v w : S → ℝ) (μ : Move S) : μ.ev (fun s => v s + w s) = μ.ev v + μ.ev w := by
  cases μ with
  | stop => simp
  | det s => rfl
  | rand m g => simp [Finset.sum_add_distrib, add_div]

end Move

/-- A game: every process has one move in every state. -/
structure MDP (Q : Type*) (S : Type*) where
  /-- The move of process `q` in state `s`. -/
  move : S → Q → Move S

namespace MDP

open scoped Classical

variable {Q S : Type*} (M : MDP Q S)

/-- No process can move. -/
def Terminal (s : S) : Prop := ∀ q, M.move s q = .stop

/-- Optimal expected payoff within `n` steps (non-terminated runs pay `0`). -/
noncomputable def val (pay : S → ℝ) : ℕ → S → ℝ
  | 0, s => by classical exact if M.Terminal s then pay s else 0
  | n + 1, s => by
    classical exact if M.Terminal s then pay s else ⨆ q, (M.move s q).ev (val pay n)

/-- Optimal expected payoff of a terminating run: `Prob[P → B]` for `pay` the indicator of `B`. -/
noncomputable def opt (pay : S → ℝ) (s : S) : ℝ := ⨆ n, M.val pay n s

/-- Value of the positional adversary `σ` (it always moves process `σ s`). -/
noncomputable def valS (σ : S → Q) (pay : S → ℝ) : ℕ → S → ℝ
  | 0, s => by classical exact if M.Terminal s then pay s else 0
  | n + 1, s => by
    classical exact if M.Terminal s then pay s else (M.move s (σ s)).ev (valS σ pay n)

/-- `s'` is reachable from `s` by deterministic moves. -/
inductive DetReach : S → S → Prop
  | refl (s : S) : DetReach s s
  | step {s s' s'' : S} (q : Q) : M.move s q = .det s' → DetReach s' s'' → DetReach s s''

/-- `s'` is reachable from `s`. -/
inductive Reach : S → S → Prop
  | refl (s : S) : Reach s s
  | det {s s' s'' : S} (q : Q) : M.move s q = .det s' → Reach s' s'' → Reach s s''
  | rand {s s'' : S} (q : Q) (m : ℕ) (g : Fin (m + 1) → S) (i : Fin (m + 1)) :
      M.move s q = .rand m g → Reach (g i) s'' → Reach s s''

variable {M}

lemma DetReach.reach {s s' : S} (h : M.DetReach s s') : M.Reach s s' := by
  induction h with
  | refl => exact .refl _
  | step q h _ ih => exact .det q h ih

lemma DetReach.trans {s s' s'' : S} (h : M.DetReach s s') (h' : M.DetReach s' s'') :
    M.DetReach s s'' := by
  induction h with
  | refl => exact h'
  | step q h _ ih => exact .step q h (ih h')

lemma Reach.trans {s s' s'' : S} (h : M.Reach s s') (h' : M.Reach s' s'') : M.Reach s s'' := by
  induction h with
  | refl => exact h'
  | det q h _ ih => exact .det q h (ih h')
  | rand q m g i h _ ih => exact .rand q m g i h (ih h')

lemma DetReach.single {s s' : S} (q : Q) (h : M.move s q = .det s') : M.DetReach s s' :=
  .step q h (.refl _)

lemma DetReach.snoc {s s' s'' : S} (h : M.DetReach s s') (q : Q) (h' : M.move s' q = .det s'') :
    M.DetReach s s'' := h.trans (.single q h')

lemma not_terminal_of_det {s s' : S} {q : Q} (h : M.move s q = .det s') : ¬ M.Terminal s :=
  fun ht => by simp [ht q] at h

lemma not_terminal_of_rand {s : S} {q : Q} {m : ℕ} {g : Fin (m + 1) → S}
    (h : M.move s q = .rand m g) : ¬ M.Terminal s :=
  fun ht => by simp [ht q] at h

section Values

variable [Finite Q] [Nonempty Q] {pay : S → ℝ}

lemma bddAbove_ev (v : S → ℝ) (s : S) : BddAbove (Set.range fun q => (M.move s q).ev v) :=
  (Set.finite_range _).bddAbove

@[simp] lemma val_zero (s : S) :
    M.val pay 0 s = if M.Terminal s then pay s else 0 := by
  classical simp [val]

lemma val_succ (n : ℕ) (s : S) :
    M.val pay (n + 1) s = if M.Terminal s then pay s else ⨆ q, (M.move s q).ev (M.val pay n) := by
  classical simp [val]

lemma val_of_terminal {s : S} (h : M.Terminal s) (n : ℕ) : M.val pay n s = pay s := by
  cases n <;> simp [val_succ, h]

lemma val_succ_of_not_terminal {s : S} (h : ¬ M.Terminal s) (n : ℕ) :
    M.val pay (n + 1) s = ⨆ q, (M.move s q).ev (M.val pay n) := by
  simp [val_succ, h]

lemma ev_le_val_succ {s : S} (q : Q) (n : ℕ) (h : ¬ M.Terminal s) :
    (M.move s q).ev (M.val pay n) ≤ M.val pay (n + 1) s := by
  rw [val_succ_of_not_terminal h]
  exact le_ciSup (bddAbove_ev _ _) q

lemma val_nonneg (hp : ∀ s, 0 ≤ pay s) : ∀ n s, 0 ≤ M.val pay n s
  | 0, s => by simp only [val_zero]; split_ifs <;> simp [hp]
  | n + 1, s => by
    rw [val_succ]; split_ifs with h
    · exact hp s
    · exact (Move.ev_nonneg (val_nonneg hp n) _).trans
        (le_ciSup (bddAbove_ev _ _) (Classical.arbitrary Q))

lemma val_le_one (hp : ∀ s, pay s ≤ 1) : ∀ n s, M.val pay n s ≤ 1
  | 0, s => by simp only [val_zero]; split_ifs <;> simp [hp]
  | n + 1, s => by
    rw [val_succ]; split_ifs with h
    · exact hp s
    · exact ciSup_le fun q => Move.ev_le_one (val_le_one hp n) _

lemma val_le_succ (hp : ∀ s, 0 ≤ pay s) : ∀ n s, M.val pay n s ≤ M.val pay (n + 1) s
  | 0, s => by
    by_cases h : M.Terminal s
    · simp [val_of_terminal h]
    · simp only [val_zero, h, ite_false]; exact val_nonneg hp 1 s
  | n + 1, s => by
    by_cases h : M.Terminal s
    · simp [val_of_terminal h]
    · rw [val_succ_of_not_terminal h, val_succ_of_not_terminal h]
      exact ciSup_le fun q => (Move.ev_mono (val_le_succ hp n) _).trans
        (le_ciSup (bddAbove_ev _ _) q)

lemma val_monotone (hp : ∀ s, 0 ≤ pay s) (s : S) : Monotone fun n => M.val pay n s :=
  monotone_nat_of_le_succ fun n => val_le_succ hp n s

lemma bddAbove_val (hp1 : ∀ s, pay s ≤ 1) (s : S) : BddAbove (Set.range fun n => M.val pay n s) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; exact val_le_one hp1 n s⟩

lemma val_le_opt (hp1 : ∀ s, pay s ≤ 1) (n : ℕ) (s : S) : M.val pay n s ≤ M.opt pay s :=
  le_ciSup (bddAbove_val hp1 s) n

lemma opt_nonneg (hp : ∀ s, 0 ≤ pay s) (s : S) : 0 ≤ M.opt pay s := by
  by_cases h : BddAbove (Set.range fun n => M.val pay n s)
  · exact (val_nonneg hp 0 s).trans (le_ciSup h 0)
  · simp [opt, Real.iSup_of_not_bddAbove h]

lemma opt_le_one (hp : ∀ s, 0 ≤ pay s) (hp1 : ∀ s, pay s ≤ 1) (s : S) : M.opt pay s ≤ 1 :=
  ciSup_le fun n => val_le_one hp1 n s

lemma tendsto_val (hp : ∀ s, 0 ≤ pay s) (hp1 : ∀ s, pay s ≤ 1) (s : S) :
    Filter.Tendsto (fun n => M.val pay n s) Filter.atTop (nhds (M.opt pay s)) :=
  tendsto_atTop_ciSup (val_monotone hp s) (bddAbove_val hp1 s)

lemma opt_of_terminal {s : S} (h : M.Terminal s) : M.opt pay s = pay s := by
  simp [opt, val_of_terminal h]

/-- **Supersolutions bound the value.** If a relation `R s x` ("`x` is an admissible upper bound
at `s`") is nonnegative, dominates the payoff at terminal states, and is preserved by every
move in expectation, then it bounds the optimal value. -/
theorem val_le_of_super (R : S → ℝ → Prop) (hnn : ∀ s x, R s x → 0 ≤ x)
    (hterm : ∀ s x, R s x → M.Terminal s → pay s ≤ x)
    (hdet : ∀ s x q s', R s x → M.move s q = .det s' → ∃ x', x' ≤ x ∧ R s' x')
    (hrand : ∀ s x q m (g : Fin (m + 1) → S), R s x → M.move s q = .rand m g →
      ∃ xs : Fin (m + 1) → ℝ, (∑ i, xs i) / (m + 1) ≤ x ∧ ∀ i, R (g i) (xs i)) :
    ∀ n s x, R s x → M.val pay n s ≤ x := by
  intro n
  induction n with
  | zero =>
    intro s x h
    simp only [val_zero]; split_ifs with ht
    · exact hterm s x h ht
    · exact hnn s x h
  | succ n ih =>
    intro s x h
    rw [val_succ]; split_ifs with ht
    · exact hterm s x h ht
    · refine ciSup_le fun q => ?_
      cases hm : M.move s q with
      | stop => simpa using hnn s x h
      | det s' =>
        obtain ⟨x', hx', h'⟩ := hdet s x q s' h hm
        exact (ih s' x' h').trans hx'
      | rand m g =>
        obtain ⟨xs, hxs, h'⟩ := hrand s x q m g h hm
        simp only [Move.ev_rand]
        exact (div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => ih _ _ (h' i))
          (by positivity)).trans hxs

theorem opt_le_of_super (R : S → ℝ → Prop) (hnn : ∀ s x, R s x → 0 ≤ x)
    (hterm : ∀ s x, R s x → M.Terminal s → pay s ≤ x)
    (hdet : ∀ s x q s', R s x → M.move s q = .det s' → ∃ x', x' ≤ x ∧ R s' x')
    (hrand : ∀ s x q m (g : Fin (m + 1) → S), R s x → M.move s q = .rand m g →
      ∃ xs : Fin (m + 1) → ℝ, (∑ i, xs i) / (m + 1) ≤ x ∧ ∀ i, R (g i) (xs i))
    {s : S} {x : ℝ} (h : R s x) : M.opt pay s ≤ x := by
  by_cases hb : BddAbove (Set.range fun n => M.val pay n s)
  · exact ciSup_le fun n => val_le_of_super R hnn hterm hdet hrand n s x h
  · simp only [opt, Real.iSup_of_not_bddAbove hb]; exact hnn s x h

variable (hp : ∀ s, 0 ≤ pay s) (hp1 : ∀ s, pay s ≤ 1)
include hp hp1

/-- The adversary may take a deterministic move. -/
lemma opt_det {s s' : S} {q : Q} (h : M.move s q = .det s') : M.opt pay s' ≤ M.opt pay s := by
  refine ciSup_le fun n => ?_
  calc M.val pay n s' = (M.move s q).ev (M.val pay n) := by rw [h]; rfl
    _ ≤ M.val pay (n + 1) s := ev_le_val_succ q n (not_terminal_of_det h)
    _ ≤ M.opt pay s := val_le_opt hp1 _ _

lemma opt_detReach {s s' : S} (h : M.DetReach s s') : M.opt pay s' ≤ M.opt pay s := by
  induction h with
  | refl => exact le_rfl
  | step q h _ ih => exact ih.trans (opt_det hp hp1 h)

/-- The adversary may take a random move. -/
lemma opt_rand {s : S} {q : Q} {m : ℕ} {g : Fin (m + 1) → S} (h : M.move s q = .rand m g) :
    (∑ i, M.opt pay (g i)) / (m + 1) ≤ M.opt pay s := by
  have hlim : Filter.Tendsto (fun n => (∑ i, M.val pay n (g i)) / (m + 1)) Filter.atTop
      (nhds ((∑ i, M.opt pay (g i)) / (m + 1))) :=
    (tendsto_finsetSum _ fun i _ => tendsto_val hp hp1 (g i)).div_const _
  refine le_of_tendsto' hlim fun n => ?_
  calc (∑ i, M.val pay n (g i)) / (m + 1) = (M.move s q).ev (M.val pay n) := by rw [h]; rfl
    _ ≤ M.val pay (n + 1) s := ev_le_val_succ q n (not_terminal_of_rand h)
    _ ≤ M.opt pay s := val_le_opt hp1 _ _

omit hp hp1 in
/-- Subadditivity in the payoff (the adversary cannot do better on a sum than on each summand
separately). -/
lemma opt_add_le {pay₁ pay₂ : S → ℝ} (h₁ : ∀ s, 0 ≤ pay₁ s) (h₁' : ∀ s, pay₁ s ≤ 1)
    (h₂ : ∀ s, 0 ≤ pay₂ s) (h₂' : ∀ s, pay₂ s ≤ 1) (hle : ∀ s, pay s ≤ pay₁ s + pay₂ s) (s : S) :
    M.opt pay s ≤ M.opt pay₁ s + M.opt pay₂ s := by
  refine opt_le_of_super (fun s x => x = M.opt pay₁ s + M.opt pay₂ s) ?_ ?_ ?_ ?_ rfl
  · rintro s x rfl; exact add_nonneg (opt_nonneg h₁ s) (opt_nonneg h₂ s)
  · rintro s x rfl ht; rw [opt_of_terminal ht, opt_of_terminal ht]; exact hle s
  · rintro s x q s' rfl hm
    exact ⟨_, add_le_add (opt_det h₁ h₁' hm) (opt_det h₂ h₂' hm), rfl⟩
  · rintro s x q m g rfl hm
    refine ⟨fun i => M.opt pay₁ (g i) + M.opt pay₂ (g i), ?_, fun i => rfl⟩
    rw [Finset.sum_add_distrib, add_div]
    exact add_le_add (opt_rand h₁ h₁' hm) (opt_rand h₂ h₂' hm)

omit hp hp1 in
lemma opt_mono {pay₁ : S → ℝ} (h₁ : ∀ s, 0 ≤ pay₁ s) (h₁' : ∀ s, pay₁ s ≤ 1)
    (hle : ∀ s, pay s ≤ pay₁ s) (s : S) : M.opt pay s ≤ M.opt pay₁ s := by
  have := opt_add_le (M := M) (pay := pay) (pay₂ := fun _ => (0 : ℝ)) h₁ h₁' (fun _ => le_rfl)
    (fun _ => zero_le_one) (fun s => by simpa using hle s) s
  have h0 : M.opt (fun _ => (0 : ℝ)) s = 0 := by
    refine le_antisymm ?_ (opt_nonneg (fun _ => le_rfl) s)
    exact opt_le_of_super (pay := fun _ => (0 : ℝ)) (fun _ x => x = 0) (by simp) (by simp)
      (by rintro s x q s' rfl -; exact ⟨0, le_rfl, rfl⟩)
      (by rintro s x q m g rfl -; exact ⟨fun _ => 0, by simp, fun _ => rfl⟩) rfl
  linarith

end Values

end MDP

end Podc.BluntingAdversary
