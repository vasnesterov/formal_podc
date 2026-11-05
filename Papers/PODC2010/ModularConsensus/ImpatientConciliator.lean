import Papers.PODC2010.ModularConsensus.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Log

/-!
# Procedure ImpatientFirstMoverConciliator (Section 5.2, Theorem 7 of Aspnes, PODC 2010)

J. Aspnes, *A modular approach to shared-memory consensus, with applications to the
probabilistic-write model*, PODC 2010.

```
shared data: register r, initially ⊥
procedure ImpatientFirstMoverConciliator(v)
1  k ← 0
2  while r = ⊥ do
3     write v to r with probability 2^k / (2n)
4     k ← k + 1
5  end
6  return (adopt, r)
```

## Model

* `n` processes `Fin n`, process `p` has input `inp p : V` (any type of values).
* One multi-writer register `reg : Option V` (`none` = ⊥). Every scheduled step of a process is
  one register operation: either the loop test (a read of `r`) or the probabilistic write.
* **Probabilistic writes** (the model of Section 2): the `k`-th write attempt (`k = 0, 1, …`) of a
  process takes effect with probability `attemptProb n k = min 1 (2^k / (2n))`; the coin is flipped
  atomically with the write step, *after* the adversary has scheduled it.
* **Adversary**: adaptive and full-information about the past. An `Adversary` is an arbitrary
  function of the history (the list of scheduled processes with the outcomes of their coins) and
  of the current configuration; it returns the process to schedule next, or `none` (an idle
  step: this lets the adversary stop, i.e. crash, any set of processes). It cannot see coins that
  have not been flipped yet, because those do not exist yet: the execution is the probability
  distribution `run inp adv N h c : PMF _` obtained by iterating "the adversary chooses `p`, then
  `p`'s coin is flipped (if `p` is about to write), then `p` takes its step" for `N` steps. This
  adversary is at least as strong as the paper's (location-oblivious adversary, which can see
  memory and pending operations but cannot base the scheduling of a probabilistic write on the
  outcome of its coin).
* Probabilities are those of `PMF` (Mathlib), as `ℝ≥0∞`-valued outer measures.

## Main results

* `agreement_prob` — **Theorem 7, probabilistic agreement**: for every adversary and every
  number of steps `N`, the processes that have returned agree with probability at least
  `(1 - e^{-1/4}) / 4`.
* `individual_work` — **Theorem 7, individual work**: in every execution each process performs
  at most `2⌈lg n⌉ + 5` register operations (and returns if it performed that many);
  `attempts_le` — at most `⌈lg n⌉ + 2` loop iterations.
* `expected_total_work` — **Theorem 7, expected total work `O(n)`**: at most `7n` (expected
  number of register operations of all processes, for every adversary and every `N`).
* `validity`, `coherence` — **Theorem 7**, validity and coherence (with the predicates of
  `Papers.PODC2010.ModularConsensus.Basic`).
* `attempts_tight` — the bound `⌈lg n⌉ + 2` on the number of loop iterations is attained
  (`n = 1`), so the sentence "the loop is never executed for more than `⌈lg n⌉ + 1` iterations"
  of the paper is off by one (its final bound `2⌈lg 2n⌉ + 3 = 2⌈lg n⌉ + 5` is correct and also
  attained).
* `disagreement_possible` — non-vacuity: for `n = 2` some adversary produces disagreement with
  positive probability.

## Proof method

Instead of the paper's argument on the "all-failures path", we use a potential function
(a submartingale) `Φ` on configurations: as long as `r = ⊥`, `Φ = g(S)` with
`S = ∑ (probabilities of all failed attempts)` and `g(S) = (1 - e^{min(S, 1/4) - 1/4}) / 4`;
once `r ≠ ⊥`, `Φ = ∏_{p about to write} (1 - P[p's pending write succeeds])` as long as every
returned value equals the content of `r` (and `0` otherwise). `Φ ≤ 1[agreement]`,
`Φ(initial) = (1 - e^{-1/4})/4`, and every step does not decrease `Φ` in expectation
(`Φ_step`), so `P[agreement after N steps] ≥ E[Φ] ≥ Φ(initial)` (`Φ_le_run`). This avoids the
paper's case distinctions (the index `t` may not exist, the execution may stop early).
The paper's estimates appear in the step where the first write succeeds:
`attemptProb_le_sum` (`2^k/(2n) = 1/(2n) + ∑_{j<k} 2^j/(2n)`, valid also with the `min 1` cap)
and `one_sub_sum_le_prod` (union bound). Expected total work uses the potential
`Ψ = (operations so far) + (credits 3/2/1/0 per process) + 4n·[r = ⊥]` (`Ψ_step`), using that every
write attempt succeeds with probability `≥ 1/(2n)` (`attemptProb_ge`).
-/

namespace Podc.ModularConsensus.Impatient

open scoped ENNReal NNReal
open Finset

variable {n : ℕ} {V : Type}

/-! ### Attempt probabilities and coins -/

/-- The probability `min 1 (2^k / (2n))` that the `k`-th write attempt (counted from `0`) of a
process takes effect. -/
noncomputable def attemptProb (n k : ℕ) : ℝ≥0 := min 1 ((2 : ℝ≥0) ^ k / (2 * (n : ℝ≥0)))

lemma attemptProb_le_one (n k : ℕ) : attemptProb n k ≤ 1 := min_le_left _ _

lemma coe_attemptProb (n k : ℕ) :
    (attemptProb n k : ℝ) = min 1 ((2 : ℝ) ^ k / (2 * (n : ℝ))) := by
  unfold attemptProb; push_cast; rfl

lemma attemptProb_nonneg (n k : ℕ) : (0 : ℝ) ≤ attemptProb n k := NNReal.coe_nonneg _

lemma attemptProb_le_one' (n k : ℕ) : (attemptProb n k : ℝ) ≤ 1 := by
  exact_mod_cast attemptProb_le_one n k

/-- The attempt with index `⌈lg n⌉ + 1 = ⌈lg 2n⌉` succeeds with probability `1`. -/
lemma attemptProb_clog (hn : 0 < n) : attemptProb n (Nat.clog 2 n + 1) = 1 := by
  unfold attemptProb
  refine min_eq_left ?_
  have h : 2 * n ≤ 2 ^ (Nat.clog 2 n + 1) := by
    rw [pow_succ, mul_comm (2 ^ _)]
    exact Nat.mul_le_mul_left 2 (Nat.le_pow_clog (b := 2) (by norm_num) n)
  have hpos : (0 : ℝ≥0) < 2 * (n : ℝ≥0) := by positivity
  rw [le_div_iff₀ hpos, one_mul]
  exact_mod_cast h

/-- The key estimate of the proof of Theorem 7: `2^k/(2n) = 1/(2n) + ∑_{j<k} 2^j/(2n)`; with the
`min 1` cap it becomes an inequality. -/
lemma attemptProb_le_sum (n k : ℕ) :
    (attemptProb n k : ℝ) ≤ 1 / (2 * (n : ℝ)) + ∑ j ∈ range k, (attemptProb n j : ℝ) := by
  induction k with
  | zero =>
    simp only [coe_attemptProb, pow_zero, range_zero, sum_empty, add_zero]
    exact min_le_right _ _
  | succ k ih =>
    have h2 : (attemptProb n (k + 1) : ℝ) ≤ 2 * attemptProb n k := by
      rw [coe_attemptProb, coe_attemptProb]
      have : (2 : ℝ) ^ (k + 1) / (2 * (n : ℝ)) = 2 * (2 ^ k / (2 * (n : ℝ))) := by
        rw [pow_succ]; ring
      rw [this]
      rcases le_total ((2 : ℝ) ^ k / (2 * (n : ℝ))) 1 with h | h
      · rw [min_eq_right h]; exact min_le_right _ _
      · rw [min_eq_left h]; linarith [min_le_left (1 : ℝ) (2 * (2 ^ k / (2 * (n : ℝ))))]
    rw [sum_range_succ]
    linarith

/-- A Bernoulli coin that shows `true` with probability `x`. -/
noncomputable def coin (x : ℝ≥0) (hx : x ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => ((cond b x (1 - x) : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool]
    simp only [Bool.cond_true, Bool.cond_false]
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le hx, ENNReal.coe_one])

@[simp] lemma coin_true (x : ℝ≥0) (hx : x ≤ 1) : coin x hx true = x := by simp [coin]

@[simp] lemma coin_false (x : ℝ≥0) (hx : x ≤ 1) : coin x hx false = ((1 - x : ℝ≥0) : ℝ≥0∞) := by
  simp [coin]

/-! ### Configurations, steps, executions -/

/-- The program counter of a process. -/
inductive PC (V : Type) where
  /-- about to execute the loop test `r = ⊥` (a read of `r`) -/
  | test
  /-- about to execute the probabilistic write of line 3 -/
  | write
  /-- returned `(adopt, v)` -/
  | done (v : V)

/-- Is the process about to write? -/
def PC.isWrite : PC V → Bool
  | .write => true
  | _ => false

@[simp] lemma PC.isWrite_test : (PC.test : PC V).isWrite = false := rfl
@[simp] lemma PC.isWrite_write : (PC.write : PC V).isWrite = true := rfl
@[simp] lemma PC.isWrite_done (v : V) : (PC.done v).isWrite = false := rfl

/-- Register operations performed so far, beyond the `2k` of the completed loop iterations. -/
def PC.cost : PC V → ℕ
  | .test => 0
  | .write => 1
  | .done _ => 1

/-- A configuration: the register `r`, and for every process its program counter, its attempt
counter `k`, and the number of register operations it has performed. -/
structure Config (n : ℕ) (V : Type) where
  /-- the register `r` (`none` = ⊥) -/
  reg : Option V
  /-- program counters -/
  pc : Fin n → PC V
  /-- the local variable `k` (number of write attempts made) -/
  att : Fin n → ℕ
  /-- number of register operations performed (individual work) -/
  ops : Fin n → ℕ

/-- The initial configuration. -/
def Config.init : Config n V := ⟨none, fun _ => .test, fun _ => 0, fun _ => 0⟩

/-- The step of process `p`; `b` is the outcome of its coin (used only by a write step). -/
def Config.next (inp : Fin n → V) (c : Config n V) (p : Fin n) (b : Bool) : Config n V :=
  match c.pc p with
  | .test =>
    match c.reg with
    | none => { c with pc := Function.update c.pc p .write,
                       ops := Function.update c.ops p (c.ops p + 1) }
    | some v => { c with pc := Function.update c.pc p (.done v),
                         ops := Function.update c.ops p (c.ops p + 1) }
  | .write =>
    { reg := if b then some (inp p) else c.reg
      pc := Function.update c.pc p .test
      att := Function.update c.att p (c.att p + 1)
      ops := Function.update c.ops p (c.ops p + 1) }
  | .done _ => c

/-- The coin flipped when `p` is scheduled: a coin with bias `attemptProb n k` for the `k`-th
write attempt; a dummy coin (always `false`) for a read or for a returned process. -/
noncomputable def coinFor (c : Config n V) (p : Fin n) : PMF Bool :=
  match c.pc p with
  | .write => coin (attemptProb n (c.att p)) (attemptProb_le_one n _)
  | _ => PMF.pure false

/-- Histories: the scheduled processes with the outcomes of their coins, latest first. -/
abbrev History (n : ℕ) := List (Fin n × Bool)

/-- An adaptive, full-information adversary: given the history and the current configuration,
it chooses the next process to take a step (`none`: idle step). -/
def Adversary (n : ℕ) (V : Type) := History n → Config n V → Option (Fin n)

/-- The distribution of (history, configuration) after `N` scheduling decisions of `adv`,
starting from history `h` and configuration `c`. -/
noncomputable def run (inp : Fin n → V) (adv : Adversary n V) :
    ℕ → History n → Config n V → PMF (History n × Config n V)
  | 0, h, c => PMF.pure (h, c)
  | N + 1, h, c =>
    match adv h c with
    | none => run inp adv N h c
    | some p => (coinFor c p).bind fun b => run inp adv N ((p, b) :: h) (c.next inp p b)

/-- The output of process `p` in configuration `c`: `(adopt, v)` once it returned `v`. -/
def output (c : Config n V) (p : Fin n) : Option (Decision × V) :=
  match c.pc p with
  | .done v => some (.adopt, v)
  | _ => none

/-! ### Basic facts about steps -/

section Steps

variable (inp : Fin n → V) (c : Config n V) (p : Fin n) (b : Bool)

lemma next_test_none (h1 : c.pc p = .test) (h2 : c.reg = none) :
    c.next inp p b = { c with pc := Function.update c.pc p .write,
                              ops := Function.update c.ops p (c.ops p + 1) } := by
  simp [Config.next, h1, h2]

lemma next_test_some {v : V} (h1 : c.pc p = .test) (h2 : c.reg = some v) :
    c.next inp p b = { c with pc := Function.update c.pc p (.done v),
                              ops := Function.update c.ops p (c.ops p + 1) } := by
  simp [Config.next, h1, h2]

lemma next_write (h1 : c.pc p = .write) :
    c.next inp p b = { reg := if b then some (inp p) else c.reg
                       pc := Function.update c.pc p .test
                       att := Function.update c.att p (c.att p + 1)
                       ops := Function.update c.ops p (c.ops p + 1) } := by
  simp [Config.next, h1]

lemma next_done {v : V} (h1 : c.pc p = .done v) : c.next inp p b = c := by
  simp [Config.next, h1]

lemma coinFor_write (h1 : c.pc p = .write) :
    coinFor c p = coin (attemptProb n (c.att p)) (attemptProb_le_one n _) := by
  simp [coinFor, h1]

lemma coinFor_not_write (h1 : (c.pc p).isWrite = false) : coinFor c p = PMF.pure false := by
  unfold coinFor
  split
  · next h => rw [h] at h1; simp [PC.isWrite] at h1
  · rfl

end Steps

/-! ### Potential function -/

/-- Every returned value equals the content of `r`. -/
def Consistent (c : Config n V) : Prop := ∀ p v, c.pc p = .done v → c.reg = some v

/-- Sum of the probabilities of all write attempts made so far. -/
noncomputable def sumProb (c : Config n V) : ℝ :=
  ∑ p, ∑ j ∈ range (c.att p), (attemptProb n j : ℝ)

/-- Lower bound on the agreement probability while `r = ⊥`, as a function of `sumProb`. -/
noncomputable def g (x : ℝ) : ℝ := (1 - Real.exp (min x (1 / 4) - 1 / 4)) / 4

/-- Probability that none of the pending writes succeeds. -/
noncomputable def wprod (c : Config n V) : ℝ :=
  ∏ r ∈ univ.filter (fun r => (c.pc r).isWrite = true), (1 - (attemptProb n (c.att r) : ℝ))

open Classical in
/-- The potential function. -/
noncomputable def Φ (c : Config n V) : ℝ :=
  if Consistent c then (if c.reg = none then g (sumProb c) else wprod c) else 0

lemma g_nonneg (x : ℝ) : 0 ≤ g x := by
  unfold g
  have : Real.exp (min x (1 / 4) - 1 / 4) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith [min_le_right x (1 / 4)])
  linarith

lemma g_le (x : ℝ) : g x ≤ 1 / 4 := by
  unfold g; linarith [Real.exp_pos (min x (1 / 4) - 1 / 4)]

lemma g_of_le {x : ℝ} (hx : 1 / 4 ≤ x) : g x = 0 := by
  unfold g; rw [min_eq_right hx]; simp

/-- The analytic heart of the bound `P[no success among the first t attempts] ≤ e^{-1/4}`. -/
lemma g_step (S x : ℝ) (hx0 : 0 ≤ x) :
    g S ≤ x * (1 / 4) + (1 - x) * g (S + x) := by
  have hm : min (S + x) (1 / 4) ≤ min S (1 / 4) + x := by
    rw [← min_add_add_right]; exact min_le_min le_rfl (by linarith)
  have h2 : (1 - x) * Real.exp (min (S + x) (1 / 4) - 1 / 4) ≤
      Real.exp (min S (1 / 4) - 1 / 4) := by
    calc (1 - x) * Real.exp (min (S + x) (1 / 4) - 1 / 4)
        ≤ Real.exp (-x) * Real.exp (min S (1 / 4) + x - 1 / 4) :=
          mul_le_mul (Real.one_sub_le_exp_neg x) (Real.exp_le_exp.2 (by linarith))
            (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (min S (1 / 4) - 1 / 4) := by rw [← Real.exp_add]; ring_nf
  unfold g
  nlinarith

-- CSLib candidate
lemma one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ 1) : 1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have hfa0 := h0 a (mem_insert_self a s)
    have hfa1 := h1 a (mem_insert_self a s)
    have hs : 0 ≤ ∑ i ∈ s, f i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    nlinarith

lemma wprod_nonneg (c : Config n V) : 0 ≤ wprod c :=
  prod_nonneg fun r _ => by linarith [attemptProb_le_one' n (c.att r)]

lemma wprod_le_one (c : Config n V) : wprod c ≤ 1 :=
  prod_le_one₀ (fun r _ => by linarith [attemptProb_le_one' n (c.att r)])
    (fun r _ => by linarith [attemptProb_nonneg n (c.att r)])

lemma Φ_nonneg (c : Config n V) : 0 ≤ Φ c := by
  unfold Φ; split_ifs
  · exact g_nonneg _
  · exact wprod_nonneg c
  · exact le_rfl

lemma Φ_le_one (c : Config n V) : Φ c ≤ 1 := by
  unfold Φ; split_ifs
  · linarith [g_le (sumProb c)]
  · exact wprod_le_one c
  · norm_num

lemma agreement_of_consistent {c : Config n V} (h : Consistent c) : Agreement (output c) := by
  intro p q d e v w hp hq
  unfold output at hp hq
  cases h1 : c.pc p <;> rw [h1] at hp <;> simp at hp
  cases h2 : c.pc q <;> rw [h2] at hq <;> simp at hq
  obtain ⟨-, rfl⟩ := hp
  obtain ⟨-, rfl⟩ := hq
  have e1 := h _ _ h1
  rw [h _ _ h2] at e1
  exact (Option.some.inj e1).symm

lemma consistent_of_Φ_ne_zero {c : Config n V} (h : Φ c ≠ 0) : Consistent c := by
  by_contra hc; exact h (by simp [Φ, hc])

/-! ### The potential does not decrease in expectation -/

section PotentialSteps

variable (inp : Fin n → V)

/-- The writer set after a write step of `p` loses `p`. -/
lemma pc_next_write_done {c : Config n V} {p : Fin n} (h1 : c.pc p = .write) {b : Bool}
    {r : Fin n} {v : V} (hr : (c.next inp p b).pc r = .done v) : r ≠ p ∧ c.pc r = .done v := by
  rw [next_write inp c p b h1] at hr
  by_cases hrp : r = p
  · subst hrp; simp at hr
  · exact ⟨hrp, by simpa [Function.update_of_ne hrp] using hr⟩

lemma consistent_next_false {c : Config n V} {p : Fin n} (h1 : c.pc p = .write)
    (hc : Consistent c) : Consistent (c.next inp p false) := by
  intro r v hr
  have := hc r v (pc_next_write_done inp h1 hr).2
  rw [next_write inp c p false h1]; simpa using this

lemma consistent_next_true {c : Config n V} {p : Fin n} (h1 : c.pc p = .write)
    (hc : Consistent c) (hreg : c.reg = none) : Consistent (c.next inp p true) := by
  intro r v hr
  have := hc r v (pc_next_write_done inp h1 hr).2
  rw [hreg] at this; exact absurd this (by simp)

lemma sumProb_next_write {c : Config n V} {p : Fin n} (h1 : c.pc p = .write) (b : Bool) :
    sumProb (c.next inp p b) = sumProb c + attemptProb n (c.att p) := by
  rw [next_write inp c p b h1]
  unfold sumProb
  dsimp only
  rw [← add_sum_erase _ _ (mem_univ p), ← add_sum_erase _ _ (mem_univ p),
    Function.update_self, sum_range_succ]
  have : ∑ x ∈ univ.erase p, ∑ j ∈ range (Function.update c.att p (c.att p + 1) x),
      (attemptProb n j : ℝ) = ∑ x ∈ univ.erase p, ∑ j ∈ range (c.att x), (attemptProb n j : ℝ) :=
    sum_congr rfl fun r hr => by rw [Function.update_of_ne (ne_of_mem_erase hr)]
  rw [this]; ring

/-- The pending writers other than `p`. -/
def others (c : Config n V) (p : Fin n) : Finset (Fin n) :=
  (univ.filter fun r => (c.pc r).isWrite = true).erase p

lemma wprod_next_write {c : Config n V} {p : Fin n} (h1 : c.pc p = .write) (b : Bool) :
    wprod (c.next inp p b) = ∏ r ∈ others c p, (1 - (attemptProb n (c.att r) : ℝ)) := by
  rw [next_write inp c p b h1]
  unfold wprod others
  have hs : (univ.filter fun r => (Function.update c.pc p PC.test r).isWrite = true) =
      (univ.filter fun r => (c.pc r).isWrite = true).erase p := by
    ext r
    by_cases hr : r = p
    · subst hr; simp
    · simp [hr]
  simp only
  rw [hs]
  exact prod_congr rfl fun r hr => by rw [Function.update_of_ne (ne_of_mem_erase hr)]

lemma wprod_eq_mul {c : Config n V} {p : Fin n} (h1 : c.pc p = .write) :
    wprod c = (1 - (attemptProb n (c.att p) : ℝ)) *
      ∏ r ∈ others c p, (1 - (attemptProb n (c.att r) : ℝ)) :=
  (mul_prod_erase _ (fun r => (1 - (attemptProb n (c.att r) : ℝ))) (by simp [h1])).symm

/-- **The union bound of the proof of Theorem 7**: when the first write (by `p`) succeeds, the
probability that some other pending write succeeds is at most `1/2 + ∑ (probabilities of the
failed attempts)`. -/
lemma one_half_sub_le_prod_others (c : Config n V) (p : Fin n) :
    1 / 2 - sumProb c ≤ ∏ r ∈ others c p, (1 - (attemptProb n (c.att r) : ℝ)) := by
  have hn : (n : ℝ) ≠ 0 := by have := p.pos; positivity
  have hsum : ∑ r ∈ others c p, (attemptProb n (c.att r) : ℝ) ≤ 1 / 2 + sumProb c := by
    calc ∑ r ∈ others c p, (attemptProb n (c.att r) : ℝ)
        ≤ ∑ r ∈ others c p, (1 / (2 * (n : ℝ)) + ∑ j ∈ range (c.att r), (attemptProb n j : ℝ)) :=
          sum_le_sum fun r _ => attemptProb_le_sum n _
      _ ≤ ∑ r, (1 / (2 * (n : ℝ)) + ∑ j ∈ range (c.att r), (attemptProb n j : ℝ)) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ =>
            add_nonneg (by positivity) (sum_nonneg fun j _ => attemptProb_nonneg n j)
      _ = 1 / 2 + sumProb c := by
          rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          unfold sumProb
          field_simp
  have := one_sub_sum_le_prod (others c p) (fun r => (attemptProb n (c.att r) : ℝ))
    (fun r _ => attemptProb_nonneg n _) (fun r _ => attemptProb_le_one' n _)
  linarith

/-- One write step does not decrease `Φ` in expectation. -/
lemma Φ_step_write (c : Config n V) (p : Fin n) (h1 : c.pc p = .write) :
    Φ c ≤ (attemptProb n (c.att p) : ℝ) * Φ (c.next inp p true) +
      (1 - attemptProb n (c.att p)) * Φ (c.next inp p false) := by
  have hx0 := attemptProb_nonneg n (c.att p)
  have hx1 := attemptProb_le_one' n (c.att p)
  have hT := Φ_nonneg (c.next inp p true)
  have hF := Φ_nonneg (c.next inp p false)
  by_cases hc : Consistent c
  swap
  · rw [show Φ c = 0 by simp [Φ, hc]]; nlinarith
  have hcF := consistent_next_false inp h1 hc
  rcases hreg : c.reg with _ | v
  · have hcT := consistent_next_true inp h1 hc hreg
    have hregT : (c.next inp p true).reg = some (inp p) := by rw [next_write inp c p true h1]; simp
    have hregF : (c.next inp p false).reg = none := by rw [next_write inp c p false h1]; simpa
    have eΦ : Φ c = g (sumProb c) := by simp [Φ, hc, hreg]
    have eT : Φ (c.next inp p true) = wprod (c.next inp p true) := by simp [Φ, hcT, hregT]
    have eF : Φ (c.next inp p false) = g (sumProb c + attemptProb n (c.att p)) := by
      simp [Φ, hcF, hregF, sumProb_next_write inp h1]
    rw [eΦ, eT, eF, wprod_next_write inp h1]
    have hP := prod_nonneg fun r (_ : r ∈ others c p) =>
      (by linarith [attemptProb_le_one' n (c.att r)] : (0 : ℝ) ≤ 1 - attemptProb n (c.att r))
    have hg := g_nonneg (sumProb c + attemptProb n (c.att p))
    by_cases hS : sumProb c ≤ 1 / 4
    · have hA := one_half_sub_le_prod_others c p
      have := g_step (sumProb c) _ hx0
      nlinarith
    · rw [g_of_le (by linarith)]; nlinarith
  · have hregF : (c.next inp p false).reg = some v := by rw [next_write inp c p false h1]; simpa
    have eΦ : Φ c = wprod c := by simp [Φ, hc, hreg]
    have eF : Φ (c.next inp p false) = wprod (c.next inp p false) := by simp [Φ, hcF, hregF]
    rw [eΦ, eF, wprod_eq_mul h1, wprod_next_write inp h1]
    nlinarith

/-- A read step (or a step of a returned process) does not decrease `Φ`. -/
lemma Φ_step_read (c : Config n V) (p : Fin n) (hw : (c.pc p).isWrite = false) :
    Φ c ≤ Φ (c.next inp p false) := by
  by_cases hc : Consistent c
  swap
  · rw [show Φ c = 0 by simp [Φ, hc]]; exact Φ_nonneg _
  rcases h1 : c.pc p with _ | _ | v
  · rcases hreg : c.reg with _ | v
    · have e := next_test_none inp c p false h1 hreg
      have hc' : Consistent (c.next inp p false) := by
        intro r w hr
        rw [e] at hr
        by_cases hrp : r = p
        · subst hrp; simp at hr
        · exact absurd (hc r w (by simpa [Function.update_of_ne hrp] using hr)) (by simp [hreg])
      have hreg' : (c.next inp p false).reg = none := by rw [e]; exact hreg
      have hatt : (c.next inp p false).att = c.att := by rw [e]
      simp [Φ, hc, hc', hreg, hreg', sumProb, hatt]
    · have e := next_test_some inp c p false h1 hreg
      have hc' : Consistent (c.next inp p false) := by
        intro r w hr
        rw [e] at hr ⊢
        by_cases hrp : r = p
        · subst hrp; simp at hr; simpa [hr] using hreg
        · exact hc r w (by simpa [Function.update_of_ne hrp] using hr)
      have hreg' : (c.next inp p false).reg = some v := by rw [e]; exact hreg
      have hw' : wprod (c.next inp p false) = wprod c := by
        rw [e]
        unfold wprod
        congr 1
        ext r
        by_cases hrp : r = p
        · subst hrp; simp [h1]
        · simp [Function.update_of_ne hrp]
      simp [Φ, hc, hc', hreg, hreg', hw']
  · rw [h1] at hw; simp at hw
  · rw [next_done inp c p false h1]

/-- `Φ` is a submartingale along every step chosen by the adversary. -/
lemma Φ_step (c : Config n V) (p : Fin n) :
    ENNReal.ofReal (Φ c) ≤ ∑' b, coinFor c p b * ENNReal.ofReal (Φ (c.next inp p b)) := by
  cases hw : (c.pc p).isWrite
  · rw [coinFor_not_write c p hw, tsum_bool]
    simp only [PMF.pure_apply, ite_true, one_mul, Bool.true_eq_false, ite_false, zero_mul,
      add_zero]
    exact ENNReal.ofReal_le_ofReal (Φ_step_read inp c p hw)
  · have h1 : c.pc p = .write := by
      cases h : c.pc p <;> simp_all [PC.isWrite]
    rw [coinFor_write c p h1, tsum_bool, coin_true, coin_false]
    have key := Φ_step_write inp c p h1
    have hx1 := attemptProb_le_one n (c.att p)
    have e : ((1 - attemptProb n (c.att p) : ℝ≥0) : ℝ) = 1 - (attemptProb n (c.att p) : ℝ) := by
      rw [NNReal.coe_sub hx1, NNReal.coe_one]
    calc ENNReal.ofReal (Φ c)
        ≤ ENNReal.ofReal (((1 - attemptProb n (c.att p) : ℝ≥0) : ℝ) * Φ (c.next inp p false) +
            (attemptProb n (c.att p) : ℝ) * Φ (c.next inp p true)) :=
          ENNReal.ofReal_le_ofReal (by rw [e]; linarith)
      _ = _ := by
          rw [ENNReal.ofReal_add (mul_nonneg (NNReal.coe_nonneg _) (Φ_nonneg _))
              (mul_nonneg (NNReal.coe_nonneg _) (Φ_nonneg _)),
            ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_mul (NNReal.coe_nonneg _),
            ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]

end PotentialSteps

/-! ### Theorem 7: probabilistic agreement -/

/-- The event "all processes that have returned returned the same value". -/
def AgreementEvent (n : ℕ) (V : Type) : Set (History n × Config n V) :=
  {s | Agreement (output s.2)}

lemma Φ_le_run (inp : Fin n → V) (adv : Adversary n V) (N : ℕ) :
    ∀ h c, ENNReal.ofReal (Φ c) ≤ (run inp adv N h c).toOuterMeasure (AgreementEvent n V) := by
  induction N with
  | zero =>
    intro h c
    rw [run, PMF.toOuterMeasure_pure_apply]
    split_ifs with hA
    · exact ENNReal.ofReal_le_one.2 (Φ_le_one c)
    · have : Φ c = 0 := by
        by_contra hne
        exact hA (agreement_of_consistent (consistent_of_Φ_ne_zero hne))
      simp [this]
  | succ N ih =>
    intro h c
    rw [run]
    split
    · exact ih h c
    · next p _ =>
      rw [PMF.toOuterMeasure_bind_apply]
      exact (Φ_step inp c p).trans (ENNReal.tsum_le_tsum fun b => by gcongr; exact ih _ _)

lemma Φ_init : Φ (Config.init : Config n V) = (1 - Real.exp (-1 / 4)) / 4 := by
  have hc : Consistent (Config.init : Config n V) := by
    intro p v hp; simp [Config.init] at hp
  have hS : sumProb (Config.init : Config n V) = 0 := by simp [sumProb, Config.init]
  have hr : (Config.init : Config n V).reg = none := rfl
  simp only [Φ, hc, hr, ↓reduceIte, hS, g]
  rw [min_eq_left (by norm_num)]
  ring_nf

/-- **Theorem 7 of [Aspnes 2010], probabilistic agreement.** Against every adaptive adversary
(which sees the whole history, including the outcomes of all coins flipped so far) and for every
number `N` of scheduling steps, with probability at least `(1 - e^{-1/4}) / 4 ≈ 0.0553` all
processes that have returned from ImpatientFirstMoverConciliator returned the same value. -/
theorem agreement_prob (inp : Fin n → V) (adv : Adversary n V) (N : ℕ) :
    ENNReal.ofReal ((1 - Real.exp (-1 / 4)) / 4) ≤
      (run inp adv N [] Config.init).toOuterMeasure {s | Agreement (output s.2)} := by
  rw [← Φ_init (n := n) (V := V)]
  exact Φ_le_run inp adv N [] Config.init

/-! ### Invariants on the support of executions -/

section Support

variable (inp : Fin n → V) (adv : Adversary n V)

/-- Invariants preserved by every possible step hold on the support of every execution. -/
lemma run_support_inv (Pr : Config n V → Prop)
    (hstep : ∀ c p b, Pr c → b ∈ (coinFor c p).support → Pr (c.next inp p b)) :
    ∀ N h c, Pr c → ∀ s ∈ (run inp adv N h c).support, Pr s.2 := by
  intro N
  induction N with
  | zero =>
    intro h c hc s hs
    rw [run, PMF.support_pure, Set.mem_singleton_iff] at hs
    rw [hs]; exact hc
  | succ N ih =>
    intro h c hc s hs
    rw [run] at hs
    split at hs
    · exact ih h c hc s hs
    · next p _ =>
      rw [PMF.mem_support_bind_iff] at hs
      obtain ⟨b, hb, hs⟩ := hs
      exact ih _ _ (hstep c p b hc hb) s hs

lemma mem_support_run_zero (h : History n) (c : Config n V) :
    (h, c) ∈ (run inp adv 0 h c).support := by
  simp [run]

lemma mem_support_run_succ {N : ℕ} {h : History n} {c : Config n V} {p : Fin n} {b : Bool}
    {s : History n × Config n V} (hadv : adv h c = some p) (hb : b ∈ (coinFor c p).support)
    (hs : s ∈ (run inp adv N ((p, b) :: h) (c.next inp p b)).support) :
    s ∈ (run inp adv (N + 1) h c).support := by
  rw [run, hadv]
  exact (PMF.mem_support_bind_iff _ _ _).2 ⟨b, hb, hs⟩

/-- A write attempt with probability `1` succeeds. -/
lemma eq_true_of_mem_support {c : Config n V} {p : Fin n} {b : Bool}
    (hb : b ∈ (coinFor c p).support) (h1 : c.pc p = .write)
    (hq : attemptProb n (c.att p) = 1) : b = true := by
  rw [coinFor_write c p h1, PMF.mem_support_iff] at hb
  cases b
  · simp [hq] at hb
  · rfl

/-- Invariant for the individual-work bound (`m = ⌈lg n⌉`): every process performed
`2k + cost(pc)` operations, `k ≤ m + 2`, a pending write has `k ≤ m + 1`, and `k = m + 2` only
after `r` has been written. -/
def WorkInv (c : Config n V) : Prop :=
  ∀ p, c.ops p = 2 * c.att p + (c.pc p).cost ∧ c.att p ≤ Nat.clog 2 n + 2 ∧
    ((c.pc p).isWrite = true → c.att p ≤ Nat.clog 2 n + 1) ∧
    (c.att p = Nat.clog 2 n + 2 → c.reg ≠ none)

lemma workInv_init : WorkInv (Config.init : Config n V) := by
  intro p; simp [Config.init, PC.cost]

lemma workInv_step (c : Config n V) (p : Fin n) (b : Bool) (hc : WorkInv c)
    (hb : b ∈ (coinFor c p).support) : WorkInv (c.next inp p b) := by
  intro r
  obtain ⟨h1, h2, h3, h4⟩ := hc r
  rcases hpc : c.pc p with _ | _ | v
  · rcases hreg : c.reg with _ | v
    · rw [next_test_none inp c p b hpc hreg]
      by_cases hrp : r = p
      · subst hrp
        obtain ⟨_, _, _, h4p⟩ := hc r
        have : c.att r ≠ Nat.clog 2 n + 2 := fun h => h4p h hreg
        simp only [Function.update_self, PC.isWrite_write, PC.cost, hreg]
        rw [hpc] at h1
        simp only [PC.cost] at h1
        refine ⟨by omega, h2, fun _ => by omega, fun h => absurd h this⟩
      · simpa [Function.update_of_ne hrp] using hc r
    · rw [next_test_some inp c p b hpc hreg]
      by_cases hrp : r = p
      · subst hrp
        rw [hpc] at h1
        simp only [PC.cost] at h1
        simp only [Function.update_self, PC.isWrite_done, PC.cost, hreg]
        refine ⟨by omega, h2, by simp, by simp⟩
      · simpa [Function.update_of_ne hrp] using hc r
  · rw [next_write inp c p b hpc]
    have hregp : c.reg ≠ none → (if b = true then some (inp p) else c.reg) ≠ none := by
      intro h; split <;> simp_all
    by_cases hrp : r = p
    · subst hrp
      rw [hpc] at h1 h3
      simp only [PC.cost, PC.isWrite_write, forall_const] at h1 h3
      simp only [Function.update_self, PC.isWrite_test, PC.cost]
      refine ⟨by omega, by omega, by simp, fun h => ?_⟩
      have hm : c.att r = Nat.clog 2 n + 1 := by omega
      have hb' : b = true :=
        eq_true_of_mem_support hb hpc (by rw [hm]; exact attemptProb_clog r.pos)
      simp [hb']
    · simp only [Function.update_of_ne hrp]
      exact ⟨h1, h2, h3, fun h => hregp (h4 h)⟩
  · rw [next_done inp c p b hpc]; exact hc r

/-- **Theorem 7 of [Aspnes 2010], individual work.** In every execution (every configuration
reachable with positive probability), every process has performed at most `2⌈lg n⌉ + 5`
register operations, and a process that has not returned has performed fewer; i.e. every process
returns after at most `2⌈lg n⌉ + 5` operations. -/
theorem individual_work (N : ℕ) :
    ∀ s ∈ (run inp adv N [] Config.init).support, ∀ p,
      s.2.ops p ≤ 2 * Nat.clog 2 n + 5 ∧
      ((∀ v, s.2.pc p ≠ .done v) → s.2.ops p < 2 * Nat.clog 2 n + 5) := by
  intro s hs p
  obtain ⟨h1, h2, h3, -⟩ :=
    run_support_inv inp adv WorkInv (workInv_step inp) N [] Config.init workInv_init s hs p
  rcases hpc : s.2.pc p with _ | _ | v <;> rw [hpc] at h1 h3 <;> simp [PC.cost] at h1 h3
  · omega
  · omega
  · exact ⟨by omega, fun h => absurd rfl (h v)⟩

/-- The loop of ImpatientFirstMoverConciliator is executed at most `⌈lg n⌉ + 2 = ⌈lg 2n⌉ + 1`
times (the paper says `⌈lg n⌉ + 1`; see `attempts_tight`). -/
theorem attempts_le (N : ℕ) :
    ∀ s ∈ (run inp adv N [] Config.init).support, ∀ p, s.2.att p ≤ Nat.clog 2 n + 2 :=
  fun s hs p =>
    (run_support_inv inp adv WorkInv (workInv_step inp) N [] Config.init workInv_init s hs p).2.1

/-- Invariant for validity. -/
def ValidInv (c : Config n V) : Prop :=
  (∀ v, c.reg = some v → ∃ i, inp i = v) ∧ ∀ p v, c.pc p = .done v → ∃ i, inp i = v

lemma validInv_step (c : Config n V) (p : Fin n) (b : Bool) (hc : ValidInv inp c) :
    ValidInv inp (c.next inp p b) := by
  obtain ⟨hr, hd⟩ := hc
  rcases hpc : c.pc p with _ | _ | v
  · rcases hreg : c.reg with _ | v
    · rw [next_test_none inp c p b hpc hreg]
      refine ⟨hr, fun r w hw => ?_⟩
      by_cases hrp : r = p
      · subst hrp; simp at hw
      · exact hd r w (by simpa [Function.update_of_ne hrp] using hw)
    · rw [next_test_some inp c p b hpc hreg]
      refine ⟨hr, fun r w hw => ?_⟩
      by_cases hrp : r = p
      · subst hrp; simp at hw; exact hr w (hw ▸ hreg)
      · exact hd r w (by simpa [Function.update_of_ne hrp] using hw)
  · rw [next_write inp c p b hpc]
    refine ⟨fun w hw => ?_, fun r w hw => ?_⟩
    · dsimp only at hw
      split at hw
      · exact ⟨p, Option.some.inj hw⟩
      · exact hr w hw
    · by_cases hrp : r = p
      · subst hrp; simp at hw
      · exact hd r w (by simpa [Function.update_of_ne hrp] using hw)
  · rw [next_done inp c p b hpc]; exact ⟨hr, hd⟩

/-- **Theorem 7 of [Aspnes 2010], validity.** Every returned value is some process's input. -/
theorem validity (N : ℕ) :
    ∀ s ∈ (run inp adv N [] Config.init).support,
      Validity (fun p => some (inp p)) (output s.2) := by
  intro s hs p d v hp
  have := run_support_inv inp adv (ValidInv inp) (fun c p b hc _ => validInv_step inp c p b hc)
    N [] Config.init ⟨by simp [Config.init], by simp [Config.init]⟩ s hs
  unfold output at hp
  split at hp
  · next v' hv =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨i, hi⟩ := this.2 p v' hv
    exact ⟨i, by simp [hi, hp.2]⟩
  · simp at hp

/-- **Theorem 7 of [Aspnes 2010], coherence**: vacuous, the procedure always returns `adopt`. -/
theorem coherence (c : Config n V) : Coherence (output c) := by
  intro p q v d w hp
  unfold output at hp
  split at hp <;> simp at hp

end Support

/-! ### Expected total work -/

section Work

variable (inp : Fin n → V) (adv : Adversary n V)

-- CSLib candidate
lemma tsum_bind_mul {α β : Type} (μ : PMF α) (f : α → PMF β) (g : β → ℝ≥0∞) :
    ∑' b, (μ.bind f) b * g b = ∑' a, μ a * ∑' b, f a b * g b := by
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  rw [ENNReal.tsum_comm]

-- CSLib candidate
lemma tsum_pure_mul {β : Type} (x : β) (g : β → ℝ≥0∞) : ∑' b, (PMF.pure x) b * g b = g x := by
  simp [PMF.pure_apply]

/-- Total work: the number of register operations performed by all processes. -/
def totalWork (c : Config n V) : ℕ := ∑ r, c.ops r

/-- Remaining-work credit of a process: while `r = ⊥`, a process about to read may still need
`3` operations before the first successful write; after it, at most `1`. -/
def potW (reg : Option V) : PC V → ℕ
  | .test => if reg.isNone then 3 else 1
  | .write => 2
  | .done _ => 0

/-- Work potential: operations performed plus credits, plus `4n` while `r = ⊥`. -/
def Ψ (c : Config n V) : ℕ :=
  (∑ r, (c.ops r + potW c.reg (c.pc r))) + if c.reg.isNone then 4 * n else 0

lemma totalWork_le_Ψ (c : Config n V) : totalWork c ≤ Ψ c :=
  (sum_le_sum fun _ _ => Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

lemma Ψ_init : Ψ (Config.init : Config n V) = 7 * n := by
  simp [Ψ, Config.init, potW]; ring

lemma potW_le {reg reg' : Option V} (h : reg'.isNone = true → reg.isNone = true) (x : PC V) :
    potW reg' x ≤ potW reg x := by
  cases x <;> simp only [potW, le_refl]
  split_ifs <;> simp_all

lemma sum_le_of_single {F G : Fin n → ℕ} (p : Fin n) (d : ℕ) (hr : ∀ r, r ≠ p → F r ≤ G r)
    (hp : F p ≤ G p + d) : ∑ r, F r ≤ (∑ r, G r) + d := by
  rw [← add_sum_erase _ _ (mem_univ p), ← add_sum_erase _ _ (mem_univ p)]
  have := sum_le_sum fun r (h : r ∈ univ.erase p) => hr r (ne_of_mem_erase h)
  omega

lemma Ψ_le_of_single (c c' : Config n V) (p : Fin n) (hreg : c'.reg = c.reg)
    (hr : ∀ r, r ≠ p → c'.ops r = c.ops r ∧ c'.pc r = c.pc r)
    (hp : c'.ops p + potW c.reg (c'.pc p) ≤ c.ops p + potW c.reg (c.pc p)) : Ψ c' ≤ Ψ c := by
  unfold Ψ
  rw [hreg]
  have := sum_le_of_single (F := fun r => c'.ops r + potW c.reg (c'.pc r))
    (G := fun r => c.ops r + potW c.reg (c.pc r)) p 0
    (fun r hr' => by rw [(hr r hr').1, (hr r hr').2]) (by simpa using hp)
  omega

lemma Ψ_step_read (c : Config n V) (p : Fin n) (hw : (c.pc p).isWrite = false) :
    Ψ (c.next inp p false) ≤ Ψ c := by
  rcases hpc : c.pc p with _ | _ | v
  · rcases hreg : c.reg with _ | v
    · rw [next_test_none inp c p false hpc hreg]
      refine Ψ_le_of_single _ _ p rfl (fun r hr => by simp [Function.update_of_ne hr]) ?_
      simp [hpc, hreg, potW]
    · rw [next_test_some inp c p false hpc hreg]
      refine Ψ_le_of_single _ _ p rfl (fun r hr => by simp [Function.update_of_ne hr]) ?_
      simp [hpc, hreg, potW]
  · rw [hpc] at hw; simp at hw
  · rw [next_done inp c p false hpc]

lemma Ψ_step_write (c : Config n V) (p : Fin n) (h1 : c.pc p = .write) (b : Bool) :
    (∑ r, ((c.next inp p b).ops r + potW (c.next inp p b).reg ((c.next inp p b).pc r))) ≤
      (∑ r, (c.ops r + potW c.reg (c.pc r))) +
        if (c.next inp p b).reg.isNone then 2 else 0 := by
  have hreg' : (c.next inp p b).reg = if b then some (inp p) else c.reg := by
    rw [next_write inp c p b h1]
  have hmono : (c.next inp p b).reg.isNone = true → c.reg.isNone = true := by
    rw [hreg']; split <;> simp
  refine sum_le_of_single p _ (fun r hr => ?_) ?_
  · rw [next_write inp c p b h1] at hmono ⊢
    simp only [Function.update_of_ne hr]
    exact Nat.add_le_add_left (potW_le hmono _) _
  · have hpc' : (c.next inp p b).pc p = .test := by rw [next_write inp c p b h1]; simp
    have hops' : (c.next inp p b).ops p = c.ops p + 1 := by rw [next_write inp c p b h1]; simp
    rw [hpc', hops', h1]
    simp only [potW]
    split_ifs <;> omega

lemma Ψ_write_none (c : Config n V) (p : Fin n) (h1 : c.pc p = .write) (hreg : c.reg = none) :
    Ψ (c.next inp p false) ≤ Ψ c + 2 ∧ Ψ (c.next inp p true) + 4 * n ≤ Ψ c := by
  have hF := Ψ_step_write inp c p h1 false
  have hT := Ψ_step_write inp c p h1 true
  have hregF : (c.next inp p false).reg = none := by rw [next_write inp c p false h1]; simpa
  have hregT : (c.next inp p true).reg = some (inp p) := by rw [next_write inp c p true h1]; simp
  unfold Ψ
  rw [hregF] at hF ⊢
  rw [hregT] at hT ⊢
  rw [hreg] at hF hT ⊢
  simp only [Option.isNone_none, Option.isNone_some, ite_true, Bool.false_eq_true, ite_false,
    add_zero] at hF hT ⊢
  omega

lemma Ψ_write_some (c : Config n V) (p : Fin n) (h1 : c.pc p = .write) {v : V}
    (hreg : c.reg = some v) (b : Bool) : Ψ (c.next inp p b) ≤ Ψ c := by
  have hb := Ψ_step_write inp c p h1 b
  have hregb : ∃ w, (c.next inp p b).reg = some w := by
    rw [next_write inp c p b h1]; cases b
    · exact ⟨v, by simpa⟩
    · exact ⟨inp p, by simp⟩
  obtain ⟨w, hw⟩ := hregb
  unfold Ψ
  rw [hw] at hb ⊢
  rw [hreg] at hb ⊢
  simp only [Option.isNone_some, Bool.false_eq_true, ite_false, add_zero] at hb ⊢
  exact hb

lemma attemptProb_ge (hn : 0 < n) (k : ℕ) : 1 / (2 * (n : ℝ)) ≤ attemptProb n k := by
  rw [coe_attemptProb]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine le_min ?_ ?_
  · rw [div_le_one (by positivity)]; linarith
  · gcongr; exact one_le_pow₀ (by norm_num)

/-- `Ψ` is a supermartingale: expected work potential does not increase. -/
lemma Ψ_step (c : Config n V) (p : Fin n) :
    ∑' b, coinFor c p b * (Ψ (c.next inp p b) : ℝ≥0∞) ≤ Ψ c := by
  cases hw : (c.pc p).isWrite
  · rw [coinFor_not_write c p hw, tsum_pure_mul]
    exact_mod_cast Ψ_step_read inp c p hw
  · have h1 : c.pc p = .write := by
      cases h : c.pc p <;> simp_all
    rw [coinFor_write c p h1, tsum_bool, coin_true, coin_false]
    have hx1 := attemptProb_le_one n (c.att p)
    have hx1' := attemptProb_le_one' n (c.att p)
    have hx0 := attemptProb_nonneg n (c.att p)
    have hge := attemptProb_ge p.pos (c.att p)
    have hn : (0 : ℝ) < n := by exact_mod_cast p.pos
    have e : ((1 - attemptProb n (c.att p) : ℝ≥0) : ℝ) = 1 - (attemptProb n (c.att p) : ℝ) := by
      rw [NNReal.coe_sub hx1, NNReal.coe_one]
    have key : ((1 - attemptProb n (c.att p) : ℝ≥0) : ℝ) * (Ψ (c.next inp p false) : ℝ) +
        (attemptProb n (c.att p) : ℝ) * (Ψ (c.next inp p true) : ℝ) ≤ (Ψ c : ℝ) := by
      rw [e]
      have h1x : 0 ≤ 1 - (attemptProb n (c.att p) : ℝ) := by linarith
      rcases hreg : c.reg with _ | v
      · obtain ⟨hF, hT⟩ := Ψ_write_none inp c p h1 hreg
        have hF' : (Ψ (c.next inp p false) : ℝ) ≤ Ψ c + 2 := by exact_mod_cast hF
        have hT' : (Ψ (c.next inp p true) : ℝ) + 4 * n ≤ Ψ c := by exact_mod_cast hT
        have hx2n : 1 ≤ (attemptProb n (c.att p) : ℝ) * (2 * n) := by
          rw [div_le_iff₀ (by positivity)] at hge; linarith
        have := mul_le_mul_of_nonneg_left hF' h1x
        have := mul_le_mul_of_nonneg_left hT' hx0
        nlinarith
      · have hF' : (Ψ (c.next inp p false) : ℝ) ≤ Ψ c := by
          exact_mod_cast Ψ_write_some inp c p h1 hreg false
        have hT' : (Ψ (c.next inp p true) : ℝ) ≤ Ψ c := by
          exact_mod_cast Ψ_write_some inp c p h1 hreg true
        have := mul_le_mul_of_nonneg_left hF' h1x
        have := mul_le_mul_of_nonneg_left hT' hx0
        nlinarith
    calc ((1 - attemptProb n (c.att p) : ℝ≥0) : ℝ≥0∞) * (Ψ (c.next inp p false) : ℝ≥0∞) +
          (attemptProb n (c.att p) : ℝ≥0∞) * (Ψ (c.next inp p true) : ℝ≥0∞)
        = ENNReal.ofReal (((1 - attemptProb n (c.att p) : ℝ≥0) : ℝ) * (Ψ (c.next inp p false) : ℝ) +
            (attemptProb n (c.att p) : ℝ) * (Ψ (c.next inp p true) : ℝ)) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_mul (NNReal.coe_nonneg _),
            ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast,
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (Ψ c : ℝ) := ENNReal.ofReal_le_ofReal key
      _ = Ψ c := ENNReal.ofReal_natCast _

lemma work_le_Ψ (N : ℕ) : ∀ h c,
    ∑' s, run inp adv N h c s * (totalWork s.2 : ℝ≥0∞) ≤ Ψ c := by
  induction N with
  | zero =>
    intro h c
    rw [run, tsum_pure_mul]
    exact_mod_cast totalWork_le_Ψ c
  | succ N ih =>
    intro h c
    rw [run]
    split
    · exact ih h c
    · next p _ =>
      rw [tsum_bind_mul]
      exact (ENNReal.tsum_le_tsum fun b => by gcongr; exact ih _ _).trans (Ψ_step inp c p)

/-- **Theorem 7 of [Aspnes 2010], expected total work `O(n)`**: against every adversary and for
every `N`, the expected number of register operations performed by all processes is at most
`7n`. -/
theorem expected_total_work (N : ℕ) :
    ∑' s, run inp adv N [] Config.init s * (totalWork s.2 : ℝ≥0∞) ≤ 7 * n := by
  have := work_le_Ψ inp adv N [] Config.init
  rw [Ψ_init] at this
  exact_mod_cast this

end Work

/-! ### Tightness of the individual-work bound and non-vacuity of agreement -/

section Examples

lemma false_mem_support_coinFor {c : Config n V} {p : Fin n}
    (h : c.pc p = .write → attemptProb n (c.att p) ≠ 1) : false ∈ (coinFor c p).support := by
  rw [PMF.mem_support_iff]
  rcases hpc : c.pc p with _ | _ | v
  · simp [coinFor, hpc]
  · rw [coinFor_write c p hpc, coin_false]
    have := h hpc
    have hle := attemptProb_le_one n (c.att p)
    simp only [ne_eq, ENNReal.coe_eq_zero]
    intro h0
    exact this (le_antisymm hle (tsub_eq_zero_iff_le.1 h0))
  · simp [coinFor, hpc]

lemma true_mem_support_coinFor {c : Config n V} {p : Fin n} (h1 : c.pc p = .write) :
    true ∈ (coinFor c p).support := by
  rw [PMF.mem_support_iff, coinFor_write c p h1, coin_true]
  have hn : (n : ℝ≥0) ≠ 0 := by have := p.pos; positivity
  simp [attemptProb, hn, ENNReal.mul_eq_top]

/-- The bound `⌈lg n⌉ + 2` on loop iterations (`attempts_le`) and the bound `2⌈lg n⌉ + 5` on
individual work (`individual_work`) are attained: for `n = 1` the single process may fail its
first write attempt (probability `1/2`), so it executes the loop `2 = ⌈lg 1⌉ + 2` times and
performs `5 = 2⌈lg 1⌉ + 5` operations. This contradicts the sentence of Section 5.2 "the loop is
never executed for more than `⌈lg n⌉ + 1` iterations". -/
theorem attempts_tight (inp : Fin 1 → V) :
    ∃ s ∈ (run inp (fun _ _ => some 0) 5 [] Config.init).support,
      s.2.att 0 = Nat.clog 2 1 + 2 ∧ s.2.ops 0 = 2 * Nat.clog 2 1 + 5 ∧
      s.2.pc 0 = .done (inp 0) := by
  refine ⟨_, mem_support_run_succ inp _ rfl (b := false) (false_mem_support_coinFor ?_) <|
    mem_support_run_succ inp _ rfl (b := false) (false_mem_support_coinFor ?_) <|
    mem_support_run_succ inp _ rfl (b := false) (false_mem_support_coinFor ?_) <|
    mem_support_run_succ inp _ rfl (b := true) (true_mem_support_coinFor ?_) <|
    mem_support_run_succ inp _ rfl (b := false) (false_mem_support_coinFor ?_) <|
    mem_support_run_zero inp _ _ _, ?_⟩
  all_goals simp [Config.next, Config.init, attemptProb]

/-- The schedule of `disagreement_possible`: `p₀` reads, `p₁` reads, `p₀` writes, `p₀` reads,
`p₁` writes, `p₁` reads (then idle). -/
def badAdv : Adversary 2 (Fin 2) := fun h _ => ([0, 1, 0, 0, 1, 1] : List (Fin 2))[h.length]?

/-- Non-vacuity of Theorem 7: agreement is not certain. With `n = 2` and inputs `0, 1`, if both
processes read `⊥`, `p₀` writes successfully (probability `1/4`) and returns `0`, then `p₁`
writes successfully (probability `1/4`) and returns `1`. -/
theorem disagreement_possible :
    ∃ s ∈ (run id badAdv 6 [] Config.init).support, ¬ Agreement (output s.2) := by
  refine ⟨_, mem_support_run_succ id _ rfl (b := false) (false_mem_support_coinFor ?_) <|
    mem_support_run_succ id _ rfl (b := false) (false_mem_support_coinFor ?_) <|
    mem_support_run_succ id _ rfl (b := true) (true_mem_support_coinFor ?_) <|
    mem_support_run_succ id _ rfl (b := false) (false_mem_support_coinFor ?_) <|
    mem_support_run_succ id _ rfl (b := true) (true_mem_support_coinFor ?_) <|
    mem_support_run_succ id _ rfl (b := false) (false_mem_support_coinFor ?_) <|
    mem_support_run_zero id _ _ _, ?_⟩
  rotate_left 6
  · intro hA
    have := hA 0 1 .adopt .adopt 0 1 (by simp [output, Config.next, Config.init])
      (by simp [output, Config.next, Config.init])
    exact absurd this (by decide)
  all_goals simp [Config.next, Config.init, attemptProb]

/-- The disagreement event of `disagreement_possible` has positive probability. -/
theorem disagreement_prob_pos :
    0 < (run id badAdv 6 [] Config.init).toOuterMeasure {s | ¬ Agreement (output s.2)} := by
  obtain ⟨s, hs, hA⟩ := disagreement_possible
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [PMF.toOuterMeasure_apply_eq_zero_iff] at h0
  exact Set.disjoint_left.1 h0 hs hA

end Examples

end Podc.ModularConsensus.Impatient
