import Papers.PODC2022.AsyncCycleColoring.Model
import Papers.PODC2022.AsyncCycleColoring.Mex

/-!
# Algorithm 2 (5-colouring) and its failure to be wait-free

Section 3.2 of the paper. Code for process `p` with neighbours `q`, `q'`:

```
Input: X_p;  Initially a_p, b_p ← 0
Forever:
  write(X_p, a_p, b_p) and read((X_q, a_q, b_q), (X_q', a_q', b_q'))
  P⁺ ← { u ∈ {q, q'} | X_u > X_p }
  C⁺ ← { a_u | u ∈ P⁺ } ∪ { b_u | u ∈ P⁺ }
  C  ← { a_q, b_q, a_q', b_q' }
  if a_p ∉ C then return(a_p)
  else if b_p ∉ C then return(b_p)
  else a_p ← min ℕ ∖ C⁺ ;  b_p ← min ℕ ∖ C
```

A neighbour whose register is still `⊥` (not yet awake) contributes nothing to `P⁺`, `C⁺`, `C`.

* `alg2_properOutputs`, `alg2_outputs_lt_five`: the outputs are a proper colouring with colours in
  `{0, …, 4}` (the correctness and palette parts of Theorem 3.11 hold).
* `theorem_3_11_false`: the termination part of Theorem 3.11 is **false**. On `C_3` with
  identifiers `0, 1, 2`, if all three processes take a first round together, process `1` then
  crashes (or is merely slow), and processes `0` and `2` keep taking their rounds simultaneously,
  then `0` and `2` never return: their states alternate with period 2.
  The same execution refutes Lemma 3.13 (process `2` is a local maximum, so its set `A_2` stays
  empty, yet it never returns).
-/

namespace AsyncCycle

/-- Local state of Algorithm 2 (also the register content): identifier and the two colours. -/
structure St2 where
  X : ℕ
  a : ℕ
  b : ℕ
deriving DecidableEq, Repr

/-- Colours read from the awake neighbours. -/
def St2.cols (u : St2) : List ℕ := [u.a, u.b]

/-- One round of Algorithm 2. -/
def alg2Step (s : St2) (l r : Option St2) : St2 ⊕ ℕ :=
  let nb := [l, r].filterMap id
  let C := nb.flatMap St2.cols
  let Cp := (nb.filter (fun u => s.X < u.X)).flatMap St2.cols
  if s.a ∉ C then Sum.inr s.a
  else if s.b ∉ C then Sum.inr s.b
  else Sum.inl ⟨s.X, mex Cp, mex C⟩

/-- Algorithm 2. -/
def alg2 : Alg St2 ℕ := ⟨alg2Step⟩

/-- Initial states: identifier `X p`, colours `0`. -/
def init2 {n : ℕ} (X : ZMod n → ℕ) : ZMod n → St2 := fun p => ⟨X p, 0, 0⟩

/-! ### Correctness and palette -/

lemma alg2_claimSafe : ClaimSafe alg2 (fun s => {s.a, s.b}) := by
  intro s l r o h
  simp only [alg2, alg2Step] at h
  split_ifs at h with h1 h2
  · cases h
    refine ⟨by simp, ?_, ?_⟩ <;> rintro x rfl hx <;>
      rcases hx with hx | hx <;> simp_all [St2.cols]
  · cases h
    refine ⟨by simp, ?_, ?_⟩ <;> rintro x rfl hx <;>
      rcases hx with hx | hx <;> simp_all [St2.cols]

/-- Theorem 3.11, correctness: the outputs properly colour the terminated processes. -/
theorem alg2_properOutputs {n : ℕ} (X : ZMod n → ℕ) : ProperOutputs alg2 (init2 X) :=
  properOutputs_of_claimSafe alg2_claimSafe

lemma length_flatMap_cols_le (l : List St2) : (l.flatMap St2.cols).length ≤ 2 * l.length := by
  induction l with
  | nil => simp
  | cons u l ih => simp [List.flatMap_cons, St2.cols] at ih ⊢; omega

lemma length_filterMap_pair_le (l r : Option St2) : ([l, r].filterMap id).length ≤ 2 :=
  (List.length_filterMap_le _ _).trans (by simp)

/-- Theorem 3.11, palette: every output is in `{0, …, 4}`. -/
theorem alg2_outputs_lt_five {n : ℕ} (X : ZMod n → ℕ) :
    OutputsIn alg2 (init2 X) {c | c < 5} := by
  refine outputsIn_of_inv (Inv := fun s => s.a ≤ 4 ∧ s.b ≤ 4) (fun _ => by simp [init2])
    ?_ ?_
  · intro s l r s' _ h
    simp only [alg2, alg2Step] at h
    split_ifs at h
    cases h
    have h2 := length_filterMap_pair_le l r
    have hC := length_flatMap_cols_le ([l, r].filterMap id)
    have hCp := length_flatMap_cols_le
      (([l, r].filterMap id).filter (fun u => s.X < u.X))
    have hf := List.length_filter_le (fun u => decide (s.X < u.X)) ([l, r].filterMap id)
    exact ⟨(mex_le_length _).trans (by omega), (mex_le_length _).trans (by omega)⟩
  · intro s l r o hs h
    simp only [alg2, alg2Step] at h
    split_ifs at h <;> cases h <;> simp <;> omega

/-! ### The counterexample to termination (Theorem 3.11, Lemma 3.13) -/

/-- Identifiers `0, 1, 2` on `C_3`. -/
def X3 : ZMod 3 → ℕ := fun p => p.val

/-- All three processes at time 1, then only processes `0` and `2`, simultaneously, forever
(process `1` crashes after its first round). -/
def sched3 : ℕ → Finset (ZMod 3) := fun t => if t ≤ 1 then Finset.univ else {0, 2}

lemma run2_periodic_base :
    run alg2 (init2 X3) sched3 4 = run alg2 (init2 X3) sched3 2 := by
  have hloc : (run alg2 (init2 X3) sched3 4).loc = (run alg2 (init2 X3) sched3 2).loc := by
    funext p; revert p; decide
  have hreg : (run alg2 (init2 X3) sched3 4).reg = (run alg2 (init2 X3) sched3 2).reg := by
    funext p; revert p; decide
  have hout : (run alg2 (init2 X3) sched3 4).out = (run alg2 (init2 X3) sched3 2).out := by
    funext p; revert p; decide
  cases h : run alg2 (init2 X3) sched3 4
  cases h' : run alg2 (init2 X3) sched3 2
  simp_all

lemma run2_periodic (k : ℕ) :
    run alg2 (init2 X3) sched3 (2 * k + 2) = run alg2 (init2 X3) sched3 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : 2 * (k + 1) + 2 = 2 * k + 2 + 1 + 1 := by omega
    rw [e, run_succ, run_succ, ih]
    have h1 : sched3 (2 * k + 2 + 1) = sched3 3 := by simp [sched3]
    have h2 : sched3 (2 * k + 2 + 1 + 1) = sched3 4 := by simp [sched3]
    rw [h1, h2]
    exact run2_periodic_base

lemma run2_out_zero_none (t : ℕ) : (run alg2 (init2 X3) sched3 t).out 0 = none := by
  obtain ⟨k, rfl | rfl⟩ : ∃ k, t = 2 * k ∨ t = 2 * k + 1 := ⟨t / 2, by omega⟩
  · rcases k with _ | k
    · rfl
    · have e : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [e, run2_periodic]; decide
  · rcases k with _ | k
    · decide
    · have e : 2 * (k + 1) + 1 = 2 * k + 2 + 1 := by omega
      rw [e, run_succ, run2_periodic]
      have h1 : sched3 (2 * k + 2 + 1) = sched3 3 := by simp [sched3]
      rw [h1]; decide

lemma run2_out_two_none (t : ℕ) : (run alg2 (init2 X3) sched3 t).out 2 = none := by
  obtain ⟨k, rfl | rfl⟩ : ∃ k, t = 2 * k ∨ t = 2 * k + 1 := ⟨t / 2, by omega⟩
  · rcases k with _ | k
    · rfl
    · have e : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [e, run2_periodic]; decide
  · rcases k with _ | k
    · decide
    · have e : 2 * (k + 1) + 1 = 2 * k + 2 + 1 := by omega
      rw [e, run_succ, run2_periodic]
      have h1 : sched3 (2 * k + 2 + 1) = sched3 3 := by simp [sched3]
      rw [h1]; decide

/-- In this execution, processes `0` and `2` are activated at every time and never return. -/
theorem alg2_runs_forever (t : ℕ) :
    ActsAt alg2 (init2 X3) sched3 t 0 ∧ ActsAt alg2 (init2 X3) sched3 t 2 ∧
      (run alg2 (init2 X3) sched3 t).out 0 = none ∧ (run alg2 (init2 X3) sched3 t).out 2 = none := by
  have hmem : (0 : ZMod 3) ∈ sched3 (t + 1) ∧ (2 : ZMod 3) ∈ sched3 (t + 1) := by
    unfold sched3; split_ifs <;> decide
  exact ⟨⟨hmem.1, run2_out_zero_none t⟩, ⟨hmem.2, run2_out_two_none t⟩,
    run2_out_zero_none t, run2_out_two_none t⟩

lemma workActs_alg2_X3 (T : ℕ) : workActs alg2 (init2 X3) sched3 0 T = T := by
  unfold workActs
  rw [Finset.filter_true_of_mem (fun t _ => (alg2_runs_forever t).1), Finset.card_range]

/-- **Theorem 3.11 (termination) is false**: Algorithm 2 is not wait-free on `C_3`, even with the
identifiers `0, 1, 2`: there is no bound on the number of activations before a process returns. -/
theorem theorem_3_11_false : ¬ ∃ K, WaitFreeWithin alg2 (init2 X3) K := by
  rintro ⟨K, hK⟩
  have := hK sched3 0 (K + 1)
  rw [workActs_alg2_X3] at this
  omega

/-- **Lemma 3.13 is false**: process `2` is a local maximum (`X_2 > X_0, X_1`), hence not a
local minimum, and its set `A_2(t)` of larger identifiers heard of along increasing paths is
empty at all times; yet it is activated at every time step and never returns. -/
theorem lemma_3_13_false :
    (X3 2 > X3 1 ∧ X3 2 > X3 0) ∧
      ∀ t, ActsAt alg2 (init2 X3) sched3 t 2 ∧ (run alg2 (init2 X3) sched3 t).out 2 = none :=
  ⟨by decide, fun t => ⟨(alg2_runs_forever t).2.1, (alg2_runs_forever t).2.2.2⟩⟩

end AsyncCycle
