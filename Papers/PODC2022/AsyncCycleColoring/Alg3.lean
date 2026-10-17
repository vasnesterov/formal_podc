import Papers.PODC2022.AsyncCycleColoring.Alg2
import Papers.PODC2022.AsyncCycleColoring.ColeVishkin
import Mathlib.Order.WithBot

/-!
# Algorithm 3 (fast 5-colouring) and its failure to be wait-free

Section 4.2 of the paper. Code for process `p` with neighbours `q`, `q'`:

```
Input: X_p;  Initially a_p, b_p, r_p ← 0
Forever:
 5  write(X_p, r_p, a_p, b_p) and read((X_q, r_q, a_q, b_q), (X_q', r_q', a_q', b_q'))
 6  if a_p ∉ {a_q, b_q, a_q', b_q'} then return(a_p)
 7  else if b_p ∉ {a_q, b_q, a_q', b_q'} then return(b_p)
 8  else
 9    a_p ← min ℕ ∖ { a_u, b_u | u ∼ p, X_u > X_p }
10    b_p ← min ℕ ∖ { a_q, b_q, a_q', b_q' }
11    if (r_p < ∞) ∧ (r_p ≤ min{r_q, r_q'}) then
12      if min{X_q, X_q'} < X_p < max{X_q, X_q'} then
13        r_p ← r_p + 1
14        Y ← f(X_p, min{X_q, X_q'})
15        if Y < min{X_q, X_q'} then X_p ← Y
16      else
17        r_p ← ∞
18        if X_p < min{X_q, X_q'} then
19          X_p ← min(X_p, min(ℕ ∖ { f(X_q, X_p), f(X_q', X_p) }))
```

**Reading of `⊥`.** The paper does not say how a `⊥` register enters lines 11–19. We follow the
proof of Lemma 4.10 (`r̂_{q₋ₖ₋₁}(t₀) = ⊥` is the case `k = r̂_p(t₀)`): a `⊥` value of `r` counts
as `-1`, i.e. it blocks line 11. In lines 6–10 a `⊥` neighbour contributes nothing, as in
Algorithm 2. The counterexample below does not depend on this choice: from time 1 on, all
registers it reads are written.

* `alg3_properOutputs`, `alg3_outputs_lt_five`: correctness and palette of Theorem 4.4 hold.
* `theorem_4_4_false`: the termination part of Theorem 4.4 is **false**, by the same execution as
  for Algorithm 2 (`theorem_3_11_false`): processes `0` (a local minimum, which sets `r_0 ← ∞`) and
  `2` (a local maximum, `r_2 ← ∞`) never change their identifiers again and then behave exactly
  as in Algorithm 2.
-/

namespace AsyncCycle

/-- Local state of Algorithm 3: identifier, counter (`⊤` = `∞`), colours. -/
structure St3 where
  X : ℕ
  r : WithTop ℕ
  a : ℕ
  b : ℕ
deriving DecidableEq

/-- Colours of a state. -/
def St3.cols (u : St3) : List ℕ := [u.a, u.b]

/-- The value of `r` read in a register; `⊥` (unwritten register) is below every counter. -/
def St3.rOf : Option St3 → WithBot (WithTop ℕ)
  | none => ⊥
  | some u => (u.r : WithBot (WithTop ℕ))

/-- Lines 11–19: the update of `(X_p, r_p)`, given the registers of the two neighbours. -/
def alg3XR (X : ℕ) (r : WithTop ℕ) (l r' : Option St3) : ℕ × WithTop ℕ :=
  match l, r' with
  | some u, some v =>
    if r < ⊤ ∧ r ≤ u.r ∧ r ≤ v.r then
      if min u.X v.X < X ∧ X < max u.X v.X then
        (if cvF X (min u.X v.X) < min u.X v.X then cvF X (min u.X v.X) else X, r + 1)
      else
        (if X < min u.X v.X then min X (mex [cvF u.X X, cvF v.X X]) else X, ⊤)
    else (X, r)
  | _, _ => (X, r)  -- a `⊥` neighbour blocks line 11

/-- One round of Algorithm 3. -/
def alg3Step (s : St3) (l r : Option St3) : St3 ⊕ ℕ :=
  let nb := [l, r].filterMap id
  let C := nb.flatMap St3.cols
  let Cp := (nb.filter (fun u => s.X < u.X)).flatMap St3.cols
  if s.a ∉ C then Sum.inr s.a
  else if s.b ∉ C then Sum.inr s.b
  else
    let xr := alg3XR s.X s.r l r
    Sum.inl ⟨xr.1, xr.2, mex Cp, mex C⟩

/-- Algorithm 3. -/
def alg3 : Alg St3 ℕ := ⟨alg3Step⟩

/-- Initial states: identifier `X p`, counters and colours `0`. -/
def init3 {n : ℕ} (X : ZMod n → ℕ) : ZMod n → St3 := fun p => ⟨X p, 0, 0, 0⟩

/-! ### Correctness and palette -/

lemma alg3_claimSafe : ClaimSafe alg3 (fun s => {s.a, s.b}) := by
  intro s l r o h
  simp only [alg3, alg3Step] at h
  split_ifs at h with h1 h2
  · cases h
    refine ⟨by simp, ?_, ?_⟩ <;> rintro x rfl hx <;>
      rcases hx with hx | hx <;> simp_all [St3.cols]
  · cases h
    refine ⟨by simp, ?_, ?_⟩ <;> rintro x rfl hx <;>
      rcases hx with hx | hx <;> simp_all [St3.cols]

/-- Theorem 4.4, correctness: the outputs properly colour the terminated processes. -/
theorem alg3_properOutputs {n : ℕ} (X : ZMod n → ℕ) : ProperOutputs alg3 (init3 X) :=
  properOutputs_of_claimSafe alg3_claimSafe

lemma length_flatMap_cols3_le (l : List St3) : (l.flatMap St3.cols).length ≤ 2 * l.length := by
  induction l with
  | nil => simp
  | cons u l ih => simp [List.flatMap_cons, St3.cols] at ih ⊢; omega

/-- Theorem 4.4, palette: every output is in `{0, …, 4}`. -/
theorem alg3_outputs_lt_five {n : ℕ} (X : ZMod n → ℕ) :
    OutputsIn alg3 (init3 X) {c | c < 5} := by
  refine outputsIn_of_inv (Inv := fun s => s.a ≤ 4 ∧ s.b ≤ 4) (fun _ => by simp [init3])
    ?_ ?_
  · intro s l r s' _ h
    simp only [alg3, alg3Step] at h
    split_ifs at h
    cases h
    have h2 : ([l, r].filterMap id).length ≤ 2 :=
      (List.length_filterMap_le _ _).trans (by simp)
    have hC := length_flatMap_cols3_le ([l, r].filterMap id)
    have hCp := length_flatMap_cols3_le
      (([l, r].filterMap id).filter (fun u => s.X < u.X))
    have hf := List.length_filter_le (fun u => decide (s.X < u.X)) ([l, r].filterMap id)
    exact ⟨(mex_le_length _).trans (by omega), (mex_le_length _).trans (by omega)⟩
  · intro s l r o hs h
    simp only [alg3, alg3Step] at h
    split_ifs at h <;> cases h <;> simp <;> omega

/-! ### The counterexample to termination (Theorem 4.4) -/

lemma run3_periodic_base :
    run alg3 (init3 X3) sched3 4 = run alg3 (init3 X3) sched3 2 := by
  have hloc : (run alg3 (init3 X3) sched3 4).loc = (run alg3 (init3 X3) sched3 2).loc := by
    funext p; revert p; decide
  have hreg : (run alg3 (init3 X3) sched3 4).reg = (run alg3 (init3 X3) sched3 2).reg := by
    funext p; revert p; decide
  have hout : (run alg3 (init3 X3) sched3 4).out = (run alg3 (init3 X3) sched3 2).out := by
    funext p; revert p; decide
  cases h : run alg3 (init3 X3) sched3 4
  cases h' : run alg3 (init3 X3) sched3 2
  simp_all

lemma run3_periodic (k : ℕ) :
    run alg3 (init3 X3) sched3 (2 * k + 2) = run alg3 (init3 X3) sched3 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : 2 * (k + 1) + 2 = 2 * k + 2 + 1 + 1 := by omega
    rw [e, run_succ, run_succ, ih]
    have h1 : sched3 (2 * k + 2 + 1) = sched3 3 := by simp [sched3]
    have h2 : sched3 (2 * k + 2 + 1 + 1) = sched3 4 := by simp [sched3]
    rw [h1, h2]
    exact run3_periodic_base

lemma run3_out_none (t : ℕ) :
    (run alg3 (init3 X3) sched3 t).out 0 = none ∧ (run alg3 (init3 X3) sched3 t).out 2 = none := by
  obtain ⟨k, rfl | rfl⟩ : ∃ k, t = 2 * k ∨ t = 2 * k + 1 := ⟨t / 2, by omega⟩
  · rcases k with _ | k
    · exact ⟨rfl, rfl⟩
    · have e : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [e, run3_periodic]; decide
  · rcases k with _ | k
    · decide
    · have e : 2 * (k + 1) + 1 = 2 * k + 2 + 1 := by omega
      rw [e, run_succ, run3_periodic]
      have h1 : sched3 (2 * k + 2 + 1) = sched3 3 := by simp [sched3]
      rw [h1]; decide

/-- In this execution of Algorithm 3, processes `0` and `2` are activated at every time and
never return. -/
theorem alg3_runs_forever (t : ℕ) :
    ActsAt alg3 (init3 X3) sched3 t 0 ∧ ActsAt alg3 (init3 X3) sched3 t 2 ∧
      (run alg3 (init3 X3) sched3 t).out 0 = none ∧ (run alg3 (init3 X3) sched3 t).out 2 = none := by
  have hmem : (0 : ZMod 3) ∈ sched3 (t + 1) ∧ (2 : ZMod 3) ∈ sched3 (t + 1) := by
    unfold sched3; split_ifs <;> decide
  exact ⟨⟨hmem.1, (run3_out_none t).1⟩, ⟨hmem.2, (run3_out_none t).2⟩, run3_out_none t⟩

/-- **Theorem 4.4 (termination) is false**: Algorithm 3 is not wait-free on `C_3` with the
identifiers `0, 1, 2`; in particular it does not terminate within `O(log* n)` activations. -/
theorem theorem_4_4_false : ¬ ∃ K, WaitFreeWithin alg3 (init3 X3) K := by
  rintro ⟨K, hK⟩
  have := hK sched3 0 (K + 1)
  have hw : workActs alg3 (init3 X3) sched3 0 (K + 1) = K + 1 := by
    unfold workActs
    rw [Finset.filter_true_of_mem (fun t _ => (alg3_runs_forever t).1), Finset.card_range]
  omega

end AsyncCycle
