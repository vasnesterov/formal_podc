import Papers.PODC2022.AsyncCycleColoring.Alg3
import Mathlib.Tactic.Ring

/-!
# Algorithms 2 and 3 are not wait-free on any cycle `C_n`, `n ≥ 3`

Generalisation of `theorem_3_11_false` and `theorem_4_4_false` (proved for `C_3` by evaluation)
to every `n ≥ 3`, with the identifiers `X_p = p` (`p ∈ {0, …, n - 1}`).

Schedule `schedN n`: all processes take a round at time `1`; from time `2` on, only processes `0`
and `n - 1` (the global minimum and the global maximum of the identifiers, which are neighbours)
take their rounds, simultaneously. The others crash after their first round (or are slow).
The registers of `1` and `n - 2` stay frozen at the initial states, and `0`, `n - 1` alternate
between two local states with period `2`; they never return.

The core is the algorithm-independent `not_waitFree_of_two_cycle`: any algorithm whose local step
function admits such a 2-periodic pattern is not wait-free.
-/

namespace AsyncCycle

/-- All processes at time `1` (and `0`), then only `0` and `-1 = n - 1`, forever. -/
def schedN (n : ℕ) [NeZero n] : ℕ → Finset (ZMod n) :=
  fun t => if t ≤ 1 then Finset.univ else {0, -1}

section ZModFacts

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma zmod_val_one (hn : 3 ≤ n) : (1 : ZMod n).val = 1 := by
  have : Fact (1 < n) := ⟨by omega⟩
  exact ZMod.val_one n

lemma zmod_val_neg_one (hn : 3 ≤ n) : (-1 : ZMod n).val = n - 1 := by
  rw [ZMod.neg_val', zmod_val_one hn, Nat.mod_eq_of_lt (by omega)]

lemma zmod_val_neg_two (hn : 3 ≤ n) : (-2 : ZMod n).val = n - 2 := by
  rw [ZMod.neg_val', ZMod.val_ofNat_of_lt (show 2 < n by omega)]
  exact Nat.mod_eq_of_lt (show n - 2 < n by omega)

lemma zmod_one_ne_neg_one (hn : 3 ≤ n) : (1 : ZMod n) ≠ -1 := fun h => by
  have := congrArg ZMod.val h; rw [zmod_val_one hn, zmod_val_neg_one hn] at this; omega

lemma zmod_neg_two_ne_zero (hn : 3 ≤ n) : (-2 : ZMod n) ≠ 0 := fun h => by
  have := congrArg ZMod.val h; rw [zmod_val_neg_two hn, ZMod.val_zero] at this; omega

lemma zmod_neg_two_ne_neg_one (hn : 3 ≤ n) : (-2 : ZMod n) ≠ -1 := fun h => by
  have := congrArg ZMod.val h; rw [zmod_val_neg_two hn, zmod_val_neg_one hn] at this; omega

end ZModFacts

section Generic

variable {n : ℕ} [NeZero n] {S O : Type*} (A : Alg S O) (init : ZMod n → S)

/-- The state of the execution under `schedN n` at time `t`: processes `0` and `-1` are working
with local states `a` and `b`, the registers of `1` and `-2` hold their initial states. -/
def TwoCycleInv (t : ℕ) (a b : S) : Prop :=
  (run A init (schedN n) t).out 0 = none ∧ (run A init (schedN n) t).out (-1) = none ∧
    (run A init (schedN n) t).reg 1 = some (init 1) ∧
    (run A init (schedN n) t).reg (-2) = some (init (-2)) ∧
    (run A init (schedN n) t).loc 0 = a ∧ (run A init (schedN n) t).loc (-1) = b

lemma mem_schedN_zero (t : ℕ) : (0 : ZMod n) ∈ schedN n t := by
  unfold schedN; split_ifs <;> simp

lemma mem_schedN_neg_one (t : ℕ) : (-1 : ZMod n) ∈ schedN n t := by
  unfold schedN; split_ifs <;> simp

lemma twoCycleInv_one {a b : S}
    (ha : A.step (init 0) (some (init (-1))) (some (init 1)) = Sum.inl a)
    (hb : A.step (init (-1)) (some (init (-2))) (some (init 0)) = Sum.inl b) :
    TwoCycleInv A init 1 a b := by
  have hact : ∀ p : ZMod n, ActsAt A init (schedN n) 0 p := fun p =>
    ⟨by simp [schedN], rfl⟩
  have hreg : ∀ p : ZMod n, (run A init (schedN n) 1).reg p = some (init p) := fun p =>
    reg_succ_of_acts A init _ (hact p)
  have r0 : resAt A init (schedN n) 0 0 = Sum.inl a := by
    simp only [resAt, zero_sub, zero_add, hreg, run_zero_loc]; exact ha
  have r1 : resAt A init (schedN n) 0 (-1) = Sum.inl b := by
    simp only [resAt, show (-1 : ZMod n) - 1 = -2 by ring, neg_add_cancel, hreg, run_zero_loc]
    exact hb
  exact ⟨out_succ_of_inl A init _ (hact 0) r0, out_succ_of_inl A init _ (hact (-1)) r1,
    hreg 1, hreg (-2), loc_succ_of_inl A init _ (hact 0) r0,
    loc_succ_of_inl A init _ (hact (-1)) r1⟩

lemma twoCycleInv_succ (hn : 3 ≤ n) {t : ℕ} (ht : 1 ≤ t) {a b a' b' : S}
    (h : TwoCycleInv A init t a b)
    (ha : A.step a (some b) (some (init 1)) = Sum.inl a')
    (hb : A.step b (some (init (-2))) (some a) = Sum.inl b') :
    TwoCycleInv A init (t + 1) a' b' := by
  obtain ⟨o0, o1, g1, g2, l0, l1⟩ := h
  have hs : schedN n (t + 1) = {0, -1} := by
    unfold schedN; simp only [show ¬ (t + 1 ≤ 1) by omega, ↓reduceIte]
  have act0 : ActsAt A init (schedN n) t 0 := ⟨mem_schedN_zero _, o0⟩
  have act1 : ActsAt A init (schedN n) t (-1) := ⟨mem_schedN_neg_one _, o1⟩
  have nact1 : ¬ ActsAt A init (schedN n) t 1 := fun h' => by
    have := h'.1
    rw [hs] at this
    simp [(ZMod.one_eq_zero_iff (n := n)).not.2 (by omega), zmod_one_ne_neg_one hn] at this
  have nact2 : ¬ ActsAt A init (schedN n) t (-2) := fun h' => by
    have := h'.1
    rw [hs] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h'' | h''
    · exact zmod_neg_two_ne_zero hn h''
    · exact zmod_neg_two_ne_neg_one hn h''
  have g1' : (run A init (schedN n) (t + 1)).reg 1 = some (init 1) := by
    rw [reg_succ_of_not_acts A init _ nact1, g1]
  have g2' : (run A init (schedN n) (t + 1)).reg (-2) = some (init (-2)) := by
    rw [reg_succ_of_not_acts A init _ nact2, g2]
  have r0 : resAt A init (schedN n) t 0 = Sum.inl a' := by
    rw [resAt, zero_sub, zero_add, g1', reg_succ_of_acts A init _ act1, l0, l1]; exact ha
  have r1 : resAt A init (schedN n) t (-1) = Sum.inl b' := by
    rw [resAt, show (-1 : ZMod n) - 1 = -2 by ring, neg_add_cancel, g2',
      reg_succ_of_acts A init _ act0, l0, l1]; exact hb
  exact ⟨out_succ_of_inl A init _ act0 r0, out_succ_of_inl A init _ act1 r1, g1', g2',
    loc_succ_of_inl A init _ act0 r0, loc_succ_of_inl A init _ act1 r1⟩

/-- **Generic non-termination.** If, under the schedule `schedN n`, the local step function lets
processes `0` and `-1` (taking their rounds together, next to the frozen registers of `1` and
`-2`) cycle through the states `(s₀, s₁) → (u₀, u₁) → (s₀, s₁) → ⋯` without returning, then
processes `0` and `-1` work at every time step. -/
theorem actsAt_of_two_cycle (hn : 3 ≤ n) {s₀ s₁ u₀ u₁ : S}
    (h₁ : A.step (init 0) (some (init (-1))) (some (init 1)) = Sum.inl s₀)
    (h₂ : A.step (init (-1)) (some (init (-2))) (some (init 0)) = Sum.inl s₁)
    (h₃ : A.step s₀ (some s₁) (some (init 1)) = Sum.inl u₀)
    (h₄ : A.step s₁ (some (init (-2))) (some s₀) = Sum.inl u₁)
    (h₅ : A.step u₀ (some u₁) (some (init 1)) = Sum.inl s₀)
    (h₆ : A.step u₁ (some (init (-2))) (some u₀) = Sum.inl s₁) (t : ℕ) :
    ActsAt A init (schedN n) t 0 ∧ ActsAt A init (schedN n) t (-1) := by
  have key : ∀ k, TwoCycleInv A init (2 * k + 1) s₀ s₁ ∧ TwoCycleInv A init (2 * k + 2) u₀ u₁ := by
    intro k
    induction k with
    | zero =>
      have i1 := twoCycleInv_one A init h₁ h₂
      exact ⟨i1, twoCycleInv_succ A init hn le_rfl i1 h₃ h₄⟩
    | succ k ih =>
      have i1 := twoCycleInv_succ A init hn (by omega) ih.2 h₅ h₆
      exact ⟨i1, twoCycleInv_succ A init hn (by omega) i1 h₃ h₄⟩
  have hout : (run A init (schedN n) t).out 0 = none ∧ (run A init (schedN n) t).out (-1) = none := by
    obtain ⟨k, rfl | rfl⟩ : ∃ k, t = 2 * k ∨ t = 2 * k + 1 := ⟨t / 2, by omega⟩
    · rcases k with _ | k
      · exact ⟨rfl, rfl⟩
      · obtain ⟨o0, o1, -⟩ := (key k).2
        exact ⟨o0, o1⟩
    · obtain ⟨o0, o1, -⟩ := (key k).1
      exact ⟨o0, o1⟩
  exact ⟨⟨mem_schedN_zero _, hout.1⟩, ⟨mem_schedN_neg_one _, hout.2⟩⟩

/-- Under the hypotheses of `actsAt_of_two_cycle`, the algorithm is not wait-free. -/
theorem not_waitFree_of_two_cycle (hn : 3 ≤ n) {s₀ s₁ u₀ u₁ : S}
    (h₁ : A.step (init 0) (some (init (-1))) (some (init 1)) = Sum.inl s₀)
    (h₂ : A.step (init (-1)) (some (init (-2))) (some (init 0)) = Sum.inl s₁)
    (h₃ : A.step s₀ (some s₁) (some (init 1)) = Sum.inl u₀)
    (h₄ : A.step s₁ (some (init (-2))) (some s₀) = Sum.inl u₁)
    (h₅ : A.step u₀ (some u₁) (some (init 1)) = Sum.inl s₀)
    (h₆ : A.step u₁ (some (init (-2))) (some u₀) = Sum.inl s₁) :
    ¬ ∃ K, WaitFreeWithin A init K := by
  rintro ⟨K, hK⟩
  have := hK (schedN n) 0 (K + 1)
  have hw : workActs A init (schedN n) 0 (K + 1) = K + 1 := by
    unfold workActs
    rw [Finset.filter_true_of_mem
      (fun t _ => (actsAt_of_two_cycle A init hn h₁ h₂ h₃ h₄ h₅ h₆ t).1), Finset.card_range]
  omega

end Generic

/-! ### The concrete steps of Algorithms 2 and 3

`N`, `x₁`, `x₂` are the identifiers of `-1`, `1`, `-2`; process `0` has identifier `0`. Only the
comparisons `0 < N`, `0 < x₁`, `x₂ < N` matter. -/

section Steps

variable {N x₁ x₂ : ℕ}

lemma alg2_step₁ (h1 : 0 < N) (h2 : 0 < x₁) :
    alg2Step ⟨0, 0, 0⟩ (some ⟨N, 0, 0⟩) (some ⟨x₁, 0, 0⟩) = Sum.inl ⟨0, 1, 1⟩ := by
  simp [alg2Step, St2.cols, h1, h2]; decide

lemma alg2_step₂ (h : x₂ < N) :
    alg2Step ⟨N, 0, 0⟩ (some ⟨x₂, 0, 0⟩) (some ⟨0, 0, 0⟩) = Sum.inl ⟨N, 0, 1⟩ := by
  simp [alg2Step, St2.cols, h.not_gt]; decide

lemma alg2_step₃ (h1 : 0 < N) (h2 : 0 < x₁) :
    alg2Step ⟨0, 1, 1⟩ (some ⟨N, 0, 1⟩) (some ⟨x₁, 0, 0⟩) = Sum.inl ⟨0, 2, 2⟩ := by
  simp [alg2Step, St2.cols, h1, h2]; decide

lemma alg2_step₄ (h : x₂ < N) :
    alg2Step ⟨N, 0, 1⟩ (some ⟨x₂, 0, 0⟩) (some ⟨0, 1, 1⟩) = Sum.inl ⟨N, 0, 2⟩ := by
  simp [alg2Step, St2.cols, h.not_gt]; decide

lemma alg2_step₅ (h1 : 0 < N) (h2 : 0 < x₁) :
    alg2Step ⟨0, 2, 2⟩ (some ⟨N, 0, 2⟩) (some ⟨x₁, 0, 0⟩) = Sum.inl ⟨0, 1, 1⟩ := by
  simp [alg2Step, St2.cols, h1, h2]; decide

lemma alg2_step₆ (h : x₂ < N) :
    alg2Step ⟨N, 0, 2⟩ (some ⟨x₂, 0, 0⟩) (some ⟨0, 2, 2⟩) = Sum.inl ⟨N, 0, 1⟩ := by
  simp [alg2Step, St2.cols, h.not_gt]; decide

/-- Once `r_p = ∞`, lines 11–19 of Algorithm 3 are skipped. -/
lemma alg3XR_top (X : ℕ) (l r : Option St3) : alg3XR X ⊤ l r = (X, ⊤) := by
  unfold alg3XR; split <;> simp

lemma alg3_step₁ (h1 : 0 < N) (h2 : 0 < x₁) :
    alg3Step ⟨0, 0, 0, 0⟩ (some ⟨N, 0, 0, 0⟩) (some ⟨x₁, 0, 0, 0⟩) = Sum.inl ⟨0, ⊤, 1, 1⟩ := by
  simp [alg3Step, alg3XR, St3.cols, h1, h2]; decide

lemma alg3_step₂ (h : x₂ < N) :
    alg3Step ⟨N, 0, 0, 0⟩ (some ⟨x₂, 0, 0, 0⟩) (some ⟨0, 0, 0, 0⟩) = Sum.inl ⟨N, ⊤, 0, 1⟩ := by
  simp [alg3Step, alg3XR, St3.cols, h.not_gt, (Nat.zero_le x₂).trans_lt h]; decide

lemma alg3_step₃ (h1 : 0 < N) (h2 : 0 < x₁) :
    alg3Step ⟨0, ⊤, 1, 1⟩ (some ⟨N, ⊤, 0, 1⟩) (some ⟨x₁, 0, 0, 0⟩) = Sum.inl ⟨0, ⊤, 2, 2⟩ := by
  simp [alg3Step, alg3XR_top, St3.cols, h1, h2]; decide

lemma alg3_step₄ (h : x₂ < N) :
    alg3Step ⟨N, ⊤, 0, 1⟩ (some ⟨x₂, 0, 0, 0⟩) (some ⟨0, ⊤, 1, 1⟩) = Sum.inl ⟨N, ⊤, 0, 2⟩ := by
  simp [alg3Step, alg3XR_top, St3.cols, h.not_gt]; decide

lemma alg3_step₅ (h1 : 0 < N) (h2 : 0 < x₁) :
    alg3Step ⟨0, ⊤, 2, 2⟩ (some ⟨N, ⊤, 0, 2⟩) (some ⟨x₁, 0, 0, 0⟩) = Sum.inl ⟨0, ⊤, 1, 1⟩ := by
  simp [alg3Step, alg3XR_top, St3.cols, h1, h2]; decide

lemma alg3_step₆ (h : x₂ < N) :
    alg3Step ⟨N, ⊤, 0, 2⟩ (some ⟨x₂, 0, 0, 0⟩) (some ⟨0, ⊤, 2, 2⟩) = Sum.inl ⟨N, ⊤, 0, 1⟩ := by
  simp [alg3Step, alg3XR_top, St3.cols, h.not_gt]; decide

end Steps

/-! ### Main results -/

variable {n : ℕ} [NeZero n]

/-- Algorithm 2 is not wait-free for any identifier assignment in which some process (wlog `0`)
has identifier `0` and its neighbour `-1` has a larger identifier than its other neighbour `-2`
(and than `0`), e.g. when `0` is the global minimum and `-1` the global maximum. -/
theorem alg2_not_waitFree_of (hn : 3 ≤ n) (X : ZMod n → ℕ) (h0 : X 0 = 0) (h1 : 0 < X 1)
    (h2 : X (-2) < X (-1)) : ¬ ∃ K, WaitFreeWithin alg2 (init2 X) K := by
  have hN : 0 < X (-1) := (Nat.zero_le _).trans_lt h2
  refine not_waitFree_of_two_cycle alg2 (init2 X) hn (s₀ := ⟨0, 1, 1⟩) (s₁ := ⟨X (-1), 0, 1⟩)
    (u₀ := ⟨0, 2, 2⟩) (u₁ := ⟨X (-1), 0, 2⟩) ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [alg2, init2, h0]
  exacts [alg2_step₁ hN h1, alg2_step₂ h2, alg2_step₃ hN h1, alg2_step₄ h2, alg2_step₅ hN h1,
    alg2_step₆ h2]

/-- Algorithm 3 is not wait-free under the same hypotheses as `alg2_not_waitFree_of`. -/
theorem alg3_not_waitFree_of (hn : 3 ≤ n) (X : ZMod n → ℕ) (h0 : X 0 = 0) (h1 : 0 < X 1)
    (h2 : X (-2) < X (-1)) : ¬ ∃ K, WaitFreeWithin alg3 (init3 X) K := by
  have hN : 0 < X (-1) := (Nat.zero_le _).trans_lt h2
  refine not_waitFree_of_two_cycle alg3 (init3 X) hn (s₀ := ⟨0, ⊤, 1, 1⟩)
    (s₁ := ⟨X (-1), ⊤, 0, 1⟩) (u₀ := ⟨0, ⊤, 2, 2⟩) (u₁ := ⟨X (-1), ⊤, 0, 2⟩) ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [alg3, init3, h0]
  exacts [alg3_step₁ hN h1, alg3_step₂ h2, alg3_step₃ hN h1, alg3_step₄ h2, alg3_step₅ hN h1,
    alg3_step₆ h2]

lemma val_hyps (hn : 3 ≤ n) :
    (0 : ZMod n).val = 0 ∧ 0 < (1 : ZMod n).val ∧ (-2 : ZMod n).val < (-1 : ZMod n).val := by
  rw [ZMod.val_zero, zmod_val_one hn, zmod_val_neg_two hn, zmod_val_neg_one hn]; omega

/-- **Theorem 3.11 (termination) is false on every cycle `C_n`, `n ≥ 3`**: with the identifiers
`X_p = p ∈ {0, …, n - 1}`, Algorithm 2 is not wait-free. In the execution `schedN n`, processes `0`
(the minimum) and `n - 1` (the maximum) take a round at every time step and never return. -/
theorem theorem_3_11_false_all (n : ℕ) (hn : 3 ≤ n) [NeZero n] :
    ¬ ∃ K, WaitFreeWithin alg2 (init2 (fun p : ZMod n => p.val)) K :=
  alg2_not_waitFree_of hn _ (val_hyps hn).1 (val_hyps hn).2.1 (val_hyps hn).2.2

/-- **Theorem 4.4 (termination) is false on every cycle `C_n`, `n ≥ 3`**: with the identifiers
`X_p = p ∈ {0, …, n - 1}`, Algorithm 3 is not wait-free (so a fortiori it does not terminate in
`O(log* n)` activations). Same execution as `theorem_3_11_false_all`; processes `0` and `n - 1`
set `r ← ∞` at their first round and keep their identifiers. -/
theorem theorem_4_4_false_all (n : ℕ) (hn : 3 ≤ n) [NeZero n] :
    ¬ ∃ K, WaitFreeWithin alg3 (init3 (fun p : ZMod n => p.val)) K :=
  alg3_not_waitFree_of hn _ (val_hyps hn).1 (val_hyps hn).2.1 (val_hyps hn).2.2

end AsyncCycle
