import Mathlib.Logic.Function.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith

/-!
# SS-Token on a ring with a fixed leader (abstract dynamics)

Positions `0, …, N - 1` of a directed ring, the leader at position `0`. The state is a pair
`(token, bit)` of functions `ℕ → Bool`. A step on the edge `t → succ t` is Protocol 3 of the paper
(SS-Token, from Angluin et al.): a non-leader successor copies a different bit and takes the
token; the leader flips its bit when it equals its predecessor's and takes the token. In both
cases the successor's bit is negated.

* `run_legit`: stepping along the ring `0, 1, 2, …` for `2N + p` steps from **any** state yields
  the legitimate state `Legit p b` (one token at `p`, bits `b` up to `p`, `¬b` after).
* `Legit.step`: a step in a legitimate state either moves the token one position forward (on the
  token's edge) or changes nothing.
-/

namespace SSLERegular.TokenRing

/-- Successor position on the ring of size `N`. -/
def succP (N t : ℕ) : ℕ := if t + 1 = N then 0 else t + 1

/-- Does SS-Token fire on the edge `t → succP N t`? -/
def Fires (N : ℕ) (bt : ℕ → Bool) (t : ℕ) : Prop :=
  (succP N t ≠ 0 ∧ bt (succP N t) ≠ bt t) ∨ (succP N t = 0 ∧ bt t = bt (succP N t))

instance (N : ℕ) (bt : ℕ → Bool) (t : ℕ) : Decidable (Fires N bt t) := by
  unfold Fires; infer_instance

/-- One SS-Token step on the edge `t → succP N t`. -/
def stepT (N : ℕ) (st : (ℕ → Bool) × (ℕ → Bool)) (t : ℕ) : (ℕ → Bool) × (ℕ → Bool) :=
  if Fires N st.2 t then
    (Function.update (Function.update st.1 t false) (succP N t) true,
      Function.update st.2 (succP N t) (!st.2 (succP N t)))
  else st

/-- Stepping along the ring: step `n` uses the edge at position `n % N`. -/
def run (N : ℕ) (st0 : (ℕ → Bool) × (ℕ → Bool)) : ℕ → (ℕ → Bool) × (ℕ → Bool)
  | 0 => st0
  | n + 1 => stepT N (run N st0 n) (n % N)

/-- Legitimate state: one token at `m`, bits `b` on `0..m` and `¬b` after. -/
def Legit (N m : ℕ) (b : Bool) (st : (ℕ → Bool) × (ℕ → Bool)) : Prop :=
  ∀ t < N, st.1 t = decide (t = m) ∧ st.2 t = if t ≤ m then b else !b

variable {N : ℕ}

lemma run_succ (st0 : (ℕ → Bool) × (ℕ → Bool)) (n : ℕ) :
    run N st0 (n + 1) = stepT N (run N st0 n) (n % N) := rfl

lemma succP_of_lt {t : ℕ} (h : t + 1 < N) : succP N t = t + 1 := by
  unfold succP; rw [if_neg (by omega)]

lemma succP_last (hN : 1 ≤ N) : succP N (N - 1) = 0 := by
  unfold succP; rw [if_pos (by omega)]

/-- Phase A: after `s ≤ N - 1` steps, the bits on `0..s` equal the initial bit of the leader. -/
lemma phaseA (hN : 2 ≤ N) (st0 : (ℕ → Bool) × (ℕ → Bool)) :
    ∀ s ≤ N - 1, ∀ t ≤ s, (run N st0 s).2 t = st0.2 0 := by
  intro s
  induction s with
  | zero => intro _ t ht; simp [run, show t = 0 by omega]
  | succ s ih =>
    intro hs t ht
    have hs' : s + 1 < N := by omega
    have ih' := ih (by omega)
    simp only [run, Nat.mod_eq_of_lt (show s < N by omega)]
    unfold stepT
    rw [succP_of_lt hs']
    split_ifs with hf
    · simp only [Function.update_apply]
      by_cases hts : t = s + 1
      · subst hts
        simp only [if_true]
        unfold Fires at hf
        rw [succP_of_lt hs'] at hf
        rcases hf with ⟨-, h⟩ | ⟨h, -⟩
        · rw [← ih' s le_rfl]
          revert h; cases (run N st0 s).2 (s + 1) <;> cases (run N st0 s).2 s <;> simp
        · omega
      · rw [if_neg hts]; exact ih' t (by omega)
    · by_cases hts : t = s + 1
      · subst hts
        unfold Fires at hf
        rw [succP_of_lt hs'] at hf
        push Not at hf
        rw [← ih' s le_rfl]
        by_contra hne
        exact absurd (hf.1 (by omega)) (by simpa using hne)
      · exact ih' t (by omega)

/-- After the first full round the leader has flipped: the state of phase B with `s = 0`. -/
lemma phaseB (hN : 2 ≤ N) (st0 : (ℕ → Bool) × (ℕ → Bool)) :
    ∀ s < N, (∀ t < N, (run N st0 (N + s)).2 t = if t ≤ s then !st0.2 0 else st0.2 0) ∧
      ∀ t ≤ s, (run N st0 (N + s)).1 t = decide (t = s) := by
  intro s
  induction s with
  | zero =>
    intro _
    have hA := phaseA hN st0 (N - 1) le_rfl
    have hrun : run N st0 N = stepT N (run N st0 (N - 1)) (N - 1) := by
      have := run_succ (N := N) st0 (N - 1)
      rw [show N - 1 + 1 = N by omega, Nat.mod_eq_of_lt (show N - 1 < N by omega)] at this
      exact this
    have hf : Fires N (run N st0 (N - 1)).2 (N - 1) := by
      right; rw [succP_last (by omega)]; exact ⟨rfl, by rw [hA _ le_rfl, hA 0 (Nat.zero_le _)]⟩
    simp only [Nat.add_zero, hrun]
    unfold stepT
    rw [if_pos hf, succP_last (by omega)]
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simp only [Function.update_apply]
      by_cases h0 : t = 0
      · subst h0; simp [hA 0 (Nat.zero_le _)]
      · simp [h0, hA t (by omega)]
    · simp [show t = 0 by omega]
  | succ s ih =>
    intro hs
    obtain ⟨ihb, iht⟩ := ih (by omega)
    have hs' : s + 1 < N := hs
    have hrun : run N st0 (N + (s + 1)) = stepT N (run N st0 (N + s)) s := by
      rw [show N + (s + 1) = (N + s) + 1 by omega]
      simp only [run]
      rw [show (N + s) % N = s by rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt (by omega)]
    have hf : Fires N (run N st0 (N + s)).2 s := by
      left; rw [succP_of_lt hs']
      refine ⟨by omega, ?_⟩
      rw [ihb _ hs', ihb _ (by omega)]
      simp
    rw [hrun]
    unfold stepT
    rw [if_pos hf, succP_of_lt hs']
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simp only [Function.update_apply]
      by_cases h1 : t = s + 1
      · subst h1; rw [if_pos rfl, ihb _ ht]; simp
      · rw [if_neg h1, ihb t ht]
        by_cases h2 : t ≤ s
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
    · simp only [Function.update_apply]
      by_cases h1 : t = s + 1
      · subst h1; simp
      · rw [if_neg h1]
        by_cases h2 : t = s
        · subst h2; simp
        · rw [if_neg h2, iht t (by omega)]; simp; omega

/-- A legitimate state is preserved by every step; on the token's edge the token advances. -/
lemma Legit.step (hN : 2 ≤ N) {m : ℕ} {b : Bool} {st : (ℕ → Bool) × (ℕ → Bool)}
    (h : Legit N m b st) (hm : m < N) {t : ℕ} (ht : t < N) :
    (t ≠ m → stepT N st t = st) ∧
    (t = m → Legit N (succP N m) (if m + 1 = N then !b else b) (stepT N st t)) := by
  constructor
  · intro htm
    unfold stepT
    rw [if_neg]
    unfold Fires
    by_cases hlast : t + 1 = N
    · have hs : succP N t = 0 := by unfold succP; rw [if_pos hlast]
      rw [hs]
      have a := (h t ht).2; have c := (h 0 (by omega)).2
      rw [if_neg (by omega)] at a; rw [if_pos (Nat.zero_le _)] at c
      rw [a, c]; cases b <;> simp
    · have hs : succP N t = t + 1 := succP_of_lt (by omega)
      rw [hs]
      have a := (h t ht).2; have c := (h (t + 1) (by omega)).2
      rw [a, c]
      by_cases htm' : t < m
      · rw [if_pos (by omega), if_pos (by omega)]; simp
      · rw [if_neg (by omega), if_neg (by omega)]; simp
  · rintro rfl
    unfold stepT
    by_cases hlast : t + 1 = N
    · have hs : succP N t = 0 := by unfold succP; rw [if_pos hlast]
      have hf : Fires N st.2 t := by
        right; rw [hs]
        refine ⟨rfl, ?_⟩
        rw [(h t ht).2, (h 0 (by omega)).2, if_pos le_rfl, if_pos (Nat.zero_le _)]
      rw [if_pos hf, hs, if_pos hlast]
      intro s hsN
      simp only [Function.update_apply]
      by_cases h0 : s = 0
      · subst h0; simp [(h 0 (by omega)).2]
      · rw [if_neg h0, if_neg h0, (h s hsN).2]
        refine ⟨?_, ?_⟩
        · by_cases hst : s = t
          · subst hst; simp; omega
          · rw [if_neg hst, (h s hsN).1]; simp; omega
        · rw [if_pos (by omega : s ≤ t), if_neg (by omega)]; simp
    · have hs : succP N t = t + 1 := succP_of_lt (by omega)
      have hf : Fires N st.2 t := by
        left; rw [hs]
        refine ⟨by omega, ?_⟩
        rw [(h t ht).2, (h (t + 1) (by omega)).2, if_pos le_rfl, if_neg (by omega)]
        cases b <;> simp
      rw [if_pos hf, hs, if_neg hlast]
      intro s hsN
      simp only [Function.update_apply]
      by_cases h1 : s = t + 1
      · subst h1
        rw [(h (t + 1) hsN).2]
        simp
      · rw [if_neg h1, if_neg h1, (h s hsN).2]
        refine ⟨?_, ?_⟩
        · by_cases hst : s = t
          · subst hst; simp
          · rw [if_neg hst, (h s hsN).1]; simp; omega
        · by_cases h2 : s ≤ t
          · rw [if_pos h2, if_pos (by omega)]
          · rw [if_neg h2, if_neg (by omega)]

/-- **Convergence of SS-Token**: after `2N + p` steps along the ring, the state is legitimate
with the token at `p`. -/
theorem run_legit (hN : 2 ≤ N) (st0 : (ℕ → Bool) × (ℕ → Bool)) {p : ℕ} (hp : p < N) :
    Legit N p (st0.2 0) (run N st0 (2 * N + p)) := by
  -- after `2N - 1` steps: legitimate with the token at `N - 1`
  have hB := phaseB hN st0 (N - 1) (by omega)
  have h1 : Legit N (N - 1) (!st0.2 0) (run N st0 (N + (N - 1))) := by
    intro t ht
    exact ⟨hB.2 t (by omega), by rw [hB.1 t ht]; simp⟩
  -- one more step: the leader flips
  have h2 : Legit N 0 (st0.2 0) (run N st0 (2 * N)) := by
    have hrun : run N st0 (2 * N) = stepT N (run N st0 (N + (N - 1))) (N - 1) := by
      rw [show 2 * N = (N + (N - 1)) + 1 by omega]
      simp only [run]
      rw [show (N + (N - 1)) % N = N - 1 by
        rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt (by omega)]
    rw [hrun]
    have := (h1.step hN (by omega) (show N - 1 < N by omega)).2 rfl
    rw [succP_last (by omega), if_pos (by omega)] at this
    simpa using this
  -- then the token walks forward
  induction p with
  | zero => simpa using h2
  | succ p ih =>
    have ih' := ih (by omega)
    have hrun : run N st0 (2 * N + (p + 1)) = stepT N (run N st0 (2 * N + p)) p := by
      rw [show 2 * N + (p + 1) = (2 * N + p) + 1 by omega]
      simp only [run]
      rw [show (2 * N + p) % N = p by
        rw [show 2 * N + p = p + N * 2 by omega, Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt (by omega)]
    rw [hrun]
    have := (ih'.step hN (by omega) (show p < N by omega)).2 rfl
    rw [succP_of_lt (by omega), if_neg (by omega)] at this
    exact this

end SSLERegular.TokenRing
