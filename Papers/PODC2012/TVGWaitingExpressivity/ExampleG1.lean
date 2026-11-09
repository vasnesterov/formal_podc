import Papers.PODC2012.TVGWaitingExpressivity.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# The example `G₁` of Section 2: a TVG-automaton recognizing `aⁿbⁿ` without waiting

Casteigts et al., *Expressivity of Time-Varying Graphs and the Power of Waiting in Dynamic
Networks* (arXiv:1205.1975v1), Section 2, Figure 2 and Table 1.

Nodes `v₀, v₁, v₂`, alphabet `{a, b}`, five edges (written `(u, letter, v)`):

| edge | `(u, ℓ, v)`      | `ρ(e, t) = 1` iff                 | `ζ(e, t)`  |
|------|------------------|-----------------------------------|------------|
| e₀   | `(v₀, a, v₀)`    | always                            | `(p − 1)t` |
| e₁   | `(v₀, b, v₁)`    | `t > p`                           | `(q − 1)t` |
| e₂   | `(v₁, b, v₁)`    | `t ≠ pⁱqⁱ⁻¹` for all `i > 1`      | `(q − 1)t` |
| e₃   | `(v₀, b, v₂)`    | `t = p`                           | any        |
| e₄   | `(v₁, b, v₂)`    | `t = pⁱqⁱ⁻¹` for some `i > 1`     | any        |

`p, q` are distinct primes, `v₀` is initial, `v₂` accepting, and journeys start at time `1`.
The "any" latencies of `e₃, e₄` are arbitrary functions `ζ₃, ζ₄` (default `0`).

Main results: `Lnowait_G1` (`L_nowait(G₁) = {aⁿbⁿ : n ≥ 1}`) and `G1_deterministic`.
-/

namespace Podc.TVGWaitingExpressivity

namespace ExampleG1

/-- The alphabet `{a, b}` of the example. -/
inductive Letter
  | a
  | b
  deriving DecidableEq

/-- The nodes `v₀, v₁, v₂` of the example. -/
inductive Node
  | v0
  | v1
  | v2
  deriving DecidableEq

open Letter Node

instance : Fintype Letter := ⟨{a, b}, by intro x; cases x <;> simp⟩

instance : Fintype Node := ⟨{v0, v1, v2}, by intro x; cases x <;> simp⟩

/-- The TVG-automaton `A(G₁)` of Section 2 (Figure 2, Table 1), for parameters `p, q` (two distinct
primes in the paper) and arbitrary latencies `ζ₃, ζ₄` of the edges `e₃, e₄` (Table 1: "any"). -/
def G1 (p q : ℕ) (ζ₃ ζ₄ : ℕ → ℕ := fun _ => 0) : TVGAutomaton Node Letter where
  present
    | (v0, a, v0), _ => True
    | (v0, b, v1), t => p < t
    | (v1, b, v1), t => ∀ i > 1, t ≠ p ^ i * q ^ (i - 1)
    | (v0, b, v2), t => t = p
    | (v1, b, v2), t => ∃ i > 1, t = p ^ i * q ^ (i - 1)
    | _, _ => False
  latency
    | (v0, a, v0), t => (p - 1) * t
    | (v0, b, v1), t => (q - 1) * t
    | (v1, b, v1), t => (q - 1) * t
    | (v0, b, v2), t => ζ₃ t
    | (v1, b, v2), t => ζ₄ t
    | _, _ => 0
  init := {v0}
  accept := {v2}
  start := 1

/-- `pⁿqʲ = pⁱqⁱ⁻¹` for distinct primes forces `n = i` and `j = i − 1`. -/
theorem pow_mul_pow_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {n j i : ℕ}
    (h : p ^ n * q ^ j = p ^ i * q ^ (i - 1)) : n = i ∧ j = i - 1 := by
  have hp0 : p ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hq0 : q ^ j ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hp0' : p ^ i ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hq0' : q ^ (i - 1) ≠ 0 := pow_ne_zero _ hq.ne_zero
  have h1 := congrArg (fun m => m.factorization p) h
  have h2 := congrArg (fun m => m.factorization q) h
  simp only [Nat.factorization_mul hp0 hq0, Nat.factorization_mul hp0' hq0',
    Nat.Prime.factorization_pow hp, Nat.Prime.factorization_pow hq, Finsupp.add_apply,
    Finsupp.single_apply] at h1 h2
  simp [hpq, hpq.symm] at h1 h2
  exact ⟨h1, h2⟩


theorem add_pred_mul {q : ℕ} (hq : 1 ≤ q) (T : ℕ) : T + (q - 1) * T = T * q := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]; ring

variable {p q : ℕ} {ζ₃ ζ₄ : ℕ → ℕ}

/-- `v₂` has no outgoing edges. -/
theorem journey_from_v2 {P : PauseRule} {t : ℕ} {w : List Letter} {x : Node} {t' : ℕ}
    (h : (G1 p q ζ₃ ζ₄).Journey P v2 t w x t') : w = [] ∧ x = v2 := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ hpres _ => rename_i c v _ _ _; cases c <;> cases v <;> simp [G1] at hpres

/-- Reading the `b`s at `v₁`: from `v₁` at time `pⁿqʲ` (`j < n`, `n ≥ 2`), exactly the word
`bⁿ⁻ʲ` leads to `v₂`. -/
theorem from_v1_iff (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {n : ℕ} (hn : 2 ≤ n) :
    ∀ (w : List Letter) (j : ℕ), j < n →
      ((∃ t', (G1 p q ζ₃ ζ₄).Journey noWait v1 (p ^ n * q ^ j) w v2 t') ↔
        w = List.replicate (n - j) b) := by
  intro w
  induction w with
  | nil =>
    intro j hj
    simp only [TVG.journey_nil_iff, reduceCtorEq, false_and, exists_const, false_iff]
    intro h
    have := congrArg List.length h
    simp at this; omega
  | cons c w ih =>
    intro j hj
    have htime : p ^ n * q ^ j + (q - 1) * (p ^ n * q ^ j) = p ^ n * q ^ (j + 1) := by
      rw [add_pred_mul hq.one_le, pow_succ]; ring
    have hrep : List.replicate (n - j) b = b :: List.replicate (n - (j + 1)) b := by
      rw [show n - j = n - (j + 1) + 1 by omega, List.replicate_succ]
    rw [hrep]
    constructor
    · rintro ⟨t', h⟩
      rw [TVG.journey_cons_iff] at h
      obtain ⟨v, t₁, rfl, hpres, h⟩ := h
      cases c <;> cases v <;> simp [G1] at hpres
      · -- `e₂`
        have hj' : j + 1 ≠ n := by
          rintro rfl
          exact hpres (j + 1) (by omega) (by simp)
        simp only [G1, htime] at h
        simpa using (ih (j + 1) (by omega)).1 ⟨t', h⟩
      · -- `e₄`
        obtain ⟨i, hi, he⟩ := hpres
        obtain ⟨rfl, rfl⟩ := pow_mul_pow_eq hp hq hpq he
        obtain ⟨rfl, -⟩ := journey_from_v2 h
        simp; omega
    · rintro h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hj' : j + 1 = n
      · rw [show n - (j + 1) = 0 by omega, List.replicate_zero]
        exact ⟨_, TVG.Journey.cons (v := v2) rfl ⟨n, by omega, by rw [← hj']; simp⟩ (.nil _ _)⟩
      · obtain ⟨t', h⟩ := (ih (j + 1) (by omega)).2 rfl
        refine ⟨t', TVG.Journey.cons (v := v1) rfl ?_ ?_⟩
        · intro i hi he
          obtain ⟨rfl, rfl⟩ := pow_mul_pow_eq hp hq hpq he
          omega
        · simpa only [G1, htime] using h

/-- Reading at `v₀`: from `v₀` at time `pᵐ`, the words leading to `v₂` are exactly `aᵏbᵐ⁺ᵏ` with
`m + k ≥ 1`. -/
theorem from_v0_iff (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∀ (w : List Letter) (m : ℕ),
      ((∃ t', (G1 p q ζ₃ ζ₄).Journey noWait v0 (p ^ m) w v2 t') ↔
        ∃ k, 1 ≤ m + k ∧ w = List.replicate k a ++ List.replicate (m + k) b) := by
  intro w
  induction w with
  | nil =>
    intro m
    simp only [TVG.journey_nil_iff, reduceCtorEq, false_and, exists_const, false_iff, not_exists,
      not_and]
    intro k hk h
    have := congrArg List.length h
    simp at this; omega
  | cons c w ih =>
    intro m
    have htime : p ^ m + (p - 1) * p ^ m = p ^ (m + 1) := by
      rw [add_pred_mul hp.one_le, pow_succ]
    have htime' : p ^ m + (q - 1) * p ^ m = p ^ m * q ^ 1 := by
      rw [add_pred_mul hq.one_le, pow_one]
    constructor
    · rintro ⟨t', h⟩
      rw [TVG.journey_cons_iff] at h
      obtain ⟨v, t₁, rfl, hpres, h⟩ := h
      cases c <;> cases v <;> simp [G1] at hpres
      · -- `e₀`
        simp only [G1, htime] at h
        obtain ⟨k, -, rfl⟩ := (ih (m + 1)).1 ⟨t', h⟩
        refine ⟨k + 1, by omega, ?_⟩
        rw [show m + (k + 1) = m + 1 + k by omega]
        simp [List.replicate_succ]
      · -- `e₁`
        have hm : 1 < m := by
          by_contra hm
          interval_cases m
          · simp at hpres; exact absurd hpres (by have := hp.two_le; omega)
          · simp at hpres
        simp only [G1, htime'] at h
        have := (from_v1_iff hp hq hpq (by omega) w 1 hm).1 ⟨t', h⟩
        refine ⟨0, by omega, ?_⟩
        rw [this, show m + 0 = m - 1 + 1 by omega, List.replicate_succ]
        simp
      · -- `e₃`
        have hm : m = 1 := by
          have := Nat.pow_right_injective hp.two_le (show p ^ m = p ^ 1 by simpa using hpres)
          simpa using this
        subst hm
        obtain ⟨rfl, -⟩ := journey_from_v2 h
        exact ⟨0, by omega, by simp⟩
    · rintro ⟨k, hk, h⟩
      cases k with
      | zero =>
        obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simp only [List.replicate_zero, List.nil_append, Nat.add_zero, List.replicate_succ,
          List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · rw [List.replicate_zero]
          exact ⟨_, TVG.Journey.cons (v := v2) rfl (by simp [G1]) (.nil _ _)⟩
        · obtain ⟨t', h⟩ :=
            (from_v1_iff (ζ₃ := ζ₃) (ζ₄ := ζ₄) hp hq hpq (n := m + 1) (by omega)
              (List.replicate m b) 1 (by omega)).2 (by simp)
          refine ⟨t', TVG.Journey.cons (v := v1) rfl ?_ ?_⟩
          · show p < p ^ (m + 1)
            simpa using Nat.pow_lt_pow_right hp.one_lt (show 1 < m + 1 by omega)
          · simpa only [G1, htime'] using h
      | succ k =>
        simp only [List.replicate_succ, List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨t', h⟩ := (ih (m + 1)).2 ⟨k, by omega, by rw [show m + 1 + k = m + (k + 1) by omega]⟩
        refine ⟨t', TVG.Journey.cons (v := v0) rfl trivial ?_⟩
        simpa only [G1, htime] using h

/-- Example of Section 2 (Figure 2, Table 1) of [Casteigts et al.]: for two distinct primes `p, q`
(and whatever latencies of `e₃, e₄`), the TVG-automaton `G₁` started at time `1` accepts, using
direct journeys only, exactly the context-free language `{aⁿbⁿ : n ≥ 1}`. -/
theorem Lnowait_G1 (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (G1 p q ζ₃ ζ₄).Lnowait = {w | ∃ n ≥ 1, w = List.replicate n a ++ List.replicate n b} := by
  ext w
  have := from_v0_iff (ζ₃ := ζ₃) (ζ₄ := ζ₄) hp hq hpq w 0
  simp only [pow_zero, Nat.zero_add] at this
  simp only [TVGAutomaton.Lnowait, TVGAutomaton.lang]
  simp only [G1, Set.mem_singleton_iff, exists_eq_left]
  exact this

/-- Example of Section 2: the TVG-automaton `G₁` is deterministic — for every node, time and letter
at most one edge is present (this holds for all parameters). -/
theorem G1_deterministic (p q : ℕ) (ζ₃ ζ₄ : ℕ → ℕ) (u : Node) (c : Letter) (t : ℕ) (v v' : Node)
    (h : (G1 p q ζ₃ ζ₄).present (u, c, v) t) (h' : (G1 p q ζ₃ ζ₄).present (u, c, v') t) :
    v = v' := by
  cases u <;> cases c <;> cases v <;> cases v' <;> simp only [G1] at h h' ⊢ <;>
    first
    | trivial
    | (obtain ⟨i, hi, he⟩ := h; exact absurd he (h' i hi))
    | (obtain ⟨i, hi, he⟩ := h'; exact absurd he (h i hi))
    | omega

end ExampleG1

end Podc.TVGWaitingExpressivity
