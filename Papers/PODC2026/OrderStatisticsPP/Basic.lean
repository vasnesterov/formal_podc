import Cslib.Probability.Markov.Absorption
import Mathlib.Order.UpperLower.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Opinion dynamics on totally ordered opinions: the threshold method

D'Archivio, AlMahmoud, Natale, Mallmann-Trenn, *Order Statistics in Population Protocols via
Simple Dynamics*, PODC 2026.

`n` agents (`Fin n`) hold opinions in a finite linear order `α`; a configuration is
`c : Fin n → α`. A dynamics is a finite Markov chain `T` on configurations (a row-stochastic
matrix, see `Cslib.Probability.Markov`). The *fixation probability* of `x` from `c` is
`lim_{t → ∞} (T ^ t) c (const x)` (consensus configurations are absorbing, so this is the
probability that the process is eventually forever in consensus on `x`).

Instead of the paper's rank-ancestry process (Lemmas 4.2–4.5, 4.7) we use a *threshold*
argument: for every lower set `D` of opinions, the number `cnt D c` of agents whose opinion lies
in `D` performs a birth–death walk, and `cumul π (cnt D c) = ∑_{k ≤ cnt D c} π k` is a harmonic
function as soon as the up- and down-probabilities are balanced by `π` (`harmonic_of_balance`).
Absorption (`Cslib.Probability.Markov.tendsto_sum_mul_of_harmonic`) then gives the fixation law
(`fixation_of_harmonic`): the probability to fix on `x` is `∑ π k` over the ranks `k` of `x`.
-/

set_option linter.unusedSectionVars false

namespace OrderStatisticsPP

open Finset Matrix Filter Topology Cslib.Probability.Markov

/-- Configurations: the opinion of each of the `n` agents. -/
abbrev Config (n : ℕ) (α : Type*) := Fin n → α

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- The consensus configuration on `x`. -/
def const (x : α) : Config n α := fun _ => x

/-- Number of agents whose opinion lies in `D`. -/
noncomputable def cnt (D : Set α) (c : Config n α) : ℕ := Nat.card {u : Fin n // c u ∈ D}

/-- Real indicator of `D`. -/
noncomputable def ind (D : Set α) (a : α) : ℝ := D.indicator 1 a

lemma cnt_eq_card (D : Set α) [DecidablePred (· ∈ D)] (c : Config n α) :
    cnt D c = (univ.filter fun u => c u ∈ D).card := by
  unfold cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The rank of `x` in `c` (with ties: the largest rank): `#{u | c u ≤ x}`. For injective `c`,
`rank c (c u) = k` iff `c u` is the `k`-th smallest opinion `x_(k)`. -/
noncomputable def rank (c : Config n α) (x : α) : ℕ := cnt (Set.Iic x) c

/-- Cumulative sums `∑_{k = 1}^{m} π k`. -/
def cumul (π : ℕ → ℝ) (m : ℕ) : ℝ := ∑ k ∈ Ioc 0 m, π k

lemma cumul_zero (π : ℕ → ℝ) : cumul π 0 = 0 := by simp [cumul]

lemma cumul_succ (π : ℕ → ℝ) (m : ℕ) : cumul π (m + 1) = cumul π m + π (m + 1) := by
  unfold cumul
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le m)]

lemma cumul_sub (π : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    cumul π b - cumul π a = ∑ k ∈ Ioc a b, π k := by
  unfold cumul
  rw [← Finset.sum_Ioc_consecutive π (Nat.zero_le a) hab]
  ring

lemma exists_pos_of_sum_pos' {ι : Type*} {s : Finset ι} {f : ι → ℝ} (h : 0 < ∑ i ∈ s, f i) :
    ∃ i ∈ s, 0 < f i :=
  Finset.exists_lt_of_sum_lt (by simpa using h)

/-! ### Basic facts on `cnt`, `ind` -/

lemma ind_mem {D : Set α} {a : α} (h : a ∈ D) : ind D a = 1 := by
  simp [ind, h]

lemma ind_not_mem {D : Set α} {a : α} (h : a ∉ D) : ind D a = 0 := by
  simp [ind, h]

lemma ind_eq_ite (D : Set α) [DecidablePred (· ∈ D)] (a : α) :
    ind D a = if a ∈ D then 1 else 0 := by
  by_cases h : a ∈ D <;> simp [ind, h]

lemma cnt_eq_sum (D : Set α) (c : Config n α) : (cnt D c : ℝ) = ∑ u, ind D (c u) := by
  classical
  rw [cnt_eq_card, Finset.card_filter]
  push_cast
  simp only [ind_eq_ite]

lemma cnt_le (D : Set α) (c : Config n α) : cnt D c ≤ n := by
  classical
  rw [cnt_eq_card]
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma cnt_mono {D E : Set α} (h : D ⊆ E) (c : Config n α) : cnt D c ≤ cnt E c := by
  classical
  rw [cnt_eq_card, cnt_eq_card]
  exact Finset.card_le_card fun u => by
    simp only [Finset.mem_filter]; exact fun ⟨hu, hd⟩ => ⟨hu, h hd⟩

open Classical in
lemma cnt_const (D : Set α) (z : α) : cnt D (const z : Config n α) = if z ∈ D then n else 0 := by
  classical
  rw [cnt_eq_card]
  unfold const
  split_ifs with h <;> simp [h]

lemma cnt_pos_iff (D : Set α) (c : Config n α) : 0 < cnt D c ↔ ∃ u, c u ∈ D := by
  classical
  rw [cnt_eq_card, Finset.card_pos]
  simp [Finset.Nonempty]

lemma cnt_eq_zero_iff (D : Set α) (c : Config n α) : cnt D c = 0 ↔ ∀ u, c u ∉ D := by
  have := cnt_pos_iff D c
  constructor
  · intro h u hu; have := this.mpr ⟨u, hu⟩; omega
  · intro h; by_contra hne; obtain ⟨u, hu⟩ := this.mp (Nat.pos_of_ne_zero hne); exact h u hu

open Classical in
lemma cnt_update_int (D : Set α) (c : Config n α) (u : Fin n) (y : α) :
    (cnt D (Function.update c u y) : ℤ) =
      cnt D c - (if c u ∈ D then 1 else 0) + (if y ∈ D then 1 else 0) := by
  classical
  have key : ∀ c' : Config n α, (cnt D c' : ℤ) = ∑ v, (if c' v ∈ D then 1 else 0) := by
    intro c'
    rw [cnt_eq_card, Finset.card_filter]
    push_cast
    rfl
  rw [key, key]
  have hs := Finset.add_sum_erase Finset.univ (fun v => (if c v ∈ D then (1 : ℤ) else 0))
    (Finset.mem_univ u)
  have hs' := Finset.add_sum_erase Finset.univ
    (fun v => (if Function.update c u y v ∈ D then (1 : ℤ) else 0)) (Finset.mem_univ u)
  have he : ∑ v ∈ Finset.univ.erase u, (if Function.update c u y v ∈ D then (1 : ℤ) else 0) =
      ∑ v ∈ Finset.univ.erase u, (if c v ∈ D then (1 : ℤ) else 0) :=
    Finset.sum_congr rfl fun v hv => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
  simp only [Function.update_self] at hs'
  rw [← hs, ← hs', he]
  ring

lemma ind_zero_or_one (D : Set α) (a : α) : ind D a = 0 ∨ ind D a = 1 := by
  by_cases h : a ∈ D
  · exact Or.inr (ind_mem h)
  · exact Or.inl (ind_not_mem h)

lemma cnt_eq_n_iff (D : Set α) (c : Config n α) : cnt D c = n ↔ ∀ u, c u ∈ D := by
  classical
  rw [cnt_eq_card]
  constructor
  · intro h u
    have : (univ.filter fun u => c u ∈ D) = univ :=
      Finset.eq_univ_of_card _ (by simpa using h)
    have hu : u ∈ (univ.filter fun u => c u ∈ D) := by rw [this]; exact Finset.mem_univ u
    exact (Finset.mem_filter.mp hu).2
  · intro h
    rw [Finset.filter_true_of_mem fun u _ => h u]
    simp

/-! ### Lower sets -/

lemma max_mem_iff {D : Set α} (hD : IsLowerSet D) {a b : α} : max a b ∈ D ↔ a ∈ D ∧ b ∈ D := by
  constructor
  · intro h; exact ⟨hD (le_max_left a b) h, hD (le_max_right a b) h⟩
  · rintro ⟨ha, hb⟩; rcases max_choice a b with h | h <;> rw [h] <;> assumption

lemma min_mem_iff {D : Set α} (hD : IsLowerSet D) {a b : α} : min a b ∈ D ↔ a ∈ D ∨ b ∈ D := by
  constructor
  · intro h; rcases min_choice a b with h' | h' <;> rw [h'] at h <;> simp [h]
  · rintro (h | h)
    · exact hD (min_le_left a b) h
    · exact hD (min_le_right a b) h

/-- The median of three opinions. -/
def med3 (a b c : α) : α := max (min a b) (min (max a b) c)

/-- The median lies in a lower set iff at least two of the three opinions do. -/
lemma med3_mem_iff {D : Set α} (hD : IsLowerSet D) {a b c : α} :
    med3 a b c ∈ D ↔ (a ∈ D ∧ b ∈ D) ∨ (b ∈ D ∧ c ∈ D) ∨ (a ∈ D ∧ c ∈ D) := by
  unfold med3
  rw [max_mem_iff hD, min_mem_iff hD, min_mem_iff hD, max_mem_iff hD]
  tauto

lemma med3_self (z : α) : med3 z z z = z := by simp [med3]

lemma med3_eq_of_eq {a b : α} (h : a ≤ b) : med3 a b b = b := by
  simp [med3, h]

lemma ind_max {D : Set α} (hD : IsLowerSet D) (a b : α) :
    ind D (max a b) = ind D a * ind D b := by
  by_cases ha : a ∈ D <;> by_cases hb : b ∈ D <;>
    simp [ind_mem, ind_not_mem, ha, hb, max_mem_iff hD]

lemma ind_med3 {D : Set α} (hD : IsLowerSet D) (a b c : α) :
    ind D (med3 a b c) = ind D a * ind D b + ind D b * ind D c + ind D a * ind D c
      - 2 * (ind D a * ind D b * ind D c) := by
  by_cases ha : a ∈ D <;> by_cases hb : b ∈ D <;> by_cases hc : c ∈ D <;>
    simp [ind_mem, ind_not_mem, ha, hb, hc, med3_mem_iff hD]; norm_num

end OrderStatisticsPP
