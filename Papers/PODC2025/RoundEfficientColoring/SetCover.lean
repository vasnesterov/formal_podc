import Mathlib

/-!
# The greedy colour cover of Lemma 5.4

Chang–Mishra–Nguyen–Salim, PODC 2025, proof of Lemma 5.4: every vertex `v ∈ U` has a set
`avail v` of at least a third of the `P` colours of a palette available. Greedily pick a colour
available at `≥ 1/3` of the remaining vertices (double counting), remove those vertices, and repeat.
The result is a list `cs = [c₁, …, c_t]` of colours and, for every `v ∈ U`, the index `lvl v` of
the first chosen colour available at `v` (`v ∈ U_{lvl v + 1} \ U_{lvl v + 2}` in the paper's
notation). Since `|U_{i+1}| ≤ (2/3)|U_i|`:

* `∑_{v ∈ U} lvl v = ∑_{i ≥ 2} |U_i| ≤ 2 |U|` (the paper's bound `∑ |V_i| ≤ 3 |U₁|` on the
  binary arrays is `∑ (lvl v + 1) ≤ 3 |U|`);
* `3 ^ t ≤ 2 ^ t · 3 |U|`, i.e. `t = O(log |U|)`.
-/

namespace Podc.RoundEfficientColoring

open Finset

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- One greedy step: some colour of the palette is available at a third of the vertices. -/
lemma exists_color_third (U : Finset V) {P : ℕ} (hP : 1 ≤ P) (avail : V → Finset ℕ)
    (hsub : ∀ v ∈ U, avail v ⊆ range P) (hthird : ∀ v ∈ U, P ≤ 3 * #(avail v)) :
    ∃ c < P, #U ≤ 3 * #(U.filter (fun v => c ∈ avail v)) := by
  by_contra hcon
  push Not at hcon
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := range P) (t := U) (r := fun c v => c ∈ avail v)
  have h1 : ∑ v ∈ U, #((range P).bipartiteBelow (fun c v => c ∈ avail v) v) =
      ∑ v ∈ U, #(avail v) := by
    refine Finset.sum_congr rfl fun v hv => congrArg _ ?_
    ext c
    simp only [bipartiteBelow, mem_filter, mem_range]
    exact ⟨fun h => h.2, fun h => ⟨mem_range.mp (hsub v hv h), h⟩⟩
  have h2 : 3 * ∑ c ∈ range P, #(U.bipartiteAbove (fun c v => c ∈ avail v) c) < P * #U := by
    rw [Finset.mul_sum]
    calc ∑ c ∈ range P, 3 * #(U.bipartiteAbove (fun c v => c ∈ avail v) c)
        < ∑ _c ∈ range P, #U :=
          Finset.sum_lt_sum_of_nonempty ⟨0, mem_range.mpr hP⟩ fun c hc => hcon c (mem_range.mp hc)
      _ = P * #U := by simp
  have h3 : P * #U ≤ 3 * ∑ v ∈ U, #(avail v) := by
    rw [Finset.mul_sum]
    calc P * #U = ∑ _v ∈ U, P := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun v hv => hthird v hv
  rw [hdc, h1] at h2
  omega

/-- **The greedy colour cover** (Lemma 5.4, combinatorial part). -/
theorem exists_greedy_cover {P : ℕ} (hP : 1 ≤ P) (avail : V → Finset ℕ) :
    ∀ U : Finset V, (∀ v ∈ U, avail v ⊆ range P) → (∀ v ∈ U, P ≤ 3 * #(avail v)) →
    ∃ cs : List ℕ, ∃ lvl : V → ℕ,
      (∀ v ∈ U, lvl v < cs.length ∧ cs.getD (lvl v) 0 ∈ avail v) ∧
      (∀ v ∉ U, lvl v = 0) ∧ (∀ c ∈ cs, c < P) ∧
      ∑ v ∈ U, lvl v ≤ 2 * #U ∧ (U = ∅ → cs = []) ∧
      (U.Nonempty → 3 ^ cs.length ≤ 2 ^ cs.length * (3 * #U)) := by
  intro U
  induction hn : #U using Nat.strong_induction_on generalizing U with
  | _ n ih =>
  intro hsub hthird
  rcases U.eq_empty_or_nonempty with rfl | hne
  · exact ⟨[], fun _ => 0, by simp, fun _ _ => rfl, by simp, by simp, fun _ => rfl, by simp⟩
  obtain ⟨c, hcP, hc⟩ := exists_color_third U hP avail hsub hthird
  set U' := U.filter (fun v => c ∉ avail v) with hU'
  have hsplit := Finset.card_filter_add_card_filter_not (s := U) (fun v => c ∈ avail v)
  have hU'card : 3 * #U' ≤ 2 * #U := by rw [hU']; omega
  have hlt : #U' < n := by
    have : 0 < #U := hne.card_pos
    rw [← hn]; omega
  obtain ⟨cs', lvl', hcov, hout, hcs, hsum, hempty, hlen⟩ :=
    ih _ hlt U' rfl (fun v hv => hsub v (mem_filter.mp hv).1)
      (fun v hv => hthird v (mem_filter.mp hv).1)
  refine ⟨c :: cs', fun v => if v ∈ U' then lvl' v + 1 else 0, fun v hv => ?_, fun v hv => ?_,
    ?_, ?_, fun h => absurd h hne.ne_empty, fun _ => ?_⟩
  · by_cases hv' : v ∈ U'
    · simp only [hv', ite_true, List.length_cons, List.getD_cons_succ]
      exact ⟨by have := (hcov v hv').1; omega, (hcov v hv').2⟩
    · simp only [hv', ite_false, List.length_cons, List.getD_cons_zero]
      refine ⟨by omega, ?_⟩
      by_contra h
      exact hv' (mem_filter.mpr ⟨hv, h⟩)
  · have : v ∉ U' := fun h => hv (mem_filter.mp h).1
    simp [this]
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hcP
    · exact hcs x hx
  · have : ∑ v ∈ U, (if v ∈ U' then lvl' v + 1 else 0) = ∑ v ∈ U', (lvl' v + 1) := by
      rw [← Finset.sum_filter]
      congr 1
      ext v
      simp only [mem_filter, hU']
      tauto
    rw [this, Finset.sum_add_distrib]
    simp only [sum_const, smul_eq_mul, mul_one]
    omega
  · rcases U'.eq_empty_or_nonempty with h | h
    · rw [hempty h]
      have : 1 ≤ #U := hne.card_pos
      simp; omega
    · have h1 := hlen h
      simp only [List.length_cons, pow_succ]
      calc 3 ^ cs'.length * 3 ≤ 2 ^ cs'.length * (3 * #U') * 3 := by
            exact Nat.mul_le_mul_right _ h1
        _ = 2 ^ cs'.length * (3 * (3 * #U')) := by ring
        _ ≤ 2 ^ cs'.length * (3 * (2 * #U)) := by
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hU'card)
        _ = 2 ^ cs'.length * 2 * (3 * #U) := by ring
        _ = 2 ^ cs'.length * 2 * (3 * n) := by rw [hn]

/-! ### `t = O(log n)` and `t · w = O(n)` -/

lemma two_mul_add_one_mul_le (x : ℕ) : (2 * x + 1) * x ≤ 4 * 2 ^ x := by
  induction x with
  | zero => simp
  | succ x ih =>
    have := Nat.lt_two_pow_self (n := x)
    rw [pow_succ]
    nlinarith

/-- From `3 ^ t ≤ 2 ^ t · m`: `2 ^ (t / 2) ≤ m` (as `(3/2)² > 2`). -/
lemma two_pow_half_le {t m : ℕ} (h : 3 ^ t ≤ 2 ^ t * m) : 2 ^ (t / 2) ≤ m := by
  set j := t / 2
  have ht : t = 2 * j + (t - 2 * j) := by omega
  have h89 : 2 ^ (3 * j) ≤ 3 ^ (2 * j) := by
    rw [pow_mul, pow_mul]; exact Nat.pow_le_pow_left (by norm_num) j
  have : 2 ^ t * 2 ^ j ≤ 2 ^ t * m := by
    calc 2 ^ t * 2 ^ j = 2 ^ (t - 2 * j) * 2 ^ (3 * j) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
      _ ≤ 3 ^ (t - 2 * j) * 3 ^ (2 * j) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) _) h89
      _ = 3 ^ t := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ t * m := h
  exact Nat.le_of_mul_le_mul_left this (by positivity)

/-- If `3 ^ t ≤ 2 ^ t · (3m)` and `2 ^ w ≤ 2m`, then `(t + 1)(w + 1) ≤ 100 m` (the colours of the
greedy cover can be sent in binary with `O(m)` bits). -/
lemma cover_bits_le {t w m : ℕ} (ht : 3 ^ t ≤ 2 ^ t * (3 * m)) (hw : 2 ^ w ≤ 2 * m) :
    (t + 1) * (w + 1) ≤ 100 * m := by
  have h1 := two_pow_half_le ht
  set j := t / 2
  set x := max j w
  have hx : 2 ^ x ≤ 3 * m := by
    rcases le_total j w with h | h
    · rw [show x = w from max_eq_right h]; omega
    · rw [show x = j from max_eq_left h]; exact h1
  have hjx : j ≤ x := le_max_left _ _
  have hwx : w ≤ x := le_max_right _ _
  have hpos : 1 ≤ m := by
    have := Nat.one_le_two_pow (n := x); omega
  have hq := two_mul_add_one_mul_le x
  have ht2 : t + 1 ≤ 2 * x + 2 := by omega
  have hxp := Nat.lt_two_pow_self (n := x)
  calc (t + 1) * (w + 1) ≤ (2 * x + 2) * (x + 1) := Nat.mul_le_mul ht2 (by omega)
    _ = (2 * x + 1) * x + 3 * x + 2 := by ring
    _ ≤ 4 * 2 ^ x + 3 * 2 ^ x + 2 * 2 ^ x := by omega
    _ ≤ 100 * m := by omega

end Podc.RoundEfficientColoring
