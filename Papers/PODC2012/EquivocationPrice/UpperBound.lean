import Papers.PODC2012.EquivocationPrice.Defs

/-!
# Upper bound `Tₙ(h) = O(n³/h²)` (Theorem 7), by counting

Jaffe, Moscibroda, Sen, *On the Price of Equivocation in Byzantine Agreement*, PODC 2012,
Section 4.

The paper proves Theorem 7 with lifted hypergraphs of Ramanujan graphs of degree `Θ(n/h)` (see
`Expander.lean` for the conditional part of that argument) and remarks that a simple probabilistic
argument also works. We formalize the latter, derandomized as a greedy hitting-set argument:

* every valid colouring `(A, B, C)` has `|A|·|B|·|C| ≥ h²·n/3` crossing triples
  (`ab ≥ h(a + b - h)` twice, `card_crossing_ge`);
* there are at most `4ⁿ` colourings (maps `V → Fin 4`);
* greedily choosing a triple hitting the largest number of not-yet-hit colourings, `m` triples
  leave at most `4ⁿ (1 - K/N)ᵐ ≤ 4ⁿ e^{-Km/N}` colourings unhit, `N = C(n, 3)`
  (`exists_hitting`); this is `< 1` for `m = ⌊n³/h²⌋`.

Main results: `theorem_7` (an `h`-disjoint 3-uniform hypergraph with `|E|·h² ≤ n³` exists for
`1 ≤ h ≤ n/3`) and `T_le` (`Tₙ(h)·h² ≤ n³`).
-/

namespace Podc.EquivocationPrice

open Finset

section Hitting

variable {α ι : Type*} [DecidableEq α]

/-- One greedy step: some triple `t ∈ U` hits at least a `K/|U|` fraction of the not-yet-hit
sets. -/
lemma greedy_step (U : Finset α) (I : Finset ι) (S : ι → Finset α) (hS : ∀ i ∈ I, S i ⊆ U)
    (K : ℝ) (hK0 : 0 < K) (hK : ∀ i ∈ I, K ≤ (S i).card) (E : Finset α) (hE : E ⊆ U) :
    ∃ E' ⊆ U, E'.card ≤ E.card + 1 ∧
      ((I.filter fun i => Disjoint E' (S i)).card : ℝ) * U.card ≤
        (I.filter fun i => Disjoint E (S i)).card * (U.card - K) := by
  set R := I.filter fun i => Disjoint E (S i) with hRdef
  rcases R.eq_empty_or_nonempty with hR | ⟨i₀, hi₀⟩
  · refine ⟨E, hE, by omega, ?_⟩
    rw [← hRdef, hR]; simp
  have hi₀I : i₀ ∈ I := (mem_filter.1 hi₀).1
  -- double counting
  have hsum : ∑ t ∈ U, ((R.filter fun i => t ∈ S i).card : ℝ) = ∑ i ∈ R, ((S i).card : ℝ) := by
    have : ∀ t ∈ U, ((R.filter fun i => t ∈ S i).card : ℝ) =
        ∑ i ∈ R, if t ∈ S i then (1 : ℝ) else 0 := by
      intro t _; rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, nsmul_one]
    rw [sum_congr rfl this, sum_comm]
    refine sum_congr rfl fun i hi => ?_
    rw [← sum_filter, sum_const, nsmul_one]
    congr 2
    ext t
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun ht => hS i (mem_filter.1 hi).1 ht
  have hUne : U.Nonempty := by
    obtain ⟨x, hx⟩ : (S i₀).Nonempty := by
      rw [← card_pos]; exact_mod_cast hK0.trans_le (hK i₀ hi₀I)
    exact ⟨x, hS i₀ hi₀I hx⟩
  have hRK : (R.card : ℝ) * K ≤ ∑ t ∈ U, ((R.filter fun i => t ∈ S i).card : ℝ) := by
    rw [hsum, show (R.card : ℝ) * K = ∑ _i ∈ R, K by rw [sum_const, nsmul_eq_mul]]
    exact sum_le_sum fun i hi => hK i (mem_filter.1 hi).1
  obtain ⟨t, htU, ht⟩ : ∃ t ∈ U, (R.card : ℝ) * K ≤ U.card * (R.filter fun i => t ∈ S i).card := by
    refine exists_le_of_sum_le hUne ?_
    rw [sum_const, nsmul_eq_mul, ← mul_sum]
    exact mul_le_mul_of_nonneg_left hRK (by positivity)
  refine ⟨insert t E, insert_subset htU hE, card_insert_le _ _, ?_⟩
  have hfilt : (I.filter fun i => Disjoint (insert t E) (S i)) = R.filter fun i => t ∉ S i := by
    ext i; simp only [hRdef, mem_filter, disjoint_insert_left]; tauto
  rw [hfilt]
  have hc := card_filter_add_card_filter_not (s := R) (fun i => t ∈ S i)
  have hc' : ((R.filter fun i => t ∉ S i).card : ℝ) =
      R.card - (R.filter fun i => t ∈ S i).card := by
    rw [← hc]; push_cast; ring
  rw [hc']
  nlinarith

/-- `m` greedy steps. -/
lemma greedy_iter (U : Finset α) (I : Finset ι) (S : ι → Finset α) (hS : ∀ i ∈ I, S i ⊆ U)
    (K : ℝ) (hK0 : 0 < K) (hKU : K ≤ U.card) (hK : ∀ i ∈ I, K ≤ (S i).card) (m : ℕ) :
    ∃ E ⊆ U, E.card ≤ m ∧
      ((I.filter fun i => Disjoint E (S i)).card : ℝ) * U.card ^ m ≤ I.card * (U.card - K) ^ m := by
  induction m with
  | zero => exact ⟨∅, empty_subset _, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨E, hEU, hEm, hE⟩ := ih
    obtain ⟨E', hE'U, hE'm, hE'⟩ := greedy_step U I S hS K hK0 hK E hEU
    refine ⟨E', hE'U, by omega, ?_⟩
    have h1 : (0 : ℝ) ≤ U.card - K := by linarith
    calc ((I.filter fun i => Disjoint E' (S i)).card : ℝ) * U.card ^ (m + 1)
        = (((I.filter fun i => Disjoint E' (S i)).card : ℝ) * U.card) * U.card ^ m := by ring
      _ ≤ ((I.filter fun i => Disjoint E (S i)).card * (U.card - K)) * U.card ^ m := by
          gcongr
      _ = (((I.filter fun i => Disjoint E (S i)).card : ℝ) * U.card ^ m) * (U.card - K) := by ring
      _ ≤ (I.card * (U.card - K) ^ m) * (U.card - K) := by gcongr
      _ = I.card * (U.card - K) ^ (m + 1) := by ring

/-- **Greedy hitting set.** If each of the sets `S i ⊆ U` (`i ∈ I`) has at least `K > 0`
elements and `|I|·e^{-Km/|U|} < 1`, then some `m` elements of `U` hit every `S i`. -/
-- CSLib candidate
theorem exists_hitting (U : Finset α) (I : Finset ι) (S : ι → Finset α) (hS : ∀ i ∈ I, S i ⊆ U)
    (K : ℝ) (hK0 : 0 < K) (hK : ∀ i ∈ I, K ≤ (S i).card) (m : ℕ)
    (hm : (I.card : ℝ) * Real.exp (-(K * m / U.card)) < 1) :
    ∃ E ⊆ U, E.card ≤ m ∧ ∀ i ∈ I, ¬ Disjoint E (S i) := by
  rcases I.eq_empty_or_nonempty with hI | ⟨i₀, hi₀⟩
  · exact ⟨∅, empty_subset _, by simp, by simp [hI]⟩
  have hKU : K ≤ U.card :=
    (hK i₀ hi₀).trans (by exact_mod_cast card_le_card (hS i₀ hi₀))
  have hU : (0 : ℝ) < U.card := hK0.trans_le hKU
  obtain ⟨E, hEU, hEm, hE⟩ := greedy_iter U I S hS K hK0 hKU hK m
  refine ⟨E, hEU, hEm, ?_⟩
  have hbad : ((I.filter fun i => Disjoint E (S i)).card : ℝ) < 1 := by
    have hq : (U.card - K) / U.card ≤ Real.exp (-(K / U.card)) := by
      have := Real.add_one_le_exp (-(K / U.card))
      rw [sub_div, div_self hU.ne']; linarith
    have hq0 : 0 ≤ (U.card - K) / U.card := div_nonneg (by linarith) hU.le
    have hpow : ((U.card - K) / U.card) ^ m ≤ Real.exp (-(K * m / U.card)) := by
      calc ((U.card - K) / U.card) ^ m ≤ Real.exp (-(K / U.card)) ^ m := by gcongr
        _ = Real.exp (-(K * m / U.card)) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
    have hUm : (0 : ℝ) < U.card ^ m := by positivity
    calc ((I.filter fun i => Disjoint E (S i)).card : ℝ)
        ≤ I.card * ((U.card - K) / U.card) ^ m := by
          rw [div_pow, mul_div_assoc', le_div_iff₀ hUm]; exact hE
      _ ≤ I.card * Real.exp (-(K * m / U.card)) := by gcongr
      _ < 1 := hm
  have : (I.filter fun i => Disjoint E (S i)).card = 0 := by
    have := hbad; norm_cast at this; omega
  rw [card_eq_zero, filter_eq_empty_iff] at this
  exact this

end Hitting

section Crossing

variable {V : Type*} [DecidableEq V]

/-- The size bound behind Claim 14: a valid colouring has `abc ≥ h²(n - h)/2 ≥ h²n/3`. -/
lemma sq_mul_le_three_mul {a b c h n : ℕ} (ha : h ≤ a) (hb : h ≤ b) (hc : h ≤ c)
    (hs : n + 3 * h ≤ 2 * (a + b + c)) (hn : 3 * h ≤ n) : h ^ 2 * n ≤ 3 * (a * b * c) := by
  have ha' : (h : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (h : ℤ) ≤ b := by exact_mod_cast hb
  have hc' : (h : ℤ) ≤ c := by exact_mod_cast hc
  have hs' : (n : ℤ) + 3 * h ≤ 2 * (a + b + c) := by exact_mod_cast hs
  have hn' : 3 * (h : ℤ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℤ) ≤ h := by positivity
  have e1 := mul_nonneg (mul_nonneg (sub_nonneg.2 ha') (sub_nonneg.2 hb')) (h0.trans hc')
  have e2 := mul_nonneg h0 (mul_nonneg (by linarith : (0 : ℤ) ≤ a + b - 2 * h) (sub_nonneg.2 hc'))
  have e3 := mul_le_mul_of_nonneg_left hs' (sq_nonneg (h : ℤ))
  have e4 := mul_nonneg (sq_nonneg (h : ℤ)) (sub_nonneg.2 hn')
  have : (h : ℤ) ^ 2 * n ≤ 3 * (a * b * c) := by nlinarith
  exact_mod_cast this

end Crossing

section Main

variable {V : Type*} [DecidableEq V] [Fintype V]

instance (h : ℕ) (A B C : Finset V) : Decidable (ValidColoring h A B C) := by
  unfold ValidColoring; infer_instance

/-- The partial colouring encoded by `f : V → Fin 4` (colour `3` = uncoloured). -/
def colouring (f : V → Fin 4) : Finset V × Finset V × Finset V :=
  (univ.filter (f · = 0), univ.filter (f · = 1), univ.filter (f · = 2))

/-- The valid colourings for `h`, as a finset of triples. -/
def validColourings (h : ℕ) : Finset (Finset V × Finset V × Finset V) :=
  ((univ : Finset (V → Fin 4)).image colouring).filter fun p => ValidColoring h p.1 p.2.1 p.2.2

lemma card_validColourings_le (h : ℕ) :
    (validColourings h : Finset (Finset V × Finset V × Finset V)).card ≤ 4 ^ Fintype.card V := by
  refine (card_filter_le _ _).trans (card_image_le.trans ?_)
  simp

lemma mem_validColourings {h : ℕ} {A B C : Finset V} (hv : ValidColoring h A B C) :
    (A, B, C) ∈ validColourings h := by
  refine mem_filter.2 ⟨mem_image.2 ⟨fun v => if v ∈ A then (0 : Fin 4) else if v ∈ B then 1 else
    if v ∈ C then 2 else 3, mem_univ _, ?_⟩, hv⟩
  obtain ⟨hAB, hAC, hBC, -⟩ := hv
  simp only [colouring, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ext v <;> by_cases hA : v ∈ A <;> by_cases hB : v ∈ B <;>
    by_cases hC : v ∈ C <;> simp [hA, hB, hC]
  all_goals first
    | exact disjoint_left.1 hAB hA hB
    | exact disjoint_left.1 hAC hA hC
    | exact disjoint_left.1 hBC hB hC

/-- The numerical condition of the greedy argument for `m = ⌊n³/h²⌋`. -/
lemma numeric_bound {n h : ℕ} (h1 : 1 ≤ h) (h3 : 3 * h ≤ n) :
    (4 : ℝ) ^ n * Real.exp (-((h ^ 2 * n / 3 : ℝ) * ((n ^ 3 / h ^ 2 : ℕ) : ℝ) / (n.choose 3 : ℕ)))
      < 1 := by
  set m := n ^ 3 / h ^ 2 with hm
  have hn3 : 3 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast h1
  have hNpos : (0 : ℝ) < (n.choose 3 : ℕ) := by exact_mod_cast Nat.choose_pos hn3
  have hN : ((n.choose 3 : ℕ) : ℝ) ≤ n ^ 3 / 6 := by
    have := Nat.choose_le_pow_div (α := ℝ) 3 n
    simpa [Nat.factorial] using this
  -- `h² m > n³ - h²`
  have hmod := Nat.div_add_mod (n ^ 3) (h ^ 2)
  have hlt := Nat.mod_lt (n ^ 3) (by positivity : 0 < h ^ 2)
  have hm' : (n : ℝ) ^ 3 < h ^ 2 * m + h ^ 2 := by
    have : n ^ 3 < h ^ 2 * m + h ^ 2 := by rw [hm]; omega
    exact_mod_cast this
  -- `n³ ≥ 27 h²`
  have hcube : 27 * h ^ 2 ≤ n ^ 3 := by
    calc 27 * h ^ 2 ≤ 27 * h ^ 3 := by gcongr; omega
      _ = (3 * h) ^ 3 := by ring
      _ ≤ n ^ 3 := Nat.pow_le_pow_left h3 3
  have hcube' : (27 : ℝ) * h ^ 2 ≤ n ^ 3 := by exact_mod_cast hcube
  have hlog : Real.log 4 < 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  have hK : 0 ≤ (h ^ 2 * n / 3 : ℝ) * m := by positivity
  have key : n * Real.log 4 < (h ^ 2 * n / 3 : ℝ) * m / (n.choose 3 : ℕ) := by
    calc (n : ℝ) * Real.log 4 < 2 * h ^ 2 * m / n ^ 2 := by
          rw [lt_div_iff₀ (by positivity)]
          have hl0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          nlinarith [mul_le_mul_of_nonneg_left hlog.le (by positivity : (0 : ℝ) ≤ n ^ 3)]
      _ = (h ^ 2 * n / 3 : ℝ) * m / (n ^ 3 / 6) := by field_simp; ring
      _ ≤ (h ^ 2 * n / 3 : ℝ) * m / (n.choose 3 : ℕ) := div_le_div_of_nonneg_left hK hNpos hN
  have h4 : (4 : ℝ) ^ n = Real.exp (n * Real.log 4) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [h4, ← Real.exp_add, ← Real.exp_zero]
  exact Real.exp_lt_exp.2 (by linarith)

/-- **Theorem 7** of [JMS12] (the bound `Tₙ(h) = O(n³/h²)`, with constant `1`), proved by a
counting (greedy hitting-set) argument instead of Ramanujan graphs: for `1 ≤ h ≤ n/3` there is an
`h`-disjoint 3-uniform hypergraph on `n` vertices with at most `n³/h²` hyperedges. -/
theorem theorem_7 (n h : ℕ) (h1 : 1 ≤ h) (h3 : 3 * h ≤ n) :
    ∃ E : Finset (Finset (Fin n)), Uniform3 E ∧ HDisjoint E h ∧ E.card * h ^ 2 ≤ n ^ 3 := by
  set U := (univ : Finset (Fin n)).powersetCard 3
  set I := (validColourings h : Finset (Finset (Fin n) × Finset (Fin n) × Finset (Fin n)))
  set S := fun p : Finset (Fin n) × Finset (Fin n) × Finset (Fin n) => crossing p.1 p.2.1 p.2.2
  set K : ℝ := h ^ 2 * n / 3
  have hn : 0 < n := by omega
  have hK0 : 0 < K := by positivity
  have hval : ∀ p ∈ I, ValidColoring h p.1 p.2.1 p.2.2 := fun p hp => (mem_filter.1 hp).2
  have hS : ∀ p ∈ I, S p ⊆ U := fun p hp => by
    obtain ⟨hAB, hAC, hBC, -⟩ := hval p hp
    exact crossing_subset_univ hAB hAC hBC
  have hKS : ∀ p ∈ I, K ≤ (S p).card := fun p hp => by
    obtain ⟨hAB, hAC, hBC, ha, hb, hc, hs⟩ := hval p hp
    have := sq_mul_le_three_mul ha hb hc (by simpa using hs) h3
    simp only [S, card_crossing hAB hAC hBC, K]
    rw [div_le_iff₀ (by norm_num)]
    have : ((h ^ 2 * n : ℕ) : ℝ) ≤ ((3 * (p.1.card * p.2.1.card * p.2.2.card) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at this ⊢; linarith
  have hm : (I.card : ℝ) * Real.exp (-(K * ((n ^ 3 / h ^ 2 : ℕ) : ℝ) / U.card)) < 1 := by
    have hU : U.card = n.choose 3 := by simp [U]
    rw [hU]
    calc (I.card : ℝ) * Real.exp (-(K * ((n ^ 3 / h ^ 2 : ℕ) : ℝ) / (n.choose 3 : ℕ)))
        ≤ (4 : ℝ) ^ n * Real.exp (-(K * ((n ^ 3 / h ^ 2 : ℕ) : ℝ) / (n.choose 3 : ℕ))) := by
          gcongr
          have := card_validColourings_le (V := Fin n) h
          simp only [Fintype.card_fin] at this
          exact_mod_cast this
      _ < 1 := numeric_bound h1 h3
  obtain ⟨E, hEU, hEm, hE⟩ := exists_hitting U I S hS K hK0 hKS _ hm
  refine ⟨E, fun e he => (mem_powersetCard.1 (hEU he)).2, ?_, ?_⟩
  · intro A B C hv
    have hmem : (A, B, C) ∈ I := mem_validColourings hv
    exact rainbow_iff.2 (hE (A, B, C) hmem)
  · calc E.card * h ^ 2 ≤ (n ^ 3 / h ^ 2) * h ^ 2 := Nat.mul_le_mul_right _ hEm
      _ ≤ n ^ 3 := Nat.div_mul_le_self _ _

/-- **Theorem 7** of [JMS12], as a bound on `Tₙ(h)` (Definition 3): `Tₙ(h)·h² ≤ n³` for
`1 ≤ h ≤ n/3`. -/
theorem T_le {n h : ℕ} (h1 : 1 ≤ h) (h3 : 3 * h ≤ n) : T n h * h ^ 2 ≤ n ^ 3 := by
  obtain ⟨E, hU, hD, hE⟩ := theorem_7 n h h1 h3
  exact (Nat.mul_le_mul_right _ (Nat.sInf_le (show E.card ∈ {m | ∃ E : Finset (Finset (Fin n)),
    Uniform3 E ∧ HDisjoint E h ∧ E.card = m} from ⟨E, hU, hD, rfl⟩))).trans hE

end Main

end Podc.EquivocationPrice
