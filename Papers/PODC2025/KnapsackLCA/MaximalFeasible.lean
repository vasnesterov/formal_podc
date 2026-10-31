import Papers.PODC2025.KnapsackLCA.Defs

/-!
# No sublinear LCA for maximal feasible Knapsack (Theorem 3.4)

The hard distribution of the paper (weights scaled by `4`, so that they are integers): pick an
ordered pair `i ≠ j` uniformly, give item `i` weight `3`, item `j` weight `1` or `3` with
probability `1/2` each, all other items weight `0`; weight limit `4`; all profits `1/n`
(so the instances are normalised, as Definition 2.2 requires).

The paper draws `(i, j)` from `[n]²`, which allows `i = j` (ill-defined weights); we use ordered
pairs of distinct indices.

The paper's Lemma 3.5 argues *per query `k`* that the answer on the "default view" (only zero
weights seen) must be "yes", from the global error bound `1/5`; this does not follow (the error
is an average over `k`). We replace it by a joint counting argument: if `b_k` is the default
answer on query `k` and `m` of the `b_k` are "yes", the deterministic algorithm fails on
* `(i, j, light)` whenever `b_i = no` and `j` is not probed on the default run of `i`;
* `(i, j, heavy)` whenever `b_i = b_j` and neither probes the other,
which is a fraction at least `1/2 (1 - y + y² + (1-y)²) - O(q/n) ≥ 7/16 - O(q/n)` of the
distribution (`y = m/n`), for every choice of the `b_k` (`count_le`).

* `theorem_3_4`: global correctness with failure probability `1/5` (the paper's "probability of
  success at least 4/5") forces at least `n/11` queries, for every `n ≥ 2` — the paper's constant.
* `theorem_3_4_perQuery`: per-query correctness with failure probability `1/5` forces at least
  `n/40 - 1/5` queries.
-/

namespace Podc.KnapsackLCA

open Cslib Cslib.Probability.PMF Cslib.QueryTree

variable {Ω : Type*} {n : ℕ}

/-- The hard instance of Theorem 3.4 (weights scaled by 4): `w_i = 3`, `w_j = 3` if `heavy`
else `1`, other weights `0`, weight limit `4`, profits `1/n`. -/
noncomputable def hardInstance (i j : Fin n) (heavy : Bool) : Instance n where
  item ℓ := ((1 : ℝ) / n, if ℓ = i then 3 else if ℓ = j then (if heavy then 3 else 1) else 0)
  cap := 4

/-- What the algorithm sees on query `k` as long as it only probes zero-weight items. -/
noncomputable def defaultOracle (k : Fin n) : Fin n → ℝ × ℕ :=
  fun ℓ => ((1 : ℝ) / n, if ℓ = k then 3 else 0)

theorem hardInstance_normalized (i j : Fin n) (h : Bool) : (hardInstance i j h).Normalized := by
  have hn : (n : ℝ) ≠ 0 := by have := i.pos; positivity
  refine ⟨⟨fun ℓ => by simp [hardInstance, Instance.profit], fun ℓ => ?_⟩, ?_⟩
  · simp only [Instance.weight, hardInstance]; split_ifs <;> norm_num
  · simp [Instance.profit, hardInstance, hn]

theorem hardInstance_load {i j : Fin n} (hij : i ≠ j) (h : Bool) (C : Finset (Fin n)) :
    (hardInstance i j h).load C =
      (if i ∈ C then 3 else 0) + (if j ∈ C then (if h then 3 else 1) else 0) := by
  simp only [Instance.load, Instance.weight, hardInstance]
  rw [Finset.sum_congr rfl fun ℓ _ => (show (if ℓ = i then 3 else
      if ℓ = j then (if h then 3 else 1) else 0) =
      (if ℓ = i then 3 else 0) + (if ℓ = j then (if h then 3 else 1) else 0) by
    by_cases h1 : ℓ = i
    · subst h1; simp [hij]
    · simp [h1])]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

/-- Light case: every maximal feasible solution contains `i` (in fact all items). -/
theorem mem_of_light {i j : Fin n} (hij : i ≠ j) {C : Finset (Fin n)}
    (hC : (hardInstance i j false).IsMaximalFeasible C) : i ∈ C := by
  by_contra hi
  apply hC.2 i hi
  simp only [Instance.Feasible, hardInstance_load hij, Finset.mem_insert, true_or, ite_true]
  show _ ≤ 4
  simp only [Bool.false_eq_true, ite_false]
  split_ifs <;> omega

/-- Heavy case: a maximal feasible solution contains exactly one of `i`, `j`. -/
theorem mem_iff_of_heavy {i j : Fin n} (hij : i ≠ j) {C : Finset (Fin n)}
    (hC : (hardInstance i j true).IsMaximalFeasible C) : i ∈ C ↔ j ∉ C := by
  have h1 := hC.1
  simp only [Instance.Feasible, hardInstance_load hij] at h1
  change _ ≤ 4 at h1
  constructor
  · intro hi hj; simp [hi, hj] at h1
  · intro hj
    by_contra hi
    apply hC.2 i hi
    simp only [Instance.Feasible, hardInstance_load hij, Finset.mem_insert, true_or, ite_true,
      hj, Ne.symm hij, false_or]
    show 3 + 0 ≤ 4
    omega

theorem hardInstance_item_left {i j : Fin n} (h : Bool) {ℓ : Fin n} (hℓ : ℓ ≠ j) :
    (hardInstance i j h).item ℓ = defaultOracle i ℓ := by
  simp [hardInstance, defaultOracle, hℓ]

theorem hardInstance_item_right {i j : Fin n} (hij : i ≠ j) {ℓ : Fin n} (hℓ : ℓ ≠ i) :
    (hardInstance i j true).item ℓ = defaultOracle j ℓ := by
  by_cases h : ℓ = j
  · subst h; simp [hardInstance, defaultOracle, hℓ]
  · simp [hardInstance, defaultOracle, hℓ, h]

namespace LCA

variable (A : LCA n Ω)

/-- The answer on query `k` with seed `r` on the default view. -/
noncomputable def bit (r : Ω) (k : Fin n) : Bool := (A.run 4 r k).eval (defaultOracle k)

/-- The items probed on query `k` with seed `r` on the default view. -/
noncomputable def probes (r : Ω) (k : Fin n) : List (Fin n) :=
  (A.run 4 r k).queried (defaultOracle k)

/-- The answers to the two special queries `i`, `j` are consistent with one maximal feasible
solution of the hard instance. -/
def LocalOK (r : Ω) (i j : Fin n) (h : Bool) : Prop :=
  ∃ C, (hardInstance i j h).IsMaximalFeasible C ∧
    (A.answer (hardInstance i j h) r i = true ↔ i ∈ C) ∧
    (A.answer (hardInstance i j h) r j = true ↔ j ∈ C)

theorem answer_left {i j : Fin n} (h : Bool) {r : Ω} (hj : j ∉ A.probes r i) :
    A.answer (hardInstance i j h) r i = A.bit r i := by
  refine eval_eq_of_agree _ _ _ fun ℓ hℓ => hardInstance_item_left h ?_
  rintro rfl; exact hj hℓ

theorem answer_right {i j : Fin n} (hij : i ≠ j) {r : Ω} (hi : i ∉ A.probes r j) :
    A.answer (hardInstance i j true) r j = A.bit r j := by
  refine eval_eq_of_agree _ _ _ fun ℓ hℓ => hardInstance_item_right hij ?_
  rintro rfl; exact hi hℓ

theorem localOK_light {r : Ω} {i j : Fin n} (hij : i ≠ j) (h : A.LocalOK r i j false) :
    A.bit r i = true ∨ j ∈ A.probes r i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hC, hi, -⟩ := h
  have := hi.2 (mem_of_light hij hC)
  rw [answer_left A false hcon.2] at this
  simp [this] at hcon

theorem localOK_heavy {r : Ω} {i j : Fin n} (hij : i ≠ j) (h : A.LocalOK r i j true) :
    A.bit r i ≠ A.bit r j ∨ j ∈ A.probes r i ∨ i ∈ A.probes r j := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hb, hpj, hpi⟩ := hcon
  obtain ⟨C, hC, hi, hj⟩ := h
  rw [answer_left A true hpj] at hi
  rw [answer_right A hij hpi] at hj
  have := mem_iff_of_heavy hij hC
  cases hbi : A.bit r i <;> rw [hbi] at hi <;> rw [← hb, hbi] at hj <;> simp_all

/-- Weight of a hard instance in the uniform distribution (up to normalisation): `1` for
`i ≠ j`, `0` otherwise. -/
noncomputable def pairWeight (x : Fin n × Fin n × Bool) : ℝ := if x.1 = x.2.1 then 0 else 1

/-- **Counting core of Theorem 3.4.** For every seed, the number of hard instances on which the
two special answers are consistent with a maximal feasible solution is at most
`2 n (n-1) - (7n² - 10n - 1)/8 + 3 n q`. -/
theorem count_le {q : ℕ} (hq : A.QueryBound q) (r : Ω) :
    ∑ x : Fin n × Fin n × Bool, {r | A.LocalOK r x.1 x.2.1 x.2.2}.indicator
        (fun _ => pairWeight x) r ≤
      2 * ((n : ℝ) ^ 2 - n) - (7 * (n : ℝ) ^ 2 - 10 * n - 1) / 8 + 3 * n * q := by
  classical
  set x : Fin n → ℝ := fun i => if A.bit r i then 1 else 0
  set p : Fin n → Fin n → ℝ := fun i j => if j ∈ A.probes r i then 1 else 0
  set m : ℝ := ∑ i, x i
  have hx01 : ∀ i, x i = 0 ∨ x i = 1 := fun i => by simp only [x]; split_ifs <;> simp
  have hp0 : ∀ i j, 0 ≤ p i j := fun i j => by simp only [p]; split_ifs <;> norm_num
  -- pointwise bounds
  set g : Fin n → Fin n → ℝ := fun i j => x i * x j + (1 - x i) * (1 - x j)
  have hlight : ∀ i j, {r | A.LocalOK r i j false}.indicator (fun _ => pairWeight (i, j, false)) r
      ≤ (if i = j then 0 else x i) + p i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have h0 : pairWeight (i, i, false) = 0 := by simp [pairWeight]
      rw [Set.indicator_apply, h0, ite_self]; simpa using hp0 i i
    · rw [Set.indicator_apply]
      split_ifs with hok
      · rcases A.localOK_light hij hok with hb | hp
        · simp [pairWeight, hij, x, hb, hp0]
        · simp only [pairWeight, hij, x, p, hp, ite_false, ite_true]
          split_ifs <;> norm_num
      · rcases hx01 i with h | h <;> rw [h] <;> linarith [hp0 i j]
  have hheavy : ∀ i j, {r | A.LocalOK r i j true}.indicator (fun _ => pairWeight (i, j, true)) r
      ≤ (if i = j then 0 else 1 - g i j) + p i j + p j i := by
    intro i j
    have hg : ∀ i j, 0 ≤ 1 - g i j ∧ 1 - g i j ≤ 1 := fun i j => by
      rcases hx01 i with h | h <;> rcases hx01 j with h' | h' <;> simp [g, h, h']
    by_cases hij : i = j
    · subst hij
      have h0 : pairWeight (i, i, true) = 0 := by simp [pairWeight]
      rw [Set.indicator_apply, h0, ite_self]; simpa using add_nonneg (hp0 i i) (hp0 i i)
    · rw [Set.indicator_apply]
      split_ifs with hok
      · rcases A.localOK_heavy hij hok with hb | hp | hp
        · have : 1 - g i j = 1 := by
            simp only [g, x]
            cases hbi : A.bit r i <;> cases hbj : A.bit r j <;> simp_all
          simp only [pairWeight, hij, this, ite_false]; linarith [hp0 i j, hp0 j i]
        · simp only [pairWeight, hij, p, hp, ite_false, ite_true]
          linarith [hg i j, hp0 j i]
        · simp only [pairWeight, hij, p, hp, ite_false, ite_true]
          linarith [hg i j, hp0 i j]
      · linarith [hg i j, hp0 i j, hp0 j i]
  -- probes
  have hprow : ∀ i, ∑ j, p i j ≤ q := by
    intro i
    simp only [p]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h1 : (Finset.univ.filter fun j => j ∈ A.probes r i).card ≤ q := by
      calc _ ≤ (A.probes r i).toFinset.card := Finset.card_le_card fun j hj => by
              simp only [Finset.mem_filter] at hj; simpa using hj.2
        _ ≤ (A.probes r i).length := List.toFinset_card_le _
        _ = (A.run 4 r i).cost (defaultOracle i) := length_queried _ _
        _ ≤ q := hq _ _ _ _
    exact_mod_cast h1
  have hpsum : ∑ i, ∑ j, p i j ≤ n * q := by
    calc _ ≤ ∑ _i : Fin n, (q : ℝ) := Finset.sum_le_sum fun i _ => hprow i
      _ = n * q := by simp
  have hpsum' : ∑ i, ∑ j, p j i ≤ n * q := by rw [Finset.sum_comm]; exact hpsum
  -- the main sums
  have hS1 : ∑ i : Fin n, ∑ j : Fin n, (if i = j then 0 else x i) = m * (n - 1) := by
    have : ∀ i : Fin n, ∑ j : Fin n, (if i = j then 0 else x i) = x i * (n - 1) := fun i => by
      rw [Finset.sum_congr rfl fun j _ => (show (if i = j then 0 else x i) =
        x i - (if i = j then x i else 0) by split_ifs <;> ring)]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]; simp; ring
    simp only [this, m, Finset.sum_mul]
  have hS2 : ∑ i : Fin n, ∑ j : Fin n, (if i = j then 0 else 1 - g i j) =
      n ^ 2 - (m ^ 2 + (n - m) ^ 2) := by
    have hgii : ∀ i, g i i = 1 := fun i => by rcases hx01 i with h | h <;> simp [g, h]
    have : ∀ i : Fin n, ∑ j : Fin n, (if i = j then 0 else 1 - g i j) = ∑ j, (1 - g i j) := by
      intro i
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h
      · subst h; simp [hgii]
      · rfl
    simp only [this, Finset.sum_sub_distrib, g, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [m]
    ring
  -- assemble
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  have hsum : ∑ i : Fin n, ∑ j : Fin n,
      ({r | A.LocalOK r i j true}.indicator (fun _ => pairWeight (i, j, true)) r +
        {r | A.LocalOK r i j false}.indicator (fun _ => pairWeight (i, j, false)) r) ≤
      ∑ i : Fin n, ∑ j : Fin n, ((if i = j then 0 else 1 - g i j) + (if i = j then 0 else x i)
        + 2 * p i j + p j i) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    linarith [hlight i j, hheavy i j]
  refine hsum.trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hS1, hS2]
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun i _ => by rcases hx01 i with h | h <;> simp [h]
  nlinarith [sq_nonneg (4 * ((n : ℝ) - m) - (n + 1)), hpsum, hpsum']

/-- **Yao step of Theorem 3.4.** If on every hard instance the two special answers are
consistent with a maximal feasible solution with probability `≥ 1 - ε`, then
`(1 - ε) · 2n(n-1) ≤ 2n(n-1) - (7n² - 10n - 1)/8 + 3nq`. -/
theorem yao_bound {q : ℕ} (hq : A.QueryBound q) (ε : ℝ)
    (hgood : ∀ i j h, i ≠ j → 1 - ε ≤ probReal A.seed {r | A.LocalOK r i j h}) :
    (1 - ε) * (2 * ((n : ℝ) ^ 2 - n)) ≤
      2 * ((n : ℝ) ^ 2 - n) - (7 * (n : ℝ) ^ 2 - 10 * n - 1) / 8 + 3 * n * q := by
  classical
  have hw : ∀ x : Fin n × Fin n × Bool, 0 ≤ pairWeight x := fun x => by
    simp only [pairWeight]; split_ifs <;> norm_num
  have hU := sum_mul_probReal_le A.seed Finset.univ pairWeight hw
    (fun x => {r | A.LocalOK r x.1 x.2.1 x.2.2}) _ (A.count_le hq)
  have hlow : ∀ x : Fin n × Fin n × Bool, (1 - ε) * pairWeight x ≤
      pairWeight x * probReal A.seed {r | A.LocalOK r x.1 x.2.1 x.2.2} := by
    rintro ⟨i, j, h⟩
    simp only [pairWeight]
    split_ifs with hij
    · simp
    · simpa using hgood i j h hij
  have htot : ∑ x : Fin n × Fin n × Bool, pairWeight x = 2 * ((n : ℝ) ^ 2 - n) := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    have e : ∀ i j : Fin n, pairWeight (i, j, true) + pairWeight (i, j, false) =
        2 - (if i = j then 2 else 0) := by
      intro i j; simp only [pairWeight]; split_ifs <;> norm_num
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  calc (1 - ε) * (2 * ((n : ℝ) ^ 2 - n)) = ∑ x, (1 - ε) * pairWeight x := by
        rw [← Finset.mul_sum, htot]
    _ ≤ ∑ x, pairWeight x * probReal A.seed {r | A.LocalOK r x.1 x.2.1 x.2.2} :=
        Finset.sum_le_sum fun x _ => hlow x
    _ ≤ _ := hU

end LCA

/-- **Theorem 3.4** (global correctness, the reading used in the paper's proof). An LCA that,
on every normalised instance, gives access to a maximal feasible solution with success
probability at least `4/5` (failure probability `1/5`) makes at least `n/11` queries, for every
`n ≥ 2`. (The paper writes "`(t(n), 4/5)`-LCA", i.e. failure probability `4/5`; its proof uses
success probability `4/5`.) -/
theorem theorem_3_4 (hn : 2 ≤ n) (A : LCA n Ω) {q : ℕ} (hq : A.QueryBound q)
    (hA : A.CorrectStrong {I | I.Normalized} (fun I C => I.IsMaximalFeasible C) (1 / 5)) :
    (n : ℝ) / 11 ≤ q := by
  have key := A.yao_bound hq (1 / 5) fun i j h hij => by
    refine (hA _ (hardInstance_normalized i j h)).trans (probReal_mono _ fun r hr => ?_)
    exact ⟨_, hr, by simp [LCA.solution], by simp [LCA.solution]⟩
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  by_contra hlt
  push Not at hlt
  rcases Nat.eq_zero_or_pos q with h0 | hpos
  · rw [h0] at key; push_cast at key; nlinarith
  · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hpos
    nlinarith

/-- **Theorem 3.4** (per-query correctness, Definition 2.2 read query by query). An LCA that,
on every normalised instance, answers every single query consistently with a maximal feasible
solution with failure probability `1/5` makes at least `n/40 - 1/5` queries. -/
theorem theorem_3_4_perQuery (hn : 1 ≤ n) (A : LCA n Ω) {q : ℕ} (hq : A.QueryBound q)
    (hA : A.Correct {I | I.Normalized} (fun I C => I.IsMaximalFeasible C) (1 / 5)) :
    (n : ℝ) / 40 - 1 / 5 ≤ q := by
  have key := A.yao_bound hq (2 / 5) fun i j h hij => by
    obtain ⟨C, hC⟩ := hA _ (hardInstance_normalized i j h)
    have h2 := probReal_add_le_inter A.seed (E := {r | (hardInstance i j h).IsMaximalFeasible
      (C r) ∧ (A.answer (hardInstance i j h) r i = true ↔ i ∈ C r)})
      (F := {r | (hardInstance i j h).IsMaximalFeasible (C r) ∧
        (A.answer (hardInstance i j h) r j = true ↔ j ∈ C r)})
    have h3 : probReal A.seed ({r | (hardInstance i j h).IsMaximalFeasible (C r) ∧
        (A.answer (hardInstance i j h) r i = true ↔ i ∈ C r)} ∩
        {r | (hardInstance i j h).IsMaximalFeasible (C r) ∧
        (A.answer (hardInstance i j h) r j = true ↔ j ∈ C r)}) ≤
        probReal A.seed {r | A.LocalOK r i j h} :=
      probReal_mono _ fun r hr => ⟨C r, hr.1.1, hr.1.2, hr.2.2⟩
    linarith [hC i, hC j]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  by_contra hlt
  push Not at hlt
  nlinarith

end Podc.KnapsackLCA
