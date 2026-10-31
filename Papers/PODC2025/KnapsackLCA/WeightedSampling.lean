import Mathlib
import Podc.Computability.QueryComplexity.QueryTree

/-!
# Section 4: the weighted-sampling LCA `LCA-KP` fails on instances with equal efficiencies

We model the deterministic part of Algorithm 2 (`LCA-KP`) with Algorithm 3 (`CONVERT-GREEDY`),
given the random data of one run: the first weighted sample `R` (Line 1) and the outputs
`ẽ_k` of the `t` calls to `rQuantile` (Line 10). The only property of `rQuantile` the paper
uses is its accuracy guarantee (Theorem 4.5): `ẽ_k` is a `τ`-approximate `(1 - kq)`-quantile of
the profit-weighted efficiency distribution of `S(I) ∪ G(I)`, i.e.
`Pr[eff ≤ ẽ_k] ≥ 1 - kq - τ` and `Pr[eff ≥ ẽ_k] ≥ kq - τ` (as used in the proof of Lemma 4.6).

**Counterexample.** `uniformInstance N`: `N` items, each of (normalised) profit and weight
`1/N` (integer weights `1`, weight limit `N/2` before normalisation), weight limit `1/2`.
For `ε = 1/m`, `m ≥ 2` (`m ≥ 30` in `theorem_4_1_false`), `N ≥ m²`, all items are small with efficiency `1`, so the efficiency
distribution is a point mass:
* no equally partitioning sequence (Definition 4.3) of length `≥ 1` exists
  (`no_eps_uniform`), refuting Lemma 4.6 (which claims that the computed sequence is an EPS with
  probability `≥ 1 - 13ε/36`);
* whenever the quantiles are accurate, every `ẽ_k` equals `1`, every item of the constructed
  instance `Ĩ` has efficiency `1`, so no index `k` has `ẽ_k > p_j/w_j`, `e_small = -1`, and
  `LCA-KP` answers "no" to every query (`answerKP_uniform`), whatever the order chosen by the
  sorting step;
* the empty solution is not a `(1/2, 6ε)`-approximation (`OPT ≥ 1/2 - 1/(2N)`);
* hence (`theorem_4_1_false`): under the accuracy guarantee of Theorem 4.5 (failure
  probability `≤ tβ ≤ ε/36` per run), no seed-dependent `(1/2, 6ε)`-approximate solution is
  consistent with the answers with probability `≥ 1 - ε` per query, contradicting
  Theorem 4.1 / Lemma 4.9 (already in the weakest, per-query reading; the global reading is
  stronger).
-/

namespace Podc.KnapsackLCA.Sec4

open Cslib.Probability.PMF

/-- A normalised Knapsack instance of Section 4 with real profits and weights. -/
structure RInstance (n : ℕ) where
  /-- Profits. -/
  p : Fin n → ℝ
  /-- Weights. -/
  w : Fin n → ℝ
  /-- Weight limit. -/
  K : ℝ

namespace RInstance

variable {n : ℕ} (I : RInstance n) (ε : ℝ)

/-- Efficiency `p/w` of an item. -/
noncomputable def eff (i : Fin n) : ℝ := I.p i / I.w i

/-- Large items `L(I)`: profit `> ε²`. -/
def IsLarge (i : Fin n) : Prop := ε ^ 2 < I.p i

/-- Small items `S(I)`: profit `≤ ε²`, efficiency `≥ ε²`. -/
def IsSmall (i : Fin n) : Prop := I.p i ≤ ε ^ 2 ∧ ε ^ 2 ≤ I.eff i

/-- Total profit of a set. -/
def profitOf (C : Finset (Fin n)) : ℝ := ∑ i ∈ C, I.p i

/-- Feasibility. -/
def Feasible (C : Finset (Fin n)) : Prop := ∑ i ∈ C, I.w i ≤ I.K

/-- `(α, β)`-approximate solution (Definition 2.1). -/
def IsApproxSol (α β : ℝ) (C : Finset (Fin n)) : Prop :=
  I.Feasible C ∧ ∀ C', I.Feasible C' → α * I.profitOf C' - β ≤ I.profitOf C

open scoped Classical in
/-- Profit-weighted probability that an item of `S(I) ∪ G(I)` (= not large) has efficiency
satisfying `P`: the distribution `D` that `rQuantile` samples from. -/
noncomputable def effMass (P : ℝ → Prop) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => ¬ I.IsLarge ε i ∧ P (I.eff i)), I.p i) /
    ∑ i ∈ Finset.univ.filter (fun i => ¬ I.IsLarge ε i), I.p i

/-- `v` is a `τ`-approximate `π`-quantile of `D` (Theorem 4.5, as used in Lemma 4.6). -/
def IsApproxQuantile (τ π v : ℝ) : Prop :=
  π - τ ≤ I.effMass ε (· ≤ v) ∧ 1 - π - τ ≤ I.effMass ε (v ≤ ·)

open scoped Classical in
/-- The sets `A_k(I)` for an efficiency sequence `e_1, …, e_t` (Section 4). -/
noncomputable def Aset (e : ℕ → ℝ) (t k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => I.IsSmall ε i ∧
    if t = 0 then True
    else if k = 0 then e 1 ≤ I.eff i
    else if k < t then I.eff i < e k ∧ e (k + 1) ≤ I.eff i
    else I.eff i < e t

/-- **Definition 4.3** (equally partitioning sequence). -/
def IsEPS (e : ℕ → ℝ) (t : ℕ) : Prop :=
  (∀ k < t, ε ≤ I.profitOf (I.Aset ε e t k) ∧ I.profitOf (I.Aset ε e t k) < ε + ε ^ 2) ∧
    I.profitOf (I.Aset ε e t t) < ε + ε ^ 2

end RInstance

/-! ### Algorithm 2 (`LCA-KP`) and Algorithm 3 (`CONVERT-GREEDY`) -/

/-- An item of the constructed instance `Ĩ`: profit, weight, and its index in `I`
(`none` for the synthetic representatives of small items). -/
structure TItem (n : ℕ) where
  /-- Profit. -/
  p : ℝ
  /-- Weight. -/
  w : ℝ
  /-- Index in the original instance. -/
  src : Option (Fin n)

/-- Efficiency of an item of `Ĩ`. -/
noncomputable def TItem.eff {n : ℕ} (x : TItem n) : ℝ := x.p / x.w

variable {n : ℕ} (ε : ℝ) (I : RInstance n)

open scoped Classical in
/-- Lines 1–3: the large items of the sample `R`, without duplicates (`L(Ĩ)`). -/
noncomputable def largeOf (R : List (Fin n)) : List (Fin n) :=
  (R.filter fun i => decide (I.IsLarge ε i)).dedup

/-- `p(L(Ĩ))`. -/
noncomputable def pL (R : List (Fin n)) : ℝ := ((largeOf ε I R).map I.p).sum

/-- Line 5: `q`. -/
noncomputable def qParam (R : List (Fin n)) : ℝ := (ε + ε ^ 2 / 2) / (1 - pL ε I R)

/-- Line 5: `t = ⌊1/q⌋`. -/
noncomputable def tParam (R : List (Fin n)) : ℕ := ⌊1 / qParam ε I R⌋₊

/-- Line 5: `τ = ε²/5`. -/
noncomputable def tau : ℝ := ε ^ 2 / 5

open scoped Classical in
/-- Lines 4 and 11–17: the length `t'` of the sequence `EPS` (`0` in the `else` branch). -/
noncomputable def tPrime (R : List (Fin n)) (e : ℕ → ℝ) : ℕ :=
  if ε ≤ 1 - pL ε I R then
    (if e (tParam ε I R) < ε ^ 2 then tParam ε I R - 1 else tParam ε I R)
  else 0

/-- Line 18 (step 3 of the `Ĩ`-construction): the items of `Ĩ`: the large items of `R`, and
`⌊1/ε⌋` copies of `(ε², ε²/ẽ_{k+1})` for `k = 0, …, t'-1`. -/
noncomputable def tildeItems (R : List (Fin n)) (e : ℕ → ℝ) : List (TItem n) :=
  (largeOf ε I R).map (fun i => ⟨I.p i, I.w i, some i⟩) ++
    (List.range (tPrime ε I R e)).flatMap fun k =>
      List.replicate ⌊1 / ε⌋₊ ⟨ε ^ 2, ε ^ 2 / e (k + 1), none⟩

/-- Output of `CONVERT-GREEDY`: `Index_large`, `e_small` (`none` encodes `-1`), `B_indicator`. -/
structure CGOut (n : ℕ) where
  /-- `Index_large`. -/
  large : Finset (Fin n)
  /-- `e_small`, `none` for `-1`. -/
  esmall : Option ℝ
  /-- `B_indicator`. -/
  bind : Bool

/-- Total weight of the first `j` items. -/
noncomputable def prefixW (l : List (TItem n)) (j : ℕ) : ℝ := ((l.take j).map TItem.w).sum

/-- Total profit of the first `j` items. -/
noncomputable def prefixP (l : List (TItem n)) (j : ℕ) : ℝ := ((l.take j).map TItem.p).sum

/-- Line 2 of Algorithm 3: the largest `j ≤ |S̃|` such that the first `j` items have weight
`≤ K` (`0` if none). -/
noncomputable def cgJ (K : ℝ) (l : List (TItem n)) : ℕ :=
  Nat.findGreatest (fun j => prefixW l j ≤ K) l.length

/-- Line 3 of Algorithm 3: the largest `k ≤ t'` with `ẽ_k > p_j/w_j` (`0` if there is none,
or if `j = 0`). -/
noncomputable def cgK (e : ℕ → ℝ) (t' : ℕ) (l : List (TItem n)) (j : ℕ) : ℕ :=
  match (if j = 0 then none else l[j - 1]?) with
  | none => 0
  | some x => Nat.findGreatest (fun k => 1 ≤ k ∧ x.eff < e k) t'

open scoped Classical in
/-- **Algorithm 3** on the sorted item list `l` of `Ĩ` (weight limit `K`) and the sequence
`ẽ_1, …, ẽ_{t'}`. -/
noncomputable def convertGreedy (K : ℝ) (e : ℕ → ℝ) (t' : ℕ) (l : List (TItem n)) :
    CGOut n :=
  if cgJ K l = l.length ∨ (l[cgJ K l]?.map TItem.p).getD 0 ≤ prefixP l (cgJ K l) then
    ⟨((l.take (cgJ K l)).filterMap fun x => if ε ^ 2 < x.p then x.src else none).toFinset,
      if 3 ≤ cgK e t' l (cgJ K l) then some (e (cgK e t' l (cgJ K l) - 2)) else none, false⟩
  else
    ⟨((l[cgJ K l]?).bind TItem.src).toFinset, none, true⟩

/-- If every item of `Ĩ` has efficiency `v` and no `ẽ_k` (`1 ≤ k ≤ t'`) exceeds `v`, then the
index `k` of Line 3 is `0`. -/
theorem cgK_eq_zero (e : ℕ → ℝ) (t' : ℕ) (l : List (TItem n)) (j : ℕ) (v : ℝ)
    (hl : ∀ x ∈ l, x.eff = v) (he : ∀ k, 1 ≤ k → k ≤ t' → e k ≤ v) : cgK e t' l j = 0 := by
  unfold cgK
  split
  · rfl
  · rename_i x hx
    have hxl : x ∈ l := by
      split_ifs at hx
      exact List.mem_of_getElem? hx
    rw [Nat.findGreatest_eq_zero_iff]
    intro k hk0 hkt hk
    have := he k hk.1 hkt
    rw [hl x hxl] at hk
    linarith [hk.2]

/-- Under the same hypotheses, `CONVERT-GREEDY` returns `e_small = -1`. -/
theorem convertGreedy_esmall (K : ℝ) (e : ℕ → ℝ) (t' : ℕ) (l : List (TItem n)) (v : ℝ)
    (hl : ∀ x ∈ l, x.eff = v) (he : ∀ k, 1 ≤ k → k ≤ t' → e k ≤ v) :
    (convertGreedy ε K e t' l).esmall = none := by
  unfold convertGreedy
  rw [cgK_eq_zero e t' l _ v hl he]
  split_ifs <;> first | rfl | omega

open scoped Classical in
/-- **Algorithm 2** (`LCA-KP`), Lines 18–24, given the random data of the run: the sample `R`,
the `rQuantile` outputs `e`, and the order `l` in which Line 1 of Algorithm 3 sorts `Ĩ`. -/
noncomputable def answerKP (R : List (Fin n)) (e : ℕ → ℝ) (l : List (TItem n)) (i : Fin n) :
    Bool :=
  let out := convertGreedy ε I.K e (tPrime ε I R e) l
  if ε ^ 2 < I.p i then decide (i ∈ out.large)
  else match out.esmall with
    | some v => decide (v ≤ I.eff i)
    | none => false

/-- The `rQuantile` outputs of a run are accurate (Theorem 4.5 for each of the `t` calls). -/
def Accurate (R : List (Fin n)) (e : ℕ → ℝ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ tParam ε I R →
    I.IsApproxQuantile ε (tau ε) (1 - k * qParam ε I R) (e k)

/-! ### The counterexample -/

/-- `N` identical items of profit and weight `1/N`; weight limit `1/2`. -/
noncomputable def uniformInstance (N : ℕ) : RInstance N where
  p _ := 1 / N
  w _ := 1 / N
  K := 1 / 2

section Uniform

variable {N : ℕ}

theorem uniform_eff (hN : 0 < N) (i : Fin N) : (uniformInstance N).eff i = 1 := by
  have : (N : ℝ) ≠ 0 := by positivity
  simp [RInstance.eff, uniformInstance, this]

theorem uniform_not_large {ε : ℝ} (hN : 1 ≤ ε ^ 2 * N) (i : Fin N) :
    ¬ (uniformInstance N).IsLarge ε i := by
  have hN0 : (0 : ℝ) < N := by
    by_contra h; push Not at h; nlinarith [sq_nonneg ε]
  simp only [RInstance.IsLarge, uniformInstance, not_lt]
  rw [div_le_iff₀ hN0]; linarith

theorem uniform_small {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hN : 1 ≤ ε ^ 2 * N) (i : Fin N) :
    (uniformInstance N).IsSmall ε i := by
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hN; linarith
    · exact h
  refine ⟨not_lt.1 (uniform_not_large hN i), ?_⟩
  rw [uniform_eff hN0]; nlinarith

open scoped Classical in
theorem uniform_effMass {ε : ℝ} (hN : 1 ≤ ε ^ 2 * N) (P : ℝ → Prop) :
    (uniformInstance N).effMass ε P = if P 1 then 1 else 0 := by
  classical
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hN; linarith
    · exact h
  have hNr : (N : ℝ) ≠ 0 := by positivity
  simp only [RInstance.effMass, uniform_eff hN0, uniform_not_large hN, not_false_eq_true,
    true_and, Finset.filter_true]
  split_ifs with h
  · simp [h, uniformInstance, hNr]
  · simp [h]

/-- In the uniform instance, an accurate quantile for `π ∈ (τ, 1 - τ)` equals `1`. -/
theorem uniform_quantile_eq_one {ε τ π v : ℝ} (hN : 1 ≤ ε ^ 2 * N)
    (h1 : τ < π) (h2 : π < 1 - τ) (hv : (uniformInstance N).IsApproxQuantile ε τ π v) :
    v = 1 := by
  obtain ⟨ha, hb⟩ := hv
  rw [uniform_effMass hN] at ha hb
  split_ifs at ha hb <;> linarith

/-- **Lemma 4.6 is false.** In the uniform instance (with `ε + ε² ≤ 1`), no sequence of length
`t ≥ 1` is an equally partitioning sequence: every `A_k(I)` is either empty or everything. -/
theorem no_eps_uniform {ε : ℝ} (hε : 0 < ε) (hε1 : ε + ε ^ 2 ≤ 1) (hN : 1 ≤ ε ^ 2 * N)
    (e : ℕ → ℝ) {t : ℕ} (ht : 1 ≤ t) : ¬ (uniformInstance N).IsEPS ε e t := by
  classical
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hN; linarith
    · exact h
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hε1' : ε ≤ 1 := by nlinarith
  have hsmall := uniform_small hε hε1' hN
  have heff := uniform_eff hN0
  rintro ⟨hlow, htop⟩
  have hA0 := hlow 0 (by omega)
  have hne : ∀ k < t, (( uniformInstance N).Aset ε e t k).Nonempty := by
    intro k hk
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := (hlow k hk).1
    rw [h] at this
    simp [RInstance.profitOf] at this; linarith
  obtain ⟨i₀, hi₀⟩ := hne 0 (by omega)
  have ht0 : t ≠ 0 := by omega
  simp only [RInstance.Aset, Finset.mem_filter, Finset.mem_univ, true_and, ht0, ite_false,
    ite_true, heff] at hi₀
  -- `A_0` is everything
  have hA0all : (uniformInstance N).Aset ε e t 0 = Finset.univ := by
    ext i
    simp [RInstance.Aset, hsmall i, ht0, heff, hi₀.2]
  by_cases ht1 : t = 1
  · subst ht1
    have := hA0.2
    rw [hA0all] at this
    simp [RInstance.profitOf, uniformInstance, hNr] at this
    linarith
  · obtain ⟨i₁, hi₁⟩ := hne 1 (by omega)
    simp only [RInstance.Aset, Finset.mem_filter, Finset.mem_univ, true_and, ht0, ite_false,
      one_ne_zero, heff] at hi₁
    rw [ite_eq_left (by omega)] at hi₁
    linarith [hi₁.2.1, hi₀.2]

end Uniform

/-! ### `LCA-KP` answers "no" to every query of the uniform instance -/

section Answer

variable {N m : ℕ}

theorem largeOf_uniform {ε : ℝ} (hN : 1 ≤ ε ^ 2 * N) (R : List (Fin N)) :
    largeOf ε (uniformInstance N) R = [] := by
  classical
  simp [largeOf, uniform_not_large hN]

/-- With `ε = 1/m` (`m ≥ 2`) and no large item (`q = ε + ε²/2`), every `1 ≤ k ≤ ⌊1/q⌋` has
`τ < 1 - kq < 1 - τ`. -/
theorem quantile_range (hm : 2 ≤ m) {q : ℝ} (hq : q = 1 / (m : ℝ) + (1 / (m : ℝ)) ^ 2 / 2)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ ⌊1 / q⌋₊) :
    tau (1 / (m : ℝ)) < 1 - k * q ∧ 1 - k * q < 1 - tau (1 / (m : ℝ)) := by
  have hM : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hq' : q = (2 * (m : ℝ) + 1) / (2 * (m : ℝ) ^ 2) := by rw [hq]; field_simp
  have htau : tau (1 / (m : ℝ)) = 1 / (5 * (m : ℝ) ^ 2) := by simp only [tau]; field_simp
  have hinv : 1 / q < (m : ℝ) := by
    rw [hq', one_div_div, div_lt_iff₀ (by positivity)]; nlinarith
  have hq0 : 0 < q := by rw [hq']; positivity
  have htm : ⌊1 / q⌋₊ < m := by
    have : (⌊1 / q⌋₊ : ℝ) < (m : ℝ) := lt_of_le_of_lt (Nat.floor_le (by positivity)) hinv
    exact_mod_cast this
  have hkm : (k : ℝ) ≤ (m : ℝ) - 1 := by
    have : k + 1 ≤ m := by omega
    have : ((k + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  rw [htau]
  have e1 : ((m : ℝ) - 1) * ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) ^ 2)) + 1 / (5 * (m : ℝ) ^ 2) =
      1 - (5 * (m : ℝ) + 3) / (10 * (m : ℝ) ^ 2) := by field_simp; ring
  have e2 : (2 * (m : ℝ) + 1) / (2 * (m : ℝ) ^ 2) - 1 / (5 * (m : ℝ) ^ 2) = (10 * (m : ℝ) + 3) / (10 * (m : ℝ) ^ 2) := by
    field_simp; ring
  have p1 : 0 < (5 * (m : ℝ) + 3) / (10 * (m : ℝ) ^ 2) := by positivity
  have p2 : 0 < (10 * (m : ℝ) + 3) / (10 * (m : ℝ) ^ 2) := by positivity
  have m1 : (k : ℝ) * q ≤ ((m : ℝ) - 1) * q := mul_le_mul_of_nonneg_right hkm hq0.le
  have m2 : 1 * q ≤ (k : ℝ) * q := mul_le_mul_of_nonneg_right hk1' hq0.le
  rw [hq'] at m1 m2 ⊢
  constructor <;> linarith

/-- **`LCA-KP` answers "no" to every query of the uniform instance** (`ε = 1/m`, `m ≥ 2`,
`N ≥ m²`), on every run whose `rQuantile` outputs are accurate, for every sample `R` and every
order `l` of the items of `Ĩ` (in particular every order sorted by efficiency). -/
theorem answerKP_uniform (hm : 2 ≤ m) (hN : m ^ 2 ≤ N) (R : List (Fin N)) (e : ℕ → ℝ)
    (he : Accurate (1 / (m : ℝ)) (uniformInstance N) R e) (l : List (TItem N))
    (hl : ∀ x ∈ l, x ∈ tildeItems (1 / (m : ℝ)) (uniformInstance N) R e) (i : Fin N) :
    answerKP (1 / (m : ℝ)) (uniformInstance N) R e l i = false := by
  classical
  set ε : ℝ := 1 / (m : ℝ)
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hε : 0 < ε := by positivity
  have hεN : 1 ≤ ε ^ 2 * N := by
    have : ((m ^ 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    simp only [ε]; rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    push_cast at this; linarith
  have hL := largeOf_uniform hεN R
  have hpL : pL ε (uniformInstance N) R = 0 := by rw [pL, hL]; simp
  have hq : qParam ε (uniformInstance N) R = 1 / (m : ℝ) + (1 / (m : ℝ)) ^ 2 / 2 := by
    rw [qParam, hpL, sub_zero, div_one]
  -- all quantiles equal 1
  have he1 : ∀ k, 1 ≤ k → k ≤ tParam ε (uniformInstance N) R → e k = 1 := by
    intro k hk1 hkt
    have hr := quantile_range hm hq hk1 hkt
    exact uniform_quantile_eq_one hεN hr.1 hr.2 (he k hk1 hkt)
  have ht' : tPrime ε (uniformInstance N) R e ≤ tParam ε (uniformInstance N) R := by
    simp only [tPrime]; split_ifs <;> omega
  -- every item of `Ĩ` has efficiency 1
  have heffl : ∀ x ∈ l, x.eff = 1 := by
    intro x hx
    have := hl x hx
    simp only [tildeItems, hL, List.map_nil, List.nil_append, List.mem_flatMap, List.mem_range,
      List.mem_replicate] at this
    obtain ⟨k, hk, -, rfl⟩ := this
    have := he1 (k + 1) (by omega) (by omega)
    simp only [TItem.eff, this, div_one]
    exact div_self (by positivity)
  have hnotlarge : ¬ ε ^ 2 < (uniformInstance N).p i := uniform_not_large hεN i
  -- `e_small = -1`
  have hes := convertGreedy_esmall ε (uniformInstance N).K e (tPrime ε (uniformInstance N) R e)
    l 1 heffl fun k hk1 hkt => (he1 k hk1 (hkt.trans ht')).le
  simp only [answerKP, hnotlarge, ite_false, hes]

/-- The empty solution is not a `(1/2, 6ε)`-approximation of the uniform instance when
`6ε < (N - 1)/(4N)`. More precisely, every `(1/2, 6ε)`-approximate solution contains at least
`(N - 1)/4 - 6εN` items. -/
theorem card_of_approx {ε : ℝ} (hN : 0 < N) {C : Finset (Fin N)}
    (hC : (uniformInstance N).IsApproxSol (1 / 2) (6 * ε) C) :
    (N - 1 : ℝ) / 4 - 6 * ε * N ≤ C.card := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- a feasible set with `⌊N/2⌋` items
  set C' : Finset (Fin N) := Finset.univ.map (Fin.castLEEmb (Nat.div_le_self N 2))
  have hcard : C'.card = N / 2 := by simp [C']
  have hfeas : (uniformInstance N).Feasible C' := by
    simp only [RInstance.Feasible, uniformInstance, Finset.sum_const, hcard, nsmul_eq_mul]
    have : ((N / 2 : ℕ) : ℝ) ≤ N / 2 := by
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self N 2
    rw [mul_one_div, div_le_iff₀ hNr]; linarith
  have h := hC.2 C' hfeas
  simp only [RInstance.profitOf, uniformInstance, Finset.sum_const, hcard, nsmul_eq_mul] at h
  have hhalf : (N - 1 : ℝ) / 2 ≤ ((N / 2 : ℕ) : ℝ) := by
    have := Nat.div_add_mod N 2
    have hmod := Nat.mod_lt N (show 2 > 0 by norm_num)
    have : (N : ℝ) = 2 * ((N / 2 : ℕ) : ℝ) + ((N % 2 : ℕ) : ℝ) := by exact_mod_cast this.symm
    have : ((N % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : N % 2 ≤ 1)
    linarith
  have key : ((N / 2 : ℕ) : ℝ) * (1 / N) / 2 - 6 * ε ≤ C.card * (1 / N) := by linarith
  have := mul_le_mul_of_nonneg_right key hNr.le
  field_simp at this
  nlinarith

end Answer

/-! ### Theorem 4.1 is false -/

/-- **Theorem 4.1 is false.** Model a randomized execution of `LCA-KP` on the uniform instance
by a seed `ω ∼ ν` (internal randomness and the weighted samples of every run); the run answering
query `i` uses the sample `R ω i`, the `rQuantile` outputs `e ω i` and the sorting order
`l ω i` of `Ĩ`. Assume the accuracy guarantee of Theorem 4.5 (with the union bound over the
`t` calls of a run): each run is accurate with probability `≥ 1 - η`. If
`δ + η + 6ε < (N - 1)/(4N)`, there is **no** seed-dependent `(1/2, 6ε)`-approximate solution
`C ω` with which each single answer is consistent with probability `≥ 1 - δ`. -/
theorem lcaKP_not_correct {Ω : Type*} {N m : ℕ} (hm : 2 ≤ m) (hN : m ^ 2 ≤ N) (ν : PMF Ω)
    (R : Ω → Fin N → List (Fin N)) (e : Ω → Fin N → ℕ → ℝ) (l : Ω → Fin N → List (TItem N))
    (hl : ∀ ω i, ∀ x ∈ l ω i, x ∈ tildeItems (1 / (m : ℝ)) (uniformInstance N) (R ω i) (e ω i))
    (η δ : ℝ) (hη : ∀ i, 1 - η ≤
      probReal ν {ω | Accurate (1 / (m : ℝ)) (uniformInstance N) (R ω i) (e ω i)})
    (hsmall : δ + η + 6 * (1 / (m : ℝ)) < (N - 1) / (4 * N)) :
    ¬ ∃ C : Ω → Finset (Fin N), ∀ i, 1 - δ ≤ probReal ν
      {ω | (uniformInstance N).IsApproxSol (1 / 2) (6 * (1 / (m : ℝ))) (C ω) ∧
        (answerKP (1 / (m : ℝ)) (uniformInstance N) (R ω i) (e ω i) (l ω i) i = true ↔
          i ∈ C ω)} := by
  classical
  rintro ⟨C, hC⟩
  set ε : ℝ := 1 / (m : ℝ)
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  set E : Fin N → Set Ω := fun i =>
    {ω | (uniformInstance N).IsApproxSol (1 / 2) (6 * ε) (C ω) ∧ i ∉ C ω}
  -- each `E i` has probability `≥ 1 - δ - η`
  have hlow : ∀ i, 1 - δ - η ≤ probReal ν (E i) := by
    intro i
    have h2 := probReal_add_le_inter ν
      {ω | (uniformInstance N).IsApproxSol (1 / 2) (6 * ε) (C ω) ∧
        (answerKP ε (uniformInstance N) (R ω i) (e ω i) (l ω i) i = true ↔ i ∈ C ω)}
      {ω | Accurate ε (uniformInstance N) (R ω i) (e ω i)}
    have h3 : probReal ν ({ω | (uniformInstance N).IsApproxSol (1 / 2) (6 * ε) (C ω) ∧
        (answerKP ε (uniformInstance N) (R ω i) (e ω i) (l ω i) i = true ↔ i ∈ C ω)} ∩
        {ω | Accurate ε (uniformInstance N) (R ω i) (e ω i)}) ≤ probReal ν (E i) :=
      probReal_mono ν fun ω hω => by
      obtain ⟨⟨hap, hiff⟩, hacc⟩ := hω
      refine ⟨hap, fun hi => ?_⟩
      have := hiff.2 hi
      rw [answerKP_uniform hm hN _ _ hacc _ (hl ω i)] at this
      exact Bool.false_ne_true this
    linarith [hC i, hη i, h3]
  -- every outcome lies in at most `N - ((N-1)/4 - 6εN)` of the `E i`
  have hup := sum_mul_probReal_le ν Finset.univ (fun _ => 1) (fun _ => zero_le_one) E
    (N - ((N - 1 : ℝ) / 4 - 6 * ε * N)) fun ω => by
      by_cases hap : (uniformInstance N).IsApproxSol (1 / 2) (6 * ε) (C ω)
      · have hc := card_of_approx hN0 hap
        have : ∑ i, (E i).indicator (fun _ => (1 : ℝ)) ω = (Finset.univ \ C ω).card := by
          simp only [E, Set.indicator_apply, Set.mem_ofPred_eq, hap, true_and]
          rw [Finset.sum_boole]
          congr 2; ext i; simp
        rw [this, Finset.card_univ_sdiff, Fintype.card_fin, Nat.cast_sub (by
          simpa using Finset.card_le_univ (C ω))]
        linarith
      · have : ∑ i, (E i).indicator (fun _ => (1 : ℝ)) ω = 0 :=
          Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (fun h => hap h.1) _
        rw [this]
        have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
        have : (0 : ℝ) ≤ ε := by positivity
        nlinarith
  have hsum : (N : ℝ) * (1 - δ - η) ≤ ∑ i : Fin N, 1 * probReal ν (E i) := by
    calc (N : ℝ) * (1 - δ - η) = ∑ _i : Fin N, (1 - δ - η) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => by linarith [hlow i]
  have := hsum.trans hup
  have hsm : δ + η + 6 * ε < (N - 1) / (4 * N) := hsmall
  rw [lt_div_iff₀ (by positivity)] at hsm
  nlinarith

/-- **Theorem 4.1 fails with the paper's parameters.** For `ε = 1/m` with `m ≥ 30` and
`N ≥ m²`: if each run's quantiles are accurate with probability `≥ 1 - ε/36` (what Theorem 4.5
and the union bound over `t ≤ 1/ε` calls with `β = ε²/36` give), then `LCA-KP` does not provide
query access to a `(1/2, 6ε)`-approximate solution with failure probability `ε`, even in the
per-query sense. -/
theorem theorem_4_1_false {Ω : Type*} {N m : ℕ} (hm : 30 ≤ m) (hN : m ^ 2 ≤ N) (ν : PMF Ω)
    (R : Ω → Fin N → List (Fin N)) (e : Ω → Fin N → ℕ → ℝ) (l : Ω → Fin N → List (TItem N))
    (hl : ∀ ω i, ∀ x ∈ l ω i, x ∈ tildeItems (1 / (m : ℝ)) (uniformInstance N) (R ω i) (e ω i))
    (hη : ∀ i, 1 - (1 / (m : ℝ)) / 36 ≤
      probReal ν {ω | Accurate (1 / (m : ℝ)) (uniformInstance N) (R ω i) (e ω i)}) :
    ¬ ∃ C : Ω → Finset (Fin N), ∀ i, 1 - 1 / (m : ℝ) ≤ probReal ν
      {ω | (uniformInstance N).IsApproxSol (1 / 2) (6 * (1 / (m : ℝ))) (C ω) ∧
        (answerKP (1 / (m : ℝ)) (uniformInstance N) (R ω i) (e ω i) (l ω i) i = true ↔
          i ∈ C ω)} := by
  refine lcaKP_not_correct (by omega) hN ν R e l hl _ _ hη ?_
  have hm' : (30 : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : (m : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hNr : (900 : ℝ) ≤ N := by nlinarith
  rw [lt_div_iff₀ (by positivity)]
  have : 1 / (m : ℝ) ≤ 1 / 30 := one_div_le_one_div_of_le (by norm_num) hm'
  nlinarith

/-- Non-vacuity of `theorem_4_1_false`: accurate quantile outputs exist (all equal to `1`). -/
theorem accurate_one {N m : ℕ} (hm : 2 ≤ m) (hN : m ^ 2 ≤ N) (R : List (Fin N)) :
    Accurate (1 / (m : ℝ)) (uniformInstance N) R fun _ => 1 := by
  intro k hk1 hkt
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hε : (0 : ℝ) < 1 / m := by positivity
  have hεN : 1 ≤ (1 / (m : ℝ)) ^ 2 * N := by
    have : ((m ^ 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    push_cast at this; linarith
  have hL := largeOf_uniform hεN R
  have hpL : pL (1 / (m : ℝ)) (uniformInstance N) R = 0 := by rw [pL, hL]; simp
  have hq : qParam (1 / (m : ℝ)) (uniformInstance N) R = 1 / (m : ℝ) + (1 / (m : ℝ)) ^ 2 / 2 := by
    rw [qParam, hpL, sub_zero, div_one]
  have hr := quantile_range hm hq hk1 hkt
  have ht0 : 0 ≤ tau (1 / (m : ℝ)) := by unfold tau; positivity
  simp only [RInstance.IsApproxQuantile, uniform_effMass hεN, le_refl, ite_true]
  constructor <;> linarith [hr.1, hr.2]

end Podc.KnapsackLCA.Sec4
