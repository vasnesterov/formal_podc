import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

-- CSLib candidate: Cslib/Computability/QueryComplexity/QueryTree.lean

/-!
# Adaptive query trees and randomized query lower bounds

A deterministic algorithm that reads its input `f : ι → α` only through queries `i ↦ f i`
(with arbitrary answers, not only bits) is an *adaptive query tree*: an internal node asks
the query `i` and the answer `f i` selects the subtree. A randomized query algorithm is a
family of query trees indexed by a random seed drawn from a `PMF`.

## Main definitions

* `Cslib.QueryTree ι α β`: adaptive query trees with queries `ι`, answers `α`, outputs `β`.
* `QueryTree.eval`, `QueryTree.cost`, `QueryTree.queried`: output, number of queries and list
  of queried positions on the input `f`.
* `QueryTree.seq` (monadic bind) and `QueryTree.simulate` (replace every query by a
  sub-algorithm), used for query-preserving reductions.
* `Cslib.Probability.PMF.probReal μ E`: probability of an event under a `PMF`, as a real.

## Main statements

* `QueryTree.eval_eq_of_agree`: a tree cannot distinguish inputs that agree on the positions it
  queries.
* `QueryTree.eval_simulate`, `QueryTree.cost_simulate_le`: correctness and cost of simulations.
* `QueryTree.card_mul_probReal_le_sum_add`: the **needle lemma**. If a randomized algorithm
  makes at most `q` queries on `f₀`, and `f j` (`j ∈ J`) are inputs such that every position is
  changed by at most `D` of them, then the probability of an output event on `f₀` is at most the
  average over `j` of its probability on `f j` plus `q D / |J|`.
* `QueryTree.or_lower_bound`: the randomized query complexity of `OR_n` with error `δ` is at
  least `n (1 - 2δ)` (so `R(OR_n) ≥ n/3`).
* `Cslib.Probability.PMF.sum_mul_probReal_le`: the averaging principle (the easy direction of
  Yao's principle): a bound on `∑ⱼ wⱼ 1[r ∈ Eⱼ]` for every seed bounds `∑ⱼ wⱼ Pr[Eⱼ]`.
-/

namespace Cslib

/-- An adaptive query tree: queries in `ι`, answers in `α`, outputs in `β`. -/
inductive QueryTree (ι : Type*) (α : Type*) (β : Type*) where
  /-- Stop and output `b`. -/
  | leaf (b : β) : QueryTree ι α β
  /-- Query position `i`; continue with `k a` on answer `a`. -/
  | query (i : ι) (k : α → QueryTree ι α β) : QueryTree ι α β

namespace QueryTree

variable {ι α β γ ι' α' : Type*}

/-- The output of the tree on the input `f`. -/
def eval : QueryTree ι α β → (ι → α) → β
  | leaf b, _ => b
  | query i k, f => eval (k (f i)) f

/-- The number of queries the tree makes on the input `f`. -/
def cost : QueryTree ι α β → (ι → α) → ℕ
  | leaf _, _ => 0
  | query i k, f => cost (k (f i)) f + 1

/-- The positions queried on the input `f`, in order. -/
def queried : QueryTree ι α β → (ι → α) → List ι
  | leaf _, _ => []
  | query i k, f => i :: queried (k (f i)) f

@[simp] theorem eval_leaf (b : β) (f : ι → α) : (leaf b : QueryTree ι α β).eval f = b := rfl
@[simp] theorem eval_query (i : ι) (k : α → QueryTree ι α β) (f : ι → α) :
    (query i k).eval f = (k (f i)).eval f := rfl
@[simp] theorem cost_leaf (b : β) (f : ι → α) : (leaf b : QueryTree ι α β).cost f = 0 := rfl
@[simp] theorem cost_query (i : ι) (k : α → QueryTree ι α β) (f : ι → α) :
    (query i k).cost f = (k (f i)).cost f + 1 := rfl

theorem length_queried (t : QueryTree ι α β) (f : ι → α) : (t.queried f).length = t.cost f := by
  induction t with
  | leaf b => rfl
  | query i k ih => simp [queried, ih]

/-- A query tree cannot distinguish two inputs that agree on the positions it queries. -/
theorem eval_eq_of_agree (t : QueryTree ι α β) (f g : ι → α)
    (h : ∀ i ∈ t.queried f, g i = f i) : t.eval g = t.eval f := by
  induction t with
  | leaf b => rfl
  | query i k ih =>
    have hi : g i = f i := h i (by simp [queried])
    simp only [eval_query, hi]
    exact ih _ fun j hj => h j (by simp [queried, hj])

/-- Sequential composition: run `t`, then the tree selected by its output. -/
def seq : QueryTree ι α γ → (γ → QueryTree ι α β) → QueryTree ι α β
  | leaf c, g => g c
  | query i k, g => query i fun a => seq (k a) g

@[simp] theorem eval_seq (t : QueryTree ι α γ) (g : γ → QueryTree ι α β) (f : ι → α) :
    (t.seq g).eval f = (g (t.eval f)).eval f := by
  induction t with
  | leaf c => rfl
  | query i k ih => simp [seq, ih]

@[simp] theorem cost_seq (t : QueryTree ι α γ) (g : γ → QueryTree ι α β) (f : ι → α) :
    (t.seq g).cost f = t.cost f + (g (t.eval f)).cost f := by
  induction t with
  | leaf c => simp [seq]
  | query i k ih => simp [seq, ih]; omega

/-- Simulation: replace every query `i` of `t` by the sub-algorithm `s i` (over another input),
whose output is used as the answer to the query. -/
def simulate : QueryTree ι α β → (ι → QueryTree ι' α' α) → QueryTree ι' α' β
  | leaf b, _ => leaf b
  | query i k, s => (s i).seq fun a => simulate (k a) s

@[simp] theorem eval_simulate (t : QueryTree ι α β) (s : ι → QueryTree ι' α' α) (f : ι' → α') :
    (t.simulate s).eval f = t.eval fun i => (s i).eval f := by
  induction t with
  | leaf b => rfl
  | query i k ih => simp [simulate, ih]

/-- If every sub-algorithm makes at most `d` queries, the simulation makes at most `d` times as
many queries as the simulated tree on the simulated input. -/
theorem cost_simulate_le (t : QueryTree ι α β) (s : ι → QueryTree ι' α' α) (f : ι' → α') (d : ℕ)
    (hs : ∀ i, (s i).cost f ≤ d) :
    (t.simulate s).cost f ≤ d * t.cost fun i => (s i).eval f := by
  induction t with
  | leaf b => simp [simulate]
  | query i k ih =>
    simp only [simulate, cost_seq, cost_query]
    have := ih ((s i).eval f)
    have := hs i
    rw [Nat.mul_succ]
    omega

/-- Read the positions of `l` in order, then output `g` of the input read so far (unread
positions are `default`). -/
def ofFun [DecidableEq ι] [Inhabited α] : List ι → ((ι → α) → β) → QueryTree ι α β
  | [], g => leaf (g fun _ => default)
  | i :: l, g => query i fun a => ofFun l fun f => g (Function.update f i a)

theorem eval_ofFun [DecidableEq ι] [Inhabited α] (l : List ι) (g : (ι → α) → β) (f : ι → α) :
    (ofFun l g).eval f = g fun j => if j ∈ l then f j else default := by
  induction l generalizing g with
  | nil => simp [ofFun]
  | cons i l ih =>
    simp only [ofFun, eval_query, ih]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]

theorem cost_ofFun [DecidableEq ι] [Inhabited α] (l : List ι) (g : (ι → α) → β) (f : ι → α) :
    (ofFun l g).cost f = l.length := by
  induction l generalizing g with
  | nil => rfl
  | cons i l ih => simp [ofFun, ih]

/-- Every function of an input `Fin n → α` is computed by a query tree with `n` queries. -/
theorem eval_ofFun_finRange {n : ℕ} [Inhabited α] (g : (Fin n → α) → β) (f : Fin n → α) :
    (ofFun (List.finRange n) g).eval f = g f := by
  rw [eval_ofFun]; congr 1; funext j; simp

theorem cost_ofFun_finRange {n : ℕ} [Inhabited α] (g : (Fin n → α) → β) (f : Fin n → α) :
    (ofFun (List.finRange n) g).cost f = n := by
  rw [cost_ofFun, List.length_finRange]

end QueryTree

namespace Probability.PMF

open ENNReal

variable {Ω κ : Type*}

/-- The probability of the event `E` under the distribution `μ`, as a real number. -/
noncomputable def probReal (μ : _root_.PMF Ω) (E : Set Ω) : ℝ := (μ.toOuterMeasure E).toReal

variable (μ : _root_.PMF Ω)

theorem toOuterMeasure_le_one (E : Set Ω) : μ.toOuterMeasure E ≤ 1 := by
  rw [_root_.PMF.toOuterMeasure_apply]
  calc ∑' x, E.indicator μ x ≤ ∑' x, μ x :=
        ENNReal.tsum_le_tsum fun x => Set.indicator_le_self _ _ x
    _ = 1 := μ.tsum_coe

theorem toOuterMeasure_ne_top (E : Set Ω) : μ.toOuterMeasure E ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (toOuterMeasure_le_one μ E)

theorem probReal_nonneg (E : Set Ω) : 0 ≤ probReal μ E := ENNReal.toReal_nonneg

theorem probReal_le_one (E : Set Ω) : probReal μ E ≤ 1 := by
  unfold probReal
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using toOuterMeasure_le_one μ E)

theorem probReal_mono {E F : Set Ω} (h : E ⊆ F) : probReal μ E ≤ probReal μ F :=
  ENNReal.toReal_mono (toOuterMeasure_ne_top μ F) (μ.toOuterMeasure.mono h)

theorem probReal_union_le (E F : Set Ω) : probReal μ (E ∪ F) ≤ probReal μ E + probReal μ F := by
  unfold probReal
  rw [← ENNReal.toReal_add (toOuterMeasure_ne_top μ E) (toOuterMeasure_ne_top μ F)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨toOuterMeasure_ne_top μ E,
    toOuterMeasure_ne_top μ F⟩) (MeasureTheory.measure_union_le (μ := μ.toOuterMeasure) E F)

/-- Monotonicity up to an exceptional event. -/
theorem probReal_le_add_of_subset {E F B : Set Ω} (h : E ⊆ F ∪ B) :
    probReal μ E ≤ probReal μ F + probReal μ B :=
  (probReal_mono μ h).trans (probReal_union_le μ F B)

theorem probReal_add_inter (E F : Set Ω) :
    probReal μ E + probReal μ F = probReal μ (E ∪ F) + probReal μ (E ∩ F) := by
  unfold probReal
  rw [← ENNReal.toReal_add (toOuterMeasure_ne_top μ E) (toOuterMeasure_ne_top μ F),
    ← ENNReal.toReal_add (toOuterMeasure_ne_top μ _) (toOuterMeasure_ne_top μ _)]
  congr 1
  simp only [_root_.PMF.toOuterMeasure_apply]
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  congr 1
  ext x
  exact (Set.indicator_union_add_inter_apply _ E F x).symm

theorem probReal_add_compl (E : Set Ω) : probReal μ E + probReal μ Eᶜ = 1 := by
  rw [probReal_add_inter, Set.union_compl_self, Set.inter_compl_self]
  unfold probReal
  simp [_root_.PMF.toOuterMeasure_apply, μ.tsum_coe]

theorem probReal_compl (E : Set Ω) : probReal μ Eᶜ = 1 - probReal μ E := by
  linarith [probReal_add_compl μ E]

/-- Intersection bound: `Pr[E ∩ F] ≥ Pr[E] + Pr[F] - 1`. -/
theorem probReal_add_le_inter (E F : Set Ω) :
    probReal μ E + probReal μ F ≤ 1 + probReal μ (E ∩ F) := by
  rw [probReal_add_inter]
  linarith [probReal_le_one μ (E ∪ F)]

/-- **Averaging principle** (the easy direction of Yao's principle): if for every outcome `r`
the weighted number `∑ⱼ wⱼ 1[r ∈ Eⱼ]` is at most `U`, then `∑ⱼ wⱼ Pr[Eⱼ] ≤ U`. -/
theorem sum_mul_probReal_le (J : Finset κ) (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j) (E : κ → Set Ω)
    (U : ℝ) (h : ∀ r, ∑ j ∈ J, (E j).indicator (fun _ => w j) r ≤ U) :
    ∑ j ∈ J, w j * probReal μ (E j) ≤ U := by
  obtain ⟨r₀, -⟩ := μ.support_nonempty
  have hind : ∀ j r, 0 ≤ (E j).indicator (fun _ => w j) r := fun j r => Set.indicator_nonneg (fun _ _ => hw j) r
  have hU : 0 ≤ U := (Finset.sum_nonneg fun j _ => hind j r₀).trans (h r₀)
  have key : ∑ j ∈ J, ENNReal.ofReal (w j) * μ.toOuterMeasure (E j) ≤ ENNReal.ofReal U := by
    simp only [_root_.PMF.toOuterMeasure_apply]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    calc ∑' x, ∑ j ∈ J, ENNReal.ofReal (w j) * (E j).indicator μ x
        ≤ ∑' x, μ x * ENNReal.ofReal U := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          have hx : ∑ j ∈ J, ENNReal.ofReal (w j) * (E j).indicator μ x
              = μ x * ENNReal.ofReal (∑ j ∈ J, (E j).indicator (fun _ => w j) x) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hind j x), Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hxj : x ∈ E j <;> simp [hxj, mul_comm]
          rw [hx]
          gcongr
          exact h x
      _ = ENNReal.ofReal U := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
  have hfin : ∀ j ∈ J, ENNReal.ofReal (w j) * μ.toOuterMeasure (E j) ≠ ⊤ := fun j _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (toOuterMeasure_ne_top μ _)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top key
  rw [ENNReal.toReal_sum hfin, ENNReal.toReal_ofReal hU] at this
  simpa [probReal, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw _)] using this

open scoped Classical in
/-- Counting version of `sum_mul_probReal_le`: if every outcome lies in at most `k` of the
events `Eⱼ`, `j ∈ J`, their probabilities sum to at most `k`. -/
theorem sum_probReal_le (J : Finset κ) (E : κ → Set Ω) (k : ℝ)
    (h : ∀ r, ((J.filter fun j => r ∈ E j).card : ℝ) ≤ k) :
    ∑ j ∈ J, probReal μ (E j) ≤ k := by
  have := sum_mul_probReal_le μ J (fun _ => 1) (fun _ => zero_le_one) E k fun r => by
    convert h r using 1
    rw [Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : r ∈ E j <;> simp [hj]
  simpa using this

end Probability.PMF

namespace QueryTree

open Probability.PMF

variable {Ω ι α β κ : Type*}

open scoped Classical in
/-- **Needle lemma.** Let a randomized query algorithm `T` make at most `q` queries on the
input `f₀`, and let `f j` (`j ∈ J`) be inputs such that every position `i` is changed
(`f j i ≠ f₀ i`) by at most `D` of them. Then for every output event `P`,
`|J| · Pr[P(T f₀)] ≤ ∑ⱼ Pr[P(T (f j))] + q D`. -/
theorem card_mul_probReal_le_sum_add [DecidableEq α] (μ : _root_.PMF Ω) (T : Ω → QueryTree ι α β)
    (f₀ : ι → α) (q : ℕ) (hq : ∀ r, (T r).cost f₀ ≤ q) (J : Finset κ) (f : κ → ι → α) (D : ℕ)
    (hD : ∀ i, (J.filter fun j => f j i ≠ f₀ i).card ≤ D) (P : β → Prop) :
    (J.card : ℝ) * probReal μ {r | P ((T r).eval f₀)} ≤
      ∑ j ∈ J, probReal μ {r | P ((T r).eval (f j))} + q * D := by
  -- the bad event for `j`: some queried position (on `f₀`) is changed by `f j`
  set B : κ → Set Ω := fun j => {r | ∃ i ∈ (T r).queried f₀, f j i ≠ f₀ i}
  have hsub : ∀ j, {r | P ((T r).eval f₀)} ⊆ {r | P ((T r).eval (f j))} ∪ B j := by
    intro j r hr
    by_cases hb : r ∈ B j
    · exact Or.inr hb
    · left
      simp only [B, Set.mem_ofPred_eq, not_exists, not_and, not_not] at hb
      simp only [Set.mem_ofPred_eq] at hr ⊢
      rwa [eval_eq_of_agree _ _ _ hb]
  have h1 : ∀ j, probReal μ {r | P ((T r).eval f₀)} ≤
      probReal μ {r | P ((T r).eval (f j))} + probReal μ (B j) := fun j =>
    probReal_le_add_of_subset μ (hsub j)
  have h2 : ∑ j ∈ J, probReal μ (B j) ≤ q * D := by
    refine sum_probReal_le μ J B _ fun r => ?_
    have hcount : (J.filter fun j => r ∈ B j) ⊆
        ((T r).queried f₀).toFinset.biUnion fun i => J.filter fun j => f j i ≠ f₀ i := by
      intro j hj
      simp only [Finset.mem_filter, B, Set.mem_ofPred_eq] at hj
      obtain ⟨hjJ, i, hi, hne⟩ := hj
      simp only [Finset.mem_biUnion, List.mem_toFinset, Finset.mem_filter]
      exact ⟨i, hi, hjJ, hne⟩
    have := (Finset.card_le_card hcount).trans Finset.card_biUnion_le
    have h3 : ∑ i ∈ ((T r).queried f₀).toFinset, (J.filter fun j => f j i ≠ f₀ i).card ≤
        ((T r).queried f₀).toFinset.card * D := Finset.sum_le_card_nsmul _ _ _ fun i _ => hD i
    have h4 : ((T r).queried f₀).toFinset.card ≤ q :=
      (List.toFinset_card_le _).trans ((length_queried _ _).le.trans (hq r))
    have h5 : (J.filter fun j => r ∈ B j).card ≤ q * D :=
      this.trans (h3.trans (Nat.mul_le_mul_right _ h4))
    have h6 : ((J.filter fun j => r ∈ B j).card : ℝ) ≤ q * D := by exact_mod_cast h5
    convert h6 using 3
    exact Finset.filter_congr_decidable _ _ _
  calc (J.card : ℝ) * probReal μ {r | P ((T r).eval f₀)}
      = ∑ j ∈ J, probReal μ {r | P ((T r).eval f₀)} := by simp
    _ ≤ ∑ j ∈ J, (probReal μ {r | P ((T r).eval (f j))} + probReal μ (B j)) :=
        Finset.sum_le_sum fun j _ => h1 j
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith

/-- The `OR` function on `n` bits. -/
def orFn {n : ℕ} (x : Fin n → Bool) : Bool := decide (∃ i, x i = true)

/-- **Randomized query lower bound for `OR_n`.** A randomized query algorithm that computes
`OR_n` with error at most `δ` on every input, and makes at most `q` queries, satisfies
`n (1 - 2δ) ≤ q`. In particular `R(OR_n) ≥ n/3`. -/
theorem or_lower_bound {n : ℕ} (μ : _root_.PMF Ω) (T : Ω → QueryTree (Fin n) Bool Bool)
    (q : ℕ) (δ : ℝ) (hq : ∀ r x, (T r).cost x ≤ q)
    (hcorrect : ∀ x, 1 - δ ≤ probReal μ {r | (T r).eval x = orFn x}) :
    (n : ℝ) * (1 - 2 * δ) ≤ q := by
  classical
  set f : Fin n → Fin n → Bool := fun j i => decide (i = j)
  have hneedle := card_mul_probReal_le_sum_add μ T (fun _ => false) q (fun r => hq r _)
    Finset.univ f 1 (fun i => by
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, f, ne_eq, Bool.not_eq_false, decide_eq_true_eq] at ha hb
      exact ha.symm.trans hb) (fun b => b = false)
  have h0 : 1 - δ ≤ probReal μ {r | (T r).eval (fun _ => false) = false} := by
    have := hcorrect fun _ => false
    simpa [orFn] using this
  have hj : ∀ j, probReal μ {r | (T r).eval (f j) = false} ≤ δ := by
    intro j
    have := hcorrect (f j)
    have hor : orFn (f j) = true := by simp [orFn, f]
    rw [hor] at this
    have hc : {r | (T r).eval (f j) = false} = {r | (T r).eval (f j) = true}ᶜ := by
      ext r; simp
    rw [hc, probReal_compl]
    linarith
  have hsum : ∑ j : Fin n, probReal μ {r | (T r).eval (f j) = false} ≤ n * δ := by
    calc _ ≤ ∑ _j : Fin n, δ := Finset.sum_le_sum fun j _ => hj j
      _ = n * δ := by simp
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_one, mul_one] at hneedle
  nlinarith

end QueryTree

end Cslib
