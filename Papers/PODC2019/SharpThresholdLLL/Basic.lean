import Cslib.Probability.Finite.Product
import Mathlib

/-!
# LLL instances in the variable setting, and conditional probabilities

Brandt–Maus–Uitto, *A Sharp Threshold Phenomenon for the Distributed Complexity of the Lovász
Local Lemma*, PODC 2019.

An instance has finitely many independent random variables `X_i` (`i : ι`). Each variable has a
finite range `α i` and a distribution `prob i`. It also has finitely many bad events `E_v`
(`v : V`), and each event is determined by the variables in `vbl v`. Two events are adjacent in
the *dependency graph* iff they share a variable (`dep v` is the neighbourhood of `v`).

The sequential process fixes variables one at a time. A state of the process is a partial
assignment `σ : ∀ i, Option (α i)`. The conditional probability
`Pr[E_v | X_i = x_i for the fixed i]` is `condProb σ v`: the probability of `E_v` under the
product distribution (`Cslib.Probability.piExpect`) in which fixed variables are point masses and
unfixed variables keep their distribution.

Main facts (instances of the general facts on product distributions in
`Cslib/Probability/Finite/Product.lean`):
* `sum_condProb_fix` (law of total probability): averaging over the value of an unfixed
  variable `j` gives back the current conditional probability.
* `condProb_fix_of_not_mem` (independence): fixing a variable that `E_v` does not depend on does
  not change `Pr[E_v | ·]`.
* `condProb_total`: once all variables are fixed, `Pr[E_v | ·]` is `1` or `0` according to
  whether `E_v` occurs.
-/

open Finset Cslib.Probability

set_option linter.unusedSectionVars false

namespace SharpThresholdLLL

-- CSLib candidate (LLL instances in the variable setting)
/-- An LLL instance in the variable setting. -/
structure Instance (ι : Type) (α : ι → Type) [∀ i, Fintype (α i)] (V : Type) where
  /-- the distribution of variable `i` -/
  prob : ∀ i, α i → ℝ
  prob_nonneg : ∀ i a, 0 ≤ prob i a
  prob_sum : ∀ i, ∑ a, prob i a = 1
  /-- the variables on which event `v` depends -/
  vbl : V → Finset ι
  /-- the bad events, as predicates on full assignments -/
  bad : V → (∀ i, α i) → Prop
  /-- `E_v` depends only on the variables in `vbl v` -/
  bad_local : ∀ v (x y : ∀ i, α i), (∀ i ∈ vbl v, x i = y i) → (bad v x ↔ bad v y)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)]
  [∀ i, DecidableEq (α i)] {V : Type} [Fintype V] [DecidableEq V]

namespace Instance

variable (I : Instance ι α V)

/-- The events affected by variable `i` (its hyperedge). Rank `r` means `#(evs i) ≤ r`. -/
def evs (i : ι) : Finset V := univ.filter fun v => i ∈ I.vbl v

/-- The neighbourhood of `v` in the dependency graph: the other events that share a variable
with `E_v`. The dependency degree `d` bounds `#(dep v)`. -/
def dep (v : V) : Finset V := univ.filter fun u => u ≠ v ∧ ∃ i, i ∈ I.vbl u ∧ i ∈ I.vbl v

/-- The dependency graph as a `SimpleGraph`. -/
def depGraph : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ i, i ∈ I.vbl u ∧ i ∈ I.vbl v
  symm := ⟨fun _ _ ⟨h, i, h1, h2⟩ => ⟨h.symm, i, h2, h1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma mem_dep {u v : V} : u ∈ I.dep v ↔ I.depGraph.Adj u v := by
  simp [dep, depGraph]

lemma mem_evs {i : ι} {v : V} : v ∈ I.evs i ↔ i ∈ I.vbl v := by simp [evs]

lemma mem_dep_of_mem_evs {i : ι} {u v : V} (hu : u ∈ I.evs i) (hv : v ∈ I.evs i) (h : u ≠ v) :
    u ∈ I.dep v := by
  rw [mem_evs] at hu hv
  simp only [dep, mem_filter, mem_univ, true_and]
  exact ⟨h, i, hu, hv⟩

lemma not_mem_dep_self (v : V) : v ∉ I.dep v := by simp [dep]

lemma dep_symm {u v : V} : u ∈ I.dep v ↔ v ∈ I.dep u := by
  rw [mem_dep, mem_dep]; exact I.depGraph.adj_comm _ _

/-- The marginal distribution of variable `i` in state `σ`: a point mass if `i` is fixed, its
original distribution otherwise. -/
def marg (σ : ∀ i, Option (α i)) (i : ι) (a : α i) : ℝ :=
  match σ i with
  | none => I.prob i a
  | some b => if a = b then 1 else 0

open scoped Classical in
/-- `condProb σ v = Pr[E_v | X_i = σ_i for all fixed i]`: the probability of `E_v` under the
product of the marginals `marg σ i`. -/
noncomputable def condProb (σ : ∀ i, Option (α i)) (v : V) : ℝ :=
  piExpect (I.marg σ) fun x => if I.bad v x then 1 else 0

/-- The empty partial assignment (nothing fixed yet). -/
def empty : ∀ i, Option (α i) := fun _ => none

/-- `Pr[E_v]`, the unconditional probability of `E_v` under the product distribution. -/
noncomputable def pr (v : V) : ℝ := I.condProb empty v

lemma marg_empty (i : ι) (a : α i) : I.marg empty i a = I.prob i a := rfl

open scoped Classical in
/-- `Pr[E_v] = Σ_x (∏_i Pr[X_i = x_i]) · 1[E_v(x)]`. -/
lemma pr_eq (v : V) :
    I.pr v = ∑ x : (∀ i, α i), (∏ i, I.prob i (x i)) * (if I.bad v x then 1 else 0) := by
  rfl

lemma marg_nonneg (σ : ∀ i, Option (α i)) (i : ι) (a : α i) : 0 ≤ I.marg σ i a := by
  unfold marg; split
  · exact I.prob_nonneg i a
  · split <;> norm_num

lemma condProb_nonneg (σ : ∀ i, Option (α i)) (v : V) : 0 ≤ I.condProb σ v :=
  piExpect_nonneg (I.marg_nonneg σ) fun _ => by split <;> norm_num

lemma marg_of_none {σ : ∀ i, Option (α i)} {j : ι} (hj : σ j = none) : I.marg σ j = I.prob j := by
  ext a; simp [marg, hj]

lemma marg_of_some {σ : ∀ i, Option (α i)} {j : ι} {b : α j} (hj : σ j = some b) :
    I.marg σ j = Pi.single b 1 := by
  ext a; simp [marg, hj, Pi.single_apply]

/-- Fixing `X_j = b` replaces the marginal of `j` by the point mass at `b`. -/
lemma marg_update_some (σ : ∀ i, Option (α i)) (j : ι) (b : α j) :
    I.marg (Function.update σ j (some b)) = Function.update (I.marg σ) j (Pi.single b 1) := by
  ext i a
  by_cases h : i = j
  · subst h; simp [marg, Pi.single_apply]
  · simp [marg, Function.update_of_ne h]

/-- **Law of total probability.** If `j` is not fixed in `σ`, averaging the conditional
probability after fixing `X_j = b` over `b` (weighted by `Pr[X_j = b]`) gives the current
conditional probability. -/
theorem sum_condProb_fix (σ : ∀ i, Option (α i)) {j : ι} (hj : σ j = none) (v : V) :
    ∑ b, I.prob j b * I.condProb (Function.update σ j (some b)) v = I.condProb σ v := by
  simp only [condProb, marg_update_some, ← I.marg_of_none hj]
  exact sum_mul_piExpect_update_single _ j _

/-- **Independence.** Fixing a variable `j ∉ vbl v` does not change `Pr[E_v | ·]`. -/
theorem condProb_fix_of_not_mem (σ : ∀ i, Option (α i)) {j : ι} (hj : σ j = none) {v : V}
    (hv : j ∉ I.vbl v) (a : α j) :
    I.condProb (Function.update σ j (some a)) v = I.condProb σ v := by
  classical
  unfold condProb
  rw [marg_update_some]
  refine piExpect_update_single_of_forall_update j (by rw [I.marg_of_none hj]; exact I.prob_sum j)
    (fun x b => ?_) a
  have : I.bad v (Function.update x j b) ↔ I.bad v x := by
    apply I.bad_local
    intro i hi
    rw [Function.update_of_ne (fun h : i = j => hv (h ▸ hi))]
  simp only [this]

/-- Once every variable is fixed (to `x`), `Pr[E_v | ·]` is the indicator of `E_v` at `x`. -/
theorem condProb_total (σ : ∀ i, Option (α i)) (x : ∀ i, α i) (hx : ∀ i, σ i = some (x i))
    (v : V) [Decidable (I.bad v x)] : I.condProb σ v = if I.bad v x then 1 else 0 := by
  classical
  have : I.marg σ = fun i => Pi.single (x i) 1 := funext fun i => I.marg_of_some (hx i)
  rw [condProb, this, piExpect_single]
  congr 1

end Instance

end SharpThresholdLLL
