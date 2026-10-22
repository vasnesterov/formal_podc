import Mathlib

/-!
# Throughput maximization on line and tree networks: the abstract problem

Chakaravarthy, Roy, Sabharwal, *Distributed algorithms for scheduling on line and tree networks*,
PODC 2012 (arXiv:1205.1924v2).

After the reformulation of Section 2 every problem considered in the paper (tree networks, line
networks with windows, unit or arbitrary heights) is a packing problem over a finite set `D` of
*demand instances*: each `d : D` belongs to a demand `dem d : A`, has a profit, and uses a finite set
`path d : Finset E` of edges. Edges of different networks are different elements of `E`, so two
instances *overlap* iff their edge sets intersect.

* `Inst A D E` — the abstract instance.
* `Overlap`, `Conflict`, `IsIndep` — Section 2 (a feasible solution of the unit-height problem is an
  independent set of demand instances).
* `IsHFeasible` — feasible solutions with heights (Section 6).
* `IsLPFeasible h x` — the LP relaxation of Section 3.1 (`h = 1`) and of Section 6.1 (heights `h`).
* `Duals`, `lhs`, `val`, `weak_duality` — the dual LP and weak duality, in the scaled form used by
  Lemmas 3.1 and 6.1 (if all dual constraints are `λ`-satisfied then `λ · (LP value) ≤ val`).
-/

set_option linter.unusedSectionVars false

namespace Podc.LineTreeScheduling

open Finset

/-- An instance of the throughput maximization problem, reformulated in terms of demand instances
(Section 2): `dem d` is the demand `a_d` owning the instance `d`, `path d` the set of edges used by
`d`, `profit d` its profit. -/
structure Inst (A D E : Type*) where
  /-- The demand `a_d` to which the demand instance `d` belongs. -/
  dem : D → A
  /-- The edges of `path(d)`. -/
  path : D → Finset E
  /-- The profit `p(d)`. -/
  profit : D → ℝ

variable {A D E : Type*} [DecidableEq A] [DecidableEq D] [DecidableEq E]

namespace Inst

variable (I : Inst A D E)

/-- `d₁` and `d₂` overlap: their paths share an edge. -/
def Overlap (d₁ d₂ : D) : Prop := (I.path d₁ ∩ I.path d₂).Nonempty

/-- `d₁` and `d₂` conflict: they belong to the same demand or they overlap. -/
def Conflict (d₁ d₂ : D) : Prop := I.dem d₁ = I.dem d₂ ∨ I.Overlap d₁ d₂

/-- An independent set of demand instances (= a feasible solution in the unit-height case). -/
def IsIndep (S : Finset D) : Prop := ∀ d₁ ∈ S, ∀ d₂ ∈ S, d₁ ≠ d₂ → ¬ I.Conflict d₁ d₂

/-- The profit `p(S)` of a set of demand instances. -/
def profitOf (S : Finset D) : ℝ := ∑ d ∈ S, I.profit d

lemma overlap_comm {d₁ d₂ : D} : I.Overlap d₁ d₂ ↔ I.Overlap d₂ d₁ := by
  unfold Overlap; rw [inter_comm]

lemma conflict_comm {d₁ d₂ : D} : I.Conflict d₁ d₂ ↔ I.Conflict d₂ d₁ := by
  unfold Conflict; rw [overlap_comm, eq_comm]

lemma conflict_self (d : D) : I.Conflict d d := Or.inl rfl

/-- A feasible solution with heights `h` (Section 6): at most one instance per demand, and on
every edge the heights of the selected instances using it sum to at most `1`. -/
def IsHFeasible (h : D → ℝ) (S : Finset D) : Prop :=
  (∀ d₁ ∈ S, ∀ d₂ ∈ S, d₁ ≠ d₂ → I.dem d₁ ≠ I.dem d₂) ∧
    ∀ e, ∑ d ∈ S with e ∈ I.path d, h d ≤ 1

variable [Fintype D]

/-- Feasible solutions of the LP relaxation (Section 3.1 for `h = 1`, Section 6.1 in general):
`x ≥ 0`, `∑_{d ∼ e} x(d) h(d) ≤ 1` for every edge and `∑_{d ∈ Inst(a)} x(d) ≤ 1` for every
demand. -/
def IsLPFeasible (h : D → ℝ) (x : D → ℝ) : Prop :=
  (∀ d, 0 ≤ x d) ∧ (∀ e, ∑ d with e ∈ I.path d, x d * h d ≤ 1) ∧
    ∀ a, ∑ d with I.dem d = a, x d ≤ 1

/-- The LP value `∑_d x(d) p(d)`. -/
def lpValue (x : D → ℝ) : ℝ := ∑ d, x d * I.profit d

/-- The indicator vector of a set of instances. -/
def ind (S : Finset D) : D → ℝ := fun d => if d ∈ S then 1 else 0

lemma lpValue_ind (S : Finset D) : I.lpValue (ind S) = I.profitOf S := by
  classical
  simp [lpValue, ind, profitOf, ite_mul, Finset.sum_ite_mem]

/-- An independent set is a feasible (integral) solution of the unit-height LP. -/
lemma IsIndep.isLPFeasible {S : Finset D} (hS : I.IsIndep S) :
    I.IsLPFeasible (fun _ => 1) (ind S) := by
  classical
  refine ⟨fun d => by unfold ind; split_ifs <;> norm_num, fun e => ?_, fun a => ?_⟩
  · simp only [ind, mul_one, sum_boole, Nat.cast_le_one]
    rw [Finset.card_le_one]
    intro d₁ h₁ d₂ h₂
    simp only [mem_filter, mem_univ, true_and] at h₁ h₂
    by_contra hne
    exact hS d₁ h₁.2 d₂ h₂.2 hne (Or.inr ⟨e, mem_inter.2 ⟨h₁.1, h₂.1⟩⟩)
  · simp only [ind, sum_boole, Nat.cast_le_one]
    rw [Finset.card_le_one]
    intro d₁ h₁ d₂ h₂
    simp only [mem_filter, mem_univ, true_and] at h₁ h₂
    by_contra hne
    exact hS d₁ h₁.2 d₂ h₂.2 hne (Or.inl (h₁.1.trans h₂.1.symm))

/-- A feasible solution with heights is a feasible (integral) solution of the height LP. -/
lemma IsHFeasible.isLPFeasible {h : D → ℝ} {S : Finset D} (hS : I.IsHFeasible h S) :
    I.IsLPFeasible h (ind S) := by
  classical
  refine ⟨fun d => by unfold ind; split_ifs <;> norm_num, fun e => ?_, fun a => ?_⟩
  · have := hS.2 e
    simp only [ind, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_filter] at this ⊢
    calc _ = ∑ d, (if d ∈ S then (if e ∈ I.path d then h d else 0) else 0) := by
            refine Finset.sum_congr rfl fun d _ => ?_
            split_ifs <;> rfl
          _ = ∑ d ∈ S, (if e ∈ I.path d then h d else 0) := by
            rw [Finset.sum_ite_mem univ S]; simp
          _ ≤ 1 := this
  · simp only [ind, sum_boole, Nat.cast_le_one]
    rw [Finset.card_le_one]
    intro d₁ h₁ d₂ h₂
    simp only [mem_filter, mem_univ, true_and] at h₁ h₂
    by_contra hne
    exact hS.1 d₁ h₁.2 d₂ h₂.2 hne (h₁.1.trans h₂.1.symm)

end Inst

/-- An assignment of the dual variables `α(a)` (demands) and `β(e)` (edges). -/
structure Duals (A E : Type*) where
  /-- `α(a)`. -/
  α : A → ℝ
  /-- `β(e)`. -/
  β : E → ℝ

instance : Zero (Duals A E) := ⟨⟨0, 0⟩⟩

/-- The dual objective `val(α, β) = ∑_a α(a) + ∑_e β(e)`. -/
def Duals.val [Fintype A] [Fintype E] (y : Duals A E) : ℝ := ∑ a, y.α a + ∑ e, y.β e

@[simp] lemma Duals.zero_α : (0 : Duals A E).α = 0 := rfl
@[simp] lemma Duals.zero_β : (0 : Duals A E).β = 0 := rfl

namespace Inst

variable (I : Inst A D E)

/-- Left-hand side of the dual constraint of `d`: `α(a_d) + h(d) ∑_{e ∼ d} β(e)` (Section 3.1 for
`h = 1`, Section 6.1 in general). -/
def lhs (h : D → ℝ) (y : Duals A E) (d : D) : ℝ := y.α (I.dem d) + h d * ∑ e ∈ I.path d, y.β e

variable [Fintype D] [Fintype A] [Fintype E]

/-- **Weak duality**, in the scaled form used in the proofs of Lemmas 3.1 and 6.1: if the dual
assignment is nonnegative and every dual constraint is `λ`-satisfied, then
`λ · (LP value of x) ≤ val(α, β)` for every feasible `x`. (With `λ = 1` this is the usual weak
duality theorem; the paper scales `(α, β)` by `1/λ` instead.) -/
theorem weak_duality {h : D → ℝ} {x : D → ℝ} (hx : I.IsLPFeasible h x) {y : Duals A E}
    (hα : ∀ a, 0 ≤ y.α a) (hβ : ∀ e, 0 ≤ y.β e) {lam : ℝ}
    (hsat : ∀ d, lam * I.profit d ≤ I.lhs h y d) :
    lam * I.lpValue x ≤ y.val := by
  classical
  obtain ⟨hx0, hxe, hxa⟩ := hx
  have h1 : lam * I.lpValue x ≤ ∑ d, x d * I.lhs h y d := by
    rw [lpValue, Finset.mul_sum]
    refine Finset.sum_le_sum fun d _ => ?_
    have := mul_le_mul_of_nonneg_left (hsat d) (hx0 d)
    linarith
  have h2 : ∑ d, x d * I.lhs h y d =
      ∑ a, y.α a * ∑ d ∈ univ.filter (fun d => I.dem d = a), x d +
        ∑ e, y.β e * ∑ d ∈ univ.filter (fun d => e ∈ I.path d), x d * h d := by
    simp only [lhs, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_fiberwise univ I.dem (fun d => x d * y.α (I.dem d))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [(Finset.mem_filter.1 hd).2]; ring
    · simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm' (t' := univ) (s' := fun e => univ.filter (fun d => e ∈ I.path d))]
      · refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => by ring
      · intro d e; simp
  have h3 : ∑ a, y.α a * ∑ d ∈ univ.filter (fun d => I.dem d = a), x d ≤ ∑ a, y.α a :=
    Finset.sum_le_sum fun a _ => mul_le_of_le_one_right (hα a) (hxa a)
  have h4 : ∑ e, y.β e * ∑ d ∈ univ.filter (fun d => e ∈ I.path d), x d * h d ≤ ∑ e, y.β e :=
    Finset.sum_le_sum fun e _ => mul_le_of_le_one_right (hβ e) (hxe e)
  rw [Duals.val]; linarith

end Inst

end Podc.LineTreeScheduling
