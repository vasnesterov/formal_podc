import Cslib.Foundations.SocialChoice.Aggregation
import Mathlib

/-!
# Fair ordering via streaming social choice: definitions of Section 3

G. Ramseyer, A. Goel. *Fair Ordering in Replicated Systems via Streaming Social Choice*
(arXiv 2304.02730v4; Brief Announcement at PODC 2024).

`n` replicas (a finite type `ι`) each submit an ordering vote on a set of transactions `X`. In the
static setting (Sections 3–4) every replica votes on every transaction, so a vote is a strict
total order on `X`: a `Cslib.SocialChoice.Pref X`, where `P a b` means "`a` before `b`".

* `count σ a b`: the number of replicas reporting `a ≺ b` (the ordering graph of Def. 3.2 has
  edge weight `count σ a b / n`).
* `AtLeast σ γ a b`: at least `γ n` replicas report `a ≺ b`.
* `ExactlyMinimal T γ out` (Def. 3.3) and `MinimalBatchFair T γ δ out` (Def. 3.5): the output
  order `out` reverses a pair that `γ n` replicas *truly* received in order only if a chain of
  pairs, each received in order by `γ n` (resp. `(γ - 2δ) n`) replicas, is output in order from
  the second transaction back to the first. `T` is the profile of true (observed) orderings.
* Faulty replicas: `Agree T P F` says that the reported profile `P` coincides with the true
  profile `T` outside the faulty set `F`. A deterministic ranking algorithm is an aggregation map
  `Cslib.SocialChoice.Aggregation ι X = Profile ι X → Pref X` applied to the reported profile.
-/

namespace Podc.FairOrderingSocialChoice

open Cslib.SocialChoice Finset Relation

variable {ι X : Type*} [Fintype ι]

/-- Number of replicas whose vote puts `a` before `b`. -/
noncomputable def count (σ : Profile ι X) (a b : X) : ℕ := by
  classical exact #{i | (σ i).P a b}

theorem count_def [DecidableEq ι] (σ : Profile ι X) (a b : X) [DecidablePred fun i => (σ i).P a b] :
    count σ a b = #{i | (σ i).P a b} := by
  unfold count; congr 1; ext; simp

theorem count_le (σ : Profile ι X) (a b : X) : count σ a b ≤ Fintype.card ι := by
  classical unfold count; exact card_filter_le _ _

/-- For distinct `a, b`, the counts of the two directions add up to `n`. -/
theorem count_add_count (σ : Profile ι X) {a b : X} (hab : a ≠ b) :
    count σ a b + count σ b a = Fintype.card ι := by
  classical
  unfold count
  rw [← card_union_of_disjoint]
  · convert card_univ (α := ι)
    ext i; simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
    exact (σ i).total hab
  · rw [disjoint_filter]; intro i _ h h'; exact (σ i).asymm h h'

/-- The weight `w(a, b)` of the ordering graph (Def. 3.2): the fraction of replicas reporting
`a ≺ b`. -/
noncomputable def weight (σ : Profile ι X) (a b : X) : ℝ := count σ a b / Fintype.card ι

/-- At least `γ n` replicas report (or received) `a ≺ b`. -/
def AtLeast (σ : Profile ι X) (γ : ℝ) (a b : X) : Prop := γ * Fintype.card ι ≤ count σ a b

/-- **Definition 3.3** (exact `γ`-minimality). If `γ n` replicas received `a ≺ b` but `b` is
output before `a`, then there is a sequence `b = τ₁, …, τₖ = a` such that `γ n` replicas received
`τᵢ ≺ τᵢ₊₁` and `τᵢ` is output before `τᵢ₊₁`. -/
def ExactlyMinimal (T : Profile ι X) (γ : ℝ) (out : Pref X) : Prop :=
  ∀ a b, AtLeast T γ a b → out.P b a → ReflTransGen (fun x y => AtLeast T γ x y ∧ out.P x y) b a

/-- **Definition 3.5** (`(γ, δ)`-minimal-batch-order-fairness). If `γ n` replicas received
`a ≺ b` but `b` is output before `a`, then there is a sequence `b = τ₁, …, τₖ = a` such that at
least `(γ - 2δ) n` replicas received `τᵢ ≺ τᵢ₊₁` and `τᵢ` is output before `τᵢ₊₁`. -/
def MinimalBatchFair (T : Profile ι X) (γ δ : ℝ) (out : Pref X) : Prop :=
  ∀ a b, AtLeast T γ a b → out.P b a →
    ReflTransGen (fun x y => AtLeast T (γ - 2 * δ) x y ∧ out.P x y) b a

/-- Definition 3.3 is the case `δ = 0` of Definition 3.5. -/
theorem minimalBatchFair_zero_iff (T : Profile ι X) (γ : ℝ) (out : Pref X) :
    MinimalBatchFair T γ 0 out ↔ ExactlyMinimal T γ out := by
  simp [MinimalBatchFair, ExactlyMinimal]

/-- When the `γ`-dependency graph of the true profile is acyclic, exact `γ`-minimality says that
the output is a linear extension of it (the weaker condition mentioned after Lemma 3.4). -/
theorem ExactlyMinimal.P_of_acyclic {T : Profile ι X} {γ : ℝ} {out : Pref X}
    (h : ExactlyMinimal T γ out) (hacyc : ∀ x, ¬ TransGen (AtLeast T γ) x x) {a b : X}
    (hab : AtLeast T γ a b) : out.P a b := by
  have hne : a ≠ b := by rintro rfl; exact hacyc a (.single hab)
  by_contra hn
  have hba := (out.not_P_iff hne).1 hn
  have hpath := h a b hab hba
  have : TransGen (AtLeast T γ) b b :=
    TransGen.tail' (ReflTransGen.mono (fun _ _ h => h.1) _ _ hpath) hab
  exact hacyc b this

/-- The reported profile `P` coincides with the true profile `T` outside the set `F` of faulty
replicas. Faulty replicas may report arbitrary (total) orders. -/
def Agree (T P : Profile ι X) (F : Finset ι) : Prop := ∀ i ∉ F, P i = T i

/-- Faulty replicas shift each count by at most `|F|`. -/
theorem count_le_count_add {T P : Profile ι X} {F : Finset ι} (h : Agree T P F) (a b : X) :
    count T a b ≤ count P a b + F.card := by
  classical
  unfold count
  calc #{i | (T i).P a b} ≤ #((univ.filter fun i => (P i).P a b) ∪ F) := by
        apply card_le_card; intro i; simp only [mem_filter, mem_univ, true_and, mem_union]
        intro hi; by_cases hF : i ∈ F
        · exact Or.inr hF
        · exact Or.inl (by rw [h i hF]; exact hi)
    _ ≤ _ := card_union_le _ _

omit [Fintype ι] in
theorem Agree.symm {T P : Profile ι X} {F : Finset ι} (h : Agree T P F) : Agree P T F :=
  fun i hi => (h i hi).symm

end Podc.FairOrderingSocialChoice
