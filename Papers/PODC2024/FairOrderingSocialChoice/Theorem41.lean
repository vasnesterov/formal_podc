import Papers.PODC2024.FairOrderingSocialChoice.Defs
import Papers.PODC2024.FairOrderingSocialChoice.RankedPairs

/-!
# Theorem 4.1: Ranked Pairs is `(γ, f/n)`-minimally-batch-order-fair for every `γ`

Ranked Pairs (Algorithm 2) on the *reported* profile `P`: edges `(a, b)` are processed in
decreasing order of the reported count `count P a b`, ties broken by an arbitrary fixed injective
rule `tb`; an edge is accepted unless it closes a cycle; the output is the transitive closure.

* `rpPref key hkey`: the output of the greedy selection for any injective processing order, as a
  strict total order (`Pref X`).
* `minimalBatchFair_of_approx`: if the weights used to order the edges are within `ε` of the true
  weights, the output is `(γ, ε)`-minimally-batch-order-fair for **every** `γ`.
* `theorem_4_1`: Ranked Pairs on a profile reported with `f = |F|` faulty replicas is
  `(γ, f/n)`-minimally-batch-order-fair for every `γ`; the algorithm does not depend on `γ`, `f`.
* `lemma_6_11`: the same with edge weights rounded to the nearest `1/k` before ordering, with
  `δ = f/n + 1/(2k)` (the fairness half of Lemma 6.11, for the non-streaming algorithm).
-/

namespace Podc.FairOrderingSocialChoice

open Cslib.SocialChoice Finset Relation RP

variable {ι X : Type*} [Fintype ι]

section Output

variable {β : Type*} [LinearOrder β] [WellFoundedLT β]

/-- The output of Ranked Pairs on all of `X` for an injective processing order `key`, as a strict
total order. -/
noncomputable def rpPref (key : X × X → β) (hkey : Function.Injective key) : Pref X where
  P := rpLt Set.univ key
  irrefl := rpLt_irrefl fun _ _ _ _ _ _ h => hkey h
  trans := rpLt_trans
  total := rpLt_total (Set.mem_univ _) (Set.mem_univ _)

/-- Ranked Pairs with approximately correct weights. Suppose edges are processed in an order in
which an earlier edge never has a smaller weight `w`, and `w` is within `ε` of the true weight
`count T a b / n`. Then the output is `(γ, ε)`-minimally-batch-order-fair for every `γ`. -/
theorem minimalBatchFair_of_approx (T : Profile ι X) (w : X → X → ℝ) (ε : ℝ)
    (hw : ∀ a b, |w a b - count T a b / Fintype.card ι| ≤ ε)
    (key : X × X → β) (hkey : Function.Injective key)
    (hmono : ∀ e e' : X × X, key e' < key e → w e.1 e.2 ≤ w e'.1 e'.2) (γ : ℝ) :
    MinimalBatchFair T γ ε (rpPref key hkey) := by
  intro a b hab hba
  have hba' : rpLt Set.univ key b a := hba
  have hne : a ≠ b := by rintro rfl; exact (rpPref key hkey).irrefl a hba
  have hrej : ¬ accepted Set.univ key (a, b) :=
    not_accepted_of_rpLt (fun _ _ _ _ _ _ h => hkey h) hba'
  have hpath := rejected_path (Set.mem_univ a) (Set.mem_univ b) hne hrej
  refine rtg_mono (fun x y hxy => ⟨?_, TransGen.single hxy.2⟩) hpath
  -- the edge `(x, y)` was processed before `(a, b)`
  have hwxy : w a b ≤ w x y := hmono (a, b) (x, y) hxy.1
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hn | hn
  · simp [AtLeast, hn]
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have h1 := (abs_le.1 (hw a b))
  have h2 := (abs_le.1 (hw x y))
  have hab' : γ ≤ count T a b / Fintype.card ι := by
    rw [le_div_iff₀ hnR]; exact hab
  unfold AtLeast
  rw [← le_div_iff₀ hnR]
  linarith

end Output

/-- Faulty replicas move each weight by at most `|F| / n`. -/
theorem weight_dev {T P : Profile ι X} {F : Finset ι} (hTP : Agree T P F) (a b : X) :
    |(count P a b : ℝ) / Fintype.card ι - count T a b / Fintype.card ι|
      ≤ F.card / Fintype.card ι := by
  have h1 : (count T a b : ℝ) ≤ count P a b + F.card := by
    exact_mod_cast count_le_count_add hTP a b
  have h2 : (count P a b : ℝ) ≤ count T a b + F.card := by
    exact_mod_cast count_le_count_add hTP.symm a b
  rw [← sub_div, abs_div, Nat.abs_cast]
  gcongr
  rw [abs_le]; constructor <;> linarith

/-- The processing order of Ranked Pairs on the profile `σ`: decreasing count, ties broken by
the injective rule `tb`. -/
noncomputable def rpKey (σ : Profile ι X) (tb : X × X → ℕ) (e : X × X) : ℕ ×ₗ ℕ :=
  toLex (Fintype.card ι - count σ e.1 e.2, tb e)

theorem rpKey_injective (σ : Profile ι X) {tb : X × X → ℕ} (htb : Function.Injective tb) :
    Function.Injective (rpKey σ tb) := by
  intro e e' h
  exact htb (congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) h)

/-- An edge processed earlier has at least the same count. -/
theorem count_le_of_rpKey_lt (σ : Profile ι X) (tb : X × X → ℕ) {e e' : X × X}
    (h : rpKey σ tb e' < rpKey σ tb e) : count σ e.1 e.2 ≤ count σ e'.1 e'.2 := by
  have h1 := count_le σ e.1 e.2
  have h2 := count_le σ e'.1 e'.2
  unfold rpKey at h
  rcases (Prod.Lex.toLex_lt_toLex).1 h with h | ⟨h, -⟩ <;> omega

/-- **Ranked Pairs Voting** (Algorithm 2) on the reported profile `σ`, with tie-breaking rule
`tb`. -/
noncomputable def rankedPairs (σ : Profile ι X) (tb : X × X → ℕ) (htb : Function.Injective tb) : Pref X :=
  rpPref (rpKey σ tb) (rpKey_injective σ htb)

/-- **Theorem 4.1** of [Ramseyer–Goel]. Let `T` be the true orderings and `P` the reported ones,
which differ only on the `f = |F|` faulty replicas. Ranked Pairs on `P` (with any tie-breaking
rule) satisfies `(γ, f/n)`-minimal-batch-order-fairness simultaneously for every `γ`; the
algorithm does not depend on `γ` or on a bound on `f`. -/
theorem theorem_4_1 (T P : Profile ι X) (F : Finset ι) (hTP : Agree T P F)
    (tb : X × X → ℕ) (htb : Function.Injective tb) (γ : ℝ) :
    MinimalBatchFair T γ (F.card / Fintype.card ι) (rankedPairs P tb htb) := by
  apply minimalBatchFair_of_approx T (fun a b => (count P a b : ℝ) / Fintype.card ι)
  · intro a b
    exact weight_dev hTP a b
  · intro e e' h
    gcongr
    exact count_le_of_rpKey_lt P tb h

/-- Weights rounded to the nearest multiple of `1/k` (Section 6.3). -/
noncomputable def roundedWeight (σ : Profile ι X) (k : ℕ) (a b : X) : ℝ :=
  round ((k : ℝ) * (count σ a b / Fintype.card ι)) / k

/-- **Lemma 6.11** of [Ramseyer–Goel] (fairness part, for Ranked Pairs on rounded weights).
Processing edges in decreasing order of the weights rounded to the nearest `1/k` (ties broken
arbitrarily, i.e. by any injective order compatible with the rounded weights) achieves
`(γ, f/n + 1/(2k))`-minimal-batch-order-fairness for every `γ`. -/
theorem lemma_6_11 {β : Type*} [LinearOrder β] [WellFoundedLT β]
    (T P : Profile ι X) (F : Finset ι) (hTP : Agree T P F) (k : ℕ) (hk : 0 < k)
    (key : X × X → β) (hkey : Function.Injective key)
    (hmono : ∀ e e' : X × X, key e' < key e →
      roundedWeight P k e.1 e.2 ≤ roundedWeight P k e'.1 e'.2) (γ : ℝ) :
    MinimalBatchFair T γ (F.card / Fintype.card ι + 1 / (2 * k)) (rpPref key hkey) := by
  apply minimalBatchFair_of_approx T (roundedWeight P k) _ _ key hkey hmono
  intro a b
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hround : |roundedWeight P k a b - count P a b / Fintype.card ι| ≤ 1 / (2 * k) := by
    unfold roundedWeight
    set x : ℝ := (k : ℝ) * (count P a b / Fintype.card ι)
    have hx : (count P a b : ℝ) / Fintype.card ι = x / k := by
      simp only [x]; field_simp
    have := abs_sub_round x
    rw [hx, ← sub_div, abs_div, abs_of_pos hkR, abs_sub_comm, div_le_div_iff₀ hkR (by positivity)]
    nlinarith
  have hfault : |(count P a b : ℝ) / Fintype.card ι - count T a b / Fintype.card ι|
      ≤ F.card / Fintype.card ι := by
    exact weight_dev hTP a b
  calc _ = |(roundedWeight P k a b - count P a b / Fintype.card ι) +
        ((count P a b : ℝ) / Fintype.card ι - count T a b / Fintype.card ι)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by linarith

end Podc.FairOrderingSocialChoice
