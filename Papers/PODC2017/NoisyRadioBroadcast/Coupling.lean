import Papers.PODC2017.NoisyRadioBroadcast.Model
import Cslib.Probability.Finite.Product

-- CSLib candidate: `Cslib/Probability/Finite/AdaptiveSampling.lean`

/-!
# Adaptive sampling of fresh coordinates preserves the product law

Let `y₀, y₁, …` be i.i.d. random elements of a finite set `B` with law `w`. Suppose that in step
`r` an adaptive procedure chooses an index `σ r y ∈ I` that depends only on `y₀, …, y_{r-1}`
(`Causal`) and never chooses the same index twice (`FreshUpTo`). Then the sequence `y` has the
same law as the sequence obtained by reading, in step `r`, the coordinate `z (σ r ·)` of an i.i.d.
array `z : I → B` (`couple σ b₀ z`). This is the coupling behind "the `j`-th transmission of
message `i` uses its own coin" arguments: it turns the round-indexed faults of an adaptive schedule
into faults indexed by (message, number of previous transmissions of that message), which are
independent across messages.

* `couple_eq` : `couple σ b₀ z r = z (σ r (couple σ b₀ z))`.
* `sum_couple` : `∑ z, (∏ i, w (z i)) * g (couple z |_R) = ∑ y, (∏ r, w (y r)) * g y`.
* `prob_eq_sum_couple` : the same for the probability `prob` of the noisy radio model.
-/

namespace Podc.NoisyRadioBroadcast

open Finset

section Coupling

variable {B I : Type*} (σ : ℕ → (ℕ → B) → I)

/-- `σ r y` depends only on `y 0, …, y (r - 1)`. -/
def Causal : Prop := ∀ r (y y' : ℕ → B), (∀ r' < r, y r' = y' r') → σ r y = σ r y'

/-- Along every sequence, the first `R` selected indices are distinct. -/
def FreshUpTo (R : ℕ) : Prop := ∀ (y : ℕ → B) r r', r < R → r' < R → σ r y = σ r' y → r = r'

/-- The sequence read off the array `z` by the adaptive selection `σ`. -/
noncomputable def couple (b₀ : B) (z : I → B) : ℕ → B
  | r => z (σ r (fun r' => if r' < r then couple b₀ z r' else b₀))
termination_by r => r
decreasing_by assumption

variable {σ}

theorem couple_eq (hσ : Causal σ) (b₀ : B) (z : I → B) (r : ℕ) :
    couple σ b₀ z r = z (σ r (couple σ b₀ z)) := by
  rw [couple]
  congr 1
  exact hσ r _ _ fun r' hr' => by simp [hr']

theorem couple_eq_iff (hσ : Causal σ) (b₀ : B) (z : I → B) (y : ℕ → B) (R : ℕ) :
    (∀ r < R, couple σ b₀ z r = y r) ↔ ∀ r < R, z (σ r y) = y r := by
  constructor
  · intro h r hr
    rw [← h r hr, couple_eq hσ, hσ r y (couple σ b₀ z) fun r' hr' => (h r' (hr'.trans hr)).symm]
  · intro h r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr
      rw [couple_eq hσ, hσ r (couple σ b₀ z) y fun r' hr' => ih r' hr' (hr'.trans hr)]
      exact h r hr

variable [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]

/-- Marginal of a product law on finitely many distinct coordinates. -/
theorem sum_prod_indicator_inj (w : B → ℝ) (hw : ∑ b, w b = 1) {R : ℕ} (J : Fin R → I)
    (hJ : Function.Injective J) (y : Fin R → B) :
    ∑ z : I → B, (∏ i, w (z i)) * (if ∀ r, z (J r) = y r then 1 else 0) = ∏ r, w (y r) := by
  classical
  -- the indicator as a product over coordinates
  set h : I → B → ℝ := fun i b =>
    if hi : ∃ r, J r = i then (if b = y hi.choose then 1 else 0) else 1 with hh
  have hind : ∀ z : I → B, (if ∀ r, z (J r) = y r then (1 : ℝ) else 0) = ∏ i, h i (z i) := by
    intro z
    have hch : ∀ r, (⟨r, rfl⟩ : ∃ r', J r' = J r).choose = r := fun r =>
      hJ (⟨r, rfl⟩ : ∃ r', J r' = J r).choose_spec
    by_cases hz : ∀ r, z (J r) = y r
    · rw [ite_eq_left hz]
      refine (prod_eq_one fun i _ => ?_).symm
      simp only [hh]
      split_ifs with hi h2
      · rfl
      · exfalso; apply h2
        obtain ⟨r, rfl⟩ := hi
        rw [hz r, hch r]
      · rfl
    · rw [ite_eq_right hz]
      push Not at hz
      obtain ⟨r, hr⟩ := hz
      refine (prod_eq_zero (mem_univ (J r)) ?_).symm
      simp only [hh]
      rw [dite_eq_left ⟨r, rfl⟩, hch r, ite_eq_right hr]
  simp_rw [hind, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => w b * h i b)]
  have hfac : ∀ i, ∑ b, w b * h i b = if hi : ∃ r, J r = i then w (y hi.choose) else 1 := by
    intro i
    simp only [hh]
    split_ifs with hi
    · simp
    · simpa using hw
  simp_rw [hfac]
  rw [← prod_subset (subset_univ (univ.image J)) (fun i _ hi => by
    rw [dite_eq_right]; rintro ⟨r, rfl⟩; exact hi (mem_image_of_mem J (mem_univ r)))]
  rw [prod_image fun a _ b _ hab => hJ hab]
  refine prod_congr rfl fun r _ => ?_
  rw [dite_eq_left ⟨r, rfl⟩]
  congr 2
  exact hJ (⟨r, rfl⟩ : ∃ r', J r' = J r).choose_spec

/-- Extends a finite sequence by the default `b₀`. -/
def extendSeq {R : ℕ} (b₀ : B) (y : Fin R → B) : ℕ → B := fun r =>
  if h : r < R then y ⟨r, h⟩ else b₀

/-- **Adaptive fresh sampling preserves the product law.** -/
theorem sum_couple (hσ : Causal σ) {R : ℕ} (hfresh : FreshUpTo σ R) (w : B → ℝ)
    (hw : ∑ b, w b = 1) (b₀ : B) (g : (Fin R → B) → ℝ) :
    ∑ z : I → B, (∏ i, w (z i)) * g (fun r => couple σ b₀ z r) =
      ∑ y : Fin R → B, (∏ r, w (y r)) * g y := by
  classical
  rw [← Finset.sum_fiberwise (s := univ) (g := fun z : I → B => fun r : Fin R => couple σ b₀ z r)]
  refine sum_congr rfl fun y _ => ?_
  set J : Fin R → I := fun r => σ r (extendSeq b₀ y) with hJdef
  have hJ : Function.Injective J := fun r r' h =>
    Fin.ext (hfresh _ _ _ r.2 r'.2 h)
  have hfib : ∀ z : I → B, ((fun r : Fin R => couple σ b₀ z r) = y) ↔ ∀ r, z (J r) = y r := by
    intro z
    have := couple_eq_iff hσ b₀ z (extendSeq b₀ y) R
    constructor
    · intro hz r
      have h2 := this.1 (fun r' hr' => by
        rw [← hz]; simp [extendSeq, hr']) r r.2
      simpa [extendSeq, hJdef] using h2
    · intro hz
      funext r
      have h2 := this.2 (fun r' hr' => by
        have := hz ⟨r', hr'⟩; simpa [extendSeq, hr', hJdef] using this) r r.2
      simpa [extendSeq] using h2
  rw [sum_filter]
  have : ∀ z : I → B, (if (fun r : Fin R => couple σ b₀ z r) = y then
      (∏ i, w (z i)) * g (fun r : Fin R => couple σ b₀ z r) else 0) =
      ((∏ i, w (z i)) * (if ∀ r, z (J r) = y r then 1 else 0)) * g y := by
    intro z
    by_cases hz : (fun r : Fin R => couple σ b₀ z r) = y
    · rw [ite_eq_left hz, ite_eq_left ((hfib z).1 hz), hz]; ring
    · rw [ite_eq_right hz, ite_eq_right (mt (hfib z).2 hz)]; ring
  simp_rw [this, ← sum_mul, sum_prod_indicator_inj w hw J hJ y]

end Coupling

/-! ### Application to the noisy radio model -/

section Radio

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An event of the coin sequence that depends only on the rounds `< R`. -/
def DeterminedUpTo (R : ℕ) (E : (ℕ → V → Bool) → Prop) : Prop :=
  ∀ ω ω' : ℕ → V → Bool, (∀ r < R, ω r = ω' r) → (E ω ↔ E ω')

variable {I : Type*} [Fintype I] [DecidableEq I] {σ : ℕ → (ℕ → V → Bool) → I}

open Classical in
/-- The probability of an event of the first `R` rounds, computed on an i.i.d. coin array read by
an adaptive fresh selection. -/
theorem prob_eq_sum_couple (hσ : Causal σ) {R : ℕ} (hfresh : FreshUpTo σ R) (p : ℝ)
    {E : (ℕ → V → Bool) → Prop} (hE : DeterminedUpTo R E) :
    prob p R E = ∑ z : I → V → Bool, (∏ i, Cslib.Probability.coinProb (1 - p) (z i)) *
      if E (couple σ (fun _ => true) z) then 1 else 0 := by
  have := sum_couple hσ hfresh (Cslib.Probability.coinProb (1 - p))
    (Cslib.Probability.sum_coinProb _) (fun _ => true)
    (fun y => if E (extendCoins y) then (1 : ℝ) else 0)
  rw [prob, ← this]
  refine sum_congr rfl fun z _ => ?_
  congr 2
  exact propext (hE _ _ fun r hr => by simp [extendCoins, hr])

end Radio

end Podc.NoisyRadioBroadcast
