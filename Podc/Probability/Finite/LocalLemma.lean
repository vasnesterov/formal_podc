import Cslib.Probability.Finite.Uniform
import Mathlib.Analysis.Complex.ExponentialBounds

-- CSLib candidate: Cslib/Probability/Finite/LocalLemma.lean

/-!
# The Lovász Local Lemma (variable version, uniform product space)

We work on a finite product space `∀ i, Ω i` (finitely many independent variables, each uniform
on a finite nonempty range) with probabilities computed by counting (`Cslib.Probability.uprob`).
A finite family of *bad events* `A e`, `e : E`, is given together with variable sets `vbl e`:
the event `A e` is determined by the variables in `vbl e`. Two events are *dependent* if their
variable sets intersect; `dependencyNbhd vbl e` is the set of events `e' ≠ e` dependent on `e`.

## Main statements

* `uprob_and_eq_mul_of_dependsOn`: events determined by disjoint sets of variables are
  independent, `Pr[P ∧ Q] = Pr[P] · Pr[Q]`.
* `uprob_and_forall_not_le`: the key inequality of the local lemma, in multiplicative form
  `Pr[A e ∧ ⋀_{e' ∈ S} ¬A e'] ≤ x e · Pr[⋀_{e' ∈ S} ¬A e']` for `e ∉ S`.
* `prod_one_sub_le_uprob_forall_not` (asymmetric LLL, probability bound): if
  `Pr[A e] ≤ x e ∏_{e' ∈ Γ(e)} (1 - x e')` with `0 ≤ x e ≤ 1`, then
  `∏_e (1 - x e) ≤ Pr[no bad event]`.
* `exists_forall_not_of_asymmetric` (asymmetric LLL): if moreover `x e < 1`, some outcome avoids
  all bad events.
* `exists_forall_not_of_symmetric` (symmetric LLL): if `Pr[A e] ≤ p`, `|Γ(e)| ≤ d` and
  `e p (d + 1) ≤ 1`, some outcome avoids all bad events.
* Counting forms of the symmetric LLL: `exists_forall_not_of_card_mul_exp_le` and
  `exists_forall_not_of_card_mul_three_le` (in `ℕ`, with the constant `3 > e`).

## Proof

The standard one (Erdős–Lovász, Spencer): strong induction on `|S|`, splitting `S` into the
events dependent on `e` and the rest (which is independent of `A e`); the conditional
probabilities are cross-multiplied, so no division by a possibly zero probability occurs.
-/

open Finset

namespace Cslib.Probability

/-! ### Basic laws -/

section Basic

variable {X : Type*} [Fintype X]

/-- Splitting an event along another one: `Pr[E] = Pr[E ∧ F] + Pr[E ∧ ¬F]`. -/
theorem uprob_eq_uprob_and_add_uprob_and_not (E F : X → Prop) :
    uprob E = uprob (fun x => E x ∧ F x) + uprob (fun x => E x ∧ ¬ F x) := by
  classical
  simp only [uprob_eq_card_filter, ← add_div]
  congr 1
  rw [← filter_filter, ← filter_filter]
  exact_mod_cast (card_filter_add_card_filter_not (s := univ.filter E) F).symm

/-- `uprob` is invariant under an equivalence of sample spaces. -/
theorem uprob_comp_equiv {Y : Type*} [Fintype Y] (e : X ≃ Y) (E : Y → Prop) :
    uprob (fun x => E (e x)) = uprob E := by
  unfold uprob
  rw [Fintype.card_congr e, Nat.card_congr (e.subtypeEquiv fun _ => Iff.rfl)]

/-- **Independence of the factors of a product.** Under the uniform distribution on `Y × Z`,
`Pr[P p.1 ∧ Q p.2] = Pr[P] · Pr[Q]`. -/
theorem uprob_prod {Y Z : Type*} [Fintype Y] [Fintype Z] (P : Y → Prop) (Q : Z → Prop) :
    uprob (fun p : Y × Z => P p.1 ∧ Q p.2) = uprob P * uprob Q := by
  unfold uprob
  rw [Nat.card_congr Equiv.subtypeProdEquivProd, Nat.card_prod, Fintype.card_prod]
  push_cast
  rw [div_mul_div_comm]

/-- The sure event has probability `1` on a nonempty sample space. -/
theorem uprob_true_eq_one [Nonempty X] : uprob (fun _ : X => True) = 1 := by
  rw [uprob_true, ite_eq_right_iff.2 fun h => absurd h Fintype.card_ne_zero]

end Basic

/-! ### Independence of events determined by disjoint sets of variables -/

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]

/-- **Independence on product spaces.** If `P` is determined by the coordinates in `J` and `Q`
by the coordinates outside `J`, then `Pr[P ∧ Q] = Pr[P] · Pr[Q]` under the uniform
distribution on `∀ i, Ω i`. -/
theorem uprob_and_eq_mul_of_dependsOn {P Q : (∀ i, Ω i) → Prop} (J : Finset ι)
    (hP : ∀ σ τ : ∀ i, Ω i, (∀ i ∈ J, σ i = τ i) → (P σ ↔ P τ))
    (hQ : ∀ σ τ : ∀ i, Ω i, (∀ i ∉ J, σ i = τ i) → (Q σ ↔ Q τ)) :
    uprob (fun σ => P σ ∧ Q σ) = uprob P * uprob Q := by
  rcases isEmpty_or_nonempty (∀ i, Ω i) with hX | hX
  · simp [uprob, Fintype.card_eq_zero]
  obtain ⟨σ₀⟩ := hX
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ J) Ω
  let P₁ : (∀ i : {i // i ∈ J}, Ω i) → Prop := fun y => P (e.symm (y, (e σ₀).2))
  let Q₁ : (∀ i : {i // i ∉ J}, Ω i) → Prop := fun z => Q (e.symm ((e σ₀).1, z))
  have hP₁ : ∀ σ, P σ ↔ P₁ (e σ).1 := fun σ => hP _ _ fun i hi => by
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  have hQ₁ : ∀ σ, Q σ ↔ Q₁ (e σ).2 := fun σ => hQ _ _ fun i hi => by
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  have : Nonempty (∀ i : {i // i ∈ J}, Ω i) := ⟨(e σ₀).1⟩
  have : Nonempty (∀ i : {i // i ∉ J}, Ω i) := ⟨(e σ₀).2⟩
  have hPQ : uprob (fun σ => P σ ∧ Q σ) = uprob P₁ * uprob Q₁ := by
    rw [← uprob_prod, ← uprob_comp_equiv e]
    simp only [hP₁, hQ₁]
  have h1 : uprob P = uprob P₁ := by
    rw [← mul_one (uprob P₁), ← uprob_true_eq_one (X := ∀ i : {i // i ∉ J}, Ω i),
      ← uprob_prod, ← uprob_comp_equiv e]
    simp only [and_true]
    exact congrArg uprob (funext fun σ => propext (hP₁ σ))
  have h2 : uprob Q = uprob Q₁ := by
    rw [← one_mul (uprob Q₁), ← uprob_true_eq_one (X := ∀ i : {i // i ∈ J}, Ω i),
      ← uprob_prod, ← uprob_comp_equiv e]
    simp only [true_and]
    exact congrArg uprob (funext fun σ => propext (hQ₁ σ))
  rw [hPQ, h1, h2]

end Pi

/-! ### The local lemma -/

section LocalLemma

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
  {E : Type*} [Fintype E] [DecidableEq E]

/-- The dependency neighbourhood `Γ(e)` of a bad event `e` in the variable setting: the events
`e' ≠ e` whose variable set meets that of `e`. -/
def dependencyNbhd (vbl : E → Finset ι) (e : E) : Finset E :=
  univ.filter fun e' => e' ≠ e ∧ ¬ Disjoint (vbl e) (vbl e')

omit [Fintype ι] in
/-- Membership in the dependency neighbourhood. -/
theorem mem_dependencyNbhd {vbl : E → Finset ι} {e e' : E} :
    e' ∈ dependencyNbhd vbl e ↔ e' ≠ e ∧ ¬ Disjoint (vbl e) (vbl e') := by
  simp [dependencyNbhd]

variable (A : E → (∀ i, Ω i) → Prop)

omit [Fintype E] in
/-- Adding one more good event: `Pr[⋀_{insert a U} ¬A] = Pr[⋀_U ¬A] - Pr[A a ∧ ⋀_U ¬A]`. -/
theorem uprob_forall_not_insert (a : E) (U : Finset E) :
    uprob (fun σ => ∀ e' ∈ insert a U, ¬ A e' σ) =
      uprob (fun σ => ∀ e' ∈ U, ¬ A e' σ) - uprob (fun σ => A a σ ∧ ∀ e' ∈ U, ¬ A e' σ) := by
  rw [uprob_eq_uprob_and_add_uprob_and_not (fun σ => ∀ e' ∈ U, ¬ A e' σ) (A a)]
  have h1 : (fun σ => ∀ e' ∈ insert a U, ¬ A e' σ) =
      fun σ => (∀ e' ∈ U, ¬ A e' σ) ∧ ¬ A a σ := by
    ext σ; simp [and_comm]
  have h2 : (fun σ => A a σ ∧ ∀ e' ∈ U, ¬ A e' σ) =
      fun σ => (∀ e' ∈ U, ¬ A e' σ) ∧ A a σ := by
    ext σ; exact and_comm
  rw [h1, h2]
  ring

variable {A} {x : E → ℝ}

omit [Fintype E] in
/-- The product step of the local lemma: if the key inequality holds for all sets of size `< n`,
then adding the events of `R` (disjoint from `T`, `|T ∪ R| ≤ n`) to `T` multiplies the
probability of avoiding all of them by at least `∏_{e ∈ R} (1 - x e)`. -/
theorem prod_one_sub_mul_le_uprob_forall_not (hx1 : ∀ e, x e ≤ 1)
    (n : ℕ) (ih : ∀ T : Finset E, #T < n → ∀ e ∉ T,
      uprob (fun σ => A e σ ∧ ∀ e' ∈ T, ¬ A e' σ) ≤ x e * uprob (fun σ => ∀ e' ∈ T, ¬ A e' σ))
    (T R : Finset E) (hTR : Disjoint T R) (hn : #(T ∪ R) ≤ n) :
    (∏ e ∈ R, (1 - x e)) * uprob (fun σ => ∀ e' ∈ T, ¬ A e' σ) ≤
      uprob (fun σ => ∀ e' ∈ T ∪ R, ¬ A e' σ) := by
  induction R using Finset.induction_on with
  | empty => simp
  | insert a R ha ihR =>
    rw [disjoint_insert_right] at hTR
    have haU : a ∉ T ∪ R := by simp [ha, hTR.1]
    have hU : T ∪ insert a R = insert a (T ∪ R) := by ext; simp
    rw [hU, card_insert_of_notMem haU] at hn
    have hlt : #(T ∪ R) < n := by omega
    have h1 := ihR hTR.2 hlt.le
    have h2 := ih (T ∪ R) hlt a haU
    rw [hU, uprob_forall_not_insert, prod_insert ha, mul_assoc]
    have hxa : 0 ≤ 1 - x a := by linarith [hx1 a]
    calc (1 - x a) * ((∏ e ∈ R, (1 - x e)) * uprob (fun σ => ∀ e' ∈ T, ¬ A e' σ))
        ≤ (1 - x a) * uprob (fun σ => ∀ e' ∈ T ∪ R, ¬ A e' σ) :=
          mul_le_mul_of_nonneg_left h1 hxa
      _ ≤ _ := by linarith

variable {vbl : E → Finset ι}

/-- **Key inequality of the Lovász Local Lemma** (multiplicative form of
`Pr[A e | ⋀_{e' ∈ S} ¬A e'] ≤ x e`). -/
theorem uprob_and_forall_not_le
    (hvbl : ∀ e σ τ, (∀ i ∈ vbl e, σ i = τ i) → (A e σ ↔ A e τ))
    (hx0 : ∀ e, 0 ≤ x e) (hx1 : ∀ e, x e ≤ 1)
    (hA : ∀ e, uprob (A e) ≤ x e * ∏ e' ∈ dependencyNbhd vbl e, (1 - x e'))
    (S : Finset E) (e : E) (he : e ∉ S) :
    uprob (fun σ => A e σ ∧ ∀ e' ∈ S, ¬ A e' σ) ≤ x e * uprob (fun σ => ∀ e' ∈ S, ¬ A e' σ) := by
  suffices H : ∀ n, ∀ S : Finset E, #S < n → ∀ e ∉ S,
      uprob (fun σ => A e σ ∧ ∀ e' ∈ S, ¬ A e' σ) ≤ x e * uprob (fun σ => ∀ e' ∈ S, ¬ A e' σ) from
    H _ S (Nat.lt_succ_self _) e he
  intro n
  induction n with
  | zero => intro S hS; simp at hS
  | succ n ih =>
    intro S hS e he
    set S₁ := S.filter (· ∈ dependencyNbhd vbl e)
    set S₂ := S.filter (· ∉ dependencyNbhd vbl e)
    have hS12 : S = S₂ ∪ S₁ := by ext; simp [S₁, S₂]; tauto
    have hdisj : Disjoint S₂ S₁ := disjoint_filter.2 fun _ _ h h' => h h'
    -- `⋀_{S₂} ¬A` is determined by the variables outside `vbl e`
    have hind : uprob (fun σ => A e σ ∧ ∀ e' ∈ S₂, ¬ A e' σ) =
        uprob (A e) * uprob (fun σ => ∀ e' ∈ S₂, ¬ A e' σ) := by
      refine uprob_and_eq_mul_of_dependsOn (vbl e) (hvbl e) fun σ τ h => ?_
      refine forall₂_congr fun e' he' => not_congr (hvbl e' σ τ fun i hi => h i fun hie => ?_)
      simp only [S₂, mem_filter, mem_dependencyNbhd, not_and, not_not] at he'
      have hne : e' ≠ e := fun h => he (h ▸ he'.1)
      exact disjoint_left.1 (he'.2 hne) hie hi
    have hprod : ∏ e' ∈ dependencyNbhd vbl e, (1 - x e') ≤ ∏ e' ∈ S₁, (1 - x e') :=
      prod_le_prod_of_subset_of_le_one₀ (fun i hi => (mem_filter.1 hi).2)
        (fun i _ => by linarith [hx1 i]) (fun i _ _ => by linarith [hx0 i])
    · have hstep := prod_one_sub_mul_le_uprob_forall_not hx1 n ih S₂ S₁ hdisj
        (by rw [← hS12]; omega)
      rw [← hS12] at hstep
      have hB₂ := uprob_nonneg (fun σ => ∀ e' ∈ S₂, ¬ A e' σ)
      calc uprob (fun σ => A e σ ∧ ∀ e' ∈ S, ¬ A e' σ)
          ≤ uprob (fun σ => A e σ ∧ ∀ e' ∈ S₂, ¬ A e' σ) :=
            uprob_mono fun σ h => ⟨h.1, fun e' he' => h.2 e' (filter_subset _ _ he')⟩
        _ = uprob (A e) * uprob (fun σ => ∀ e' ∈ S₂, ¬ A e' σ) := hind
        _ ≤ (x e * ∏ e' ∈ S₁, (1 - x e')) * uprob (fun σ => ∀ e' ∈ S₂, ¬ A e' σ) := by
            gcongr
            exact (hA e).trans (mul_le_mul_of_nonneg_left hprod (hx0 e))
        _ = x e * ((∏ e' ∈ S₁, (1 - x e')) * uprob (fun σ => ∀ e' ∈ S₂, ¬ A e' σ)) := by ring
        _ ≤ x e * uprob (fun σ => ∀ e' ∈ S, ¬ A e' σ) :=
            mul_le_mul_of_nonneg_left hstep (hx0 e)

variable [∀ i, Nonempty (Ω i)]

/-- **Lovász Local Lemma, asymmetric form (probability bound).** If each bad event `A e` is
determined by the variables `vbl e`, `0 ≤ x e ≤ 1`, and
`Pr[A e] ≤ x e · ∏_{e' ∈ Γ(e)} (1 - x e')`, then with probability at least `∏_e (1 - x e)` no
bad event happens. -/
theorem prod_one_sub_le_uprob_forall_not
    (hvbl : ∀ e σ τ, (∀ i ∈ vbl e, σ i = τ i) → (A e σ ↔ A e τ))
    (hx0 : ∀ e, 0 ≤ x e) (hx1 : ∀ e, x e ≤ 1)
    (hA : ∀ e, uprob (A e) ≤ x e * ∏ e' ∈ dependencyNbhd vbl e, (1 - x e')) :
    ∏ e, (1 - x e) ≤ uprob (fun σ => ∀ e, ¬ A e σ) := by
  have h := prod_one_sub_mul_le_uprob_forall_not (A := A) hx1 (Fintype.card E)
    (fun T _ e he => uprob_and_forall_not_le hvbl hx0 hx1 hA T e he) ∅ univ
    (disjoint_empty_left _) (by simp)
  simpa [uprob_true_eq_one] using h

/-- **Lovász Local Lemma, asymmetric form.** If each bad event `A e` is determined by the
variables `vbl e`, `0 ≤ x e < 1`, and `Pr[A e] ≤ x e · ∏_{e' ∈ Γ(e)} (1 - x e')`, then some
outcome avoids all bad events. -/
theorem exists_forall_not_of_asymmetric
    (hvbl : ∀ e σ τ, (∀ i ∈ vbl e, σ i = τ i) → (A e σ ↔ A e τ))
    (hx0 : ∀ e, 0 ≤ x e) (hx1 : ∀ e, x e < 1)
    (hA : ∀ e, uprob (A e) ≤ x e * ∏ e' ∈ dependencyNbhd vbl e, (1 - x e')) :
    ∃ σ : ∀ i, Ω i, ∀ e, ¬ A e σ := by
  refine exists_of_uprob_pos (lt_of_lt_of_le ?_
    (prod_one_sub_le_uprob_forall_not hvbl hx0 (fun e => (hx1 e).le) hA))
  exact prod_pos fun e _ => by linarith [hx1 e]

/-- `(1 + 1/d)^d ≤ e`, in the form `1 ≤ e · (1 - 1/(d+1))^d`. -/
theorem one_le_exp_one_mul_one_sub_inv_pow (d : ℕ) :
    1 ≤ Real.exp 1 * (1 - 1 / ((d : ℝ) + 1)) ^ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (1 + 1 / (d : ℝ)) ^ d ≤ Real.exp 1 := by
    calc (1 + 1 / (d : ℝ)) ^ d ≤ Real.exp (1 / d) ^ d := by
          gcongr
          linarith [Real.add_one_le_exp (1 / (d : ℝ))]
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul, mul_one_div_cancel hd'.ne']
  have h2 : (1 - 1 / ((d : ℝ) + 1)) * (1 + 1 / (d : ℝ)) = 1 := by
    field_simp; ring
  calc (1 : ℝ) = ((1 - 1 / ((d : ℝ) + 1)) * (1 + 1 / (d : ℝ))) ^ d := by rw [h2, one_pow]
    _ = (1 - 1 / ((d : ℝ) + 1)) ^ d * (1 + 1 / (d : ℝ)) ^ d := mul_pow _ _ _
    _ ≤ (1 - 1 / ((d : ℝ) + 1)) ^ d * Real.exp 1 := by
        gcongr
        refine pow_nonneg ?_ _
        rw [sub_nonneg, div_le_one (by positivity)]
        linarith
    _ = _ := mul_comm _ _

/-- **Lovász Local Lemma, symmetric form.** If each bad event `A e` is determined by the
variables `vbl e`, has probability at most `p`, depends on at most `d` other events, and
`e · p · (d + 1) ≤ 1`, then some outcome avoids all bad events. -/
theorem exists_forall_not_of_symmetric
    (hvbl : ∀ e σ τ, (∀ i ∈ vbl e, σ i = τ i) → (A e σ ↔ A e τ))
    (p : ℝ) (d : ℕ) (hp : ∀ e, uprob (A e) ≤ p) (hd : ∀ e, #(dependencyNbhd vbl e) ≤ d)
    (hpd : Real.exp 1 * p * (d + 1) ≤ 1) :
    ∃ σ : ∀ i, Ω i, ∀ e, ¬ A e σ := by
  have he1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.2 one_pos
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · -- no dependencies: `x e = Pr[A e] ≤ p ≤ 1/e < 1`
    have hΓ : ∀ e, dependencyNbhd vbl e = ∅ := fun e => card_eq_zero.1 (Nat.le_zero.1 (hd e))
    refine exists_forall_not_of_asymmetric (x := fun e => uprob (A e)) hvbl
      (fun e => uprob_nonneg _) (fun e => ?_) (fun e => by simp [hΓ e])
    have := hp e
    have := uprob_nonneg (A e)
    push_cast at hpd
    nlinarith
  · have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    set x : ℝ := 1 / ((d : ℝ) + 1) with hx
    have hxpos : 0 < x := by positivity
    have hx1 : x < 1 := by rw [hx, div_lt_one (by positivity)]; linarith
    refine exists_forall_not_of_asymmetric (x := fun _ => x) hvbl (fun _ => hxpos.le)
      (fun _ => hx1) (fun e => ?_)
    rw [prod_const]
    have hpow : (1 - x) ^ d ≤ (1 - x) ^ #(dependencyNbhd vbl e) :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (hd e)
    have hkey := one_le_exp_one_mul_one_sub_inv_pow d
    rw [← hx] at hkey
    -- `p ≤ x / e ≤ x (1 - x)^d`
    have hp' : p * Real.exp 1 ≤ x := by
      rw [hx, le_div_iff₀ (by positivity)]; linarith
    have hxe : x ≤ x * (Real.exp 1 * (1 - x) ^ d) := le_mul_of_one_le_right hxpos.le hkey
    have hpx : p ≤ x * (1 - x) ^ d := by
      have hepos : 0 < Real.exp 1 := Real.exp_pos 1
      have : p * Real.exp 1 ≤ x * (1 - x) ^ d * Real.exp 1 := by nlinarith
      exact le_of_mul_le_mul_right this hepos
    calc uprob (A e) ≤ p := hp e
      _ ≤ x * (1 - x) ^ d := hpx
      _ ≤ x * (1 - x) ^ #(dependencyNbhd vbl e) := mul_le_mul_of_nonneg_left hpow hxpos.le

/-- **Lovász Local Lemma, symmetric counting form.** If each bad event `A e` is determined by
the variables `vbl e`, depends on at most `d` other events, and
`#{σ | A e σ} · e · (d + 1) ≤ |∀ i, Ω i|`, then some outcome avoids all bad events. -/
theorem exists_forall_not_of_card_mul_exp_le [∀ e, DecidablePred (A e)]
    (hvbl : ∀ e σ τ, (∀ i ∈ vbl e, σ i = τ i) → (A e σ ↔ A e τ))
    (d : ℕ) (hd : ∀ e, #(dependencyNbhd vbl e) ≤ d)
    (hcard : ∀ e, (#(univ.filter (A e)) : ℝ) * (Real.exp 1 * (d + 1)) ≤
      Fintype.card (∀ i, Ω i)) :
    ∃ σ : ∀ i, Ω i, ∀ e, ¬ A e σ := by
  have hpos : (0 : ℝ) < Real.exp 1 * (d + 1) := by positivity
  refine exists_forall_not_of_symmetric hvbl (1 / (Real.exp 1 * (d + 1))) d (fun e => ?_) hd
    (le_of_eq (by field_simp))
  rw [uprob_le_iff, div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
  exact hcard e

/-- **Lovász Local Lemma, symmetric counting form in `ℕ`.** If each bad event `A e` is
determined by the variables `vbl e`, depends on at most `d` other events, and
`3 (d + 1) · #{σ | A e σ} ≤ |∀ i, Ω i|`, then some outcome avoids all bad events. -/
theorem exists_forall_not_of_card_mul_three_le [∀ e, DecidablePred (A e)]
    (hvbl : ∀ e σ τ, (∀ i ∈ vbl e, σ i = τ i) → (A e σ ↔ A e τ))
    (d : ℕ) (hd : ∀ e, #(dependencyNbhd vbl e) ≤ d)
    (hcard : ∀ e, #(univ.filter (A e)) * (3 * (d + 1)) ≤ Fintype.card (∀ i, Ω i)) :
    ∃ σ : ∀ i, Ω i, ∀ e, ¬ A e σ := by
  refine exists_forall_not_of_card_mul_exp_le hvbl d hd fun e => ?_
  have h3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have := hcard e
  calc (#(univ.filter (A e)) : ℝ) * (Real.exp 1 * (d + 1))
      ≤ (#(univ.filter (A e)) : ℝ) * (3 * (d + 1)) := by gcongr
    _ ≤ Fintype.card (∀ i, Ω i) := by exact_mod_cast this

end LocalLemma

end Cslib.Probability
