import Papers.PODC2019.CommComplexityBA.NoSetupAdversary

/-!
# Theorem 13 (BB form of Theorem 3): no sublinear-multicast Byzantine broadcast without setup

`theorem_13`: with plain authenticated channels and no setup, no protocol solves Byzantine
broadcast with probability `p > 5/6` against `C` adaptive corruptions while, also with probability
`p`, at most `C` honest nodes speak; provided `1 ≤ C` and `C + 2 ≤ n`. (`theorem_13_general`:
success probability `q₁` and communication probability `q₂` force `4 q₁ + 2 q₂ ≤ 5`, in the form
`1 ≤ 4 (1 - q₁) + 2 (1 - q₂)`.)

`n = 2` is a genuine exception: see `NoSetupCounterexample.lean`.

Proof (the paper's, made precise). Fix a non-sender `S`. For `x = (ω, ρ)` (node tapes, adversary
tapes) let `U_b(x)` be the untruncated two-copy system (copy 1 sender input `b`, tapes `ω`; copy 2
sender input `!b`, tapes `ρ`) and `E_b(x)` the event that both copies always have at most `C`
speakers. Let `σ` exchange the tapes of all nodes but `S` between `ω` and `ρ`; it preserves the
measure.
1. `Eᶜ` is covered by "too many speakers in `W_{c,b}`" and `σ⁻¹` "too many speakers in
   `W_{c,!b}`" (first crossing argument), so `μ E ≥ 1 - 2(1 - q₂)`.
2. On `E_b(x)`, `S`'s output in `W_{h,b}(x)` equals its output in `W_{h,!b}(σ x)` (symmetry).
   Hence `E_false ⊆ X_false ∪ σ⁻¹ X_true` where `X_b` = "`S` does not output `b` in `W_{h,b}`".
3. `X_b` is covered by the failure events of `W_{h,b}` and `W_{c,b}` (same execution: in
   `W_{c,b}` all nodes `≠ S` output `b` by validity; in `W_{h,b}` the honest `S` must agree with a
   forever-honest node `≠ S`), so `μ X_b ≤ 2(1 - q₁)`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open Cslib.Byzantine.LockStep (firstSome?)

namespace CommComplexityBA.NoSetup

variable {P M T : Type*} [DecidableEq P] [Fintype P]

/-! ### The tape exchange `σ` -/

section Swap

variable [MeasurableSpace T]

-- CSLib candidate (measure-preserving tape exchange)
/-- Exchange the tapes of all nodes except `S` between the two components. -/
noncomputable def swapE (S : P) : ((P → T) × (P → T)) ≃ᵐ ((P → T) × (P → T)) :=
  (MeasurableEquiv.arrowProdEquivProdArrow T T P).symm.trans
    ((MeasurableEquiv.piCongrRight fun j => if j = S then MeasurableEquiv.refl (T × T)
      else MeasurableEquiv.prodComm).trans (MeasurableEquiv.arrowProdEquivProdArrow T T P))

lemma swapE_apply (S : P) (x : (P → T) × (P → T)) :
    swapE S x = (Function.update x.2 S (x.1 S), Function.update x.1 S (x.2 S)) := by
  ext j <;> by_cases h : j = S
  all_goals
    first
    | (subst h; simp [swapE, MeasurableEquiv.arrowProdEquivProdArrow,
        MeasurableEquiv.piCongrRight])
    | (simp [swapE, h, MeasurableEquiv.arrowProdEquivProdArrow,
        MeasurableEquiv.piCongrRight, Function.update_of_ne h]; rfl)

instance (ν : P → Measure T) [∀ j, IsProbabilityMeasure (ν j)] : IsProbabilityMeasure (μ2 ν) := by
  unfold μ2; infer_instance

lemma swapE_mp (S : P) (ν : P → Measure T) [∀ j, IsProbabilityMeasure (ν j)] :
    MeasurePreserving (swapE S) (μ2 ν) (μ2 ν) := by
  have h1 := measurePreserving_arrowProdEquivProdArrow T T P ν ν
  refine (h1.comp ?_).comp h1.symm
  refine measurePreserving_pi _ _ fun j => ?_
  by_cases h : j = S
  · subst h; simp only [ite_true]; exact MeasurePreserving.id _
  · simp only [h, ite_false]; exact Measure.measurePreserving_swap

end Swap

namespace Protocol

/-- Forever-honest nodes exist when the adversary's budget is smaller than a set of nodes. -/
lemma exists_honest {I R : Type*} (π : Protocol P I M T) (inp : P → I) (ω : P → T) {C : ℕ}
    (A : Adversary P M R C) (ρ : R) (W : Finset P) (hW : C < W.card) :
    ∃ w ∈ W, π.Honest inp ω A ρ w := by
  classical
  have hmono : ∀ {r r'}, r ≤ r' → A.corrupt ρ (π.run inp ω A ρ r).2 ⊆
      A.corrupt ρ (π.run inp ω A ρ r').2 := by
    intro r r' h
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (A.corrupt_mono ρ _ _)
  by_contra hcon
  push Not at hcon
  simp only [Honest, not_forall, not_not] at hcon
  choose! R hR using hcon
  have hsub : W ⊆ A.corrupt ρ (π.run inp ω A ρ (W.sup R)).2 := fun w hw =>
    hmono (Finset.le_sup hw) (hR w hw)
  have := (Finset.card_le_card hsub).trans (A.card_corrupt ρ _)
  omega

variable (π : Protocol P (Option Bool) M T) (s S : P) (C : ℕ)

/-- The two-copy parameters of world `W_b` at `(ω, ρ)` (copy 2 truncated iff `t2`). -/
def par (b : Bool) (ω ρ : P → T) (t1 t2 : Bool) : TCParams P (Option Bool) T :=
  wParams S (bbInput s (!b)) (bbInput s b) ω ρ t1 t2

lemma copyTraffic_eq_sent (b : Bool) (ω : P → T) (hS : MHistory P M) (h : P → MHistory P M) :
    π.copyTraffic S (ω S) (bbInput s b S) ω (bbInput s b) hS h =
      π.sent (bbInput s b) ω (Function.update h S hS) := by
  simp [copyTraffic]

lemma run_W (A : Adversary P M (P → T) C) (hA : A.inject = π.wInject S C (bbInput s (!b)))
    (ω ρ : P → T) (r : ℕ) :
    (π.run (bbInput s b) ω A ρ r).1 =
      Function.update (π.tcRun S C (par s S b ω ρ false true) r).h1 S
        (π.tcRun S C (par s S b ω ρ false true) r).hS := by
  simp only [run, hA]
  rw [π.run_eq_tc S C (bbInput s (!b)) (bbInput s b) ω ρ r]
  rfl

lemma output_S_W (A : Adversary P M (P → T) C) (hA : A.inject = π.wInject S C (bbInput s (!b)))
    (ω ρ : P → T) :
    π.output (bbInput s b) ω A ρ S = firstSome? fun r =>
      π.decide S (bbInput s b S) (ω S) (π.tcRun S C (par s S b ω ρ false true) r).hS := by
  simp only [output, π.run_W s S C A hA, Function.update_self]

/-- Members of the copy-1 speaker set speak in the execution of `W`. -/
lemma speaks_of_mem_sp1 (A : Adversary P M (P → T) C)
    (hA : A.inject = π.wInject S C (bbInput s (!b))) (ω ρ : P → T) (r : ℕ) (j : P)
    (hj : j ∈ (π.tcRun S C (par s S b ω ρ false true) r).sp1) :
    j ≠ S ∧ π.Speaks (bbInput s b) ω A ρ j := by
  induction r with
  | zero => simp [tcRun] at hj
  | succ r ih =>
    rw [tcRun_sp1_succ, Finset.mem_union] at hj
    rcases hj with hj | hj
    · exact ih hj
    · obtain ⟨hjS, q, hq⟩ := mem_speakersOf.mp hj
      refine ⟨hjS, r, q, ?_⟩
      rw [π.run_W s S C A hA ω ρ r]
      have := π.copyTraffic_eq_sent s S b ω (π.tcRun S C (par s S b ω ρ false true) r).hS
        (π.tcRun S C (par s S b ω ρ false true) r).h1
      rw [← this]
      exact hq

variable (hsS : s ≠ S) (hC : 1 ≤ C)

include hsS in
lemma bbInput_S (b : Bool) : bbInput s b S = none := by simp [bbInput, Ne.symm hsS]

/-- In `W_{c,b}`, more than `C` copy-1 speakers make `FewSpeakers` fail. -/
lemma not_few_of_sp1 (b : Bool) (ω ρ : P → T) (r : ℕ)
    (h : C < (π.tcRun S C (par s S b ω ρ false true) r).sp1.card) :
    ¬ FewSpeakers π s b (π.advC S C (bbInput s (!b)) hC) ω ρ := by
  intro hfew
  have hsub : (↑(π.tcRun S C (par s S b ω ρ false true) r).sp1 : Set P) ⊆
      {p | π.Honest (bbInput s b) ω (π.advC S C (bbInput s (!b)) hC) ρ p ∧
        π.Speaks (bbInput s b) ω (π.advC S C (bbInput s (!b)) hC) ρ p} := by
    intro j hj
    obtain ⟨hjS, hsp⟩ := π.speaks_of_mem_sp1 s S C (π.advC S C (bbInput s (!b)) hC) rfl ω ρ r j hj
    exact ⟨fun r' => by simp [advC, hjS], hsp⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at this
  unfold FewSpeakers at hfew
  omega

include hsS in
/-- The two-copy system of `W_{!b}` at `σ x` is the swap of the system of `W_b` at `x` with the
truncation moved to copy 1. -/
lemma tc_sigma (b : Bool) (ω ρ : P → T) (r : ℕ) :
    π.tcRun S C (par s S (!b) (Function.update ρ S (ω S)) (Function.update ω S (ρ S)) false true) r
      = (π.tcRun S C (par s S b ω ρ true false) r).swap := by
  rw [← tcRun_swap]
  have hpar : par s S (!b) (Function.update ρ S (ω S)) (Function.update ω S (ρ S)) false true =
      { ({ (par s S b ω ρ true false).swap with
          τ1 := Function.update (par s S b ω ρ true false).swap.τ1 S (ω S) }) with
        τ2 := Function.update (par s S b ω ρ true false).swap.τ2 S (ρ S) } := by
    simp only [par, wParams, TCParams.swap, Bool.not_not, Function.update_self,
      bbInput_S s S hsS]
  rw [hpar, tcRun_update_τ2, tcRun_update_τ1]

/-- Truncation does not matter on `E`. -/
lemma tc_eq_untrunc_of_E (b : Bool) (ω ρ : P → T) (t1 t2 : Bool)
    (hE : ∀ r, (π.tcRun S C (par s S b ω ρ false false) r).sp1.card ≤ C ∧
      (π.tcRun S C (par s S b ω ρ false false) r).sp2.card ≤ C) (r : ℕ) :
    π.tcRun S C (par s S b ω ρ t1 t2) r = π.tcRun S C (par s S b ω ρ false false) r :=
  π.tcRun_eq_untrunc S C (par s S b ω ρ t1 t2) r
    (fun r' _ => ⟨fun _ => (hE (r' + 1)).1, fun _ => (hE (r' + 1)).2⟩) r le_rfl

include hsS in
/-- **Symmetry** (step 2). -/
lemma output_S_symm (b : Bool) (ω ρ : P → T)
    (hE : ∀ r, (π.tcRun S C (par s S b ω ρ false false) r).sp1.card ≤ C ∧
      (π.tcRun S C (par s S b ω ρ false false) r).sp2.card ≤ C) :
    π.output (bbInput s (!b)) (Function.update ρ S (ω S)) (π.advH S C (bbInput s (!!b)))
        (Function.update ω S (ρ S)) S =
      π.output (bbInput s b) ω (π.advH S C (bbInput s (!b))) ρ S := by
  rw [π.output_S_W s S C (π.advH S C (bbInput s (!!b))) rfl,
    π.output_S_W s S C (π.advH S C (bbInput s (!b))) rfl]
  congr 1
  funext r
  rw [π.tc_sigma s S C hsS b ω ρ r, π.tc_eq_untrunc_of_E s S C b ω ρ true false hE,
    π.tc_eq_untrunc_of_E s S C b ω ρ false true hE]
  simp [TCState.swap, bbInput_S s S hsS]

include hsS in
/-- **First crossing** (step 1). -/
lemma not_E (b : Bool) (ω ρ : P → T)
    (hE : ¬ ∀ r, (π.tcRun S C (par s S b ω ρ false false) r).sp1.card ≤ C ∧
      (π.tcRun S C (par s S b ω ρ false false) r).sp2.card ≤ C) :
    ¬ FewSpeakers π s b (π.advC S C (bbInput s (!b)) hC) ω ρ ∨
      ¬ FewSpeakers π s (!b) (π.advC S C (bbInput s (!!b)) hC) (Function.update ρ S (ω S))
        (Function.update ω S (ρ S)) := by
  classical
  push Not at hE
  set U := par s S b ω ρ false false
  have hex : ∃ r, ¬ ((π.tcRun S C U r).sp1.card ≤ C ∧ (π.tcRun S C U r).sp2.card ≤ C) := by
    obtain ⟨r, hr⟩ := hE
    exact ⟨r, fun h => by have := h.2; omega⟩
  set r0 := Nat.find hex with hr0
  have hmin : ∀ r < r0, (π.tcRun S C U r).sp1.card ≤ C ∧ (π.tcRun S C U r).sp2.card ≤ C :=
    fun r hr => not_not.mp (Nat.find_min hex hr)
  have hspec := Nat.find_spec hex
  rw [← hr0] at hspec
  obtain ⟨r1, hr1⟩ : ∃ r1, r0 = r1 + 1 := by
    rcases Nat.eq_zero_or_pos r0 with h0 | h0
    · exfalso; rw [h0] at hspec; exact hspec (by simp [tcRun, U])
    · exact ⟨r0 - 1, by omega⟩
  -- agreement of the truncated systems with `U` up to round `r1`
  have hagree : ∀ t1 t2 : Bool, π.tcRun S C (par s S b ω ρ t1 t2) r1 = π.tcRun S C U r1 :=
    fun t1 t2 => π.tcRun_eq_untrunc S C (par s S b ω ρ t1 t2) r1
      (fun r hr => ⟨fun _ => (hmin (r + 1) (by omega)).1, fun _ => (hmin (r + 1) (by omega)).2⟩)
      r1 le_rfl
  have hsp1 : (π.tcRun S C (par s S b ω ρ false true) r0).sp1 = (π.tcRun S C U r0).sp1 := by
    rw [hr1, tcRun_sp1_succ, tcRun_sp1_succ, hagree]; rfl
  have hsp2 : (π.tcRun S C (par s S b ω ρ true false) r0).sp2 = (π.tcRun S C U r0).sp2 := by
    rw [hr1, tcRun_sp2_succ, tcRun_sp2_succ, hagree]; rfl
  by_cases h1 : (π.tcRun S C U r0).sp1.card ≤ C
  · have h2 : C < (π.tcRun S C U r0).sp2.card := by
      by_contra h; exact hspec ⟨h1, by omega⟩
    right
    refine π.not_few_of_sp1 s S C hC (!b) _ _ r0 ?_
    rw [π.tc_sigma s S C hsS b ω ρ r0]
    simpa [TCState.swap, hsp2] using h2
  · left
    exact π.not_few_of_sp1 s S C hC b ω ρ r0 (by rw [hsp1]; omega)

include hsS in
/-- Step 3: if `S` does not output `b` in `W_{h,b}`, then `W_{h,b}` or `W_{c,b}` fails. -/
lemma fail_of_output_S (b : Bool) (ω ρ : P → T) (hn : C + 2 ≤ Fintype.card P)
    (hX : π.output (bbInput s b) ω (π.advH S C (bbInput s (!b))) ρ S ≠ some b) :
    ¬ BBGood π s b (π.advH S C (bbInput s (!b))) ω ρ ∨
      ¬ BBGood π s b (π.advC S C (bbInput s (!b)) hC) ω ρ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hH, hCg⟩ := hcon
  set AH := π.advH S C (bbInput s (!b))
  set AC := π.advC S C (bbInput s (!b)) hC
  have hout : ∀ p, π.output (bbInput s b) ω AH ρ p = π.output (bbInput s b) ω AC ρ p :=
    fun p => rfl
  have hHonC : ∀ p, p ≠ S → π.Honest (bbInput s b) ω AC ρ p := fun p hp r => by simp [AC, advC, hp]
  obtain ⟨u, hu, huH⟩ := exists_honest π (bbInput s b) ω AH ρ (Finset.univ.erase S) (by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega)
  have huS : u ≠ S := Finset.ne_of_mem_erase hu
  have hSH : π.Honest (bbInput s b) ω AH ρ S := fun r => π.not_mem_wCorrupt S C _ ρ _
  have hu_out : π.output (bbInput s b) ω AH ρ u = some b := by
    rw [hout]; exact hCg.2 (hHonC s hsS) u (hHonC u huS)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hH.1.1 S hSH)
  have := hH.1.2 S u y b hSH huH hy hu_out
  exact hX (hy.trans (by rw [this]))

end Protocol

variable [MeasurableSpace T]

/-- **Theorem 13**, general form: success probability `q₁` and probability `q₂` of at most `C`
honest speakers force `1 ≤ 4 (1 - q₁) + 2 (1 - q₂)`. -/
theorem theorem_13_general (π : Protocol P (Option Bool) M T) (ν : P → Measure T)
    [∀ j, IsProbabilityMeasure (ν j)] (s : P) {C : ℕ} (hC : 1 ≤ C)
    (hn : C + 2 ≤ Fintype.card P) {q₁ q₂ : ℝ} (hBB : SolvesBB π ν s C q₁)
    (hFew : FewSpeakersWP π ν s C q₂) :
    (1 : ENNReal) ≤ 4 * ENNReal.ofReal (1 - q₁) + 2 * ENNReal.ofReal (1 - q₂) := by
  classical
  -- a non-sender `S`
  obtain ⟨S, hS⟩ : ∃ S, S ≠ s := by
    by_contra h
    push Not at h
    have : Fintype.card P ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => (h a).trans (h b).symm
    omega
  have hsS : s ≠ S := Ne.symm hS
  set μ := μ2 ν
  set σ := swapE (T := T) S
  have hσ : ∀ A : Set ((P → T) × (P → T)), μ (σ ⁻¹' A) = μ A :=
    (swapE_mp S ν).measure_preimage_equiv
  -- the event `E` for `b = false`
  set E : Set ((P → T) × (P → T)) := {x | ∀ r,
    (π.tcRun S C (Protocol.par s S false x.1 x.2 false false) r).sp1.card ≤ C ∧
      (π.tcRun S C (Protocol.par s S false x.1 x.2 false false) r).sp2.card ≤ C}
  set AF := π.advC S C (bbInput s (!false)) hC
  set AT := π.advC S C (bbInput s (!!false)) hC
  -- step 1
  have hEc : Eᶜ ⊆ {x | ¬ FewSpeakers π s false AF x.1 x.2} ∪
      σ ⁻¹' {x | ¬ FewSpeakers π s (!false) AT x.1 x.2} := by
    intro x hx
    rcases π.not_E s S C hsS hC false x.1 x.2 hx with h | h
    · exact Or.inl h
    · right; simp only [Set.mem_preimage, Set.mem_ofPred_eq, σ, swapE_apply]; exact h
  have hE1 : 1 ≤ μ E + 2 * ENNReal.ofReal (1 - q₂) := by
    calc (1 : ENNReal) = μ Set.univ := measure_univ.symm
      _ ≤ μ E + μ Eᶜ := by rw [← Set.union_compl_self E]; exact measure_union_le _ _
      _ ≤ μ E + (μ {x | ¬ FewSpeakers π s false AF x.1 x.2} +
          μ (σ ⁻¹' {x | ¬ FewSpeakers π s (!false) AT x.1 x.2})) :=
          add_le_add le_rfl ((measure_mono hEc).trans (measure_union_le _ _))
      _ ≤ μ E + 2 * ENNReal.ofReal (1 - q₂) := by
          rw [hσ, two_mul]
          exact add_le_add le_rfl (add_le_add (hFew AF false) (hFew AT (!false)))
  -- steps 2 and 3
  set XF : Set ((P → T) × (P → T)) :=
    {x | π.output (bbInput s false) x.1 (π.advH S C (bbInput s (!false))) x.2 S ≠ some false}
  set XT : Set ((P → T) × (P → T)) :=
    {x | π.output (bbInput s (!false)) x.1 (π.advH S C (bbInput s (!!false))) x.2 S ≠
      some (!false)}
  have hEX : E ⊆ XF ∪ σ ⁻¹' XT := by
    intro x hx
    by_cases hF : x ∈ XF
    · exact Or.inl hF
    · right
      simp only [XF, Set.mem_ofPred_eq, not_not] at hF
      simp only [XT, Set.mem_preimage, Set.mem_ofPred_eq, σ, swapE_apply]
      rw [π.output_S_symm s S C hsS false x.1 x.2 hx, hF]
      simp
  have hX : ∀ b : Bool, μ {x | π.output (bbInput s b) x.1 (π.advH S C (bbInput s (!b))) x.2 S ≠
      some b} ≤ 2 * ENNReal.ofReal (1 - q₁) := by
    intro b
    calc _ ≤ μ ({x | ¬ BBGood π s b (π.advH S C (bbInput s (!b))) x.1 x.2} ∪
          {x | ¬ BBGood π s b (π.advC S C (bbInput s (!b)) hC) x.1 x.2}) :=
          measure_mono fun x hx => π.fail_of_output_S s S C hsS hC b x.1 x.2 hn hx
      _ ≤ _ := (measure_union_le _ _).trans (by rw [two_mul]; exact add_le_add (hBB _ b) (hBB _ b))
  have hE2 : μ E ≤ 4 * ENNReal.ofReal (1 - q₁) := by
    calc μ E ≤ μ XF + μ (σ ⁻¹' XT) := (measure_mono hEX).trans (measure_union_le _ _)
      _ = μ XF + μ XT := by rw [hσ]
      _ ≤ 2 * ENNReal.ofReal (1 - q₁) + 2 * ENNReal.ofReal (1 - q₁) := add_le_add (hX false)
          (hX true)
      _ = 4 * ENNReal.ofReal (1 - q₁) := by ring
  calc (1 : ENNReal) ≤ μ E + 2 * ENNReal.ofReal (1 - q₂) := hE1
    _ ≤ _ := add_le_add hE2 le_rfl

/-- **Theorem 13** (the Byzantine-broadcast form of Theorem 3). In the plain authenticated
channel model without setup, no protocol solves Byzantine broadcast with probability `p > 5/6`
against `C` adaptive corruptions while having at most `C` honest speakers (in particular multicast complexity `≤ C`)
with probability `p`; here `1 ≤ C` and `C + 2 ≤ n`. -/
theorem theorem_13 (π : Protocol P (Option Bool) M T) (ν : P → Measure T)
    [∀ j, IsProbabilityMeasure (ν j)] (s : P) {C : ℕ} (hC : 1 ≤ C)
    (hn : C + 2 ≤ Fintype.card P) {p : ℝ} (hp : 5 / 6 < p) :
    ¬ (SolvesBB π ν s C p ∧ FewSpeakersWP π ν s C p) := by
  rintro ⟨hBB, hFew⟩
  have h := theorem_13_general π ν s hC hn hBB hFew
  have h6 : (4 : ENNReal) * ENNReal.ofReal (1 - p) + 2 * ENNReal.ofReal (1 - p) =
      ENNReal.ofReal (6 * (1 - p)) := by
    rw [ENNReal.ofReal_mul (by norm_num), ← add_mul]; norm_num
  rw [h6, ENNReal.one_le_ofReal] at h
  linarith

end CommComplexityBA.NoSetup
