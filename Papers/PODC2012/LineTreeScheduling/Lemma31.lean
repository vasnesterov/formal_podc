import Papers.PODC2012.LineTreeScheduling.Framework

/-!
# Lemma 3.1: the approximation guarantee of the two-phase framework (unit heights)

The unit-height raising rule (`δ(d) = s/(|π(d)|+1)`, raise `α(a_d)` and every `β(e)`, `e ∈ π(d)`,
by `δ(d)`) and the second phase that pops the stack and adds an instance if it conflicts with no
instance selected so far. `lemma_3_1`: for every run satisfying the interference property with
critical sets of size `≤ Δ` after which all dual constraints are `λ`-satisfied, the output `S` is a
feasible solution and `p(S) ≥ λ/(Δ+1) · p(Opt)`; we prove it even against the LP optimum.
-/

set_option linter.unusedSectionVars false

namespace Podc.LineTreeScheduling

open Finset

variable {A D E : Type*} [DecidableEq A] [DecidableEq D] [DecidableEq E]

noncomputable section

/-- The raising rule of the unit-height framework (Section 3.2) with critical edges `crit`. -/
def unitRule (crit : D → Finset E) : Rule D E := ⟨fun _ => 1, fun _ => 1, crit⟩

namespace Inst

variable (I : Inst A D E)

lemma unitRule_wf {crit : D → Finset E} (h : ∀ d, crit d ⊆ I.path d) : (unitRule crit).WF I :=
  ⟨fun _ => zero_le_one, fun _ => zero_le_one, h⟩

/-- Acceptance test of the second phase (unit heights): `S ∪ {d}` is independent, i.e. `d`
conflicts with no instance of `S`. -/
def accU (S : Finset D) (d : D) : Prop := ∀ s ∈ S, ¬ I.Conflict d s

instance (S : Finset D) (d : D) : Decidable (I.accU S d) := Classical.dec _

/-- The solution output by the second phase (unit heights). -/
abbrev solU (Is : ℕ → Finset D) (T : ℕ) : Finset D := sol Is T I.accU

variable {I}
variable {Is : ℕ → Finset D} {T : ℕ}

lemma isIndep_phase2 (hind : ∀ t < T, I.IsIndep (Is t)) {n : ℕ} (hn : n ≤ T) :
    I.IsIndep (phase2 Is T I.accU n) := by
  induction n with
  | zero => intro d₁ h₁; simp [phase2] at h₁
  | succ n ih =>
    have ih := ih (by omega)
    intro d₁ h₁ d₂ h₂ hne
    simp only [phase2, Finset.mem_union, Finset.mem_filter] at h₁ h₂
    rcases h₁ with h₁ | ⟨h₁, a₁⟩ <;> rcases h₂ with h₂ | ⟨h₂, a₂⟩
    · exact ih d₁ h₁ d₂ h₂ hne
    · exact fun hc => a₂ d₁ h₁ ((I.conflict_comm).1 hc)
    · exact a₁ d₂ h₂
    · exact hind _ (by omega) d₁ h₁ d₂ h₂ hne

/-- **Lemma 3.1** (Chakaravarthy–Roy–Sabharwal, PODC 2012). Consider any run of the two-phase
framework with critical edge sets `crit` (`π(d) ⊆ path(d)`), satisfying the interference property,
with critical sets of size at most `Δ` (over all raised instances) and slackness parameter `λ`
(all dual constraints `λ`-satisfied at the end of the first phase). Then the second phase outputs a
feasible solution `S` with `λ/(Δ+1) · x ≤ p(S)` for every feasible solution `x` of the LP
relaxation, in particular `λ/(Δ+1) · p(Opt) ≤ p(S)` (`lemma_3_1_opt`). -/
theorem lemma_3_1 [Fintype A] [Fintype D] [Fintype E] {crit : D → Finset E}
    (hcrit : ∀ d, crit d ⊆ I.path d) (hv : I.ValidRun (unitRule crit) Is T)
    (hint : I.Interference (unitRule crit) Is T) {Δ : ℕ}
    (hΔ : ∀ t < T, ∀ d ∈ Is t, (crit d).card ≤ Δ) {lam : ℝ}
    (hlam : ∀ d, lam * I.profit d ≤ I.lhs (fun _ => 1) (I.run (unitRule crit) Is T) d)
    {x : D → ℝ} (hx : I.IsLPFeasible (fun _ => 1) x) :
    I.IsIndep (I.solU Is T) ∧ lam / (Δ + 1) * I.lpValue x ≤ I.profitOf (I.solU Is T) := by
  have hR := I.unitRule_wf hcrit
  refine ⟨isIndep_phase2 hv.indep le_rfl, ?_⟩
  have hcov : ∀ s < T, ∀ d' ∈ Is s, d' ∉ I.solU Is T →
      1 ≤ ∑ t ∈ (range T).filter (s < ·), ∑ d ∈ (Is t).filter (· ∈ I.solU Is T),
        I.weight (unitRule crit) d' d := by
    intro s hs d' hd' hnot
    rcases mem_sol_or_not_acc I.accU hs hd' with h | h
    · exact absurd h hnot
    · simp only [accU, not_forall, not_not] at h
      obtain ⟨d₀, hd₀, hc⟩ := h
      obtain ⟨t₀, hst, ht₀, hd₀t⟩ := mem_phase2_later I.accU hs hd₀
      refine one_le_cover_of_mem hR hv hst ht₀ hd₀t (phase2_subset_sol I.accU hd₀) ?_
      simp only [weight, unitRule, one_mul]
      rcases hc with hdem | hov
      · simp only [hdem, ↓reduceIte]
        have := Nat.cast_nonneg (α := ℝ) (crit d' ∩ I.path d₀).card
        linarith
      · have hne := hint s t₀ hst ht₀ d' hd' d₀ hd₀t hov
        have : (1 : ℝ) ≤ (crit d' ∩ I.path d₀).card := by
          exact_mod_cast Finset.card_pos.2 hne
        have : (0 : ℝ) ≤ if I.dem d' = I.dem d₀ then 1 else 0 := by split_ifs <;> norm_num
        linarith
  have key := lam_mul_lpValue_le hR hv (sol_subset_raised I.accU) hcov
    (M := Δ + 1) (by positivity)
    (fun s hs d hd => by
      simp only [unitRule, one_mul]
      exact_mod_cast Nat.add_le_add_left (hΔ s hs d hd) 1 |>.trans_eq (Nat.add_comm _ _))
    hlam hx
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

/-- Lemma 3.1 against an optimal (integral) solution. -/
theorem lemma_3_1_opt [Fintype A] [Fintype D] [Fintype E] {crit : D → Finset E}
    (hcrit : ∀ d, crit d ⊆ I.path d) (hv : I.ValidRun (unitRule crit) Is T)
    (hint : I.Interference (unitRule crit) Is T) {Δ : ℕ}
    (hΔ : ∀ t < T, ∀ d ∈ Is t, (crit d).card ≤ Δ) {lam : ℝ}
    (hlam : ∀ d, lam * I.profit d ≤ I.lhs (fun _ => 1) (I.run (unitRule crit) Is T) d)
    {O : Finset D} (hO : I.IsIndep O) :
    lam / (Δ + 1) * I.profitOf O ≤ I.profitOf (I.solU Is T) := by
  have := (lemma_3_1 hcrit hv hint hΔ hlam (Inst.IsIndep.isLPFeasible I hO)).2
  rwa [lpValue_ind] at this

end Inst

end

end Podc.LineTreeScheduling
