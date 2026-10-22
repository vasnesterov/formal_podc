import Papers.PODC2012.LineTreeScheduling.Framework

/-!
# Lemma 6.1: the framework for narrow instances (arbitrary heights)

Raising rule of Section 6.1: `δ(d) = s/(1 + 2h(d)|π(d)|²)`, `α(a_d) += δ(d)`,
`β(e) += 2|π(d)|δ(d)` for `e ∈ π(d)`. Second phase: add `d` if no instance of the same demand is
selected and the bandwidth constraints stay satisfied on all edges of `path(d)`.

`lemma_6_1`: if all heights are in `[0, 1/2]` (narrow instances), the run satisfies the
interference property, critical sets have size `≤ Δ` and all dual constraints are `λ`-satisfied,
then the output is feasible and `p(S) ≥ λ/(1+2Δ²) · p(Opt)` (even against the LP optimum).

The proof follows the paper; the pigeonhole step ("there is an edge `ẽ ∈ π(d')` carrying more than
`1/(2|π(d')|)`") is replaced by the equivalent double counting
`∑_{e ∈ π(d')} ∑_{d ∼ e} h(d) = ∑_d h(d) |π(d') ∩ path(d)| ≥ ∑_{d ∈ X} h(d)`.
-/

set_option linter.unusedSectionVars false

namespace Podc.LineTreeScheduling

open Finset

variable {A D E : Type*} [DecidableEq A] [DecidableEq D] [DecidableEq E]

noncomputable section

/-- The raising rule for narrow instances (Section 6.1) with heights `h` and critical edges
`crit`: the edge variables are raised by `2|π(d)| δ(d)`. -/
def narrowRule (h : D → ℝ) (crit : D → Finset E) : Rule D E :=
  ⟨h, fun d => 2 * (crit d).card, crit⟩

namespace Inst

variable (I : Inst A D E)

lemma narrowRule_wf {h : D → ℝ} (hh : ∀ d, 0 ≤ h d) {crit : D → Finset E}
    (hc : ∀ d, crit d ⊆ I.path d) : (narrowRule h crit).WF I :=
  ⟨hh, fun d => by simp only [narrowRule]; positivity, hc⟩

/-- Acceptance test of the second phase with heights: no instance of the same demand is selected,
and adding `d` keeps the total height on every edge of `path(d)` at most `1`. -/
def accH (h : D → ℝ) (S : Finset D) (d : D) : Prop :=
  (∀ s ∈ S, I.dem s ≠ I.dem d) ∧ ∀ e ∈ I.path d, h d + ∑ s ∈ S with e ∈ I.path s, h s ≤ 1

instance (h : D → ℝ) (S : Finset D) (d : D) : Decidable (I.accH h S d) := Classical.dec _

/-- The solution output by the second phase (heights `h`). -/
abbrev solH (h : D → ℝ) (Is : ℕ → Finset D) (T : ℕ) : Finset D := sol Is T (I.accH h)

variable {I}
variable {Is : ℕ → Finset D} {T : ℕ}

lemma isHFeasible_phase2 {h : D → ℝ} (hind : ∀ t < T, I.IsIndep (Is t)) {n : ℕ}
    (hn : n ≤ T) : I.IsHFeasible h (phase2 Is T (I.accH h) n) := by
  induction n with
  | zero => exact ⟨fun d₁ h₁ => by simp [phase2] at h₁, fun e => by simp [phase2]⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    set P := phase2 Is T (I.accH h) n
    set F := (Is (T - 1 - n)).filter (I.accH h P)
    have hF : I.IsIndep F := fun d₁ h₁ d₂ h₂ =>
      hind _ (by omega) d₁ (Finset.mem_filter.1 h₁).1 d₂ (Finset.mem_filter.1 h₂).1
    have hdisj : Disjoint P F := by
      rw [Finset.disjoint_left]
      intro d hP hF'
      exact (Finset.mem_filter.1 hF').2.1 d hP rfl
    show I.IsHFeasible h (P ∪ F)
    refine ⟨fun d₁ h₁ d₂ h₂ hne => ?_, fun e => ?_⟩
    · rcases Finset.mem_union.1 h₁ with h₁ | h₁ <;> rcases Finset.mem_union.1 h₂ with h₂ | h₂
      · exact ih1 d₁ h₁ d₂ h₂ hne
      · exact (Finset.mem_filter.1 h₂).2.1 d₁ h₁
      · exact fun hc => (Finset.mem_filter.1 h₁).2.1 d₂ h₂ hc.symm
      · exact fun hc => hF d₁ h₁ d₂ h₂ hne (Or.inl hc)
    · rw [Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hdisj)]
      by_cases hne : (F.filter (fun d => e ∈ I.path d)).Nonempty
      · obtain ⟨f, hf⟩ := hne
        have hsing : F.filter (fun d => e ∈ I.path d) = {f} := by
          refine Finset.eq_singleton_iff_unique_mem.2 ⟨hf, fun g hg => ?_⟩
          by_contra hgf
          have hg' := Finset.mem_filter.1 hg
          have hf' := Finset.mem_filter.1 hf
          exact hF g hg'.1 f hf'.1 hgf (Or.inr ⟨e, Finset.mem_inter.2 ⟨hg'.2, hf'.2⟩⟩)
        rw [hsing, Finset.sum_singleton]
        have hf' := Finset.mem_filter.1 hf
        have := (Finset.mem_filter.1 hf'.1).2.2 e hf'.2
        linarith
      · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty, add_zero]
        exact ih2 e

/-- **Lemma 6.1** (Chakaravarthy–Roy–Sabharwal, PODC 2012). Suppose all instances are narrow
(`0 ≤ h(d) ≤ 1/2`). Consider any run of the height framework with critical edge sets `crit`,
satisfying the interference property, with critical sets of size at most `Δ` and slackness
parameter `λ`. Then the second phase outputs a feasible solution `S` with
`λ/(1+2Δ²) · x ≤ p(S)` for every feasible solution `x` of the LP relaxation with heights; in
particular `λ/(1+2Δ²) · p(Opt) ≤ p(S)` (`lemma_6_1_opt`). -/
theorem lemma_6_1 [Fintype A] [Fintype D] [Fintype E] {h : D → ℝ} (hh0 : ∀ d, 0 ≤ h d)
    (hh : ∀ d, h d ≤ 1 / 2) {crit : D → Finset E} (hcrit : ∀ d, crit d ⊆ I.path d)
    (hv : I.ValidRun (narrowRule h crit) Is T) (hint : I.Interference (narrowRule h crit) Is T)
    {Δ : ℕ} (hΔ : ∀ t < T, ∀ d ∈ Is t, (crit d).card ≤ Δ) {lam : ℝ}
    (hlam : ∀ d, lam * I.profit d ≤ I.lhs h (I.run (narrowRule h crit) Is T) d)
    {x : D → ℝ} (hx : I.IsLPFeasible h x) :
    I.IsHFeasible h (I.solH h Is T) ∧
      lam / (1 + 2 * Δ ^ 2) * I.lpValue x ≤ I.profitOf (I.solH h Is T) := by
  have hR := I.narrowRule_wf hh0 hcrit
  refine ⟨isHFeasible_phase2 hv.indep le_rfl, ?_⟩
  set S := I.solH h Is T
  have hcov : ∀ s < T, ∀ d' ∈ Is s, d' ∉ S →
      1 ≤ ∑ t ∈ (range T).filter (s < ·), ∑ d ∈ (Is t).filter (· ∈ S),
        I.weight (narrowRule h crit) d' d := by
    intro s hs d' hd' hnot
    rcases mem_sol_or_not_acc (I.accH h) hs hd' with hm | hm
    · exact absurd hm hnot
    set P := phase2 Is T (I.accH h) (T - 1 - s)
    simp only [accH, not_and_or, not_forall, not_not, not_le] at hm
    rcases hm with ⟨d₀, hd₀, hdem⟩ | ⟨e, he, hgt⟩
    · -- killed by an instance of the same demand (the set `K₁`)
      obtain ⟨t₀, hst, ht₀, hd₀t⟩ := mem_phase2_later (I.accH h) hs hd₀
      refine one_le_cover_of_mem hR hv hst ht₀ hd₀t (phase2_subset_sol (I.accH h) hd₀) ?_
      simp only [weight, narrowRule, hdem.symm, ↓reduceIte]
      have := mul_nonneg (mul_nonneg (hh0 d₀) (by positivity : (0 : ℝ) ≤ 2 * (crit d').card))
        (Nat.cast_nonneg (α := ℝ) (crit d' ∩ I.path d₀).card)
      linarith
    · -- killed by the bandwidth constraint on the edge `e` (the set `K₂`)
      set X := P.filter (fun d => e ∈ I.path d)
      have hX : 1 / 2 < ∑ d ∈ X, h d := by linarith [hh d']
      -- every instance of `X` is a later member of `S` overlapping `d'`
      have hXmem : ∀ d ∈ X, ∃ t₀, s < t₀ ∧ t₀ < T ∧ d ∈ Is t₀ ∧ d ∈ S := by
        intro d hd
        obtain ⟨t₀, hst, ht₀, hdt⟩ := mem_phase2_later (I.accH h) hs (Finset.mem_filter.1 hd).1
        exact ⟨t₀, hst, ht₀, hdt, phase2_subset_sol (I.accH h) (Finset.mem_filter.1 hd).1⟩
      have hw : ∀ d ∈ X, 2 * h d ≤ I.weight (narrowRule h crit) d' d := by
        intro d hd
        obtain ⟨t₀, hst, ht₀, hdt, -⟩ := hXmem d hd
        have hne := hint s t₀ hst ht₀ d' hd' d hdt
          ⟨e, Finset.mem_inter.2 ⟨he, (Finset.mem_filter.1 hd).2⟩⟩
        have h1 : (1 : ℝ) ≤ (crit d' ∩ I.path d).card := by exact_mod_cast Finset.card_pos.2 hne
        have h2 : (1 : ℝ) ≤ (crit d').card := by
          exact_mod_cast Finset.card_pos.2 (hne.mono Finset.inter_subset_left)
        simp only [weight, narrowRule]
        have h3 : (0 : ℝ) ≤ if I.dem d' = I.dem d then 1 else 0 := by split_ifs <;> norm_num
        have h4 : 2 * h d ≤ h d * (2 * (crit d').card) * (crit d' ∩ I.path d).card := by
          have := hh0 d
          have : 2 * h d ≤ h d * (2 * (crit d').card) := by nlinarith
          nlinarith
        linarith
      rw [sum_filter_raised hR hv]
      have hsub : X ⊆ ((range T).filter (s < ·)).biUnion (fun t => (Is t).filter (· ∈ S)) := by
        intro d hd
        obtain ⟨t₀, hst, ht₀, hdt, hdS⟩ := hXmem d hd
        exact Finset.mem_biUnion.2 ⟨t₀, Finset.mem_filter.2 ⟨Finset.mem_range.2 ht₀, hst⟩,
          Finset.mem_filter.2 ⟨hdt, hdS⟩⟩
      calc (1 : ℝ) ≤ ∑ d ∈ X, 2 * h d := by rw [← Finset.mul_sum]; linarith
        _ ≤ ∑ d ∈ X, I.weight (narrowRule h crit) d' d := Finset.sum_le_sum hw
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => weight_nonneg hR d' d
  have key := lam_mul_lpValue_le hR hv (sol_subset_raised (I.accH h)) hcov
    (M := 1 + 2 * Δ ^ 2) (by positivity)
    (fun s hs d hd => by
      simp only [narrowRule]
      have : ((crit d).card : ℝ) ≤ Δ := by exact_mod_cast hΔ s hs d hd
      have : (0 : ℝ) ≤ (crit d).card := Nat.cast_nonneg _
      nlinarith)
    hlam hx
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

/-- Lemma 6.1 against an optimal (integral) solution. -/
theorem lemma_6_1_opt [Fintype A] [Fintype D] [Fintype E] {h : D → ℝ} (hh0 : ∀ d, 0 ≤ h d)
    (hh : ∀ d, h d ≤ 1 / 2) {crit : D → Finset E} (hcrit : ∀ d, crit d ⊆ I.path d)
    (hv : I.ValidRun (narrowRule h crit) Is T) (hint : I.Interference (narrowRule h crit) Is T)
    {Δ : ℕ} (hΔ : ∀ t < T, ∀ d ∈ Is t, (crit d).card ≤ Δ) {lam : ℝ}
    (hlam : ∀ d, lam * I.profit d ≤ I.lhs h (I.run (narrowRule h crit) Is T) d)
    {O : Finset D} (hO : I.IsHFeasible h O) :
    lam / (1 + 2 * Δ ^ 2) * I.profitOf O ≤ I.profitOf (I.solH h Is T) := by
  have := (lemma_6_1 hh0 hh hcrit hv hint hΔ hlam (Inst.IsHFeasible.isLPFeasible I hO)).2
  rwa [lpValue_ind] at this

end Inst

end

end Podc.LineTreeScheduling
