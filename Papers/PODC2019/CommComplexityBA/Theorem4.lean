import Papers.PODC2019.CommComplexityBA.LowerBound

/-!
# Theorems 4 and 1: `Ω(f²)` messages against a strongly adaptive adversary

* `theorem_4` (Byzantine broadcast, Theorem 4 of the paper): if a protocol solves Byzantine
  broadcast with probability `3/4 + ε` against every strongly adaptive (omission) adversary
  corrupting at most `f < n` nodes, then for some sender input and some adversary (a *static* one
  corrupting `⌈f/2⌉` nodes) the honest nodes send at least `ε f² / 2` messages in expectation.
  Since `ε ≤ 1/4`, this is more than the paper's `(εf)²` (`theorem_4_paper`).
* `theorem_1` (Byzantine agreement, Theorem 1 of the paper): the same bound for BA.
-/

set_option linter.unusedSectionVars false

open MeasureTheory

namespace CommComplexityBA

variable {P M Ω : Type*} [Fintype P] [DecidableEq P] [MeasurableSpace Ω] [Countable M]

lemma BBGood.termCons {f : ℕ} {π : Protocol P (Option Bool) M Ω} {s : P} {b : Bool}
    {A : Adversary P f} {ω : Ω} (h : BBGood π s b A ω) :
    TermCons (π.output (bbInput s b) ω A) (π.Honest (bbInput s b) ω A) := h.1

lemma BAGood.termCons {f : ℕ} {π : Protocol P Bool M Ω} {inp : P → Bool}
    {A : Adversary P f} {ω : Ω} (h : BAGood π inp A ω) :
    TermCons (π.output inp ω A) (π.Honest inp ω A) := h.1

/-- `⌈f/2⌉ · (⌊f/2⌋ + 1) ≥ f²/4`. -/
lemma four_mul_half_ge (f : ℕ) : f ^ 2 ≤ 4 * ((f + 1) / 2) * (f / 2 + 1) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' f
  · have h1 : (2 * j + 1) / 2 = j := by omega
    have h2 : 2 * j / 2 = j := by omega
    rw [h1, h2]; nlinarith
  · have h1 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    have h2 : (2 * j + 1) / 2 = j := by omega
    rw [h1, h2]; nlinarith

/-- From the core bound with `δ = 1/4 - ε`, `|V| = ⌈f/2⌉`, `k = ⌊f/2⌋` to `ε f² / 2`. -/
lemma final_arith (f : ℕ) (ε : ℝ) :
    ENNReal.ofReal (ε * f ^ 2 / 2) ≤
      ENNReal.ofReal ((1 / 2 - 2 * (1 / 4 - ε)) * (((f + 1) / 2 : ℕ) : ℝ) * ((f / 2 : ℕ) + 1)) := by
  rcases le_or_gt 0 ε with h0 | h0
  · apply ENNReal.ofReal_le_ofReal
    have h := four_mul_half_ge f
    have h' : ((f : ℝ)) ^ 2 ≤ 4 * (((f + 1) / 2 : ℕ) : ℝ) * (((f / 2 : ℕ) : ℝ) + 1) := by
      exact_mod_cast h
    nlinarith
  · rw [ENNReal.ofReal_of_nonpos]
    · exact bot_le
    · have : (0 : ℝ) ≤ (f : ℝ) ^ 2 := by positivity
      nlinarith

/-- For each node, its silent output is `some false` or `some true` with probability at most `1/2`
for at least one of the two values. -/
lemma silent_le_half {I : Type*} (π : Protocol P I M Ω) (hπ : π.IsMeasurable) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (p : P) (x : I) :
    ∃ v : Bool, μ {ω | π.silentOut p x ω = some v} ≤ 2⁻¹ := by
  by_contra h
  push Not at h
  have hdisj : Disjoint {ω | π.silentOut p x ω = some false} {ω | π.silentOut p x ω = some true} :=
    Set.disjoint_left.mpr fun ω h1 h2 => by simp_all
  have hU := measure_union (μ := μ) hdisj (π.fiberMeas_silentOut hπ p x (some true))
  have hle : μ ({ω | π.silentOut p x ω = some false} ∪ {ω | π.silentOut p x ω = some true}) ≤ 1 :=
    prob_le_one
  rw [hU] at hle
  have := ENNReal.add_lt_add (h false) (h true)
  rw [ENNReal.inv_two_add_inv_two] at this
  exact absurd hle (not_le.mpr this)

/-- Pick `m` nodes of `N` whose silent output (with input `x p`) is `v` with probability `≤ 1/2`,
for a common `v`, provided `2m ≤ |N| + 1`. -/
lemma exists_class {I : Type*} (π : Protocol P I M Ω) (hπ : π.IsMeasurable) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (x : P → I) (N : Finset P) (m : ℕ) (hm : 2 * m ≤ N.card + 1) :
    ∃ (v : Bool) (V : Finset P), V ⊆ N ∧ V.card = m ∧
      ∀ p ∈ V, μ {ω | π.silentOut p (x p) ω = some v} ≤ 2⁻¹ := by
  classical
  let C : Bool → Finset P := fun v => N.filter fun p => μ {ω | π.silentOut p (x p) ω = some v} ≤ 2⁻¹
  have hcov : N ⊆ C false ∪ C true := by
    intro p hp
    obtain ⟨v, hv⟩ := silent_le_half π hπ μ p (x p)
    cases v
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hv⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hv⟩)
  have hcard := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  have : m ≤ (C false).card ∨ m ≤ (C true).card := by omega
  obtain ⟨v, hv⟩ : ∃ v, m ≤ (C v).card := by
    rcases this with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  obtain ⟨V, hVC, hVcard⟩ := Finset.exists_subset_card_eq hv
  refine ⟨v, V, fun p hp => (Finset.mem_filter.mp (hVC hp)).1, hVcard, fun p hp => ?_⟩
  exact (Finset.mem_filter.mp (hVC hp)).2

/-- **Theorem 4** (Byzantine broadcast). If `π` solves Byzantine broadcast with probability
`3/4 + ε` against every strongly adaptive adversary corrupting at most `f < n` nodes, then there
are a sender input and an adversary (even a static one) under which the honest nodes send at least
`ε f² / 2` messages in expectation. (The paper states `(εf)²`, see `theorem_4_paper`.) -/
theorem theorem_4 (π : Protocol P (Option Bool) M Ω) (hπ : π.IsMeasurable) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : P) {f : ℕ} (hfn : f < Fintype.card P) {ε : ℝ} (hε : ε ≤ 1 / 4)
    (hsolve : SolvesBB π μ s f (3 / 4 + ε)) :
    ∃ (b : Bool) (A : Adversary P f),
      ENNReal.ofReal (ε * f ^ 2 / 2) ≤ ∫⁻ ω, π.honestMsgs (bbInput s b) ω A ∂μ := by
  classical
  rcases Nat.eq_zero_or_pos f with rfl | hf1
  · exact ⟨false, ⟨fun _ => ∅, fun _ _ _ => false, fun _ _ => le_rfl, fun _ => by simp,
      fun _ _ _ h => by simp at h⟩, by simp⟩
  set m := (f + 1) / 2
  set k := f / 2
  have hNcard : (Finset.univ.erase s).card = Fintype.card P - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  obtain ⟨v, V, hVN, hVcard, hsil⟩ := exists_class π hπ μ (bbInput s false) (Finset.univ.erase s) m
    (by omega)
  have hsV : s ∉ V := fun h => by simpa using hVN h
  have hVf : V.card ≤ f := by omega
  have hsilv : ∀ p ∈ V, μ {ω | π.silentOut p (bbInput s v p) ω = some v} ≤ 2⁻¹ := by
    intro p hp
    have hps : p ≠ s := fun h => hsV (h ▸ hp)
    simpa [bbInput, hps] using hsil p hp
  have hδ : ENNReal.ofReal (1 - (3 / 4 + ε)) = ENNReal.ofReal (1 / 4 - ε) := by ring_nf
  have hcore := π.core_bound hπ μ (bbInput s v) v V hVf k (by omega) (by omega)
    (δ := 1 / 4 - ε) (by linarith)
    (by
      refine (measure_mono ?_).trans ((hsolve (deafAdv V hVf) v).trans hδ.le)
      intro ω hω h
      apply hω
      intro u hu
      have hH := fun q => (π.deaf_honest_iff (bbInput s v) ω V hVf q)
      exact h.2 ((hH s).mpr hsV) u ((hH u).mpr hu))
    (fun A => (measure_mono (fun ω (hω : ω ∈ {ω | ¬ TermCons _ _}) h =>
      hω (BBGood.termCons h))).trans ((hsolve A v).trans hδ.le))
    hsilv
  refine ⟨v, deafAdv V hVf, le_trans ?_ hcore⟩
  rw [hVcard]
  exact final_arith f ε

/-- Theorem 4 with the paper's constant `(εf)²` (for `0 ≤ ε`, which is implied by the paper's
statement; our `ε f² / 2` is larger since `ε ≤ 1/4`). -/
theorem theorem_4_paper (π : Protocol P (Option Bool) M Ω) (hπ : π.IsMeasurable)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : P) {f : ℕ} (hfn : f < Fintype.card P) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hsolve : SolvesBB π μ s f (3 / 4 + ε)) :
    ∃ (b : Bool) (A : Adversary P f),
      ENNReal.ofReal ((ε * f) ^ 2) ≤ ∫⁻ ω, π.honestMsgs (bbInput s b) ω A ∂μ := by
  obtain ⟨b, A, h⟩ := theorem_4 π hπ μ s hfn hε hsolve
  refine ⟨b, A, le_trans (ENNReal.ofReal_le_ofReal ?_) h⟩
  have : (0 : ℝ) ≤ (f : ℝ) ^ 2 := by positivity
  nlinarith

/-- **Theorem 1** (Byzantine agreement): if `π` solves Byzantine agreement with probability
`3/4 + ε` against every strongly adaptive adversary corrupting at most `f < n` nodes, then for
some inputs and some adversary the honest nodes send at least `ε f² / 2` messages in
expectation. -/
theorem theorem_1 (π : Protocol P Bool M Ω) (hπ : π.IsMeasurable) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : ℕ} (hfn : f < Fintype.card P) {ε : ℝ} (hε : ε ≤ 1 / 4)
    (hsolve : SolvesBA π μ f (3 / 4 + ε)) :
    ∃ (inp : P → Bool) (A : Adversary P f),
      ENNReal.ofReal (ε * f ^ 2 / 2) ≤ ∫⁻ ω, π.honestMsgs inp ω A ∂μ := by
  classical
  rcases Nat.eq_zero_or_pos f with rfl | hf1
  · exact ⟨fun _ => false, ⟨fun _ => ∅, fun _ _ _ => false, fun _ _ => le_rfl, fun _ => by simp,
      fun _ _ _ h => by simp at h⟩, by simp⟩
  set m := (f + 1) / 2
  set k := f / 2
  obtain ⟨v, V, -, hVcard, hsil⟩ := exists_class π hπ μ (fun _ => false) Finset.univ m
    (by rw [Finset.card_univ]; omega)
  have hVf : V.card ≤ f := by omega
  set inp : P → Bool := fun q => if q ∈ V then false else v
  have hsilv : ∀ p ∈ V, μ {ω | π.silentOut p (inp p) ω = some v} ≤ 2⁻¹ := by
    intro p hp
    simpa [inp, hp] using hsil p hp
  have hδ : ENNReal.ofReal (1 - (3 / 4 + ε)) = ENNReal.ofReal (1 / 4 - ε) := by ring_nf
  have hcore := π.core_bound hπ μ inp v V hVf k (by omega) (by omega)
    (δ := 1 / 4 - ε) (by linarith)
    (by
      refine (measure_mono ?_).trans ((hsolve (deafAdv V hVf) inp).trans hδ.le)
      intro ω hω h
      apply hω
      intro u hu
      have hH := fun q => (π.deaf_honest_iff inp ω V hVf q)
      refine h.2 v (fun q hq => ?_) u ((hH u).mpr hu)
      simp [inp, (hH q).mp hq])
    (fun A => (measure_mono (fun ω (hω : ω ∈ {ω | ¬ TermCons _ _}) h =>
      hω (BAGood.termCons h))).trans ((hsolve A inp).trans hδ.le))
    hsilv
  refine ⟨inp, deafAdv V hVf, le_trans ?_ hcore⟩
  rw [hVcard]
  exact final_arith f ε

end CommComplexityBA
