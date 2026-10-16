import Papers.PODC2019.CommComplexityBA.Adversaries

/-!
# The core of the lower bound (proof of Theorem 4)

`Protocol.core_bound`: fix inputs `inp`, a value `v`, a set `V` of nodes and a threshold `k` with
`|V| - 1 + k ≤ f` and `|V| + k < n`. Suppose that
* under `deafAdv V` all nodes outside `V` output `v`, except with probability `δ`;
* every adversary breaks termination or consistency with probability at most `δ`;
* every `p ∈ V`, never receiving anything, outputs `v` with probability at most `1/2`.
Then under `deafAdv V` the expected number of messages sent by honest nodes is at least
`(1/2 - 2δ) · |V| · (k + 1)`.

The proof is the paper's, with one change: the paper conditions on the event "`p` receives at most
`f/2` messages under `A`" and claims that, conditionally on it, `p` still fails to output `v` with
probability `≥ 1/2`. This is unjustified (the event depends on `p`'s own randomness, which also
determines its silent output). We use a union bound instead, and replace the paper's
Markov-plus-averaging step by Markov's inequality for each `p ∈ V` separately; this gives
`2ε · |V| · (k + 1)` for `δ = 1/4 - ε`, which is *better* than the paper's `(εf)²`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory

namespace CommComplexityBA

variable {P I M Ω : Type*} [Fintype P] [DecidableEq P] {f : ℕ} [MeasurableSpace Ω] [Countable M]

namespace Protocol

variable (π : Protocol P I M Ω)

lemma fiberMeas_sentAt (hπ : π.IsMeasurable) (inp : P → I) (A : Adversary P f) (r : ℕ) (p q : P) :
    FiberMeas (fun ω => π.sentAt inp ω A r p q) :=
  (π.fiberMeas_runD inp hπ A.drop r).bind (F := fun ω s => (π.msg inp ω s.1 p q).isSome)
    fun s => (π.fiberMeas_msg inp hπ s.1 p q).map _

lemma measurable_cntTo (hπ : π.IsMeasurable) (inp : P → I) (V : Finset P) (hV : V.card ≤ f)
    (p : P) : Measurable (fun ω => π.cntTo inp ω V hV p) := by
  refine Measurable.ennreal_tsum fun r => ?_
  have h : FiberMeas (fun ω => π.cntRound inp ω V hV p r) :=
    (FiberMeas.pi fun s => π.fiberMeas_sentAt hπ inp (deafAdv V hV) r s p).map
      (fun g => (Finset.univ.filter fun s => s ∉ V ∧ g s = true).card)
  exact measurable_from_nat.comp h.measurable

/-- Messages into `V` are messages sent by honest nodes under `deafAdv V`. -/
lemma sum_cntTo_le (inp : P → I) (ω : Ω) (V : Finset P) (hV : V.card ≤ f) :
    ∑ p ∈ V, π.cntTo inp ω V hV p ≤ π.honestMsgs inp ω (deafAdv V hV) := by
  classical
  unfold cntTo honestMsgs
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine ENNReal.tsum_le_tsum fun r => ?_
  calc ∑ p ∈ V, (π.cntRound inp ω V hV p r : ENNReal)
      = ∑ p ∈ V, ∑ s, (if s ∉ V ∧ π.sentAt inp ω (deafAdv V hV) r s p = true then 1 else 0 :
          ENNReal) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [cntRound, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
          Nat.cast_zero]
    _ ≤ ∑ q, ∑ s, (if s ∉ V ∧ π.sentAt inp ω (deafAdv V hV) r s q = true then 1 else 0 :
          ENNReal) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ s, ∑ q, (if π.Honest inp ω (deafAdv V hV) s ∧
          π.sentAt inp ω (deafAdv V hV) r s q = true then 1 else 0 : ENNReal) := by
        rw [Finset.sum_comm]
        simp only [π.deaf_honest_iff]

/-- The per-node estimate: for `p ∈ V`, `(1/2 - 2δ) (k + 1)` is at most the expected number of
messages from `Vᶜ` to `p` under `deafAdv V`. -/
lemma node_bound (hπ : π.IsMeasurable) (μ : Measure Ω) [IsProbabilityMeasure μ] (inp : P → I)
    (v : Bool) (V : Finset P) (hVf : V.card ≤ f) (k : ℕ) (hk : V.card - 1 + k ≤ f)
    (hn : V.card + k < Fintype.card P) {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : μ {ω | ¬ ∀ u, u ∉ V → π.output inp ω (deafAdv V hVf) u = some v} ≤ ENNReal.ofReal δ)
    (hA' : ∀ A : Adversary P f,
      μ {ω | ¬ TermCons (π.output inp ω A) (π.Honest inp ω A)} ≤ ENNReal.ofReal δ)
    {p : P} (hp : p ∈ V) (hsil : μ {ω | π.silentOut p (inp p) ω = some v} ≤ 2⁻¹) :
    ENNReal.ofReal (1 / 2 - 2 * δ) * (k + 1) ≤ ∫⁻ ω, π.cntTo inp ω V hVf p ∂μ := by
  classical
  have hcardE : (V.erase p).card + k ≤ f := by rw [Finset.card_erase_of_mem hp]; exact hk
  set B : Adversary P f := (blockAdv V p k).mono hcardE with hB
  set C := {ω | ((k : ENNReal) + 1) ≤ π.cntTo inp ω V hVf p} with hC
  -- the key inclusion
  have hsub : {ω | π.silentOut p (inp p) ω ≠ some v} ⊆
      ({ω | ¬ ∀ u, u ∉ V → π.output inp ω (deafAdv V hVf) u = some v} ∪
        {ω | ¬ TermCons (π.output inp ω B) (π.Honest inp ω B)}) ∪ C := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, hC, not_le] at hcon
    obtain ⟨⟨hU, hTC⟩, hcnt⟩ := hcon
    have hrun : ∀ r, π.run inp ω (deafAdv V hVf) r = π.run inp ω B r :=
      π.deaf_run_eq_block_run inp ω V hVf hp k hcnt
    have hout : ∀ u, π.output inp ω (deafAdv V hVf) u = π.output inp ω B u := by
      intro u; simp only [output, hrun]
    have hpH : π.Honest inp ω B p := fun r => not_mem_blockAdv_corrupt V hp k _
    obtain ⟨u, hu, huH⟩ := π.exists_honest inp ω B (c := (V.erase p).card + k)
      (fun l => blockAdv_card_corrupt V p k l) (Finset.univ.erase p) (by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_erase_of_mem hp,
          Finset.card_univ]
        have : 0 < V.card := Finset.card_pos.mpr ⟨p, hp⟩
        omega)
    have hup : u ≠ p := Finset.ne_of_mem_erase hu
    have huV : u ∉ V := by
      intro huV
      exact huH 0 (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hup, huV⟩))
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hTC.1 p hpH)
    have hu_out : π.output inp ω B u = some v := (hout u) ▸ hU u huV
    have hyv : y = v := hTC.2 p u y v hpH huH hy hu_out
    apply hω
    rw [← π.deaf_output inp ω V hVf hp, hout, hy, hyv]
  -- probabilities
  have hne : (1 : ENNReal) ≤ 2⁻¹ + μ {ω | π.silentOut p (inp p) ω ≠ some v} := by
    calc (1 : ENNReal) = μ Set.univ := measure_univ.symm
      _ ≤ μ {ω | π.silentOut p (inp p) ω = some v} + μ {ω | π.silentOut p (inp p) ω ≠ some v} := by
          exact (measure_mono (fun ω _ => em (π.silentOut p (inp p) ω = some v))).trans
            (measure_union_le _ _)
      _ ≤ _ := add_le_add hsil le_rfl
  have hbad : μ {ω | π.silentOut p (inp p) ω ≠ some v} ≤
      ENNReal.ofReal δ + ENNReal.ofReal δ + μ C :=
    (measure_mono hsub).trans ((measure_union_le _ _).trans
      (add_le_add ((measure_union_le _ _).trans (add_le_add hA (hA' B))) le_rfl))
  have hmain : ENNReal.ofReal (1 / 2 - 2 * δ) ≤ μ C := by
    by_cases hX : μ C = ⊤
    · simp [hX]
    rw [ENNReal.ofReal_le_iff_le_toReal hX]
    have h := hne.trans (add_le_add le_rfl hbad)
    have hfin : (2⁻¹ : ENNReal) + (ENNReal.ofReal δ + ENNReal.ofReal δ + μ C) ≠ ⊤ := by
      simp [hX, ENNReal.add_eq_top]
    have := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_add (by simp) (by simp [hX, ENNReal.add_eq_top]),
      ENNReal.toReal_add (by simp [ENNReal.add_eq_top]) hX,
      ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_ofReal hδ] at this
    simp at this
    linarith
  -- Markov
  have hmarkov := mul_meas_ge_le_lintegral₀
    (μ := μ) (π.measurable_cntTo hπ inp V hVf p).aemeasurable ((k : ENNReal) + 1)
  calc ENNReal.ofReal (1 / 2 - 2 * δ) * (k + 1) ≤ μ C * (k + 1) := by gcongr
    _ = ((k : ENNReal) + 1) * μ C := mul_comm _ _
    _ ≤ _ := hmarkov

/-- **Core of Theorem 4.** -/
theorem core_bound (hπ : π.IsMeasurable) (μ : Measure Ω) [IsProbabilityMeasure μ] (inp : P → I)
    (v : Bool) (V : Finset P) (hVf : V.card ≤ f) (k : ℕ) (hk : V.card - 1 + k ≤ f)
    (hn : V.card + k < Fintype.card P) {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : μ {ω | ¬ ∀ u, u ∉ V → π.output inp ω (deafAdv V hVf) u = some v} ≤ ENNReal.ofReal δ)
    (hA' : ∀ A : Adversary P f,
      μ {ω | ¬ TermCons (π.output inp ω A) (π.Honest inp ω A)} ≤ ENNReal.ofReal δ)
    (hsil : ∀ p ∈ V, μ {ω | π.silentOut p (inp p) ω = some v} ≤ 2⁻¹) :
    ENNReal.ofReal ((1 / 2 - 2 * δ) * V.card * (k + 1)) ≤
      ∫⁻ ω, π.honestMsgs inp ω (deafAdv V hVf) ∂μ := by
  by_cases hη : 0 ≤ 1 / 2 - 2 * δ
  · calc ENNReal.ofReal ((1 / 2 - 2 * δ) * V.card * (k + 1))
        = ∑ _p ∈ V, ENNReal.ofReal (1 / 2 - 2 * δ) * (k + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul hη]
          simp only [ENNReal.ofReal_natCast]
          rw [ENNReal.ofReal_add (by positivity) zero_le_one]
          simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_one]
          ring
      _ ≤ ∑ p ∈ V, ∫⁻ ω, π.cntTo inp ω V hVf p ∂μ :=
          Finset.sum_le_sum fun p hp =>
            π.node_bound hπ μ inp v V hVf k hk hn hδ hA hA' hp (hsil p hp)
      _ = ∫⁻ ω, ∑ p ∈ V, π.cntTo inp ω V hVf p ∂μ :=
          (lintegral_finsetSum _ fun p _ => π.measurable_cntTo hπ inp V hVf p).symm
      _ ≤ _ := lintegral_mono fun ω => π.sum_cntTo_le inp ω V hVf
  · rw [ENNReal.ofReal_of_nonpos]
    · exact bot_le
    · have : (0 : ℝ) ≤ V.card * (k + 1) := by positivity
      nlinarith

end Protocol

end CommComplexityBA
