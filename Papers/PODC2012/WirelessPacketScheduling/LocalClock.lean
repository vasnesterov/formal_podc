import Mathlib

/-!
# Executions of links with local clocks (Section 8, Theorem 20)

The network of Figure 1: `K = m - 1` short links and one long link. A transmission on a short link
always succeeds; a transmission on the long link succeeds only if no short link transmits in the
same slot. Packets arrive at every link with probability `λ` per slot.

**Model.** An acknowledgement-based protocol with only a local clock gets no information from
the rest of the network on a short link (its transmissions always succeed), so the execution of
short link `i` is a random process of its own randomness (arrivals and coins) in its *local*
time, independent of the other links. The local clocks are not synchronised: link `i` is
switched on at global time `d i` (chosen by the adversary), so its global behaviour is its local
execution shifted by `d i` (it is silent before). We therefore model

* each short link by a `LinkExec` on its own probability space `(Ω i, μ i)`
  (transmission indicator `tx`, arrivals `arr ≤ 1`, deliveries `dlv ≤ tx`, queue `q` with
  `q 0 = 0`, `q (τ+1) + dlv τ = q τ + arr τ`),
* the joint randomness of the short links by the product measure `Measure.pi μ`,
* the long link by an arbitrary `LinkExec` on any probability space `G` carrying a
  measure-preserving map `π` to the short links' randomness; its *successful* transmissions
  (`tx`) can only happen in slots in which no short link transmits. This allows arbitrary
  dependence of the long link on everything (it is stronger than the paper needs).

Stability = bounded expected queue length (the notion of Section 4.1); arrival rate `λ` = expected
arrivals `λ` per slot.

Main result (`no_stable_local_protocol`): if `(1 - λ)^K < λ`, then for every family of stable
short-link executions there are switch-on times `d` such that no long-link execution is stable.
-/

namespace Podc.WirelessPacketScheduling.LocalClock

open MeasureTheory Finset

-- CSLib candidate
/-- An execution of one link, in its local time: `tx τ` = a (successful) transmission in slot `τ`,
`arr τ ≤ 1` arrivals, `dlv τ ≤ tx τ` deliveries, `q τ` queue length. -/
structure LinkExec (Ω : Type*) [MeasurableSpace Ω] where
  tx : ℕ → Ω → Bool
  arr : ℕ → Ω → ℕ
  dlv : ℕ → Ω → ℕ
  q : ℕ → Ω → ℕ
  q_zero : ∀ ω, q 0 ω = 0
  q_succ : ∀ τ ω, q (τ + 1) ω + dlv τ ω = q τ ω + arr τ ω
  arr_le : ∀ τ ω, arr τ ω ≤ 1
  dlv_le : ∀ τ ω, dlv τ ω ≤ (tx τ ω).toNat
  meas_tx : ∀ τ, Measurable (tx τ)
  meas_arr : ∀ τ, Measurable (arr τ)
  meas_dlv : ∀ τ, Measurable (dlv τ)

namespace LinkExec

variable {Ω : Type*} [MeasurableSpace Ω] (L : LinkExec Ω)

/-- Arrival rate `λ`: one packet arrives in slot `τ` with probability `λ`. -/
def Rate (μ : Measure Ω) (lam : ℝ) : Prop := ∀ τ, ∫ ω, (L.arr τ ω : ℝ) ∂μ = lam

/-- Stability: the expected queue length is bounded. -/
def Stable (μ : Measure Ω) : Prop := ∃ B : ℝ, ∀ τ, ∫ ω, (L.q τ ω : ℝ) ∂μ ≤ B

lemma q_le (τ : ℕ) (ω : Ω) : L.q τ ω ≤ τ := by
  induction τ with
  | zero => simp [L.q_zero]
  | succ τ ih => have := L.q_succ τ ω; have := L.arr_le τ ω; omega

lemma dlv_le_one (τ : ℕ) (ω : Ω) : L.dlv τ ω ≤ 1 :=
  (L.dlv_le τ ω).trans (by cases L.tx τ ω <;> simp)

lemma meas_q (τ : ℕ) : Measurable (L.q τ) := by
  induction τ with
  | zero =>
    have : L.q 0 = fun _ => 0 := funext L.q_zero
    rw [this]; exact measurable_const
  | succ τ ih =>
    have h : L.q (τ + 1) = fun ω => L.q τ ω + L.arr τ ω - L.dlv τ ω := by
      funext ω; have := L.q_succ τ ω; omega
    rw [h]
    exact (ih.add (L.meas_arr τ)).sub (L.meas_dlv τ)

/-- Conservation over a window: `q(τ₀+k) + ∑ dlv = q τ₀ + ∑ arr`. -/
lemma window_cons (τ₀ k : ℕ) (ω : Ω) :
    (L.q (τ₀ + k) ω : ℝ) + ∑ τ ∈ Ico τ₀ (τ₀ + k), (L.dlv τ ω : ℝ) =
      L.q τ₀ ω + ∑ τ ∈ Ico τ₀ (τ₀ + k), (L.arr τ ω : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show τ₀ + (k + 1) = τ₀ + k + 1 by ring, sum_Ico_succ_top (by omega),
      sum_Ico_succ_top (by omega)]
    have := L.q_succ (τ₀ + k) ω
    have h : (L.q (τ₀ + k + 1) ω : ℝ) + L.dlv (τ₀ + k) ω = L.q (τ₀ + k) ω + L.arr (τ₀ + k) ω := by
      exact_mod_cast this
    linarith

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma integrable_nat {f : Ω → ℕ} (hf : Measurable f) {c : ℕ} (hc : ∀ ω, f ω ≤ c) :
    Integrable (fun ω => (f ω : ℝ)) μ := by
  refine Integrable.of_bound (C := c) (((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp hf).aestronglyMeasurable) (Filter.Eventually.of_forall
    fun ω => ?_)
  simp only [Real.norm_natCast]; exact_mod_cast hc ω

omit [IsProbabilityMeasure μ] in
lemma integral_tx (τ : ℕ) :
    ∫ ω, ((L.tx τ ω).toNat : ℝ) ∂μ = μ.real {ω | L.tx τ ω = true} := by
  have hs : MeasurableSet {ω | L.tx τ ω = true} :=
    (L.meas_tx τ) (measurableSet_singleton true)
  rw [← integral_indicator_one hs]
  congr 1; funext ω
  by_cases h : L.tx τ ω = true <;> simp [h, Set.indicator]

/-- Expected deliveries are at most the transmission probability. -/
lemma integral_dlv_le (τ : ℕ) : ∫ ω, (L.dlv τ ω : ℝ) ∂μ ≤ μ.real {ω | L.tx τ ω = true} := by
  rw [← L.integral_tx μ τ]
  refine integral_mono (integrable_nat μ (L.meas_dlv τ) (L.dlv_le_one τ))
    (integrable_nat μ (f := fun ω => (L.tx τ ω).toNat)
      ((measurable_from_top (f := Bool.toNat)).comp (L.meas_tx τ))
      (c := 1) (fun ω => by cases L.tx τ ω <;> simp)) fun ω => ?_
  exact Nat.cast_le.mpr (L.dlv_le τ ω)

lemma integrable_q (τ : ℕ) : Integrable (fun ω => (L.q τ ω : ℝ)) μ :=
  integrable_nat μ (L.meas_q τ) (L.q_le τ)

lemma integrable_arr (τ : ℕ) : Integrable (fun ω => (L.arr τ ω : ℝ)) μ :=
  integrable_nat μ (L.meas_arr τ) (L.arr_le τ)

lemma integrable_dlv (τ : ℕ) : Integrable (fun ω => (L.dlv τ ω : ℝ)) μ :=
  integrable_nat μ (L.meas_dlv τ) (L.dlv_le_one τ)

/-- Expected conservation over a window: `E q(τ₀) + λ k ≤ E q(τ₀+k) + ∑ P(tx τ)`. -/
lemma cons_ge (lam : ℝ) (hR : L.Rate μ lam) (τ₀ k : ℕ) :
    ∫ ω, (L.q τ₀ ω : ℝ) ∂μ + lam * k ≤
      ∫ ω, (L.q (τ₀ + k) ω : ℝ) ∂μ + ∑ τ ∈ Ico τ₀ (τ₀ + k), μ.real {ω | L.tx τ ω = true} := by
  have hcons := integral_congr_ae (μ := μ) (Filter.Eventually.of_forall (L.window_cons τ₀ k))
  rw [integral_add (L.integrable_q μ _) (integrable_finsetSum _ fun τ _ => L.integrable_dlv μ τ),
    integral_add (L.integrable_q μ _) (integrable_finsetSum _ fun τ _ => L.integrable_arr μ τ),
    integral_finsetSum _ fun τ _ => L.integrable_dlv μ τ,
    integral_finsetSum _ fun τ _ => L.integrable_arr μ τ] at hcons
  have hS : ∑ τ ∈ Ico τ₀ (τ₀ + k), ∫ ω, (L.arr τ ω : ℝ) ∂μ = lam * k := by
    rw [Finset.sum_congr rfl (fun τ _ => hR τ)]; simp [mul_comm]
  rw [hS] at hcons
  have h2 : ∑ τ ∈ Ico τ₀ (τ₀ + k), ∫ ω, (L.dlv τ ω : ℝ) ∂μ ≤
      ∑ τ ∈ Ico τ₀ (τ₀ + k), μ.real {ω | L.tx τ ω = true} :=
    sum_le_sum fun τ _ => L.integral_dlv_le μ τ
  linarith

/-- **Stability forces throughput** (first step of the proof of Theorem 20): if the arrival rate
is `λ` and the expected queue length is at most `B`, then every window of `k` slots contains at
least `λ k - B` expected transmissions. -/
lemma window_tx (lam B : ℝ) (hR : L.Rate μ lam) (hB : ∀ τ, ∫ ω, (L.q τ ω : ℝ) ∂μ ≤ B)
    (τ₀ k : ℕ) : lam * k - B ≤ ∑ τ ∈ Ico τ₀ (τ₀ + k), μ.real {ω | L.tx τ ω = true} := by
  have h0 : 0 ≤ ∫ ω, (L.q τ₀ ω : ℝ) ∂μ := integral_nonneg fun ω => Nat.cast_nonneg _
  have := L.cons_ge μ lam hR τ₀ k
  have := hB (τ₀ + k)
  linarith

end LinkExec

/-! ### The network of Figure 1 -/

section Global

variable {K : ℕ} {Ω : Fin K → Type*} [∀ i, MeasurableSpace (Ω i)]
  (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] (S : ∀ i, LinkExec (Ω i))

/-- Short link `i`, switched on at global time `n`, transmits in global slot `t`. -/
def ShortTx (i : Fin K) (n t : ℕ) (x : Ω i) : Prop := n ≤ t ∧ (S i).tx (t - n) x = true

/-- All short links are silent in global slot `t` (switch-on times `d`). -/
def Silent (d : Fin K → ℕ) (t : ℕ) (ω : ∀ i, Ω i) : Prop := ∀ i, ¬ ShortTx S i (d i) t (ω i)

lemma measurableSet_shortTx (i : Fin K) (n t : ℕ) :
    MeasurableSet {x : Ω i | ¬ ShortTx S i n t x} := by
  have : MeasurableSet {x : Ω i | (S i).tx (t - n) x = false} :=
    ((S i).meas_tx (t - n)) (measurableSet_singleton false)
  by_cases h : n ≤ t
  · simpa [ShortTx, h] using this
  · simp [ShortTx, h]

lemma silent_eq_pi (d : Fin K → ℕ) (t : ℕ) :
    {ω | Silent S d t ω} = Set.univ.pi (fun i => {x : Ω i | ¬ ShortTx S i (d i) t x}) := by
  ext ω; simp [Silent]

lemma measurableSet_silent (d : Fin K → ℕ) (t : ℕ) : MeasurableSet {ω | Silent S d t ω} := by
  rw [silent_eq_pi]
  exact MeasurableSet.univ_pi fun i => measurableSet_shortTx S i (d i) t

/-- Probability that short link `i`, switched on at time `n`, is silent in slot `t`. -/
noncomputable def silentProb (i : Fin K) (n t : ℕ) : ℝ := (μ i).real {x | ¬ ShortTx S i n t x}

/-- By independence of the short links, `P(all silent) = ∏ P(link i silent)`. -/
lemma measureReal_silent (d : Fin K → ℕ) (t : ℕ) :
    (Measure.pi μ).real {ω | Silent S d t ω} = ∏ i, silentProb μ S i (d i) t := by
  rw [silent_eq_pi, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  rfl

omit [∀ i, IsProbabilityMeasure (μ i)] in
lemma silentProb_nonneg (i : Fin K) (n t : ℕ) : 0 ≤ silentProb μ S i n t := measureReal_nonneg

lemma silentProb_le_one (i : Fin K) (n t : ℕ) : silentProb μ S i n t ≤ 1 := measureReal_le_one

lemma silentProb_of_le (i : Fin K) (n t : ℕ) (h : n ≤ t) :
    silentProb μ S i n t = 1 - (μ i).real {x | (S i).tx (t - n) x = true} := by
  have hm : MeasurableSet {x : Ω i | (S i).tx (t - n) x = true} :=
    ((S i).meas_tx (t - n)) (measurableSet_singleton true)
  rw [silentProb, ← probReal_compl_eq_one_sub hm]
  congr 1; ext x; simp [ShortTx, h]

/-- A long link (any protocol): a `LinkExec` on any probability space `G` carrying the short
links' randomness through a measure-preserving map `π`, with successful transmissions only in
slots where all short links are silent. -/
structure LongLink (d : Fin K → ℕ) (G : Type*) [MeasurableSpace G] (ν : Measure G) where
  π : G → ∀ i, Ω i
  mp : MeasurePreserving π ν (Measure.pi μ)
  L : LinkExec G
  tx_silent : ∀ t g, L.tx t g = true → Silent S d t (π g)

variable {μ S}

omit [∀ i, IsProbabilityMeasure (μ i)] in
lemma LongLink.tx_le {d : Fin K → ℕ} {G : Type*} [MeasurableSpace G] {ν : Measure G}
    [IsFiniteMeasure ν] (LL : LongLink μ S d G ν) (t : ℕ) :
    ν.real {g | LL.L.tx t g = true} ≤ (Measure.pi μ).real {ω | Silent S d t ω} := by
  have h1 : {g | LL.L.tx t g = true} ⊆ LL.π ⁻¹' {ω | Silent S d t ω} :=
    fun g hg => LL.tx_silent t g hg
  have h2 : ν.real (LL.π ⁻¹' {ω | Silent S d t ω}) = (Measure.pi μ).real {ω | Silent S d t ω} := by
    rw [measureReal_def, measureReal_def, LL.mp.measure_preimage
      (measurableSet_silent S d t).nullMeasurableSet]
  rw [← h2]
  exact measureReal_mono h1

omit [∀ i, IsProbabilityMeasure (μ i)] in
/-- The expected queue of the long link grows by `λ` per slot minus the probability that all
short links are silent. -/
lemma LongLink.queue_ge {d : Fin K → ℕ} {G : Type*} [MeasurableSpace G] {ν : Measure G}
    [IsProbabilityMeasure ν] (LL : LongLink μ S d G ν) (lam : ℝ) (hR : LL.L.Rate ν lam) (T : ℕ) :
    lam * T - ∑ t ∈ range T, (Measure.pi μ).real {ω | Silent S d t ω} ≤
      ∫ g, (LL.L.q T g : ℝ) ∂ν := by
  have h := LL.L.cons_ge ν lam hR 0 T
  have hq0 : ∫ g, (LL.L.q 0 g : ℝ) ∂ν = 0 := by simp [LL.L.q_zero]
  simp only [zero_add] at h
  rw [hq0, zero_add, Nat.Ico_zero_eq_range] at h
  have : ∑ t ∈ range T, ν.real {g | LL.L.tx t g = true} ≤
      ∑ t ∈ range T, (Measure.pi μ).real {ω | Silent S d t ω} :=
    sum_le_sum fun t _ => LL.tx_le t
  linarith

variable (μ S)

/-- Averaged over the `k` switch-on times `δ < k`, a stable short link is silent in slot `t ≥ k-1`
with probability at most `1 - λ + B/k`. -/
lemma sum_silentProb_le (i : Fin K) (lam B : ℝ) (hR : (S i).Rate (μ i) lam)
    (hB : ∀ τ, ∫ x, ((S i).q τ x : ℝ) ∂(μ i) ≤ B) (k t : ℕ) (hk : k ≤ t + 1) :
    ∑ δ ∈ range k, silentProb μ S i δ t ≤ k * (1 - lam) + B := by
  have hw := (S i).window_tx (μ i) lam B hR hB (t + 1 - k) k
  have hre : ∑ δ ∈ range k, (μ i).real {x | (S i).tx (t - δ) x = true} =
      ∑ τ ∈ Ico (t + 1 - k) (t + 1 - k + k), (μ i).real {x | (S i).tx τ x = true} := by
    rw [Finset.sum_Ico_eq_sum_range, show t + 1 - k + k - (t + 1 - k) = k by omega,
      ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [Finset.mem_range] at hδ
    rw [show t - (k - 1 - δ) = t + 1 - k + δ by omega]
  have hs : ∑ δ ∈ range k, silentProb μ S i δ t =
      ∑ δ ∈ range k, (1 - (μ i).real {x | (S i).tx (t - δ) x = true}) :=
    Finset.sum_congr rfl fun δ hδ => silentProb_of_le μ S i δ t (by
      rw [Finset.mem_range] at hδ; omega)
  rw [hs, Finset.sum_sub_distrib, hre]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  linarith

/-- Choice of the window length `k`: `(1 - λ + B/k)^K < λ` for `k` large. -/
lemma exists_window (K : ℕ) (lam B : ℝ) (hK : (1 - lam) ^ K < lam) :
    ∃ k : ℕ, 1 ≤ k ∧ (1 - lam + B / k) ^ K < lam := by
  have ht : Filter.Tendsto (fun k : ℕ => (1 - lam + B / k) ^ K) Filter.atTop
      (nhds ((1 - lam + 0) ^ K)) :=
    ((tendsto_const_div_atTop_nhds_zero_nat B).const_add (1 - lam)).pow K
  rw [add_zero] at ht
  obtain ⟨k, hk⟩ := ((ht.eventually (gt_mem_nhds hK)).and (Filter.eventually_ge_atTop 1)).exists
  exact ⟨k, hk.2, hk.1⟩

/-- **Theorem 20 (core).** In the network of Figure 1 with `K` short links, let every short link
run a stable execution with arrival rate `λ` (in its local time). If `(1 - λ)^K < λ`, there are
switch-on times `d` of the short links such that **no** execution of the long link with arrival
rate `λ` is stable, whatever its protocol (it may even know everything). -/
theorem no_stable_long_link (lam : ℝ) (hlam1 : lam ≤ 1)
    (hK : (1 - lam) ^ K < lam)
    (hR : ∀ i, (S i).Rate (μ i) lam) (hS : ∀ i, (S i).Stable (μ i)) :
    ∃ d : Fin K → ℕ, ∀ (G : Type) [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν]
      (LL : LongLink μ S d G ν), LL.L.Rate ν lam → ¬ LL.L.Stable ν := by
  choose Bi hBi using hS
  set B := ∑ i, |Bi i| with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hBB : ∀ i τ, ∫ x, ((S i).q τ x : ℝ) ∂(μ i) ≤ B := fun i τ =>
    (hBi i τ).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Bi i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
  obtain ⟨k, hk1, hρ⟩ := exists_window K lam B hK
  set ρ := (1 - lam + B / k) ^ K with hρdef
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  by_contra hcon
  push Not at hcon
  choose G _ ν _ LL hRate hStab using
    fun δ : Fin K → Fin k => hcon (fun i => (δ i : ℕ))
  choose C hC using hStab
  -- the bound per slot, summed over all switch-on times
  have hF : ∀ t : ℕ, ∑ δ : Fin K → Fin k,
      (Measure.pi μ).real {ω | Silent S (fun i => (δ i : ℕ)) t ω} ≤
        (k : ℝ) ^ K * ρ + (if t + 1 < k then (k : ℝ) ^ K else 0) := by
    intro t
    simp_rw [measureReal_silent]
    rw [← Fintype.prod_sum (f := fun i (δ : Fin k) => silentProb μ S i (δ : ℕ) t)]
    have hfs : ∀ i, ∑ δ : Fin k, silentProb μ S i (δ : ℕ) t = ∑ δ ∈ range k, silentProb μ S i δ t :=
      fun i => Fin.sum_univ_eq_sum_range (fun δ => silentProb μ S i δ t) k
    simp only [hfs]
    split_ifs with ht
    · have : ∏ i : Fin K, ∑ δ ∈ range k, silentProb μ S i δ t ≤ ∏ _i : Fin K, (k : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun δ _ =>
          silentProb_nonneg μ S i δ t) fun i _ => ?_
        calc ∑ δ ∈ range k, silentProb μ S i δ t ≤ ∑ _δ ∈ range k, (1 : ℝ) :=
              Finset.sum_le_sum fun δ _ => silentProb_le_one μ S i δ t
          _ = k := by simp
      have hρ0 : 0 ≤ (k : ℝ) ^ K * ρ := by
        have : 0 ≤ 1 - lam + B / k := by
          have := div_nonneg hB0 hkpos.le; linarith
        positivity
      simp only [prod_const, card_univ, Fintype.card_fin] at this
      linarith
    · have hle : ∏ i : Fin K, ∑ δ ∈ range k, silentProb μ S i δ t ≤
          ∏ _i : Fin K, ((k : ℝ) * (1 - lam + B / k)) := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun δ _ =>
          silentProb_nonneg μ S i δ t) fun i _ => ?_
        have := sum_silentProb_le μ S i lam B (hR i) (hBB i) k t (by omega)
        calc _ ≤ (k : ℝ) * (1 - lam) + B := this
          _ = (k : ℝ) * (1 - lam + B / k) := by field_simp
      simp only [prod_const, card_univ, Fintype.card_fin, mul_pow] at hle
      linarith
  -- summing over time
  have hsum : ∀ T : ℕ, ∑ δ : Fin K → Fin k, ∑ t ∈ range T,
      (Measure.pi μ).real {ω | Silent S (fun i => (δ i : ℕ)) t ω} ≤
        T * ((k : ℝ) ^ K * ρ) + k * (k : ℝ) ^ K := by
    intro T
    rw [Finset.sum_comm]
    calc _ ≤ ∑ t ∈ range T, ((k : ℝ) ^ K * ρ + (if t + 1 < k then (k : ℝ) ^ K else 0)) :=
          Finset.sum_le_sum fun t _ => hF t
      _ = T * ((k : ℝ) ^ K * ρ) + ∑ t ∈ range T, (if t + 1 < k then (k : ℝ) ^ K else 0) := by
          rw [Finset.sum_add_distrib]; simp
      _ ≤ T * ((k : ℝ) ^ K * ρ) + ∑ t ∈ range k, (k : ℝ) ^ K := by
          gcongr
          rw [← Finset.sum_filter]
          refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity)
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
          omega
      _ = _ := by simp
  -- the long links' queues
  have hq : ∀ T : ℕ, (k : ℝ) ^ K * lam * T - (T * ((k : ℝ) ^ K * ρ) + k * (k : ℝ) ^ K) ≤
      ∑ δ : Fin K → Fin k, C δ := by
    intro T
    have h1 : ∀ δ : Fin K → Fin k, lam * T - ∑ t ∈ range T,
        (Measure.pi μ).real {ω | Silent S (fun i => (δ i : ℕ)) t ω} ≤ C δ := fun δ =>
      ((LL δ).queue_ge lam (hRate δ) T).trans (hC δ T)
    have h2 := Finset.sum_le_sum fun δ (_ : δ ∈ Finset.univ) => h1 δ
    rw [Finset.sum_sub_distrib] at h2
    simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow] at h2
    have := hsum T
    nlinarith
  -- contradiction for large `T`
  have hkK : (0 : ℝ) < (k : ℝ) ^ K := by positivity
  obtain ⟨T, hT⟩ := exists_nat_gt
    ((∑ δ : Fin K → Fin k, C δ + k * (k : ℝ) ^ K) / ((k : ℝ) ^ K * (lam - ρ)))
  have hpos : 0 < (k : ℝ) ^ K * (lam - ρ) := mul_pos hkK (by linarith)
  rw [div_lt_iff₀ hpos] at hT
  have := hq T
  nlinarith

end Global


end Podc.WirelessPacketScheduling.LocalClock
