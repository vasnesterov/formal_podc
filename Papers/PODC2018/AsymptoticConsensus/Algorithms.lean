import Papers.PODC2018.AsymptoticConsensus.LowerBounds

/-!
# Upper bounds: Algorithms 1 and 2 of FNS'18 (tightness of Theorems 1 and 2)

Függer, Nowak, Schwarz. *Tight Bounds for Asymptotic and Approximate Consensus.* PODC 2018.

* `Averaging f N r`: a memoryless algorithm (state = current value) whose new values lie in the
  convex hull of the old ones and whose spread contracts by a factor `r < 1` in every round of
  `N`. Such an algorithm solves asymptotic consensus in `N` (`Averaging.solves`) with
  contraction rate at most `r` (`Averaging.rate_le`).
* **Algorithm 1** (`alg1`, two agents): `y_i ← y_i/3 + 2 y_j/3` if `j`'s value was received.
  It solves asymptotic consensus in the model `rooted2` of all rooted graphs on two agents with
  rate `≤ 1/3` (`alg1_solves`, `alg1_rate_le`); with Theorem 1 the rate is exactly `1/3`
  (`alg1_rate_eq`, `alg1_rate_eq_N3`).
* **Algorithm 2** (`midpoint`, `V = ℝ`): `y_i ← (min + max)/2` of the received values. It solves
  asymptotic consensus in the model of all non-split graphs with rate `≤ 1/2`
  (`midpoint_solves`, `midpoint_rate_le`); with Theorem 2 the rate is exactly `1/2` for `n ≥ 3`
  (`midpoint_rate_eq`).
-/

namespace AsymptoticConsensus

open Cslib.HeardOf Filter Topology Set
open scoped ENNReal

/-! ### Memoryless averaging algorithms -/

section Averaging

variable {α V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The memoryless algorithm with transition function `f`: the state is the current value. -/
def memoryless (f : StepFn α V) : Alg α V V := ⟨fun _ v => v, f, id⟩

/-- `f` is an averaging algorithm in `N` with contraction factor `r < 1`: every new value lies in
the convex hull of the old values, and the diameter of the values shrinks by the factor `r`. -/
structure Averaging (f : StepFn α V) (N : Set (Graph α)) (r : ℝ≥0∞) : Prop where
  mem_hull : ∀ G ∈ N, ∀ (C : α → V) i, next f G C i ∈ convexHull ℝ (range C)
  ediam_le : ∀ G ∈ N, ∀ C : α → V,
    Metric.ediam (range (next f G C)) ≤ r * Metric.ediam (range C)
  lt_one : r < 1

namespace Averaging

variable {f : StepFn α V} {N : Set (Graph α)} {r : ℝ≥0∞}

theorem hull_next_subset (h : Averaging f N r) {G : Graph α} (hG : G ∈ N) (C : α → V) :
    convexHull ℝ (range (next f G C)) ⊆ convexHull ℝ (range C) :=
  convexHull_min (range_subset_iff.2 (h.mem_hull G hG C)) (convex_convexHull ℝ _)

theorem hull_conf_antitone (h : Averaging f N r) {p : ℕ → Graph α} (hp : p ∈ Pat N)
    (C : α → V) : Antitone fun t => convexHull ℝ (range (conf f C p t)) :=
  antitone_nat_of_succ_le fun t => h.hull_next_subset (hp t) _

theorem ediam_conf_le (h : Averaging f N r) {p : ℕ → Graph α} (hp : p ∈ Pat N) (C : α → V)
    (t : ℕ) : Metric.ediam (range (conf f C p t)) ≤ Metric.ediam (range C) * r ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    calc Metric.ediam (range (conf f C p (t + 1)))
        ≤ r * Metric.ediam (range (conf f C p t)) := h.ediam_le _ (hp t) _
      _ ≤ r * (Metric.ediam (range C) * r ^ t) := by gcongr
      _ = Metric.ediam (range C) * r ^ (t + 1) := by ring

/-- In every run, all values converge to a common limit lying in the convex hull of the values
at every time. -/
theorem exists_limit [Finite α] [Nonempty α] (h : Averaging f N r) {p : ℕ → Graph α}
    (hp : p ∈ Pat N) (C : α → V) :
    ∃ z, (∀ t, z ∈ convexHull ℝ (range (conf f C p t))) ∧
      ∀ i, Tendsto (fun t => conf f C p t i) atTop (𝓝 z) := by
  set D := Metric.ediam (range C)
  have hD : D ≠ ∞ := (finite_range C).isBounded.ediam_ne_top
  have hmem : ∀ t i, conf f C p t i ∈ convexHull ℝ (range (conf f C p t)) :=
    fun t i => subset_convexHull ℝ _ ⟨i, rfl⟩
  have hdist : ∀ t, ∀ y ∈ convexHull ℝ (range (conf f C p t)),
      ∀ y' ∈ convexHull ℝ (range (conf f C p t)), edist y y' ≤ D * r ^ t := by
    intro t y hy y' hy'
    calc edist y y' ≤ Metric.ediam (convexHull ℝ (range (conf f C p t))) :=
          Metric.edist_le_ediam_of_mem hy hy'
      _ = Metric.ediam (range (conf f C p t)) := convexHull_ediam _
      _ ≤ D * r ^ t := h.ediam_conf_le hp C t
  have hanti := h.hull_conf_antitone hp C
  obtain i₀ : α := Classical.arbitrary α
  set u : ℕ → V := fun t => conf f C p t i₀
  have hcau : CauchySeq u := cauchySeq_of_edist_le_geometric r D h.lt_one hD fun t =>
    hdist t _ (hmem t i₀) _ (hanti (Nat.le_succ t) (hmem (t + 1) i₀))
  have hK : IsCompact (convexHull ℝ (range C)) := (finite_range C).isCompact_convexHull ℝ
  obtain ⟨z, -, hz⟩ := cauchySeq_tendsto_of_isComplete hK.isComplete
    (fun t => hanti (Nat.zero_le t) (hmem t i₀)) hcau
  have hzt : ∀ t, z ∈ convexHull ℝ (range (conf f C p t)) := fun t =>
    ((finite_range _).isClosed_convexHull ℝ).mem_of_tendsto hz
      (eventually_atTop.2 ⟨t, fun s hs => hanti hs (hmem s i₀)⟩)
  refine ⟨z, hzt, fun i => ?_⟩
  rw [tendsto_iff_edist_tendsto_0]
  have h0 : Tendsto (fun t : ℕ => D * r ^ t) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h.lt_one)
      (Or.inr hD)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le)
    fun t => hdist t _ (hmem t i) _ (hzt t)

/-- An averaging algorithm solves asymptotic consensus. -/
theorem solves [Finite α] [Nonempty α] (h : Averaging f N r) : (memoryless f).Solves N := by
  intro x p hp
  obtain ⟨z, hz, hlim⟩ := h.exists_limit hp x
  exact ⟨z, hz 0, hlim⟩

/-- The valency of any configuration lies in the convex hull of its values. -/
theorem val_subset [Finite α] [Nonempty α] (h : Averaging f N r) (C : α → V) :
    (memoryless f).val (Pat N) C ⊆ convexHull ℝ (range C) := by
  rintro z ⟨q, hq, hzq⟩
  obtain ⟨z', hz', hlim⟩ := h.exists_limit hq C
  have : z = z' := Alg.HasLimit.unique hzq hlim
  subst this
  exact hz' 0

/-- `δ_N(C) ≤ Δ(y(C))`. -/
theorem δ_le [Finite α] [Nonempty α] (h : Averaging f N r) (C : α → V) :
    (memoryless f).δ N C ≤ Metric.ediam (range C) :=
  (Metric.ediam_mono (h.val_subset C)).trans (convexHull_ediam _).le

/-- The contraction rate of an averaging algorithm is at most its contraction factor. -/
theorem rate_le [Finite α] [Nonempty α] (h : Averaging f N r) : (memoryless f).rate N ≤ r := by
  refine iSup_le fun x => iSup₂_le fun p hp => ?_
  exact Cslib.HeardOf.Chain.limsup_rpow_inv_le (finite_range x).isBounded.ediam_ne_top fun t =>
    (h.δ_le _).trans (h.ediam_conf_le hp x t)

end Averaging

end Averaging

/-! ### Algorithm 1: two agents -/

section Alg1

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Algorithm 1 of FNS'18** (two agents): if agent `i` receives the value `y_j` of the other
agent `j = 1 - i`, it sets `y_i ← y_i/3 + 2 y_j/3`; otherwise it keeps `y_i`. -/
noncomputable def alg1Step : StepFn (Fin 2) V := fun i m =>
  (m (1 - i)).elim ((m i).getD 0) fun b => (3 : ℝ)⁻¹ • (m i).getD 0 + (2 / 3 : ℝ) • b

/-- Algorithm 1 as an `Alg` (state = current value). -/
noncomputable def alg1 : Alg (Fin 2) V V := memoryless alg1Step

/-- The network model of all rooted graphs on two agents: at least one message is delivered.
It contains `H₀, H₁, H₂`. -/
def rooted2 : Set (Graph (Fin 2)) := {G | G 0 1 ∨ G 1 0}

theorem N3_subset_rooted2 : ({H0, H1, H2} : Set (Graph (Fin 2))) ⊆ rooted2 := by
  intro G hG
  simp only [mem_insert_iff, mem_singleton_iff] at hG
  rcases hG with rfl | rfl | rfl <;> simp [rooted2, H0, H1, H2]

open Classical in
theorem next_alg1 (G : Graph (Fin 2)) (C : Fin 2 → V) (i : Fin 2) :
    next alg1Step G C i =
      if G (1 - i) i then (3 : ℝ)⁻¹ • C i + (2 / 3 : ℝ) • C (1 - i) else C i := by
  by_cases h : G (1 - i) i <;> fin_cases i <;> simp_all [next, alg1Step, msgs, Hears]

open Classical in
theorem next_alg1_zero (G : Graph (Fin 2)) (C : Fin 2 → V) :
    next alg1Step G C 0 = if G 1 0 then (3 : ℝ)⁻¹ • C 0 + (2 / 3 : ℝ) • C 1 else C 0 := by
  by_cases h : G 1 0 <;> simp_all [next, alg1Step, msgs, Hears]

open Classical in
theorem next_alg1_one (G : Graph (Fin 2)) (C : Fin 2 → V) :
    next alg1Step G C 1 = if G 0 1 then (3 : ℝ)⁻¹ • C 1 + (2 / 3 : ℝ) • C 0 else C 1 := by
  by_cases h : G 0 1 <;> simp_all [next, alg1Step, msgs, Hears]

theorem range_fin_two {X : Type*} (C : Fin 2 → X) : range C = {C 0, C 1} := by
  ext y; simp [Fin.exists_fin_two, eq_comm]

theorem edist_eq_of_sub_eq {x y a b : V} (c : ℝ) (hc : |c| = 3⁻¹) (h : x - y = c • (a - b)) :
    edist x y = 3⁻¹ * edist a b := by
  rw [edist_eq_enorm_sub, h, enorm_smul, ← edist_eq_enorm_sub, Real.enorm_eq_ofReal_abs, hc,
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

/-- Algorithm 1 is an averaging algorithm with contraction factor `1/3` in every rooted graph. -/
theorem averaging_alg1 : Averaging (alg1Step (V := V)) rooted2 3⁻¹ where
  mem_hull G _ C i := by
    rw [next_alg1]
    have hi : C i ∈ convexHull ℝ (range C) := subset_convexHull ℝ _ ⟨i, rfl⟩
    split_ifs
    · exact convex_convexHull ℝ _ hi (subset_convexHull ℝ _ ⟨1 - i, rfl⟩) (by norm_num)
        (by norm_num) (by norm_num)
    · exact hi
  ediam_le G hG C := by
    rw [range_fin_two, range_fin_two, Metric.ediam_pair, Metric.ediam_pair, next_alg1_zero,
      next_alg1_one]
    by_cases h10 : G 1 0 <;> by_cases h01 : G 0 1 <;> simp only [h10, h01, ite_true, ite_false]
    · exact (edist_eq_of_sub_eq (-3⁻¹) (by norm_num) (by module)).le
    · exact (edist_eq_of_sub_eq 3⁻¹ (by norm_num) (by module)).le
    · exact (edist_eq_of_sub_eq 3⁻¹ (by norm_num) (by module)).le
    · exact absurd hG (by simp [rooted2, h10, h01])
  lt_one := by norm_num

/-- **Algorithm 1 of FNS'18** solves asymptotic consensus in the model of all rooted graphs on two
agents (in particular in `{H₀, H₁, H₂}`). -/
theorem alg1_solves : (alg1 (V := V)).Solves rooted2 := averaging_alg1.solves

/-- The contraction rate of Algorithm 1 in the rooted model is at most `1/3`. -/
theorem alg1_rate_le : (alg1 (V := V)).rate rooted2 ≤ 3⁻¹ := averaging_alg1.rate_le

/-- **Tightness of Theorem 1 of FNS'18**: Algorithm 1 has contraction rate exactly `1/3` in the
model of all rooted graphs on two agents. -/
theorem alg1_rate_eq [Nontrivial V] : (alg1 (V := V)).rate rooted2 = 3⁻¹ :=
  le_antisymm alg1_rate_le (theorem1 alg1 N3_subset_rooted2 alg1_solves)

/-- **Tightness of Theorem 1 of FNS'18**: Algorithm 1 solves asymptotic consensus in
`{H₀, H₁, H₂}` with contraction rate exactly `1/3`. -/
theorem alg1_rate_eq_N3 [Nontrivial V] :
    (alg1 (V := V)).Solves {H0, H1, H2} ∧ (alg1 (V := V)).rate {H0, H1, H2} = 3⁻¹ :=
  ⟨alg1_solves.mono N3_subset_rooted2,
    le_antisymm ((Alg.rate_mono N3_subset_rooted2).trans alg1_rate_le)
      (theorem1 alg1 subset_rfl (alg1_solves.mono N3_subset_rooted2))⟩

end Alg1

/-! ### Algorithm 2: the midpoint algorithm -/

section Midpoint

variable {α : Type*} [Fintype α]

/-- The set of received values. -/
noncomputable def received (m : α → Option ℝ) : Finset ℝ :=
  Finset.univ.biUnion fun j => (m j).toFinset

/-- **Algorithm 2 of FNS'18** (midpoint algorithm): every agent sets
`y_i ← (min_{j heard} y_j + max_{j heard} y_j) / 2`. -/
noncomputable def midStep : StepFn α ℝ := fun _ m =>
  if h : (received m).Nonempty then ((received m).min' h + (received m).max' h) / 2 else 0

/-- The midpoint algorithm as an `Alg` (state = current value). -/
noncomputable def midpoint : Alg α ℝ ℝ := memoryless midStep

theorem mem_received_msgs {G : Graph α} {C : α → ℝ} {i : α} {v : ℝ} :
    v ∈ received (msgs G C i) ↔ ∃ j, Hears G i j ∧ C j = v := by
  classical
  simp [received, msgs]

theorem received_msgs_nonempty (G : Graph α) (C : α → ℝ) (i : α) :
    (received (msgs G C i)).Nonempty :=
  ⟨C i, mem_received_msgs.2 ⟨i, hears_self G i, rfl⟩⟩

/-- The new value of `i` is the midpoint of the least and the largest value it heard. -/
theorem next_midStep (G : Graph α) (C : α → ℝ) (i : α) :
    ∃ lo hi, next midStep G C i = (lo + hi) / 2 ∧ (∃ j, Hears G i j ∧ C j = lo) ∧
      (∃ j, Hears G i j ∧ C j = hi) ∧ ∀ k, Hears G i k → lo ≤ C k ∧ C k ≤ hi := by
  have hne := received_msgs_nonempty G C i
  refine ⟨_, _, ?_, mem_received_msgs.1 (Finset.min'_mem _ hne),
    mem_received_msgs.1 (Finset.max'_mem _ hne), fun k hk => ⟨Finset.min'_le _ _ ?_,
      Finset.le_max' _ _ ?_⟩⟩
  · simp [next, midStep, hne]
  all_goals exact mem_received_msgs.2 ⟨k, hk, rfl⟩

/-- The midpoint algorithm is an averaging algorithm with contraction factor `1/2` in every
non-split graph. -/
theorem averaging_midStep [Nonempty α] : Averaging (midStep (α := α)) {G | NonSplit G} 2⁻¹ where
  mem_hull G _ C i := by
    obtain ⟨lo, hi, he, ⟨j, -, rfl⟩, ⟨j', -, rfl⟩, -⟩ := next_midStep G C i
    rw [he]
    have := convex_convexHull ℝ (range C) (subset_convexHull ℝ _ ⟨j, rfl⟩)
      (subset_convexHull ℝ _ ⟨j', rfl⟩) (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num)
    convert this using 1
    simp only [smul_eq_mul]; ring
  ediam_le G hG C := by
    obtain ⟨a, ha⟩ := Finite.exists_min C
    obtain ⟨b, hb⟩ := Finite.exists_max C
    refine Metric.ediam_le ?_
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := hG i j
    obtain ⟨lo, hi, he, ⟨l1, -, rfl⟩, ⟨l2, -, rfl⟩, hlh⟩ := next_midStep G C i
    obtain ⟨lo', hi', he', ⟨l1', -, rfl⟩, ⟨l2', -, rfl⟩, hlh'⟩ := next_midStep G C j
    have h1 := hlh k hik; have h2 := hlh' k hjk
    have := ha l1; have := ha l1'; have := hb l2; have := hb l2'
    calc edist (next midStep G C i) (next midStep G C j)
        = ENNReal.ofReal |next midStep G C i - next midStep G C j| := by
          rw [edist_dist, Real.dist_eq]
      _ ≤ ENNReal.ofReal ((C b - C a) / 2) := by
          refine ENNReal.ofReal_le_ofReal (abs_le.2 ⟨?_, ?_⟩) <;> rw [he, he'] <;> linarith
      _ = 2⁻¹ * ENNReal.ofReal (C b - C a) := by
          rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_inv_of_pos (by norm_num)]
          simp
      _ = 2⁻¹ * edist (C b) (C a) := by
          rw [edist_dist, Real.dist_eq, abs_of_nonneg (by linarith [ha b])]
      _ ≤ 2⁻¹ * Metric.ediam (range C) := by
          gcongr; exact Metric.edist_le_ediam_of_mem ⟨b, rfl⟩ ⟨a, rfl⟩
  lt_one := by norm_num

/-- **Algorithm 2 of FNS'18** (midpoint) solves asymptotic consensus in the model of all
non-split graphs. -/
theorem midpoint_solves [Nonempty α] : (midpoint (α := α)).Solves {G | NonSplit G} :=
  averaging_midStep.solves

/-- The contraction rate of the midpoint algorithm in the non-split model is at most `1/2`. -/
theorem midpoint_rate_le [Nonempty α] : (midpoint (α := α)).rate {G | NonSplit G} ≤ 2⁻¹ :=
  averaging_midStep.rate_le

/-- **Tightness of Theorem 2 of FNS'18**: for `n ≥ 3` agents the midpoint algorithm has
contraction rate exactly `1/2` in the model of all non-split graphs. -/
theorem midpoint_rate_eq (hn : 3 ≤ Fintype.card α) :
    (midpoint (α := α)).rate {G | NonSplit G} = 2⁻¹ := by
  have : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  exact le_antisymm midpoint_rate_le (theorem2_nonsplit hn midpoint midpoint_solves)

end Midpoint

end AsymptoticConsensus
