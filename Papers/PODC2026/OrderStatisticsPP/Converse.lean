import Papers.PODC2026.OrderStatisticsPP.CopyOrMax
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# Copy-or-Max: geometric fixation forces a connected circulation (Proposition 6 (⇒))

We prove the converse direction of Proposition 6 / Theorem 1(2): if the weighted Copy-or-Max
dynamics has the geometric fixation law from *every* configuration with pairwise distinct
opinions (values in a linear order with at least `n` elements), then the weights form a
circulation and the support graph is connected.

The paper's proof of this direction is not valid (see `differencies.md`); we use instead:
* *threshold lumping*: projecting opinions to `y ≤ ·` turns Copy-or-Max into binary Copy-or-Max
  (`thr_pow`), so the binary fixation probabilities are determined by the hypothesis;
* the binary fixation probability is harmonic; harmonicity at a configuration with a single `0`
  at agent `v` forces in-flow = out-flow at `v`;
* a disconnected support graph never reaches consensus from a configuration with distinct
  opinions.
-/

set_option linter.unusedSectionVars false

namespace OrderStatisticsPP

open Finset Matrix Filter Topology Cslib.Probability.Markov

variable {n : ℕ} {α : Type*} [LinearOrder α] [Fintype α] {w : Fin n → Fin n → ℝ} {p : ℝ}

/-! ### Threshold lumping -/

/-- Threshold projection to binary opinions (`true` iff `y ≤ opinion`). -/
def thr (y : α) (s : Config n α) : Config n Bool := fun u => decide (y ≤ s u)

lemma thr_step (y : α) (ω : Fin n × Fin n × Bool) (s : Config n α) :
    thr y (Function.update s ω.1 (comNew s ω)) =
      Function.update (thr y s) ω.1 (comNew (thr y s) ω) := by
  funext v
  unfold thr
  rcases eq_or_ne v ω.1 with rfl | h
  · simp only [Function.update_self, comNew]
    split_ifs
    · rfl
    · by_cases ha : y ≤ s ω.1 <;> by_cases hb : y ≤ s ω.2.1 <;> simp [ha, hb, le_max_iff]
  · simp [Function.update_of_ne h]

lemma thr_pow (y : α) (t : ℕ) (g : Config n Bool → ℝ) (s : Config n α) :
    ((copyOrMaxW w p : Matrix (Config n Bool) _ ℝ) ^ t *ᵥ g) (thr y s) =
      ((copyOrMaxW w p : Matrix (Config n α) _ ℝ) ^ t *ᵥ (g ∘ thr y)) s :=
  pow_mulVec_comp_of_lump (thr y)
    (fun g s => randomMap_lump _ _ _ _ (fun ω s => thr_step y ω s) g s) t g s

/-! ### Configurations with prescribed order -/

/-- `#{u' ∈ T | u' < u}`. -/
def below (T : Finset (Fin n)) (u : Fin n) : ℕ := (T.filter (· < u)).card

lemma below_lt_below {T : Finset (Fin n)} {u v : Fin n} (hu : u ∈ T) (huv : u < v) :
    below T u < below T v := by
  unfold below
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans huv⟩
  · have := h (Finset.mem_filter.mpr ⟨hu, huv⟩)
    simp at this

lemma below_inj {T : Finset (Fin n)} {u v : Fin n} (hu : u ∈ T) (hv : v ∈ T)
    (h : below T u = below T v) : u = v := by
  rcases lt_trichotomy u v with huv | rfl | huv
  · exact absurd h (below_lt_below hu huv).ne
  · rfl
  · exact absurd h (below_lt_below hv huv).ne'

lemma below_lt_card {T : Finset (Fin n)} {u : Fin n} (hu : u ∈ T) : below T u < T.card := by
  unfold below
  exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨u, hu, lt_irrefl u⟩)

/-- Position of `u` when the agents of `O` are placed on top (in index order), the others below. -/
def rk (O : Finset (Fin n)) (u : Fin n) : ℕ :=
  if u ∈ O then (n - O.card) + below O u else below Oᶜ u

lemma rk_lt (O : Finset (Fin n)) (u : Fin n) : rk O u < n := by
  unfold rk
  have hO : O.card ≤ n := by simpa using Finset.card_le_univ O
  split_ifs with hu
  · have := below_lt_card hu; omega
  · have := below_lt_card (Finset.mem_compl.mpr hu)
    rw [Finset.card_compl, Fintype.card_fin] at this; omega

lemma rk_ge_iff (O : Finset (Fin n)) (u : Fin n) : n - O.card ≤ rk O u ↔ u ∈ O := by
  unfold rk
  split_ifs with hu
  · simp [hu]
  · have := below_lt_card (Finset.mem_compl.mpr hu)
    rw [Finset.card_compl, Fintype.card_fin] at this
    simp only [hu, iff_false, not_le]; omega

lemma rk_injective (O : Finset (Fin n)) : Function.Injective (rk O) := by
  intro u v h
  have hu := rk_ge_iff O u
  have hv := rk_ge_iff O v
  by_cases hu' : u ∈ O <;> by_cases hv' : v ∈ O
  · unfold rk at h; simp only [hu', hv', ite_true] at h
    exact below_inj hu' hv' (by omega)
  · exact absurd (h ▸ hu.mpr hu') (fun h' => hv' (hv.mp h'))
  · exact absurd (h ▸ hv.mpr hv') (fun h' => hu' (hu.mp (h.symm ▸ h')))
  · unfold rk at h; simp only [hu', hv', ite_false] at h
    exact below_inj (Finset.mem_compl.mpr hu') (Finset.mem_compl.mpr hv') h

/-- A permutation of the agents placing `O` on the top `|O|` positions. -/
noncomputable def topPerm (O : Finset (Fin n)) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun u => ⟨rk O u, rk_lt O u⟩)
    (Finite.injective_iff_bijective.mp fun _ _ h => rk_injective O (Fin.mk.inj_iff.mp h))

lemma topPerm_val (O : Finset (Fin n)) (u : Fin n) : (topPerm O u : ℕ) = rk O u := rfl

/-- Rank of `E (σ u)` in the configuration `E ∘ σ`. -/
lemma rank_comp (E : Fin n ↪o α) (σ : Equiv.Perm (Fin n)) (u : Fin n) :
    rank (fun v => E (σ v)) (E (σ u)) = σ u + 1 := by
  unfold rank cnt
  calc Nat.card {v // E (σ v) ∈ Set.Iic (E (σ u))}
      = Nat.card {v // σ v ≤ σ u} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun v => by simp)
    _ = Nat.card {j : Fin n // j ≤ σ u} := Nat.card_congr (σ.subtypeEquiv fun v => Iff.rfl)
    _ = σ u + 1 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        rw [show (univ.filter fun j : Fin n => j ≤ σ u) = Finset.Iic (σ u) by ext; simp]
        exact Fin.card_Iic _

/-! ### Binary fixation probabilities under the hypothesis -/

/-- Hypothesis of the converse: the geometric fixation law holds from every configuration with
pairwise distinct opinions. -/
def GeomFix (w : Fin n → Fin n → ℝ) (p : ℝ) (α : Type*) [LinearOrder α] [Fintype α] : Prop :=
  ∀ c : Config n α, Function.Injective c → ∀ u,
    Tendsto (fun t => ((copyOrMaxW w p : Matrix (Config n α) _ ℝ) ^ t) c (const (c u))) atTop
      (𝓝 (geomLaw n p (rank c (c u))))

lemma cnt_Iio_true (b : Config n Bool) :
    cnt (Set.Iio true) b = n - (univ.filter fun u => b u = true).card := by
  rw [cnt_eq_card]
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun u => b u = true)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  have e : (univ.filter fun u => b u ∈ Set.Iio true) = univ.filter fun u => ¬ b u = true := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Iio]
    generalize b u = x
    cases x <;> decide
  rw [e]; omega

lemma sum_geomLaw_perm (σ : Equiv.Perm (Fin n)) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 0 < n) : ∑ u, geomLaw n p (σ u + 1) = 1 := by
  rw [Equiv.sum_comp σ (fun j : Fin n => geomLaw n p (j + 1)),
    Fin.sum_univ_eq_sum_range (fun j => geomLaw n p (j + 1)), ← cumul_eq_sum_range,
    cumul_geomLaw hp0 hp1 hn]

lemma sum_compl_geomLaw_topPerm (O : Finset (Fin n)) (p : ℝ) :
    ∑ u ∈ Oᶜ, geomLaw n p (topPerm O u + 1) = cumul (geomLaw n p) (n - O.card) := by
  rw [cumul_eq_sum_range]
  refine Finset.sum_bij (fun u _ => (topPerm O u : ℕ)) ?_ ?_ ?_ ?_
  · intro u hu
    have := (rk_ge_iff O u).not.mpr (Finset.mem_compl.mp hu)
    rw [Finset.mem_range, topPerm_val]; omega
  · intro u _ v _ h
    exact (topPerm O).injective (Fin.ext h)
  · intro j hj
    rw [Finset.mem_range] at hj
    have hjn : j < n := by have := Finset.card_le_univ O; simp at this; omega
    refine ⟨(topPerm O).symm ⟨j, hjn⟩, ?_, by simp⟩
    rw [Finset.mem_compl, ← rk_ge_iff, ← topPerm_val, Equiv.apply_symm_apply]
    simp only; omega
  · intro u _; rfl

lemma bin_limit (hn : 0 < n) (E : Fin n ↪o α) (hw : ∀ u v, 0 ≤ w u v)
    (hW : 0 < ∑ i, ∑ j, w i j) (hp0 : 0 < p) (hp1 : p < 1) (H : GeomFix w p α)
    (b : Config n Bool) :
    Tendsto (fun t => ((copyOrMaxW w p : Matrix (Config n Bool) _ ℝ) ^ t) b (const true)) atTop
      (𝓝 (1 - cumul (geomLaw n p) (cnt (Set.Iio true) b))) := by
  rw [cnt_Iio_true]
  set O := univ.filter fun u => b u = true with hOdef
  by_cases hO : O = ∅
  · -- `b` is the consensus on `false`, which is absorbing
    have hb : b = const false := by
      funext u
      have : u ∉ O := by rw [hO]; simp
      simpa [hOdef, const] using this
    rw [hO, Finset.card_empty, Nat.sub_zero, cumul_geomLaw hp0 hp1 hn, sub_self]
    have hz : ∀ t, ((copyOrMaxW w p : Matrix (Config n Bool) _ ℝ) ^ t) b (const true) = 0 := by
      intro t
      rw [hb]
      refine pow_eq_zero_of_closed (copyOrMaxW_mem hw hW hp0.le hp1.le) (· = const false)
        (fun a b' ha hab => ?_) rfl t ?_
      · by_contra hne
        subst ha
        exact (lt_irrefl _) (copyOrMaxW_absorbing false b' hne ▸ hab)
      · intro h
        exact Bool.noConfusion (congrFun h ⟨0, hn⟩)
    simp [hz]
  have hOne : O.Nonempty := Finset.nonempty_iff_ne_empty.mpr hO
  have hOpos : 0 < O.card := Finset.card_pos.mpr hOne
  set k := n - O.card with hk
  have hkn : k < n := by omega
  set σ := topPerm O
  set c : Config n α := fun v => E (σ v) with hcdef
  set y : α := E ⟨k, hkn⟩
  have hc : Function.Injective c := E.injective.comp σ.injective
  have hyc : ∀ u, y ≤ c u ↔ u ∈ O := by
    intro u
    simp only [y, hcdef, E.le_iff_le, Fin.le_def, σ, topPerm_val]
    exact rk_ge_iff O u
  have hb : thr y c = b := by
    funext u
    simp only [thr, hyc, hOdef, Finset.mem_filter, Finset.mem_univ, true_and]
    cases b u <;> simp
  set T : Matrix (Config n α) _ ℝ := copyOrMaxW w p
  have hT := copyOrMaxW_mem (α := α) hw hW hp0.le hp1.le
  -- the binary probability as a sum over configurations
  have hL : ∀ t, ((copyOrMaxW w p : Matrix (Config n Bool) _ ℝ) ^ t) b (const true) =
      ∑ s, (T ^ t) c s * (if thr y s = const true then 1 else 0) := by
    intro t
    rw [pow_apply_eq_mulVec ((copyOrMaxW w p : Matrix (Config n Bool) _ ℝ) ^ t) b (const true),
      ← hb, thr_pow]
    simp [mulVec, dotProduct, T, Function.comp]
  have hlimu : ∀ u, Tendsto (fun t => (T ^ t) c (const (c u))) atTop
      (𝓝 (geomLaw n p (σ u + 1))) := by
    intro u
    have := H c hc u
    rwa [rank_comp E σ u] at this
  have hinj : Function.Injective fun u => (const (c u) : Config n α) :=
    fun u v h => hc (const_injective hn h)
  -- lower bound
  have hlow : ∀ t, ∑ u ∈ O, (T ^ t) c (const (c u)) ≤
      ∑ s, (T ^ t) c s * (if thr y s = const true then 1 else 0) := by
    intro t
    rw [← Finset.sum_image (f := fun s => (T ^ t) c s) (fun u _ v _ h => hinj h)]
    calc ∑ s ∈ O.image fun u => const (c u), (T ^ t) c s
        = ∑ s ∈ O.image fun u => const (c u),
            (T ^ t) c s * (if thr y s = const true then 1 else 0) := by
          refine Finset.sum_congr rfl fun s hs => ?_
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
          have : thr y (const (c u) : Config n α) = (const true : Config n Bool) := by
            funext v; simp [thr, const, (hyc u).mpr hu]
          rw [ite_eq_left this, mul_one]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun s _ _ => mul_nonneg (pow_nonneg_entry hT t _ _) (by split_ifs <;> norm_num)
  -- upper bound
  have hup : ∀ t, ∑ s, (T ^ t) c s * (if thr y s = const true then 1 else 0) ≤
      1 - ∑ u ∈ Oᶜ, (T ^ t) c (const (c u)) := by
    intro t
    set A := Oᶜ.image fun u => (const (c u) : Config n α)
    have e2 : ∑ u ∈ Oᶜ, (T ^ t) c (const (c u)) = ∑ s, (T ^ t) c s * (if s ∈ A then 1 else 0) := by
      rw [← Finset.sum_image (f := fun s => (T ^ t) c s) (fun u _ v _ h => hinj h)]
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [e2, le_sub_iff_add_le, ← Finset.sum_add_distrib]
    refine le_trans (Finset.sum_le_sum fun s _ => ?_) (pow_sum_row hT t c).le
    have h0 := pow_nonneg_entry hT t c s
    by_cases hs : s ∈ A
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
      have : thr y (const (c u) : Config n α) ≠ (const true : Config n Bool) := by
        intro h
        have := congrFun h ⟨0, hn⟩
        simp [thr, const, (hyc u).not.mpr (Finset.mem_compl.mp hu)] at this
      rw [ite_eq_right this, ite_eq_left hs]; linarith
    · rw [ite_eq_right hs]; split_ifs <;> linarith
  -- limits of the bounds
  have hG : ∑ u ∈ O, geomLaw n p (σ u + 1) = 1 - cumul (geomLaw n p) k := by
    have h1 := sum_geomLaw_perm σ hp0 hp1 hn
    rw [← Finset.sum_compl_add_sum O] at h1
    rw [← sum_compl_geomLaw_topPerm O p]
    linarith
  have hlo : Tendsto (fun t => ∑ u ∈ O, (T ^ t) c (const (c u))) atTop
      (𝓝 (1 - cumul (geomLaw n p) k)) := by
    rw [← hG]; exact tendsto_finsetSum _ fun u _ => hlimu u
  have hhi : Tendsto (fun t => 1 - ∑ u ∈ Oᶜ, (T ^ t) c (const (c u))) atTop
      (𝓝 (1 - cumul (geomLaw n p) k)) := by
    rw [← sum_compl_geomLaw_topPerm O p]
    exact tendsto_const_nhds.sub (tendsto_finsetSum _ fun u _ => hlimu u)
  simp_rw [hL]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi hlow hup

/-- Under the hypothesis, the binary fixation probability is harmonic, which yields the balance
`π(m+1) · P[up] = π(m) · P[down]` at every binary configuration. -/
lemma bin_balance (hn : 0 < n) (E : Fin n ↪o α) (hw : ∀ u v, 0 ≤ w u v)
    (hW : 0 < ∑ i, ∑ j, w i j) (hp0 : 0 < p) (hp1 : p < 1) (H : GeomFix w p α)
    (b : Config n Bool) :
    geomLaw n p (cnt (Set.Iio true) b + 1) *
        upMass (comμ w p) (fun ω _ => ω.1) (fun ω c => comNew c ω) (Set.Iio true) b =
      geomLaw n p (cnt (Set.Iio true) b) *
        downMass (comμ w p) (fun ω _ => ω.1) (fun ω c => comNew c ω) (Set.Iio true) b := by
  set TB : Matrix (Config n Bool) _ ℝ := copyOrMaxW w p
  have hTB : TB ∈ rowStochastic ℝ _ := copyOrMaxW_mem hw hW hp0.le hp1.le
  set F : Config n Bool → ℝ := fun b => 1 - cumul (geomLaw n p) (cnt (Set.Iio true) b)
  have hF : ∀ b, Tendsto (fun t => (TB ^ t) b (const true)) atTop (𝓝 (F b)) :=
    bin_limit hn E hw hW hp0 hp1 H
  have hharm : (TB *ᵥ F) b = F b := by
    have h1 : Tendsto (fun t => (TB ^ (t + 1)) b (const true)) atTop (𝓝 (F b)) :=
      (hF b).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun t => (TB ^ (t + 1)) b (const true)) atTop (𝓝 ((TB *ᵥ F) b)) := by
      simp only [pow_succ', mul_apply]
      exact tendsto_finsetSum _ fun b' _ => (hF b').const_mul _
    exact tendsto_nhds_unique h2 h1
  have hcum : (TB *ᵥ fun b => cumul (geomLaw n p) (cnt (Set.Iio true) b)) b =
      cumul (geomLaw n p) (cnt (Set.Iio true) b) := by
    have e : (fun b => cumul (geomLaw n p) (cnt (Set.Iio true) b)) = fun b => 1 - F b := by
      funext b; simp [F]
    rw [e]
    have hs := sum_row_of_mem_rowStochastic hTB b
    simp only [mulVec, dotProduct, mul_sub, mul_one, Finset.sum_sub_distrib, hs] at hharm ⊢
    linarith
  have key := randomMap_mulVec_cumul (comμ w p) (comμ_sum hW) (fun ω _ => ω.1)
    (fun ω c => comNew c ω) (geomLaw n p) (Set.Iio true) b
  have : (copyOrMaxW w p : Matrix (Config n Bool) _ ℝ) =
      randomMap (comμ w p) (fun ω c => Function.update c ω.1 (comNew c ω)) := rfl
  rw [← this] at key
  linarith

/-- Under the hypothesis, the weights form a circulation. -/
theorem isCirculation_of_geomFix (hn : 0 < n) (E : Fin n ↪o α) (hw : ∀ u v, 0 ≤ w u v)
    (hW : 0 < ∑ i, ∑ j, w i j) (hp0 : 0 < p) (hp1 : p < 1) (H : GeomFix w p α) :
    IsCirculation w := by
  intro v
  by_cases hn1 : n = 1
  · subst hn1
    have : ∀ u : Fin 1, u = v := fun u => Subsingleton.elim u v
    simp [this 0]
  have hn2 : 2 ≤ n := by omega
  -- the binary configuration with a single `false` at `v`
  set b : Config n Bool := fun u => decide (u ≠ v)
  have hI : ∀ x, ind (Set.Iio true) (b x) = if x = v then 1 else 0 := by
    intro x
    by_cases hx : x = v
    · subst hx; simp [b, ind_mem]
    · simp [b, hx, ind_not_mem]
  have hm : cnt (Set.Iio true) b = 1 := by
    have := cnt_eq_sum (Set.Iio true) b
    simp only [hI, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
    exact_mod_cast this
  have hbal := bin_balance hn E hw hW hp0 hp1 H b
  rw [com_upMass (isLowerSet_Iio true), com_downMass (isLowerSet_Iio true), hm] at hbal
  simp only [hI] at hbal
  have hup : ∑ u, ∑ v', w u v' * ((1 - if u = v then (1 : ℝ) else 0) * if v' = v then 1 else 0) =
      ∑ u, w u v - w v v := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_sub,
      Finset.sum_sub_distrib]
  have hdown : ∑ u, ∑ v', w u v' * ((if u = v then (1 : ℝ) else 0) * (1 - if v' = v then 1 else 0)) =
      ∑ u, w v u - w v v := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq']
  rw [hup, hdown] at hbal
  have h12 := geomLaw_succ_mul (n := n) (p := p) (m := 1) (by omega)
  have hpos := geomLaw_pos hp0 hp1 hn (1 + 1)
  rw [← h12] at hbal
  have key : geomLaw n p (1 + 1) * p / (∑ i, ∑ j, w i j) *
      ((∑ u, w u v - w v v) - (∑ u, w v u - w v v)) = 0 := by
    linear_combination hbal
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (by positivity)
  · linarith

/-- Under the hypothesis, the support graph is connected. -/
theorem connected_of_geomFix (hn : 0 < n) (E : Fin n ↪o α) (hw : ∀ u v, 0 ≤ w u v)
    (hW : 0 < ∑ i, ∑ j, w i j) (hp0 : 0 < p) (hp1 : p < 1) (H : GeomFix w p α) :
    (supportGraph w).Connected := by
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [SimpleGraph.connected_iff]
  refine ⟨fun a z => ?_, hne⟩
  by_contra hr
  classical
  set S := univ.filter fun x => (supportGraph w).Reachable a x
  have haS : a ∈ S := by simp [S]
  have hzS : z ∉ S := by simpa [S] using hr
  -- no positive edge crosses the cut
  have hcut : ∀ x y, 0 < w x y → (x ∈ S ↔ y ∈ S) := by
    intro x y hxy
    by_cases hxy' : x = y
    · subst hxy'; rfl
    have hadj : (supportGraph w).Adj x y := by
      simp only [supportGraph, SimpleGraph.fromRel_adj]; exact ⟨hxy', Or.inl hxy⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
  set c : Config n α := fun v => E v
  have hc : Function.Injective c := E.injective
  set T : Matrix (Config n α) _ ℝ := copyOrMaxW w p
  have hT : T ∈ rowStochastic ℝ _ := copyOrMaxW_mem hw hW hp0.le hp1.le
  set P : Config n α → Prop := fun s => ∀ u, ∃ v, s u = c v ∧ (u ∈ S ↔ v ∈ S)
  have hP : ∀ s s', P s → 0 < T s s' → P s' := by
    intro s s' hs hss'
    obtain ⟨ω, hω, rfl⟩ := exists_of_randomMap_pos hss'
    have hwω : 0 < w ω.1 ω.2.1 := by
      by_contra hle
      have : w ω.1 ω.2.1 = 0 := le_antisymm (not_lt.mp hle) (hw _ _)
      simp [comμ, this] at hω
    have hS := hcut _ _ hwω
    intro u
    rcases eq_or_ne u ω.1 with rfl | hu
    · rw [Function.update_self]
      have hx : ∃ x, comNew s ω = s x ∧ (ω.1 ∈ S ↔ x ∈ S) := by
        unfold comNew
        split_ifs
        · exact ⟨ω.2.1, rfl, hS⟩
        · rcases max_choice (s ω.1) (s ω.2.1) with h | h
          · exact ⟨ω.1, h, Iff.rfl⟩
          · exact ⟨ω.2.1, h, hS⟩
      obtain ⟨x, hx, hxS⟩ := hx
      obtain ⟨v, hv, hvS⟩ := hs x
      exact ⟨v, hx.trans hv, hxS.trans hvS⟩
    · rw [Function.update_of_ne hu]; exact hs u
  have hPc : P c := fun u => ⟨u, rfl, Iff.rfl⟩
  have hnot : ¬ P (const (c a)) := by
    intro h
    obtain ⟨v, hv, hvS⟩ := h z
    have : a = v := hc hv
    subst this
    exact hzS (hvS.mpr haS)
  have hzero : ∀ t, (T ^ t) c (const (c a)) = 0 := fun t =>
    pow_eq_zero_of_closed hT P hP hPc t hnot
  have hlim := H c hc a
  simp only [T] at hzero
  simp only [hzero] at hlim
  exact (geomLaw_pos hp0 hp1 hn _).ne (tendsto_nhds_unique tendsto_const_nhds hlim)

/-- **Proposition 6 / Theorem 1(2) (both directions).** For nonnegative weights with positive
total weight and `p ∈ (0, 1)`, the weighted Copy-or-Max dynamics fixes on the `k`-th smallest
opinion with probability `(1-p) p^(n-k) / (1-p^n)` from every configuration with distinct
opinions if and only if the weights form a circulation and the support graph is connected.
(Opinions range over a finite linear order with at least `n` elements.) -/
theorem copyOrMaxW_geomFix_iff (hn : 0 < n) (hcard : n ≤ Fintype.card α)
    (hw : ∀ u v, 0 ≤ w u v) (hW : 0 < ∑ i, ∑ j, w i j) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ c : Config n α, Function.Injective c → ∀ u,
      Tendsto (fun t => ((copyOrMaxW w p : Matrix (Config n α) _ ℝ) ^ t) c (const (c u))) atTop
        (𝓝 ((1 - p) * p ^ (n - rank c (c u)) / (1 - p ^ n)))) ↔
      IsCirculation w ∧ (supportGraph w).Connected := by
  let E : Fin n ↪o α := (Finset.univ : Finset α).orderEmbOfCardLe (by simpa using hcard)
  constructor
  · intro H
    exact ⟨isCirculation_of_geomFix hn E hw hW hp0 hp1 H,
      connected_of_geomFix hn E hw hW hp0 hp1 H⟩
  · rintro ⟨hcirc, hconn⟩ c hc u
    exact copyOrMaxW_fixation_injective hn hw hW hp0 hp1 hcirc hconn c hc u

end OrderStatisticsPP
