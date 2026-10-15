import Papers.PODC2018.AsymptoticConsensus.Exact
import Papers.PODC2018.AsymptoticConsensus.FirstDeviation

/-!
# Theorem 4 of FNS'18: exact consensus vs. topology of valencies

Theorem 4 claims: *exact consensus is solvable in `N` iff some asymptotic consensus algorithm
for `N` has, for all `N' ⊆ N` and all initial configurations, a valency that is a singleton or
disconnected.*

* (⇒) holds: `theorem4_mp` (in `Exact.lean`).
* (⇐) is **false**: `theorem4_false`. The algorithm `fd` (`FirstDeviation.lean`) solves
  asymptotic consensus in `{H₀, H₁, H₂}` (two agents) and all its limits are initial values, so its
  valencies are finite; yet exact consensus is not solvable there (`not_exactSolvable_N3`, from
  Theorem 1). The paper's proof uses "`δ_N(C_t) → 0` along every execution by Convergence and
  Agreement", which holds only when the consensus function is continuous (the paper itself notes
  that it need not be). Consequently `fd` has non-vanishing valency diameters
  (`fd_not_vanishing`).
* Repaired (⇐) (`theorem4_mpr_repaired`): for algorithms with vanishing valency diameters
  (`VanishingValency`, equivalent to continuity of the consensus function), every
  source-incompatible submodel of finite α-diameter yields a valency that is a nontrivial connected
  set. With the characterization of Coulouma et al. [12] as a hypothesis (`CouloumaHyp`), this gives
  the corrected equivalence `theorem4_repaired`.
-/

namespace AsymptoticConsensus

open Cslib.HeardOf Cslib.HeardOf.Chain Filter Topology Set Classical
open Cslib.DynNet (IsRoot)
open scoped ENNReal

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The statement of Theorem 4 of FNS'18 for agents `α` and values `V`. -/
def Theorem4Statement (α V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : Prop :=
  ∀ N : Set (Graph α), ExactSolvable α V N ↔
    ∃ (σ : Type) (A : Alg α σ V), A.Solves N ∧ ValencyProp A N

theorem valencyProp_fd [Nontrivial V] :
    ValencyProp (fd (V := V)) ({H0, H1, H2} : Set (Graph (Fin 2))) := by
  intro N' hN' hne x
  refine singleton_or_not_preconnected_of_finite ((Set.toFinite {x 0, x 1}).subset ?_)
    ((fd_solves.mono hN').val_nonempty hne (Alg.Reach.initC hne x))
  rintro z ⟨q, hq, hz⟩
  rcases fd_limit x q (pat_mono hN' hq) z hz with rfl | rfl <;> simp

/-- **Theorem 4 (⇐) of FNS'18 is false**: for two agents and the network model `{H₀, H₁, H₂}`,
the algorithm `fd` solves asymptotic consensus and all its valencies of initial configurations are
singletons or disconnected, but exact consensus is not solvable. -/
theorem theorem4_mpr_counterexample [Nontrivial V] :
    (fd (V := V)).Solves ({H0, H1, H2} : Set (Graph (Fin 2))) ∧
    ValencyProp (fd (V := V)) ({H0, H1, H2} : Set (Graph (Fin 2))) ∧
    ¬ ExactSolvable (Fin 2) V ({H0, H1, H2} : Set (Graph (Fin 2))) :=
  ⟨fd_solves, valencyProp_fd, not_exactSolvable_N3 subset_rfl⟩

/-- **Theorem 4 of FNS'18 is false** (for two agents and real values). -/
theorem theorem4_false : ¬ Theorem4Statement (Fin 2) ℝ := by
  intro h
  obtain ⟨hs, hv, hne⟩ := theorem4_mpr_counterexample (V := ℝ)
  exact hne ((h _).2 ⟨_, fd, hs, hv⟩)

/-! ### The repaired converse -/

/-- Valency diameters vanish along every execution of every submodel (equivalently: the
consensus function is continuous). The paper asserts this for all algorithms. -/
def VanishingValency {α σ : Type*} (A : Alg α σ V) (N : Set (Graph α)) : Prop :=
  ∀ N' ⊆ N, ∀ x : α → V, ∀ p ∈ Pat N',
    Tendsto (fun t => A.δ N' (conf A.step (A.initC x) p t)) atTop (𝓝 0)

theorem coord_sub_le (φ : V →L[ℝ] ℝ) (u w : V) : |φ u - φ w| ≤ ‖φ‖ * dist u w := by
  rw [← map_sub, dist_eq_norm, ← Real.norm_eq_abs]; exact φ.le_opNorm _

/-- **Theorem 4 (⇐), repaired.** Let `A` solve asymptotic consensus in `N` with vanishing
valency diameters. If `N' ⊆ N` is nonempty, source-incompatible and has finite α-diameter, then
some initial configuration has a valency in `N'` that is nontrivial and connected. -/
theorem theorem4_mpr_repaired [Nontrivial V] {n : ℕ} (hn : 2 ≤ n) {σ : Type*}
    {A : Alg (Fin n) σ V} {N N' : Set (Graph (Fin n))} (hA : A.Solves N)
    (hvan : VanishingValency A N) (hN' : N' ⊆ N) (hne : N'.Nonempty)
    (hSI : SourceIncompatible N') {D : ℕ} (hα : AlphaDiamLE AlphaRel N' D) :
    ∃ x : Fin n → V, (A.val (Pat N') (A.initC x)).Nontrivial ∧
      IsPreconnected (A.val (Pat N') (A.initC x)) := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hA' : A.Solves N' := hA.mono hN'
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨g, -, hgv⟩ := exists_dual_vector ℝ v (norm_ne_zero_iff.2 hv)
  set φ : V →L[ℝ] ℝ := ‖v‖⁻¹ • g
  have hφv : φ v = 1 := by
    simp [φ, hgv, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  have hφpos : 0 < ‖φ‖ := norm_pos_iff.2 fun h => by simp [h] at hφv
  obtain ⟨x, hx01, hδ⟩ := Alg.lemma21 hn hA' hSI v
  set Y := A.val (Pat N') (A.initC x)
  -- the valency lies on the segment `[0, v]`; coordinates along it are given by `φ`
  have hseg : Y ⊆ segment ℝ 0 v := by
    refine (hA'.val_initC_subset_hull hne x).trans ?_
    rw [← convexHull_pair]
    exact convexHull_mono (by rintro _ ⟨i, rfl⟩; rcases hx01 i with h | h <;> simp [h])
  have hcoord : ∀ y ∈ Y, y = φ y • v := by
    intro y hy
    obtain ⟨a, b, -, -, -, rfl⟩ := hseg hy
    simp [hφv]
  have hnt : Y.Nontrivial := by
    rw [← Metric.ediam_pos_iff]
    refine pos_iff_ne_zero.2 fun h0 => hv ?_
    have : edist (0 : V) v ≤ 0 := by simpa [Alg.δ, Y, h0] using hδ
    exact (edist_le_zero.1 this).symm
  -- the key claim: no gaps
  have key : ∀ θ : ℝ, (∃ a ∈ Y, φ a < θ) → (∃ b ∈ Y, θ < φ b) → θ • v ∈ Y := by
    intro θ ⟨a, ha, hat⟩ ⟨b, hb, hbt⟩
    by_contra hθ
    have hnotθ : ∀ w ∈ Y, φ w ≠ θ := fun w hw h => hθ (by rw [← h, ← hcoord w hw]; exact hw)
    let Inv : (Fin n → σ) → Prop := fun C => A.Reach N' C ∧ A.val (Pat N') C ⊆ Y ∧
      (∃ a ∈ A.val (Pat N') C, φ a < θ) ∧ (∃ b ∈ A.val (Pat N') C, θ < φ b)
    have hstep : ∀ C, Inv C → ∃ G ∈ N', Inv (next A.step G C) ∧
        (0 : ℝ≥0∞) ≤ 1 * 0 := by
      rintro C ⟨hC, hCY, ⟨a, ha, hat⟩, ⟨b, hb, hbt⟩⟩
      rw [Alg.val_eq_iUnion N' C, mem_iUnion₂] at ha hb
      obtain ⟨G, hG, haG⟩ := ha
      obtain ⟨H, hH, hbH⟩ := hb
      obtain ⟨q, -, c, hc0, hcq, hc⟩ := hα G hG H hH
      have hcN : ∀ r ≤ q, c r ∈ N' := by
        intro r hr
        rcases Nat.eq_zero_or_pos r with rfl | hr0
        · rw [hc0]; exact hG
        · have := (hc (r - 1) (by omega)).2.1; rwa [Nat.sub_add_cancel hr0] at this
      have hex : ∃ r, r ≤ q ∧ ∃ w ∈ A.val (Pat N') (next A.step (c r) C), θ < φ w :=
        ⟨q, le_rfl, b, hcq ▸ hbH, hbt⟩
      set r := Nat.find hex
      obtain ⟨hrq, w, hw, hwt⟩ := Nat.find_spec hex
      have hsub : A.val (Pat N') (next A.step (c r) C) ⊆ Y :=
        (Alg.val_next_subset (hcN r hrq) C).trans hCY
      refine ⟨c r, hcN r hrq, ⟨hC.next (hcN r hrq), hsub, ?_, ⟨w, hw, hwt⟩⟩, by simp⟩
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · exact ⟨a, by rw [hr0, hc0]; exact haG, hat⟩
      · have hmin := Nat.find_min hex (show r - 1 < r by omega)
        obtain ⟨h1, h2, K, hK, hrel⟩ := hc (r - 1) (by omega)
        obtain ⟨u, hu1, hu2⟩ := Alg.val_inter_nonempty_alpha hA' h1 h2 hK hrel hC
        rw [Nat.sub_add_cancel hr0] at hu2
        have hle : φ u ≤ θ := by
          by_contra hlt; push Not at hlt
          exact hmin ⟨by omega, u, hu1, hlt⟩
        exact ⟨u, hu2, lt_of_le_of_ne hle (hnotθ u (hsub hu2))⟩
    obtain ⟨s, Cs, h0, hs, hsucc, hinv⟩ := exists_seq_of_step (next A.step) N' Inv
      (fun _ => 0) 1 hstep (A.initC x)
      ⟨Alg.Reach.initC hne x, subset_rfl, ⟨a, ha, hat⟩, ⟨b, hb, hbt⟩⟩
    have hp : s ∈ Pat N' := hs
    have hCs : ∀ t, Cs t = conf A.step (A.initC x) s t := by
      intro t; induction t with
      | zero => exact h0
      | succ t ih => rw [hsucc, ih, conf_succ]
    obtain ⟨y, -, hy⟩ := hA' x s hp
    have hyC : ∀ t, y ∈ A.val (Pat N') (Cs t) := fun t =>
      ⟨shift t s, shift_mem_pat hp t, by rw [hCs]; exact (Alg.hasLimit_shift t).2 hy⟩
    have hyY : y ∈ Y := (hinv 0).1.2.1 (hyC 0)
    have hlim := hvan N' hN' x s hp
    -- `φ y = θ`, contradiction
    have hclose : ∀ d > 0, ∀ᶠ t in atTop, ∀ u ∈ A.val (Pat N') (Cs t), |φ y - φ u| < d := by
      intro d hd
      have hr : 0 < d / (2 * ‖φ‖) := div_pos hd (by positivity)
      have := (ENNReal.tendsto_nhds_zero.1 hlim) (ENNReal.ofReal (d / (2 * ‖φ‖))) (by simpa using hr)
      filter_upwards [this] with t ht u hu
      rw [← hCs] at ht
      have hed : edist y u ≤ ENNReal.ofReal (d / (2 * ‖φ‖)) :=
        (Metric.edist_le_ediam_of_mem (hyC t) hu).trans ht
      rw [edist_le_ofReal hr.le] at hed
      calc |φ y - φ u| ≤ ‖φ‖ * dist y u := coord_sub_le φ y u
        _ ≤ ‖φ‖ * (d / (2 * ‖φ‖)) := by gcongr
        _ = d / 2 := by field_simp
        _ < d := by linarith
    have hne' := hnotθ y hyY
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · obtain ⟨t, ht⟩ := (hclose (θ - φ y) (by linarith)).exists
      obtain ⟨-, -, -, ⟨b, hb, hbt⟩⟩ := hinv t |>.1
      have := ht b hb
      rw [abs_lt] at this; linarith
    · obtain ⟨t, ht⟩ := (hclose (φ y - θ) (by linarith)).exists
      obtain ⟨-, -, ⟨a, ha, hat⟩, -⟩ := hinv t |>.1
      have := ht a ha
      rw [abs_lt] at this; linarith
  -- `Y` is the image of an order-connected set of coordinates
  set T : Set ℝ := {θ | θ • v ∈ Y}
  have hYT : Y = (fun θ : ℝ => θ • v) '' T := by
    ext y
    constructor
    · intro hy; exact ⟨φ y, by simpa [T, ← hcoord y hy] using hy, (hcoord y hy).symm⟩
    · rintro ⟨θ, hθ, rfl⟩; exact hθ
  have hφs : ∀ θ : ℝ, φ (θ • v) = θ := fun θ => by simp [hφv]
  have hT : T.OrdConnected := ⟨fun θ₁ h₁ θ₂ h₂ θ hθ => by
    rcases eq_or_lt_of_le hθ.1 with rfl | hlt1
    · exact h₁
    rcases eq_or_lt_of_le hθ.2 with rfl | hlt2
    · exact h₂
    exact key θ ⟨_, h₁, by rw [hφs]; exact hlt1⟩ ⟨_, h₂, by rw [hφs]; exact hlt2⟩⟩
  refine ⟨x, hnt, ?_⟩
  change IsPreconnected Y
  rw [hYT]
  exact hT.isPreconnected.image _ (continuous_id.smul continuous_const).continuousOn

/-- The part of the characterization of Coulouma, Godard, Peters [12] (Theorem 19 with Lemma 17)
used by Theorem 4: if exact consensus is not solvable in `N`, some nonempty submodel is
source-incompatible and α-connected (finite α-diameter). Taken as a hypothesis (not proved here). -/
def CouloumaHyp (n : ℕ) (V : Type) [NormedAddCommGroup V] (N : Set (Graph (Fin n))) : Prop :=
  ¬ ExactSolvable (Fin n) V N →
    ∃ N' ⊆ N, N'.Nonempty ∧ SourceIncompatible N' ∧ ∃ D, AlphaDiamLE AlphaRel N' D

/-- The derived algorithm of an exact consensus algorithm has vanishing valency diameters. -/
theorem vanishing_toAsym {α σ : Type*} [Finite α] [Nonempty α] {N : Set (Graph α)}
    {B : EAlg α σ V} (hB : B.Solves N) : VanishingValency (toAsym B) N := by
  intro N' hN' x p hp
  obtain ⟨T, hT⟩ := δ_toAsym_eventually_zero (hB.mono hN') x hp
  refine tendsto_atTop_of_eventually_const (i₀ := T) fun t ht => ?_
  exact le_antisymm ((Alg.δ_conf_antitone hp _ ht).trans hT.le) bot_le

/-- **Theorem 4 of FNS'18, repaired** (conditional on the characterization of [12]): exact
consensus is solvable in `N` iff some asymptotic consensus algorithm for `N` with vanishing
valency diameters (= continuous consensus function) has only singleton or disconnected valencies
of initial configurations in all submodels. The added continuity requirement is necessary
(`theorem4_false`). -/
theorem theorem4_repaired [Nontrivial V] {n : ℕ} (hn : 2 ≤ n) {N : Set (Graph (Fin n))}
    (hCGP : CouloumaHyp n V N) : ExactSolvable (Fin n) V N ↔
      ∃ (σ : Type) (A : Alg (Fin n) σ V), A.Solves N ∧ VanishingValency A N ∧ ValencyProp A N := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  constructor
  · rintro ⟨σ, B, hB⟩
    exact ⟨σ × V, toAsym B, (theorem4_mp hB).1, vanishing_toAsym hB, (theorem4_mp hB).2⟩
  · rintro ⟨σ, A, hA, hvan, hval⟩
    by_contra hex
    obtain ⟨N', hN', hne, hSI, D, hD⟩ := hCGP hex
    obtain ⟨x, hnt, hpc⟩ := theorem4_mpr_repaired hn hA hvan hN' hne hSI hD
    rcases hval N' hN' hne x with ⟨z, hz⟩ | hnpc
    · rw [hz] at hnt; exact hnt.not_subsingleton subsingleton_singleton
    · exact hnpc hpc

end AsymptoticConsensus
