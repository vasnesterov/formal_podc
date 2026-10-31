import Papers.PODC2014.LinearInDeltaLB.Ramsey

/-!
# Lemmas 6 and 7: the ID-algorithm is order-invariant on loopy neighbourhoods

Standing assumptions (`Setup`): `A` is a `t`-time ID-algorithm (`t ≥ 1`) finding maximal
fractional matchings on graphs of maximum degree `Δ ≥ 2k`; the order on `F_k` is left-invariant
(Lemma 4); `I ⊆ ℕ` is homogeneous for the saturation indicator on all shapes of radius `t`
(Lemma 5).

* `Setup.sat_of_loopy` (Lemma 6): in a loopy PO-view labelled order-preservingly by identifiers from
  `I`, `A` saturates every node near the root.
* `Setup.out_eq_of_single` (Lemma 7, one node changed): changing the identifier of one node in an
  order-preserving way does not change the output of the root — the propagation principle (Fact 8)
  would otherwise push a disagreement outside the radius-`t` neighbourhood of the changed node.
* `Setup.out_eq` (Lemma 7): the output of the root is the same for all order-preserving labellings
  by identifiers from `I` (via a chain of one-node changes, `chain_induction`).

Difference from the paper: we label the whole ball of radius `2t + 2` of the PO-view (not only
the radius-`t` ball) and compare labellings of the same ball; this removes the need for the sparse
subset `J ⊆ I` and for extending labellings.
-/

namespace Podc.LinearInDeltaLB

open FreeGroup Pointwise

/-- Propagation principle (Facts 3 and 8): two weightings with the same total `1` that disagree on
`i₀` disagree somewhere else. -/
theorem exists_ne_of_sum_eq {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∑ i ∈ s, a i = 1)
    (hb : ∑ i ∈ s, b i = 1) {i₀ : ι} (hi₀ : i₀ ∈ s) (hne : a i₀ ≠ b i₀) :
    ∃ i ∈ s, i ≠ i₀ ∧ a i ≠ b i := by
  classical
  by_contra h
  push Not at h
  have e : ∑ i ∈ s.erase i₀, a i = ∑ i ∈ s.erase i₀, b i :=
    Finset.sum_congr rfl fun i hi => h i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
  rw [← Finset.add_sum_erase s a hi₀] at ha
  rw [← Finset.add_sum_erase s b hi₀] at hb
  exact hne (by linarith)

/-- Connecting two order-preserving labellings of a finite set by one-node changes. -/
theorem chain_induction {β : Type*} [LinearOrder β] (R : Set β) (hR : R.Finite) (I : Set ℕ)
    (Q : (β → ℕ) → (β → ℕ) → Prop) (htrans : ∀ a b c, Q a b → Q b c → Q a c)
    (hstep : ∀ ψ₁ ψ₂ : β → ℕ, StrictMonoOn ψ₁ R → StrictMonoOn ψ₂ R → ψ₁ '' R ⊆ I →
      ψ₂ '' R ⊆ I → ∀ v, (∀ x ∈ R, x ≠ v → ψ₁ x = ψ₂ x) → Q ψ₁ ψ₂) (v₀ : β)
    (ψ₁ ψ₂ : β → ℕ) (hm₁ : StrictMonoOn ψ₁ R) (hm₂ : StrictMonoOn ψ₂ R) (hI₁ : ψ₁ '' R ⊆ I)
    (hI₂ : ψ₂ '' R ⊆ I) : Q ψ₁ ψ₂ := by
  classical
  suffices H : ∀ n (ψ₁ : β → ℕ), {x ∈ R | ψ₁ x ≠ ψ₂ x}.ncard = n → StrictMonoOn ψ₁ R →
      ψ₁ '' R ⊆ I → Q ψ₁ ψ₂ from H _ ψ₁ rfl hm₁ hI₁
  intro n
  induction n with
  | zero =>
    intro ψ₁ hn hm₁ hI₁
    rw [Set.ncard_eq_zero (hR.subset (fun x hx => hx.1))] at hn
    refine hstep ψ₁ ψ₂ hm₁ hm₂ hI₁ hI₂ v₀ fun x hx _ => ?_
    by_contra h
    have : x ∈ ({x ∈ R | ψ₁ x ≠ ψ₂ x} : Set β) := ⟨hx, h⟩
    rw [hn] at this; exact this
  | succ n ih =>
    intro ψ₁ hn hm₁ hI₁
    have hfin : {x ∈ R | ψ₁ x ≠ ψ₂ x}.Finite := hR.subset fun x hx => hx.1
    have hne : {x ∈ R | ψ₁ x ≠ ψ₂ x}.Nonempty := by
      rw [← Set.ncard_pos hfin, hn]; omega
    -- the node to change
    obtain ⟨x, hxD, hgood⟩ : ∃ x ∈ {x ∈ R | ψ₁ x ≠ ψ₂ x},
        StrictMonoOn (Function.update ψ₁ x (ψ₂ x)) R := by
      by_cases hA : ∃ x ∈ R, ψ₁ x < ψ₂ x
      · have hP : {x ∈ R | ψ₁ x < ψ₂ x}.Finite := hR.subset fun x hx => hx.1
        obtain ⟨x, ⟨hxR, hx⟩, hmax⟩ :=
          Set.exists_max_image _ id hP (by obtain ⟨x, hx, h⟩ := hA; exact ⟨x, hx, h⟩)
        refine ⟨x, ⟨hxR, hx.ne⟩, fun a ha b hb hab => ?_⟩
        by_cases hax : a = x <;> by_cases hbx : b = x
        · subst hax; subst hbx; exact absurd hab (lt_irrefl _)
        · subst hax
          simp only [Function.update_self, Function.update_of_ne hbx]
          have : ¬ ψ₁ b < ψ₂ b := fun h => absurd (hmax b ⟨hb, h⟩) (not_le.2 hab)
          exact lt_of_lt_of_le (hm₂ hxR hb hab) (not_lt.1 this)
        · subst hbx
          simp only [Function.update_self, Function.update_of_ne hax]
          exact (hm₁ ha hxR hab).trans hx
        · simp only [Function.update_of_ne hax, Function.update_of_ne hbx]
          exact hm₁ ha hb hab
      · push Not at hA
        obtain ⟨x, ⟨hxR, hx⟩, hmin⟩ := Set.exists_min_image _ id hfin hne
        refine ⟨x, ⟨hxR, hx⟩, fun a ha b hb hab => ?_⟩
        by_cases hax : a = x <;> by_cases hbx : b = x
        · subst hax; subst hbx; exact absurd hab (lt_irrefl _)
        · subst hax
          simp only [Function.update_self, Function.update_of_ne hbx]
          exact lt_of_lt_of_le (hm₂ hxR hb hab) (hA b hb)
        · subst hbx
          simp only [Function.update_self, Function.update_of_ne hax]
          have : ψ₁ a = ψ₂ a := by
            by_contra h; exact absurd (hmin a ⟨ha, h⟩) (not_le.2 hab)
          rw [this]; exact hm₂ ha hxR hab
        · simp only [Function.update_of_ne hax, Function.update_of_ne hbx]
          exact hm₁ ha hb hab
    have hI' : Function.update ψ₁ x (ψ₂ x) '' R ⊆ I := by
      rintro _ ⟨y, hy, rfl⟩
      by_cases hyx : y = x
      · subst hyx; simp only [Function.update_self]; exact hI₂ ⟨y, hy, rfl⟩
      · rw [Function.update_of_ne hyx]; exact hI₁ ⟨y, hy, rfl⟩
    refine htrans _ _ _ (hstep ψ₁ _ hm₁ hgood hI₁ hI' x fun y _ hyx => ?_) (ih _ ?_ hgood hI')
    · rw [Function.update_of_ne hyx]
    · have : {y ∈ R | Function.update ψ₁ x (ψ₂ x) y ≠ ψ₂ y} = {x ∈ R | ψ₁ x ≠ ψ₂ x} \ {x} := by
        ext y
        by_cases hyx : y = x
        · subst hyx; simp
        · simp [hyx]
      rw [this, Set.ncard_sdiff_singleton_of_mem hxD, hn]; rfl

variable {k : ℕ} [LinearOrder (FG k)]

/-- The standing assumptions of Section 5.4. -/
structure Setup (A : IDAlg) (Δ t : ℕ) (I : Finset ℕ) : Prop where
  solves : A.Solves Δ
  time : A.HasRunTime t
  t_pos : 0 < t
  deg : 2 * k ≤ Δ
  homog : Homog (k := k) A t I
  leftInv : ∀ g x y : FG k, x < y → g * x < g * y

theorem strictMonoOn_translate (hlo : ∀ g x y : FG k, x < y → g * x < g * y) {R : Set (FG k)}
    {ψ : FG k → ℕ} (hψ : StrictMonoOn ψ R) (w : FG k) :
    StrictMonoOn (fun x => ψ (w * x)) (w⁻¹ • R) := by
  intro a ha b hb hab
  rw [Set.mem_inv_smul_set_iff, smul_eq_mul] at ha hb
  exact hψ ha hb (hlo w a b hab)

/-- The shape of `U` at `w`: the radius-`t` ball of `U` re-rooted at `w`. -/
noncomputable def shape (U : Set (FG k)) (w : FG k) (t : ℕ) : Finset (FG k) :=
  ((ballF_finite (k := k) t).subset (Set.inter_subset_right (s := w⁻¹ • U))).toFinset

omit [LinearOrder (FG k)] in
@[simp] theorem coe_shape (U : Set (FG k)) (w : FG k) (t : ℕ) :
    (shape U w t : Set (FG k)) = w⁻¹ • U ∩ ballF k t := by
  simp [shape]

omit [LinearOrder (FG k)] in
theorem mem_shape {U : Set (FG k)} {w x : FG k} {t : ℕ} :
    x ∈ shape U w t ↔ w * x ∈ U ∧ norm x ≤ t := by
  rw [← Finset.mem_coe, coe_shape, Set.mem_inter_iff, Set.mem_inv_smul_set_iff, smul_eq_mul,
    mem_ballF]

namespace Setup

variable {A : IDAlg} {Δ t : ℕ} {I : Finset ℕ} (hS : Setup (k := k) A Δ t I)
include hS

/-- Every labelled finite piece of `F_k` is a legal input, so `A` solves it. -/
theorem isMaxFM {R : Set (FG k)} (hR : R.Finite) {ψ : FG k → ℕ} (hψ : Set.InjOn ψ R) :
    IsMaxFMGraph (idGraph R ψ) (A (idGraph R ψ)) :=
  hS.solves _ (edgeSet_idGraph_finite hR) fun v =>
    (ncard_neighborSet_idGraph_le hψ v).trans hS.deg

/-- The saturation indicator at `ψ w` is the colour of the shape at `w`. -/
theorem sat_iff {U : Set (FG k)} {Rr : ℕ} {ψ : FG k → ℕ} (hψ : StrictMonoOn ψ (U ∩ ballF k Rr))
    {w : FG k} (hw : w ∈ U) (hwr : norm w + t ≤ Rr) :
    Sat A (idGraph (U ∩ ballF k Rr) ψ) (ψ w) ↔
      satColour A (shape U w t) ((shape U w t).image fun x => ψ (w * x)) = true := by
  have hsub : U ∩ w • ballF k t ⊆ U ∩ ballF k Rr := by
    rintro x ⟨hxU, hx⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mem_ballF] at hx
    refine ⟨hxU, ?_⟩
    have := norm_mul_le' w (w⁻¹ * x)
    rw [mul_inv_cancel_left] at this
    rw [mem_ballF]; omega
  have hloc : ∀ x ∈ U ∩ ballF k Rr, norm (w⁻¹ * x) ≤ t → x ∈ U ∩ w • ballF k t := by
    rintro x ⟨hxU, -⟩ hx
    exact ⟨hxU, by rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mem_ballF]; exact hx⟩
  have hwR : w ∈ U ∩ w • ballF k t :=
    ⟨hw, by rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, inv_mul_cancel, mem_ballF]; simp⟩
  have hag := gAgree_idGraph_of_subset hsub hψ.injOn hwR hloc
  rw [sat_congr hS.time hS.t_pos hag]
  have hset : U ∩ w • ballF k t = w • (shape U w t : Set (FG k)) := by
    rw [coe_shape, Set.smul_set_inter, smul_inv_smul]
  have hmono : StrictMonoOn (fun x => ψ (w * x)) (shape U w t : Set (FG k)) := by
    refine (strictMonoOn_translate hS.leftInv hψ w).mono ?_
    intro x hx
    rw [coe_shape] at hx
    rw [Set.mem_inv_smul_set_iff, smul_eq_mul]
    apply hsub
    obtain ⟨hx1, hx2⟩ := hx
    rw [Set.mem_inv_smul_set_iff, smul_eq_mul] at hx1
    exact ⟨hx1, by rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, inv_mul_cancel_left]; exact hx2⟩
  rw [hset, ← idGraph_translate]
  have h1 : (1 : FG k) ∈ shape U w t := by rw [mem_shape]; simpa using hw
  have hcongr := idGraph_congr (R := (shape U w t : Set (FG k)))
    (fun x hx => (labelOf_eq hmono hx).symm)
  rw [hcongr]
  have hw1 : ψ w = labelOf (shape U w t) ((shape U w t).image fun x => ψ (w * x)) 1 := by
    rw [labelOf_eq hmono h1, mul_one]
  rw [hw1]
  simp [satColour]

/-- **Lemma 6.** In a loopy PO-view labelled order-preservingly by identifiers from `I`, `A`
saturates every node `w` with `|w| + 1 + t ≤ Rr`. -/
theorem sat_of_loopy {U : Set (FG k)} (hU : IsLoopyF U) {Rr : ℕ} {ψ : FG k → ℕ}
    (hψ : StrictMonoOn ψ (U ∩ ballF k Rr)) (hI : ψ '' (U ∩ ballF k Rr) ⊆ I) {w : FG k}
    (hw : w ∈ U) (hwr : norm w + 1 + t ≤ Rr) :
    Sat A (idGraph (U ∩ ballF k Rr) ψ) (ψ w) := by
  obtain ⟨l, hl, hle⟩ := hU w hw
  have hshape : shape U (w * ltr l) t = shape U w t := by
    ext x; rw [← Finset.mem_coe, ← Finset.mem_coe, coe_shape, coe_shape, hle]
  have hnl : norm (w * ltr l) ≤ norm w + 1 := norm_mul_ltr_le w l
  obtain ⟨b, hb⟩ := hS.homog (shape U w t) (by rw [coe_shape]; exact Set.inter_subset_right)
  -- the colour seen from a node `u` with the same shape
  have key : ∀ u ∈ U, norm u + t ≤ Rr → shape U u t = shape U w t →
      (Sat A (idGraph (U ∩ ballF k Rr) ψ) (ψ u) ↔ b = true) := by
    intro u hu hur hsh
    rw [sat_iff hS hψ hu hur, hsh]
    have hsubR : ∀ x ∈ shape U w t, u * x ∈ U ∩ ballF k Rr := by
      intro x hx
      rw [← hsh, mem_shape] at hx
      refine ⟨hx.1, ?_⟩
      have := norm_mul_le' u x
      rw [mem_ballF]; omega
    rw [hb]
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact hI ⟨u * x, hsubR x hx, rfl⟩
    · apply Finset.card_image_of_injOn
      intro x hx y hy hxy
      exact mul_left_cancel (hψ.injOn (hsubR x hx) (hsubR y hy) hxy)
  have hwR : w ∈ U ∩ ballF k Rr := ⟨hw, by rw [mem_ballF]; omega⟩
  have hwlR : w * ltr l ∈ U ∩ ballF k Rr := ⟨hl, by rw [mem_ballF]; omega⟩
  have hadj : (idGraph (U ∩ ballF k Rr) ψ).Adj (ψ w) (ψ (w * ltr l)) :=
    (idGraph_adj_iff hψ.injOn hwR _).2 ⟨l, hwlR, rfl⟩
  have hR : (U ∩ ballF k Rr).Finite := (ballF_finite Rr).subset Set.inter_subset_right
  have hmax := (hS.isMaxFM hR hψ.injOn).maximal _ _ hadj
  have hb' : b = true := by
    rcases hmax with h | h
    · exact (key w hw (by omega) rfl).1 h
    · exact (key _ hl (by omega) hshape).1 h
  exact (key w hw (by omega) rfl).2 hb'

/-! ### Lemma 7 -/

/-- The radius of the labelled piece of the PO-view used in Lemma 7. -/
def rad (t : ℕ) : ℕ := 2 * t + 2

omit hS [LinearOrder (FG k)] in
theorem finite_piece (U : Set (FG k)) (R : ℕ) : (U ∩ ballF k R).Finite :=
  (ballF_finite R).subset Set.inter_subset_right

/-- Consistency of edge weights (from `IsMaxFMGraph.symm`). -/
theorem out_symm {R : Set (FG k)} (hR : R.Finite) {ψ : FG k → ℕ} (hψ : Set.InjOn ψ R)
    {w : FG k} (hw : w ∈ R) {l : Fin k × Bool} (hwl : w * ltr l ∈ R) :
    A (idGraph R ψ) (ψ w) (ψ (w * ltr l)) =
      A (idGraph R ψ) (ψ (w * ltr l)) (ψ (w * ltr l * ltr (linv l))) := by
  rw [mul_ltr_mul_ltr_linv]
  exact (hS.isMaxFM hR hψ).symm _ _ ((idGraph_adj_iff hψ hw _).2 ⟨l, hwl, rfl⟩)

open Classical in
/-- Saturation as a sum over letters (Lemma 6 for nodes at distance `≤ t + 1`). -/
theorem out_sum {U : Set (FG k)} (hU : IsLoopyF U) {ψ : FG k → ℕ}
    (hψ : StrictMonoOn ψ (U ∩ ballF k (rad t))) (hI : ψ '' (U ∩ ballF k (rad t)) ⊆ I)
    {w : FG k} (hw : w ∈ U) (hn : norm w ≤ t + 1) :
    ∑ l ∈ Finset.univ.filter (fun l => w * ltr l ∈ U ∩ ballF k (rad t)),
      A (idGraph (U ∩ ballF k (rad t)) ψ) (ψ w) (ψ (w * ltr l)) = 1 := by
  have h := hS.sat_of_loopy hU hψ hI hw (by unfold rad; omega)
  unfold Sat at h
  have hwR : w ∈ U ∩ ballF k (rad t) := ⟨hw, by rw [mem_ballF]; unfold rad; omega⟩
  rw [finsum_neighborSet_idGraph hψ.injOn hwR] at h
  convert h

/-- Locality: away from the changed node `v`, outputs coincide. -/
theorem out_eq_of_far {R : Set (FG k)} {ψ₁ ψ₂ : FG k → ℕ}
    (hψ₁ : Set.InjOn ψ₁ R) (hψ₂ : Set.InjOn ψ₂ R) {v : FG k}
    (hv : ∀ x ∈ R, x ≠ v → ψ₁ x = ψ₂ x) {w : FG k} (hw : w ∈ R) (hfar : t < norm (w⁻¹ * v))
    {l : Fin k × Bool} (hwl : w * ltr l ∈ R) :
    A (idGraph R ψ₁) (ψ₁ w) (ψ₁ (w * ltr l)) = A (idGraph R ψ₂) (ψ₂ w) (ψ₂ (w * ltr l)) := by
  have ht := hS.t_pos
  have hne : ∀ x, norm (w⁻¹ * x) ≤ t → x ≠ v := by
    rintro x hx rfl; omega
  set R₀ := R ∩ w • ballF k t
  have hsub : R₀ ⊆ R := Set.inter_subset_left
  have hwR₀ : w ∈ R₀ :=
    ⟨hw, by rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, inv_mul_cancel, mem_ballF]; simp⟩
  have hloc : ∀ x ∈ R, norm (w⁻¹ * x) ≤ t → x ∈ R₀ := fun x hx h =>
    ⟨hx, by rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mem_ballF]; exact h⟩
  have h₁ := gAgree_idGraph_of_subset hsub hψ₁ hwR₀ hloc
  have h₂ := gAgree_idGraph_of_subset hsub hψ₂ hwR₀ hloc
  have hc : idGraph R₀ ψ₁ = idGraph R₀ ψ₂ := idGraph_congr fun x hx => by
    refine hv x hx.1 (hne x ?_)
    have := hx.2
    rwa [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mem_ballF] at this
  have hw12 : ψ₁ w = ψ₂ w := hv w hw (hne w (by simp))
  have h₂' : Cslib.Local.GAgree (idGraph R ψ₂) (idGraph R₀ ψ₂) (ψ₁ w) t := by
    rw [hw12]; exact h₂
  have hag : Cslib.Local.GAgree (idGraph R ψ₁) (idGraph R ψ₂) (ψ₁ w) t :=
    (hc ▸ h₁).trans h₂'.symm
  rw [hS.time _ _ _ hag, hw12,
    hv _ hwl (hne _ (by rw [inv_mul_cancel_left, norm_ltr]; omega))]

/-- **Lemma 7**, one node changed: if two order-preserving `I`-labellings of the radius-`(2t+2)`
ball of a loopy PO-view differ only at one node, the outputs of the root coincide. -/
theorem out_eq_of_single {U : Set (FG k)} (hU : IsLoopyF U) (h1 : (1 : FG k) ∈ U)
    {ψ₁ ψ₂ : FG k → ℕ} (hm₁ : StrictMonoOn ψ₁ (U ∩ ballF k (rad t)))
    (hm₂ : StrictMonoOn ψ₂ (U ∩ ballF k (rad t))) (hI₁ : ψ₁ '' (U ∩ ballF k (rad t)) ⊆ I)
    (hI₂ : ψ₂ '' (U ∩ ballF k (rad t)) ⊆ I) (v : FG k)
    (hv : ∀ x ∈ U ∩ ballF k (rad t), x ≠ v → ψ₁ x = ψ₂ x) (l : Fin k × Bool) (hl : ltr l ∈ U) :
    A (idGraph (U ∩ ballF k (rad t)) ψ₁) (ψ₁ 1) (ψ₁ (ltr l)) =
      A (idGraph (U ∩ ballF k (rad t)) ψ₂) (ψ₂ 1) (ψ₂ (ltr l)) := by
  classical
  set R := U ∩ ballF k (rad t) with hRdef
  have hR : R.Finite := finite_piece U _
  have ht := hS.t_pos
  -- the outputs `y₁`, `y₂` and the disagreement relation
  set y₁ : FG k → (Fin k × Bool) → ℝ := fun w l => A (idGraph R ψ₁) (ψ₁ w) (ψ₁ (w * ltr l))
  set y₂ : FG k → (Fin k × Bool) → ℝ := fun w l => A (idGraph R ψ₂) (ψ₂ w) (ψ₂ (w * ltr l))
  have memR : ∀ {w}, w ∈ U → norm w ≤ rad t → w ∈ R := fun hw hn => ⟨hw, hn⟩
  have symm₁ : ∀ {w l}, w ∈ R → w * ltr l ∈ R → y₁ w l = y₁ (w * ltr l) (linv l) :=
    fun hw hwl => hS.out_symm hR hm₁.injOn hw hwl
  have symm₂ : ∀ {w l}, w ∈ R → w * ltr l ∈ R → y₂ w l = y₂ (w * ltr l) (linv l) :=
    fun hw hwl => hS.out_symm hR hm₂.injOn hw hwl
  by_contra hne
  have hne' : y₁ 1 l ≠ y₂ 1 l := by simpa [y₁, y₂] using hne
  have h1R : (1 : FG k) * ltr l ∈ R := memR (by simpa using hl) (by simp [rad])
  -- the changed node is close to the root
  by_cases hvt : t < norm v
  · exact hne' (hS.out_eq_of_far hm₁.injOn hm₂.injOn hv (memR h1 (by simp)) (by simpa using hvt)
      h1R)
  push Not at hvt
  set D : FG k → (Fin k × Bool) → Prop := fun w l => w * ltr l ∈ R ∧ y₁ w l ≠ y₂ w l
  set W : Set (FG k) := {w | w ∈ U ∧ norm w ≤ t + 1 ∧ w ≠ 1 ∧
    FreeGroup.norm (v⁻¹ * w) = FreeGroup.norm v⁻¹ + norm w ∧ ∃ p, FreeGroup.norm (w * ltr p) < norm w ∧ D w p}
  have hWfin : W.Finite := (ballF_finite (t + 1)).subset fun w hw => hw.2.1
  -- `W` is nonempty: a disagreement at the root not towards `v`
  have hWne : W.Nonempty := by
    have s₁ := hS.out_sum hU hm₁ hI₁ h1 (by simp)
    have s₂ := hS.out_sum hU hm₂ hI₂ h1 (by simp)
    obtain ⟨l', hl', hl'l, hne''⟩ := exists_ne_of_sum_eq _ (y₁ 1) (y₂ 1) s₁ s₂
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1R⟩) hne'
    have hl'R : (1 : FG k) * ltr l' ∈ R := (Finset.mem_filter.1 hl').2
    obtain ⟨m, hmR, hm, hmD⟩ : ∃ m, (1 : FG k) * ltr m ∈ R ∧ ¬ FreeGroup.norm (v⁻¹ * ltr m) < FreeGroup.norm v⁻¹ ∧
        y₁ 1 m ≠ y₂ 1 m := by
      by_cases h : FreeGroup.norm (v⁻¹ * ltr l) < FreeGroup.norm v⁻¹
      · refine ⟨l', hl'R, fun h' => hl'l (eq_of_norm_mul_ltr_lt h' h), hne''⟩
      · exact ⟨l, h1R, h, hne'⟩
    have hmU : ltr m ∈ U := by simpa using hmR.1
    refine ⟨ltr m, hmU, by simp, ltr_ne_one m, by rw [norm_mul_ltr_of_not_lt hm, norm_ltr], linv m,
      by simp, ?_, ?_⟩
    · simpa using memR h1 (by simp)
    · have e₁ := symm₁ (memR h1 (by simp)) hmR
      have e₂ := symm₂ (memR h1 (by simp)) hmR
      simp only [one_mul] at e₁ e₂
      rw [← e₁, ← e₂]; exact hmD
  obtain ⟨w₀, hw₀W, hmax⟩ := Set.exists_max_image W FreeGroup.norm hWfin hWne
  obtain ⟨hw₀U, hw₀n, hw₀1, hsh, p, hp, hpR, hpD⟩ := hw₀W
  have hw₀R : w₀ ∈ R := memR hw₀U (by unfold rad; omega)
  have hdist : FreeGroup.norm (w₀⁻¹ * v) = norm v + norm w₀ := by
    rw [← FreeGroup.norm_inv_eq, mul_inv_rev, inv_inv, hsh, FreeGroup.norm_inv_eq]
  by_cases hfar : t < FreeGroup.norm (w₀⁻¹ * v)
  · exact hpD (hS.out_eq_of_far hm₁.injOn hm₂.injOn hv hw₀R hfar hpR)
  push Not at hfar
  have hw₀t : norm w₀ ≤ t := by omega
  have s₁ := hS.out_sum hU hm₁ hI₁ hw₀U (by omega)
  have s₂ := hS.out_sum hU hm₂ hI₂ hw₀U (by omega)
  obtain ⟨l₁, hl₁, hl₁p, hl₁D⟩ := exists_ne_of_sum_eq _ (y₁ w₀) (y₂ w₀) s₁ s₂
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hpR⟩) hpD
  have hl₁R : w₀ * ltr l₁ ∈ R := (Finset.mem_filter.1 hl₁).2
  have hgrow : ¬ FreeGroup.norm (w₀ * ltr l₁) < norm w₀ := fun h => hl₁p (eq_of_norm_mul_ltr_lt h hp)
  have hn₁ := norm_mul_ltr_of_not_lt hgrow
  have hw₁W : w₀ * ltr l₁ ∈ W := by
    refine ⟨hl₁R.1, by omega, ?_, norm_mul_mul_ltr_eq hsh hw₀1 hgrow, linv l₁, ?_, ?_, ?_⟩
    · intro h; rw [h] at hn₁; simp at hn₁
    · rw [mul_ltr_mul_ltr_linv]; omega
    · rw [mul_ltr_mul_ltr_linv]; exact hw₀R
    · rw [← symm₁ hw₀R hl₁R, ← symm₂ hw₀R hl₁R]; exact hl₁D
  have := hmax _ hw₁W
  omega

/-- **Lemma 7.** The output of the root of a loopy PO-view is the same for all order-preserving
labellings of its radius-`(2t+2)` ball by identifiers from `I`. -/
theorem out_eq {U : Set (FG k)} (hU : IsLoopyF U) (h1 : (1 : FG k) ∈ U)
    {ψ₁ ψ₂ : FG k → ℕ} (hm₁ : StrictMonoOn ψ₁ (U ∩ ballF k (rad t)))
    (hm₂ : StrictMonoOn ψ₂ (U ∩ ballF k (rad t))) (hI₁ : ψ₁ '' (U ∩ ballF k (rad t)) ⊆ I)
    (hI₂ : ψ₂ '' (U ∩ ballF k (rad t)) ⊆ I) (l : Fin k × Bool) (hl : ltr l ∈ U) :
    A (idGraph (U ∩ ballF k (rad t)) ψ₁) (ψ₁ 1) (ψ₁ (ltr l)) =
      A (idGraph (U ∩ ballF k (rad t)) ψ₂) (ψ₂ 1) (ψ₂ (ltr l)) := by
  refine chain_induction (U ∩ ballF k (rad t)) (finite_piece U _) (I : Set ℕ)
    (fun ψ₁ ψ₂ => ∀ l, ltr l ∈ U →
      A (idGraph (U ∩ ballF k (rad t)) ψ₁) (ψ₁ 1) (ψ₁ (ltr l)) =
        A (idGraph (U ∩ ballF k (rad t)) ψ₂) (ψ₂ 1) (ψ₂ (ltr l)))
    (fun _ _ _ h₁ h₂ l hl => (h₁ l hl).trans (h₂ l hl))
    (fun ψ₁ ψ₂ hm₁ hm₂ hI₁ hI₂ v hv => hS.out_eq_of_single hU h1 hm₁ hm₂ hI₁ hI₂ v hv) 1
    ψ₁ ψ₂ hm₁ hm₂ hI₁ hI₂ l hl

end Setup

end Podc.LinearInDeltaLB
