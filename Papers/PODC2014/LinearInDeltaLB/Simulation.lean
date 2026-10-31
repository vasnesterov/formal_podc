import Papers.PODC2014.LinearInDeltaLB.OrderInvariance

/-!
# The simulations EC ⇝ PO ⇝ OI ⇝ ID (Sections 5.1, 5.3, 5.4, 5.5)

From a `t`-time ID-algorithm `A` (under `Setup`) and an order-preserving labelling `Ψ` of a large
ball of `F_k` by identifiers from the homogeneous set `I`, we build the EC-algorithm `simEC A Ψ t`:
the root of an EC-view `V` turns `V` into its PO-view (Section 5.1), orders it by the
left-invariant order of `F_k` (Section 5.3, simulation (4)), labels its radius-`t` ball by `Ψ`,
runs `A`, and returns, for each colour `c`, the sum of the weights of the two directed edges of
colour `c` (Section 5.1).

* `simEC_hasRunTime`: `simEC A Ψ t` has run-time `t`.
* `simEC_solvesLoopy` (Corollary 9 + Section 5.5): it finds a maximal fractional matching on every
  loopy EC-graph. Proof: run `A` on a big labelled ball of the PO-view; by Lemma 7 its outputs near
  the root are the outputs of `simEC`; correctness of `A` on that finite graph gives the
  constraints.
-/

namespace Podc.LinearInDeltaLB

open FreeGroup Pointwise Cslib.ColourSystem

variable {k : ℕ}

/-- The output of the PO-algorithm (the ID-algorithm run on the `Ψ`-labelled radius-`t` ball of
the PO-view `U`) on the edge of the root labelled by the letter `l`. -/
noncomputable def poOut (A : IDAlg) (Ψ : FG k → ℕ) (t : ℕ) (U : Set (FG k))
    (l : Fin k × Bool) : ℝ :=
  A (idGraph (U ∩ ballF k t) Ψ) (Ψ 1) (Ψ (ltr l))

/-- The simulated EC-algorithm. -/
noncomputable def simEC (A : IDAlg) (Ψ : FG k → ℕ) (t : ℕ) : ECAlg k := fun V c =>
  poOut A Ψ t (cover (tGraph V fun _ => ∅) 1) (c, true) +
    poOut A Ψ t (cover (tGraph V fun _ => ∅) 1) (c, false)

/-- `simEC A Ψ t` has run-time `t` (in the EC sense). -/
theorem simEC_hasRunTime (A : IDAlg) (Ψ : FG k → ℕ) (t : ℕ) : (simEC A Ψ t).HasRunTime t := by
  intro U V h
  funext c
  simp only [simEC, poOut, cover_inter_ballF h]

theorem simEC_view {α : Type*} (G : ColouredGraph k α) (A : IDAlg) (Ψ : FG k → ℕ) (t : ℕ) (a : α)
    (c : Fin k) :
    simEC A Ψ t (G.view a) c = poOut A Ψ t (cover G a) (c, true) + poOut A Ψ t (cover G a) (c, false) := by
  simp only [simEC, cover_tGraph_view]

theorem sum_letters {s : Finset (Fin k)} (f : Fin k × Bool → ℝ) :
    ∑ l ∈ Finset.univ.filter (fun l : Fin k × Bool => l.1 ∈ s), f l =
      ∑ c ∈ s, (f (c, true) + f (c, false)) := by
  have : Finset.univ.filter (fun l : Fin k × Bool => l.1 ∈ s) = s ×ˢ Finset.univ := by
    ext l; simp
  rw [this, Finset.sum_product]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_bool]

namespace Setup

variable [LinearOrder (FG k)] {A : IDAlg} {Δ t : ℕ} {I : Finset ℕ} (hS : Setup (k := k) A Δ t I)
include hS

/-- The radius of the big labelled ball used in the proof of correctness. -/
def bigRad (t : ℕ) : ℕ := rad t + t + 1

variable {Ψ : FG k → ℕ} (hΨ : StrictMonoOn Ψ (ballF k (bigRad t)))
  (hΨI : Ψ '' ballF k (bigRad t) ⊆ I)
include hΨ hΨI

/-- The key identification: in the big labelled ball of the PO-view of `a`, the output of node `w`
(near the root) on its edge `l` is the PO-output of the PO-view of the endpoint `b` of `w`. -/
theorem big_out {α : Type*} {G : ColouredGraph k α} (hG : IsLoopy G) (a : α) {w : FG k} {b : α}
    (hwb : poWalk G a w = some b) (hw : norm w ≤ t + 1) {l : Fin k × Bool}
    (hl : w * ltr l ∈ cover G a) :
    A (idGraph (cover G a ∩ ballF k (bigRad t)) Ψ) (Ψ w) (Ψ (w * ltr l)) =
      poOut A Ψ t (cover G b) l := by
  set U := cover G a
  have hU' : w⁻¹ • U = cover G b := inv_smul_cover G hwb
  have hwU : w ∈ U := (mem_cover G).2 ⟨b, hwb⟩
  -- step 1: restrict to the ball of radius `rad t` around `w`
  have hsub : U ∩ w • ballF k (rad t) ⊆ U ∩ ballF k (bigRad t) := by
    rintro x ⟨hxU, hx⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mem_ballF] at hx
    refine ⟨hxU, ?_⟩
    have := norm_mul_le' w (w⁻¹ * x)
    rw [mul_inv_cancel_left] at this
    rw [mem_ballF]; unfold bigRad; omega
  have hinj : Set.InjOn Ψ (U ∩ ballF k (bigRad t)) := (hΨ.mono Set.inter_subset_right).injOn
  have hwmem : w ∈ U ∩ w • ballF k (rad t) := by
    refine ⟨hwU, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, inv_mul_cancel, mem_ballF,
      FreeGroup.norm_one]
    omega
  have hloc : ∀ x ∈ U ∩ ballF k (bigRad t), norm (w⁻¹ * x) ≤ t →
      x ∈ U ∩ w • ballF k (rad t) := by
    rintro x ⟨hxU, -⟩ hx
    refine ⟨hxU, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mem_ballF]
    unfold rad; omega
  have hag := gAgree_idGraph_of_subset (t := t) hsub hinj hwmem hloc
  rw [hS.time _ _ _ hag]
  -- step 2: translate
  have hset : U ∩ w • ballF k (rad t) = w • (w⁻¹ • U ∩ ballF k (rad t)) := by
    rw [Set.smul_set_inter, smul_inv_smul]
  rw [hset, ← idGraph_translate, hU']
  -- step 3: Lemma 7
  have hmem : ∀ x ∈ cover G b ∩ ballF k (rad t), w * x ∈ ballF k (bigRad t) := by
    rintro x ⟨-, hx⟩
    have := norm_mul_le' w x
    rw [mem_ballF] at hx ⊢; unfold bigRad; omega
  have hloopy := isLoopyF_cover G hG b
  have h1 := one_mem_cover G b
  have hlb : ltr l ∈ cover G b := by
    rw [← hU', Set.mem_inv_smul_set_iff, smul_eq_mul]; exact hl
  have hm₁ : StrictMonoOn (fun x => Ψ (w * x)) (cover G b ∩ ballF k (rad t)) :=
    fun x hx y hy hxy => hΨ (hmem x hx) (hmem y hy) (hS.leftInv w x y hxy)
  have hm₂ : StrictMonoOn Ψ (cover G b ∩ ballF k (rad t)) := hΨ.mono fun x ⟨_, hx⟩ => by
    rw [mem_ballF] at hx ⊢; unfold bigRad; omega
  have hI₁ : (fun x => Ψ (w * x)) '' (cover G b ∩ ballF k (rad t)) ⊆ I := by
    rintro _ ⟨x, hx, rfl⟩; exact hΨI ⟨_, hmem x hx, rfl⟩
  have hI₂ : Ψ '' (cover G b ∩ ballF k (rad t)) ⊆ I := by
    rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
    exact hΨI ⟨x, by rw [mem_ballF] at hx ⊢; unfold bigRad; omega, rfl⟩
  have h7 := hS.out_eq hloopy h1 hm₁ hm₂ hI₁ hI₂ l hlb
  simp only [mul_one] at h7
  rw [h7]
  -- step 4: restrict to the radius-`t` ball
  unfold poOut
  have hsub' : cover G b ∩ ballF k t ⊆ cover G b ∩ ballF k (rad t) := fun x ⟨h1, h2⟩ =>
    ⟨h1, by rw [mem_ballF] at h2 ⊢; unfold rad; omega⟩
  have hag' := gAgree_idGraph_of_subset (t := t) hsub' hm₂.injOn (w := 1) ⟨h1, by simp [mem_ballF]⟩
    (fun x ⟨hx, _⟩ hxt => ⟨hx, by simpa [mem_ballF] using hxt⟩)
  rw [hS.time _ _ _ hag']

open Classical in
/-- Loads in the EC-graph are loads of the big labelled ball. -/
theorem load_eq {α : Type*} {G : ColouredGraph k α} (hG : IsLoopy G) (a : α) {w : FG k} {b : α}
    (hwb : poWalk G a w = some b) (hw : norm w ≤ t + 1) :
    load G (fun x => simEC A Ψ t (G.view x)) b =
      ∑ᶠ u ∈ (idGraph (cover G a ∩ ballF k (bigRad t)) Ψ).neighborSet (Ψ w),
        A (idGraph (cover G a ∩ ballF k (bigRad t)) Ψ) (Ψ w) u := by
  have hinj : Set.InjOn Ψ (cover G a ∩ ballF k (bigRad t)) :=
    (hΨ.mono Set.inter_subset_right).injOn
  have hwR : w ∈ cover G a ∩ ballF k (bigRad t) :=
    ⟨(mem_cover G).2 ⟨b, hwb⟩, by rw [mem_ballF]; unfold bigRad rad; omega⟩
  rw [finsum_neighborSet_idGraph hinj hwR]
  have hfilt : ∀ l ∈ (Finset.univ : Finset (Fin k × Bool)),
      w * ltr l ∈ cover G a ∩ ballF k (bigRad t) ↔
        l.1 ∈ Finset.univ.filter (fun c => (G.step b c).isSome) := by
    intro l _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
      mul_ltr_mem_cover G hwb, mem_ballF]
    constructor
    · exact fun h => h.1
    · intro h; refine ⟨h, ?_⟩
      have := norm_mul_ltr_le w l; unfold bigRad rad; omega
  symm
  refine (Finset.sum_congr (s₂ := Finset.univ.filter (fun l : Fin k × Bool =>
    l.1 ∈ Finset.univ.filter (fun c => (G.step b c).isSome))) ?_ (fun _ _ => rfl)).trans ?_
  · ext l; simpa using hfilt l (Finset.mem_univ _)
  rw [sum_letters]
  unfold load
  symm
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Finset.mem_filter] at hc
  show simEC A Ψ t (G.view b) c = _
  rw [simEC_view]
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 hc.2
  have h1 : w * ltr (c, true) ∈ cover G a := by rw [mul_ltr_mem_cover G hwb]; exact hc.2
  have h2 : w * ltr (c, false) ∈ cover G a := by rw [mul_ltr_mem_cover G hwb]; exact hc.2
  rw [hS.big_out hΨ hΨI hG a hwb hw h1, hS.big_out hΨ hΨI hG a hwb hw h2]

/-- **Corollary 9 / Section 5.5.** The simulated EC-algorithm finds a maximal fractional matching
on every loopy EC-graph. -/
theorem simEC_isMaxFM {α : Type*} {G : ColouredGraph k α} (hG : IsLoopy G) :
    IsMaxFM G (fun x => simEC A Ψ t (G.view x)) := by
  -- the big labelled ball of the PO-view of `a`
  have big : ∀ a : α, IsMaxFMGraph (idGraph (cover G a ∩ ballF k (bigRad t)) Ψ)
      (A (idGraph (cover G a ∩ ballF k (bigRad t)) Ψ)) := fun a =>
    hS.isMaxFM ((ballF_finite _).subset Set.inter_subset_right)
      (hΨ.mono Set.inter_subset_right).injOn
  have adj : ∀ a : α, ∀ l, ltr l ∈ cover G a →
      (idGraph (cover G a ∩ ballF k (bigRad t)) Ψ).Adj (Ψ 1) (Ψ (ltr l)) := by
    intro a l hl
    have hinj : Set.InjOn Ψ (cover G a ∩ ballF k (bigRad t)) :=
      (hΨ.mono Set.inter_subset_right).injOn
    have := (idGraph_adj_iff hinj (w := 1) ⟨one_mem_cover G a, by simp [mem_ballF]⟩ (Ψ (ltr l))).2
      ⟨l, ⟨by simpa using hl, by rw [one_mul, mem_ballF, norm_ltr]; unfold bigRad; omega⟩,
        by simp⟩
    exact this
  have mem : ∀ a : α, ∀ l, (G.step a l.1).isSome → ltr l ∈ cover G a := fun a l h =>
    (mem_cover G).2 (by rw [poWalk_ltr]; exact Option.isSome_iff_exists.1 h)
  -- PO-outputs at the root are outputs of the big ball
  have root : ∀ a : α, ∀ l, ltr l ∈ cover G a →
      poOut A Ψ t (cover G a) l =
        A (idGraph (cover G a ∩ ballF k (bigRad t)) Ψ) (Ψ 1) (Ψ (ltr l)) := by
    intro a l hl
    have := hS.big_out hΨ hΨI hG a (poWalk_one G a) (by simp) (l := l) (by simpa using hl)
    simpa using this.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- consistency
    intro a b' c hab
    rw [simEC_view, simEC_view]
    have hwp : poWalk G a (ltr (c, true)) = some b' := by simpa using hab
    have hwm : poWalk G a (ltr (c, false)) = some b' := by simpa using hab
    have hs : (G.step a c).isSome := by rw [hab]; rfl
    have e₁ := hS.big_out hΨ hΨI hG a hwp (by simp) (l := (c, false)) (by
      rw [show ltr (c, true) * ltr (c, false) = 1 from ltr_mul_ltr_linv (c, true)]
      exact one_mem_cover G a)
    have e₂ := hS.big_out hΨ hΨI hG a hwm (by simp) (l := (c, true)) (by
      rw [show ltr (c, false) * ltr (c, true) = 1 from ltr_mul_ltr_linv (c, false)]
      exact one_mem_cover G a)
    rw [show ltr (c, true) * ltr (c, false) = 1 from ltr_mul_ltr_linv (c, true)] at e₁
    rw [show ltr (c, false) * ltr (c, true) = 1 from ltr_mul_ltr_linv (c, false)] at e₂
    rw [← e₁, ← e₂, root a _ (mem a (c, true) hs), root a _ (mem a (c, false) hs),
      (big a).symm _ _ (adj a _ (mem a (c, true) hs)),
      (big a).symm _ _ (adj a _ (mem a (c, false) hs))]
    ring
  · -- nonnegativity
    intro a c hc
    rw [simEC_view, root a _ (mem a (c, true) hc), root a _ (mem a (c, false) hc)]
    exact add_nonneg ((big a).nonneg _ _ (adj a _ (mem a (c, true) hc)))
      ((big a).nonneg _ _ (adj a _ (mem a (c, false) hc)))
  · -- load at most one
    intro a
    rw [hS.load_eq hΨ hΨI hG a (poWalk_one G a) (by simp)]
    exact (big a).le_one _
  · -- maximality
    intro a b' c hab
    have hwp : poWalk G a (ltr (c, true)) = some b' := by simpa using hab
    rw [hS.load_eq hΨ hΨI hG a (poWalk_one G a) (by simp),
      hS.load_eq hΨ hΨI hG a hwp (by simp)]
    exact (big a).maximal _ _ (adj a _ (mem a (c, true) (by rw [hab]; rfl)))

end Setup

end Podc.LinearInDeltaLB
