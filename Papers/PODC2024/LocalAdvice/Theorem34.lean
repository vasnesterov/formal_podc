import Papers.PODC2024.LocalAdvice.Decoder

/-!
# Theorem 34: the algorithm `A` outputs a proper 3-colouring

Given the advice of an encoding schema (`Schema.bit`), `decode` outputs the colouring `psi`:
the fixed greedy colouring `φ`, except on small components of `G_{2,3}` (diameter `≤ 4000Δ⁹`), which
get the 2-colouring with colour 2 on their smallest identifier. `psi` is proper.
-/

namespace Podc.LocalAdvice

open SimpleGraph Finset Cslib.Local

noncomputable section

open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V} {φ : V → Fin 3} {Δ : ℕ}

/-- The smallest identifier of the component of `u`. -/
def compMin (H : SimpleGraph V) (u : V) : V :=
  (univ.filter fun z => H.Reachable u z).min' ⟨u, by simp⟩

lemma compMin_reachable (H : SimpleGraph V) (u : V) : H.Reachable u (compMin H u) := by
  have := min'_mem (univ.filter fun z => H.Reachable u z) ⟨u, by simp⟩
  simp only [mem_filter, mem_univ, true_and] at this
  exact this

lemma compMin_eq_of_reachable {H : SimpleGraph V} {u v : V} (h : H.Reachable u v) :
    compMin H u = compMin H v := by
  unfold compMin
  congr 1
  ext z
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

variable (G φ Δ) in
/-- The colouring `ψ` of the proof of Theorem 34. -/
def psi (u : V) : Fin 3 :=
  if φ u = 0 then 0
  else if IsLarge (H23 G φ) (4000 * Δ ^ 9) u then φ u
  else if Even ((H23 G φ).dist u (compMin (H23 G φ) u)) then 1 else 2

omit [Fintype V] [LinearOrder V] in
/-- `SmallAt` (what the algorithm checks) is equivalent to the component having diameter `≤ D`. -/
lemma smallAt_iff_not_isLarge (H : SimpleGraph V) (D : ℕ) (u : V) :
    SmallAt H D u ↔ ¬ IsLarge H D u := by
  constructor
  · rintro ⟨h1, h2⟩ ⟨x, y, hx, hy, hxy⟩
    have hball : ∀ z, H.Reachable u z → H.edist u z ≤ D := by
      intro z hz
      by_contra hfar
      have hd : D + 1 ≤ H.dist u z := by
        by_contra hlt
        exact hfar (hz.edist_le_natCast (by omega))
      obtain ⟨f, -, -, hf⟩ := exists_geodesic_of_le H hz hd
      have := h1 (f (D + 1)) (by rw [hf _ le_rfl])
      rw [hf _ le_rfl] at this
      norm_cast at this
      omega
    have := h2 x y (hball x hx) (hball y hy)
    have := SimpleGraph.dist_le_of_edist_le_natCast this
    omega
  · intro hl
    have hr : ∀ x y, H.Reachable u x → H.Reachable u y → H.dist x y ≤ D := by
      intro x y hx hy
      by_contra h
      exact hl ⟨x, y, hx, hy, by omega⟩
    refine ⟨fun z hz => ?_, fun x y hx hy => ?_⟩
    · have hz' := SimpleGraph.reachable_of_edist_le_natCast hz
      exact hz'.edist_le_natCast (by simpa using hr u z (Reachable.refl u) hz')
    · have hx' := SimpleGraph.reachable_of_edist_le_natCast hx
      have hy' := SimpleGraph.reachable_of_edist_le_natCast hy
      exact (hx'.symm.trans hy').edist_le_natCast (hr x y hx' hy')

omit [Fintype V] [LinearOrder V] in
lemma fin3_ne_zero {c : Fin 3} (h : c ≠ 0) : c = 1 ∨ c = 2 := by
  revert h c; decide

/-- `ψ` is a proper 3-colouring. -/
theorem psi_proper (hφ : IsGreedy G φ) {u v : V} (huv : G.Adj u v) :
    psi G φ Δ u ≠ psi G φ Δ v := by
  have hne := hφ.1 u v huv
  have hnz : ∀ w, φ w ≠ 0 → psi G φ Δ w ≠ 0 := by
    intro w hw
    unfold psi
    simp only [hw, ite_false]
    split_ifs <;> simp [hw]
  by_cases hu : φ u = 0
  · have hv : φ v ≠ 0 := fun h => hne (hu.trans h.symm)
    have : psi G φ Δ u = 0 := by simp [psi, hu]
    rw [this]; exact (hnz v hv).symm
  by_cases hv : φ v = 0
  · have : psi G φ Δ v = 0 := by simp [psi, hv]
    rw [this]; exact hnz u hu
  have hH : (H23 G φ).Adj u v := ⟨huv, hu, hv⟩
  have hlarge : IsLarge (H23 G φ) (4000 * Δ ^ 9) u ↔ IsLarge (H23 G φ) (4000 * Δ ^ 9) v :=
    ⟨fun h => h.of_reachable hH.reachable, fun h => h.of_reachable hH.symm.reachable⟩
  unfold psi
  simp only [hu, hv, ite_false]
  by_cases hL : IsLarge (H23 G φ) (4000 * Δ ^ 9) u
  · simp only [hL, hlarge.1 hL, ite_true]; exact hne
  · simp only [hL, (not_congr hlarge).1 hL, ite_false]
    rw [← compMin_eq_of_reachable hH.reachable]
    have hm := compMin_reachable (H23 G φ) u
    have e1 := even_dist_iff hφ hm hu
    have e2 := even_dist_iff hφ (hH.symm.reachable.trans hm) hv
    have hm0 := H23_reachable_ne_zero hm hu
    generalize compMin (H23 G φ) u = m at *
    by_cases ha : Even ((H23 G φ).dist u m) <;> by_cases hb : Even ((H23 G φ).dist v m) <;>
      simp only [ha, hb, ite_true, ite_false]
    · exact absurd ((e1.1 ha).trans (e2.1 hb).symm) hne
    · decide
    · decide
    · intro _
      have h1 := mt e1.2 ha
      have h2 := mt e2.2 hb
      rcases fin3_ne_zero hu with h3 | h3 <;> rcases fin3_ne_zero hv with h4 | h4 <;>
        rcases fin3_ne_zero hm0 with h5 | h5 <;> simp_all

namespace Schema

variable (σ : Schema G φ Δ)

lemma inW_bit_iff (hφ : IsGreedy G φ) (v : V) : InW G σ.bit v ↔ φ v = 0 := by
  rw [σ.lemma_33 hφ v]
  unfold InW ones
  rfl

lemma hb_bit (hφ : IsGreedy G φ) : Hb G σ.bit = H23 G φ := by
  ext x y
  simp only [Hb, restrict_adj, σ.inW_bit_iff hφ]

/-- Nodes of large components output their colour in `φ`. -/
lemma outLarge_eq (hφ : IsGreedy G φ) (hΔ : 1 ≤ Δ) {u : V} (hu : φ u ≠ 0)
    (hL : IsLarge (H23 G φ) (4000 * Δ ^ 9) u) :
    outLarge Δ (H23 G φ) σ.bit u = φ u := by
  have hc := pow_chain hΔ
  -- a 1-bit within distance `3000Δ⁹`
  obtain ⟨r, hr, hur⟩ := σ.R_dom u hu hL
  have hv := σ.sel_mem r hr
  obtain ⟨hXne, -⟩ := σ.X_spec hr
  obtain ⟨z, hz⟩ := hXne
  have hzK := σ.X_subset r hz
  have hzu : (H23 G φ).edist u z ≤ (3000 * Δ ^ 9 : ℕ) :=
    (SimpleGraph.edist_le_natCast_add (SimpleGraph.edist_le_natCast_add hur (σ.Q_near r hr _ hv))
      (σ.K_near hr hv hzK)).trans (Nat.cast_le.2 (by omega))
  have hne : (zone (H23 G φ) σ.bit u (3000 * Δ ^ 9)).Nonempty :=
    ⟨z, mem_zone.2 ⟨hzu, σ.bit_eq_true.2 (Or.inr ⟨r, hr, hz⟩)⟩⟩
  unfold outLarge
  simp only [hne, ↓reduceDIte]
  set w := (zone (H23 G φ) σ.bit u (3000 * Δ ^ 9)).min' hne
  have hw := mem_zone.1 (min'_mem _ hne)
  have hw0 : φ w ≠ 0 := H23_edist_ne_zero hw.1 hu
  obtain ⟨r', hr', hwX⟩ := (σ.bit_iff_of_ne_zero hw0).1 hw.2
  have hZ : zone (H23 G φ) σ.bit w (30 * Δ ^ 3) = σ.X r' := by
    rw [← σ.zone_eq hΔ hr' hwX hw0]; rfl
  unfold outW
  rw [hZ]
  obtain ⟨hXne', hcase⟩ := σ.X_spec hr'
  simp only [hXne', ↓reduceDIte]
  set x := (σ.X r').min' hXne'
  have hx : x ∈ σ.X r' := min'_mem _ _
  have hxw : (H23 G φ).edist w x ≤ (30 * Δ ^ 3 : ℕ) := by
    rw [← hZ] at hx; exact (mem_zone.1 hx).1
  have hreach : (H23 G φ).Reachable u x :=
    (SimpleGraph.reachable_of_edist_le_natCast hw.1).trans
      (SimpleGraph.reachable_of_edist_le_natCast hxw)
  have hpar := even_dist_iff hφ hreach hu
  rcases hcase with ⟨hconn, hx1⟩ | ⟨hconn, hx2⟩
  · simp only [hconn, ite_true]
    split_ifs with he
    · rw [hpar.1 he, hx1]
    · rcases fin3_ne_zero hu with h | h
      · exact absurd (hpar.2 (h.trans hx1.symm)) he
      · exact h.symm
  · simp only [hconn, ite_false]
    split_ifs with he
    · rw [hpar.1 he, hx2]
    · rcases fin3_ne_zero hu with h | h
      · exact h.symm
      · exact absurd (hpar.2 (h.trans hx2.symm)) he

/-- `A` outputs `ψ`. -/
theorem decode_eq_psi (hφ : IsGreedy G φ) (hΔ : 1 ≤ Δ) (u : V) :
    decode Δ G σ.bit u = psi G φ Δ u := by
  unfold decode psi
  rw [σ.inW_bit_iff hφ, σ.hb_bit hφ]
  by_cases hu : φ u = 0
  · simp [hu]
  simp only [hu, ite_false]
  unfold decode2
  by_cases hL : IsLarge (H23 G φ) (4000 * Δ ^ 9) u
  · rw [ite_eq_right (by rw [smallAt_iff_not_isLarge]; exact not_not.2 hL), ite_eq_left hL]
    exact σ.outLarge_eq hφ hΔ hu hL
  · rw [ite_eq_left ((smallAt_iff_not_isLarge _ _ _).2 hL), ite_eq_right hL]
    unfold outSmall compMin
    congr 4
    ext z
    simp only [mem_ballF, mem_filter, mem_univ, true_and]
    constructor
    · exact SimpleGraph.reachable_of_edist_le_natCast
    · intro hz
      have h := (smallAt_iff_not_isLarge _ _ _).2 hL
      by_contra hfar
      apply hL
      refine ⟨u, z, Reachable.refl u, hz, ?_⟩
      by_contra hle
      exact hfar (hz.edist_le_natCast (by omega))

end Schema

/-- **Theorem 34** of [Balliu et al., arXiv:2405.04519]. Let `φ` be a greedy 3-colouring of `G`
(`Δ ≥ 1`) and `σ` an encoding schema for it. With the advice `σ.bit`, algorithm `A` (`decode Δ`)
outputs a proper 3-colouring, and it runs in `8000Δ⁹ + 3 = O(Δ⁹)` rounds. -/
theorem theorem_34 (hφ : IsGreedy G φ) (hΔ : 1 ≤ Δ) (σ : Schema G φ Δ) :
    (∀ u v, G.Adj u v → decode Δ G σ.bit u ≠ decode Δ G σ.bit v) ∧
      IsLocal (8000 * Δ ^ 9 + 3) (decode (V := V) Δ) := by
  refine ⟨fun u v huv => ?_, decode_isLocal⟩
  rw [σ.decode_eq_psi hφ hΔ, σ.decode_eq_psi hφ hΔ]
  exact psi_proper hφ huv

end

end Podc.LocalAdvice
