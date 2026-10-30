import Papers.PODC2024.LocalAdvice.Schema
import Cslib.Computability.Distributed.Local.Locality

/-!
# The 3-colouring algorithm `A` of Appendix D and its locality

`decode Δ G b u` is the output of node `u` on graph `G` with advice bits `b`:

1. `u` outputs colour 1 iff it has bit 1 and at most one neighbour with bit 1 (`InW`);
2. otherwise it looks at the graph `Hb G b` induced by the nodes not in `W`; if its component is
   small (diameter `≤ 4000Δ⁹`, detected from the ball of radius `4000Δ⁹ + 1`, `SmallAt`), it outputs
   the colour of the 2-colouring of the component that gives colour 2 to the smallest identifier;
3. otherwise it picks the smallest-identifier node `w` with bit 1 within distance `3000Δ⁹`, the set
   `Z` of nodes with bit 1 within distance `30Δ³` of `w`, and its smallest identifier `x`, and
   outputs colour 2 or 3 according to whether `Z` is connected and to the parity of `dist(u, x)`.

(Paper colours `1, 2, 3` are `0, 1, 2`.) Every node only reads its radius-`(8000Δ⁹ + 3)` view:
`decode_isLocal`.
-/

namespace Podc.LocalAdvice

open SimpleGraph Finset Cslib.Local

noncomputable section

open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The nodes with bit 1. -/
def ones (b : V → Bool) : Finset V := univ.filter fun v => b v = true

omit [LinearOrder V] in
@[simp] lemma mem_ones {b : V → Bool} {v : V} : v ∈ ones b ↔ b v = true := by simp [ones]

/-- `v ∈ W`: bit 1 and at most one neighbour with bit 1 (these nodes output colour 1). -/
def InW (G : SimpleGraph V) (b : V → Bool) (v : V) : Prop :=
  b v = true ∧ (nbrIn G v (ones b)).card ≤ 1

/-- The graph induced by the nodes outside `W`. -/
def Hb (G : SimpleGraph V) (b : V → Bool) : SimpleGraph V := restrict G fun v => ¬ InW G b v

/-- The component of `u` in `H` has diameter `≤ D`, read off the ball of radius `D + 1`: no node at
distance `D + 1`, and any two nodes of the radius-`D` ball are within distance `D`. -/
def SmallAt (H : SimpleGraph V) (D : ℕ) (u : V) : Prop :=
  (∀ z, H.edist u z ≤ (D + 1 : ℕ) → H.edist u z ≤ D) ∧
  ∀ x y, H.edist u x ≤ D → H.edist u y ≤ D → H.edist x y ≤ D

/-- The ball of radius `k` around `u`. -/
def ballF (H : SimpleGraph V) (u : V) (k : ℕ) : Finset V := univ.filter fun z => H.edist u z ≤ k

omit [LinearOrder V] in
@[simp] lemma mem_ballF {H : SimpleGraph V} {u z : V} {k : ℕ} :
    z ∈ ballF H u k ↔ H.edist u z ≤ k := by simp [ballF]

omit [LinearOrder V] in
lemma ballF_nonempty (H : SimpleGraph V) (u : V) (k : ℕ) : (ballF H u k).Nonempty :=
  ⟨u, by simp⟩

/-- The nodes with bit 1 within distance `k` of `w`. -/
def zone (H : SimpleGraph V) (b : V → Bool) (w : V) (k : ℕ) : Finset V :=
  univ.filter fun z => H.edist w z ≤ k ∧ b z = true

omit [LinearOrder V] in
@[simp] lemma mem_zone {H : SimpleGraph V} {b : V → Bool} {w z : V} {k : ℕ} :
    z ∈ zone H b w k ↔ H.edist w z ≤ k ∧ b z = true := by simp [zone]

variable (Δ : ℕ)

/-- Output of a node of a large component, given the chosen 1-bit `w`: with `Z` the zone of
radius `30Δ³` around `w` and `x` its smallest identifier, colour 2 iff (`Z` connected) agrees with
(`dist(u, x)` even). -/
def outW (H : SimpleGraph V) (b : V → Bool) (u w : V) : Fin 3 :=
  if h : (zone H b w (30 * Δ ^ 3)).Nonempty then
    if ZConn H (zone H b w (30 * Δ ^ 3)) then
      (if Even (H.dist u ((zone H b w (30 * Δ ^ 3)).min' h)) then 1 else 2)
    else (if Even (H.dist u ((zone H b w (30 * Δ ^ 3)).min' h)) then 2 else 1)
  else 0

/-- Output of a node of a large component: choose the smallest-identifier 1-bit `w` within
distance `3000Δ⁹`. -/
def outLarge (H : SimpleGraph V) (b : V → Bool) (u : V) : Fin 3 :=
  if h : (zone H b u (3000 * Δ ^ 9)).Nonempty then outW Δ H b u ((zone H b u (3000 * Δ ^ 9)).min' h)
  else 0

/-- Output of a node of a small component: the 2-colouring giving colour 2 to the smallest
identifier of the component. -/
def outSmall (H : SimpleGraph V) (u : V) : Fin 3 :=
  if Even (H.dist u ((ballF H u (4000 * Δ ^ 9)).min' (ballF_nonempty _ _ _))) then 1 else 2

/-- Output of a node outside `W`, computed in `H = Hb G b`. -/
def decode2 (H : SimpleGraph V) (b : V → Bool) (u : V) : Fin 3 :=
  if SmallAt H (4000 * Δ ^ 9) u then outSmall Δ H u else outLarge Δ H b u

/-- **The 3-colouring algorithm `A`** of Appendix D: the output of node `u` on `(G, b)`. -/
def decode (G : SimpleGraph V) (b : V → Bool) (u : V) : Fin 3 :=
  if InW G b u then 0 else decode2 Δ (Hb G b) b u

/-! ### Locality -/

variable {Δ}

section Transfer

variable {G G' : SimpleGraph V} {b b' : V → Bool} {u : V} {R : ℕ}

omit [Fintype V] [LinearOrder V] in
/-- A neighbour of a node at distance `< R` is at distance `≤ R`. -/
lemma edist_le_of_lt_of_adj {x y : V} (hx : G.edist u x < R) (hxy : G.Adj x y) :
    G.edist u y ≤ R := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hx)
  have h3 := SimpleGraph.edist_le_add_one_of_adj (u := u) hxy
  rw [← hk] at hx h3
  have : k < R := by exact_mod_cast hx
  exact h3.trans (by exact_mod_cast (by omega : k + 1 ≤ R))

omit [Fintype V] [LinearOrder V] in
-- CSLib candidate: Cslib/Computability/Distributed/Local/Locality.lean
/-- Restricting agreeing graphs to predicates that agree on the ball gives agreeing graphs. -/
lemma gAgree_restrict {P P' : V → Prop} (hA : GAgree G G' u R)
    (hP : ∀ z, G.edist u z ≤ R → (P z ↔ P' z)) : GAgree (restrict G P) (restrict G' P') u R := by
  intro x hx y
  have hx' : G.edist u x < R := lt_of_le_of_lt (edist_anti (restrict_le G P)) hx
  simp only [restrict_adj]
  by_cases hxy : G.Adj x y
  · have hy : G.edist u y ≤ R := edist_le_of_lt_of_adj hx' hxy
    rw [hP x hx'.le, hP y hy, hA hx' y]
  · have : ¬ G'.Adj x y := fun h => hxy ((hA hx' y).2 h)
    simp [hxy, this]

/-- Membership in `W` is determined by the radius-1 view. -/
lemma inW_iff_of_viewEq (hv : ViewEq R G b G' b' u) {z : V} (hz : G.edist u z < R) :
    InW G b z ↔ InW G' b' z := by
  have hnb : nbrIn G z (ones b) = nbrIn G' z (ones b') := by
    ext y
    simp only [mem_nbrIn, mem_ones]
    constructor
    · rintro ⟨h1, h2⟩
      have hy : G.edist u y ≤ R := edist_le_of_lt_of_adj hz h1
      exact ⟨(hv.1 hz y).1 h1, (hv.2 y hy) ▸ h2⟩
    · rintro ⟨h1, h2⟩
      have h1' := (hv.1 hz y).2 h1
      have hy : G.edist u y ≤ R := edist_le_of_lt_of_adj hz h1'
      exact ⟨h1', (hv.2 y hy).symm ▸ h2⟩
  unfold InW
  rw [hnb, hv.2 z hz.le]

omit [Fintype V] [LinearOrder V] in
lemma pow_three_le_pow_nine (Δ : ℕ) : Δ ^ 3 ≤ Δ ^ 9 := by
  rcases Nat.eq_zero_or_pos Δ with rfl | h
  · simp
  · exact Nat.pow_le_pow_right h (by norm_num)

variable {H H' : SimpleGraph V}

omit [Fintype V] [LinearOrder V] in
/-- `SmallAt` is determined by the radius-`(2D+1)` view. -/
lemma smallAt_of_gAgree {D : ℕ} (hA : GAgree H H' u R) (hR : 2 * D + 1 ≤ R)
    (h : SmallAt H D u) : SmallAt H' D u := by
  refine ⟨fun z hz => ?_, fun x y hx hy => ?_⟩
  · have := h.1 z ((hA.edist_le_iff (by omega)).1 hz)
    exact (hA.edist_le_iff (by omega)).2 this
  · have hx' := (hA.edist_le_iff (m := D) (by omega)).1 hx
    have hy' := (hA.edist_le_iff (m := D) (by omega)).1 hy
    have hAx := hA.mono hx' (show D + (R - D) ≤ R by omega)
    exact (hAx.edist_le_iff (by omega)).2 (h.2 x y hx' hy')

omit [LinearOrder V] in
lemma ballF_congr (hA : GAgree H H' u R) {k : ℕ} (hk : k ≤ R) : ballF H' u k = ballF H u k := by
  ext z; simp only [mem_ballF]; exact hA.edist_le_iff hk

omit [LinearOrder V] in
lemma zone_congr {w : V} (hA : GAgree H H' w R) {k : ℕ} (hk : k ≤ R)
    (hb : ∀ z, H.edist w z ≤ k → b z = b' z) : zone H' b' w k = zone H b w k := by
  ext z
  simp only [mem_zone]
  rw [hA.edist_le_iff hk]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, (hb z h1) ▸ h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (hb z h1).symm ▸ h2⟩

omit [Fintype V] in
lemma zConn_congr (hA : GAgree H H' u R) {Z : Finset V} (hZ : ∀ z ∈ Z, H.edist u z < R) :
    ZConn H' Z ↔ ZConn H Z := by
  have : restrict H' (· ∈ Z) = restrict H (· ∈ Z) := by
    ext x y
    simp only [restrict_adj]
    by_cases hx : x ∈ Z
    · rw [hA (hZ x hx) y]
    · simp [hx]
  unfold ZConn; rw [this]

end Transfer

section Local2

variable {H H' : SimpleGraph V} {b b' : V → Bool} {u : V}

/-- The output of a large-component node given `w` is local. -/
lemma outW_congr (hA : GAgree H H' u (8000 * Δ ^ 9 + 2))
    (hb : ∀ z, H.edist u z ≤ (8000 * Δ ^ 9 + 2 : ℕ) → b z = b' z) {w : V}
    (hw : H.edist u w ≤ (3000 * Δ ^ 9 : ℕ)) : outW Δ H' b' u w = outW Δ H b u w := by
  have h39 := pow_three_le_pow_nine Δ
  have hAw := hA.mono hw (show 3000 * Δ ^ 9 + (5000 * Δ ^ 9 + 2) ≤ 8000 * Δ ^ 9 + 2 by omega)
  have hnear : ∀ z, H.edist w z ≤ (30 * Δ ^ 3 : ℕ) →
      H.edist u z ≤ (3000 * Δ ^ 9 + 30 * Δ ^ 3 : ℕ) :=
    fun z hz => SimpleGraph.edist_le_natCast_add hw hz
  have hZ : zone H' b' w (30 * Δ ^ 3) = zone H b w (30 * Δ ^ 3) :=
    zone_congr hAw (by omega) fun z hz => hb z ((hnear z hz).trans (Nat.cast_le.2 (by omega)))
  unfold outW
  rw [hZ]
  by_cases h : (zone H b w (30 * Δ ^ 3)).Nonempty
  · simp only [h, ↓reduceDIte]
    have hx := min'_mem _ h
    rw [mem_zone] at hx
    have hxu := hnear _ hx.1
    rw [zConn_congr hA (fun z hz => by
        have := hnear z (mem_zone.1 hz).1
        exact lt_of_le_of_lt this (by exact_mod_cast (by omega :
          3000 * Δ ^ 9 + 30 * Δ ^ 3 < 8000 * Δ ^ 9 + 2))),
      hA.dist_eq (hxu.trans (Nat.cast_le.2 (by omega)))]
  · simp [h]

lemma outLarge_congr (hA : GAgree H H' u (8000 * Δ ^ 9 + 2))
    (hb : ∀ z, H.edist u z ≤ (8000 * Δ ^ 9 + 2 : ℕ) → b z = b' z) :
    outLarge Δ H' b' u = outLarge Δ H b u := by
  have hZ : zone H' b' u (3000 * Δ ^ 9) = zone H b u (3000 * Δ ^ 9) :=
    zone_congr hA (by omega) fun z hz => hb z (hz.trans (Nat.cast_le.2 (by omega)))
  unfold outLarge
  rw [hZ]
  by_cases h : (zone H b u (3000 * Δ ^ 9)).Nonempty
  · simp only [h, ↓reduceDIte]
    exact outW_congr hA hb (mem_zone.1 (min'_mem _ h)).1
  · simp [h]

lemma outSmall_congr (hA : GAgree H H' u (8000 * Δ ^ 9 + 2)) :
    outSmall Δ H' u = outSmall Δ H u := by
  unfold outSmall
  have hB := ballF_congr hA (k := 4000 * Δ ^ 9) (by omega)
  simp only [hB]
  have hm := min'_mem _ (ballF_nonempty H u (4000 * Δ ^ 9))
  rw [mem_ballF] at hm
  rw [hA.dist_eq (hm.trans (Nat.cast_le.2 (by omega)))]

lemma decode2_congr (hA : GAgree H H' u (8000 * Δ ^ 9 + 2))
    (hb : ∀ z, H.edist u z ≤ (8000 * Δ ^ 9 + 2 : ℕ) → b z = b' z) :
    decode2 Δ H' b' u = decode2 Δ H b u := by
  have hs : SmallAt H' (4000 * Δ ^ 9) u ↔ SmallAt H (4000 * Δ ^ 9) u :=
    ⟨smallAt_of_gAgree hA.symm (by omega), smallAt_of_gAgree hA (by omega)⟩
  unfold decode2
  rw [outSmall_congr hA, outLarge_congr hA hb]
  simp only [hs]

end Local2

/-- **Locality of `A`** (round complexity part of Theorem 34): the output of a node only depends
on its radius-`(8000Δ⁹ + 3)` view, i.e. `A` runs in `8000Δ⁹ + 3 = O(Δ⁹)` rounds. -/
theorem decode_isLocal : IsLocal (8000 * Δ ^ 9 + 3) (decode (V := V) Δ) := by
  intro G b G' b' u hv
  have hW : ∀ z, G.edist u z ≤ (8000 * Δ ^ 9 + 2 : ℕ) → (¬ InW G b z ↔ ¬ InW G' b' z) := by
    intro z hz
    rw [inW_iff_of_viewEq hv (lt_of_le_of_lt hz (by exact_mod_cast (by omega :
      8000 * Δ ^ 9 + 2 < 8000 * Δ ^ 9 + 3)))]
  have hA : GAgree (Hb G b) (Hb G' b') u (8000 * Δ ^ 9 + 2) :=
    gAgree_restrict (hv.1.mono_radius (by omega)) hW
  have hbits : ∀ z, (Hb G b).edist u z ≤ (8000 * Δ ^ 9 + 2 : ℕ) → b z = b' z := fun z hz =>
    hv.2 z ((edist_anti (restrict_le G _)).trans (hz.trans (Nat.cast_le.2 (by omega))))
  unfold decode
  rw [inW_iff_of_viewEq hv (by simp), decode2_congr hA hbits]

end

end Podc.LocalAdvice
