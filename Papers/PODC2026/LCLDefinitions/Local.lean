import Mathlib

/-!
# Local propagation arguments for edge-consistent distance-2 colourings

Generic part of the proof of (our repaired) Theorem 5.1 of *It does not matter how you define
locally checkable labelings* (Cruciani, Das, Raevskaya, Suomela; PODC 2026).

For a graph `G` and a colouring `χ`:
* `IsDist2 G χ`: `χ` is injective on every closed neighbourhood (condition 1 of Theorem 5.1);
* `IsCons G χ`: `χ` is (globally) edge-consistent: if `χ v' = χ v` then for every neighbour `u` of
  `v` some neighbour `u'` of `v'` has `χ u' = χ u`.

`BlockFacts G pv p0 p1 p2 p3 p4 p5 nx` records the local structure of one A-gadget `p0, …, p5`
with its outside neighbours `pv` (before `p0`) and `nx` (after `p5`). The lemmas below are the
local case analyses: the colour of `pv` differs from those of `p3`, `p4` (`ne_pv_p3`,
`ne_pv_p4`; this is the content of the paper's Lemma 5.2 / Figure 2), an original vertex never
shares its colour with a vertex in a triangle (`ne_of_triangle`, the paper's Lemma 5.9 /
Corollary 5.10), and colours propagate rigidly through a gadget (`block_step`, the induction step
of the paper's Lemma 5.12 / 5.13).
-/

namespace Podc.LCLDefinitions

variable {α C : Type*}

/-- `χ` is a distance-2 colouring: injective on every closed neighbourhood. -/
def IsDist2 (G : SimpleGraph α) (χ : α → C) : Prop :=
  ∀ v a b, (a = v ∨ G.Adj v a) → (b = v ∨ G.Adj v b) → a ≠ b → χ a ≠ χ b

/-- `χ` is edge-consistent: vertices of the same colour see the same colours around them. -/
def IsCons (G : SimpleGraph α) (χ : α → C) : Prop :=
  ∀ v u, G.Adj v u → ∀ v', χ v' = χ v → ∃ u', G.Adj v' u' ∧ χ u' = χ u

variable {G : SimpleGraph α} {χ : α → C}

lemma IsDist2.ne_adj (h : IsDist2 G χ) {a b : α} (hab : G.Adj a b) : χ a ≠ χ b :=
  h a a b (Or.inl rfl) (Or.inr hab) hab.ne

lemma IsDist2.ne_common (h : IsDist2 G χ) {a b c : α} (ha : G.Adj c a) (hb : G.Adj c b)
    (hab : a ≠ b) : χ a ≠ χ b :=
  h c a b (Or.inr ha) (Or.inr hb) hab

lemma IsDist2.eq_of_common (h : IsDist2 G χ) {a b c : α} (ha : G.Adj c a) (hb : G.Adj c b)
    (he : χ a = χ b) : a = b := by
  by_contra hab; exact h.ne_common ha hb hab he

lemma IsCons.step (h : IsCons G χ) {x y x' : α} (hxy : χ y = χ x) (hx : G.Adj x x') :
    ∃ y', G.Adj y y' ∧ χ y' = χ x' :=
  h x x' hx y hxy

/-- The local structure of an A-gadget `p0, …, p5` (in our numbering: path `p0 … p5` plus chords
`p0 p2`, `p1 p4`, `p3 p5`) together with its outside neighbours `pv` and `nx`. -/
structure BlockFacts (G : SimpleGraph α) (pv p0 p1 p2 p3 p4 p5 nx : α) : Prop where
  a0 : G.Adj pv p0
  a01 : G.Adj p0 p1
  a02 : G.Adj p0 p2
  a12 : G.Adj p1 p2
  a14 : G.Adj p1 p4
  a23 : G.Adj p2 p3
  a34 : G.Adj p3 p4
  a35 : G.Adj p3 p5
  a45 : G.Adj p4 p5
  a5 : G.Adj p5 nx
  n0 : ∀ y, G.Adj p0 y → y = pv ∨ y = p1 ∨ y = p2
  n1 : ∀ y, G.Adj p1 y → y = p0 ∨ y = p2 ∨ y = p4
  n2 : ∀ y, G.Adj p2 y → y = p0 ∨ y = p1 ∨ y = p3
  n3 : ∀ y, G.Adj p3 y → y = p2 ∨ y = p4 ∨ y = p5
  n4 : ∀ y, G.Adj p4 y → y = p1 ∨ y = p3 ∨ y = p5
  n5 : ∀ y, G.Adj p5 y → y = p3 ∨ y = p4 ∨ y = nx
  d03 : p0 ≠ p3
  d04 : p0 ≠ p4
  d13 : p1 ≠ p3
  d24 : p2 ≠ p4
  d25 : p2 ≠ p5
  dv1 : pv ≠ p1
  dv2 : pv ≠ p2
  dn3 : nx ≠ p3
  dn4 : nx ≠ p4

namespace BlockFacts

variable {pv p0 p1 p2 p3 p4 p5 nx : α} (bf : BlockFacts G pv p0 p1 p2 p3 p4 p5 nx)
include bf

/-- The two ends of an A-gadget get different colours. -/
lemma ne_p0_p5 (hD : IsDist2 G χ) (hC : IsCons G χ) : χ p0 ≠ χ p5 := by
  intro h
  -- `p5` must see the colours of `p1` and `p2`; only `nx` is available for both
  obtain ⟨z, hz, hz1⟩ := hC.step h.symm bf.a01
  obtain ⟨z', hz', hz2⟩ := hC.step h.symm bf.a02
  have e1 : z = nx := by
    rcases bf.n5 z hz with rfl | rfl | rfl
    · exact absurd hz1 (hD.ne_common bf.a23 bf.a12.symm bf.d13.symm)
    · exact absurd hz1 (hD.ne_adj bf.a14.symm)
    · rfl
  have e2 : z' = nx := by
    rcases bf.n5 z' hz' with rfl | rfl | rfl
    · exact absurd hz2 (hD.ne_adj bf.a23.symm)
    · exact absurd hz2 (hD.ne_common bf.a14 bf.a12 bf.d24.symm)
    · rfl
  subst e1 e2
  exact hD.ne_adj bf.a12 (hz1.symm.trans hz2)

/-- The vertex before an A-gadget and its vertex `p4` get different colours (paper: an original
vertex and the vertex `5` of its first gadget; Lemma 5.2, Figure 2). -/
lemma ne_pv_p4 (hD : IsDist2 G χ) (hC : IsCons G χ) : χ pv ≠ χ p4 := by
  intro h
  obtain ⟨y, hy, hy0⟩ := hC.step h.symm bf.a0
  rcases bf.n4 y hy with rfl | rfl | rfl
  · exact hD.ne_adj bf.a01.symm hy0
  · exact hD.ne_common bf.a23 bf.a02.symm bf.d03.symm hy0
  · exact bf.ne_p0_p5 hD hC hy0.symm

/-- The vertex before an A-gadget and its vertex `p3` get different colours. -/
lemma ne_pv_p3 (hD : IsDist2 G χ) (hC : IsCons G χ) : χ pv ≠ χ p3 := by
  intro h
  obtain ⟨y, hy, hy0⟩ := hC.step h.symm bf.a0
  rcases bf.n3 y hy with rfl | rfl | rfl
  · exact hD.ne_adj bf.a02.symm hy0
  · exact hD.ne_common bf.a14 bf.a01.symm bf.d04.symm hy0
  · exact bf.ne_p0_p5 hD hC hy0.symm

end BlockFacts

/-- An "original" vertex `o` (every neighbour of `o` is the first vertex of an A-gadget hanging at
`o`) never has the colour of a vertex in a triangle (paper: Lemma 5.9 and Corollary 5.10). -/
lemma ne_of_triangle (hD : IsDist2 G χ) (hC : IsCons G χ) {o c c1 c2 : α}
    (hO : ∀ y, G.Adj o y → ∃ p1 p2 p3 p4 p5 nx, BlockFacts G o y p1 p2 p3 p4 p5 nx)
    (h1 : G.Adj c c1) (h2 : G.Adj c c2) (h12 : G.Adj c1 c2) : χ o ≠ χ c := by
  intro h
  obtain ⟨o1, ho1, ho1c⟩ := hC.step h h1
  obtain ⟨o2, ho2, ho2c⟩ := hC.step h h2
  obtain ⟨z, hz, hzc⟩ := hC.step ho1c h12
  obtain ⟨p1, p2, p3, p4, p5, nx, bf⟩ := hO o1 ho1
  rcases bf.n0 z hz with rfl | rfl | rfl
  · exact hD.ne_adj h2 (h.symm.trans hzc)
  · -- `p1` has the colour of `o2`, so it must see the colour of `o`
    obtain ⟨w, hw, hwo⟩ := hC.step (hzc.trans ho2c.symm) ho2.symm
    rcases bf.n1 w hw with rfl | rfl | rfl
    · exact hD.ne_adj ho1 hwo.symm
    · exact hD.ne_common bf.a0.symm bf.a02 bf.dv2 hwo.symm
    · exact bf.ne_pv_p4 hD hC hwo.symm
  · obtain ⟨w, hw, hwo⟩ := hC.step (hzc.trans ho2c.symm) ho2.symm
    rcases bf.n2 w hw with rfl | rfl | rfl
    · exact hD.ne_adj ho1 hwo.symm
    · exact hD.ne_common bf.a0.symm bf.a01 bf.dv1 hwo.symm
    · exact bf.ne_pv_p3 hD hC hwo.symm

/-- Rigid propagation of colours through an A-gadget: if two gadgets `P`, `Q` start with matching
colours (`pv ≡ qv`, `p0 ≡ q0`), then their vertices match (up to the symmetry `1 ↔ 2`, `3 ↔ 4` of
the A-gadget) and so do the vertices after them. -/
lemma block_step (hD : IsDist2 G χ) (hC : IsCons G χ)
    {pv p0 p1 p2 p3 p4 p5 nx qv q0 q1 q2 q3 q4 q5 qx : α}
    (P : BlockFacts G pv p0 p1 p2 p3 p4 p5 nx) (Q : BlockFacts G qv q0 q1 q2 q3 q4 q5 qx)
    (hv : χ pv = χ qv) (h0 : χ p0 = χ q0) :
    ((χ p1 = χ q1 ∧ χ p2 = χ q2 ∧ χ p3 = χ q3 ∧ χ p4 = χ q4) ∨
      (χ p1 = χ q2 ∧ χ p2 = χ q1 ∧ χ p3 = χ q4 ∧ χ p4 = χ q3)) ∧
      χ p5 = χ q5 ∧ χ nx = χ qx := by
  -- where do the colours of `p1`, `p2` go?
  obtain ⟨y1, hy1, e1⟩ := hC.step h0.symm P.a01
  obtain ⟨y2, hy2, e2⟩ := hC.step h0.symm P.a02
  have hpv1 : χ qv ≠ χ p1 := hv ▸ hD.ne_common P.a0.symm P.a01 P.dv1
  have hpv2 : χ qv ≠ χ p2 := hv ▸ hD.ne_common P.a0.symm P.a02 P.dv2
  rcases Q.n0 y1 hy1 with rfl | rfl | rfl
  · exact absurd e1 hpv1
  · -- no flip
    rcases Q.n0 y2 hy2 with rfl | rfl | rfl
    · exact absurd e2 hpv2
    · exact absurd (e1.symm.trans e2) (hD.ne_adj P.a12)
    · obtain ⟨y4, hy4, e4⟩ := hC.step e1 P.a14
      obtain ⟨y3, hy3, e3⟩ := hC.step e2 P.a23
      have f4 : y4 = q4 := by
        rcases Q.n1 y4 hy4 with rfl | rfl | rfl
        · exact absurd (h0.trans e4) (hD.ne_common P.a01.symm P.a14 P.d04)
        · exact absurd (e2.symm.trans e4) (hD.ne_common P.a12 P.a14 P.d24)
        · rfl
      have f3 : y3 = q3 := by
        rcases Q.n2 y3 hy3 with rfl | rfl | rfl
        · exact absurd (h0.trans e3) (hD.ne_common P.a02.symm P.a23 P.d03)
        · exact absurd (e1.symm.trans e3) (hD.ne_common P.a12.symm P.a23 P.d13)
        · rfl
      subst f4 f3
      obtain ⟨y5, hy5, e5⟩ := hC.step e3 P.a35
      have f5 : y5 = q5 := by
        rcases Q.n3 y5 hy5 with rfl | rfl | rfl
        · exact absurd (e2.symm.trans e5) (hD.ne_common P.a23.symm P.a35 P.d25)
        · exact absurd (e4.symm.trans e5) (hD.ne_adj P.a45)
        · rfl
      subst f5
      obtain ⟨yx, hyx, ex⟩ := hC.step e5 P.a5
      have fx : yx = qx := by
        rcases Q.n5 yx hyx with rfl | rfl | rfl
        · exact absurd (e3.symm.trans ex) (hD.ne_common P.a35.symm P.a5 P.dn3.symm)
        · exact absurd (e4.symm.trans ex) (hD.ne_common P.a45.symm P.a5 P.dn4.symm)
        · rfl
      subst fx
      exact ⟨Or.inl ⟨e1.symm, e2.symm, e3.symm, e4.symm⟩, e5.symm, ex.symm⟩
  · -- flip
    rcases Q.n0 y2 hy2 with rfl | rfl | rfl
    · exact absurd e2 hpv2
    · obtain ⟨y4, hy4, e4⟩ := hC.step e1 P.a14
      obtain ⟨y3, hy3, e3⟩ := hC.step e2 P.a23
      have f4 : y4 = q3 := by
        rcases Q.n2 y4 hy4 with rfl | rfl | rfl
        · exact absurd (h0.trans e4) (hD.ne_common P.a01.symm P.a14 P.d04)
        · exact absurd (e2.symm.trans e4) (hD.ne_common P.a12 P.a14 P.d24)
        · rfl
      have f3 : y3 = q4 := by
        rcases Q.n1 y3 hy3 with rfl | rfl | rfl
        · exact absurd (h0.trans e3) (hD.ne_common P.a02.symm P.a23 P.d03)
        · exact absurd (e1.symm.trans e3) (hD.ne_common P.a12.symm P.a23 P.d13)
        · rfl
      subst f4 f3
      obtain ⟨y5, hy5, e5⟩ := hC.step e3 P.a35
      have f5 : y5 = q5 := by
        rcases Q.n4 y5 hy5 with rfl | rfl | rfl
        · exact absurd (e2.symm.trans e5) (hD.ne_common P.a23.symm P.a35 P.d25)
        · exact absurd (e4.symm.trans e5) (hD.ne_adj P.a45)
        · rfl
      subst f5
      obtain ⟨yx, hyx, ex⟩ := hC.step e5 P.a5
      have fx : yx = qx := by
        rcases Q.n5 yx hyx with rfl | rfl | rfl
        · exact absurd (e4.symm.trans ex) (hD.ne_common P.a45.symm P.a5 P.dn4.symm)
        · exact absurd (e3.symm.trans ex) (hD.ne_common P.a35.symm P.a5 P.dn3.symm)
        · rfl
      subst fx
      exact ⟨Or.inr ⟨e1.symm, e2.symm, e3.symm, e4.symm⟩, e5.symm, ex.symm⟩
    · exact absurd (e1.symm.trans e2) (hD.ne_adj P.a12)

end Podc.LCLDefinitions
