import Papers.PODC2026.GirthApproxCongest.Gadget
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Field.ZMod

/-!
# Dense bipartite graphs of girth at least 6 (points–lines incidence graphs)

The hypothesis `DenseHighGirth 3` of §6.2 of *Girth Approximations in the CONGEST Model*
holds unconditionally: the point–line incidence graph of the affine plane over `ZMod p`
(`p` prime) has `p³` edges on `p² + p²` vertices and no cycles of length `< 6`.

* `bipGraph_even_length_iff` — walks in `bipGraph E` have even length iff they start and end on
  the same side (so `bipGraph E` has no odd cycles);
* `six_le_egirth_bipGraph` — if `E` contains no `C₄` (two distinct left vertices share at most one
  common neighbour), then `bipGraph E` has girth `≥ 6`;
* `denseHighGirth_three` — the main result, with constant `c = 1/9`, using Bertrand's postulate
  to choose `p ≈ √a`.
-/

namespace Podc.GirthApproxCongest

open SimpleGraph

section Bip

variable {L R : Type*} (E : Finset (L × R))

-- CSLib candidate (bipartite graphs have no odd closed walks)
/-- In `bipGraph E`, a walk has even length iff its endpoints lie on the same side. -/
lemma bipGraph_even_length_iff {x y : L ⊕ R} (w : (bipGraph E).Walk x y) :
    Even w.length ↔ x.isLeft = y.isLeft := by
  induction w with
  | nil => simp
  | @cons u v z h q ih =>
    have huv : u.isLeft ≠ v.isLeft := by
      rcases u with u | u <;> rcases v with v | v <;> simp_all
    rw [Walk.length_cons, Nat.even_add_one, ih]
    revert huv
    cases u.isLeft <;> cases v.isLeft <;> cases z.isLeft <;> simp

/-- `E` contains no `C₄`: two distinct left vertices have at most one common neighbour. -/
def NoC4 : Prop :=
  ∀ u u' : L, ∀ w w' : R, u ≠ u' → w ≠ w' → (u, w) ∈ E → (u, w') ∈ E → (u', w) ∈ E →
    (u', w') ∈ E → False

variable {E}

lemma bipGraph_cycle_length_ne_four (hE : NoC4 E) {v : L ⊕ R} (c : (bipGraph E).Walk v v)
    (hc : c.IsCycle) : c.length ≠ 4 := by
  intro h4
  rcases c with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4', _ | ⟨h5, q⟩⟩⟩⟩⟩ <;>
    simp only [Walk.length_cons, Walk.length_nil] at h4 <;> try omega
  rename_i b c d
  rw [Walk.cons_isCycle_iff] at hc
  obtain ⟨hp, -⟩ := hc
  have hnd := hp.support_nodup
  simp only [Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨hbc, hbd, hbv⟩, ⟨hcd, hcv⟩, hdv, -⟩ := hnd
  rcases v with v | v <;> rcases b with b | b <;> simp at h1 <;>
    rcases c with c | c <;> simp at h2 <;> rcases d with d | d <;> simp at h3 h4'
  · exact hE v c b d (by simpa [eq_comm] using hcv) (by simpa using hbd) h1 h4' h2 h3
  · exact hE b d v c (by simpa using hbd) (by simpa [eq_comm] using hcv) h1 h2 h4' h3

/-- A `C₄`-free bipartite graph has girth at least `6`. -/
lemma six_le_egirth_bipGraph (hE : NoC4 E) : (6 : ℕ∞) ≤ (bipGraph E).egirth := by
  rw [le_egirth]
  intro v c hc
  have h3 := hc.three_le_length
  have hev : Even c.length := (bipGraph_even_length_iff E c).2 rfl
  have h4 := bipGraph_cycle_length_ne_four hE c hc
  have : 6 ≤ c.length := by
    rcases hev with ⟨k, hk⟩
    omega
  exact_mod_cast this

end Bip

section Incidence

variable (p : ℕ) [Fact p.Prime]

/-- Point `(x, y)` lies on line `(m, b)` (i.e. `y = m x + b`) of the affine plane over `ZMod p`. -/
def PLInc (pt ln : ZMod p × ZMod p) : Prop := pt.2 = ln.1 * pt.1 + ln.2

variable {p}

/-- Two distinct points lie on at most one common line. -/
lemma plInc_noC4 {pt pt' ln ln' : ZMod p × ZMod p} (hpt : pt ≠ pt') (hln : ln ≠ ln')
    (h1 : PLInc p pt ln) (h2 : PLInc p pt ln') (h3 : PLInc p pt' ln) (h4 : PLInc p pt' ln') :
    False := by
  obtain ⟨x, y⟩ := pt
  obtain ⟨x', y'⟩ := pt'
  obtain ⟨m, b⟩ := ln
  obtain ⟨m', b'⟩ := ln'
  simp only [PLInc] at h1 h2 h3 h4
  by_cases hm : m = m'
  · subst hm
    exact hln (Prod.ext rfl (show b = b' by linear_combination h2 - h1))
  · have hx : (m - m') * (x - x') = 0 := by linear_combination h3 - h4 - h1 + h2
    have hx' : x = x' := by
      rcases mul_eq_zero.1 hx with h | h
      · exact absurd (sub_eq_zero.1 h) hm
      · exact sub_eq_zero.1 h
    subst hx'
    exact hpt (Prod.ext rfl (show y = y' by linear_combination h1 - h3))

/-- The injective map `(x, m, b) ↦ ((x, m x + b), (m, b))` enumerating the incidences. -/
def plIncEmb : ZMod p × ZMod p × ZMod p ↪ (ZMod p × ZMod p) × (ZMod p × ZMod p) where
  toFun t := ((t.1, t.2.1 * t.1 + t.2.2), (t.2.1, t.2.2))
  inj' := by
    rintro ⟨x, m, b⟩ ⟨x', m', b'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨rfl, -⟩, rfl, rfl⟩ := h
    rfl

/-- The points–lines incidence graph, embedded into `Fin a ⊕ Fin a` along `f`. -/
def plEdges {a : ℕ} (f : ZMod p × ZMod p ↪ Fin a) : Finset (Fin a × Fin a) :=
  (Finset.univ.map plIncEmb).map (f.prodMap f)

lemma mem_plEdges {a : ℕ} {f : ZMod p × ZMod p ↪ Fin a} {u w : Fin a} :
    (u, w) ∈ plEdges f ↔ ∃ pt ln, f pt = u ∧ f ln = w ∧ PLInc p pt ln := by
  simp only [plEdges, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, h⟩
    exact ⟨_, _, (Prod.ext_iff.1 h).1, (Prod.ext_iff.1 h).2, rfl⟩
  · rintro ⟨pt, ln, hu, hw, h⟩
    refine ⟨(pt, ln), ⟨(pt.1, ln.1, ln.2), ?_⟩, ?_⟩
    · show ((pt.1, ln.1 * pt.1 + ln.2), (ln.1, ln.2)) = (pt, ln)
      rw [← h]
    · show (f pt, f ln) = (u, w)
      rw [hu, hw]

lemma card_plEdges {a : ℕ} (f : ZMod p × ZMod p ↪ Fin a) : (plEdges f).card = p ^ 3 := by
  simp [plEdges, ZMod.card]
  ring

lemma plEdges_noC4 {a : ℕ} (f : ZMod p × ZMod p ↪ Fin a) : NoC4 (plEdges f) := by
  intro u u' w w' hu hw h1 h2 h3 h4
  rw [mem_plEdges] at h1 h2 h3 h4
  obtain ⟨pt, ln, rfl, rfl, i1⟩ := h1
  obtain ⟨pt2, ln', e2, rfl, i2⟩ := h2
  obtain ⟨pt', ln3, rfl, e3, i3⟩ := h3
  obtain ⟨pt4, ln4, e4, e4', i4⟩ := h4
  rw [f.injective e2] at i2
  rw [f.injective e3] at i3
  rw [f.injective e4, f.injective e4'] at i4
  exact plInc_noC4 (fun h => hu (by rw [h])) (fun h => hw (by rw [h])) i1 i2 i3 i4

end Incidence

/-- For `a ≥ 4` there is a prime `p` with `p² ≤ a < (2p)²`. -/
lemma exists_prime_sq_le_lt (a : ℕ) (ha : 4 ≤ a) :
    ∃ p : ℕ, p.Prime ∧ p * p ≤ a ∧ a < (2 * p) * (2 * p) := by
  set m := Nat.sqrt a with hm
  have hm2 : 2 ≤ m := by
    rw [hm, Nat.le_sqrt]
    omega
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (m / 2) (by omega)
  refine ⟨p, hp, ?_, ?_⟩
  · have : p ≤ m := by omega
    calc p * p ≤ m * m := Nat.mul_le_mul this this
      _ ≤ a := Nat.sqrt_le a
  · have h1 : m + 1 ≤ 2 * p := by omega
    calc a < (m + 1) * (m + 1) := Nat.lt_succ_sqrt a
      _ ≤ (2 * p) * (2 * p) := Nat.mul_le_mul h1 h1

/-- Dense bipartite graphs of girth ≥ 6 exist (unconditional case k = 3 of the hypothesis of §6.2):
the points–lines incidence graph of the affine plane over `ZMod p`, with `c = 1/9`. -/
theorem denseHighGirth_three : DenseHighGirth 3 := by
  refine ⟨1 / 9, by norm_num, fun a ha => ?_⟩
  have hexp : (1 + 1 / (((3 : ℕ) : ℝ) - 1)) = (3 / 2 : ℝ) := by norm_num
  rw [hexp]
  have ha0 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  by_cases hsmall : a < 4
  · -- a single edge
    refine ⟨{(⟨0, by omega⟩, ⟨0, by omega⟩)}, ?_, ?_⟩
    · refine le_trans (by norm_num) (six_le_egirth_bipGraph ?_)
      intro u u' w w' hu _ h1 _ h3 _
      simp only [Finset.mem_singleton, Prod.mk.injEq] at h1 h3
      exact hu (h1.1.trans h3.1.symm)
    · rw [Finset.card_singleton]
      have h1 : (a : ℝ) ^ (3 / 2 : ℝ) ≤ (a : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ha0 (by norm_num)
      have h2 : (a : ℝ) ^ (2 : ℝ) ≤ 9 := by
        rw [Real.rpow_two]
        have : (a : ℝ) ≤ 3 := by exact_mod_cast (by omega : a ≤ 3)
        nlinarith
      push_cast
      linarith
  · obtain ⟨p, hp, hle, hlt⟩ := exists_prime_sq_le_lt a (by omega)
    have := Fact.mk hp
    have hcard : Fintype.card (ZMod p × ZMod p) ≤ a := by simpa [ZMod.card] using hle
    let f : ZMod p × ZMod p ↪ Fin a :=
      (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb hcard)
    refine ⟨plEdges f, le_trans (by norm_num) (six_le_egirth_bipGraph (plEdges_noC4 f)), ?_⟩
    rw [card_plEdges]
    have hlt' : (a : ℝ) ≤ ((2 * p : ℝ)) ^ (2 : ℕ) := by
      have : (a : ℝ) < ((2 * p * (2 * p) : ℕ) : ℝ) := by exact_mod_cast hlt
      push_cast at this
      nlinarith
    have h1 : (a : ℝ) ^ (3 / 2 : ℝ) ≤ (((2 * p : ℝ)) ^ (2 : ℕ)) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hlt' (by norm_num)
    have h2 : (((2 * p : ℝ)) ^ (2 : ℕ)) ^ (3 / 2 : ℝ) = 8 * (p : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
      ring
    rw [h2] at h1
    push_cast
    have : (0 : ℝ) ≤ (p : ℝ) ^ 3 := by positivity
    linarith

end Podc.GirthApproxCongest
