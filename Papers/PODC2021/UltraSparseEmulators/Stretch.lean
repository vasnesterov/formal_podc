import Papers.PODC2021.UltraSparseEmulators.Params
import Podc.Foundations.Combinatorics.SimpleGraph.Emulator

/-!
# Stretch analysis (Section 2.2.2: Lemma 2.10, Corollaries 2.11 and 2.13)

Elkin, Matar. *Ultra-Sparse Near-Additive Emulators.* PODC 2021 (arXiv:2106.01036v1).

The stretch analysis uses only a few properties of the output of Algorithm 1, collected in the
structure `Hierarchy`:

* every vertex `v` lies in a cluster of `U_{lev v}` with `lev v ≤ ℓ` (Lemma 2.8 and eq. (1));
* `ctr i v` is the center of the cluster of `P_i` containing `v`, for `i ≤ lev v`; `ctr 0 v = v`;
* the radius bound `d_H(ctr i v, v) ≤ R_i` (Lemma 2.5);
* laminarity: for `j ≤ i ≤ lev v`, the center `ctr j v` lies in the same cluster of `P_i` as `v`
  (Lemma 2.9);
* interconnection: the center of a `U_i`-cluster is joined in `H` to every neighbouring
  cluster center of `P_i` at distance `≤ δ_i` (Lemma 2.7);
* every emulator edge joins two vertices connected in `G` (emulator edges are weighted by `d_G`).

`Hierarchy.lemma_2_10` proves Lemma 2.10 for **all** walks whose vertices are all `U^{(i)}`-clustered
(not only for shortest paths with the minimal such `i`); `Hierarchy.isEmulator` is Corollary 2.11.
-/

namespace Podc.UltraSparseEmulators

open SimpleGraph
open scoped ENNReal NNReal

variable {V : Type*} {G H : SimpleGraph V}

/-! ### Upper bounds on `d_H` -/

/-- `d_H(u, v) ≤ b`, where `H` is weighted by `d_G` (`distW G`). -/
def HD (G H : SimpleGraph V) (u v : V) (b : ℝ) : Prop :=
  H.wdist G.distW u v ≤ ENNReal.ofReal b

namespace HD

variable {u v x : V} {a b : ℝ}

lemma mono (h : HD G H u v a) (hab : a ≤ b) : HD G H u v b :=
  h.trans (ENNReal.ofReal_le_ofReal hab)

lemma trans (h1 : HD G H u v a) (h2 : HD G H v x b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HD G H u x (a + b) := by
  unfold HD at *
  rw [ENNReal.ofReal_add ha hb]
  exact wdist_triangle.trans (add_le_add h1 h2)

lemma symm (h : HD G H u v a) : HD G H v u a := by
  unfold HD at *; rwa [wdist_comm]

lemma refl (u : V) : HD G H u u 0 := by
  unfold HD; simp

lemma of_adj (h : H.Adj u v) : HD G H u v (G.dist u v) := by
  unfold HD
  simpa using wdist_distW_le_of_adj (G := G) h

/-- From an upper bound on `d_H` to an upper bound on `d_G` (`d_G ≤ d_H`). -/
lemma dist_le (hH : ∀ x y, H.Adj x y → G.Reachable x y) (h : HD G H u v a) (ha : 0 ≤ a) :
    G.Reachable u v ∧ (G.dist u v : ℝ) ≤ a := by
  have h1 := (edist_le_wdist_distW hH u v).trans h
  have hr : G.Reachable u v := by
    by_contra hn
    rw [edist_eq_top_of_not_reachable hn] at h1
    simp at h1
  refine ⟨hr, ?_⟩
  rw [← hr.coe_dist_eq_edist] at h1
  have h2 : ((G.dist u v : ℝ≥0∞)) ≤ ENNReal.ofReal a := by simpa using h1
  rw [← ENNReal.ofReal_natCast] at h2
  exact (ENNReal.ofReal_le_ofReal_iff ha).1 h2

end HD

/-! ### Walk decompositions -/

namespace WalkAux

variable {G' : SimpleGraph V}

/-- Split a walk after its first `n` steps. -/
lemma exists_split {u v : V} (p : G'.Walk u v) (n : ℕ) (hn : n ≤ p.length) :
    ∃ w, ∃ (p₁ : G'.Walk u w) (p₂ : G'.Walk w v), p₁.length = n ∧
      p₁.length + p₂.length = p.length ∧
      (∀ x ∈ p₁.support, x ∈ p.support) ∧ (∀ x ∈ p₂.support, x ∈ p.support) := by
  induction p generalizing n with
  | nil => exact ⟨_, .nil, .nil, by simp at hn ⊢; omega, by simp, by simp, by simp⟩
  | @cons a b c h q ih =>
    rcases n with _ | n
    · exact ⟨a, .nil, .cons h q, rfl, by simp, by simp, fun x hx => hx⟩
    · obtain ⟨w, p₁, p₂, h1, h2, h3, h4⟩ := ih n (by simp at hn; omega)
      refine ⟨w, .cons h p₁, p₂, by simp [h1], by simp; omega, ?_, ?_⟩
      · intro x hx
        simp only [Walk.support_cons, List.mem_cons] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (h3 x hx)
      · intro x hx
        simp only [Walk.support_cons, List.mem_cons]
        exact Or.inr (h4 x hx)

/-- The first vertex of a walk satisfying `P`: either the start vertex, or it is preceded by a
vertex `w` such that no vertex of the walk up to `w` satisfies `P`. -/
lemma exists_first (P : V → Prop) {u v : V} (p : G'.Walk u v) (h : ∃ x ∈ p.support, P x) :
    ∃ z, P z ∧ ∃ r : G'.Walk z v, (∀ x ∈ r.support, x ∈ p.support) ∧
      ((u = z ∧ r.length = p.length) ∨
        ∃ w, ∃ q : G'.Walk u w, G'.Adj w z ∧ (∀ x ∈ q.support, ¬ P x ∧ x ∈ p.support) ∧
          q.length + 1 + r.length = p.length) := by
  induction p with
  | nil =>
    obtain ⟨x, hx, hP⟩ := h
    simp only [Walk.support_nil, List.mem_singleton] at hx
    subst hx
    exact ⟨x, hP, .nil, by simp, Or.inl ⟨rfl, rfl⟩⟩
  | @cons a b c hab q ih =>
    by_cases hPa : P a
    · exact ⟨a, hPa, .cons hab q, fun x hx => hx, Or.inl ⟨rfl, rfl⟩⟩
    · have h' : ∃ x ∈ q.support, P x := by
        obtain ⟨x, hx, hP⟩ := h
        simp only [Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd hP hPa
        · exact ⟨x, hx, hP⟩
      obtain ⟨z, hz, r, hr, hcase⟩ := ih h'
      have hr' : ∀ x ∈ r.support, x ∈ (Walk.cons hab q).support := fun x hx => by
        simp only [Walk.support_cons, List.mem_cons]; exact Or.inr (hr x hx)
      refine ⟨z, hz, r, hr', Or.inr ?_⟩
      rcases hcase with ⟨rfl, hlen⟩ | ⟨w, q', hwz, hq', hlen⟩
      · refine ⟨a, .nil, hab, ?_, by simp [hlen]; omega⟩
        intro x hx
        simp only [Walk.support_nil, List.mem_singleton] at hx
        subst hx
        exact ⟨hPa, by simp⟩
      · refine ⟨w, .cons hab q', hwz, ?_, by simp; omega⟩
        intro x hx
        simp only [Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨hPa, by simp⟩
        · exact ⟨(hq' x hx).1, by simp [(hq' x hx).2]⟩

end WalkAux


/-! ### The cluster hierarchy produced by Algorithm 1 -/

/-- The properties of the output of Algorithm 1 used by the stretch analysis (Section 2.2.2), for
an emulator `H` (weighted by `d_G`), accuracy `ε` and last phase `ℓ`. -/
structure Hierarchy (G H : SimpleGraph V) (ε : ℝ) (ℓ : ℕ) where
  /-- `v` lies in a cluster of `U_{lev v}`. -/
  lev : V → ℕ
  /-- `ctr i v` is the center of the cluster of `P_i` containing `v` (meaningful for
  `i ≤ lev v`). -/
  ctr : ℕ → V → V
  /-- `U^{(ℓ)}` is a partition of `V` (Lemma 2.8 and eq. (1)). -/
  lev_le : ∀ v, lev v ≤ ℓ
  /-- `P_0` consists of singletons. -/
  ctr_zero : ∀ v, ctr 0 v = v
  /-- **Lemma 2.5**: `d_H(r_C, v) ≤ R_i` for `v ∈ C ∈ P_i`. -/
  radius : ∀ i v, i ≤ lev v → HD G H (ctr i v) v (R ε i)
  /-- **Lemma 2.9** (laminarity): for `j ≤ i ≤ lev v`, the center of the `P_j`-cluster of `v`
  lies in the `P_i`-cluster of `v`. -/
  nest : ∀ j i v, j ≤ i → i ≤ lev v → i ≤ lev (ctr j v) ∧ ctr i (ctr j v) = ctr i v
  /-- **Lemma 2.7**: the center of a cluster of `U_i` is joined (by an edge of weight `d_G`) to
  every neighbouring cluster center of `P_i`. -/
  inter : ∀ i v w, lev v = i → i ≤ lev w → G.Reachable (ctr i v) (ctr i w) →
    (G.dist (ctr i v) (ctr i w) : ℝ) ≤ δ ε i →
    HD G H (ctr i v) (ctr i w) (G.dist (ctr i v) (ctr i w))
  /-- Emulator edges join vertices that are connected in `G`. -/
  reach : ∀ x y, H.Adj x y → G.Reachable x y

namespace Hierarchy

variable {ε : ℝ} {ℓ : ℕ} (C : Hierarchy G H ε ℓ)
include C

/-- Base case `i = 0` of Lemma 2.10: a walk all of whose vertices are `U_0`-clustered is
contained in `H`. -/
lemma lemma_2_10_zero {u v : V} (p : G.Walk u v) (hp : ∀ x ∈ p.support, C.lev x ≤ 0) :
    HD G H u v p.length := by
  induction p with
  | nil => simpa using HD.refl (G := G) (H := H) _
  | @cons a b c hab q ih =>
    have ha : C.lev a = 0 := Nat.le_zero.1 (hp a (by simp))
    have hd : G.dist a b = 1 := (dist_eq_one_iff_adj).2 hab
    have h1 := C.inter 0 a b ha (Nat.zero_le _) (by simpa [C.ctr_zero] using hab.reachable)
      (by simp [C.ctr_zero, hd, δ, R_zero])
    simp only [C.ctr_zero, hd, Nat.cast_one] at h1
    have h2 := ih (fun x hx => hp x (by simp [hx]))
    simpa [add_comm] using h1.trans h2 zero_le_one (Nat.cast_nonneg _)

/-- The bound (9) in the proof of Lemma 2.10: if `w` (which is `U^{(k)}`-clustered) is adjacent in
`G` to a `U_{k+1}`-clustered vertex `z`, then `d_H(w, r) ≤ 2R_{k+1}` for the center `r` of the
cluster of `z`. -/
lemma near_center (hε0 : 0 < ε) (hε1 : ε ≤ 1) {k : ℕ} {w z : V} (hwz : G.Adj w z)
    (hz : C.lev z = k + 1) (hw : C.lev w ≤ k) :
    HD G H w (C.ctr (k + 1) z) (2 * R ε (k + 1)) := by
  obtain ⟨j, hj⟩ : ∃ j, C.lev w = j := ⟨_, rfl⟩
  have hjk : j < k + 1 := by omega
  have hRj := R_nonneg hε0 j
  have hRk := R_nonneg hε0 (k + 1)
  have h1 : HD G H (C.ctr j w) w (R ε j) := C.radius j w hj.ge
  have h2 : HD G H (C.ctr j z) z (R ε j) := C.radius j z (by omega)
  obtain ⟨hr1, hd1⟩ := h1.dist_le C.reach hRj
  obtain ⟨hr2, hd2⟩ := h2.dist_le C.reach hRj
  have hreach : G.Reachable (C.ctr j w) (C.ctr j z) := (hr1.trans hwz.reachable).trans hr2.symm
  have hdist : (G.dist (C.ctr j w) (C.ctr j z) : ℝ) ≤ 2 * R ε j + 1 := by
    have t1 := hr1.dist_triangle_left (C.ctr j z)
    have t2 := hwz.reachable.dist_triangle_left (C.ctr j z)
    have e1 : G.dist w z = 1 := dist_eq_one_iff_adj.2 hwz
    have e2 : G.dist z (C.ctr j z) = G.dist (C.ctr j z) z := dist_comm
    have t3 : G.dist (C.ctr j w) (C.ctr j z) ≤ G.dist (C.ctr j w) w + (1 + G.dist (C.ctr j z) z) := by
      have := t1.trans (Nat.add_le_add_left t2 _); rwa [e1, e2] at this
    have t4 : (G.dist (C.ctr j w) (C.ctr j z) : ℝ) ≤
        G.dist (C.ctr j w) w + (1 + G.dist (C.ctr j z) z) := by exact_mod_cast t3
    linarith
  have h3 := C.inter j w z hj (by omega) hreach (hdist.trans (two_R_add_one_le_δ hε0 hε1 j))
  obtain ⟨hn1, hn2⟩ := C.nest j (k + 1) z (by omega) (by omega)
  have h4 : HD G H (C.ctr j z) (C.ctr (k + 1) z) (R ε (k + 1)) := by
    have := (C.radius (k + 1) (C.ctr j z) hn1).symm; rwa [hn2] at this
  have h5 := (h1.symm.trans (h3.mono hdist) hRj (by linarith)).trans h4 (by linarith) hRk
  exact h5.mono (by have := three_R_add_one_le hε0 hε1 hjk; linarith)

/-- One segment in the proof of Lemma 2.10 (Cases 1 and 2): a walk of length at most
`⌊(1/ε)^{k+1}⌋` whose vertices are `U^{(k+1)}`-clustered has
`d_H(x, y) ≤ α_k · |S| + 2β_k + 6R_{k+1}`. -/
lemma segment (hε0 : 0 < ε) (hε1 : ε ≤ 1) {k : ℕ}
    (ih : ∀ {u v : V} (p : G.Walk u v), (∀ x ∈ p.support, C.lev x ≤ k) →
      HD G H u v (alpha ε k * p.length + beta ε k))
    (hα : 1 ≤ alpha ε k) {u v : V} (p : G.Walk u v) (hp : ∀ x ∈ p.support, C.lev x ≤ k + 1)
    (hlen : p.length ≤ segLen ε (k + 1)) :
    HD G H u v (alpha ε k * p.length + beta ε (k + 1)) := by
  have hβk := beta_nonneg hε0 k
  have hR := R_nonneg hε0 (k + 1)
  have hβ : beta ε (k + 1) = 2 * beta ε k + 6 * R ε (k + 1) := rfl
  by_cases hex : ∃ x ∈ p.support, C.lev x = k + 1
  swap
  · -- Case 1
    push Not at hex
    have := ih p (fun x hx => by have := hp x hx; have := hex x hx; omega)
    exact this.mono (by linarith)
  -- Case 2: the first and the last `U_{k+1}`-clustered vertices `z₁`, `z₂`
  obtain ⟨z₁, hz₁, r, hr, hcase₁⟩ := WalkAux.exists_first (fun x => C.lev x = k + 1) p hex
  have hex' : ∃ x ∈ r.reverse.support, C.lev x = k + 1 := ⟨z₁, by simp, hz₁⟩
  obtain ⟨z₂, hz₂, m, hm, hcase₂⟩ :=
    WalkAux.exists_first (fun x => C.lev x = k + 1) r.reverse hex'
  have hrp : ∀ x ∈ r.reverse.support, x ∈ p.support := fun x hx =>
    hr x (by simpa using hx)
  -- left part: `d_H(u, r₁) ≤ α_k a + β_k + 2R_{k+1}`
  obtain ⟨a, ha, hL⟩ : ∃ a : ℕ, a + r.length ≤ p.length ∧
      HD G H u (C.ctr (k + 1) z₁) (alpha ε k * a + beta ε k + 2 * R ε (k + 1)) := by
    rcases hcase₁ with ⟨rfl, hl⟩ | ⟨w, q, hwz, hq, hl⟩
    · refine ⟨0, by omega, ?_⟩
      exact (C.radius (k + 1) u hz₁.ge).symm.mono (by simp; linarith)
    · refine ⟨q.length, by omega, ?_⟩
      have h1 := ih q (fun x hx => by
        have := hp x (hq x hx).2; have := (hq x hx).1; omega)
      have hw : C.lev w ≤ k := by
        have := hp w (hq w (by simp)).2; have := (hq w (by simp)).1; omega
      have h2 := C.near_center hε0 hε1 hwz hz₁ hw
      have := h1.trans h2 (by have := Nat.cast_nonneg (α := ℝ) q.length; nlinarith) (by linarith)
      exact this.mono (by linarith)
  -- right part: `d_H(r₂, v) ≤ α_k b + β_k + 2R_{k+1}`
  obtain ⟨b, hb, hRt⟩ : ∃ b : ℕ, m.length + b ≤ r.length ∧
      HD G H (C.ctr (k + 1) z₂) v (alpha ε k * b + beta ε k + 2 * R ε (k + 1)) := by
    rcases hcase₂ with ⟨rfl, hl⟩ | ⟨w, q, hwz, hq, hl⟩
    · refine ⟨0, by simp at hl; omega, ?_⟩
      exact (C.radius (k + 1) v hz₂.ge).mono (by simp; linarith)
    · refine ⟨q.length, by simp at hl; omega, ?_⟩
      have h1 := ih q (fun x hx => by
        have := hp x (hrp x (hq x hx).2); have := (hq x hx).1; omega)
      have hw : C.lev w ≤ k := by
        have := hp w (hrp w (hq w (by simp)).2); have := (hq w (by simp)).1; omega
      have h2 := C.near_center hε0 hε1 hwz hz₂ hw
      have := h1.trans h2 (by have := Nat.cast_nonneg (α := ℝ) q.length; nlinarith) (by linarith)
      exact this.symm.mono (by linarith)
  -- middle part: `d_H(r₁, r₂) = d_G(r₁, r₂) ≤ 2R_{k+1} + |m|`
  have hM : HD G H (C.ctr (k + 1) z₁) (C.ctr (k + 1) z₂) (2 * R ε (k + 1) + m.length) := by
    obtain ⟨hr1, hd1⟩ := (C.radius (k + 1) z₁ hz₁.ge).dist_le C.reach hR
    obtain ⟨hr2, hd2⟩ := (C.radius (k + 1) z₂ hz₂.ge).dist_le C.reach hR
    have hreach : G.Reachable (C.ctr (k + 1) z₁) (C.ctr (k + 1) z₂) :=
      (hr1.trans m.reverse.reachable).trans hr2.symm
    have hdist : (G.dist (C.ctr (k + 1) z₁) (C.ctr (k + 1) z₂) : ℝ) ≤
        2 * R ε (k + 1) + m.length := by
      have t1 := hr1.dist_triangle_left (C.ctr (k + 1) z₂)
      have t2 := m.reverse.reachable.dist_triangle_left (C.ctr (k + 1) z₂)
      have e1 : G.dist z₁ z₂ ≤ m.length := by simpa using SimpleGraph.dist_le m.reverse
      have e2 : G.dist z₂ (C.ctr (k + 1) z₂) = G.dist (C.ctr (k + 1) z₂) z₂ := dist_comm
      have t3 : G.dist (C.ctr (k + 1) z₁) (C.ctr (k + 1) z₂) ≤
          G.dist (C.ctr (k + 1) z₁) z₁ + (m.length + G.dist (C.ctr (k + 1) z₂) z₂) := by
        rw [e2] at t2; omega
      have t4 : (G.dist (C.ctr (k + 1) z₁) (C.ctr (k + 1) z₂) : ℝ) ≤
          G.dist (C.ctr (k + 1) z₁) z₁ + (m.length + G.dist (C.ctr (k + 1) z₂) z₂) := by
        exact_mod_cast t3
      linarith
    have hδ : (G.dist (C.ctr (k + 1) z₁) (C.ctr (k + 1) z₂) : ℝ) ≤ δ ε (k + 1) := by
      have h1 : (m.length : ℝ) ≤ segLen ε (k + 1) := by
        have : m.length ≤ p.length := by
          rcases hcase₁ with ⟨_, hl⟩ | ⟨_, _, _, _, hl⟩ <;> omega
        exact_mod_cast this.trans hlen
      have := segLen_add_le_δ hε0 (k + 1)
      linarith
    exact (C.inter (k + 1) z₁ z₂ hz₁ hz₂.ge hreach hδ).mono hdist
  have hm0 := Nat.cast_nonneg (α := ℝ) m.length
  have ha0 := Nat.cast_nonneg (α := ℝ) a
  have hb0 := Nat.cast_nonneg (α := ℝ) b
  have htot := (hL.trans hM (by nlinarith) (by linarith)).trans hRt (by nlinarith) (by nlinarith)
  refine htot.mono ?_
  have hsum : (a : ℝ) + m.length + b ≤ p.length := by
    have : a + m.length + b ≤ p.length := by omega
    exact_mod_cast this
  nlinarith

/-- Several segments: a walk of length at most `(m+1)⌊(1/ε)^{k+1}⌋` has
`d_H ≤ α_k · |p| + (m+1) β_{k+1}`. -/
lemma segments (hε0 : 0 < ε) (hε1 : ε ≤ 1) {k : ℕ}
    (ih : ∀ {u v : V} (p : G.Walk u v), (∀ x ∈ p.support, C.lev x ≤ k) →
      HD G H u v (alpha ε k * p.length + beta ε k))
    (hα : 1 ≤ alpha ε k) (m : ℕ) :
    ∀ {u v : V} (p : G.Walk u v), (∀ x ∈ p.support, C.lev x ≤ k + 1) →
      p.length ≤ (m + 1) * segLen ε (k + 1) →
      HD G H u v (alpha ε k * p.length + beta ε (k + 1) * (m + 1)) := by
  have hβ : 0 ≤ beta ε (k + 1) := beta_nonneg hε0 (k + 1)
  induction m with
  | zero =>
    intro u v p hp hlen
    exact (C.segment hε0 hε1 ih hα p hp (by simpa using hlen)).mono (by simp)
  | succ m ihm =>
    intro u v p hp hlen
    by_cases hshort : p.length ≤ segLen ε (k + 1)
    · exact (C.segment hε0 hε1 ih hα p hp hshort).mono (by push_cast; nlinarith)
    · obtain ⟨w, p₁, p₂, h1, h2, h3, h4⟩ :=
        WalkAux.exists_split p (segLen ε (k + 1)) (by omega)
      have hA := C.segment hε0 hε1 ih hα p₁ (fun x hx => hp x (h3 x hx)) (by omega)
      have hB := ihm p₂ (fun x hx => hp x (h4 x hx)) (by
        have : p₂.length = p.length - segLen ε (k + 1) := by omega
        rw [this, Nat.sub_le_iff_le_add]; nlinarith)
      have hl : (p₁.length : ℝ) + p₂.length = p.length := by exact_mod_cast h2
      have := hA.trans hB (by have := Nat.cast_nonneg (α := ℝ) p₁.length; nlinarith)
        (by have := Nat.cast_nonneg (α := ℝ) p₂.length; nlinarith)
      refine this.mono (le_of_eq ?_)
      push_cast
      rw [← hl]; ring

/-- **Lemma 2.10.** If all vertices of a walk `p` from `u` to `v` are `U^{(i)}`-clustered, then
`d_H(u, v) ≤ α_i · |p| + β_i`. (The paper states it for a shortest path `π(u, v)` and the minimal
such `i`; this version, for all walks and all such `i`, implies it.) -/
theorem lemma_2_10 (hε0 : 0 < ε) (hε1 : ε < 1) (i : ℕ) :
    ∀ {u v : V} (p : G.Walk u v), (∀ x ∈ p.support, C.lev x ≤ i) →
      HD G H u v (alpha ε i * p.length + beta ε i) := by
  induction i with
  | zero =>
    intro u v p hp
    simpa [alpha, beta] using C.lemma_2_10_zero p hp
  | succ k ih =>
    intro u v p hp
    have hα := one_le_alpha hε0 hε1 k
    have hβ := beta_nonneg hε0 (k + 1)
    have hL := one_le_segLen hε0 hε1.le (k + 1)
    by_cases h0 : p.length = 0
    · obtain rfl := Walk.eq_of_length_eq_zero h0
      rw [h0]
      exact (HD.refl u).mono (by simpa using hβ)
    set L := segLen ε (k + 1) with hLdef
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    set c := ⌈(p.length : ℝ) / L⌉₊ with hc
    have hcpos : 0 < c := Nat.ceil_pos.2 (by positivity)
    obtain ⟨m, hm⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
    have hlen : p.length ≤ (m + 1) * L := by
      have h1 : (p.length : ℝ) / L ≤ c := Nat.le_ceil _
      have h2 : (p.length : ℝ) ≤ c * L := by rwa [div_le_iff₀ hLpos] at h1
      rw [← hm]; exact_mod_cast h2
    have hcm : ((m : ℝ) + 1) ≤ p.length / L + 1 := by
      have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ p.length / L by positivity)
      rw [← hc, hm] at this; push_cast at this; linarith
    have hinv := inv_segLen_le hε0 hε1 (i := k + 1) (by omega)
    have h := C.segments hε0 hε1.le (fun q hq => ih q hq) hα m p hp hlen
    refine h.mono ?_
    have hpl := Nat.cast_nonneg (α := ℝ) p.length
    have key : beta ε (k + 1) * (m + 1) ≤
        ε ^ (k + 1) / (1 - ε ^ (k + 1)) * beta ε (k + 1) * p.length + beta ε (k + 1) := by
      have e1 : beta ε (k + 1) * (m + 1) ≤ beta ε (k + 1) * (p.length / L + 1) :=
        mul_le_mul_of_nonneg_left hcm hβ
      have e2 : (p.length : ℝ) / L = p.length * (1 / L) := by ring
      have e3 : (p.length : ℝ) * (1 / L) ≤ p.length * (ε ^ (k + 1) / (1 - ε ^ (k + 1))) :=
        mul_le_mul_of_nonneg_left hinv hpl
      nlinarith
    simp only [alpha]
    nlinarith

/-- **Corollary 2.11.** `H` is an `(α_ℓ, β_ℓ)`-emulator of `G`. -/
theorem isEmulator (hε0 : 0 < ε) (hε1 : ε < 1) :
    G.IsEmulator H G.distW (alpha ε ℓ) (beta ε ℓ) := by
  have hα := one_le_alpha hε0 hε1 ℓ
  have hβ := beta_nonneg hε0 ℓ
  intro u v
  refine ⟨edist_le_wdist_distW C.reach u v, ?_⟩
  by_cases huv : G.Reachable u v
  · obtain ⟨p, hp⟩ := huv.exists_walk_length_eq_dist
    have h := C.lemma_2_10 hε0 hε1 ℓ p (fun x _ => C.lev_le x)
    rw [hp] at h
    refine le_trans h (le_of_eq ?_)
    rw [← huv.coe_dist_eq_edist, ENNReal.ofReal_add (by positivity) hβ,
      ENNReal.ofReal_mul (by linarith)]
    simp
  · rw [edist_eq_top_of_not_reachable huv]
    have : ENNReal.ofReal (alpha ε ℓ) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero]; linarith
    simp [ENNReal.mul_top this]

end Hierarchy

end Podc.UltraSparseEmulators
