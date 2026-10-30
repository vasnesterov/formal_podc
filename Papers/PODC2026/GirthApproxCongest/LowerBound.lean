import Papers.PODC2026.GirthApproxCongest.Network
import Papers.PODC2024.MinWeightCycleCongest.LowerBound

/-!
# Theorem 6.1 and its weighted / general-`k` versions, for fixed parameters

For a bipartite graph `H` (edge set `E`, girth `≥ 2k`), `q ≥ 2` layers and a shortcut tree of
depth `d` (`q ≤ 2^d`), every CONGEST algorithm with `B`-bit messages that approximates the girth
within `T` rounds on all networks of the right shape satisfies

  `q ≤ 2T + 1`   or   `|E| ≤ T · 2 (d + 1) B + 2`,

i.e. `T = Ω(min(q, |E| / (B log q)))` — the bound `Ω̃(min(q, m))` of Theorem 6.1.

* `approx_movingCut_lowerBound`, `approx_movingCut_rand_lowerBound`: the gap reduction through
  the moving-cut simulation (deterministic; randomized conditional on the public-coin randomized
  communication lower bound for set disjointness, `PubRandDisjLB`).
* `theorem_6_1_family` (directed, deterministic), `theorem_6_1_family_rand` (randomized),
  `theorem_6_1_weighted_family` and `_rand` (undirected weighted, §6.1).
-/

namespace Podc.GirthApproxCongest

open Finset Podc.MinWeightCycleCongest Cslib.Congest Cslib.CommunicationComplexity
  Cslib.CommunicationComplexity.Protocol

open scoped ENNReal

/-! ### Gap reductions through the moving cut -/

section Approx

variable {V I σ : Type*} {B : ℕ}

-- CSLib candidate (with `PubRandDisjLB` and the randomized version below)
/-- **Gap lower bound through a moving cut (deterministic).** -/
theorem approx_movingCut_lowerBound {ι : Type*} [Fintype ι] [Fintype V]
    (F : MovingCutFamily (ι → Bool) (ι → Bool) V I) [∀ x y, DecidableRel (F.G x y).Adj]
    (A : Algorithm V I σ B) (est : V → σ → Option ℝ≥0∞) (T D : ℕ)
    (hDA : ∀ t, (F.toA t).card ≤ D) (hDB : ∀ t, (F.toB t).card ≤ D)
    (hcover : ∀ v, T < F.ka v ∨ T < F.kb v) {α a b : ℝ≥0∞}
    (hab : α * a < b) (opt : (ι → Bool) → (ι → Bool) → ℝ≥0∞)
    (hA : ∀ x y, ApproxOutput α (opt x y) (outputs A est (F.G x y) (F.inp x y) T))
    (hint : ∀ x y, (∃ i, x i = true ∧ y i = true) → opt x y ≤ a)
    (hdisj : ∀ x y, (∀ i, ¬ (x i = true ∧ y i = true)) → b ≤ opt x y) :
    Fintype.card ι ≤ T * (2 * (D * B)) + 2 := by
  refine F.not_disj_lowerBound (thresholdAlg A est b) T D hDA hDB hcover fun x y => ?_
  have h := thresholdAlg_accepts A est hab (F.G x y) (F.inp x y) T (hA x y)
  by_cases hq : ∃ i, x i = true ∧ y i = true
  · have hd : disj x y = false := disj_false_iff.2 hq
    simp only [hd, iff_true]
    exact h.1 (hint x y hq)
  · have hq' : ∀ i, ¬ (x i = true ∧ y i = true) := fun i h' => hq ⟨i, h'⟩
    have hd : disj x y = true := disj_true_iff.2 hq'
    simp only [hd, Bool.true_eq_false, iff_false]
    exact h.2 (hdisj x y hq')

/-- The public-coin randomized communication lower bound for set disjointness, as a hypothesis:
every public-coin protocol (shared uniform random string from a nonempty finite set `R`) that
computes "the sets intersect" with error at most `δ` on every input exchanges at least `κ · K`
bits. (Razborov / Kalyanasundaram–Schnitger: true for `δ = 1/3` and some `κ > 0`; not
formalized.) The moving-cut simulation needs public coins because the nodes in the middle of the
pipes are simulated by both players. -/
def PubRandDisjLB (δ κ : ℝ) : Prop :=
  ∀ (ι R : Type) [Fintype ι] [Fintype R] [Nonempty R]
    (P : R → Protocol (ι → Bool) (ι → Bool) Bool) (c : ℕ),
    (∀ r, (P r).CostLE c) → PubRandComputes P (fun x y => !disj x y) δ → κ * Fintype.card ι ≤ c

/-- **Gap lower bound through a moving cut (randomized).** -/
theorem approx_movingCut_rand_lowerBound {ι ρ : Type} [Fintype ι] {V : Type} [Fintype V]
    [DecidableEq V] [Fintype ρ] [Nonempty ρ]
    (F : MovingCutFamily (ι → Bool) (ι → Bool) V I) [∀ x y, DecidableRel (F.G x y).Adj]
    (A : Algorithm V (I × ρ) σ B) (est : V → σ → Option ℝ≥0∞) (T D : ℕ)
    (hDA : ∀ t, (F.toA t).card ≤ D) (hDB : ∀ t, (F.toB t).card ≤ D)
    (hcover : ∀ v, T < F.ka v ∨ T < F.kb v) {α a b : ℝ≥0∞}
    (hab : α * a < b) (opt : (ι → Bool) → (ι → Bool) → ℝ≥0∞) {δ κ : ℝ}
    (hDisj : PubRandDisjLB δ κ)
    (hA : ∀ x y, (failCount A est (F.G x y) (F.inp x y) T α (opt x y) : ℝ) ≤
      δ * Fintype.card (V → ρ))
    (hint : ∀ x y, (∃ i, x i = true ∧ y i = true) → opt x y ≤ a)
    (hdisj : ∀ x y, (∀ i, ¬ (x i = true ∧ y i = true)) → b ≤ opt x y) :
    κ * Fintype.card ι ≤ T * (2 * (D * B)) + 2 := by
  classical
  have h := F.rand_lowerBound (thresholdAlg A est b) T D hDA hDB hcover (fun x y => !disj x y) δ
    (fun x y => le_trans ?_ (hA x y)) ⌈κ * Fintype.card ι⌉₊
    (fun P c hc hP => Nat.ceil_le.2 (hDisj ι (V → ρ) P c hc hP))
  · exact (Nat.le_ceil _).trans (by exact_mod_cast h)
  simp only [failCount]
  norm_cast
  refine Finset.card_le_card fun r => ?_
  simp only [mem_filter, mem_univ, true_and]
  intro hr hok
  apply hr
  have h := thresholdAlg_accepts A est hab (F.G x y) (fun v => (F.inp x y v, r v)) T hok
  by_cases hq : ∃ i, x i = true ∧ y i = true
  · have hd : disj x y = false := disj_false_iff.2 hq
    simp [hd, h.1 (hint x y hq)]
  · have hq' : ∀ i, ¬ (x i = true ∧ y i = true) := fun i h' => hq ⟨i, h'⟩
    have hd : disj x y = true := disj_true_iff.2 hq'
    simp [hd, h.2 (hdisj x y hq')]

end Approx

/-! ### The concrete families -/

variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R] {q d p : ℕ}
  {E : Finset (L × R)} {V : Type*} [Fintype V] [DecidableEq V] (e : V ≃ Vtx L R q d p)

section Directed

variable {W : ℕ}

lemma dComap_adj (x y : E → Bool) (a b : V) :
    ((dGraph (q := q) (d := d) (p := p) W x y).comap e).net.Adj a b ↔
      a ≠ b ∧ (darc E x y (e a) (e b) ∨ darc E x y (e b) (e a)) := by
  simp [WDigraph.net, WDigraph.comap, dGraph_isSome]

/-- The directed family as a moving-cut family. -/
def dFamily (T : ℕ) (hT : 2 * T + 2 ≤ q) : MovingCutFamily (E → Bool) (E → Bool) V
    (V → Option (Fin (W + 2)) × Option (Fin (W + 2))) :=
  gadgetFamily e T hT (fun x y => ((dGraph (q := q) (d := d) (p := p) W x y).comap e).net)
    (fun x y => ((dGraph W x y).comap e).view) (dComap_adj e)
    (fun x y y' v hv => by
      funext u
      have h1 := darc_indep_y (E := E) (q := q) (d := d) (p := p) x y y' (u := e v) (v := e u)
        (Or.inl hv)
      have h2 := darc_indep_y (E := E) (q := q) (d := d) (p := p) x y y' (u := e u) (v := e v)
        (Or.inr hv)
      simp only [WDigraph.view, WDigraph.comap, dGraph, h1, h2])
    (fun x x' y v hv => by
      funext u
      have h1 := darc_indep_x (E := E) (q := q) (d := d) (p := p) x x' y (u := e v) (v := e u)
        (Or.inl hv)
      have h2 := darc_indep_x (E := E) (q := q) (d := d) (p := p) x x' y (u := e u) (v := e v)
        (Or.inr hv)
      simp only [WDigraph.view, WDigraph.comap, dGraph, h1, h2])

instance (T : ℕ) (hT : 2 * T + 2 ≤ q) (x y : E → Bool) :
    DecidableRel ((dFamily (W := W) e T hT).G x y).Adj :=
  inferInstanceAs (DecidableRel ((dGraph (q := q) (d := d) (p := p) W x y).comap e).net.Adj)

omit [Fintype L] [Fintype R] [Fintype V] [DecidableEq V] in
lemma dComap_unweighted (x y : E → Bool) :
    ((dGraph (q := q) (d := d) (p := p) W x y).comap e).Unweighted :=
  fun u v c h => dGraph_unweighted _ _ c h

lemma dComap_ediam (hqd : q ≤ 2 ^ d) (hq : 0 < q) (x y : E → Bool) :
    ((dGraph (q := q) (d := d) (p := p) W x y).comap e).net.ediam ≤ 2 * (d + 1) :=
  ediam_le e (dComap_adj e x y) hqd hq

include e in
/-- The directed lower bound for given gap values `a`, `b` of the girth (`α · a < b`). -/
theorem dir_lowerBound_of_gap {σ : Type*} {B T : ℕ} (hqd : q ≤ 2 ^ d)
    (A : Algorithm V (DInput V (W + 1)) σ B) (est : V → σ → Option ℝ≥0∞) {α a b : ℝ≥0∞}
    (hab : α * a < b)
    (hint : ∀ x y : E → Bool, (∃ i, x i = true ∧ y i = true) →
      (dGraph (q := q) (d := d) (p := p) W x y).mwc ≤ a)
    (hdisj : ∀ x y : E → Bool, (∀ i, ¬ (x i = true ∧ y i = true)) →
      b ≤ (dGraph (q := q) (d := d) (p := p) W x y).mwc)
    (hA : ∀ D : WDigraph V (W + 1), D.Unweighted → D.net.ediam ≤ 2 * (d + 1) →
      ApproxOutput α D.mwc (outputs A est D.net D.view T)) :
    q ≤ 2 * T + 1 ∨ E.card ≤ T * (2 * ((d + 1) * B)) + 2 := by
  by_cases hT : 2 * T + 2 ≤ q
  · right
    have h := approx_movingCut_lowerBound (dFamily (W := W) e T hT) A est T (d + 1)
      (card_toA_le e (by omega) T) (card_toB_le e (by omega) T) (fun v => cover e T hT v) hab
      (fun x y => (dGraph (q := q) (d := d) (p := p) W x y).mwc)
      (fun x y => by
        have := hA _ (dComap_unweighted e x y) (dComap_ediam e hqd (by omega) x y)
        rwa [WDigraph.mwc_comap] at this)
      hint hdisj
    simpa using h
  · left; omega

/-- The directed lower bound for randomized algorithms, given the gap values. -/
theorem dir_rand_lowerBound_of_gap {L R : Type} [DecidableEq L] [DecidableEq R] [Fintype L]
    [Fintype R] {E : Finset (L × R)} {V ρ σ : Type} [Fintype V] [DecidableEq V] [Fintype ρ]
    [Nonempty ρ] (e : V ≃ Vtx L R q d p) {B T : ℕ} (hqd : q ≤ 2 ^ d)
    (A : Algorithm V (DInput V (W + 1) × ρ) σ B) (est : V → σ → Option ℝ≥0∞) {α a b : ℝ≥0∞}
    (hab : α * a < b) {δ κ : ℝ} (hDisj : PubRandDisjLB δ κ)
    (hint : ∀ x y : E → Bool, (∃ i, x i = true ∧ y i = true) →
      (dGraph (q := q) (d := d) (p := p) W x y).mwc ≤ a)
    (hdisj : ∀ x y : E → Bool, (∀ i, ¬ (x i = true ∧ y i = true)) →
      b ≤ (dGraph (q := q) (d := d) (p := p) W x y).mwc)
    (hA : ∀ D : WDigraph V (W + 1), D.Unweighted → D.net.ediam ≤ 2 * (d + 1) →
      (failCount A est D.net D.view T α D.mwc : ℝ) ≤ δ * Fintype.card (V → ρ)) :
    q ≤ 2 * T + 1 ∨ κ * E.card ≤ T * (2 * ((d + 1) * B)) + 2 := by
  by_cases hT : 2 * T + 2 ≤ q
  · right
    have h := approx_movingCut_rand_lowerBound (dFamily (W := W) e T hT) A est T (d + 1)
      (card_toA_le e (by omega) T) (card_toB_le e (by omega) T) (fun v => cover e T hT v) hab
      (fun x y => (dGraph (q := q) (d := d) (p := p) W x y).mwc) hDisj
      (fun x y => by
        have := hA _ (dComap_unweighted e x y) (dComap_ediam e hqd (by omega) x y)
        rwa [WDigraph.mwc_comap] at this)
      hint hdisj
    simpa using h
  · left; omega

end Directed

section Undirected

variable {Wm Win Wt : ℕ}

omit [Fintype L] [Fintype R] [Fintype V] in
lemma uComap_adj (x y : E → Bool) (a b : V) :
    ((uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).comap e.toEmbedding).net.Adj a b ↔
      a ≠ b ∧ (darc E x y (e a) (e b) ∨ darc E x y (e b) (e a)) := by
  simp only [WGraph.net, WGraph.comap, Equiv.coe_toEmbedding, SimpleGraph.fromRel_adj,
    uGraph_isSome]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by tauto⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by tauto⟩

/-- The undirected weighted family as a moving-cut family. -/
def uFamily (T : ℕ) (hT : 2 * T + 2 ≤ q) : MovingCutFamily (E → Bool) (E → Bool) V
    (V → Option (Fin (Wm + 1))) :=
  gadgetFamily e T hT
    (fun x y => ((uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).comap e.toEmbedding).net)
    (fun x y => ((uGraph Wm Win Wt x y).comap e.toEmbedding).view) (uComap_adj e)
    (fun x y y' v hv => by
      funext u
      have h1 := darc_indep_y (E := E) (q := q) (d := d) (p := p) x y y' (u := e v) (v := e u)
        (Or.inl hv)
      have h2 := darc_indep_y (E := E) (q := q) (d := d) (p := p) x y y' (u := e u) (v := e v)
        (Or.inr hv)
      simp only [WGraph.view, WGraph.comap, Equiv.coe_toEmbedding, uGraph, h1, h2])
    (fun x x' y v hv => by
      funext u
      have h1 := darc_indep_x (E := E) (q := q) (d := d) (p := p) x x' y (u := e v) (v := e u)
        (Or.inl hv)
      have h2 := darc_indep_x (E := E) (q := q) (d := d) (p := p) x x' y (u := e u) (v := e v)
        (Or.inr hv)
      simp only [WGraph.view, WGraph.comap, Equiv.coe_toEmbedding, uGraph, h1, h2])

instance (T : ℕ) (hT : 2 * T + 2 ≤ q) (x y : E → Bool) :
    DecidableRel ((uFamily (Wm := Wm) (Win := Win) (Wt := Wt) e T hT).G x y).Adj :=
  inferInstanceAs (DecidableRel
    ((uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).comap e.toEmbedding).net.Adj)

lemma uComap_ediam (hqd : q ≤ 2 ^ d) (hq : 0 < q) (x y : E → Bool) :
    ((uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).comap e.toEmbedding).net.ediam ≤
      2 * (d + 1) :=
  ediam_le e (uComap_adj e x y) hqd hq

omit [Fintype L] [Fintype R] [Fintype V] [DecidableEq V] in
/-- The graphs of §6.1 have positive weights when `Win, Wt ≥ 1`. -/
lemma uComap_pos (hW : Win ≤ Wm) (hWt : Wt ≤ Wm) (hWin : 1 ≤ Win) (hWt1 : 1 ≤ Wt)
    (x y : E → Bool) (u v : V) (c : Fin (Wm + 1))
    (h : ((uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).comap e.toEmbedding).wt u v =
      some c) : 0 < c.val := by
  simp only [WGraph.comap, Equiv.coe_toEmbedding, uGraph] at h
  split_ifs at h with h'
  cases h
  have hle : 1 ≤ ew Win Wt (e u) (e v) ∧ ew Win Wt (e u) (e v) ≤ Wm := by
    unfold ew; split_ifs <;> omega
  simp only [Fin.val_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

include e in
/-- The undirected weighted lower bound for given gap values `a`, `b` of the girth. -/
theorem undir_lowerBound_of_gap {σ : Type*} {B T : ℕ} (hqd : q ≤ 2 ^ d)
    (A : Algorithm V (V → Option (Fin (Wm + 1))) σ B) (est : V → σ → Option ℝ≥0∞)
    {α a b : ℝ≥0∞} (hab : α * a < b)
    (hint : ∀ x y : E → Bool, (∃ i, x i = true ∧ y i = true) →
      (uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).mwc ≤ a)
    (hdisj : ∀ x y : E → Bool, (∀ i, ¬ (x i = true ∧ y i = true)) →
      b ≤ (uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).mwc)
    (hW : Win ≤ Wm) (hWt : Wt ≤ Wm) (hWin : 1 ≤ Win) (hWt1 : 1 ≤ Wt)
    (hA : ∀ G : WGraph V Wm, (∀ u v c, G.wt u v = some c → 0 < c.val) →
      G.net.ediam ≤ 2 * (d + 1) →
      ApproxOutput α G.mwc (outputs A est G.net G.view T)) :
    q ≤ 2 * T + 1 ∨ E.card ≤ T * (2 * ((d + 1) * B)) + 2 := by
  by_cases hT : 2 * T + 2 ≤ q
  · right
    have h := approx_movingCut_lowerBound (uFamily (Wm := Wm) (Win := Win) (Wt := Wt) e T hT)
      A est T (d + 1) (card_toA_le e (by omega) T) (card_toB_le e (by omega) T)
      (fun v => cover e T hT v) hab
      (fun x y => (uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).mwc)
      (fun x y => by
        have := hA _ (uComap_pos e hW hWt hWin hWt1 x y)
          (uComap_ediam (Win := Win) (Wt := Wt) e hqd (by omega) x y)
        rwa [WGraph.mwc_comap] at this)
      hint hdisj
    simpa using h
  · left; omega

/-- The undirected weighted lower bound for randomized algorithms, given the gap values. -/
theorem undir_rand_lowerBound_of_gap {L R : Type} [DecidableEq L] [DecidableEq R] [Fintype L]
    [Fintype R] {E : Finset (L × R)} {V ρ σ : Type} [Fintype V] [DecidableEq V] [Fintype ρ]
    [Nonempty ρ] (e : V ≃ Vtx L R q d p) {B T : ℕ} (hqd : q ≤ 2 ^ d)
    (A : Algorithm V ((V → Option (Fin (Wm + 1))) × ρ) σ B) (est : V → σ → Option ℝ≥0∞)
    {α a b : ℝ≥0∞} (hab : α * a < b) {δ κ : ℝ} (hDisj : PubRandDisjLB δ κ)
    (hint : ∀ x y : E → Bool, (∃ i, x i = true ∧ y i = true) →
      (uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).mwc ≤ a)
    (hdisj : ∀ x y : E → Bool, (∀ i, ¬ (x i = true ∧ y i = true)) →
      b ≤ (uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).mwc)
    (hW : Win ≤ Wm) (hWt : Wt ≤ Wm) (hWin : 1 ≤ Win) (hWt1 : 1 ≤ Wt)
    (hA : ∀ G : WGraph V Wm, (∀ u v c, G.wt u v = some c → 0 < c.val) →
      G.net.ediam ≤ 2 * (d + 1) →
      (failCount A est G.net G.view T α G.mwc : ℝ) ≤ δ * Fintype.card (V → ρ)) :
    q ≤ 2 * T + 1 ∨ κ * E.card ≤ T * (2 * ((d + 1) * B)) + 2 := by
  by_cases hT : 2 * T + 2 ≤ q
  · right
    have h := approx_movingCut_rand_lowerBound
      (uFamily (Wm := Wm) (Win := Win) (Wt := Wt) e T hT) A est T (d + 1)
      (card_toA_le e (by omega) T) (card_toB_le e (by omega) T) (fun v => cover e T hT v) hab
      (fun x y => (uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).mwc) hDisj
      (fun x y => by
        have := hA _ (uComap_pos e hW hWt hWin hWt1 x y)
          (uComap_ediam (Win := Win) (Wt := Wt) e hqd (by omega) x y)
        rwa [WGraph.mwc_comap] at this)
      hint hdisj
    simpa using h
  · left; omega

end Undirected

end Podc.GirthApproxCongest
