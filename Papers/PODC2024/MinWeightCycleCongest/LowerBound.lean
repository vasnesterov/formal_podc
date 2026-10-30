import Papers.PODC2024.MinWeightCycleCongest.Reduction

/-!
# Theorems 1.2.A and 1.4.A: `Ω(n / log n)` rounds for `(2 - ε)`-approximate MWC

Manoharan, Ramachandran. *Computing Minimum Weight Cycle in the CONGEST Model.* PODC 2024.

* `theorem_1_2_A`: every deterministic CONGEST algorithm with `B`-bit messages that, within `T`
  rounds, outputs an `α`-approximation (`α < 2`) of the minimum weight cycle of every unweighted
  directed `n`-node graph whose underlying network has diameter `≤ 2`, satisfies
  `n ≤ 32 · B · T + 12`. With `B = Θ(log n)` this is `T = Ω(n / log n)`.
* `theorem_1_4_A`: the same for undirected weighted graphs (weights in `{0, …, W}`, `W ≥ W₀(α)`).
* `theorem_1_2_A_rand`, `theorem_1_4_A_rand`: randomized versions (error `δ`), conditional on the
  randomized communication lower bound for set disjointness (`RandDisjLB`, Razborov /
  Kalyanasundaram–Schnitger), which is not formalized.
* `directed_four_cycle_lowerBound`: the same bound for detecting a directed `4`-cycle (§1.2.1).

The lower-bound graphs have `n = 4k + 1 + p` vertices and `4k` cut edges, and encode set
disjointness on `k²` bits (`Vtx`, `dGraph`, `uGraph`).
-/

namespace Podc.MinWeightCycleCongest

open Finset Cslib.Congest Cslib.CommunicationComplexity Cslib.CommunicationComplexity.Protocol
open Vtx

open scoped ENNReal

variable {k p : ℕ}

/-! ### The partition and the cut -/

/-- Alice simulates `L ∪ L' ∪ {hub} ∪ pads`, Bob simulates `R ∪ R'`. -/
def aliceV : Vtx k p → Bool
  | .r _ => false
  | .r' _ => false
  | _ => true

/-- The `4k` potential cut edges `ℓ_i r_i`, `ℓ'_i r'_i`, `hub r_i`, `hub r'_i`. -/
def cutV : Finset (Vtx k p × Vtx k p) :=
  univ.image (fun i => (l i, r i)) ∪ univ.image (fun i => (l' i, r' i)) ∪
    univ.image (fun i => (hub, r i)) ∪ univ.image (fun i => (hub, r' i))

lemma card_cutV : (cutV (k := k) (p := p)).card ≤ 4 * k := by
  unfold cutV
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right ((card_union_le _ _).trans (Nat.add_le_add_right
    (card_union_le _ _) _)) _).trans ?_
  have h : ∀ f : Fin k → Vtx k p × Vtx k p, (univ.image f).card ≤ k := fun f =>
    card_image_le.trans (by simp)
  have := h fun i => (l i, r i)
  have := h fun i => (l' i, r' i)
  have := h fun i => (hub, r i)
  have := h fun i => (hub, r' i)
  omega

lemma cutV_sub {q : Vtx k p × Vtx k p} (h : q ∈ cutV) :
    aliceV q.1 = true ∧ aliceV q.2 = false := by
  simp only [cutV, mem_union, mem_image, mem_univ, true_and] at h
  rcases h with ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩ <;> simp [aliceV]

lemma mem_cutV {a b : Vtx k p} (h : (a = .l i ∧ b = .r i) ∨ (a = .l' i ∧ b = .r' i) ∨
    (a = .hub ∧ b = .r i) ∨ (a = .hub ∧ b = .r' i)) : (a, b) ∈ cutV := by
  simp only [cutV, mem_union, mem_image, mem_univ, true_and]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-! ### Directed family -/

section Directed

variable {W : ℕ} {x x' y y' : Fin k × Fin k → Bool}

lemma darc_indep_y {u v : Vtx k p} (h : aliceV u = true ∨ aliceV v = true) :
    darc x y u v ↔ darc x y' u v := by
  cases u <;> cases v <;> simp_all [darc, aliceV]

lemma darc_indep_x {u v : Vtx k p} (h : aliceV u = false ∨ aliceV v = false) :
    darc x y u v ↔ darc x' y u v := by
  cases u <;> cases v <;> simp_all [darc, aliceV]

lemma darc_cut {a b : Vtx k p} (ha : aliceV a = true) (hb : aliceV b = false)
    (h : darc x y a b ∨ darc x y b a) : (a, b) ∈ cutV := by
  cases a <;> cases b <;> simp_all [darc, aliceV, cutV]

variable {V : Type*}

/-- The directed lower-bound family, relabelled along `e : V ≃ Vtx k p`. -/
def dFamily (W : ℕ) (e : V ≃ Vtx k p) : LBFamily (Fin k × Fin k → Bool) (Fin k × Fin k → Bool) V
    (V → Option (Fin (W + 2)) × Option (Fin (W + 2))) :=
  ofWeights (fun x y u v => (dGraph W x y).wt (e u) (e v)) (fun f g u => (f u, g u))
    (fun v => aliceV (e v)) (cutV.map (e.prodCongr e).symm.toEmbedding)
    (fun q hq => by
      rw [mem_map_equiv, Equiv.symm_symm] at hq
      exact cutV_sub hq)
    (fun x y a b ha hb h => by
      rw [mem_map_equiv, Equiv.symm_symm]
      simp only [dGraph_isSome] at h
      exact darc_cut ha hb h)
    (fun x y y' u v h => by simp only [dGraph, darc_indep_y (y' := y') h])
    (fun x x' y u v h => by simp only [dGraph, darc_indep_x (x' := x') h])

instance [DecidableEq V] (e : V ≃ Vtx k p) (x y : Fin k × Fin k → Bool) :
    DecidableRel ((dFamily W e).G x y).Adj :=
  inferInstanceAs (DecidableRel ((dGraph W x y).comap e).net.Adj)

lemma dFamily_G (e : V ≃ Vtx k p) : (dFamily W e).G x y = ((dGraph W x y).comap e).net := rfl

lemma dFamily_inp (e : V ≃ Vtx k p) : (dFamily W e).inp x y = ((dGraph W x y).comap e).view := rfl

lemma dFamily_card (e : V ≃ Vtx k p) : (dFamily W e).Ecut.card ≤ 4 * k := by
  simp only [dFamily, ofWeights, card_map]; exact card_cutV

lemma dComap_unweighted (e : V ≃ Vtx k p) : ((dGraph W x y).comap e).Unweighted :=
  fun u v c h => dGraph_unweighted (e u) (e v) c h

lemma dComap_ediam (e : V ≃ Vtx k p) : ((dGraph W x y).comap e).net.ediam ≤ 2 := by
  refine ediam_le_two_of_hub (e.symm .hub) fun v hv => ?_
  rw [WDigraph.net, SimpleGraph.fromRel_adj]
  refine ⟨hv, Or.inl ?_⟩
  simp only [WDigraph.comap, Equiv.apply_symm_apply, dGraph_isSome]
  exact darc_hub fun h => hv (by rw [← h, Equiv.symm_apply_apply])

end Directed

/-! ### Undirected family -/

section Undirected

variable {W w : ℕ} {x x' y y' : Fin k × Fin k → Bool}

lemma uval_indep_y {u v : Vtx k p} (h : aliceV u = true ∨ aliceV v = true) :
    uval w x y u v = uval w x y' u v := by
  cases u <;> cases v <;> simp_all [uval, aliceV]

lemma uval_indep_x {u v : Vtx k p} (h : aliceV u = false ∨ aliceV v = false) :
    uval w x y u v = uval w x' y u v := by
  cases u <;> cases v <;> simp_all [uval, aliceV]

lemma uval_cut {a b : Vtx k p} (ha : aliceV a = true) (hb : aliceV b = false)
    (h : (uval w x y a b).isSome ∨ (uval w x y b a).isSome) : (a, b) ∈ cutV := by
  cases a <;> cases b <;> simp_all [uval, aliceV, cutV]

variable {V : Type*}

/-- The undirected lower-bound family, relabelled along `e : V ≃ Vtx k p`. -/
def uFamily (W w : ℕ) (e : V ≃ Vtx k p) :
    LBFamily (Fin k × Fin k → Bool) (Fin k × Fin k → Bool) V (V → Option (Fin (W + 1))) :=
  ofWeights (fun x y u v => (uGraph W w x y).wt (e u) (e v)) (fun f _ => f)
    (fun v => aliceV (e v)) (cutV.map (e.prodCongr e).symm.toEmbedding)
    (fun q hq => by
      rw [mem_map_equiv, Equiv.symm_symm] at hq
      exact cutV_sub hq)
    (fun x y a b ha hb h => by
      rw [mem_map_equiv, Equiv.symm_symm]
      simp only [uGraph_isSome] at h
      exact uval_cut ha hb h)
    (fun x y y' u v h => by simp only [uGraph, uval_indep_y (y' := y') h])
    (fun x x' y u v h => by simp only [uGraph, uval_indep_x (x' := x') h])

instance [DecidableEq V] (e : V ≃ Vtx k p) (x y : Fin k × Fin k → Bool) :
    DecidableRel ((uFamily W w e).G x y).Adj :=
  inferInstanceAs (DecidableRel ((uGraph W w x y).comap e.toEmbedding).net.Adj)

lemma uFamily_G (e : V ≃ Vtx k p) :
    (uFamily W w e).G x y = ((uGraph W w x y).comap e.toEmbedding).net := rfl

lemma uFamily_inp (e : V ≃ Vtx k p) :
    (uFamily W w e).inp x y = ((uGraph W w x y).comap e.toEmbedding).view := rfl

lemma uFamily_card (e : V ≃ Vtx k p) : (uFamily W w e).Ecut.card ≤ 4 * k := by
  simp only [uFamily, ofWeights, card_map]; exact card_cutV

lemma uComap_ediam (e : V ≃ Vtx k p) :
    ((uGraph (p := p) W w x y).comap e.toEmbedding).net.ediam ≤ 2 := by
  refine ediam_le_two_of_hub (e.symm .hub) fun v hv => ?_
  rw [WGraph.net, SimpleGraph.fromRel_adj]
  refine ⟨hv, Or.inl ?_⟩
  simp only [WGraph.comap, Equiv.coe_toEmbedding, Equiv.apply_symm_apply, uGraph_isSome]
  rw [uval_hub fun h => hv (by rw [← h, Equiv.symm_apply_apply])]
  rfl

end Undirected

/-! ### Arithmetic -/

lemma k_le_of_sq_le {k c : ℕ} (h : k ^ 2 ≤ 8 * k * c + 2) : k ≤ 8 * c + 2 := by
  by_contra hk
  push Not at hk
  nlinarith

lemma sq_le_of_lb {k E B T : ℕ} (hE : E ≤ 4 * k) (h : k * k ≤ T * (2 * (E * B)) + 2) :
    k ^ 2 ≤ 8 * k * (B * T) + 2 := by
  have : T * (2 * (E * B)) ≤ T * (2 * (4 * k * B)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hE))
  nlinarith

lemma two_mul_lt_four {α : ℝ≥0∞} (hα : α < 2) : α * 4 < 8 := by
  calc α * 4 < 2 * 4 := ENNReal.mul_lt_mul_left (by norm_num) (by norm_num) hα
    _ = 8 := by norm_num

/-- Every `n ≥ 1` is `4k + 1 + p` with `p < 4`. -/
lemma exists_equiv_vtx {V : Type*} [Fintype V] (hn : 0 < Fintype.card V) :
    ∃ k p, Fintype.card V ≤ 4 * k + 4 ∧ Nonempty (V ≃ Vtx k p) :=
  ⟨(Fintype.card V - 1) / 4, (Fintype.card V - 1) % 4, by omega,
    ⟨Fintype.equivOfCardEq (by rw [Vtx.card]; omega)⟩⟩

/-! ### Theorem 1.2.A -/

/-- The input of a node in a directed network: weights of its outgoing and incoming arcs. -/
abbrev DInput (V : Type*) (W : ℕ) := V → Option (Fin (W + 1)) × Option (Fin (W + 1))

/-- Theorem 1.2.A for the family with parameter `k` (`n = 4k + 1 + p`): `k² ≤ 8k · B · T + 2`. -/
theorem theorem_1_2_A_family {V σ : Type*} [Fintype V] [DecidableEq V] {W B T : ℕ}
    (e : V ≃ Vtx k p) {α : ℝ≥0∞} (hα : α < 2) (A : Algorithm V (DInput V (W + 1)) σ B)
    (est : V → σ → Option ℝ≥0∞)
    (hA : ∀ D : WDigraph V (W + 1), D.Unweighted → D.net.ediam ≤ 2 →
      ApproxOutput α D.mwc (outputs A est D.net D.view T)) :
    k ^ 2 ≤ 8 * k * (B * T) + 2 := by
  have h := approx_lowerBound (dFamily W e) A est T (two_mul_lt_four hα)
    (fun x y => (dGraph W x y).mwc)
    (fun x y => by
      have := hA ((dGraph W x y).comap e) (dComap_unweighted e) (dComap_ediam e)
      rwa [WDigraph.mwc_comap] at this)
    (fun x y hq => by exact_mod_cast dGraph_mwc_le hq)
    (fun x y hq => by exact_mod_cast dGraph_mwc_ge hq)
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  exact sq_le_of_lb (dFamily_card e) h

/-- **Theorem 1.2.A** (deterministic). Computing a `(2 - ε)`-approximation of directed MWC
(weighted or unweighted) requires `Ω(n / log n)` rounds, even on graphs of diameter `≤ 2`:
if a CONGEST algorithm with `B`-bit messages outputs, within `T` rounds, an `α`-approximation
(`α < 2`) of the MWC of every unweighted `n`-node digraph with weights in `{0, …, W}` (`W ≥ 1`)
whose underlying network has diameter `≤ 2` (at least one node outputs; outputs follow
`ApproxOutput`), then `n ≤ 32 · B · T + 12`. -/
theorem theorem_1_2_A {V σ : Type*} [Fintype V] [DecidableEq V] {W B T : ℕ} (hW : 1 ≤ W)
    {α : ℝ≥0∞} (hα : α < 2) (A : Algorithm V (DInput V W) σ B) (est : V → σ → Option ℝ≥0∞)
    (hA : ∀ D : WDigraph V W, D.Unweighted → D.net.ediam ≤ 2 →
      ApproxOutput α D.mwc (outputs A est D.net D.view T)) :
    Fintype.card V ≤ 32 * B * T + 12 := by
  obtain ⟨W, rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
  · omega
  obtain ⟨k, p, hk, ⟨e⟩⟩ := exists_equiv_vtx hn
  have := k_le_of_sq_le (theorem_1_2_A_family e hα A est hA)
  nlinarith

/-! ### Theorem 1.4.A -/

/-- Theorem 1.4.A for the family with parameter `k`, heavy weight `w` with `α (2w + 2) < 4w`. -/
theorem theorem_1_4_A_family {V σ : Type*} [Fintype V] [DecidableEq V] {W w B T : ℕ}
    (e : V ≃ Vtx k p) {α : ℝ≥0∞} (hw : α * (2 * w + 2) < 4 * w) (hW : 2 * w ≤ W)
    (A : Algorithm V (V → Option (Fin (W + 1))) σ B) (est : V → σ → Option ℝ≥0∞)
    (hA : ∀ G : WGraph V W, G.net.ediam ≤ 2 →
      ApproxOutput α G.mwc (outputs A est G.net G.view T)) :
    k ^ 2 ≤ 8 * k * (B * T) + 2 := by
  have hw1 : 1 ≤ w := by
    rcases Nat.eq_zero_or_pos w with rfl | h
    · simp at hw
    · exact h
  have h := approx_lowerBound (uFamily W w e) A est T hw
    (fun x y => (uGraph W w x y).mwc)
    (fun x y => by
      have := hA ((uGraph W w x y).comap e.toEmbedding) (uComap_ediam e)
      rwa [WGraph.mwc_comap] at this)
    (fun x y hq => by exact_mod_cast uGraph_mwc_le hw1 hW hq)
    (fun x y hq => by exact_mod_cast uGraph_mwc_ge hw1 hW hq)
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  exact sq_le_of_lb (uFamily_card e) h

/-- For every `α < 2` some heavy weight `w` gives the gap `α · (2w + 2) < 4w`. -/
lemma exists_heavy_weight {α : ℝ≥0∞} (hα : α < 2) : ∃ w : ℕ, α * (2 * w + 2) < 4 * w := by
  have hα' : α ≠ ⊤ := ne_top_of_lt hα
  set t := α.toReal with ht
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have ht2 : t < 2 := by
    have := (ENNReal.toReal_lt_toReal hα' (by norm_num)).2 hα
    simpa using this
  obtain ⟨w, hw⟩ := exists_nat_gt (t / (2 - t))
  refine ⟨w, ?_⟩
  have hpos : (0 : ℝ) < 2 - t := by linarith
  have key : t * (2 * w + 2) < 4 * w := by
    rw [div_lt_iff₀ hpos] at hw
    nlinarith
  rw [← ENNReal.ofReal_toReal hα', ← ht]
  have e1 : (2 * (w : ℝ≥0∞) + 2) = ENNReal.ofReal (2 * w + 2) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_mul (by norm_num)]
    simp
  have e2 : (4 * (w : ℝ≥0∞)) = ENNReal.ofReal (4 * w) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  rw [e1, e2, ← ENNReal.ofReal_mul ht0]
  exact (ENNReal.ofReal_lt_ofReal_iff (by nlinarith)).2 key

/-- **Theorem 1.4.A** (deterministic). Computing a `(2 - ε)`-approximation of undirected weighted
MWC requires `Ω(n / log n)` rounds, even on graphs of diameter `≤ 2`: for every `α < 2` there is a
constant `W₀` such that, for weights in `{0, …, W}` with `W ≥ W₀`, every CONGEST algorithm with
`B`-bit messages that outputs within `T` rounds an `α`-approximation of the MWC of every weighted
`n`-node graph of diameter `≤ 2` satisfies `n ≤ 32 · B · T + 12`. -/
theorem theorem_1_4_A {α : ℝ≥0∞} (hα : α < 2) : ∃ W₀ : ℕ, ∀ {V σ : Type*} [Fintype V]
    [DecidableEq V] {W B T : ℕ}, W₀ ≤ W → ∀ (A : Algorithm V (V → Option (Fin (W + 1))) σ B)
    (est : V → σ → Option ℝ≥0∞), (∀ G : WGraph V W, G.net.ediam ≤ 2 →
      ApproxOutput α G.mwc (outputs A est G.net G.view T)) →
    Fintype.card V ≤ 32 * B * T + 12 := by
  obtain ⟨w, hw⟩ := exists_heavy_weight hα
  refine ⟨2 * w, fun {V σ} _ _ {W B T} hW A est hA => ?_⟩
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
  · omega
  obtain ⟨k, p, hk, ⟨e⟩⟩ := exists_equiv_vtx hn
  have := k_le_of_sq_le (theorem_1_4_A_family e hw hW A est hA)
  nlinarith

/-! ### Directed 4-cycle detection (§1.2.1) -/

/-- The digraph has a simple directed cycle of length exactly `q`. -/
def WDigraph.HasCycleOfLen {V : Type*} {W : ℕ} (D : WDigraph V W) (q : ℕ) : Prop :=
  ∃ c : D.Cycle, c.len = q

/-- "Implicit in our MWC lower bound is an `Ω̃(n)` lower bound for detecting if a given graph has a
directed cycle of length `q`" (§1.2.1), for `q = 4`: if within `T` rounds some node rejects iff the
unweighted digraph (diameter `≤ 2`) has a directed `4`-cycle, then `n ≤ 32 · B · T + 12`. -/
theorem directed_four_cycle_lowerBound {V σ : Type*} [Fintype V] [DecidableEq V] {W B T : ℕ}
    (hW : 1 ≤ W) (A : Algorithm V (DInput V W) σ B)
    (hA : ∀ D : WDigraph V W, D.Unweighted → D.net.ediam ≤ 2 →
      (A.Accepts D.net D.view T ↔ ¬ D.HasCycleOfLen 4)) :
    Fintype.card V ≤ 32 * B * T + 12 := by
  obtain ⟨W, rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
  · omega
  obtain ⟨k, p, hk, ⟨e⟩⟩ := exists_equiv_vtx hn
  have h := (dFamily W e).disj_lowerBound A T fun x y => by
    change A.Accepts ((dGraph W x y).comap e).net ((dGraph W x y).comap e).view T ↔ _
    rw [hA _ (dComap_unweighted e) (dComap_ediam e), disj_true_iff]
    constructor
    · intro hno q hq
      exact hno ⟨(dGraph.cycle4 q.1 q.2 hq.1 hq.2).comap e, rfl⟩
    · rintro hd ⟨c, hc⟩
      have := dGraph.len_ge_eight (c.unComap e) hd
      simp [WDigraph.Cycle.unComap] at this
      omega
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  have := k_le_of_sq_le (sq_le_of_lb (dFamily_card e) h)
  nlinarith

/-! ### Randomized versions -/

/-- The randomized communication lower bound for set disjointness, as a hypothesis: every
private-coin protocol computing `¬DISJ_K` with error at most `δ` on every input exchanges at least
`κ · K` bits on some input. (Kalyanasundaram–Schnitger, Razborov: this holds for `δ = 1/3` and
some constant `κ > 0`; it is not formalized.) The coin spaces must be nonempty: with an empty one
the error count is vacuously `0`, the constant protocol would "compute" `¬DISJ`, and the
hypothesis would force `κ ≤ 0` (`randDisjLB_without_nonempty_degenerate`). -/
def RandDisjLB (δ κ : ℝ) : Prop :=
  ∀ (ι RA RB : Type) [Fintype ι] [Fintype RA] [Fintype RB] [Nonempty RA] [Nonempty RB]
    (P : Protocol ((ι → Bool) × RA) ((ι → Bool) × RB) Bool) (c : ℕ),
    P.RandComputes (fun x y => !disj x y) δ → P.CostLE c → κ * Fintype.card ι ≤ c

/-- Why `RandDisjLB` requires nonempty coin spaces: without them (an empty coin space makes every
protocol "correct"), the hypothesis forces `κ ≤ 0` and the randomized bounds would be vacuous. -/
lemma randDisjLB_without_nonempty_degenerate {δ κ : ℝ}
    (h : ∀ (ι RA RB : Type) [Fintype ι] [Fintype RA] [Fintype RB]
      (P : Protocol ((ι → Bool) × RA) ((ι → Bool) × RB) Bool) (c : ℕ),
      P.RandComputes (fun x y => !disj x y) δ → P.CostLE c → κ * Fintype.card ι ≤ c) :
    κ ≤ 0 := by
  have := h Unit Empty Unit (Protocol.ret true) 0 (fun x y => by simp [errCount]) trivial
  simpa using this

lemma real_bound {κ : ℝ} (hκ : 0 ≤ κ) {n k c : ℕ} (hn : n ≤ 4 * k + 4)
    (h : κ * (k : ℝ) ^ 2 ≤ 8 * k * c + 2) : κ * n ≤ 32 * c + 8 + 4 * κ := by
  have hn' : (n : ℝ) ≤ 4 * k + 4 := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h4 : (n : ℝ) ≤ 4 := by simpa using hn'
    have h5 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    nlinarith [mul_le_mul_of_nonneg_left h4 hκ]
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have h1 : κ * k ≤ 8 * c + 2 := by
      by_contra hc
      push Not at hc
      nlinarith
    nlinarith

/-- **Theorem 1.2.A** (randomized), conditional on `RandDisjLB δ κ`: a randomized CONGEST
algorithm (private random strings `r v : ρ`) that, on every unweighted `n`-node digraph of
diameter `≤ 2`, outputs an `α`-approximation (`α < 2`) of the MWC within `T` rounds except with
probability `≤ δ`, satisfies `κ · n ≤ 32 · B · T + 8 + 4κ`. -/
theorem theorem_1_2_A_rand {V ρ σ : Type} [Fintype V] [DecidableEq V] [Fintype ρ] [Nonempty ρ]
    {W B T : ℕ} (hW : 1 ≤ W) {α : ℝ≥0∞} (hα : α < 2) {δ κ : ℝ} (hκ : 0 ≤ κ)
    (hDisj : RandDisjLB δ κ) (A : Algorithm V (DInput V W × ρ) σ B) (est : V → σ → Option ℝ≥0∞)
    (hA : ∀ D : WDigraph V W, D.Unweighted → D.net.ediam ≤ 2 →
      (failCount A est D.net D.view T α D.mwc : ℝ) ≤ δ * Fintype.card (V → ρ)) :
    κ * Fintype.card V ≤ 32 * (B * T) + 8 + 4 * κ := by
  obtain ⟨W, rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
  · rw [hn]; simp; positivity
  obtain ⟨k, p, hk, ⟨e⟩⟩ := exists_equiv_vtx hn
  have h := approx_rand_lowerBound (dFamily W e) A est T (two_mul_lt_four hα)
    (fun x y => (dGraph W x y).mwc) δ
    (fun x y => by
      have := hA ((dGraph W x y).comap e) (dComap_unweighted e) (dComap_ediam e)
      rwa [WDigraph.mwc_comap] at this)
    (fun x y hq => by exact_mod_cast dGraph_mwc_le hq)
    (fun x y hq => by exact_mod_cast dGraph_mwc_ge hq)
    ⌈κ * (k : ℝ) ^ 2⌉₊
    (fun P c hP hc => Nat.ceil_le.2 (by
      have := hDisj _ _ _ P c hP hc
      simpa [sq] using this))
  have h2 : (⌈κ * (k : ℝ) ^ 2⌉₊ : ℝ) ≤ 8 * k * ((B * T : ℕ) : ℝ) + 2 := by
    have := (Nat.cast_le (α := ℝ)).2 (h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (dFamily_card e)))) _))
    push_cast at this ⊢
    linarith
  have := real_bound hκ hk ((Nat.le_ceil _).trans h2)
  push_cast at this
  linarith

/-- **Theorem 1.4.A** (randomized), conditional on `RandDisjLB δ κ`: for every `α < 2` there is
`W₀` such that, for weights in `{0, …, W}`, `W ≥ W₀`, a randomized CONGEST algorithm that outputs
an `α`-approximation of the MWC of every weighted undirected `n`-node graph of diameter `≤ 2`
within `T` rounds except with probability `≤ δ` satisfies `κ · n ≤ 32 · B · T + 8 + 4κ`. -/
theorem theorem_1_4_A_rand {α : ℝ≥0∞} (hα : α < 2) : ∃ W₀ : ℕ, ∀ {V ρ σ : Type} [Fintype V]
    [DecidableEq V] [Fintype ρ] [Nonempty ρ] {W B T : ℕ} {δ κ : ℝ}, W₀ ≤ W → 0 ≤ κ →
    RandDisjLB δ κ → ∀ (A : Algorithm V ((V → Option (Fin (W + 1))) × ρ) σ B)
    (est : V → σ → Option ℝ≥0∞), (∀ G : WGraph V W, G.net.ediam ≤ 2 →
      (failCount A est G.net G.view T α G.mwc : ℝ) ≤ δ * Fintype.card (V → ρ)) →
    κ * Fintype.card V ≤ 32 * (B * T) + 8 + 4 * κ := by
  obtain ⟨w, hw⟩ := exists_heavy_weight hα
  refine ⟨2 * w, fun {V ρ σ} _ _ _ _ {W B T δ κ} hW hκ hDisj A est hA => ?_⟩
  have hw1 : 1 ≤ w := by
    rcases Nat.eq_zero_or_pos w with rfl | h
    · simp at hw
    · exact h
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
  · rw [hn]; simp; positivity
  obtain ⟨k, p, hk, ⟨e⟩⟩ := exists_equiv_vtx hn
  have h := approx_rand_lowerBound (uFamily W w e) A est T hw
    (fun x y => (uGraph W w x y).mwc) δ
    (fun x y => by
      have := hA ((uGraph W w x y).comap e.toEmbedding) (uComap_ediam e)
      rwa [WGraph.mwc_comap] at this)
    (fun x y hq => by exact_mod_cast uGraph_mwc_le hw1 hW hq)
    (fun x y hq => by exact_mod_cast uGraph_mwc_ge hw1 hW hq)
    ⌈κ * (k : ℝ) ^ 2⌉₊
    (fun P c hP hc => Nat.ceil_le.2 (by
      have := hDisj _ _ _ P c hP hc
      simpa [sq] using this))
  have h2 : (⌈κ * (k : ℝ) ^ 2⌉₊ : ℝ) ≤ 8 * k * ((B * T : ℕ) : ℝ) + 2 := by
    have := (Nat.cast_le (α := ℝ)).2 (h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (uFamily_card e)))) _))
    push_cast at this ⊢
    linarith
  have := real_bound hκ hk ((Nat.le_ceil _).trans h2)
  push_cast at this
  linarith

end Podc.MinWeightCycleCongest
