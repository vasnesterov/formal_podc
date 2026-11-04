import Podc.Foundations.GameTheory.NetworkCostSharing

/-!
# Bayesian ignorance in NCS games: Lemma 3.2 (affine-plane construction)

Alon, Emek, Feldman, Tennenholtz, *Bayesian Ignorance* (PODC 2010), Lemma 3.2: for every `k₀`
there are `k ≥ k₀` and a `k`-agent Bayesian NCS game `G` on a directed `Θ(k²)`-vertex graph with
`opt^P(G) / worst-eq^C(G) = Ω(k)`.

The construction uses the affine plane of prime order `q` over `ZMod q`: points `ZMod q × ZMod q`,
lines `y = a x + b` (`Sum.inl (a, b)`) and `x = c` (`Sum.inr c`). The directed graph has a source
`u`, a vertex `v ℓ` per line and a vertex `w p` per point, edges `(u, v ℓ)` of cost `1` and
`(v ℓ, w p)` (`p ∈ ℓ`) of cost `0`. There are `k = q + 1` agents (`Option (ZMod q)`, `none` being
agent `k`). The prior is uniform over pairs `(ℓ, π)` of a line and a permutation of `ZMod q`;
under `(ℓ, π)` every agent has source `u`, agent `r` has destination `w` of the `π(r)`-th point of
`ℓ`, and agent `none` has destination `v ℓ`.

## Main statements

* `worstEqC_eq_one`: `worst-eq^C(G) = 1` (every Nash equilibrium of every underlying game buys
  exactly one unit edge).
* `optP_ge`: `1 + q² / (q + 1) ≤ opt^P(G)`.
* `lemma_3_2`: the existential statement, with `k = q + 1`, `|V| = 2(k-1)² + (k-1) + 1`,
  `worst-eq^C(G) = 1` and `k - 1 ≤ opt^P(G)`; also `opt^P ≥ (k-1)·opt^C` and
  `best-eq^P ≥ (k-1)·best-eq^C`.
-/

open Finset Cslib.GameTheory Cslib.GameTheory.BayesianGame
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace Podc.BayesianIgnorance.Lemma32

variable (q : ℕ) [hq : Fact q.Prime]

/-! ### The affine plane over `ZMod q` -/

/-- Lines of the affine plane over `ZMod q`: `inl (a, b)` is `y = a x + b`, `inr c` is `x = c`. -/
abbrev Line := (ZMod q × ZMod q) ⊕ ZMod q

/-- Points of the affine plane over `ZMod q`. -/
abbrev Point := ZMod q × ZMod q

variable {q}

/-- The `j`-th point of a line. -/
def pt : Line q → ZMod q → Point q
  | .inl (a, b), j => (j, a * j + b)
  | .inr c, j => (c, j)

lemma pt_injective (ℓ : Line q) : Function.Injective (pt ℓ) := by
  rcases ℓ with ⟨a, b⟩ | c <;> intro j j' h <;> simp_all [pt]

/-- Two distinct lines meet in at most one point. -/
lemma lines_meet {ℓ ℓ' : Line q} (hne : ℓ ≠ ℓ') {j j' i i' : ZMod q}
    (h1 : pt ℓ j = pt ℓ' j') (h2 : pt ℓ i = pt ℓ' i') : j = i := by
  rcases ℓ with ⟨a, b⟩ | c <;> rcases ℓ' with ⟨a', b'⟩ | c' <;>
    simp only [pt, Prod.mk.injEq] at h1 h2
  · obtain ⟨rfl, h1⟩ := h1
    obtain ⟨rfl, h2⟩ := h2
    by_cases ha : a = a'
    · subst ha
      exact absurd (by simp [show b = b' by linear_combination h1]) hne
    · have : (a - a') * (j - i) = 0 := by linear_combination h1 - h2
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) ha
      · exact sub_eq_zero.1 h
  · rw [h1.1, h2.1]
  · rw [h1.2, h2.2, ← h1.1, ← h2.1]
  · exact absurd (by rw [← h1.1, h2.1]) hne

/-- The `q + 1` lines through a point `p`, with the index of `p` on each of them. -/
def throughPt (p : Point q) : Option (ZMod q) → Line q × ZMod q
  | none => (.inr p.1, p.2)
  | some a => (.inl (a, p.2 - a * p.1), p.1)

lemma pt_throughPt (p : Point q) (o : Option (ZMod q)) :
    pt (throughPt p o).1 (throughPt p o).2 = p := by
  rcases o with _ | a <;> simp [throughPt, pt]

lemma throughPt_injective (p : Point q) : Function.Injective (throughPt p) := by
  rintro (_ | a) (_ | a') h <;> simp_all [throughPt]

/-- At least `q` incident (line, index) pairs give the point `p` on a line other than `ℓ₀`. -/
lemma card_fiber_ne (p : Point q) (ℓ₀ : Line q) :
    q ≤ #{x : Line q × ZMod q | pt x.1 x.2 = p ∧ x.1 ≠ ℓ₀} := by
  have h1 : q + 1 ≤ #{x : Line q × ZMod q | pt x.1 x.2 = p} := by
    have := Finset.card_le_card_of_injOn (s := (univ : Finset (Option (ZMod q))))
      (t := {x : Line q × ZMod q | pt x.1 x.2 = p})
      (throughPt p) (fun o _ => by simp [pt_throughPt]) (throughPt_injective p).injOn
    simpa [ZMod.card] using this
  have h2 : #{x : Line q × ZMod q | pt x.1 x.2 = p ∧ x.1 = ℓ₀} ≤ 1 := by
    refine Finset.card_le_one.2 fun x hx y hy => ?_
    simp only [mem_filter, mem_univ, true_and] at hx hy
    obtain ⟨hx, hx'⟩ := hx
    obtain ⟨hy, hy'⟩ := hy
    have : x.1 = y.1 := hx'.trans hy'.symm
    refine Prod.ext this (pt_injective x.1 ?_)
    rw [hx, this, hy]
  have h3 := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
    fun x : Line q × ZMod q => pt x.1 x.2 = p) (fun x => x.1 = ℓ₀)
  simp only [Finset.filter_filter, ne_eq] at h3 ⊢
  omega

/-- Double counting: whatever line `c p` is singled out at every point `p`, at least `q³` incident
(line, index) pairs `(ℓ, j)` have `c (pt ℓ j) ≠ ℓ`. -/
lemma card_ne_choice (c : Point q → Line q) :
    q ^ 3 ≤ #{x : Line q × ZMod q | c (pt x.1 x.2) ≠ x.1} := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Line q × ZMod q => pt x.1 x.2)
    (t := (univ : Finset (Point q))) (fun _ _ => mem_univ _)]
  calc q ^ 3 = ∑ _p : Point q, q := by simp [ZMod.card]; ring
    _ ≤ _ := by
      refine Finset.sum_le_sum fun p _ => (card_fiber_ne p (c p)).trans (le_of_eq ?_)
      congr 1
      ext x
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by rw [h1]; exact Ne.symm h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, by rw [← h2]; exact Ne.symm h1⟩

/-! ### The network and the Bayesian game -/

variable (q)

/-- Vertices: the source `u = none`, `v ℓ = some (inl ℓ)`, `w p = some (inr p)`. -/
abbrev Vtx := Option (Line q ⊕ Point q)

/-- Edges: `inl ℓ` is `(u, v ℓ)`, `inr (ℓ, j)` is `(v ℓ, w (pt ℓ j))`. -/
abbrev Edge := Line q ⊕ (Line q × ZMod q)

/-- Agents: `some r` for `r : ZMod q` (agents `1, …, m`) and `none` (agent `k = m + 1`). -/
abbrev Agent := Option (ZMod q)

/-- The sample space of the prior: a line and a permutation of the point indices. -/
abbrev Omega := Line q × Equiv.Perm (ZMod q)

variable {q}

/-- The source vertex `u`. -/
def src : Vtx q := none

/-- The vertex `v ℓ` of a line. -/
def vL (ℓ : Line q) : Vtx q := some (.inl ℓ)

/-- The vertex `w p` of a point. -/
def wP (p : Point q) : Vtx q := some (.inr p)

/-- Endpoints of the edges. -/
def ends : Edge q → Vtx q × Vtx q
  | .inl ℓ => (src, vL ℓ)
  | .inr (ℓ, j) => (vL ℓ, wP (pt ℓ j))

/-- Edge costs: `1` for `(u, v ℓ)`, `0` for `(v ℓ, w p)`. -/
def ecost : Edge q → ℝ≥0
  | .inl _ => 1
  | .inr _ => 0

variable (q)

/-- The directed network of the construction. -/
noncomputable def net : Network (Vtx q) (Edge q) := Network.directed ends ecost

/-- The type profile `t(ℓ, π)`. -/
def prof : Omega q → Agent q → Vtx q × Vtx q
  | (ℓ, _), none => (src, vL ℓ)
  | (ℓ, π), some r => (src, wP (pt ℓ (π r)))

/-- The prior: uniform over `(ℓ, π)`. -/
noncomputable def prior : PMF (Agent q → Vtx q × Vtx q) :=
  (PMF.uniformOfFintype (Omega q)).map (prof q)

/-- The Bayesian NCS game of Lemma 3.2. -/
noncomputable abbrev game := (net q).bayesGame (prior q)

variable {q}

@[simp] lemma net_cost_inl (ℓ : Line q) : (net q).cost (.inl ℓ) = 1 := rfl
@[simp] lemma net_cost_inr (x : Line q × ZMod q) : (net q).cost (.inr x) = 0 := rfl

/-! ### Paths from the source -/

lemma connects_src {F : Finset (Edge q)} {x : Vtx q} (h : (net q).Connects F src x) :
    x = src ∨ (∃ ℓ, x = vL ℓ ∧ .inl ℓ ∈ F) ∨
      (∃ ℓ j, x = wP (pt ℓ j) ∧ .inl ℓ ∈ F ∧ .inr (ℓ, j) ∈ F) := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hst ih =>
    obtain ⟨e, he, hs⟩ := hst
    rcases e with ℓ | ⟨ℓ, j⟩ <;> simp only [net, Network.directed, ends, Prod.mk.injEq] at hs
    · obtain ⟨rfl, rfl⟩ := hs; exact Or.inr (Or.inl ⟨ℓ, rfl, he⟩)
    · obtain ⟨rfl, rfl⟩ := hs
      rcases ih with h | ⟨ℓ', h, h'⟩ | ⟨ℓ', j', h, -⟩
      · simp [src, vL] at h
      · simp only [vL, Option.some.injEq, Sum.inl.injEq] at h
        subst h
        exact Or.inr (Or.inr ⟨_, j, rfl, h', he⟩)
      · simp [vL, wP] at h

lemma connects_vL_iff {F : Finset (Edge q)} {ℓ : Line q} :
    (net q).Connects F src (vL ℓ) ↔ .inl ℓ ∈ F := by
  constructor
  · intro h
    rcases connects_src h with h | ⟨ℓ', h, h'⟩ | ⟨ℓ', j', h, -⟩
    · simp [src, vL] at h
    · simp only [vL, Option.some.injEq, Sum.inl.injEq] at h
      rwa [h]
    · simp [vL, wP] at h
  · intro h
    exact Relation.ReflTransGen.single ⟨_, h, rfl⟩

lemma connects_wP_iff {F : Finset (Edge q)} {p : Point q} :
    (net q).Connects F src (wP p) ↔ ∃ ℓ j, pt ℓ j = p ∧ .inl ℓ ∈ F ∧ .inr (ℓ, j) ∈ F := by
  constructor
  · intro h
    rcases connects_src h with h | ⟨ℓ', h, h'⟩ | ⟨ℓ', j', h, h', h''⟩
    · simp [src, wP] at h
    · simp [vL, wP] at h
    · simp only [wP, Option.some.injEq, Sum.inr.injEq] at h
      exact ⟨ℓ', j', h.symm, h', h''⟩
  · rintro ⟨ℓ, j, rfl, h, h'⟩
    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨_, h, rfl⟩) ⟨_, h', rfl⟩

/-! ### Nash equilibria of the underlying games: `worst-eq^C(G) ≤ 1` -/

@[simp] lemma prof_fst (ω : Omega q) (i : Agent q) : (prof q ω i).1 = src := by
  rcases i <;> rfl
@[simp] lemma prof_none (ω : Omega q) : (prof q ω none).2 = vL ω.1 := rfl
@[simp] lemma prof_some (ω : Omega q) (r : ZMod q) :
    (prof q ω (some r)).2 = wP (pt ω.1 (ω.2 r)) := rfl

/-- The 'right' action of every agent in state `(ℓ, π)`: the edge `(u, v ℓ)` (and `(v ℓ, w p)`). -/
def good (ω : Omega q) : Agent q → Finset (Edge q)
  | none => {.inl ω.1}
  | some r => {.inl ω.1, .inr (ω.1, ω.2 r)}

lemma good_connects (ω : Omega q) (i : Agent q) :
    (net q).Connects (good ω i) (prof q ω i).1 (prof q ω i).2 := by
  rcases i with _ | r
  · simpa using connects_vL_iff.2 (by simp [good])
  · simpa using connects_wP_iff.2 ⟨_, _, rfl, by simp [good], by simp [good]⟩

/-- In a Nash equilibrium every agent connects her terminals. -/
lemma isNashEq_connects {ω : Omega q} {a : Agent q → Finset (Edge q)}
    (h : (game q).IsNashEq (prof q ω) a) (i : Agent q) :
    (net q).Connects (a i) (prof q ω i).1 (prof q ω i).2 := by
  by_contra hc
  have h1 := h i (good ω i)
  simp only [Network.bayesGame_cost] at h1
  rw [(net q).agentCost_of_not_connects hc,
    (net q).agentCost_of_connects (by simpa using good_connects ω i)] at h1
  exact ENNReal.coe_ne_top (top_le_iff.1 h1)

/-- In a Nash equilibrium of `G_{t(ℓ, π)}` the only unit edge bought is `(u, v ℓ)`. -/
lemma isNashEq_inl {ω : Omega q} {a : Agent q → Finset (Edge q)}
    (h : (game q).IsNashEq (prof q ω) a) {i : Agent q} {ℓ' : Line q} (hi : .inl ℓ' ∈ a i) :
    ℓ' = ω.1 := by
  obtain ⟨ℓ, π⟩ := ω
  by_contra hne
  have hconn := isNashEq_connects h
  have hnone : Sum.inl ℓ ∈ a none := connects_vL_iff.1 (by simpa using hconn none)
  -- every buyer of `(u, v ℓ')` needs it, hence is an agent `r` whose point lies on `ℓ'`
  have need : ∀ j, Sum.inl ℓ' ∈ a j → ∃ r, j = some r ∧ ∃ j', pt ℓ' j' = pt ℓ (π r) := by
    intro j hj
    rcases j with _ | r
    · refine ((net q).not_isNashEq_of_removable h hj (by simp) ?_).elim
      simpa using connects_vL_iff.2 (mem_erase.2 ⟨by simpa using Ne.symm hne, hnone⟩)
    · refine ⟨r, rfl, ?_⟩
      by_contra hno
      refine (net q).not_isNashEq_of_removable h hj (by simp) ?_
      obtain ⟨ℓ'', j'', hp, h1, h2⟩ := connects_wP_iff.1 (by simpa using hconn (some r))
      have hne' : ℓ'' ≠ ℓ' := by rintro rfl; exact hno ⟨j'', hp⟩
      simpa using connects_wP_iff.2 ⟨ℓ'', j'', hp, mem_erase.2 ⟨by simpa using hne', h1⟩,
        mem_erase.2 ⟨by simp, h2⟩⟩
  obtain ⟨r, rfl, j₁, hj₁⟩ := need i hi
  have hlo : Network.loadOthers a (some r) (.inl ℓ') = 0 := by
    refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun j _ ⟨hjr, hj⟩ => ?_)
    obtain ⟨r', rfl, j₂, hj₂⟩ := need j hj
    have : π r' = π r := lines_meet (Ne.symm hne) hj₂.symm hj₁.symm
    exact hjr (by rw [π.injective this])
  have hlo' : 1 ≤ Network.loadOthers a (some r) (.inl ℓ) :=
    Finset.card_pos.2 ⟨none, by simp [hnone]⟩
  have h1 := h (some r) (good (ℓ, π) (some r))
  simp only [Network.bayesGame_cost] at h1
  rw [(net q).agentCost_of_connects (hconn _),
    (net q).agentCost_of_connects (by simpa using good_connects (ℓ, π) (some r))] at h1
  have h1' := ENNReal.coe_le_coe.1 h1
  rw [(net q).payment_eq, (net q).payment_update] at h1'
  have hge : 1 ≤ ∑ e ∈ a (some r), (net q).cost e / ((Network.loadOthers a (some r) e : ℝ≥0) + 1) := by
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun _ _ => zero_le) hi)
    simp [hlo]
  have hlt : ∑ e ∈ good (ℓ, π) (some r),
      (net q).cost e / ((Network.loadOthers a (some r) e : ℝ≥0) + 1) < 1 := by
    rw [good, Finset.sum_pair (by simp)]
    simp only [net_cost_inr, zero_div, add_zero, net_cost_inl]
    rw [div_lt_one (by positivity)]
    have : (1 : ℝ≥0) ≤ Network.loadOthers a (some r) (.inl ℓ) := by exact_mod_cast hlo'
    exact lt_add_of_le_of_pos this one_pos |>.trans_le' le_rfl
  exact absurd (hge.trans h1') (not_le.2 hlt)

/-- Every Nash equilibrium of `G_{t(ℓ, π)}` has social cost at most `1`. -/
lemma isNashEq_stateCost_le {ω : Omega q} {a : Agent q → Finset (Edge q)}
    (h : (game q).IsNashEq (prof q ω) a) : (game q).stateCost (prof q ω) a ≤ 1 := by
  rw [(net q).stateCost_bayesGame_of_forall _ (isNashEq_connects h)]
  have : (net q).totalCost a ≤ 1 := by
    unfold Network.totalCost
    calc ∑ e ∈ univ.biUnion a, (net q).cost e ≤ ∑ e ∈ {Sum.inl ω.1}, (net q).cost e := by
          refine Finset.sum_le_sum_of_ne_zero fun e he hne => ?_
          rcases e with ℓ' | x
          · obtain ⟨i, -, hi⟩ := mem_biUnion.1 he
            simp [isNashEq_inl h hi]
          · simp at hne
      _ = 1 := by simp
  exact_mod_cast this

/-! ### The 'right' profile is a Nash equilibrium: `worst-eq^C(G) = 1` -/

lemma loadOthers_le (a : Agent q → Finset (Edge q)) (i : Agent q) (e : Edge q) :
    Network.loadOthers a i e ≤ q := by
  unfold Network.loadOthers
  calc _ ≤ #(univ.erase i) := Finset.card_le_card fun j hj => by
          simp only [mem_filter, mem_univ, true_and] at hj
          exact mem_erase.2 ⟨hj.1, mem_univ _⟩
    _ = q := by simp [Finset.card_erase_of_mem, ZMod.card]

lemma loadOthers_good (ω : Omega q) (i : Agent q) :
    Network.loadOthers (good ω) i (.inl ω.1) = q := by
  unfold Network.loadOthers
  have : (univ.filter fun j => j ≠ i ∧ Sum.inl ω.1 ∈ good ω j) = univ.erase i := by
    ext j
    rw [mem_filter, mem_erase]
    rcases j with _ | r <;> simp [good]
  rw [this]
  simp [Finset.card_erase_of_mem, ZMod.card]

/-- The profile in which everybody buys `(u, v ℓ)` is a Nash equilibrium of `G_{t(ℓ, π)}`. -/
lemma isNashEq_good (ω : Omega q) : (game q).IsNashEq (prof q ω) (good ω) := by
  intro i b
  simp only [Network.bayesGame_cost]
  by_cases hb : (net q).Connects b (prof q ω i).1 (prof q ω i).2
  swap
  · rw [(net q).agentCost_of_not_connects (a := Function.update (good ω) i b) (by simpa using hb)]
    exact le_top
  rw [(net q).agentCost_of_connects (good_connects ω i),
    (net q).agentCost_of_connects (a := Function.update (good ω) i b) (by simpa using hb)]
  refine ENNReal.coe_le_coe.2 ?_
  rw [(net q).payment_eq, (net q).payment_update]
  obtain ⟨ℓ'', hℓ''⟩ : ∃ ℓ'', Sum.inl ℓ'' ∈ b := by
    rcases i with _ | r
    · exact ⟨_, connects_vL_iff.1 (by simpa using hb)⟩
    · obtain ⟨ℓ'', -, -, h, -⟩ := connects_wP_iff.1 (by simpa using hb)
      exact ⟨_, h⟩
  calc ∑ e ∈ good ω i, (net q).cost e / ((Network.loadOthers (good ω) i e : ℝ≥0) + 1)
      = 1 / ((q : ℝ≥0) + 1) := by
        rcases i with _ | r
        · simp [good, loadOthers_good]
        · simp only [good]
          rw [Finset.sum_pair (by simp)]
          simp [loadOthers_good]
    _ ≤ (net q).cost (.inl ℓ'') /
          ((Network.loadOthers (good ω) i (.inl ℓ'') : ℝ≥0) + 1) := by
        rw [net_cost_inl]
        gcongr
        exact_mod_cast loadOthers_le _ _ _
    _ ≤ _ := Finset.single_le_sum (f := fun e => (net q).cost e /
          ((Network.loadOthers (good ω) i e : ℝ≥0) + 1)) (fun _ _ => zero_le) hℓ''

lemma stateCost_good (ω : Omega q) : 1 ≤ (game q).stateCost (prof q ω) (good ω) := by
  rw [(net q).stateCost_bayesGame_of_forall _ (good_connects ω)]
  have : (1 : ℝ≥0) ≤ (net q).totalCost (good ω) := by
    unfold Network.totalCost
    have hm : Sum.inl ω.1 ∈ univ.biUnion (good ω) :=
      mem_biUnion.2 ⟨none, mem_univ _, by simp [good]⟩
    simpa using Finset.single_le_sum (f := (net q).cost) (fun _ _ => zero_le) hm
  exact_mod_cast this

instance : Fintype (Agent q → Vtx q × Vtx q) := @Pi.instFintype _ _ _ _ fun _ => inferInstance

/-- Expectations against the prior are averages over `(ℓ, π)`. -/
lemma sum_prior (g : (Agent q → Vtx q × Vtx q) → ℝ≥0∞) :
    ∑ t, prior q t * g t = ∑ ω : Omega q, (Fintype.card (Omega q) : ℝ≥0∞)⁻¹ * g (prof q ω) := by
  rw [prior, sum_map_mul]
  simp [PMF.uniformOfFintype_apply]

lemma sum_inv_card : ∑ _ω : Omega q, (Fintype.card (Omega q) : ℝ≥0∞)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

/-- Lemma 3.2 of [Alon–Emek–Feldman–Tennenholtz 2010], complete-information side:
`worst-eq^C(G) = 1`. -/
theorem worstEqC_eq_one : (game q).worstEqC = 1 := by
  unfold worstEqC
  rw [Network.bayesGame_prior, sum_prior]
  refine le_antisymm ?_ ?_
  · calc _ ≤ ∑ _ω : Omega q, (Fintype.card (Omega q) : ℝ≥0∞)⁻¹ * 1 := by
          gcongr with ω
          exact iSup₂_le fun a ha => isNashEq_stateCost_le ha
      _ = 1 := by simpa using sum_inv_card
  · calc (1 : ℝ≥0∞) = ∑ _ω : Omega q, (Fintype.card (Omega q) : ℝ≥0∞)⁻¹ * 1 := by
          simpa using sum_inv_card.symm
      _ ≤ _ := by
          gcongr with ω
          exact (stateCost_good ω).trans (le_iSup₂
            (f := fun a (_ : (game q).IsNashEq (prof q ω) a) => (game q).stateCost (prof q ω) a)
            (good ω) (isNashEq_good ω))

/-! ### Partial information: `opt^P(G) ≥ 1 + q² / (q + 1)` -/

/-- Averaging over permutations: `π r` is uniformly distributed. -/
lemma perm_avg (h : ZMod q → ℕ) (r : ZMod q) :
    q * ∑ π : Equiv.Perm (ZMod q), h (π r) =
      Fintype.card (Equiv.Perm (ZMod q)) * ∑ j, h j := by
  have key : ∀ c : ZMod q, ∑ π : Equiv.Perm (ZMod q), h (π r + c) =
      ∑ π : Equiv.Perm (ZMod q), h (π r) := fun c =>
    Fintype.sum_equiv (Equiv.mulLeft (Equiv.addRight c)) _ _ fun π => by
      simp [Equiv.Perm.mul_apply]
  calc q * ∑ π : Equiv.Perm (ZMod q), h (π r) = ∑ c : ZMod q, ∑ π : Equiv.Perm (ZMod q), h (π r + c) := by
        simp [key, ZMod.card]
    _ = ∑ π : Equiv.Perm (ZMod q), ∑ c, h (π r + c) := Finset.sum_comm
    _ = ∑ _π : Equiv.Perm (ZMod q), ∑ j, h j :=
        Finset.sum_congr rfl fun π _ => Fintype.sum_equiv (Equiv.addLeft (π r)) _ _ fun _ => rfl
    _ = _ := by simp

/-- The lines through `p` whose unit edge agent `r` buys when her destination is `w p`. -/
def boughtLines (s : Agent q → Vtx q × Vtx q → Finset (Edge q)) (r : ZMod q) (p : Point q) :
    Finset (Line q) :=
  {ℓ' | Sum.inl ℓ' ∈ s (some r) (src, wP p) ∧ ∃ j, pt ℓ' j = p}

/-- The cost of a feasible play in state `(ℓ, π)` is at least `1` (agent `k`'s edge `(u, v ℓ)`) plus
the number of unit edges `(u, v ℓ')`, `ℓ' ≠ ℓ`, bought by the agents `r` for their own points:
these are pairwise distinct since two lines meet in at most one point. -/
lemma stateCost_ge (s : Agent q → Vtx q × Vtx q → Finset (Edge q)) (ω : Omega q)
    (hc : ∀ i, (net q).Connects (play s (prof q ω) i) (prof q ω i).1 (prof q ω i).2) :
    ((1 + ∑ r, #((boughtLines s r (pt ω.1 (ω.2 r))).erase ω.1) : ℕ) : ℝ≥0∞) ≤
      (game q).stateCost (prof q ω) (play s (prof q ω)) := by
  obtain ⟨ℓ, π⟩ := ω
  rw [(net q).stateCost_bayesGame_of_forall _ hc]
  set a := play s (prof q (ℓ, π)) with ha
  have hsome : ∀ r, a (some r) = s (some r) (src, wP (pt ℓ (π r))) := fun r => rfl
  set BL : Finset (Line q) := {ℓ' | Sum.inl ℓ' ∈ univ.biUnion a}
  have h1 : (#BL : ℝ≥0) ≤ (net q).totalCost a := by
    unfold Network.totalCost
    calc (#BL : ℝ≥0) = ∑ e ∈ BL.map ⟨Sum.inl, Sum.inl_injective⟩, (net q).cost e := by simp
      _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset fun e he => ?_
        obtain ⟨ℓ', h, rfl⟩ := Finset.mem_map.1 he
        exact (mem_filter.1 h).2
  have hnone : Sum.inl ℓ ∈ a none := connects_vL_iff.1 (by simpa using hc none)
  have hdisj : ((univ : Finset (ZMod q)) : Set (ZMod q)).PairwiseDisjoint
      (fun r => (boughtLines s r (pt ℓ (π r))).erase ℓ) := by
    intro r _ r' _ hrr'
    refine Finset.disjoint_left.2 fun ℓ' h h' => hrr' ?_
    simp only [boughtLines, mem_erase, mem_filter, mem_univ, true_and] at h h'
    obtain ⟨hne, -, j, hj⟩ := h
    obtain ⟨-, -, j', hj'⟩ := h'
    exact π.injective (lines_meet (Ne.symm hne) hj.symm hj'.symm)
  have h2 : insert ℓ (univ.biUnion fun r => (boughtLines s r (pt ℓ (π r))).erase ℓ) ⊆ BL := by
    intro ℓ' h
    simp only [BL, mem_filter, mem_univ, true_and, mem_biUnion]
    rcases mem_insert.1 h with rfl | h
    · exact ⟨none, hnone⟩
    · obtain ⟨r, -, h⟩ := mem_biUnion.1 h
      simp only [boughtLines, mem_erase, mem_filter, mem_univ, true_and] at h
      exact ⟨some r, by rw [hsome]; exact h.2.1⟩
  have h3 : #(insert ℓ (univ.biUnion fun r => (boughtLines s r (pt ℓ (π r))).erase ℓ)) =
      1 + ∑ r, #((boughtLines s r (pt ℓ (π r))).erase ℓ) := by
    rw [card_insert_of_notMem (by simp), card_biUnion hdisj, add_comm]
  have h4 := Finset.card_le_card h2
  rw [h3] at h4
  calc ((1 + ∑ r, #((boughtLines s r (pt ℓ (π r))).erase ℓ) : ℕ) : ℝ≥0∞) ≤ (#BL : ℝ≥0∞) := by
        exact_mod_cast h4
    _ ≤ _ := by exact_mod_cast h1

lemma one_add_div_eq :
    1 + (q : ℝ≥0∞) ^ 2 / (q + 1) = ((q ^ 2 + q + 1 : ℕ) : ℝ≥0∞) / (q + 1) := by
  have hq1 : (q : ℝ≥0∞) + 1 ≠ 0 := by positivity
  have hq1t : (q : ℝ≥0∞) + 1 ≠ ⊤ := by simp
  refine (ENNReal.eq_div_iff hq1 hq1t).2 ?_
  rw [mul_add, ENNReal.mul_div_cancel hq1 hq1t]
  push_cast; ring

lemma le_one_add_div : (q : ℝ≥0∞) ≤ 1 + (q : ℝ≥0∞) ^ 2 / (q + 1) := by
  rw [one_add_div_eq, ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp))]
  have : q * (q + 1) ≤ q ^ 2 + q + 1 := by nlinarith
  exact_mod_cast this

lemma ennreal_bound {c M : ℕ} (hc : 0 < c) (h : c * (q ^ 2 + q + 1) ≤ M * (q + 1)) :
    1 + (q : ℝ≥0∞) ^ 2 / (q + 1) ≤ (c : ℝ≥0∞)⁻¹ * M := by
  have hq1 : (q : ℝ≥0∞) + 1 ≠ 0 := by positivity
  have hq1t : (q : ℝ≥0∞) + 1 ≠ ⊤ := by simp
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hct : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top c
  have e := one_add_div_eq (q := q)
  rw [e, ← ENNReal.div_eq_inv_mul, ENNReal.div_le_iff hq1 hq1t, mul_comm,
    ← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)]
  have : ((c * (q ^ 2 + q + 1) : ℕ) : ℝ≥0∞) ≤ ((M * (q + 1) : ℕ) : ℝ≥0∞) := by exact_mod_cast h
  push_cast at this
  calc _ = (c : ℝ≥0∞) * (q ^ 2 + q + 1) := by push_cast; ring
    _ ≤ _ := this
    _ = _ := by ring

/-- Lemma 3.2 of [Alon–Emek–Feldman–Tennenholtz 2010], partial-information side:
`opt^P(G) ≥ 1 + q² / (q + 1)` (`≥ q = k - 1`). Every strategy profile pays `1` for agent `k`'s edge,
and every agent `r` pays, in expectation, at least `q / (q + 1)` for a unit edge `(u, v ℓ')` with
`ℓ' ≠ ℓ`: given her point `p`, the line `ℓ` is uniform among the `q + 1` lines through `p`. -/
theorem optP_ge : 1 + (q : ℝ≥0∞) ^ 2 / (q + 1) ≤ (game q).optP := by
  refine le_iInf fun s => ?_
  rw [socialCost_eq, Network.bayesGame_prior, sum_prior]
  by_cases hall : ∀ ω (i : Agent q),
      (net q).Connects (play s (prof q ω) i) (prof q ω i).1 (prof q ω i).2
  swap
  · push Not at hall
    obtain ⟨ω, i, hi⟩ := hall
    have : ∑ ω : Omega q, (Fintype.card (Omega q) : ℝ≥0∞)⁻¹ *
        (game q).stateCost (prof q ω) (play s (prof q ω)) = ⊤ := by
      refine ENNReal.sum_eq_top.2 ⟨ω, mem_univ _, ?_⟩
      rw [(net q).stateCost_bayesGame_of_not _ hi]
      exact ENNReal.mul_top (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
    rw [this]; exact le_top
  -- every agent buys a unit edge through each of her possible points
  have hne : ∀ r p, (boughtLines s r p).Nonempty := by
    intro r p
    have hpt : pt (Sum.inr p.1) (Equiv.swap r p.2 r) = p := by simp [pt]
    have := hall (Sum.inr p.1, Equiv.swap r p.2) (some r)
    simp only [prof_fst, prof_some, hpt] at this
    obtain ⟨ℓ'', j, hp, h1, -⟩ := connects_wP_iff.1 this
    refine ⟨ℓ'', ?_⟩
    simp only [boughtLines, mem_filter, mem_univ, true_and]
    exact ⟨by simpa [play, prof, hpt, pt] using h1, j, hp⟩
  choose c hc using hne
  set P := Fintype.card (Equiv.Perm (ZMod q))
  set X : ZMod q → Omega q → ℕ := fun r ω => #((boughtLines s r (pt ω.1 (ω.2 r))).erase ω.1)
  have hA : ∀ r, P * q ^ 2 ≤ ∑ ω, X r ω := by
    intro r
    refine Nat.le_of_mul_le_mul_left ?_ hq.out.pos
    have hg : q ^ 3 ≤ ∑ x : Line q × ZMod q, #((boughtLines s r (pt x.1 x.2)).erase x.1) := by
      refine (card_ne_choice (c r)).trans ?_
      rw [Finset.card_filter]
      refine Finset.sum_le_sum fun x _ => ?_
      split_ifs with h
      · exact Finset.card_pos.2 ⟨c r (pt x.1 x.2), mem_erase.2 ⟨h, hc r _⟩⟩
      · exact Nat.zero_le _
    calc q * (P * q ^ 2) = P * q ^ 3 := by ring
      _ ≤ P * ∑ x : Line q × ZMod q, #((boughtLines s r (pt x.1 x.2)).erase x.1) :=
          Nat.mul_le_mul_left _ hg
      _ = q * ∑ ω, X r ω := by
          rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          exact (perm_avg (fun j => #((boughtLines s r (pt ℓ j)).erase ℓ)) r).symm
  have hB : P * q ^ 3 ≤ ∑ r, ∑ ω, X r ω := by
    calc P * q ^ 3 = ∑ _r : ZMod q, P * q ^ 2 := by simp [ZMod.card]; ring
      _ ≤ _ := Finset.sum_le_sum fun r _ => hA r
  have hsum : ∑ ω, (1 + ∑ r, X r ω) = Fintype.card (Omega q) + ∑ r, ∑ ω, X r ω := by
    rw [Finset.sum_add_distrib, Finset.sum_comm]; simp
  have hcard : Fintype.card (Omega q) = (q * q + q) * P := by
    simp [P, Omega, Line, ZMod.card]
  calc 1 + (q : ℝ≥0∞) ^ 2 / (q + 1)
      ≤ (Fintype.card (Omega q) : ℝ≥0∞)⁻¹ * ((∑ ω, (1 + ∑ r, X r ω) : ℕ) : ℝ≥0∞) := by
        refine ennreal_bound Fintype.card_pos ?_
        rw [hsum, hcard]
        nlinarith [Nat.mul_le_mul_right (q + 1) hB]
    _ = ∑ ω, (Fintype.card (Omega q) : ℝ≥0∞)⁻¹ * ((1 + ∑ r, X r ω : ℕ) : ℝ≥0∞) := by
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun ω _ => by gcongr; exact stateCost_ge s ω (hall ω)

/-! ### Lemma 3.2 -/

lemma exists_isNashEq {t : Agent q → Vtx q × Vtx q} (ht : (game q).prior t ≠ 0) :
    ∃ a, (game q).IsNashEq t a := by
  rw [Network.bayesGame_prior, ← PMF.mem_support_iff, prior, PMF.support_map] at ht
  obtain ⟨ω, -, rfl⟩ := ht
  exact ⟨good ω, isNashEq_good ω⟩

/-- Lemma 3.2 of [Alon–Emek–Feldman–Tennenholtz 2010] for the affine plane of prime order `q`:
the `(q + 1)`-agent Bayesian NCS game on the directed graph with `2q² + q + 1` vertices satisfies
`worst-eq^C(G) = 1` and `opt^P(G) ≥ 1 + q² / (q + 1) ≥ q`; consequently
`opt^P ≥ q · opt^C` and `best-eq^P ≥ q · best-eq^C`. -/
theorem lemma_3_2_prime :
    Fintype.card (Agent q) = q + 1 ∧ Fintype.card (Vtx q) = 2 * q ^ 2 + q + 1 ∧
    (game q).worstEqC = 1 ∧ 1 + (q : ℝ≥0∞) ^ 2 / (q + 1) ≤ (game q).optP ∧
    (q : ℝ≥0∞) ≤ (game q).optP ∧
    (q : ℝ≥0∞) * (game q).optC ≤ (game q).optP ∧
    (q : ℝ≥0∞) * (game q).bestEqC ≤ (game q).bestEqP := by
  have hbe : (game q).bestEqC ≤ 1 :=
    worstEqC_eq_one (q := q) ▸ (game q).bestEqC_le_worstEqC fun _ ht => exists_isNashEq ht
  have hP : (q : ℝ≥0∞) ≤ (game q).optP := le_one_add_div.trans optP_ge
  refine ⟨by simp [ZMod.card], by simp [ZMod.card]; ring, worstEqC_eq_one, optP_ge, hP, ?_, ?_⟩
  · calc (q : ℝ≥0∞) * (game q).optC ≤ q * 1 := by
          gcongr; exact (game q).optC_le_bestEqC.trans hbe
      _ ≤ _ := by simpa using hP
  · calc (q : ℝ≥0∞) * (game q).bestEqC ≤ q * 1 := by gcongr
      _ ≤ _ := by simpa using hP.trans (game q).optP_le_bestEqP

/-- Lemma 3.2 of [Alon–Emek–Feldman–Tennenholtz 2010]: for every `k₀` there exist `k ≥ k₀` and a
`k`-agent Bayesian NCS game `G` on a directed graph with `2(k-1)² + (k-1) + 1 = Θ(k²)` vertices such
that `opt^P(G) / worst-eq^C(G) ≥ k - 1` (indeed `worst-eq^C(G) = 1` and `opt^P(G) ≥ k - 1`).
Moreover `opt^P(G) ≥ (k-1) · opt^C(G)` and `best-eq^P(G) ≥ (k-1) · best-eq^C(G)`. -/
theorem lemma_3_2 (k₀ : ℕ) :
    ∃ k ≥ k₀, ∃ (ι V E : Type) (_ : Fintype ι) (_ : DecidableEq ι) (_ : Fintype V)
      (_ : DecidableEq V) (_ : Fintype E) (_ : DecidableEq E) (ends : E → V × V) (c : E → ℝ≥0)
      (p : PMF (ι → V × V)),
      Fintype.card ι = k ∧ Fintype.card V = 2 * (k - 1) ^ 2 + (k - 1) + 1 ∧
      ((Network.directed ends c).bayesGame p).worstEqC = 1 ∧
      ((k : ℝ≥0∞) - 1) ≤ ((Network.directed ends c).bayesGame p).optP ∧
      ((k : ℝ≥0∞) - 1) * ((Network.directed ends c).bayesGame p).optC ≤
        ((Network.directed ends c).bayesGame p).optP ∧
      ((k : ℝ≥0∞) - 1) * ((Network.directed ends c).bayesGame p).bestEqC ≤
        ((Network.directed ends c).bayesGame p).bestEqP := by
  obtain ⟨q, hq0, hq⟩ := Nat.exists_infinite_primes k₀
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := lemma_3_2_prime (q := q)
  have hk : ((q + 1 : ℕ) : ℝ≥0∞) - 1 = q := by push_cast; exact ENNReal.add_sub_cancel_right ENNReal.one_ne_top
  refine ⟨q + 1, by omega, Agent q, Vtx q, Edge q, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ends, ecost, prior q, h1, ?_, h3, ?_, ?_, ?_⟩
  · rw [h2]; simp
  · rw [hk]; exact h5
  · rw [hk]; exact h6
  · rw [hk]; exact h7

end Podc.BayesianIgnorance.Lemma32
