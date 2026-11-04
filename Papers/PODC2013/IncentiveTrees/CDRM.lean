import Papers.PODC2013.IncentiveTrees.Basic
import Papers.PODC2013.IncentiveTrees.Geometric

/-!
# Theorem 5: contribution-deterministic reward mechanisms (CDRM)

The reward of `p` is `R(x_p, y_p)` where `x_p = C(p)` and `y_p = C(T_p \ {p})`.
A function `R` is *successfully contribution-deterministic* if, for `x > 0`, `y ≥ 0`,
(i) `0 < ∂R/∂x < 1`, (ii) `0 < ∂R/∂y`, (iii) `φ x < R(x, y) < Φ x`,
(iv) `R(x' + x'', y) ≥ R(x', x'' + y) + R(x'', y)`.
The paper leaves `R(0, y)` unconstrained; we add right-continuity of `R(·, y)` at `0`
(equivalently, by (iii), `R(0, y) = 0`).

* `theorem_5`: such a mechanism satisfies nonnegative rewards, budget, CCI, CSI, `φ`-RPC, USA
  and UGSA; it violates URO **and PO** (the paper's statement "all properties except URO"
  includes PO, which fails since `R(x, y) < Φ x ≤ x`; Section 4.4 correctly says "except PO/URO").
* `example_i_cd`: the first CDRM example `R(x, y) = (Φ - θ / (1 + x + y)) x` (Algorithm 5)
  satisfies the hypotheses (non-vacuity).
-/

namespace Podc.IncentiveTrees

open Set

/-- The mechanism distributing rewards according to `R(x_p, y_p)`. -/
def cdrm (R : ℝ → ℝ → ℝ) : Mechanism
  | .node c ch => R c (ch.map Tree.total).sum

/-- Successfully contribution-deterministic functions (Section 6), plus right-continuity of
`R(·, y)` at `0`. -/
structure SuccessfullyCD (R : ℝ → ℝ → ℝ) (φ Φ : ℝ) : Prop where
  cont_x : ∀ y ≥ 0, ContinuousOn (fun x => R x y) (Ici 0)
  diff_x : ∀ y ≥ 0, ∀ x > 0, DifferentiableAt ℝ (fun x => R x y) x
  /-- (i), left inequality -/
  deriv_x_pos : ∀ y ≥ 0, ∀ x > 0, 0 < deriv (fun x => R x y) x
  /-- (i), right inequality -/
  deriv_x_lt_one : ∀ y ≥ 0, ∀ x > 0, deriv (fun x => R x y) x < 1
  diff_y : ∀ x > 0, ∀ y ≥ 0, DifferentiableAt ℝ (R x) y
  /-- (ii) -/
  deriv_y_pos : ∀ x > 0, ∀ y ≥ 0, 0 < deriv (R x) y
  /-- (iii), left inequality -/
  lower : ∀ x > 0, ∀ y ≥ 0, φ * x < R x y
  /-- (iii), right inequality -/
  upper : ∀ x > 0, ∀ y ≥ 0, R x y < Φ * x
  /-- (iv) -/
  split : ∀ x' > 0, ∀ x'' > 0, ∀ y ≥ 0, R x' (x'' + y) + R x'' y ≤ R (x' + x'') y

namespace SuccessfullyCD

variable {R : ℝ → ℝ → ℝ} {φ Φ : ℝ} (h : SuccessfullyCD R φ Φ)
include h

theorem zero (y : ℝ) (hy : 0 ≤ y) : R 0 y = 0 := by
  have h1 : Filter.Tendsto (fun x => R x y) (nhdsWithin 0 (Ioi 0)) (nhds (R 0 y)) :=
    ((h.cont_x y hy) 0 (mem_Ici.2 le_rfl)).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hl : Filter.Tendsto (fun x => φ * x) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have : Filter.Tendsto (fun x : ℝ => φ * x) (nhds 0) (nhds (φ * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hu : Filter.Tendsto (fun x => Φ * x) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have : Filter.Tendsto (fun x : ℝ => Φ * x) (nhds 0) (nhds (Φ * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun x => R x y) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ ?_ <;>
      filter_upwards [self_mem_nhdsWithin] with x hx
    · exact (h.lower x hx y hy).le
    · exact (h.upper x hx y hy).le
  exact tendsto_nhds_unique h1 h2

theorem strictMonoOn_x (y : ℝ) (hy : 0 ≤ y) : StrictMonoOn (fun x => R x y) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) (h.cont_x y hy) ?_
  intro x hx
  rw [interior_Ici] at hx
  exact h.deriv_x_pos y hy x hx

/-- (i) implies that profit `R(x, y) - x` is strictly decreasing in `x`. -/
theorem strictMonoOn_cost (y : ℝ) (hy : 0 ≤ y) :
    StrictMonoOn (fun x => x - R x y) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (continuousOn_id.sub (h.cont_x y hy)) ?_
  intro x hx
  rw [interior_Ici] at hx
  have hd : deriv (fun x => x - R x y) x = 1 - deriv (fun x => R x y) x := by
    have := (hasDerivAt_id x).sub (h.diff_x y hy x hx).hasDerivAt
    exact this.deriv
  rw [hd]
  linarith [h.deriv_x_lt_one y hy x hx]

theorem monotoneOn_y (x : ℝ) (hx : 0 ≤ x) : MonotoneOn (R x) (Ici 0) := by
  rcases hx.lt_or_eq with hx | rfl
  · refine (strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_).monotoneOn
    · exact fun y hy => (h.diff_y x hx y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact h.deriv_y_pos x hx y (le_of_lt hy)
  · intro y hy y' hy' _
    rw [h.zero y hy, h.zero y' hy']

theorem le_upper (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : R x y ≤ Φ * x := by
  rcases hx.lt_or_eq with hx | rfl
  · exact (h.upper x hx y hy).le
  · rw [h.zero y hy]; simp

theorem lower_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : φ * x ≤ R x y := by
  rcases hx.lt_or_eq with hx | rfl
  · exact (h.lower x hx y hy).le
  · rw [h.zero y hy]; simp

/-- (iv) and monotonicity in `y`: merging two Sybil identities never loses reward. -/
theorem superadd (m₁ m₂ E₁ E₂ : ℝ) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hE₁ : 0 ≤ E₁)
    (hE₂ : 0 ≤ E₂) : R m₁ E₁ + R m₂ E₂ ≤ R (m₁ + m₂) (E₁ + E₂) := by
  rcases hm₁.lt_or_eq with hm₁ | rfl
  · rcases hm₂.lt_or_eq with hm₂ | rfl
    · have hs := h.split m₁ hm₁ m₂ hm₂ (E₁ + E₂) (by positivity)
      have a1 : R m₁ E₁ ≤ R m₁ (m₂ + (E₁ + E₂)) :=
        h.monotoneOn_y m₁ hm₁.le (mem_Ici.2 hE₁) (mem_Ici.2 (by positivity)) (by linarith)
      have a2 : R m₂ E₂ ≤ R m₂ (E₁ + E₂) :=
        h.monotoneOn_y m₂ hm₂.le (mem_Ici.2 hE₂) (mem_Ici.2 (by positivity)) (by linarith)
      linarith
    · rw [h.zero E₂ hE₂, add_zero, add_zero]
      exact h.monotoneOn_y m₁ hm₁.le (mem_Ici.2 hE₁) (mem_Ici.2 (by positivity)) (by linarith)
  · rw [h.zero E₁ hE₁, zero_add, zero_add]
    exact h.monotoneOn_y m₂ hm₂ (mem_Ici.2 hE₂) (mem_Ici.2 (by positivity)) (by linarith)

end SuccessfullyCD

theorem Sybil.total_toTree : ∀ s : Sybil,
    s.toTree.total = s.mass + (s.reals.map Tree.total).sum := by
  refine Sybil.ind fun c s r ih => ?_
  simp only [Sybil.toTree, Tree.total, Sybil.mass, Sybil.reals, List.map_append, List.sum_append,
    List.map_map, sum_map_flatten_map, Function.comp_def]
  rw [List.map_congr_left (fun x hx => ih x hx), List.sum_map_add]
  ring

theorem Sybil.mass_nonneg : ∀ s : Sybil, s.Nonneg → 0 ≤ s.mass := by
  refine Sybil.ind fun c s r ih hs => ?_
  rw [Sybil.nonneg_node] at hs
  simp only [Sybil.mass]
  have : 0 ≤ (s.map Sybil.mass).sum :=
    List.sum_nonneg (by simpa using fun x hx => ih x hx (hs.2.1 x hx))
  linarith [hs.1]

theorem Sybil.realsTotal_nonneg : ∀ s : Sybil, s.Nonneg → 0 ≤ (s.reals.map Tree.total).sum := by
  refine Sybil.ind fun c s r ih hs => ?_
  rw [Sybil.nonneg_node] at hs
  simp only [Sybil.reals, List.map_append, List.sum_append, sum_map_flatten_map]
  have h1 : 0 ≤ (s.map fun x => (x.reals.map Tree.total).sum).sum :=
    List.sum_nonneg (by simpa using fun x hx => ih x hx (hs.2.1 x hx))
  have h2 : 0 ≤ (r.map Tree.total).sum :=
    List.sum_nonneg (by simpa using fun t ht => Tree.total_nonneg t (hs.2.2 t ht))
  linarith

theorem Tree.total_joinLeaf {d : ℝ} {T T' : Tree} (hJ : Tree.JoinLeaf d T T') :
    T'.total = T.total + d := by
  induction hJ with
  | atNode c l₁ l₂ => simp [Tree.total, Tree.leaf, List.sum_append]; ring
  | inChild c l₁ l₂ t t' _ ih => simp [Tree.total, List.sum_append, ih]; ring

theorem Tree.joinLeaf_node {d c : ℝ} {ch : List Tree} {T' : Tree}
    (hJ : Tree.JoinLeaf d (.node c ch) T') :
    ∃ ch', T' = .node c ch' ∧ (ch'.map Tree.total).sum = (ch.map Tree.total).sum + d := by
  cases hJ with
  | atNode _ l₁ l₂ => exact ⟨_, rfl, by simp [Tree.total, Tree.leaf, List.sum_append]; ring⟩
  | inChild _ l₁ l₂ t t' hJ' =>
    exact ⟨_, rfl, by simp [List.sum_append, Tree.total_joinLeaf hJ']; ring⟩

/-- Theorem 5 of [Lv–Moscibroda] (journal numbering; PODC Theorem 4.10), corrected:
a CDRM mechanism satisfies nonnegative rewards,
the budget constraint, CCI, CSI, `φ`-RPC, USA and UGSA; it violates URO and also PO. -/
theorem theorem_5 {R : ℝ → ℝ → ℝ} {φ Φ : ℝ} (hφ : 0 ≤ φ) (hΦ : Φ ≤ 1)
    (h : SuccessfullyCD R φ Φ) :
    NonnegReward (cdrm R) ∧ Budget (cdrm R) Φ ∧ CCI (cdrm R) ∧ CSI (cdrm R) ∧
      RPC (cdrm R) φ ∧ USA (cdrm R) ∧ UGSA (cdrm R) ∧ ¬ URO (cdrm R) ∧ ¬ PO (cdrm R) := by
  have hΦ0 : 0 ≤ Φ := by
    have := (h.lower 1 one_pos 0 le_rfl).trans (h.upper 1 one_pos 0 le_rfl)
    linarith
  have hy : ∀ ch : List Tree, (∀ t ∈ ch, t.Nonneg) → 0 ≤ (ch.map Tree.total).sum :=
    fun ch hch => List.sum_nonneg (by simpa using fun t ht => Tree.total_nonneg t (hch t ht))
  -- every Sybil tree earns at most `R(mass, real contribution)`
  have hsyb : ∀ s : Sybil, s.Nonneg →
      s.reward (cdrm R) ≤ R s.mass (s.reals.map Tree.total).sum := by
    refine Sybil.ind fun c s r ih hs => ?_
    rw [Sybil.nonneg_node] at hs
    obtain ⟨hc, hs', hr⟩ := hs
    -- children's bound, merged
    have hlist : ∀ l : List Sybil, (∀ x ∈ l, x ∈ s) →
        (l.map (Sybil.reward (cdrm R))).sum ≤
          R (l.map Sybil.mass).sum ((l.map fun x => (x.reals.map Tree.total).sum)).sum := by
      intro l hl
      induction l with
      | nil => simp [h.zero 0 le_rfl]
      | cons x l ihl =>
        have hx := hl x (by simp)
        have hl' : ∀ y ∈ l, y ∈ s := fun y hy => hl y (by simp [hy])
        simp only [List.map_cons, List.sum_cons]
        have e1 := ih x hx (hs' x hx)
        have e2 := ihl hl'
        have := h.superadd x.mass (l.map Sybil.mass).sum (x.reals.map Tree.total).sum
          ((l.map fun x => (x.reals.map Tree.total).sum)).sum (Sybil.mass_nonneg x (hs' x hx))
          (List.sum_nonneg (by simpa using fun y hy => Sybil.mass_nonneg y (hs' y (hl' y hy))))
          (Sybil.realsTotal_nonneg x (hs' x hx))
          (List.sum_nonneg (by
            simpa using fun y hy => Sybil.realsTotal_nonneg y (hs' y (hl' y hy))))
        linarith
    have hch := hlist s (fun x hx => hx)
    set M := (s.map Sybil.mass).sum
    set Es := (s.map fun x => (x.reals.map Tree.total).sum).sum
    set Er := (r.map Tree.total).sum
    have hM : 0 ≤ M := List.sum_nonneg (by simpa using fun x hx => Sybil.mass_nonneg x (hs' x hx))
    have hEs : 0 ≤ Es :=
      List.sum_nonneg (by simpa using fun x hx => Sybil.realsTotal_nonneg x (hs' x hx))
    have hEr : 0 ≤ Er := hy r hr
    have hyroot : ((s.map Sybil.toTree ++ r).map Tree.total).sum = M + (Es + Er) := by
      simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def]
      rw [List.map_congr_left (fun x _ => Sybil.total_toTree x), List.sum_map_add]
      simp only [M, Es, Er]
      ring
    have hreward : (Sybil.node c s r).reward (cdrm R) =
        R c (M + (Es + Er)) + (s.map (Sybil.reward (cdrm R))).sum := by
      simp only [Sybil.reward, Sybil.toTree, cdrm]
      rw [hyroot]
    have hreals : ((Sybil.node c s r).reals.map Tree.total).sum = Es + Er := by
      simp only [Sybil.reals, List.map_append, List.sum_append, sum_map_flatten_map, Es, Er]
    have hmass : (Sybil.node c s r).mass = c + M := by simp [Sybil.mass, M]
    rw [hreward, hreals, hmass]
    have hmono : R M Es ≤ R M (Es + Er) :=
      h.monotoneOn_y M hM (mem_Ici.2 hEs) (mem_Ici.2 (by positivity)) (by linarith)
    have hsplit : R c (M + (Es + Er)) + R M (Es + Er) ≤ R (c + M) (Es + Er) := by
      rcases hc.lt_or_eq with hc | rfl
      · rcases hM.lt_or_eq with hM' | hM'
        · exact h.split c hc M hM' _ (by positivity)
        · rw [← hM', h.zero _ (by positivity), add_zero, add_zero, zero_add]
      · rw [h.zero _ (by positivity), zero_add, zero_add]
    linarith
  -- the whole Sybil forest
  have hforest : ∀ (c : ℝ) (F : List Tree) (S : List Sybil), (∀ s ∈ S, s.Nonneg) →
      (S.map Sybil.reals).flatten.Perm F →
      (S.map (Sybil.reward (cdrm R))).sum ≤ R (S.map Sybil.mass).sum (F.map Tree.total).sum := by
    intro c F S hS hP
    rw [← (hP.map Tree.total).sum_eq, sum_map_flatten_map]
    clear hP
    induction S with
    | nil => simp [h.zero 0 le_rfl]
    | cons x S ih =>
      have hx := hS x (by simp)
      have hS' : ∀ y ∈ S, y.Nonneg := fun y hy => hS y (by simp [hy])
      simp only [List.map_cons, List.sum_cons]
      have := h.superadd x.mass (S.map Sybil.mass).sum (x.reals.map Tree.total).sum
        ((S.map fun x => (x.reals.map Tree.total).sum)).sum (Sybil.mass_nonneg x hx)
        (List.sum_nonneg (by simpa using fun y hy => Sybil.mass_nonneg y (hS' y hy)))
        (Sybil.realsTotal_nonneg x hx)
        (List.sum_nonneg (by simpa using fun y hy => Sybil.realsTotal_nonneg y (hS' y hy)))
      linarith [hsyb x hx, ih hS']
  have hUGSA : UGSA (cdrm R) := by
    intro c F S hc hF hS hP hm
    have h1 := hforest c F S hS hP
    have h2 := (h.strictMonoOn_cost _ (hy F hF)).monotoneOn (mem_Ici.2 hc)
      (mem_Ici.2 (hc.trans hm)) hm
    simp only [cdrm]
    linarith
  have hnPO : ¬ PO (cdrm R) := by
    intro hPO
    obtain ⟨F, -, hF, hlt⟩ := hPO 1 1 one_pos one_pos
    have := h.upper 1 one_pos _ (hy F hF)
    simp only [cdrm] at hlt
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, hUGSA.usa, hUGSA, fun hU => hnPO hU.po, hnPO⟩
  · rintro ⟨c, ch⟩ hT
    rw [Tree.nonneg_node] at hT
    have := h.lower_le c _ hT.1 (hy ch hT.2)
    simp only [cdrm]
    nlinarith [mul_nonneg hφ hT.1]
  · refine Tree.ind fun c ch ih hT => ?_
    rw [Tree.nonneg_node] at hT
    simp only [Tree.subtrees, Tree.total, List.map_cons, List.sum_cons, cdrm]
    rw [sum_map_flatten_map]
    have h1 := h.le_upper c _ hT.1 (hy ch hT.2)
    have h2 : (ch.map fun t => ((t.subtrees).map (cdrm R)).sum).sum ≤
        (ch.map fun t => Φ * t.total).sum :=
      List.sum_le_sum fun t ht => ih t ht (hT.2 t ht)
    rw [List.sum_map_mul_left] at h2
    linarith
  · intro c c' F hc hcc' hF
    exact h.strictMonoOn_x _ (hy F hF) (mem_Ici.2 hc) (mem_Ici.2 (hc.trans hcc'.le)) hcc'
  · rintro d ⟨c, ch⟩ T' hT hc hd hJ
    obtain ⟨ch', rfl, hsum⟩ := Tree.joinLeaf_node hJ
    rw [Tree.nonneg_node] at hT
    simp only [Tree.root] at hc
    simp only [cdrm, hsum]
    have hy0 := hy ch hT.2
    exact strictMonoOn_of_deriv_pos (convex_Ici 0)
      (fun y hy => (h.diff_y c hc y hy).continuousAt.continuousWithinAt)
      (fun y hy => by rw [interior_Ici] at hy; exact h.deriv_y_pos c hc y (le_of_lt hy))
      (mem_Ici.2 hy0) (mem_Ici.2 (by linarith)) (by linarith)
  · rintro ⟨c, ch⟩ hT
    rw [Tree.nonneg_node] at hT
    exact h.lower_le c _ hT.1 (hy ch hT.2)

end Podc.IncentiveTrees
