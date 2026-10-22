import Papers.PODC2012.LineTreeScheduling.Approx

/-!
# Arbitrary heights: combining the wide and narrow algorithms (Theorems 6.3 and 7.2)

Instances are *wide* if `h(d) > 1/2` and *narrow* otherwise. Two overlapping wide instances never
fit together, so on the wide instances the unit-height algorithm applies; on the narrow ones the
algorithm of Section 6.1. The two solutions are combined network by network, keeping on each
network the more profitable of the two.

* `Inst.restrict` — the sub-instance on the instances satisfying a predicate.
* `combine`, `combine_feasible`, `profitOf_le_combine` — the combination step of Theorem 6.3.
* `combine_approx` — `p(Opt) ≤ (c₁ + c₂) p(S)` from `c₁`- and `c₂`-approximations on the two parts.
* `arbitrary_alg` — the complete algorithm on an abstract instance with networks and a layered
  decomposition: `(1-ε) p(Opt) ≤ ((Δ+1) + (1+2Δ²)) p(S)` (`80` for `Δ = 6`, `23` for `Δ = 3`).
-/

set_option linter.unusedSectionVars false

namespace Podc.LineTreeScheduling

open Finset

variable {A D E : Type*} [DecidableEq A] [DecidableEq D] [DecidableEq E]

noncomputable section

namespace Inst

variable (I : Inst A D E)

/-- The sub-instance consisting of the demand instances satisfying `q`. -/
def restrict (q : D → Prop) : Inst A {d // q d} E :=
  ⟨fun d => I.dem d.1, fun d => I.path d.1, fun d => I.profit d.1⟩

variable {I}

lemma restrict_isIndep {q : D → Prop} {S : Finset {d // q d}} :
    (I.restrict q).IsIndep S ↔ I.IsIndep (S.map (Function.Embedding.subtype q)) := by
  constructor
  · intro hS d₁ h₁ d₂ h₂ hne
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at h₁ h₂
    obtain ⟨d₁, h₁, rfl⟩ := h₁; obtain ⟨d₂, h₂, rfl⟩ := h₂
    exact hS d₁ h₁ d₂ h₂ (fun h => hne (by rw [h]))
  · intro hS d₁ h₁ d₂ h₂ hne
    exact hS d₁ (Finset.mem_map_of_mem _ h₁) d₂ (Finset.mem_map_of_mem _ h₂)
      (fun h => hne (Subtype.ext h))

lemma restrict_isHFeasible {q : D → Prop} {h : D → ℝ} {S : Finset {d // q d}} :
    (I.restrict q).IsHFeasible (fun d => h d.1) S ↔
      I.IsHFeasible h (S.map (Function.Embedding.subtype q)) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun d₁ h₁ d₂ h₂ hne => ?_, fun e => ?_⟩
    · simp only [Finset.mem_map, Function.Embedding.coe_subtype] at h₁ h₂
      obtain ⟨d₁, h₁, rfl⟩ := h₁; obtain ⟨d₂, h₂, rfl⟩ := h₂
      exact h1 d₁ h₁ d₂ h₂ (fun h => hne (by rw [h]))
    · rw [Finset.filter_map, Finset.sum_map]; exact h2 e
  · rintro ⟨h1, h2⟩
    refine ⟨fun d₁ h₁ d₂ h₂ hne => h1 d₁ (Finset.mem_map_of_mem _ h₁) d₂
      (Finset.mem_map_of_mem _ h₂) (fun h => hne (Subtype.ext h)), fun e => ?_⟩
    have := h2 e
    rw [Finset.filter_map, Finset.sum_map] at this
    exact this

lemma restrict_profitOf {q : D → Prop} (S : Finset {d // q d}) :
    (I.restrict q).profitOf S = I.profitOf (S.map (Function.Embedding.subtype q)) := by
  simp [profitOf, restrict]

/-- Every finite set of instances satisfying `q` comes from the restricted instance. -/
lemma map_subtype_eq {q : D → Prop} [DecidablePred q] {O : Finset D} (hO : ∀ d ∈ O, q d) :
    (O.subtype q).map (Function.Embedding.subtype q) = O := by
  ext d
  simp only [Finset.mem_map, Finset.mem_subtype, Function.Embedding.coe_subtype]
  exact ⟨fun ⟨d', h, e⟩ => e ▸ h, fun h => ⟨⟨d, hO d h⟩, h, rfl⟩⟩

/-- Restriction of a layered decomposition. -/
def Layered.restrict {Δ ℓ : ℕ} (L : I.Layered Δ ℓ) (q : D → Prop) :
    (I.restrict q).Layered Δ ℓ where
  grp d := L.grp d.1
  crit d := L.crit d.1
  grp_lt d := L.grp_lt d.1
  crit_subset d := L.crit_subset d.1
  card_crit d := L.card_crit d.1
  prop d₁ d₂ hg hov := L.prop d₁.1 d₂.1 hg hov

/-! ### The combination step -/

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Network by network, keep the more profitable of `S₁` and `S₂` (`net d` is the network of the
instance `d`). -/
def combine (net : D → Q) (S₁ S₂ : Finset D) : Finset D :=
  S₁.filter (fun d => ∑ d' ∈ S₂ with net d' = net d, I.profit d' ≤
      ∑ d' ∈ S₁ with net d' = net d, I.profit d') ∪
    S₂.filter (fun d => ¬ ∑ d' ∈ S₂ with net d' = net d, I.profit d' ≤
      ∑ d' ∈ S₁ with net d' = net d, I.profit d')

lemma profitOf_le_combine (net : D → Q) {S₁ S₂ : Finset D} (hdisj : Disjoint S₁ S₂) :
    max (I.profitOf S₁) (I.profitOf S₂) ≤ I.profitOf (I.combine net S₁ S₂) := by
  set c : Q → Prop := fun q => ∑ d' ∈ S₂ with net d' = q, I.profit d' ≤
      ∑ d' ∈ S₁ with net d' = q, I.profit d'
  have hfib : ∀ S : Finset D, I.profitOf S = ∑ q, ∑ d ∈ S with net d = q, I.profit d := by
    intro S; unfold profitOf; rw [Finset.sum_fiberwise]
  have hdisj' : Disjoint (S₁.filter (fun d => c (net d))) (S₂.filter (fun d => ¬ c (net d))) :=
    Finset.disjoint_filter_filter hdisj
  have hcomb : I.profitOf (I.combine net S₁ S₂) =
      ∑ q, max (∑ d ∈ S₁ with net d = q, I.profit d) (∑ d ∈ S₂ with net d = q, I.profit d) := by
    unfold combine
    change I.profitOf (S₁.filter (fun d => c (net d)) ∪ S₂.filter (fun d => ¬ c (net d))) = _
    rw [hfib, Finset.sum_congr rfl fun q _ => by
      rw [Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hdisj'),
        Finset.filter_filter, Finset.filter_filter]]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : c q
    · have e1 : S₁.filter (fun d => c (net d) ∧ net d = q) = S₁.filter (fun d => net d = q) :=
        Finset.filter_congr fun d _ => ⟨fun h => h.2, fun h => ⟨h ▸ hq, h⟩⟩
      have e2 : S₂.filter (fun d => ¬ c (net d) ∧ net d = q) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun d _ h => h.1 (h.2 ▸ hq)
      rw [e1, e2, Finset.sum_empty, add_zero, max_eq_left hq]
    · have e1 : S₁.filter (fun d => c (net d) ∧ net d = q) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun d _ h => hq (h.2 ▸ h.1)
      have e2 : S₂.filter (fun d => ¬ c (net d) ∧ net d = q) = S₂.filter (fun d => net d = q) :=
        Finset.filter_congr fun d _ => ⟨fun h => h.2, fun h => ⟨h ▸ hq, h⟩⟩
      rw [e1, e2, Finset.sum_empty, zero_add, max_eq_right (le_of_lt (not_le.1 hq))]
  rw [hcomb, hfib S₁, hfib S₂]
  exact max_le (Finset.sum_le_sum fun q _ => le_max_left _ _)
    (Finset.sum_le_sum fun q _ => le_max_right _ _)

lemma combine_feasible {h : D → ℝ} (hh0 : ∀ d, 0 ≤ h d) (hh1 : ∀ d, h d ≤ 1)
    (hdemh : ∀ d₁ d₂, I.dem d₁ = I.dem d₂ → h d₁ = h d₂) (net : D → Q)
    (hnet : ∀ d₁ d₂, I.Overlap d₁ d₂ → net d₁ = net d₂) {S₁ S₂ : Finset D}
    (hS₁ : I.IsIndep S₁) (hS₁w : ∀ d ∈ S₁, 1 / 2 < h d) (hS₂ : I.IsHFeasible h S₂)
    (hS₂n : ∀ d ∈ S₂, h d ≤ 1 / 2) : I.IsHFeasible h (I.combine net S₁ S₂) := by
  set c : Q → Prop := fun q => ∑ d' ∈ S₂ with net d' = q, I.profit d' ≤
      ∑ d' ∈ S₁ with net d' = q, I.profit d'
  change I.IsHFeasible h (S₁.filter (fun d => c (net d)) ∪ S₂.filter (fun d => ¬ c (net d)))
  refine ⟨fun d₁ h₁ d₂ h₂ hne hdem => ?_, fun e => ?_⟩
  · simp only [Finset.mem_union, Finset.mem_filter] at h₁ h₂
    have hh := hdemh d₁ d₂ hdem
    rcases h₁ with ⟨h₁, -⟩ | ⟨h₁, -⟩ <;> rcases h₂ with ⟨h₂, -⟩ | ⟨h₂, -⟩
    · exact hS₁ d₁ h₁ d₂ h₂ hne (Or.inl hdem)
    · linarith [hS₁w d₁ h₁, hS₂n d₂ h₂]
    · linarith [hS₁w d₂ h₂, hS₂n d₁ h₁]
    · exact hS₂.1 d₁ h₁ d₂ h₂ hne hdem
  · set F := (S₁.filter (fun d => c (net d)) ∪ S₂.filter (fun d => ¬ c (net d))).filter
      (fun d => e ∈ I.path d)
    by_cases hne : F.Nonempty
    · obtain ⟨d₀, hd₀⟩ := hne
      have hd₀e := (Finset.mem_filter.1 hd₀).2
      -- all instances of `F` lie on the network of `d₀`
      have hsame : ∀ d ∈ F, net d = net d₀ := fun d hd =>
        hnet d d₀ ⟨e, Finset.mem_inter.2 ⟨(Finset.mem_filter.1 hd).2, hd₀e⟩⟩
      by_cases hq : c (net d₀)
      · have hF : F ⊆ S₁.filter (fun d => e ∈ I.path d) := by
          intro d hd
          have hd' := Finset.mem_filter.1 hd
          rcases Finset.mem_union.1 hd'.1 with h1 | h1
          · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h1).1, hd'.2⟩
          · exact absurd (hsame d hd ▸ hq) (Finset.mem_filter.1 h1).2
        have hle : (S₁.filter (fun d => e ∈ I.path d)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          by_contra hab
          exact hS₁ a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1 hab
            (Or.inr ⟨e, Finset.mem_inter.2 ⟨(Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2⟩⟩)
        have hFle : F.card ≤ 1 := (Finset.card_le_card hF).trans hle
        have ha : F ⊆ {d₀} := fun d hd =>
          Finset.mem_singleton.2 (Finset.card_le_one.1 hFle d hd d₀ hd₀)
        calc ∑ d ∈ F, h d ≤ ∑ d ∈ {d₀}, h d :=
              Finset.sum_le_sum_of_subset_of_nonneg ha fun d _ _ => hh0 d
          _ ≤ 1 := by rw [Finset.sum_singleton]; exact hh1 d₀
      · have hF : F ⊆ S₂.filter (fun d => e ∈ I.path d) := by
          intro d hd
          have hd' := Finset.mem_filter.1 hd
          rcases Finset.mem_union.1 hd'.1 with h1 | h1
          · exact absurd ((Finset.mem_filter.1 h1).2) (hsame d hd ▸ hq)
          · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h1).1, hd'.2⟩
        exact (Finset.sum_le_sum_of_subset_of_nonneg hF fun d _ _ => hh0 d).trans (hS₂.2 e)
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]; norm_num

/-- `Opt ≤ Opt(wide) + Opt(narrow)`, and the combined solution: if `S₁` is a
`c₁`-approximation on the wide instances (against independent sets) and `S₂` a
`c₂`-approximation on the narrow ones (against feasible solutions), then the combined solution is
feasible and a `(c₁ + c₂)`-approximation. -/
theorem combine_approx {h : D → ℝ} (hh0 : ∀ d, 0 ≤ h d) (hh1 : ∀ d, h d ≤ 1)
    (hdemh : ∀ d₁ d₂, I.dem d₁ = I.dem d₂ → h d₁ = h d₂) (net : D → Q)
    (hnet : ∀ d₁ d₂, I.Overlap d₁ d₂ → net d₁ = net d₂) {S₁ S₂ : Finset D}
    (hS₁ : I.IsIndep S₁) (hS₁w : ∀ d ∈ S₁, 1 / 2 < h d) (hS₂ : I.IsHFeasible h S₂)
    (hS₂n : ∀ d ∈ S₂, h d ≤ 1 / 2) {c₁ c₂ : ℝ}
    (h₁ : ∀ O, I.IsIndep O → (∀ d ∈ O, 1 / 2 < h d) → I.profitOf O ≤ c₁ * I.profitOf S₁)
    (h₂ : ∀ O, I.IsHFeasible h O → (∀ d ∈ O, h d ≤ 1 / 2) → I.profitOf O ≤ c₂ * I.profitOf S₂)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    I.IsHFeasible h (I.combine net S₁ S₂) ∧
      ∀ O, I.IsHFeasible h O → I.profitOf O ≤ (c₁ + c₂) * I.profitOf (I.combine net S₁ S₂) := by
  refine ⟨combine_feasible hh0 hh1 hdemh net hnet hS₁ hS₁w hS₂ hS₂n, fun O hO => ?_⟩
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]; intro d h1 h2; linarith [hS₁w d h1, hS₂n d h2]
  have hmax := I.profitOf_le_combine net hdisj
  set Ow := O.filter (fun d => 1 / 2 < h d)
  set On := O.filter (fun d => ¬ 1 / 2 < h d)
  have hsplit : I.profitOf O = I.profitOf Ow + I.profitOf On := by
    unfold profitOf; rw [Finset.sum_filter_add_sum_filter_not]
  have hOw : I.IsIndep Ow := by
    intro d₁ h₁ d₂ h₂ hne hc
    have h₁' := Finset.mem_filter.1 h₁; have h₂' := Finset.mem_filter.1 h₂
    rcases hc with hdem | ⟨e, he⟩
    · exact hO.1 d₁ h₁'.1 d₂ h₂'.1 hne hdem
    · have hsub : ({d₁, d₂} : Finset D) ⊆ O.filter (fun d => e ∈ I.path d) := by
        intro d hd
        rcases Finset.mem_insert.1 hd with rfl | hd
        · exact Finset.mem_filter.2 ⟨h₁'.1, (Finset.mem_inter.1 he).1⟩
        · rw [Finset.mem_singleton.1 hd]
          exact Finset.mem_filter.2 ⟨h₂'.1, (Finset.mem_inter.1 he).2⟩
      have := (Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => hh0 d).trans (hO.2 e)
      rw [Finset.sum_pair hne] at this
      linarith [h₁'.2, h₂'.2]
  have hOn : I.IsHFeasible h On :=
    ⟨fun d₁ h₁ d₂ h₂ => hO.1 d₁ (Finset.mem_filter.1 h₁).1 d₂ (Finset.mem_filter.1 h₂).1,
      fun e => (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _
        (Finset.filter_subset _ O)) fun d _ _ => hh0 d).trans (hO.2 e)⟩
  have e1 := h₁ Ow hOw fun d hd => (Finset.mem_filter.1 hd).2
  have e2 := h₂ On hOn fun d hd => le_of_not_gt (Finset.mem_filter.1 hd).2
  have m1 := mul_le_mul_of_nonneg_left (le_max_left _ _ |>.trans hmax) hc₁
  have m2 := mul_le_mul_of_nonneg_left (le_max_right _ _ |>.trans hmax) hc₂
  linarith

/-! ### The complete algorithm for arbitrary heights -/

variable [Fintype A] [Fintype D] [Fintype E]

/-- Wide instances: `h(d) > 1/2`. -/
abbrev Wide (h : D → ℝ) (d : D) : Prop := 1 / 2 < h d
/-- Narrow instances: `h(d) ≤ 1/2`. -/
abbrev Narrow (h : D → ℝ) (d : D) : Prop := h d ≤ 1 / 2

/-- The output of the algorithm for arbitrary heights (Theorems 6.3 / 7.2): run the unit-height
algorithm (`bw` stages per epoch) on the wide instances and the narrow-instance algorithm (`bn`
stages per epoch) on the narrow ones, each with `K` steps per stage and its own MIS oracle, and
combine the two solutions network by network. -/
def arbSol {Δ ℓ : ℕ} (L : I.Layered Δ ℓ) (h : D → ℝ) (hmin : ℝ) (bw bn K : ℕ) (net : D → Q)
    (misW : ℕ → Finset {d // Wide h d} → Finset {d // Wide h d})
    (misN : ℕ → Finset {d // Narrow h d} → Finset {d // Narrow h d}) : Finset D :=
  I.combine net
    (((I.restrict (Wide h)).solU ((I.restrict (Wide h)).algI (unitRule (L.restrict (Wide h)).crit)
      ⟨(L.restrict (Wide h)).grp, bw, K, ξUnit Δ⟩ misW) (ℓ * bw * K)).map
      (Function.Embedding.subtype _))
    (((I.restrict (Narrow h)).solH (fun d => h d.1)
      ((I.restrict (Narrow h)).algI (narrowRule (fun d => h d.1) (L.restrict (Narrow h)).crit)
        ⟨(L.restrict (Narrow h)).grp, bn, K, ξNarrow Δ hmin⟩ misN) (ℓ * bn * K)).map
      (Function.Embedding.subtype _))

/-- **The algorithm for arbitrary heights** (Section 6, Theorem 6.3; Section 7, Theorem 7.2) on an
abstract instance with networks `net` (overlapping instances lie on the same network), heights
`h_min ≤ h ≤ 1` equal for all instances of a demand, and a layered decomposition with critical set
size `Δ` and length `ℓ`. For any MIS oracles, the output is feasible and
`(1-ε) · p(O) ≤ ((Δ+1) + (1+2Δ²)) · p(S)` for every feasible solution `O`. -/
theorem arbitrary_alg {Δ ℓ : ℕ} (L : I.Layered Δ ℓ) {h : D → ℝ} {hmin : ℝ} (hmin0 : 0 < hmin)
    (hmin12 : hmin ≤ 1 / 2) (hhmin : ∀ d, hmin ≤ h d) (hh1 : ∀ d, h d ≤ 1)
    (hdemh : ∀ d₁ d₂, I.dem d₁ = I.dem d₂ → h d₁ = h d₂) (net : D → Q)
    (hnet : ∀ d₁ d₂, I.Overlap d₁ d₂ → net d₁ = net d₂) {pmin pmax : ℝ} (hpmin0 : 0 < pmin)
    (hpmin : ∀ d, pmin ≤ I.profit d) (hpmax : ∀ d, I.profit d ≤ pmax) {ε : ℝ} (hε1 : ε < 1)
    {bw bn K : ℕ} (hbw : ξUnit Δ ^ bw ≤ ε) (hbn : ξNarrow Δ hmin ^ bn ≤ ε)
    (hK : pmax < 2 ^ K * pmin)
    {misW : ℕ → Finset {d // Wide h d} → Finset {d // Wide h d}}
    (hmisW : ∀ t U, (I.restrict (Wide h)).IsMIS U (misW t U))
    {misN : ℕ → Finset {d // Narrow h d} → Finset {d // Narrow h d}}
    (hmisN : ∀ t U, (I.restrict (Narrow h)).IsMIS U (misN t U)) :
    I.IsHFeasible h (I.arbSol L h hmin bw bn K net misW misN) ∧
      ∀ O, I.IsHFeasible h O →
        (1 - ε) * I.profitOf O ≤
          ((Δ + 1) + (1 + 2 * Δ ^ 2)) * I.profitOf (I.arbSol L h hmin bw bn K net misW misN) := by
  classical
  have hh0 : ∀ d, 0 ≤ h d := fun d => hmin0.le.trans (hhmin d)
  have h1ε : 0 < 1 - ε := by linarith
  -- the wide part
  obtain ⟨hSw, hapw⟩ := unit_alg (I := I.restrict (Wide h)) (L.restrict (Wide h)) hpmin0
    (fun d => hpmin d.1) (fun d => hpmax d.1) hbw hK hmisW (x := 0) ⟨fun _ => le_rfl,
      fun e => by simp, fun a => by simp⟩
  -- the narrow part
  set Sw := ((I.restrict (Wide h)).solU ((I.restrict (Wide h)).algI
    (unitRule (L.restrict (Wide h)).crit) ⟨(L.restrict (Wide h)).grp, bw, K, ξUnit Δ⟩ misW)
    (ℓ * bw * K))
  set Sn := ((I.restrict (Narrow h)).solH (fun d => h d.1)
      ((I.restrict (Narrow h)).algI (narrowRule (fun d => h d.1) (L.restrict (Narrow h)).crit)
        ⟨(L.restrict (Narrow h)).grp, bn, K, ξNarrow Δ hmin⟩ misN) (ℓ * bn * K))
  have hwide : ∀ O : Finset D, I.IsIndep O → (∀ d ∈ O, Wide h d) →
      I.profitOf O ≤ ((Δ + 1) / (1 - ε)) * I.profitOf (Sw.map (Function.Embedding.subtype _)) := by
    intro O hO hOw
    have hO' : (I.restrict (Wide h)).IsIndep (O.subtype (Wide h)) := by
      rw [restrict_isIndep, map_subtype_eq hOw]; exact hO
    have := (unit_alg (I := I.restrict (Wide h)) (L.restrict (Wide h)) hpmin0
      (fun d => hpmin d.1) (fun d => hpmax d.1) hbw hK hmisW
      (Inst.IsIndep.isLPFeasible _ hO')).2
    rw [lpValue_ind, restrict_profitOf, restrict_profitOf, map_subtype_eq hOw] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
    linarith
  have hnarrow : ∀ O : Finset D, I.IsHFeasible h O → (∀ d ∈ O, Narrow h d) →
      I.profitOf O ≤ ((1 + 2 * Δ ^ 2) / (1 - ε)) *
        I.profitOf (Sn.map (Function.Embedding.subtype _)) := by
    intro O hO hOn
    have hO' : (I.restrict (Narrow h)).IsHFeasible (fun d => h d.1) (O.subtype (Narrow h)) := by
      rw [restrict_isHFeasible, map_subtype_eq hOn]; exact hO
    have := (narrow_alg (I := I.restrict (Narrow h)) (L.restrict (Narrow h)) hmin0 hmin12
      (fun d => hhmin d.1) (fun d => d.2) hpmin0 (fun d => hpmin d.1) (fun d => hpmax d.1) hbn hK
      hmisN (Inst.IsHFeasible.isLPFeasible _ hO')).2
    rw [lpValue_ind, restrict_profitOf, restrict_profitOf, map_subtype_eq hOn] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
    linarith
  have hSn := (narrow_alg (I := I.restrict (Narrow h)) (L.restrict (Narrow h)) hmin0 hmin12
      (fun d => hhmin d.1) (fun d => d.2) hpmin0 (fun d => hpmin d.1) (fun d => hpmax d.1) hbn hK
      hmisN (x := 0) ⟨fun _ => le_rfl, fun e => by simp, fun a => by simp⟩).1
  obtain ⟨hfeas, happ⟩ := combine_approx hh0 hh1 hdemh net hnet (restrict_isIndep.1 hSw)
    (fun d hd => by
      obtain ⟨d', -, rfl⟩ := Finset.mem_map.1 hd; exact d'.2)
    (restrict_isHFeasible.1 hSn)
    (fun d hd => by
      obtain ⟨d', -, rfl⟩ := Finset.mem_map.1 hd; exact d'.2)
    hwide hnarrow (by positivity) (by positivity)
  refine ⟨hfeas, fun O hO => ?_⟩
  have := happ O hO
  rw [← add_div, div_mul_eq_mul_div, le_div_iff₀ h1ε] at this
  unfold arbSol
  linarith

end Inst

end

end Podc.LineTreeScheduling
