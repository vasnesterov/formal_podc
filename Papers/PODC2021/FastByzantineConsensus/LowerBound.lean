import Papers.PODC2021.FastByzantineConsensus.Executions
import Papers.PODC2021.FastByzantineConsensus.Influential
import Papers.PODC2021.FastByzantineConsensus.SmallCases

/-!
# Theorem 4.5: no `f`-resilient `t`-two-step consensus with `3f + 2t − 2` processes

Kuznetsov–Tonkikh–Zhang, *Revisiting Optimal Resilience of Fast Byzantine Consensus*, PODC 2021,
Theorem 4.5 (and the tight bound `5f − 1` for `t = f`), in the authenticated partially synchronous
model (ideal signatures).

* `no_fastConsensus_of_le`: no protocol for any `2 ≤ n ≤ 3f + 2t − 2` (with `t ≤ f`).
* `theorem_4_5`: the paper's statement, `n = 3f + 2t − 2` (with `n ≥ 2`, i.e. excluding the
  degenerate `f = 1, t = 0`, see `SmallCases.theorem_4_5_fails_f1_t0`).
* `theorem_4_5_tight`: `t = f`, `n = 5f − 2`.
-/

set_option linter.unusedSectionVars false

namespace FastByzantineConsensus

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [Fintype P] [DecidableEq P]

/-- The case `n ≥ 3f + 1` (hence `t ≥ 2`) of Theorem 4.5: the chain `ρ₁, …, ρ₅`. -/
theorem no_fastConsensus_main {A : Algorithm P M S V V} {Au : Auth P M K} {f t δ : ℕ}
    (hU : A.Unforging Au) (hδ : 0 < δ) (htf : t ≤ f) (h3f : 3 * f + 1 ≤ Fintype.card P)
    (hn : Fintype.card P ≤ 3 * f + 2 * t - 2) {a b : V} (hab : a ≠ b) :
    ¬ FastConsensus A Au f t δ := by
  rintro ⟨hA, hTS⟩
  set n := Fintype.card P with hn_def
  have ht2 : 2 ≤ t := by omega
  -- Lemma 4.4: an influential process
  obtain ⟨p, I, I', T, T', hII', hT, hT', hpT, hpT', hdisj, x, hx, x', hx', v, v', hv, hv', hvv'⟩ :=
    exists_influential A hA hU hTS hδ htf (by omega) hab
  -- the groups: P₁ = T', P₅ = T, P₂ ∪ P₃ ∪ P₄ = the rest, each of size ≤ f - 1, P₃ ≠ ∅
  set R := univ \ insert p (T ∪ T') with hR
  have hRc : R.card = n - 1 - 2 * t := by
    rw [hR, card_sdiff_of_subset (subset_univ _), card_univ, card_insert_of_notMem (by simp [hpT, hpT']),
      card_union_of_disjoint hdisj, hT, hT']
    omega
  obtain ⟨G3, hG3R, hG3c⟩ := exists_subset_card_eq (s := R) (n := f - 1) (by omega)
  obtain ⟨G2, hG2R, hG2c⟩ := exists_subset_card_eq (s := R \ G3)
    (n := min (f - 1) (R.card - (f - 1))) (by rw [card_sdiff_of_subset hG3R]; omega)
  have hG2R' : G2 ⊆ R := hG2R.trans sdiff_subset
  have hG4c : ((R \ G3) \ G2).card ≤ f - 1 := by
    rw [card_sdiff_of_subset hG2R, card_sdiff_of_subset hG3R]; omega
  have memR : ∀ {q}, q ∈ R ↔ q ≠ p ∧ q ∉ T ∧ q ∉ T' := by
    intro q; simp [hR]
  let g : P → ℕ := fun q => if q = p then 0 else if q ∈ T' then 1 else if q ∈ G2 then 2 else
    if q ∈ G3 then 3 else if q ∈ T then 5 else 4
  have hgp : ∀ q, g q = 0 ↔ q = p := by intro q; simp only [g]; split_ifs <;> simp_all
  have hg5 : ∀ q, g q ≤ 5 := by intro q; simp only [g]; split_ifs <;> omega
  have hgT : ∀ q, q ∈ T ↔ g q = 5 := by
    intro q
    constructor
    · intro hq
      have h1 : q ≠ p := fun e => hpT (e ▸ hq)
      have h2 : q ∉ T' := fun h' => disjoint_left.mp hdisj hq h'
      have h3 : q ∉ G2 := fun h' => (memR.mp (hG2R' h')).2.1 hq
      have h4 : q ∉ G3 := fun h' => (memR.mp (hG3R h')).2.1 hq
      simp [g, h1, h2, h3, h4, hq]
    · simp only [g]; split_ifs <;> simp_all
  have hgT' : ∀ q, q ∈ T' ↔ g q = 1 := by
    intro q
    constructor
    · intro hq
      have h1 : q ≠ p := fun e => hpT' (e ▸ hq)
      simp [g, h1, hq]
    · simp only [g]; split_ifs <;> simp_all
  have hg3 : ∀ q, q ∈ G3 → g q = 3 := by
    intro q hq
    obtain ⟨h1, h2, h3⟩ := memR.mp (hG3R hq)
    have h4 : q ∉ G2 := fun h' => (mem_sdiff.mp (hG2R h')).2 hq
    simp [g, h1, h3, h4, hq]
  -- the reversed labelling (mirror image, for `ρ₂`)
  let g' : P → ℕ := fun q => if g q = 0 then 0 else 6 - g q
  have hg' : ∀ q, (g q = 0 ∧ g' q = 0) ∨ (1 ≤ g q ∧ g q ≤ 5 ∧ g' q = 6 - g q) := by
    intro q; have := hg5 q; simp only [g']; split_ifs <;> omega
  -- sizes of the Byzantine sets `{p} ∪ P₄` and `{p} ∪ P₂`
  have hF4 : (F4 g).card ≤ f := by
    have : F4 g ⊆ insert p ((R \ G3) \ G2) := by
      intro q hq
      rw [mem_F4] at hq
      rw [mem_insert]
      by_cases hqp : q = p
      · exact Or.inl hqp
      right
      have h0 : g q ≠ 0 := fun e => hqp ((hgp q).mp e)
      have h4 : g q = 4 := by omega
      have h1 : q ∉ T' := fun h' => by rw [(hgT' q).mp h'] at h4; omega
      have h5 : q ∉ T := fun h' => by rw [(hgT q).mp h'] at h4; omega
      have h3 : q ∉ G3 := fun h' => by rw [hg3 q h'] at h4; omega
      have h2 : q ∉ G2 := fun h' => by
        simp only [g, hqp, h1, h', ite_true, ite_false] at h4; omega
      exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨memR.mpr ⟨hqp, h5, h1⟩, h3⟩, h2⟩
    have := (card_le_card this).trans (card_insert_le _ _)
    omega
  have hF4' : (F4 g').card ≤ f := by
    have : F4 g' ⊆ insert p G2 := by
      intro q hq
      rw [mem_F4] at hq
      rw [mem_insert]
      by_cases hqp : q = p
      · exact Or.inl hqp
      right
      have hq0 : g q ≠ 0 := fun e => hqp ((hgp q).mp e)
      have : g q = 2 := by simp only [g', hq0, ite_false] at hq; have := hg5 q; omega
      simp only [g, hqp, ite_false] at this
      split_ifs at this with h1 h2 <;> omega
    have := (card_le_card this).trans (card_insert_le _ _)
    omega
  -- `ρ₃`
  let F3 : Finset P := univ.filter fun q => g q = 0 ∨ g q = 3
  let r3 : P → P → Option V := fun q x =>
    if q = p then (if g x = 1 ∨ g x = 2 then some (I p) else some (I' p)) else some (I q)
  have hF3c : F3.card ≤ f := by
    have : F3 ⊆ insert p G3 := by
      intro q hq
      simp only [F3, mem_filter, mem_univ, true_and] at hq
      rw [mem_insert]
      by_cases hqp : q = p
      · exact Or.inl hqp
      right
      have : g q = 3 := by have := (hgp q); tauto
      simp only [g, hqp, ite_false] at this
      split_ifs at this with h1 h2 h3 <;> omega
    have := (card_le_card this).trans (card_insert_le _ _)
    omega
  have hupd : Function.update I p (I p) = I := Function.update_eq_self p I
  have hupd' : Function.update I p (I' p) = I' := by
    funext q
    by_cases hq : q = p
    · subst hq; simp
    · simp [hq, hII' q hq]
  have hside : SideHyp g p I (I p) (I' p) T F3 I r3 :=
    { hp := hgp
      hg := hg5
      hT5 := hgT
      hF3 := fun q => by simp [F3]
      hJ := fun _ _ => rfl
      hr3a := fun x hx => by
        simp only [r3, ite_true]; rw [ite_eq_left hx]
      hr3b := fun x hx => by
        simp only [r3, ite_true]; rw [ite_eq_right (by omega)]
      hr3 := fun q hq x => by
        have : q ≠ p := fun e => by rw [e, (hgp p).mpr rfl] at hq; omega
        simp [r3, this] }
  have hside' : SideHyp g' p I (I' p) (I p) T' F3 I r3 :=
    { hp := fun q => by
        rw [← hgp q]; have := hg' q; constructor <;> intro <;> omega
      hg := fun q => by have := hg' q; omega
      hT5 := fun q => by
        rw [hgT' q]; have := hg' q; constructor <;> intro <;> omega
      hF3 := fun q => by
        simp only [F3, mem_filter, mem_univ, true_and]; have := hg' q
        constructor <;> intro <;> omega
      hJ := fun _ _ => rfl
      hr3a := fun x hx => by
        simp only [r3, ite_true]
        rw [ite_eq_right (by have := hg' x; omega)]
      hr3b := fun x hx => by
        simp only [r3, ite_true]
        rw [ite_eq_left (by have := hg' x; omega)]
      hr3 := fun q hq x => by
        have hq3 : g q = 3 := by have := hg' q; omega
        have : q ≠ p := fun e => by rw [e, (hgp p).mpr rfl] at hq3; omega
        simp [r3, this] }
  -- decisions in `ρ₃` of a process of `P₁` and of a process of `P₅`
  set ρ3 := rho3 (M := M) A δ F3 I r3
  have hρ3V := rho3_valid (A := A) (J := I) (r3 := r3) hδ hF3c
  have hρ3A := rho3_authValid (A := A) (D := δ) (F3 := F3) (J := I) (r3 := r3) hU (Au := Au)
  obtain ⟨x1, hx1⟩ : T'.Nonempty := card_pos.mp (by omega)
  obtain ⟨x5, hx5⟩ : T.Nonempty := card_pos.mp (by omega)
  have hx1F : x1 ∉ ρ3.faulty := by
    simp [ρ3, templateRun, F3, (hgT' x1).mp hx1]
  have hx5F : x5 ∉ ρ3.faulty := by
    simp [ρ3, templateRun, F3, (hgT x5).mp hx5]
  obtain ⟨w1, hw1⟩ := hA.termination ρ3 hρ3V hρ3A x1 hx1F
  obtain ⟨w5, hw5⟩ := hA.termination ρ3 hρ3V hρ3A x5 hx5F
  have hw : w1 = w5 := hA.agreement ρ3 hρ3V hρ3A x1 hx1F x5 hx5F w1 w5 hw1 hw5
  -- a process of `P₃` in `ρ₅` and in `ρ₁`
  obtain ⟨x3, hx3⟩ : G3.Nonempty := card_pos.mp (by omega)
  have hx3T : x3 ∉ T := fun h' => (memR.mp (hG3R hx3)).2.1 h'
  have hx3T' : x3 ∉ T' := fun h' => (memR.mp (hG3R hx3)).2.2 h'
  obtain ⟨v3, hv3⟩ := hTS I T hT x3 hx3T
  obtain ⟨v3', hv3'⟩ := hTS I' T' hT' x3 hx3T'
  -- `ρ₅ ∼_{P₃} ρ₄ ∼_{P₁} ρ₃`
  have e1 : v3 = w1 := by
    refine decision_eq_rho4 hside hU hA hδ hF4 (hg3 x3 hx3) (by rw [hupd]; exact hv3)
      ((hgT' x1).mp hx1) hw1
  -- `ρ₁ ∼_{P₃} ρ₂ ∼_{P₅} ρ₃` (mirror image)
  have e5 : v3' = w5 := by
    refine decision_eq_rho4 hside' hU hA hδ hF4' (x3 := x3) (by simp [g', hg3 x3 hx3]) (by rw [hupd']; exact hv3')
      (x1 := x5) (by simp [g', (hgT x5).mp hx5]) hw5
  -- consensus values of `ρ₅` and `ρ₁`
  obtain ⟨τ3, -, hτ3⟩ := hv3
  obtain ⟨τ3', -, hτ3'⟩ := hv3'
  have f1 : v = v3 := tsRun_agree A hA hU hδ htf hT hx hx3T hv ⟨τ3, hτ3⟩
  have f2 : v' = v3' := tsRun_agree A hA hU hδ htf hT' hx' hx3T' hv' ⟨τ3', hτ3'⟩
  exact hvv' (by rw [f1, f2, e1, e5, hw])

/-- **Theorem 4.5 (general form).** For `t ≤ f`, there is no `f`-resilient `t`-two-step consensus
protocol (with weak validity, even with ideal signatures) for any number `2 ≤ n ≤ 3f + 2t − 2`
of processes. -/
theorem no_fastConsensus_of_le {A : Algorithm P M S V V} {Au : Auth P M K} {f t δ : ℕ}
    (hU : A.Unforging Au) (hδ : 0 < δ) (htf : t ≤ f) (h2 : 2 ≤ Fintype.card P)
    (hn : Fintype.card P ≤ 3 * f + 2 * t - 2) {a b : V} (hab : a ≠ b) :
    ¬ FastConsensus A Au f t δ := by
  rcases Nat.lt_or_ge (3 * f) (Fintype.card P) with h | h
  · exact no_fastConsensus_main hU hδ htf h hn hab
  · exact fun hF => not_solves_of_le_three_mul hU h2 h hab hF.1

/-- **Theorem 4.5 of [KTZ21].** There is no `f`-resilient `t`-two-step consensus protocol for
`3f + 2t − 2` processes (`t ≤ f`; we need `3f + 2t − 2 ≥ 2`, i.e. we exclude `f = 1, t = 0`, for
which the statement is false: `theorem_4_5_fails_f1_t0`). -/
theorem theorem_4_5 {A : Algorithm P M S V V} {Au : Auth P M K} {f t δ : ℕ}
    (hU : A.Unforging Au) (hδ : 0 < δ) (htf : t ≤ f) (h2 : 2 ≤ 3 * f + 2 * t - 2)
    (hn : Fintype.card P = 3 * f + 2 * t - 2) {a b : V} (hab : a ≠ b) :
    ¬ FastConsensus A Au f t δ :=
  no_fastConsensus_of_le hU hδ htf (hn ▸ h2) hn.le hab

/-- **Tightness of `5f − 1`** (abstract, `t = f`): no `f`-resilient `f`-two-step consensus
protocol with `n ≤ 5f − 2` processes (`f ≥ 1`, `n ≥ 2`). -/
theorem theorem_4_5_tight {A : Algorithm P M S V V} {Au : Auth P M K} {f δ : ℕ}
    (hU : A.Unforging Au) (hδ : 0 < δ) (h2 : 2 ≤ Fintype.card P)
    (hn : Fintype.card P ≤ 5 * f - 2) {a b : V} (hab : a ≠ b) :
    ¬ FastConsensus A Au f f δ :=
  no_fastConsensus_of_le hU hδ le_rfl h2 (by omega) hab

/-- Theorem 4.5 in the unauthenticated model. -/
theorem theorem_4_5_noAuth {A : Algorithm P M S V V} {f t δ : ℕ} (hδ : 0 < δ) (htf : t ≤ f)
    (h2 : 2 ≤ Fintype.card P) (hn : Fintype.card P ≤ 3 * f + 2 * t - 2) {a b : V} (hab : a ≠ b) :
    ¬ FastConsensus A (Auth.none P M) f t δ :=
  no_fastConsensus_of_le A.unforging_none hδ htf h2 hn hab

end FastByzantineConsensus
