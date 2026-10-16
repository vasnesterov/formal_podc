import Papers.PODC2016.VertexCoverLocalRatio.Main

/-!
# The CONGEST variant (Section 4)

Section 4 modifies Algorithm 1 so that answers fit in `O(log n)` bits: the vault becomes
`ε' w_0(v)/2`, and a request that cannot be answered in full is answered with `t·ε' w_0(v)/2` for
the largest integer `t` with `t·ε' w_0(v)/2 ≤ budget_i(v,u)` (where `budget_i(v,u)` is the
remaining bank, line 20). We read this as: `v` grants (and deducts) exactly the rounded amount, and
continues with the remaining bank (the paper does not say what happens to later requests).

Formally this is the response rule `congestRule` (`congest_spec`: it meets `Rule.Spec (θ/2)`), with
vault factor `a = θ/2`, so `a + σ = θ` and all results of the generic analysis apply:
* `congest_correct`: `(2+ε)`-approximation (Lemma 3.2 carries over);
* `congest_small`, `congest_large`: the round bounds of Lemma 3.3 with `c = 4` instead of `2`
  (`3(68+2E)/ε` and `3(4+3E)·log d/(ε log log d)` rounds).

Message sizes are not modelled (the LOCAL implementation sends whole states); only the arithmetic
of the modified rule is checked.
-/

set_option linter.unusedSectionVars false

namespace VertexCoverLocalRatio

open Finset SimpleGraph

/-- The amount granted to a request `rx` from a remaining bank `b`, in units of `u`. -/
noncomputable def cgrant (u b rx : ℝ) : ℝ := if rx ≤ b then rx else u * ⌊b / u⌋

theorem cgrant_nonneg {u b rx : ℝ} (hu : 0 ≤ u) (hb : 0 ≤ b) (hr : 0 ≤ rx) :
    0 ≤ cgrant u b rx := by
  unfold cgrant; split_ifs
  · exact hr
  · exact mul_nonneg hu (Int.cast_nonneg (Int.floor_nonneg.2 (div_nonneg hb hu)))

theorem cgrant_le_b {u b rx : ℝ} (hu : 0 ≤ u) (hb : 0 ≤ b) : cgrant u b rx ≤ b := by
  unfold cgrant; split_ifs with h
  · exact h
  · rcases hu.lt_or_eq with hu | hu
    · have := Int.floor_le (b / u)
      calc u * ⌊b / u⌋ ≤ u * (b / u) := by gcongr
        _ = b := by field_simp
    · rw [← hu]; simpa using hb

theorem cgrant_le_r {u b rx : ℝ} (hu : 0 ≤ u) (hb : 0 ≤ b) : cgrant u b rx ≤ rx := by
  by_cases h : rx ≤ b
  · unfold cgrant; rw [if_pos h]
  · exact (cgrant_le_b hu hb).trans (le_of_not_ge h)

theorem cgrant_partial {u b rx : ℝ} (hu : 0 < u) (h : cgrant u b rx < rx) :
    b - u < cgrant u b rx := by
  unfold cgrant at *
  split_ifs at * with hle
  · exact absurd h (lt_irrefl _)
  · have := Int.lt_floor_add_one (b / u)
    have h2 : b / u - 1 < (⌊b / u⌋ : ℝ) := by linarith
    have h3 : u * (b / u - 1) < u * ⌊b / u⌋ := mul_lt_mul_of_pos_left h2 hu
    rw [mul_sub, mul_div_cancel₀ _ hu.ne', mul_one] at h3
    exact h3

/-- Answer the requesters in the order of `l` with `cgrant`. -/
noncomputable def cgreedy {V : Type*} [DecidableEq V] (u b : ℝ) (r : V → ℝ) : List V → V → ℝ
  | [] => fun _ => 0
  | x :: l => Function.update (cgreedy u (b - cgrant u b (r x)) r l) x (cgrant u b (r x))

theorem cgreedy_props {V : Type*} [DecidableEq V] {u : ℝ} (hu : 0 ≤ u) (r : V → ℝ) :
    ∀ (l : List V), l.Nodup → ∀ b : ℝ, 0 ≤ b → (∀ x ∈ l, 0 ≤ r x) →
      (∀ x ∈ l, 0 ≤ cgreedy u b r l x ∧ cgreedy u b r l x ≤ r x) ∧
      ∑ x ∈ l.toFinset, cgreedy u b r l x ≤ b ∧
      (0 < u → ∀ x ∈ l, cgreedy u b r l x < r x → b - u ≤ ∑ x ∈ l.toFinset, cgreedy u b r l x)
  | [], _, b, hb, _ => by simp [cgreedy, hb]
  | y :: l, hnd, b, hb, hr => by
    rw [List.nodup_cons] at hnd
    set m := cgrant u b (r y)
    have hm0 : 0 ≤ m := cgrant_nonneg hu hb (hr y (by simp))
    have hmb : m ≤ b := cgrant_le_b hu hb
    obtain ⟨ih1, ih2, ih3⟩ := cgreedy_props hu r l hnd.2 (b - m) (by linarith)
      (fun x hx => hr x (by simp [hx]))
    set g' := cgreedy u (b - m) r l
    have hg : ∀ x ∈ l, cgreedy u b r (y :: l) x = g' x := by
      intro x hx
      have : x ≠ y := fun h => hnd.1 (h ▸ hx)
      simp only [cgreedy, Function.update_of_ne this, g', m]
    have hgy : cgreedy u b r (y :: l) y = m := by simp [cgreedy, m]
    have hsum : ∑ x ∈ (y :: l).toFinset, cgreedy u b r (y :: l) x =
        m + ∑ x ∈ l.toFinset, g' x := by
      rw [List.toFinset_cons, sum_insert (by simpa using hnd.1), hgy]
      congr 1
      exact sum_congr rfl fun x hx => hg x (by simpa using hx)
    have hS0 : 0 ≤ ∑ x ∈ l.toFinset, g' x :=
      sum_nonneg fun x hx => (ih1 x (by simpa using hx)).1
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hgy]; exact ⟨hm0, cgrant_le_r hu hb⟩
      · rw [hg x hx]; exact ih1 x hx
    · rw [hsum]; linarith
    · intro hu' x hx hlt
      rw [hsum]
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hgy] at hlt
        have := cgrant_partial hu' hlt
        linarith
      · rw [hg x hx] at hlt
        have := ih3 hu' x hx hlt
        linarith

/-- The CONGEST response rule (unit `θ·w_0(v)/2`), processing order `ord`. -/
noncomputable def congestRule {V : Type*} [DecidableEq V] (ord : V → Finset V → List V) (θ : ℝ) :
    Rule V :=
  fun v w0 b r S => cgreedy (θ / 2 * w0) b r (ord v S)

theorem congest_spec {V : Type*} [DecidableEq V] {ord : V → Finset V → List V}
    (hord : IsOrdering ord) {θ : ℝ} (hθ : 0 < θ) : (congestRule ord θ).Spec (θ / 2) := by
  intro v w0 b r S hb hbw hr
  obtain ⟨hnd, hS⟩ := hord v S
  have hm : ∀ u ∈ S, u ∈ ord v S := fun u hu => by rw [← hS] at hu; exact List.mem_toFinset.1 hu
  have hr' : ∀ u ∈ ord v S, 0 ≤ r u := fun u hu =>
    hr u (by rw [← hS]; exact List.mem_toFinset.2 hu)
  have hw0 : 0 ≤ w0 := hb.trans hbw
  have hu : 0 ≤ θ / 2 * w0 := mul_nonneg (by linarith) hw0
  obtain ⟨h1, h2, h3⟩ := cgreedy_props hu r (ord v S) hnd b hb hr'
  simp only [congestRule]
  rw [hS] at h2 h3
  refine ⟨fun u hu => h1 u (hm u hu), h2, fun u hu' hlt => ?_⟩
  rcases hw0.lt_or_eq with hw | hw
  · exact h3 (mul_pos (by linarith) hw) u (hm u hu') hlt
  · have hb0 : b = 0 := le_antisymm (hw ▸ hbw) hb
    have h0 : b - θ / 2 * w0 = 0 := by rw [hb0, ← hw]; ring
    rw [h0]
    exact sum_nonneg fun x hx => (h1 x (hm x hx)).1

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The CONGEST variant satisfies the hypotheses: vault `ε'/2`, slack `ε'/2`. -/
theorem hyp_congest {ε : ℝ} (hε : 0 < ε) {ord : V → Finset V → List V} (hord : IsOrdering ord)
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    Hyp (epsP ε) (epsP ε / 2) (epsP ε / 2) (congestRule ord (epsP ε)) w where
  ha := by have := epsP_pos hε; linarith
  hσ := by have := epsP_pos hε; linarith
  haσ := by linarith
  hθ := epsP_lt_one hε
  hR := congest_spec hord (epsP_pos hε)
  hw0 := hw

/-- The configuration after `t` rounds of the CONGEST variant. -/
noncomputable abbrev congestDist (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (ord : V → Finset V → List V) (w : V → ℝ) (t : ℕ) : V → NState V :=
  cfg G (epsP ε) (epsP ε / 2) (congestRule ord (epsP ε)) w t

/-- Section 4, correctness: the CONGEST variant terminates and is a `(2+ε)`-approximation. -/
theorem congest_correct {ε : ℝ} (hε : 0 < ε) {ord : V → Finset V → List V}
    (hord : IsOrdering ord) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    (∃ T, ∀ v, (congestDist G ε ord w T v).st ≠ .active) ∧
      ∀ t, (∀ v, (congestDist G ε ord w t v).st ≠ .active) →
        G.IsVertexCover ↑(coverAt (congestDist G ε ord w t)) ∧
        ∀ C : Finset V, G.IsVertexCover ↑C →
          wt w (coverAt (congestDist G ε ord w t)) ≤ (2 + ε) * wt w C := by
  have h := hyp_congest hε hord hw
  refine ⟨?_, fun t ht => ?_⟩
  · obtain ⟨T, hT⟩ := exists_all_returned h (G := G)
    refine ⟨3 * T, fun v => ?_⟩
    rw [cfg_st, show 3 * T / 3 = T by omega]
    exact hT v
  · have hT : ∀ v, (run G (epsP ε) (epsP ε / 2) (congestRule ord (epsP ε)) w (t / 3)).st v ≠
        .active := fun v => by rw [← cfg_st]; exact ht v
    have hC : coverAt (congestDist G ε ord w t) =
        output G (epsP ε) (epsP ε / 2) (congestRule ord (epsP ε)) w (t / 3) := by
      ext v; simp only [coverAt, output, mem_filter, mem_univ, true_and]; rw [cfg_st]
    rw [hC]
    obtain ⟨h1, -, h3⟩ := lemma_3_2 hε rfl h hT
    exact ⟨h1, h3⟩

theorem congest_bound {ε : ℝ} (hε : 0 < ε) {ord : V → Finset V → List V} (hord : IsOrdering ord)
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {v : V} {n : ℕ}
    (hv : (run G (epsP ε) (epsP ε / 2) (congestRule ord (epsP ε)) w n).st v = .active) {K : ℝ}
    (hK : 1 < K) : (n : ℝ) ≤ 4 * K / ε + Real.log (G.degree v) / Real.log K := by
  have := active_bound (hyp_congest hε hord hw) hv hK
  have he : K * (1 - epsP ε) / (epsP ε / 2) = 4 * K / ε := by
    have h2 : K * (1 - epsP ε) / (epsP ε / 2) = 2 * (K * (1 - epsP ε) / epsP ε) := by
      rw [div_div_eq_mul_div]; ring
    rw [h2, one_sub_epsP_div hε]; ring
  rwa [he] at this

/-- Section 4, rounds for `d(v) ≤ 16`: at most `3(68+2E)/ε` rounds. -/
theorem congest_small {E ε : ℝ} (hε : 0 < ε) (hεE : ε ≤ E) {ord : V → Finset V → List V}
    (hord : IsOrdering ord) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {v : V} (hd : G.degree v ≤ 16)
    {t : ℕ} (hv : (congestDist G ε ord w t v).st = .active) :
    (t : ℝ) < 3 * ((68 + 2 * E) / ε) := by
  rw [cfg_st] at hv
  have := small_of_bound hε hεE (by norm_num : (0 : ℝ) ≤ 4) hd fun _ hK =>
    congest_bound hε hord hw hv hK
  have := nat_lt_three_mul t
  norm_num at *
  linarith

/-- Section 4, rounds for `d(v) > 16`: at most `3(4+3E)·log d/(ε log log d)` rounds. -/
theorem congest_large {E ε : ℝ} (hε : 0 < ε) (hεE : ε ≤ E) {ord : V → Finset V → List V}
    (hord : IsOrdering ord) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {v : V} (hd : 16 < G.degree v)
    {t : ℕ} (hv : (congestDist G ε ord w t v).st = .active) :
    (t : ℝ) < 3 * ((4 + 3 * E) *
      (Real.log (G.degree v) / (ε * Real.log (Real.log (G.degree v))))) := by
  rw [cfg_st] at hv
  have := large_of_bound hε hεE hd fun _ hK => congest_bound hε hord hw hv hK
  have := nat_lt_three_mul t
  linarith

end VertexCoverLocalRatio
