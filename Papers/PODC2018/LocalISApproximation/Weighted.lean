import Papers.PODC2018.LocalISApproximation.Theorem1

/-!
# Section 3: weighted graphs (deterministic part)

Vertex weights `w : V → ℝ`, `w > 0` (the paper uses positive integers; real weights are more
general). `wClosed G w v = w(N[v])`. By Lemma 2 and linearity of expectation (eq. (7), proved in
`Lemma2.lean`), the expected weight of the output of the algorithm `Max` is
`maxValue G w = ∑_v w(v)²/w(N[v])`; everything in this file is about that quantity.

* `lemma3`, `lemma4`: Lemmas 3 and 4.
* `lemma5`: Lemma 5, with the missing hypothesis `Y > 0`; `lemma5_false`: Lemma 5 as stated
  (only `a > b > 0`, `Z - Y ≥ X > 0`) is false.
* `theorem6_upper`: the upper bound of Theorem 6: for every independent set `I` (in particular
  an optimal one) `w(I) · g_Δ(x) ≤ E[w(Max)]` for some `x ∈ [0,1]`, where
  `g_Δ(x) = x²/(Δ+x) + 1/(xΔ+1)`, hence `E[w(Max)] ≥ w(opt) · min_{[0,1]} g_Δ`.
* `theorem6_tight`: tightness on `K_{Δ,Δ}` with weights `1` and `β`.
* `theorem6_min_unbounded`: the paper writes `min_{x ≤ 1}`; over `x ≤ 1` the expression is not
  bounded below by a positive number (typo for `0 ≤ x ≤ 1`).
* `boppana_weighted`: unchanged Boppana: `E[w(B)] = ∑ w(v)/(d(v)+1) ≥ w(V)/(Δ+1)`;
  `boppana_weighted_not_Delta`: its ratio exceeds `Δ` on `K_{Δ,Δ}` with weights `1`, `Q > Δ`
  (so the abstract's "only a `Δ`-approximation" should read `Δ+1`).
-/

open Finset SimpleGraph

namespace Podc.LocalISApproximation

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (w : V → ℝ)

/-- `w(N[v])`, the weight of the closed neighbourhood. -/
def wClosed (v : V) : ℝ := w v + ∑ u ∈ G.neighborFinset v, w u

/-- `∑_v w(v)²/w(N[v])`: the expected weight of the output of `Max` (eq. (7) with `S = V`). -/
noncomputable def maxValue : ℝ := ∑ v, w v ^ 2 / wClosed G w v

/-- `g_Δ(x) = x²/(Δ+x) + 1/(xΔ+1)`; Theorem 6 says `1/ρ(Δ) = min_{0 ≤ x ≤ 1} g_Δ(x)`. -/
noncomputable def gFun (Δ : ℕ) (x : ℝ) : ℝ := x ^ 2 / (Δ + x) + 1 / (x * Δ + 1)

variable {G w}

omit [DecidableEq V] in
theorem wClosed_pos (hw : ∀ v, 0 < w v) (v : V) : 0 < wClosed G w v :=
  add_pos_of_pos_of_nonneg (hw v) (sum_nonneg fun u _ => (hw u).le)

omit [DecidableEq V] in
theorem maxValue_nonneg (hw : ∀ v, 0 < w v) : 0 ≤ maxValue G w :=
  sum_nonneg fun v _ => div_nonneg (sq_nonneg _) (wClosed_pos hw v).le

/-- Double counting: `∑_{v∈S} ∑_{u∈N(v)} f(u) = ∑_u f(u) · |N(u) ∩ S|`. -/
theorem sum_sum_neighbor (S : Finset V) (f : V → ℝ) :
    ∑ v ∈ S, ∑ u ∈ G.neighborFinset v, f u = ∑ u, f u * #(G.neighborFinset u ∩ S) := by
  have h1 : ∀ v, ∑ u ∈ G.neighborFinset v, f u = ∑ u, if G.Adj v u then f u else 0 := by
    intro v; rw [← sum_filter]; congr 1; ext u; simp
  simp_rw [h1]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 3
  ext v; simp [G.adj_comm, and_comm]

omit [DecidableEq V] in
/-- **Lemma 3** (with `x_v = w(N[v])`): `∑_{v∈S} w(v)²/w(N[v]) ≥ w(S)²/∑_{v∈S} w(N[v])`. -/
theorem lemma3 (hw : ∀ v, 0 < w v) (S : Finset V) :
    (∑ v ∈ S, w v) ^ 2 / ∑ v ∈ S, wClosed G w v ≤ ∑ v ∈ S, w v ^ 2 / wClosed G w v :=
  sq_sum_div_le_sum_sq_div S w fun v _ => wClosed_pos hw v

/-- `∑_v w(N[v]) = ∑_v (d(v)+1) w(v)`. -/
theorem sum_wClosed : ∑ v, wClosed G w v = ∑ v, ((G.degree v : ℝ) + 1) * w v := by
  rw [show ∑ v, wClosed G w v = ∑ v, w v + ∑ v ∈ univ, ∑ u ∈ G.neighborFinset v, w u by
    simp only [wClosed, sum_add_distrib], sum_sum_neighbor univ w, ← sum_add_distrib]
  refine sum_congr rfl fun v _ => ?_
  rw [inter_univ, card_neighborFinset_eq_degree]; ring

/-- **Lemma 4.** If all degrees are `≤ Δ`, then `E[w(Max)] ≥ w(V)²/∑_v w(N[v]) ≥ w(V)/(Δ+1)`. -/
theorem lemma4 (hw : ∀ v, 0 < w v) {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ) :
    (∑ v, w v) / (Δ + 1) ≤ maxValue G w := by
  have h3 := lemma3 (G := G) hw univ
  have hsum : ∑ v, wClosed G w v ≤ (Δ + 1) * ∑ v, w v := by
    rw [sum_wClosed, mul_sum]
    refine sum_le_sum fun v _ => mul_le_mul_of_nonneg_right ?_ (hw v).le
    have : (G.degree v : ℝ) ≤ Δ := by exact_mod_cast hdeg v
    linarith
  rcases isEmpty_or_nonempty V with hV | hV
  · simp [maxValue]
  have hW : 0 < ∑ v, w v := sum_pos (fun v _ => hw v) univ_nonempty
  have hC : 0 < ∑ v, wClosed G w v := sum_pos (fun v _ => wClosed_pos hw v) univ_nonempty
  refine le_trans ?_ h3
  rw [div_le_div_iff₀ (by positivity) hC]
  nlinarith

/-- **Lemma 5** (with the hypothesis `Y > 0`, missing in the paper; in the paper's use
`Y = w(opt) > 0`). If `a ≥ b ≥ 0`, `Y > 0`, `X ≥ 0` and `Z - Y ≥ X`, then on `t ∈ [0,1]` the function
`a/(Y+tX) + b/(Z+(1-t)X)` is minimized at `t = 1`. (The paper assumes `a > b > 0`, `X > 0`.) -/
theorem lemma5 {a b X Y Z t : ℝ} (hab : b ≤ a) (hb : 0 ≤ b) (hY : 0 < Y) (hX : 0 ≤ X)
    (hZ : Y + X ≤ Z) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a / (Y + X) + b / Z ≤ a / (Y + t * X) + b / (Z + (1 - t) * X) := by
  have hYt : 0 < Y + t * X := by nlinarith
  have hZ' : 0 < Z := by linarith
  have hZt : 0 < Z + (1 - t) * X := by nlinarith
  have e1 : a / (Y + t * X) - a / (Y + X) = (1 - t) * X * (a / ((Y + t * X) * (Y + X))) := by
    rw [div_sub_div _ _ hYt.ne' (by linarith), ← mul_div_assoc]; congr 1; ring
  have e2 : b / Z - b / (Z + (1 - t) * X) = (1 - t) * X * (b / (Z * (Z + (1 - t) * X))) := by
    rw [div_sub_div _ _ hZ'.ne' hZt.ne', ← mul_div_assoc]; congr 1; ring
  have hcmp : b / (Z * (Z + (1 - t) * X)) ≤ a / ((Y + t * X) * (Y + X)) := by
    have h1 : Y + t * X ≤ Z := by nlinarith
    have h2 : Y + X ≤ Z + (1 - t) * X := by nlinarith
    have hprod : (Y + t * X) * (Y + X) ≤ Z * (Z + (1 - t) * X) :=
      mul_le_mul h1 h2 (by linarith) hZ'.le
    calc b / (Z * (Z + (1 - t) * X)) ≤ b / ((Y + t * X) * (Y + X)) :=
          div_le_div_of_nonneg_left hb (by positivity) hprod
      _ ≤ a / ((Y + t * X) * (Y + X)) := div_le_div_of_nonneg_right hab (by positivity)
  have := mul_le_mul_of_nonneg_left hcmp (by nlinarith : 0 ≤ (1 - t) * X)
  linarith

/-- **Lemma 5 as stated is false**: with `a = 2 > b = 1 > 0`, `X = 1 > 0`, `Y = -100`,
`Z = -50` (so `Z - Y = 50 ≥ X`), the value at `t = 0` is smaller than at `t = 1`. -/
theorem lemma5_false : ∃ a b X Y Z : ℝ, a > b ∧ b > 0 ∧ Z - Y ≥ X ∧ X > 0 ∧
    a / (Y + 0 * X) + b / (Z + (1 - 0) * X) < a / (Y + 1 * X) + b / (Z + (1 - 1) * X) :=
  ⟨2, 1, 1, -100, -50, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The value `w(I)·g_Δ(β)` with `β = w(V∖I)/w(I)`. -/
theorem mul_gFun_eq {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (Δ : ℕ) :
    A * gFun Δ (B / A) = A ^ 2 / (A + Δ * B) + B ^ 2 / (B + Δ * A) := by
  unfold gFun
  have h1 : (Δ : ℝ) + B / A = (B + Δ * A) / A := by field_simp; ring
  have h2 : B / A * Δ + 1 = (A + Δ * B) / A := by field_simp; ring
  rw [h1, h2]
  rcases hB.eq_or_lt with rfl | hB
  · simp only [zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero, zero_add]
    field_simp
  · field_simp; ring

/-- **Theorem 6 (upper bound).** Let `Δ ≥ 1`, all degrees `≤ Δ`, weights positive. For every
independent set `I` (in particular an optimal one) there is `x ∈ [0,1]` with
`w(I) · g_Δ(x) ≤ E[w(Max)]`. Hence `E[w(Max)] ≥ w(opt) · min_{x∈[0,1]} g_Δ(x)`. -/
theorem theorem6_upper (hw : ∀ v, 0 < w v) {Δ : ℕ} (hΔ : 1 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ)
    {I : Finset V} (hI : G.IsIndepSet (I : Set V)) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, (∑ v ∈ I, w v) * gFun Δ x ≤ maxValue G w := by
  set A := ∑ v ∈ I, w v with hAdef
  set B := ∑ v ∈ Iᶜ, w v with hBdef
  have hA0 : 0 ≤ A := sum_nonneg fun v _ => (hw v).le
  have hB0 : 0 ≤ B := sum_nonneg fun v _ => (hw v).le
  have hΔ' : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  rcases hA0.eq_or_lt with hA | hA
  · exact ⟨0, ⟨le_refl _, zero_le_one⟩, by rw [← hA, zero_mul]; exact maxValue_nonneg hw⟩
  by_cases hBA : A ≤ B
  · -- `β ≥ 1`: Lemma 4.
    refine ⟨1, ⟨zero_le_one, le_refl _⟩, ?_⟩
    have h4 := lemma4 (G := G) hw hdeg
    rw [← sum_add_sum_compl I] at h4
    have : gFun Δ 1 = 2 / (Δ + 1) := by unfold gFun; field_simp; ring
    rw [this]
    refine le_trans ?_ h4
    rw [← hAdef, ← hBdef, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
    linarith
  push Not at hBA
  refine ⟨B / A, ⟨div_nonneg hB0 hA.le, (div_le_one hA).2 hBA.le⟩, ?_⟩
  rw [mul_gFun_eq hA hB0]
  -- `W` = weighted degree of `V'` into `opt`
  set W := ∑ v ∈ I, ∑ u ∈ G.neighborFinset v, w u with hWdef
  have hW' : W = ∑ u ∈ Iᶜ, w u * #(G.neighborFinset u ∩ I) := by
    rw [hWdef, sum_sum_neighbor, ← sum_add_sum_compl I, add_eq_right]
    refine sum_eq_zero fun u hu => ?_
    have : G.neighborFinset u ∩ I = ∅ := by
      ext v
      simp only [mem_inter, mem_neighborFinset, Finset.notMem_empty, iff_false, not_and]
      intro hadj hv
      exact hI (mem_coe.2 hu) (mem_coe.2 hv) hadj.ne hadj
    rw [this, card_empty, Nat.cast_zero, mul_zero]
  have hW0 : 0 ≤ W := sum_nonneg fun v _ => sum_nonneg fun u _ => (hw u).le
  have hcardle : ∀ u (S : Finset V), (#(G.neighborFinset u ∩ S) : ℝ) ≤ G.degree u := by
    intro u S
    rw [← card_neighborFinset_eq_degree]
    exact_mod_cast card_le_card inter_subset_left
  have hWX : W ≤ Δ * B := by
    rw [hW', hBdef, mul_sum]
    refine sum_le_sum fun u _ => ?_
    have : (#(G.neighborFinset u ∩ I) : ℝ) ≤ Δ :=
      (hcardle u I).trans (by exact_mod_cast hdeg u)
    nlinarith [hw u]
  -- eq. (9)
  have h9 : ∑ v ∈ I, wClosed G w v = A + W := by
    rw [hAdef, hWdef]; simp only [wClosed, sum_add_distrib]
  -- eq. (10)
  have h10 : ∑ v ∈ Iᶜ, wClosed G w v ≤ B + Δ * A + Δ * B - W := by
    simp only [wClosed, sum_add_distrib, ← hBdef]
    rw [sum_sum_neighbor, ← sum_add_sum_compl I]
    have hsplit : ∀ u, (#(G.neighborFinset u ∩ Iᶜ) : ℝ) + #(G.neighborFinset u ∩ I) =
        G.degree u := by
      intro u
      rw [← card_neighborFinset_eq_degree]
      have := card_inter_add_card_sdiff (G.neighborFinset u) I
      rw [sdiff_eq_inter_compl] at this
      rw [add_comm]
      exact_mod_cast this
    have hpart1 : ∑ u ∈ I, w u * #(G.neighborFinset u ∩ Iᶜ) ≤ Δ * A := by
      rw [hAdef, mul_sum]
      refine sum_le_sum fun u _ => ?_
      have : (#(G.neighborFinset u ∩ Iᶜ) : ℝ) ≤ Δ :=
        (hcardle u Iᶜ).trans (by exact_mod_cast hdeg u)
      nlinarith [hw u]
    have hpart2 : ∑ u ∈ Iᶜ, w u * #(G.neighborFinset u ∩ Iᶜ) ≤ Δ * B - W := by
      rw [hW', hBdef, mul_sum, ← sum_sub_distrib]
      refine sum_le_sum fun u _ => ?_
      have h1 := hsplit u
      have h2 : (G.degree u : ℝ) ≤ Δ := by exact_mod_cast hdeg u
      nlinarith [hw u]
    linarith
  -- eq. (8) and Lemma 3 on `opt` and `V'`
  have hS1 : A ^ 2 / (A + W) ≤ ∑ v ∈ I, w v ^ 2 / wClosed G w v := by
    have := lemma3 (G := G) hw I; rwa [h9] at this
  have hS2 : B ^ 2 / (B + Δ * A + Δ * B - W) ≤ ∑ v ∈ Iᶜ, w v ^ 2 / wClosed G w v := by
    have h3 := lemma3 (G := G) hw Iᶜ
    rcases hB0.eq_or_lt with hB | hB
    · rw [← hB]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
      exact sum_nonneg fun v _ => div_nonneg (sq_nonneg _) (wClosed_pos hw v).le
    have hne : Iᶜ.Nonempty := by
      by_contra h; rw [not_nonempty_iff_eq_empty] at h; rw [hBdef, h, sum_empty] at hB
      exact lt_irrefl _ hB
    have hpos : 0 < ∑ v ∈ Iᶜ, wClosed G w v := sum_pos (fun v _ => wClosed_pos hw v) hne
    refine le_trans (div_le_div_of_nonneg_left (sq_nonneg _) hpos h10) h3
  -- Lemma 5 with `a = w(opt)²`, `b = w(V')²`, `Y = w(opt)`, `Z = w(V') + Δ w(opt)`,
  -- `X = Δ w(V')`, `t = W/X`
  have h5 : A ^ 2 / (A + Δ * B) + B ^ 2 / (B + Δ * A) ≤
      A ^ 2 / (A + W) + B ^ 2 / (B + Δ * A + Δ * B - W) := by
    rcases (by positivity : (0 : ℝ) ≤ Δ * B).eq_or_lt with hX | hX
    · have hW : W = 0 := le_antisymm (hX ▸ hWX) hW0
      rw [← hX, hW]; simp
    have := lemma5 (a := A ^ 2) (b := B ^ 2) (X := Δ * B) (Y := A) (Z := B + Δ * A)
      (t := W / (Δ * B)) (by nlinarith) (sq_nonneg _) hA hX.le (by nlinarith)
      (div_nonneg hW0 hX.le) ((div_le_one hX).2 hWX)
    rw [div_mul_cancel₀ _ hX.ne'] at this
    have hB' : B ≠ 0 := by rintro h; rw [h, mul_zero] at hX; exact lt_irrefl _ hX
    have hΔ0 : (Δ : ℝ) ≠ 0 := by positivity
    convert this using 3; field_simp; ring
  calc A ^ 2 / (A + Δ * B) + B ^ 2 / (B + Δ * A)
      ≤ A ^ 2 / (A + W) + B ^ 2 / (B + Δ * A + Δ * B - W) := h5
    _ ≤ ∑ v ∈ I, w v ^ 2 / wClosed G w v + ∑ v ∈ Iᶜ, w v ^ 2 / wClosed G w v := add_le_add hS1 hS2
    _ = maxValue G w := by rw [maxValue, sum_add_sum_compl]

/-! ### Tightness on `K_{Δ,Δ}` -/

/-- In a complete bipartite graph an independent set lies within one side. -/
theorem completeBipartite_indep_side {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] {I : Finset (α ⊕ β)}
    (hI : (completeBipartiteGraph α β).IsIndepSet (I : Set (α ⊕ β))) :
    (∀ x ∈ I, x.isLeft) ∨ (∀ x ∈ I, x.isRight) := by
  by_contra h
  push Not at h
  obtain ⟨⟨x, hx, hxl⟩, ⟨y, hy, hyr⟩⟩ := h
  rcases x with a | b <;> rcases y with a' | b' <;> simp at hxl hyr
  exact hI (mem_coe.2 hy) (mem_coe.2 hx) (by simp) (by simp)

/-- **Theorem 6 (tightness).** On `K_{Δ,Δ}` with weights `1` on one side and `β ∈ (0,1]` on the
other, `w(opt) = Δ` and `E[w(Max)] = w(opt) · g_Δ(β)`. -/
theorem theorem6_tight {Δ : ℕ} {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    let K := completeBipartiteGraph (Fin Δ) (Fin Δ)
    let w : Fin Δ ⊕ Fin Δ → ℝ := Sum.elim (fun _ => 1) (fun _ => β)
    (∀ I : Finset (Fin Δ ⊕ Fin Δ), K.IsIndepSet (I : Set _) → ∑ v ∈ I, w v ≤ Δ) ∧
      (∃ I : Finset (Fin Δ ⊕ Fin Δ), K.IsIndepSet (I : Set _) ∧ ∑ v ∈ I, w v = Δ) ∧
      maxValue K w = Δ * gFun Δ β := by
  intro K w
  refine ⟨?_, ⟨univ.map Function.Embedding.inl, ?_, ?_⟩, ?_⟩
  · intro I hI
    have hcard : #I ≤ Δ * 1 ∨ True := Or.inr trivial
    clear hcard
    rcases completeBipartite_indep_side hI with h | h
    · have hsub : I ⊆ univ.map Function.Embedding.inl := by
        intro x hx; have := h x hx; rcases x with a | b <;> simp_all
      calc ∑ v ∈ I, w v ≤ ∑ v ∈ univ.map Function.Embedding.inl, w v :=
            sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by rcases x <;> simp [w, hβ0.le]
        _ = Δ := by simp [w]
    · have hsub : I ⊆ univ.map Function.Embedding.inr := by
        intro x hx; have := h x hx; rcases x with a | b <;> simp_all
      calc ∑ v ∈ I, w v ≤ ∑ v ∈ univ.map Function.Embedding.inr, w v :=
            sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by rcases x <;> simp [w, hβ0.le]
        _ = Δ * β := by simp [w]
        _ ≤ Δ := by nlinarith [(Nat.cast_nonneg Δ : (0 : ℝ) ≤ Δ)]
  · intro x hx y hy _ h
    simp only [coe_map, coe_univ, Set.image_univ, Set.mem_range, Function.Embedding.inl_apply]
      at hx hy
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
    simp [K] at h
  · simp [w]
  · have hl : ∀ a : Fin Δ, wClosed K w (Sum.inl a) = 1 + Δ * β := by
      intro a
      have : K.neighborFinset (Sum.inl a) = univ.map Function.Embedding.inr := by
        ext x; cases x <;> simp [K]
      simp [wClosed, this, w]
    have hr : ∀ b : Fin Δ, wClosed K w (Sum.inr b) = β + Δ := by
      intro b
      have : K.neighborFinset (Sum.inr b) = univ.map Function.Embedding.inl := by
        ext x; cases x <;> simp [K]
      simp [wClosed, this, w]
    simp only [maxValue, Fintype.sum_sum_type, hl, hr, w, Sum.elim_inl, Sum.elim_inr, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul, gFun]
    ring

/-- The paper writes `1/ρ = min_{x ≤ 1} g_Δ(x)`. Over all `x ≤ 1` the expression takes negative
values (e.g. at `x = -(Δ+1)`), so the minimum must be over `0 ≤ x ≤ 1` (where `x = β`). -/
theorem theorem6_min_unbounded {Δ : ℕ} (hΔ : 1 ≤ Δ) : ∃ x ≤ (1 : ℝ), gFun Δ x < 0 := by
  refine ⟨-(Δ + 1), by linarith [(Nat.cast_nonneg Δ : (0 : ℝ) ≤ Δ)], ?_⟩
  have hΔ' : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  unfold gFun
  have h1 : (Δ : ℝ) + -(Δ + 1) = -1 := by ring
  have h2 : -((Δ : ℝ) + 1) * Δ + 1 < 0 := by nlinarith
  rw [h1]
  have : 1 / (-((Δ : ℝ) + 1) * Δ + 1) < 0 := by rw [one_div_neg]; exact h2
  have h3 : (-((Δ : ℝ) + 1)) ^ 2 / -1 < 0 := by
    rw [div_neg, div_one, neg_neg_iff_pos, neg_sq]; positivity
  linarith

/-! ### Unchanged Boppana on weighted graphs -/

/-- Boppana's algorithm on weighted graphs: `E[w(B)] = ∑_v w(v)/(d(v)+1)` (the paper writes the
sum over `v ∈ B`, a typo for `v ∈ V`). -/
theorem boppana_weighted (w : V → ℝ) :
    (∑ σ : V ≃ Fin (Fintype.card V), ∑ v ∈ boppana G σ, w v) / (Fintype.card V).factorial =
      ∑ v, w v / ((G.degree v : ℝ) + 1) := by
  have hf : (0 : ℝ) < (Fintype.card V).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [div_eq_iff hf.ne', sum_mul]
  have : ∀ σ : V ≃ Fin (Fintype.card V), ∑ v ∈ boppana G σ, w v =
      ∑ v, if v ∈ boppana G σ then w v else 0 := fun σ => by rw [sum_ite_mem, univ_inter]
  simp_rw [this]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have h := card_boppana_mem (G := G) v
  have hd : (0 : ℝ) < G.degree v + 1 := by positivity
  have h' : ((G.degree v : ℝ) + 1) *
      #(univ.filter fun σ : V ≃ Fin (Fintype.card V) => v ∈ boppana G σ) =
      (Fintype.card V).factorial := by exact_mod_cast h
  rw [← h']
  field_simp

omit [DecidableEq V] in
/-- Unchanged Boppana has ratio at most `Δ+1` on weighted graphs:
`E[w(B)] ≥ w(V)/(Δ+1) ≥ w(I)/(Δ+1)` for every independent set `I`. -/
theorem boppana_weighted_ratio (hw : ∀ v, 0 < w v) {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ)
    (I : Finset V) : (∑ v ∈ I, w v) / (Δ + 1) ≤ ∑ v, w v / ((G.degree v : ℝ) + 1) := by
  calc (∑ v ∈ I, w v) / (Δ + 1) ≤ (∑ v, w v) / (Δ + 1) :=
        div_le_div_of_nonneg_right (sum_le_sum_of_subset_of_nonneg (subset_univ I)
          fun v _ _ => (hw v).le) (by positivity)
    _ = ∑ v, w v / ((Δ : ℝ) + 1) := by rw [sum_div]
    _ ≤ _ := sum_le_sum fun v _ => div_le_div_of_nonneg_left (hw v).le (by positivity)
          (by have : (G.degree v : ℝ) ≤ Δ := by exact_mod_cast hdeg v
              linarith)

/-- Unchanged Boppana is **not** a `Δ`-approximation on weighted graphs: on `K_{Δ,Δ}` with
weights `1` and `Q > Δ`, the independent side has weight `ΔQ > Δ · E[w(B)]`. (The text's
`Δ+1` is right; the abstract's "`Δ`-approximation" is not.) -/
theorem boppana_weighted_not_Delta {Δ : ℕ} (hΔ : 1 ≤ Δ) {Q : ℝ} (hQ : (Δ : ℝ) < Q) :
    let K := completeBipartiteGraph (Fin Δ) (Fin Δ)
    let w : Fin Δ ⊕ Fin Δ → ℝ := Sum.elim (fun _ => 1) (fun _ => Q)
    K.IsIndepSet ((univ.map Function.Embedding.inr : Finset (Fin Δ ⊕ Fin Δ)) : Set _) ∧
      (Δ : ℝ) * ∑ v, w v / ((K.degree v : ℝ) + 1) <
        ∑ v ∈ (univ.map Function.Embedding.inr : Finset (Fin Δ ⊕ Fin Δ)), w v := by
  intro K w
  have hΔ' : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  refine ⟨?_, ?_⟩
  · intro x hx y hy _ h
    simp only [coe_map, coe_univ, Set.image_univ, Set.mem_range, Function.Embedding.inr_apply]
      at hx hy
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
    simp [K] at h
  · simp only [Fintype.sum_sum_type, K, degree_completeBipartite_inl,
      degree_completeBipartite_inr, w, Sum.elim_inl, Sum.elim_inr, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, sum_map, Function.Embedding.inr_apply]
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, ← mul_div_assoc,
      div_lt_iff₀ (by positivity)]
    nlinarith

end Podc.LocalISApproximation
