import Papers.PODC2010.TruncatedGaleShapley.Analysis

/-!
# Theorems 1 and 2 for the truncated Gale–Shapley algorithm (§6.1, §6.2), centralised form

* `matchingEdges_sum`: the weight of a matching equals the sum of `w {v, p(v)}` over the nodes of
  either colour.
* `theorem_1_rounds`: after `i ≥ 2` rounds with `i ≥ 1 + Δ(Δ-1)/ε`, the matching `M_i` is
  `ε`-stable.
* `theorem_2_rounds`: if the preferences respect the weights, then after `i ≥ 2` rounds with
  `i ≥ 1 + (Δ-1)/ε`, every matching `M*` has `w(M*) ≤ (2+ε) w(M_i)`.

The distributed statements (an algorithm in the port-numbering model with `T = 2i` communication
rounds) are in `Distributed.lean`.
-/

namespace Podc.TruncatedGaleShapley

open Finset

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Bicoloured

variable {I : Bicoloured V}

/-- The weight of the matching described by `s.p` is the sum of `w {v, p(v)}` over the nodes of
colour `col`. -/
lemma matchingEdges_sum {s : State V} (hs : I.IsMatching s.p) (w : Sym2 V → ℝ) (col : Bool) :
    ∑ e ∈ matchingEdges s.p, w e = ∑ v ∈ univ.filter (fun v => I.red v = col), nodeW s w v := by
  classical
  set D := univ.filter fun x : V × V => s.p x.1 = some x.2 ∧ I.red x.1 = col
  have hD : matchingEdges s.p = D.image fun x => s(x.1, x.2) := by
    ext e
    simp only [matchingEdges, mem_image, mem_filter, mem_univ, true_and, D]
    constructor
    · rintro ⟨⟨u, v⟩, h, rfl⟩
      by_cases hu : I.red u = col
      · exact ⟨(u, v), ⟨h, hu⟩, rfl⟩
      · refine ⟨(v, u), ⟨hs.symm u v h, ?_⟩, Sym2.eq_swap⟩
        have := I.red_ne (hs.mem_N u v h)
        revert this hu; cases I.red u <;> cases I.red v <;> cases col <;> simp
    · rintro ⟨x, ⟨h, -⟩, rfl⟩; exact ⟨x, h, rfl⟩
  have hinj : Set.InjOn (fun x : V × V => s(x.1, x.2)) D := by
    rintro ⟨a, b⟩ ha ⟨a', b'⟩ ha' h
    simp only [D, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha ha'
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only at h1 h2; rw [h1, h2]
    · exfalso
      simp only at h1 h2
      have := I.red_ne (hs.mem_N a' b' ha'.1)
      rw [← h1, ha.2, ha'.2] at this; exact this rfl
  rw [hD, sum_image hinj, sum_filter, sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun v _ => ?_
  by_cases hv : I.red v = col
  · simp only [hv, and_true, ite_true]
    unfold nodeW
    rcases s.p v with _ | u
    · simp
    · simp
  · simp [hv]

/-- The matching weight `w(M_i)` equals the blue weight `w_i(B)`. -/
lemma sum_matchingEdges_eq_blueW {s : State V} (hs : I.IsMatching s.p) (w : Sym2 V → ℝ) :
    ∑ e ∈ matchingEdges s.p, w e = I.blueW s w := by
  rw [matchingEdges_sum hs w false]; rfl

lemma Inv.isMatching {s : State V} (hs : I.Inv s) : I.IsMatching s.p := ⟨hs.p_mem, hs.p_symm⟩

lemma isMatching_run (i : ℕ) : I.IsMatching (I.run i).p := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact ⟨fun u v h => by simp [run_zero] at h, fun u v h => by simp [run_zero] at h⟩
  · exact (I.inv_run hi).isMatching

lemma C_sub_run (i : ℕ) {r : V} (hr : I.red r = true) : (I.run i).C r ⊆ I.N r := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [run_zero, hr]
  · exact (I.inv_run hi).C_sub r hr

/-- With unit weights, the number of unstable edges is at most `Δ f_i(R)` (§6.1). -/
lemma card_unstableEdges_le {Δ : ℕ} (hΔ : ∀ v, (I.N v).card ≤ Δ) (i : ℕ) :
    ((I.unstableEdges (I.run i).p).card : ℝ) ≤ Δ * I.potR (I.run i) (fun _ => 1) := by
  classical
  set s := I.run i
  set T := univ.filter fun x : V × V => I.red x.1 = true ∧ s.p x.1 = none ∧ x.2 ∈ s.C x.1
  have hsub : I.unstableEdges s.p ⊆ T.image fun x => s(x.1, x.2) := by
    intro e he
    simp only [PrefGraph.unstableEdges, mem_image, mem_filter, mem_univ, true_and] at he
    obtain ⟨⟨u, v⟩, h, rfl⟩ := he
    simp only [mem_image, mem_filter, mem_univ, true_and, T]
    by_cases hu : I.red u = true
    · exact ⟨(u, v), ⟨hu, (lemma_1 i hu h).2, (lemma_1 i hu h).1⟩, rfl⟩
    · have hv : I.red v = true := red_of_mem_blue h.1 (by simpa using hu)
      have h' := I.isUnstable_comm.1 h
      exact ⟨(v, u), ⟨hv, (lemma_1 i hv h').2, (lemma_1 i hv h').1⟩, Sym2.eq_swap⟩
  have h1 : ((I.unstableEdges s.p).card : ℝ) ≤ T.card := by
    exact_mod_cast (card_le_card hsub).trans card_image_le
  have hT : (T.card : ℝ) = ∑ r ∈ I.reds, (if s.p r = none then ((s.C r).card : ℝ) else 0) := by
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, Fintype.sum_prod_type, reds, sum_filter]
    refine sum_congr rfl fun r _ => ?_
    by_cases hr : I.red r = true
    · by_cases hp : s.p r = none
      · simp [hr, hp]
      · simp [hr, hp]
    · simp [hr]
  rw [hT] at h1
  rw [potR, mul_sum]
  refine h1.trans (sum_le_sum fun r hr => ?_)
  have hr := I.mem_reds.1 hr
  by_cases hp : s.p r = none
  · rw [pot_of_unmatched hp]; simp only [hp, ↓reduceIte]
    rcases hb : I.best r (s.C r) with _ | b
    · rw [I.best_eq_none.1 hb]; simp
    · have : (s.C r).card ≤ Δ := (card_le_card (C_sub_run i hr)).trans (hΔ r)
      simp only [mul_one]; exact_mod_cast this
  · simp only [hp, ↓reduceIte]
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hp
    rw [pot_of_matched hb]; simp

/-- **Theorem 1** (centralised core, §6.1). If all degrees are at most `Δ`, `ε > 0`, `i ≥ 2` and
`i ≥ 1 + Δ(Δ-1)/ε`, then the matching `M_i` after `i` rounds is `ε`-stable. -/
theorem theorem_1_rounds {Δ : ℕ} (hΔ : ∀ v, (I.N v).card ≤ Δ) {ε : ℝ} (hε : 0 < ε) {i : ℕ}
    (hi2 : 2 ≤ i) (hi : 1 + ((Δ : ℝ) * ((Δ - 1 : ℕ) : ℝ)) / ε ≤ i) :
    I.IsEpsStable ε (I.run i).p := by
  have hw := I.respectsPrefs_one
  have hu := card_unstableEdges_le hΔ i
  have h4 := lemma_4 hw (i := i) (by omega)
  have h5 := lemma_5 hw hΔ (i := i) (by omega)
  have hM : ((matchingEdges (I.run i).p).card : ℝ) = I.blueW (I.run i) (fun _ => 1) := by
    rw [← sum_matchingEdges_eq_blueW (isMatching_run i)]; simp
  rw [PrefGraph.isEpsStable_iff, hM]
  have hf := potR_nonneg hw (I.run i)
  have hW := blueW_nonneg hw (I.run i)
  have hi1 : (1 : ℝ) ≤ (i : ℝ) - 1 := by
    have : (2 : ℝ) ≤ i := by exact_mod_cast hi2
    linarith
  have hc : (Δ : ℝ) * ((Δ - 1 : ℕ) : ℝ) ≤ ε * ((i : ℝ) - 1) := by
    have := (div_le_iff₀ hε).1 (by linarith : (Δ : ℝ) * ((Δ - 1 : ℕ) : ℝ) / ε ≤ (i : ℝ) - 1)
    linarith
  set u := ((I.unstableEdges (I.run i).p).card : ℝ)
  set f := I.potR (I.run i) (fun _ => 1)
  set W := I.blueW (I.run i) (fun _ => 1)
  set L := I.lostW (I.run i) (fun _ => 1)
  set a := ((Δ - 1 : ℕ) : ℝ)
  have hd : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
  have e1 : ((i : ℝ) - 1) * u ≤ (Δ : ℝ) * (((i : ℝ) - 1) * f) := by
    have := mul_le_mul_of_nonneg_left hu (by linarith : (0 : ℝ) ≤ (i : ℝ) - 1); linarith
  have e2 : (Δ : ℝ) * (((i : ℝ) - 1) * f) ≤ (Δ : ℝ) * (a * W) :=
    mul_le_mul_of_nonneg_left (h4.trans h5) hd
  have e3 : (Δ : ℝ) * (a * W) ≤ ε * ((i : ℝ) - 1) * W := by
    have := mul_le_mul_of_nonneg_right hc hW; linarith
  have e4 : ((i : ℝ) - 1) * u ≤ ((i : ℝ) - 1) * (ε * W) := by linarith
  exact le_of_mul_le_mul_left e4 (by linarith)

/-- If `v` does not prefer `y` over `x`, then `w {v, y} ≤ w {v, x}`. -/
lemma RespectsPrefs.le_of_rank_le {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w) {v x y : V}
    (hx : x ∈ I.N v) (hy : y ∈ I.N v) (h : I.rank v x ≤ I.rank v y) : w s(v, y) ≤ w s(v, x) := by
  rcases h.lt_or_eq with h | h
  · exact hw.mono hx hy h
  · rw [I.rank_inj hx hy h]

/-- §6.2: for every matching `M*`, `w(M*) ≤ f_i(R) + 2 w_i(B)`. -/
lemma sum_opt_le {s : State V} (hs : I.Inv s) {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w)
    {q : V → Option V} (hq : I.IsMatching q) :
    ∑ e ∈ matchingEdges q, w e ≤ I.potR s w + 2 * I.blueW s w := by
  classical
  set Q : State V := { s with p := q }
  have hQ : I.IsMatching Q.p := hq
  have hsM : I.IsMatching s.p := hs.isMatching
  rw [show matchingEdges q = matchingEdges Q.p from rfl, matchingEdges_sum hQ w true]
  set T : V → ℝ := fun r => ∑ b ∈ I.blues, if q r = some b then nodeW s w b else 0
  have key : ∀ r ∈ I.reds, nodeW Q w r ≤ I.pot s w r + nodeW s w r + T r := by
    intro r hr
    have hr := I.mem_reds.1 hr
    have h0 := pot_nonneg hw s r
    have h1 := nodeW_nonneg hw s r
    have hT0 : 0 ≤ T r := sum_nonneg fun b _ => by split_ifs <;> simp [nodeW_nonneg hw]
    rcases hqr : q r with _ | b
    · have : nodeW Q w r = 0 := by simp [nodeW, Q, hqr]
      rw [this]; linarith
    have hbN := hq.mem_N r b hqr
    have hbb := blue_of_mem_red hbN hr
    have hT : T r = nodeW s w b := by
      simp only [T, hqr, Option.some.injEq]
      rw [sum_ite_eq]; simp [hbb]
    have hQr : nodeW Q w r = w s(r, b) := by simp [nodeW, Q, hqr]
    rw [hQr, hT]
    by_cases hbC : b ∈ s.C r
    · rcases hpr : s.p r with _ | b₂
      · obtain ⟨x, hx⟩ := I.best_isSome (v := r) ⟨b, hbC⟩
        have hpot : I.pot s w r = w s(r, x) := by rw [pot_of_unmatched hpr, hx]
        have := hw.le_of_rank_le (hs.C_sub r hr (I.best_mem hx)) hbN ((I.best_spec hx).2 b hbC)
        have := nodeW_nonneg hw s b
        linarith
      · have hbest := (hs.red_matched r b₂ hr hpr).2
        have hnode : nodeW s w r = w s(r, b₂) := by simp [nodeW, hpr]
        have := hw.le_of_rank_le (hs.C_sub r hr (I.best_mem hbest)) hbN
          ((I.best_spec hbest).2 b hbC)
        have := nodeW_nonneg hw s b
        linarith
    · obtain ⟨r₀, h₀, hlt⟩ := hs.lost r b hr hbN hbC
      have hnode : nodeW s w b = w s(b, r₀) := by simp [nodeW, h₀]
      have := hw.mono (hs.p_mem b r₀ h₀) (I.symm hbN) hlt
      rw [Sym2.eq_swap] at this
      linarith
  have hTsum : ∑ r ∈ I.reds, T r ≤ I.blueW s w := by
    simp only [T]
    rw [sum_comm, blueW]
    refine sum_le_sum fun b hb => ?_
    rw [← sum_filter]
    have hcard : (I.reds.filter fun r => q r = some b).card ≤ 1 := by
      refine card_le_one.2 fun r hr r' hr' => ?_
      have h1 := hq.symm r b (mem_filter.1 hr).2
      have h2 := hq.symm r' b (mem_filter.1 hr').2
      rw [h1] at h2; cases h2; rfl
    rw [sum_const, nsmul_eq_mul]
    have := nodeW_nonneg hw s b
    have : ((I.reds.filter fun r => q r = some b).card : ℝ) ≤ 1 := by exact_mod_cast hcard
    nlinarith
  have hred : ∑ r ∈ I.reds, nodeW s w r = I.blueW s w := by
    rw [← sum_matchingEdges_eq_blueW hsM, matchingEdges_sum hsM w true]; rfl
  calc ∑ r ∈ univ.filter (fun v => I.red v = true), nodeW Q w r
      ≤ ∑ r ∈ I.reds, (I.pot s w r + nodeW s w r + T r) := sum_le_sum key
    _ = I.potR s w + ∑ r ∈ I.reds, nodeW s w r + ∑ r ∈ I.reds, T r := by
      rw [sum_add_distrib, sum_add_distrib]; rfl
    _ ≤ I.potR s w + 2 * I.blueW s w := by rw [hred]; linarith

/-- **Theorem 2** (centralised core, §6.2). If the preferences respect the weights `w`, all degrees
are at most `Δ`, `ε > 0`, `i ≥ 2` and `i ≥ 1 + (Δ-1)/ε`, then `M_i` is a `(2+ε)`-approximation of
a maximum-weight matching: `w(M*) ≤ (2+ε) w(M_i)` for every matching `M*`. -/
theorem theorem_2_rounds {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w) {Δ : ℕ}
    (hΔ : ∀ v, (I.N v).card ≤ Δ) {ε : ℝ} (hε : 0 < ε) {i : ℕ} (hi2 : 2 ≤ i)
    (hi : 1 + ((Δ - 1 : ℕ) : ℝ) / ε ≤ i) {q : V → Option V} (hq : I.IsMatching q) :
    ∑ e ∈ matchingEdges q, w e ≤ (2 + ε) * ∑ e ∈ matchingEdges (I.run i).p, w e := by
  have hs := I.inv_run (i := i) (by omega)
  have h := sum_opt_le hs hw hq
  have h6 := lemma_6 hw hΔ hε hi2 hi
  rw [sum_matchingEdges_eq_blueW hs.isMatching]
  linarith

end Bicoloured

end Podc.TruncatedGaleShapley
