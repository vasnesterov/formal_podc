import Papers.PODC2019.HubLabelingHardness.Distances
import Papers.PODC2019.HubLabelingHardness.HLemma
import Podc.Foundations.Combinatorics.SimpleGraph.HubLabeling

/-!
# Theorem 2.1 and Theorem 1.1 of Kosowski–Uznański–Viennot (PODC 2019)

* `lemma_2_2_G`: Lemma 2.2 for `G_{b,ℓ}`: `d_G(v_{0,x}, v_{2ℓ,z}) = d_H(v_{0,x}, v_{2ℓ,z})`
  `= 2ℓA + Σ_k (z_k - x_k)²/2`, and every shortest `v_{0,x}`–`v_{2ℓ,z}` walk of `G` passes through
  `v_{ℓ,(x+z)/2}`.
* `theorem_2_1`: (i) vertex count, (ii) maximum degree `3`, (iii) every hub labeling of `G_{b,ℓ}` has
  average hub-set size `≥ 2^{bℓ} / 2^{10(b+ℓ)}`.
* `theorem_1_1`: graphs of maximum degree `3` on `n` vertices (for infinitely many `n`) where every hub
  labeling has average size `≥ n / 2^{29 √(log₂ n)}`.
-/

namespace Podc.HubLabelingHardness

open SimpleGraph Finset GV

variable {b ℓ : ℕ}

/-- **Lemma 2.2 of [KUV19], for `G_{b,ℓ}`.** If all `z_k - x_k` are even, the distance in `G_{b,ℓ}`
between `v_{0,x}` and `v_{2ℓ,z}` equals their weighted distance in `H_{b,ℓ}`, namely
`Lopt x z = 2ℓA + Σ_k (z_k - x_k)²/2`, and every shortest walk between them passes through
`v_{ℓ,(x+z)/2}`. (The paper also claims uniqueness of the shortest path in `G`; not formalized.) -/
theorem lemma_2_2_G (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) (x z : Vec b ℓ) (hxz : EvenDiff x z) :
    (G b ℓ).edist (main 0 x) (main (Fin.last _) z) = Lopt x z ∧
    (G b ℓ).edist (main 0 x) (main (Fin.last _) z) =
      (H b ℓ).wdist (fun e => (hwS b ℓ e : NNReal)) (bot x) (top z) ∧
    ∀ p : (G b ℓ).Walk (main 0 x) (main (Fin.last _) z),
      (p.length : ℕ∞) = (G b ℓ).edist (main 0 x) (main (Fin.last _) z) →
      main ⟨ℓ, by omega⟩ (midpt x z) ∈ p.support := by
  have hup : (G b ℓ).edist (main 0 x) (main (Fin.last _) z) ≤ Lopt x z := by
    obtain ⟨q, hq⟩ := exists_walk_wlen_eq_Lopt x z hxz
    have := edist_main_le_wlen hb hℓ q
    rw [hq] at this
    simpa [bot, top] using this
  have hreach : (G b ℓ).Reachable (main 0 x) (main (Fin.last _) z) :=
    reachable_of_edist_ne_top (ne_top_of_le_ne_top (by simp) hup)
  have heq : (G b ℓ).edist (main 0 x) (main (Fin.last _) z) = Lopt x z := by
    refine le_antisymm hup ?_
    obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_edist
    rw [← hp]
    exact_mod_cast (lopt_le_length_and hb hℓ hxz p).1
  refine ⟨heq, ?_, fun p hp => ?_⟩
  · rw [heq, wdist_eq_Lopt hℓ x z hxz]; rfl
  · rw [heq] at hp
    exact (lopt_le_length_and hb hℓ hxz p).2 (by exact_mod_cast hp.le)

/-! ## The triples `(x, (x+z)/2, z)` -/

lemma side_even (hb : 1 ≤ b) : 2 * (side b / 2) = side b := by
  have : side b = 2 * 2 ^ (b - 1) := by
    simp only [side]; rw [← pow_succ']; congr 1; omega
  omega

/-- First coordinate vector of a parameter `f k = (x_k, m_k)`. -/
def xf (f : Fin ℓ → Fin (side b) × Fin (side b / 2)) : Vec b ℓ := fun k => (f k).1

/-- Third coordinate vector: `z_k = 2 m_k + (x_k mod 2)` (so that `z_k ≡ x_k mod 2`). -/
def zf (f : Fin ℓ → Fin (side b) × Fin (side b / 2)) : Vec b ℓ := fun k =>
  ⟨(2 * (f k).2 + (f k).1 % 2) % side b, Nat.mod_lt _ (by have := one_le_side b; omega)⟩

lemma zf_val (hb : 1 ≤ b) (f : Fin ℓ → Fin (side b) × Fin (side b / 2)) (k : Fin ℓ) :
    (zf f k : ℕ) = 2 * (f k).2 + (f k).1 % 2 := by
  have := side_even hb; have := (f k).2.2
  simp only [zf]
  rw [Nat.mod_eq_of_lt (by omega)]

lemma evenDiff_xf_zf (hb : 1 ≤ b) (f : Fin ℓ → Fin (side b) × Fin (side b / 2)) :
    EvenDiff (xf f) (zf f) := by
  intro k
  rw [zf_val hb]
  refine ⟨((f k).2 : ℤ) - ((f k).1 : ℕ) / 2, ?_⟩
  simp only [xf]
  omega

/-- The triple `(v_{0,x}, v_{ℓ,(x+z)/2}, v_{2ℓ,z})` of a parameter. -/
def trip (hℓ : 1 ≤ ℓ) (f : Fin ℓ → Fin (side b) × Fin (side b / 2)) : GV b ℓ × GV b ℓ × GV b ℓ :=
  (main 0 (xf f), main ⟨ℓ, by omega⟩ (midpt (xf f) (zf f)), main (Fin.last _) (zf f))

lemma zf_injective (hb : 1 ≤ b) {f g : Fin ℓ → Fin (side b) × Fin (side b / 2)}
    (hx : xf f = xf g) (hz : zf f = zf g) : f = g := by
  funext k
  have h1 := congrFun hx k
  have h2 := congrArg Fin.val (congrFun hz k)
  rw [zf_val hb, zf_val hb] at h2
  simp only [xf] at h1
  rw [h1] at h2
  exact Prod.ext h1 (Fin.ext (by omega))

lemma zf_eq_of_midpt (hb : 1 ≤ b) {f g : Fin ℓ → Fin (side b) × Fin (side b / 2)}
    (hx : xf f = xf g) (hm : midpt (xf f) (zf f) = midpt (xf g) (zf g)) : zf f = zf g := by
  funext k
  have h1 := two_midpt_eq (evenDiff_xf_zf hb f) k
  have h2 := two_midpt_eq (evenDiff_xf_zf hb g) k
  rw [hm, hx] at h1
  exact Fin.ext (by omega)

lemma xf_eq_of_midpt (hb : 1 ≤ b) {f g : Fin ℓ → Fin (side b) × Fin (side b / 2)}
    (hz : zf f = zf g) (hm : midpt (xf f) (zf f) = midpt (xf g) (zf g)) : xf f = xf g := by
  funext k
  have h1 := two_midpt_eq (evenDiff_xf_zf hb f) k
  have h2 := two_midpt_eq (evenDiff_xf_zf hb g) k
  rw [hm, hz] at h1
  exact Fin.ext (by omega)

lemma Lopt_le (x z : Vec b ℓ) : Lopt x z ≤ 8 * ℓ ^ 2 * side b ^ 2 := by
  have h : ∑ k, sqd (x k) (midpt x z k) ≤ ℓ * side b ^ 2 := by
    calc ∑ k, sqd (x k) (midpt x z k) ≤ ∑ _k : Fin ℓ, side b ^ 2 :=
          Finset.sum_le_sum fun k _ => (sqd_lt _ _).le
      _ = ℓ * side b ^ 2 := by simp
  have h2 : ℓ * side b ^ 2 ≤ ℓ ^ 2 * side b ^ 2 :=
    Nat.mul_le_mul_right _ (Nat.le_self_pow two_ne_zero ℓ)
  unfold Lopt bigA
  nlinarith

/-- **Counting core of Theorem 2.1 (iii).** Every hub labeling of `G_{b,ℓ}` has total size
`Σ_v |S_v| ≥ (s · s/2)^ℓ / (2 (8ℓ²s² + 1))`: there are `s^ℓ (s/2)^ℓ` triples
`(v_{0,x}, v_{ℓ,(x+z)/2}, v_{2ℓ,z})` with `z ≡ x (mod 2)`, and for each of them the middle vertex
lies on a fixed shortest path from `v_{0,x}` or from `v_{2ℓ,z}` to one of its hubs. -/
theorem card_triples_le_sum (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) {S : GV b ℓ → Finset (GV b ℓ)}
    (hS : (G b ℓ).IsHubLabeling S) :
    (side b * (side b / 2)) ^ ℓ ≤ 2 * (8 * ℓ ^ 2 * side b ^ 2 + 1) * ∑ v, (S v).card := by
  have htrip_inj : Function.Injective (trip (b := b) hℓ) := by
    intro f g h
    simp only [trip, Prod.mk.injEq, main.injEq, true_and] at h
    exact zf_injective hb h.1 h.2.2
  let P : Finset (GV b ℓ × GV b ℓ × GV b ℓ) := univ.image (trip hℓ)
  have hcard : P.card = (side b * (side b / 2)) ^ ℓ := by
    rw [Finset.card_image_of_injective _ htrip_inj, Finset.card_univ, Fintype.card_fun,
      Fintype.card_prod]
    simp
  rw [← hcard]
  refine hS.card_le_mul_sum P _ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 ht
    have := (lemma_2_2_G hb hℓ _ _ (evenDiff_xf_zf hb f)).1
    exact reachable_of_edist_ne_top (by simp only [trip]; rw [this]; simp)
  · intro t ht
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 ht
    have := (lemma_2_2_G hb hℓ _ _ (evenDiff_xf_zf hb f)).1
    simp only [trip]; rw [this]; exact_mod_cast Lopt_le _ _
  · intro t ht
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 ht
    exact (lemma_2_2_G hb hℓ _ _ (evenDiff_xf_zf hb f)).2.2
  · rintro t ht t' ht' h
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 ht'
    simp only [trip, Prod.mk.injEq, main.injEq, true_and] at h
    rw [zf_injective hb h.1 (zf_eq_of_midpt hb h.1 h.2)]
  · rintro t ht t' ht' h
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 ht'
    simp only [trip, Prod.mk.injEq, main.injEq, true_and] at h
    rw [zf_injective hb (xf_eq_of_midpt hb h.1 h.2) h.1]

end Podc.HubLabelingHardness

namespace Podc.HubLabelingHardness

open SimpleGraph Finset GV

variable {b ℓ : ℕ}

lemma side_div_two (hb : 1 ≤ b) : side b / 2 = 2 ^ (b - 1) := by
  have := side_even hb
  have h : side b = 2 * 2 ^ (b - 1) := by
    simp only [side]; rw [← pow_succ']; congr 1; omega
  omega

/-- Theorem 2.1 (iii) in integer form: `2^{bℓ} · n ≤ 2^{10(b+ℓ)} · Σ_v |S_v|`. -/
theorem pow_mul_card_le_sum (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) {S : GV b ℓ → Finset (GV b ℓ)}
    (hS : (G b ℓ).IsHubLabeling S) :
    2 ^ (b * ℓ) * Fintype.card (GV b ℓ) ≤ 2 ^ (10 * (b + ℓ)) * ∑ v, (S v).card := by
  set T := ∑ v, (S v).card
  set n := Fintype.card (GV b ℓ)
  have hP := card_triples_le_sum hb hℓ hS
  rw [side_div_two hb, side, mul_pow, ← pow_mul, ← pow_mul] at hP
  have hn := card_le hb hℓ
  rw [side, ← pow_mul] at hn
  have hl : ℓ ^ 2 ≤ 2 ^ (2 * ℓ) := by
    rw [pow_mul']; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 2
  have h18 : 2 * (8 * ℓ ^ 2 * (2 ^ b) ^ 2 + 1) ≤ 18 * ℓ ^ 2 * 2 ^ (2 * b) := by
    have : 1 ≤ ℓ ^ 2 * (2 ^ b) ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
    rw [pow_mul']; nlinarith
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hP
  have hpos : 0 < 2 ^ (b' * ℓ) := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc 2 ^ (b' * ℓ) * (2 ^ ((b' + 1) * ℓ) * n)
      = (2 ^ ((b' + 1) * ℓ) * 2 ^ (b' * ℓ)) * n := by ring
    _ ≤ (18 * ℓ ^ 2 * 2 ^ (2 * (b' + 1)) * T) * (16 * ℓ ^ 2 * 2 ^ ((b' + 1) * (ℓ + 3))) := by
        exact Nat.mul_le_mul (hP.trans (Nat.mul_le_mul_right _ h18)) hn
    _ = 288 * (ℓ ^ 2 * ℓ ^ 2) * 2 ^ (2 * (b' + 1) + (b' + 1) * (ℓ + 3)) * T := by ring
    _ ≤ 2 ^ 9 * (2 ^ (2 * ℓ) * 2 ^ (2 * ℓ)) * 2 ^ (2 * (b' + 1) + (b' + 1) * (ℓ + 3)) * T :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) (Nat.mul_le_mul hl hl)) le_rfl)
          le_rfl
    _ = 2 ^ (9 + 4 * ℓ + 5 * b' + 5 + b' * ℓ + ℓ) * T := by
        rw [← pow_add, ← pow_add, ← pow_add]; congr 2; ring
    _ ≤ 2 ^ (b' * ℓ + 10 * (b' + 1 + ℓ)) * T :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
    _ = 2 ^ (b' * ℓ) * (2 ^ (10 * (b' + 1 + ℓ)) * T) := by rw [pow_add]; ring

/-- **Theorem 2.1 of [KUV19].** For all integers `b, ℓ ≥ 1` the graph `G_{b,ℓ}` satisfies
(i) `2ℓ · s^{ℓ+1} ≤ |V(G_{b,ℓ})| ≤ 16 ℓ² s^{ℓ+3}` with `s = 2^b`, i.e. `|V| = 2^{bℓ} · 2^{Θ(b + log ℓ)}`;
(ii) `Δ(G_{b,ℓ}) = 3`;
(iii) every hub labeling `{S_v}` of `G_{b,ℓ}` has average size
`(1/|V|) Σ_v |S_v| ≥ 2^{bℓ} / 2^{10(b+ℓ)} = 2^{bℓ} · 2^{-O(b+ℓ)}`. -/
theorem theorem_2_1 (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) [DecidableRel (G b ℓ).Adj] :
    (2 * ℓ * side b ^ (ℓ + 1) ≤ Fintype.card (GV b ℓ) ∧
      Fintype.card (GV b ℓ) ≤ 16 * ℓ ^ 2 * side b ^ (ℓ + 3)) ∧
    (G b ℓ).maxDegree = 3 ∧
    ∀ S : GV b ℓ → Finset (GV b ℓ), (G b ℓ).IsHubLabeling S →
      (2 : ℝ) ^ (b * ℓ) / 2 ^ (10 * (b + ℓ)) ≤
        (∑ v, (S v).card : ℝ) / Fintype.card (GV b ℓ) := by
  refine ⟨⟨card_ge hb hℓ, card_le hb hℓ⟩, maxDegree_eq hb hℓ, fun S hS => ?_⟩
  have h := pow_mul_card_le_sum hb hℓ hS
  have hn : (0 : ℝ) < Fintype.card (GV b ℓ) := by
    have := card_ge hb hℓ
    have : 0 < 2 * ℓ * side b ^ (ℓ + 1) := by positivity
    exact_mod_cast (by omega : 0 < Fintype.card (GV b ℓ))
  rw [div_le_div_iff₀ (by positivity) hn]
  have : ((2 ^ (b * ℓ) * Fintype.card (GV b ℓ) : ℕ) : ℝ) ≤
      ((2 ^ (10 * (b + ℓ)) * ∑ v, (S v).card : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at this
  linarith

lemma pow_le_card (m : ℕ) (hm : 1 ≤ m) : 2 ^ (m * m) ≤ Fintype.card (GV m m) := by
  have hge := card_ge hm hm
  rw [side, ← pow_mul] at hge
  calc 2 ^ (m * m) ≤ 2 ^ (m * (m + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    _ ≤ 2 * m * 2 ^ (m * (m + 1)) := Nat.le_mul_of_pos_left _ (by omega)
    _ ≤ _ := hge

/-- Theorem 1.1 in integer form for `b = ℓ = m`: `n² ≤ 2^{29m} Σ_v |S_v|`. -/
lemma sq_card_le (m : ℕ) (hm : 1 ≤ m) {S : GV m m → Finset (GV m m)}
    (hS : (G m m).IsHubLabeling S) :
    Fintype.card (GV m m) ^ 2 ≤ 2 ^ (29 * m) * ∑ v, (S v).card := by
  set n := Fintype.card (GV m m)
  have h := pow_mul_card_le_sum hm hm hS
  have hn := card_le hm hm
  rw [side, ← pow_mul] at hn
  have hl : m ^ 2 ≤ 2 ^ (2 * m) := by
    rw [pow_mul']; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 2
  have hn' : n ≤ 2 ^ (m * m + 9 * m) := by
    calc n ≤ 16 * m ^ 2 * 2 ^ (m * (m + 3)) := hn
      _ ≤ 2 ^ 4 * 2 ^ (2 * m) * 2 ^ (m * (m + 3)) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (by norm_num) hl)
      _ = 2 ^ (4 + 2 * m + m * (m + 3)) := by rw [pow_add, pow_add]
      _ ≤ 2 ^ (m * m + 9 * m) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc n ^ 2 = n * n := sq n
      _ ≤ 2 ^ (m * m + 9 * m) * n := Nat.mul_le_mul_right _ hn'
      _ = 2 ^ (9 * m) * (2 ^ (m * m) * n) := by rw [pow_add]; ring
      _ ≤ 2 ^ (9 * m) * (2 ^ (10 * (m + m)) * ∑ v, (S v).card) := Nat.mul_le_mul_left _ h
      _ = 2 ^ (29 * m) * ∑ v, (S v).card := by rw [← mul_assoc, ← pow_add]; ring_nf

/-- **Theorem 1.1 of [KUV19].** Graphs of maximum degree `3` require average hub-set size
`n / 2^{O(√log n)}`: there is a constant (`29`) such that for infinitely many `n` there is an
`n`-vertex graph of maximum degree `≤ 3` (namely `G_{m,m}`) on which every hub labeling has average size
`(1/n) Σ_v |S_v| ≥ n / 2^{29 √(log₂ n)}`. -/
theorem theorem_1_1 (N : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), N ≤ Fintype.card V ∧
      (∀ v, (G.neighborSet v).ncard ≤ 3) ∧
      ∀ S : V → Finset V, G.IsHubLabeling S →
        (Fintype.card V : ℝ) / (2 : ℝ) ^ (29 * √(Real.logb 2 (Fintype.card V))) ≤
          (∑ v, (S v).card : ℝ) / Fintype.card V := by
  set m := N + 1
  have hm : 1 ≤ m := by omega
  refine ⟨GV m m, inferInstance, G m m, ?_, ncard_neighborSet_le, fun S hS => ?_⟩
  · calc N ≤ m * m := by simp only [m]; nlinarith
      _ ≤ 2 ^ (m * m) := (Nat.lt_two_pow_self).le
      _ ≤ _ := pow_le_card m hm
  · set n := Fintype.card (GV m m)
    set T := ∑ v, (S v).card
    have h1 : ((n : ℝ)) ^ 2 ≤ (2 : ℝ) ^ (29 * m) * T := by exact_mod_cast sq_card_le m hm hS
    have h2 : ((2 : ℝ) ^ (m * m)) ≤ n := by exact_mod_cast pow_le_card m hm
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) h2
    have hlog : ((m : ℝ)) ^ 2 ≤ Real.logb 2 n := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) hnpos]
      have : (2 : ℝ) ^ ((m : ℝ) ^ 2) = (2 : ℝ) ^ (m * m) := by
        rw [show ((m : ℝ)) ^ 2 = ((m * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      rw [this]; exact h2
    have hsq : (m : ℝ) ≤ √(Real.logb 2 n) := by
      have := Real.sqrt_le_sqrt hlog
      rwa [Real.sqrt_sq (by positivity)] at this
    have h3 : (2 : ℝ) ^ (29 * m) ≤ (2 : ℝ) ^ (29 * √(Real.logb 2 n)) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
    rw [div_le_div_iff₀ (by positivity) hnpos]
    have hT : (0 : ℝ) ≤ T := by positivity
    calc (n : ℝ) * n = (n : ℝ) ^ 2 := (sq _).symm
      _ ≤ (2 : ℝ) ^ (29 * m) * T := h1
      _ ≤ (2 : ℝ) ^ (29 * √(Real.logb 2 n)) * T := by gcongr
      _ = T * (2 : ℝ) ^ (29 * √(Real.logb 2 n)) := mul_comm _ _
      _ = _ := by simp [T]

end Podc.HubLabelingHardness
