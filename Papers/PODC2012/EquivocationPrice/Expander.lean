import Papers.PODC2012.EquivocationPrice.Defs

/-!
# Lifted hypergraphs of expanders (Lemmas 8, 9, Claim 10 of Section 4)

Jaffe, Moscibroda, Sen, *On the Price of Equivocation in Byzantine Agreement*, PODC 2012,
Section 4.

The paper proves Theorem 7 by lifting an `(n, d, λ)`-expander `G` to the 3-uniform hypergraph
`L(G)` (Definition 6). Mathlib has no spectral expanders, so we take the conclusion of the
**expander mixing lemma** (EML) as a hypothesis, `MixingBound G d λ`:
`|e(S, T) - d|S||T|/n| ≤ λ √(|S||T|)` for all `S, T`, where `e(S, T)` counts ordered pairs.

* `lemma_8`: expander vertex-boundary lemma.
* `lemma_9`: if `λ < (d/n) F(a, b, c)` then `L(G)` has an `(A, B, C)`-trichromatic edge
  (the hypothesis `a ≤ b ≤ c` of the paper is not needed).
* `claim_10`: `F(a, b, c) ≥ k √(h(n - h))`, `k = (√2 - 1)/√6`, for sorted valid colourings.
* `hDisjoint_lift`: Lemma 9 + Claim 10: `λ < (dk/n) √(h(n - h))` makes `L(G)` `h`-disjoint.
* `uniform3_lift`, `card_lift_le`: `L(G)` is 3-uniform with at most `n·C(d, 2)` edges if `G` is
  `d`-regular.
* `T_le_of_expander`: the conditional form of Theorem 7.
* `mixingBound_top` and a closing `example`: the complete graph satisfies the mixing bound with
  `d = n - 1`, `λ = 1`, so the hypotheses of `hDisjoint_lift` are satisfiable (`n = 30`, `h = 2`).
-/

namespace Podc.EquivocationPrice

open Finset

variable {V : Type*} [Fintype V]

/-- `e(S, T)`: the number of ordered pairs `(u, v) ∈ S × T` with `u ~ v`. -/
def eCount (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) : ℕ :=
  ((S ×ˢ T).filter fun p => G.Adj p.1 p.2).card

/-- Conclusion of the expander mixing lemma for an `(n, d, λ)`-expander `G`:
`|e(S, T) - d|S||T|/n| ≤ λ √(|S||T|)` for all vertex sets `S, T`. -/
def MixingBound (G : SimpleGraph V) [DecidableRel G.Adj] (d lam : ℝ) : Prop :=
  ∀ S T : Finset V, |(eCount G S T : ℝ) - d * S.card * T.card / Fintype.card V| ≤
    lam * Real.sqrt (S.card * T.card)

/-- **Definition 6** (lifted hypergraph `L(G)`): the 3-sets of vertices at least two of whose
three pairs are edges of `G`, i.e. 3-sets with a vertex adjacent to the two others. -/
def lift [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  univ.filter fun e => e.card = 3 ∧ ∃ x ∈ e, ∀ y ∈ e, y ≠ x → G.Adj x y

/-- The function `F(a, b, c) = √(cb/a) (√(a + b) - √b)` of Lemma 9. -/
noncomputable def F (a b c : ℝ) : ℝ := Real.sqrt (c * b / a) * (Real.sqrt (a + b) - Real.sqrt b)

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A mixing bound with two nonempty sets forces `λ ≥ 0`. -/
lemma MixingBound.lam_nonneg {d lam : ℝ} (hG : MixingBound G d lam) {S T : Finset V}
    (hS : S.Nonempty) (hT : T.Nonempty) : 0 ≤ lam := by
  have h := (abs_nonneg _).trans (hG S T)
  have hpos : 0 < Real.sqrt (S.card * T.card) := Real.sqrt_pos.2 (by
    have := hS.card_pos; have := hT.card_pos; positivity)
  exact nonneg_of_mul_nonneg_left h hpos

lemma MixingBound.lower {d lam : ℝ} (hG : MixingBound G d lam) (S T : Finset V) :
    d * S.card * T.card / Fintype.card V - lam * Real.sqrt (S.card * T.card) ≤ eCount G S T := by
  have := (abs_le.1 (hG S T)).1; linarith

lemma MixingBound.upper {d lam : ℝ} (hG : MixingBound G d lam) (S T : Finset V) :
    (eCount G S T : ℝ) ≤
      d * S.card * T.card / Fintype.card V + lam * Real.sqrt (S.card * T.card) := by
  have := (abs_le.1 (hG S T)).2; linarith

/-- The vertices of `S` with a neighbour in `T`, `S ∩ N(T)`. -/
def nbhdIn (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) : Finset V :=
  S.filter fun v => ∃ t ∈ T, G.Adj v t

omit [Fintype V] in
lemma nbhdIn_subset (S T : Finset V) : nbhdIn G S T ⊆ S := filter_subset _ _

omit [Fintype V] in
lemma eCount_nbhdIn (S T : Finset V) : eCount G (nbhdIn G S T) T = eCount G S T := by
  unfold eCount nbhdIn
  congr 1
  ext ⟨u, v⟩
  simp only [mem_filter, mem_product]
  constructor
  · rintro ⟨⟨⟨hu, -⟩, hv⟩, ha⟩; exact ⟨⟨hu, hv⟩, ha⟩
  · rintro ⟨⟨hu, hv⟩, ha⟩; exact ⟨⟨⟨hu, v, hv, ha⟩, hv⟩, ha⟩

/-- **Lemma 8** of [JMS12] (expander vertex-boundary lemma), from the conclusion of the expander
mixing lemma: `|S ∩ N(T)| ≥ |S| - (2λn/d) √(|S|/|T|)`. -/
theorem lemma_8 {d lam : ℝ} (hG : MixingBound G d lam) (hd : 0 < d) (S T : Finset V)
    (hT : T.Nonempty) :
    (S.card : ℝ) - 2 * lam * Fintype.card V / d * Real.sqrt (S.card / T.card) ≤
      (S.filter fun v => ∃ t ∈ T, G.Adj v t).card := by
  change _ ≤ ((nbhdIn G S T).card : ℝ)
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  have hlam := hG.lam_nonneg hS hT
  set s : ℝ := ((S.card : ℕ) : ℝ)
  set t : ℝ := ((T.card : ℕ) : ℝ)
  set sT : ℝ := (((nbhdIn G S T).card : ℕ) : ℝ)
  set n : ℝ := ((Fintype.card V : ℕ) : ℝ)
  have ht : 0 < t := by simp only [t]; exact_mod_cast hT.card_pos
  have hn : 0 < n := by simp only [n]; exact_mod_cast hT.card_pos.trans_le (card_le_univ T)
  have hsT : sT ≤ s := by
    simp only [sT, s]; exact_mod_cast card_le_card (nbhdIn_subset (G := G) S T)
  have hsT0 : 0 ≤ sT := by positivity
  have h1 := hG.lower S T
  have h2 := hG.upper (nbhdIn G S T) T
  rw [eCount_nbhdIn] at h2
  have hsq : Real.sqrt (sT * t) ≤ Real.sqrt (s * t) := by gcongr
  have hst : Real.sqrt (s * t) = t * Real.sqrt (s / t) := by
    have : s * t = t ^ 2 * (s / t) := by field_simp
    rw [this, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  -- `d t (s - sT) / n ≤ 2 λ √(st)`
  have key : d * t * (s - sT) / n ≤ 2 * lam * (t * Real.sqrt (s / t)) := by
    rw [← hst]
    have : d * t * (s - sT) / n = d * s * t / n - d * sT * t / n := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hsq hlam]
  have key' : s - sT ≤ 2 * lam * n / d * Real.sqrt (s / t) := by
    rw [div_le_iff₀ hn] at key
    have : t * (d * (s - sT)) ≤ t * (2 * lam * n * Real.sqrt (s / t)) := by nlinarith
    have := le_of_mul_le_mul_left this ht
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]; linarith
  linarith

section Lemma9

variable [DecidableEq V]

lemma mem_lift_of_adj {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hzx : G.Adj z x)
    (hzy : G.Adj z y) : ({x, y, z} : Finset V) ∈ lift G := by
  simp only [lift, mem_filter, mem_univ, true_and]
  refine ⟨?_, z, by simp, ?_⟩
  · rw [card_insert_of_notMem (by simp [hxy, hxz]), card_pair hyz]
  · intro w hw hwz
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hzx
    · exact hzy
    · exact absurd rfl hwz

/-- **Lemma 9** of [JMS12]: for pairwise disjoint colour classes `A, B, C` of sizes `a, b > 0`
and `c`, if `λ < (d/n) F(a, b, c)` then `L(G)` contains a trichromatic hyperedge. (The paper
assumes `a ≤ b ≤ c`; the proof does not use it.) -/
theorem lemma_9 {d lam : ℝ} (hG : MixingBound G d lam) (hd : 0 < d) {A B C : Finset V}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (hA : A.Nonempty)
    (hB : B.Nonempty) (hlam : lam < d / Fintype.card V * F A.card B.card C.card) :
    Rainbow (lift G) A B C := by
  set a : ℝ := ((A.card : ℕ) : ℝ)
  set b : ℝ := ((B.card : ℕ) : ℝ)
  set c : ℝ := ((C.card : ℕ) : ℝ)
  set n : ℝ := ((Fintype.card V : ℕ) : ℝ)
  set CA := nbhdIn G C A
  set cA : ℝ := ((CA.card : ℕ) : ℝ)
  have ha : 0 < a := by simp only [a]; exact_mod_cast hA.card_pos
  have hb : 0 < b := by simp only [b]; exact_mod_cast hB.card_pos
  have hc : 0 ≤ c := by positivity
  have hn : 0 < n := by simp only [n]; exact_mod_cast hA.card_pos.trans_le (card_le_univ A)
  have hl0 : 0 ≤ lam := hG.lam_nonneg hA hB
  have h8 : c - 2 * lam * n / d * Real.sqrt (c / a) ≤ cA := lemma_8 hG hd C A hA
  set x := lam * n / d with hx
  have hx0 : 0 ≤ x := by positivity
  set p := Real.sqrt (c / a)
  set s := Real.sqrt b
  set t := Real.sqrt (a + b)
  have hp0 : 0 ≤ p := Real.sqrt_nonneg _
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hpa : p ^ 2 * a = c := by
    rw [Real.sq_sqrt (by positivity)]; field_simp
  have hsb : s ^ 2 = b := Real.sq_sqrt hb.le
  have hta : t ^ 2 = a + b := Real.sq_sqrt (by positivity)
  have hts : s ≤ t := Real.sqrt_le_sqrt (by linarith)
  have hF : F a b c = p * s * (t - s) := by
    simp only [F, p, s, t]
    rw [show c * b / a = c / a * b by ring, Real.sqrt_mul (by positivity)]
  have hxF : x < p * s * (t - s) := by
    rw [← hF, hx, div_lt_iff₀ hd]
    rw [div_mul_eq_mul_div, lt_div_iff₀ hn] at hlam
    linarith
  -- the quadratic inequality: `x² < (c - 2xp) b`
  have hquad : x ^ 2 < (c - 2 * x * p) * b := by
    rw [← hpa, ← hsb, show a = t ^ 2 - s ^ 2 by linarith]
    have hR : 0 < x + p * s * (t - s) + 2 * p * s ^ 2 := by
      have : 0 ≤ p * s * (t - s) := mul_nonneg (mul_nonneg hp0 hs0) (by linarith)
      have : 0 ≤ 2 * p * s ^ 2 := by positivity
      linarith
    nlinarith [mul_pos (sub_pos.2 hxF) hR]
  have h8' : c - 2 * x * p ≤ cA := by
    have : 2 * lam * n / d * p = 2 * x * p := by rw [hx]; ring
    linarith
  have hcA : x ^ 2 < cA * b := by nlinarith
  -- `w = √(cA b) > x`
  set w := Real.sqrt (cA * b)
  have hw : x < w := Real.lt_sqrt hx0 |>.2 hcA
  have hw2 : w ^ 2 = cA * b := Real.sq_sqrt (by positivity)
  have hlow := hG.lower CA B
  have hpos : (0 : ℝ) < eCount G CA B := by
    have h1 : lam = d / n * x := by rw [hx]; field_simp
    have h2 : d * cA * b / n - lam * w = d / n * w * (w - x) := by
      rw [h1, mul_assoc d cA b, ← hw2]; ring
    have : 0 < d / n * w * (w - x) :=
      mul_pos (mul_pos (div_pos hd hn) (hx0.trans_lt hw)) (sub_pos.2 hw)
    linarith
  have hne : ((CA ×ˢ B).filter fun q => G.Adj q.1 q.2).Nonempty := by
    rw [← card_pos]; exact_mod_cast hpos
  obtain ⟨⟨z, y⟩, hzy⟩ := hne
  simp only [mem_filter, mem_product, CA, nbhdIn] at hzy
  obtain ⟨⟨⟨hz, x', hx', hzx⟩, hy⟩, hadj⟩ := hzy
  refine ⟨x', hx', y, hy, z, hz, mem_lift_of_adj ?_ ?_ ?_ hzx hadj⟩
  · exact fun h => disjoint_left.1 hAB hx' (h ▸ hy)
  · exact fun h => disjoint_left.1 hAC hx' (h ▸ hz)
  · exact fun h => disjoint_left.1 hBC hy (h ▸ hz)

end Lemma9

/-- The constant `k = (√2 - 1)/√6` of Claim 10. -/
noncomputable def kConst : ℝ := (Real.sqrt 2 - 1) / Real.sqrt 6

lemma kConst_pos : 0 < kConst := by
  unfold kConst
  have : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  apply div_pos <;> linarith

/-- **Claim 10** of [JMS12]: for colour-class sizes `h ≤ a ≤ b ≤ c` with
`a + b + c ≥ (n + 3h)/2`, `F(a, b, c) ≥ k √(h(n - h))` with `k = (√2 - 1)/√6`. -/
theorem claim_10 {a b c h n : ℝ} (hh : 0 < h) (ha : h ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hs : n + 3 * h ≤ 2 * (a + b + c)) : kConst * Real.sqrt (h * (n - h)) ≤ F a b c := by
  have ha0 : 0 < a := hh.trans_le ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hc0 : 0 < c := hb0.trans_le hbc
  set r := Real.sqrt 2 with hr
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr1 : 1 ≤ r := by
    rw [hr, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  set s := Real.sqrt b
  set t := Real.sqrt (a + b)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsb : s ^ 2 = b := Real.sq_sqrt hb0.le
  have hta : t ^ 2 = a + b := Real.sq_sqrt (by positivity)
  have hts : s ≤ t := Real.sqrt_le_sqrt (by linarith)
  have htrs : t ≤ r * s := by
    rw [hr, ← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt (by linarith)
  -- `√b (√(a + b) - √b) ≥ (√2 - 1) a`
  have hkey : (r - 1) * a ≤ s * (t - s) := by
    have e1 : (r - 1) * t ≤ (2 - r) * s := by nlinarith
    have : a = (t - s) * (t + s) := by nlinarith
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left e1 (sub_nonneg.2 hts)]
  have hF : F a b c = Real.sqrt c / Real.sqrt a * (s * (t - s)) := by
    simp only [F, s, t]
    rw [Real.sqrt_div' _ ha0.le, Real.sqrt_mul hc0.le]; ring
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
  have hsa0 : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
  have h1 : (r - 1) * (Real.sqrt c * Real.sqrt a) ≤ F a b c := by
    rw [hF, div_mul_eq_mul_div, le_div_iff₀ hsa0]
    have := mul_le_mul_of_nonneg_left hkey (Real.sqrt_nonneg c)
    have e : (r - 1) * (Real.sqrt c * Real.sqrt a) * Real.sqrt a =
        Real.sqrt c * ((r - 1) * Real.sqrt a ^ 2) := by ring
    rw [e, hsa]; linarith
  have h2 : kConst * Real.sqrt (h * (n - h)) = (r - 1) * Real.sqrt (h * (n - h) / 6) := by
    rw [kConst, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 6)]; ring
  have h3 : Real.sqrt (h * (n - h) / 6) ≤ Real.sqrt c * Real.sqrt a := by
    rw [← Real.sqrt_mul hc0.le]
    apply Real.sqrt_le_sqrt
    nlinarith
  rw [h2]
  calc (r - 1) * Real.sqrt (h * (n - h) / 6) ≤ (r - 1) * (Real.sqrt c * Real.sqrt a) := by
        gcongr
    _ ≤ F a b c := h1

section Lift

variable [DecidableEq V]

/-- To check `h`-disjointness it suffices to check colourings with `|A| ≤ |B| ≤ |C|`. -/
lemma hDisjoint_of_sorted {E : Finset (Finset V)} {h : ℕ}
    (H : ∀ A B C : Finset V, ValidColoring h A B C → A.card ≤ B.card → B.card ≤ C.card →
      Rainbow E A B C) : HDisjoint E h := by
  intro A B C hv
  rcases le_total A.card B.card with hab | hab <;> rcases le_total B.card C.card with hbc | hbc <;>
    rcases le_total A.card C.card with hac | hac
  · exact H A B C hv hab hbc
  · exact H A B C hv hab hbc
  · exact rainbow_swap23 (H A C B (validColoring_swap23 hv) hac hbc)
  · exact rainbow_swap23 (rainbow_swap12
      (H C A B (validColoring_swap12 (validColoring_swap23 hv)) hac hab))
  · exact rainbow_swap12 (H B A C (validColoring_swap12 hv) hab hac)
  · exact rainbow_swap12 (rainbow_swap23
      (H B C A (validColoring_swap23 (validColoring_swap12 hv)) hbc hac))
  · exact H A B C hv (hac.trans hbc) (hab.trans hac)
  · exact rainbow_swap23 (rainbow_swap12 (rainbow_swap23
      (H C B A (validColoring_swap23 (validColoring_swap12 (validColoring_swap23 hv))) hbc hab)))

/-- **Lemma 9 + Claim 10** of [JMS12]: if `G` satisfies the expander mixing bound with
`λ < (dk/n) √(h(n - h))` then the lifted hypergraph `L(G)` is `h`-disjoint. -/
theorem hDisjoint_lift {d lam : ℝ} {h : ℕ} (hG : MixingBound G d lam) (hd : 0 < d) (h1 : 1 ≤ h)
    (hlam : lam < d * kConst / Fintype.card V * Real.sqrt (h * (Fintype.card V - h))) :
    HDisjoint (lift G) h := by
  apply hDisjoint_of_sorted
  intro A B C hv hab hbc
  obtain ⟨hAB, hAC, hBC, ha, hb, hc, hs⟩ := hv
  have hA : A.Nonempty := card_pos.1 (by omega)
  have hB : B.Nonempty := card_pos.1 (by omega)
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hA.card_pos.trans_le (card_le_univ A)
  refine lemma_9 hG hd hAB hAC hBC hA hB (hlam.trans_le ?_)
  have hcl := claim_10 (a := A.card) (b := B.card) (c := C.card) (h := h)
    (n := Fintype.card V) (by exact_mod_cast h1) (by exact_mod_cast ha) (by exact_mod_cast hab)
    (by exact_mod_cast hbc) (by exact_mod_cast hs)
  calc d * kConst / Fintype.card V * Real.sqrt (h * (Fintype.card V - h))
      = d / Fintype.card V * (kConst * Real.sqrt (h * (Fintype.card V - h))) := by ring
    _ ≤ d / Fintype.card V * F A.card B.card C.card := by gcongr

/-- `L(G)` is 3-uniform. -/
lemma uniform3_lift : Uniform3 (lift G) := fun _ he => (mem_filter.1 he).2.1

/-- `L(G)` has at most `n·C(d, 2)` hyperedges if `G` is `d`-regular (one hyperedge per vertex
and pair of its neighbours). -/
lemma card_lift_le {d : ℕ} (hreg : G.IsRegularOfDegree d) :
    (lift G).card ≤ Fintype.card V * d.choose 2 := by
  have hsub : lift G ⊆ univ.biUnion fun v =>
      ((G.neighborFinset v).powersetCard 2).image (insert v) := by
    intro e he
    obtain ⟨-, he3, x, hx, hadj⟩ := mem_filter.1 he
    rw [mem_biUnion]
    refine ⟨x, mem_univ _, mem_image.2 ⟨e.erase x, mem_powersetCard.2 ⟨?_, ?_⟩, insert_erase hx⟩⟩
    · intro y hy
      rw [SimpleGraph.mem_neighborFinset]
      exact hadj y (mem_of_mem_erase hy) (ne_of_mem_erase hy)
    · rw [card_erase_of_mem hx, he3]
  calc (lift G).card ≤ _ := card_le_card hsub
    _ ≤ ∑ v, (((G.neighborFinset v).powersetCard 2).image (insert v)).card := card_biUnion_le
    _ ≤ ∑ _v : V, d.choose 2 := by
        gcongr with v
        refine card_image_le.trans ?_
        rw [card_powersetCard, SimpleGraph.card_neighborFinset_eq_degree, hreg v]
    _ = Fintype.card V * d.choose 2 := by simp

/-- **Theorem 7** of [JMS12], conditional form (the paper's proof): a `d`-regular graph on the
vertex set `Fin n` satisfying the expander mixing bound with `λ < (dk/n) √(h(n - h))` yields an
`h`-disjoint 3-uniform hypergraph with at most `n·C(d, 2)` edges, so `Tₙ(h) ≤ n·C(d, 2)`. -/
theorem T_le_of_expander {n h d : ℕ} {lam : ℝ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree d) (hd : 0 < d) (hG : MixingBound G d lam) (h1 : 1 ≤ h)
    (hlam : lam < d * kConst / n * Real.sqrt (h * (n - h))) : T n h ≤ n * d.choose 2 := by
  have hD := hDisjoint_lift hG (by exact_mod_cast hd) h1 (by simpa using hlam)
  refine (Nat.sInf_le (show (lift G).card ∈ {m | ∃ E : Finset (Finset (Fin n)),
    Uniform3 E ∧ HDisjoint E h ∧ E.card = m} from ⟨lift G, uniform3_lift, hD, rfl⟩)).trans ?_
  simpa using card_lift_le hreg

end Lift

section NonVacuity

variable [DecidableEq V]

/-- The complete graph satisfies the mixing bound with `d = n - 1`, `λ = 1` (its nontrivial
eigenvalues are all `-1`). -/
lemma mixingBound_top :
    MixingBound (⊤ : SimpleGraph V) ((Fintype.card V : ℝ) - 1) 1 := by
  intro S T
  set s : ℝ := ((S.card : ℕ) : ℝ)
  set t : ℝ := ((T.card : ℕ) : ℝ)
  set n : ℝ := ((Fintype.card V : ℕ) : ℝ)
  set i : ℝ := (((S ∩ T).card : ℕ) : ℝ)
  -- `st - |S ∩ T| ≤ e(S, T) ≤ st`
  have hsplit := card_filter_add_card_filter_not (s := S ×ˢ T)
    (fun p : V × V => (⊤ : SimpleGraph V).Adj p.1 p.2)
  have hdiag : ((S ×ˢ T).filter fun p : V × V => ¬ (⊤ : SimpleGraph V).Adj p.1 p.2).card ≤
      (S ∩ T).card := by
    refine le_trans (card_le_card ?_) (card_image_le (f := fun x => (x, x)))
    intro p hp
    simp only [mem_filter, mem_product, SimpleGraph.top_adj, not_not] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    exact mem_image.2 ⟨p.1, mem_inter.2 ⟨h1, h3 ▸ h2⟩, by ext <;> simp [h3]⟩
  rw [card_product] at hsplit
  have he1 : (eCount ⊤ S T : ℝ) ≤ s * t := by
    have : eCount ⊤ S T ≤ S.card * T.card := by unfold eCount; omega
    simp only [s, t]; exact_mod_cast this
  have he2 : s * t - i ≤ (eCount ⊤ S T : ℝ) := by
    have : S.card * T.card ≤ eCount ⊤ S T + (S ∩ T).card := by unfold eCount; omega
    have : ((S.card * T.card : ℕ) : ℝ) ≤ ((eCount ⊤ S T + (S ∩ T).card : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at this; linarith
  have hs : s ≤ n := by simp only [s, n]; exact_mod_cast card_le_univ S
  have ht : t ≤ n := by simp only [t, n]; exact_mod_cast card_le_univ T
  have his : i ≤ s := by simp only [i, s]; exact_mod_cast card_le_card inter_subset_left
  have hit : i ≤ t := by simp only [i, t]; exact_mod_cast card_le_card inter_subset_right
  have hi0 : 0 ≤ i := by positivity
  have hs0 : 0 ≤ s := by positivity
  have ht0 : 0 ≤ t := by positivity
  rw [one_mul]
  rcases (show (0 : ℝ) ≤ n by positivity).eq_or_lt with hn | hn
  · have : s = 0 := le_antisymm (hn ▸ hs) hs0
    simp only [this, zero_mul, mul_zero] at he1 he2 ⊢
    rw [show (eCount ⊤ S T : ℝ) = 0 by linarith]; simp
  set w := Real.sqrt (s * t)
  have hw : w ^ 2 = s * t := Real.sq_sqrt (by positivity)
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hwn : w ≤ n := by
    rw [show n = Real.sqrt (n * n) by rw [Real.sqrt_mul_self hn.le]]
    exact Real.sqrt_le_sqrt (mul_le_mul hs ht ht0 hn.le)
  have hiw : i ≤ w := Real.le_sqrt_of_sq_le (by nlinarith)
  have hst : s * t / n ≤ w := by
    rw [div_le_iff₀ hn, ← hw]; nlinarith
  have hst0 : 0 ≤ s * t / n := by positivity
  have : (n - 1) * s * t / n = s * t - s * t / n := by field_simp
  rw [abs_le, this]
  constructor <;> linarith

/-- Non-vacuity of `hDisjoint_lift`: the lift of the complete graph on 30 vertices satisfies its
hypotheses for `h = 2` (`1 < (29k/30) √56`). -/
example : HDisjoint (lift (⊤ : SimpleGraph (Fin 30))) 2 := by
  refine hDisjoint_lift (mixingBound_top) (by norm_num) (by norm_num) ?_
  simp only [Fintype.card_fin, kConst]
  have h2 : (1.414 : ℝ) < Real.sqrt 2 := Real.lt_sqrt (by norm_num) |>.2 (by norm_num)
  have h6 : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have h56 : Real.sqrt ((2 : ℕ) * ((30 : ℕ) - (2 : ℕ)) : ℝ) = Real.sqrt 6 * Real.sqrt (28 / 3) := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h28 : (3.05 : ℝ) < Real.sqrt (28 / 3) := Real.lt_sqrt (by norm_num) |>.2 (by norm_num)
  rw [h56]
  push_cast
  field_simp
  nlinarith [mul_lt_mul'' h2 h28 (by norm_num) (by norm_num)]

end NonVacuity

end Podc.EquivocationPrice
