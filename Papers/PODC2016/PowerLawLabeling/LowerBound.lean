import Papers.PODC2016.PowerLawLabeling.Zeta
import Papers.PODC2016.PowerLawLabeling.Realization
import Papers.PODC2016.PowerLawLabeling.Counting
import Cslib.Foundations.Combinatorics.Labelling

/-!
# Theorem 3: the `Ω(n^{1/α})` lower bound for power-law graphs

For large `n`, every graph `H` on `i₁ = Θ(n^{1/α})` vertices is an induced subgraph of an
`α`-proper power-law graph on `n` vertices. The degree classes of the constructed graph are
(`cnt`): `⌊Cn⌋ - i₁ - p` leaves (`p ∈ {0,1}` fixes the parity of the degree sum),
`⌊Cn/d^α⌋` vertices of degree `d` for `2 ≤ d < i₁`, one vertex of each degree `i₁ ≤ d < 2 i₁`
(these host `H`), and isolated vertices for the rest (Definition 2 does not constrain `|V₀|`).
The graph itself comes from `realize`.
-/

namespace Podc.PowerLawLabeling

open Finset Filter

variable {α : ℝ}

/-- `x_d = C n / d^α`. -/
noncomputable def xr (α : ℝ) (n d : ℕ) : ℝ := C α * n / (d : ℝ) ^ α

/-- The class sizes of the constructed graph (for `d ≥ 1`). -/
noncomputable def cnt (α : ℝ) (n p d : ℕ) : ℕ :=
  if d = 1 then ⌊C α * n⌋₊ - i₁ α n - p
  else if d < i₁ α n then ⌊xr α n d⌋₊
  else if d < 2 * i₁ α n then 1 else 0

theorem xr_nonneg (hα : 1 < α) (n d : ℕ) : 0 ≤ xr α n d := C_mul_div_nonneg hα n d

theorem xr_pos (hα : 1 < α) {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) : 0 < xr α n d := by
  unfold xr
  have := C_pos hα
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

theorem xr_anti (hα : 1 < α) (n : ℕ) {d d' : ℕ} (hd : 1 ≤ d) (h : d ≤ d') :
    xr α n d' ≤ xr α n d := by
  unfold xr
  have hC := C_pos hα
  have h0 : (0 : ℝ) < d := by exact_mod_cast hd
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact Real.rpow_le_rpow h0.le (by exact_mod_cast h) (by linarith)

theorem xr_two_mul_i₁_lt_one (hα : 2 < α) (n : ℕ) : xr α n (2 * i₁ α n) < 1 := by
  have hα1 : 1 < α := by linarith
  have hi := one_le_i₁ hα1 n
  have h2 := C_mul_div_i₁_lt_two hα1 n
  have hi0 : (0 : ℝ) < i₁ α n := by exact_mod_cast hi
  unfold xr
  push_cast
  rw [Real.mul_rpow (by norm_num) hi0.le, ← div_div]
  have h4 : (4 : ℝ) ≤ 2 ^ α := by
    have := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) hα.le
    norm_num at this; linarith
  rw [div_lt_one (by positivity)]
  rw [div_lt_iff₀ (by positivity)] at h2 ⊢
  nlinarith [Real.rpow_pos_of_pos hi0 α]

/-- The class sizes `cnt` satisfy Definition 2. -/
theorem isProperPowerLaw_of_numDeg (hα : 2 < α) {n p : ℕ} (hi3 : 3 ≤ i₁ α n)
    (hfl : i₁ α n + 1 ≤ ⌊C α * n⌋₊) (hp : p ≤ 1) (G : SimpleGraph (Fin n))
    (hG : ∀ d, 1 ≤ d → numDeg G d = cnt α n p d) : IsProperPowerLaw α G := by
  have hα1 : 1 < α := by linarith
  have hn : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    subst this; simp at hfl
  set i := i₁ α n with hi
  constructor <;> simp only [Fintype.card_fin]
  · rw [hG 1 le_rfl]; simp only [cnt, ite_true]; push_cast; omega
  · rw [hG 1 le_rfl]; simp only [cnt, ite_true]
    exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (Nat.floor_le_ceil _))
  · rw [hG 2 (by norm_num)]
    simp only [cnt, show (2 : ℕ) ≠ 1 by norm_num, ite_false]
    rw [if_pos (show 2 < i₁ α n by omega), xr]; push_cast; rfl
  · rw [hG 2 (by norm_num)]
    simp only [cnt, show (2 : ℕ) ≠ 1 by norm_num, ite_false]
    rw [if_pos (show 2 < i₁ α n by omega), xr]; push_cast; exact (Nat.floor_le_ceil _).trans (Nat.le_succ _)
  · intro d hd3 _
    rw [hG d (by omega)]
    simp only [cnt, show d ≠ 1 by omega, ite_false]
    split_ifs with h1 h2
    · left; rfl
    · have hlt : xr α n d < 2 := lt_of_le_of_lt (xr_anti hα1 n (by omega) (not_lt.1 h1))
        (C_mul_div_i₁_lt_two hα1 n)
      have hpos := xr_pos hα1 hn (show 1 ≤ d by omega)
      unfold xr at hlt hpos
      by_cases h1x : 1 ≤ C α * n / (d : ℝ) ^ α
      · left; symm; rw [Nat.floor_eq_iff (by positivity)]; push_cast; constructor <;> linarith
      · right; symm; rw [Nat.ceil_eq_iff (by norm_num)]; push_cast; constructor <;> linarith
    · left; symm; rw [Nat.floor_eq_zero]
      exact lt_of_le_of_lt (xr_anti hα1 n (by omega) (by omega)) (xr_two_mul_i₁_lt_one hα n)
  · intro d hd2 _
    rw [hG d (by omega), hG (d + 1) (by omega)]
    simp only [cnt, show d ≠ 1 by omega, show d + 1 ≠ 1 by omega, ite_false]
    by_cases hd1 : d + 1 < i
    · rw [if_pos hd1, if_pos (by omega : d < i)]
      exact Nat.floor_le_floor (xr_anti hα1 n (by omega) (by omega))
    by_cases hdi : d + 1 = i
    · rw [if_neg hd1, if_pos (by omega : d < i), if_pos (by omega : d + 1 < 2 * i)]
      have := two_le_floor_of_lt_i₁ hα1 n (i := d) (by omega) (by omega)
      unfold xr; push_cast; omega
    · rw [if_neg hd1, if_neg (by omega : ¬ d < i)]
      split_ifs <;> omega


/-! ### Graph-theoretic helpers -/

section Helpers

variable {V W : Type*}

theorem neighborSet_map_apply (f : V ↪ W) (G : SimpleGraph V) (v : V) :
    (G.map f).neighborSet (f v) = f '' G.neighborSet v := by
  ext x
  simp only [SimpleGraph.mem_neighborSet, SimpleGraph.map_adj, Set.mem_image]
  constructor
  · rintro ⟨u', v', h, hu, rfl⟩
    exact ⟨v', f.injective hu ▸ h, rfl⟩
  · rintro ⟨y, h, rfl⟩
    exact ⟨v, y, h, rfl, rfl⟩

theorem deg_map_apply (f : V ↪ W) (G : SimpleGraph V) (v : V) :
    deg (G.map f) (f v) = deg G v := by
  unfold deg; rw [neighborSet_map_apply, Set.ncard_image_of_injective _ f.injective]

theorem deg_map_of_notMem (f : V ↪ W) (G : SimpleGraph V) {w : W} (hw : ∀ v, f v ≠ w) :
    deg (G.map f) w = 0 := by
  unfold deg
  have : (G.map f).neighborSet w = ∅ := by
    ext x
    simp only [SimpleGraph.mem_neighborSet, SimpleGraph.map_adj, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨u', v', _, hu, _⟩
    exact hw u' hu
  rw [this, Set.ncard_empty]

theorem numDeg_map_equiv [Fintype V] [Fintype W] (e : V ≃ W) (G : SimpleGraph V) (d : ℕ) :
    numDeg (G.map e.toEmbedding) d = numDeg G d := by
  unfold numDeg
  symm
  refine card_equiv e fun v => ?_
  simp only [mem_filter, mem_univ, true_and]
  rw [show e v = e.toEmbedding v from rfl, deg_map_apply]

theorem deg_lt_card [Fintype V] (G : SimpleGraph V) (v : V) : deg G v < Fintype.card V := by
  unfold deg
  rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
  exact Set.ncard_lt_ncard (Set.ssubset_univ_iff.2 fun h => (G.irrefl (v := v))
    (by have : v ∈ G.neighborSet v := h ▸ Set.mem_univ v; exact this)) (Set.toFinite _)

theorem sum_range_eq_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (hf : f 0 = 0) (i : ℕ) :
    ∑ d ∈ range i, f d = ∑ d ∈ Icc 1 (i - 1), f d := by
  symm
  refine sum_subset (fun d hd => by simp at hd ⊢; omega) fun d hd hd' => ?_
  simp at hd hd'
  rw [show d = 0 by omega, hf]

end Helpers

/-! ### Counting the classes -/

theorem i₁_le_floor_le (hα : 1 < α) {n : ℕ} : ⌊C α * n⌋₊ ≤ n := by
  apply Nat.floor_le_of_le
  have := C_le_one hα
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith

/-- The non-hub vertices fit: `∑_{d=1}^{i₁-1} cnt d ≤ n - i₁`. -/
theorem sum_cnt_le (hα : 1 < α) {n p : ℕ} (hi2 : 2 ≤ i₁ α n)
    (hfl : i₁ α n + 1 ≤ ⌊C α * n⌋₊) :
    ∑ d ∈ Icc 1 (i₁ α n - 1), cnt α n p d ≤ n - i₁ α n := by
  have hC := C_pos hα
  have hin : i₁ α n ≤ n := by have := i₁_le_floor_le hα (n := n); omega
  have key : ∀ d ∈ Icc 1 (i₁ α n - 1), (cnt α n p d : ℝ) ≤
      C α * n * (d : ℝ) ^ (-α) - (if d = 1 then (i₁ α n : ℝ) else 0) := by
    intro d hd
    rw [mem_Icc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    by_cases h1 : d = 1
    · subst h1
      simp only [cnt, ite_true, Nat.cast_one, Real.one_rpow, mul_one]
      have hle : ⌊C α * n⌋₊ - i₁ α n - p ≤ ⌊C α * n⌋₊ - i₁ α n := Nat.sub_le _ _
      have h1 : ((⌊C α * n⌋₊ - i₁ α n - p : ℕ) : ℝ) ≤ ((⌊C α * n⌋₊ - i₁ α n : ℕ) : ℝ) :=
        Nat.cast_le.2 hle
      have e : ((⌊C α * n⌋₊ - i₁ α n : ℕ) : ℝ) = ⌊C α * n⌋₊ - i₁ α n := Nat.cast_sub (by omega)
      have := Nat.floor_le (show 0 ≤ C α * n by positivity)
      linarith
    · have hdi : d < i₁ α n := by omega
      simp only [cnt, h1, ite_false, hdi, ite_true, sub_zero]
      rw [Real.rpow_neg hd0.le, ← div_eq_mul_inv]
      exact Nat.floor_le (xr_nonneg hα n d)
  have hsum := sum_le_sum key
  rw [sum_sub_distrib, ← mul_sum, sum_ite_eq' (Icc 1 (i₁ α n - 1)) 1,
    if_pos (by simp; omega)] at hsum
  have h1 := C_mul_sum_Icc_le_one hα (i₁ α n - 1)
  have h2 : C α * n * ∑ d ∈ Icc 1 (i₁ α n - 1), (d : ℝ) ^ (-α) ≤ n := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have h3 : ((∑ d ∈ Icc 1 (i₁ α n - 1), cnt α n p d : ℕ) : ℝ) ≤ ((n - i₁ α n : ℕ) : ℝ) := by
    push_cast; rw [Nat.cast_sub hin]; linarith
  exact_mod_cast h3

theorem sum_mul_cnt_add {n p : ℕ} (hi2 : 2 ≤ i₁ α n) (hfl : i₁ α n + 1 ≤ ⌊C α * n⌋₊)
    (hp : p ≤ 1) :
    ∑ d ∈ Icc 1 (i₁ α n - 1), d * cnt α n p d + p =
      ∑ d ∈ Icc 1 (i₁ α n - 1), d * cnt α n 0 d := by
  have h1 : (1 : ℕ) ∈ Icc 1 (i₁ α n - 1) := by simp; omega
  rw [← add_sum_erase _ _ h1, ← add_sum_erase _ _ h1]
  have : ∑ d ∈ (Icc 1 (i₁ α n - 1)).erase 1, d * cnt α n p d =
      ∑ d ∈ (Icc 1 (i₁ α n - 1)).erase 1, d * cnt α n 0 d := by
    refine sum_congr rfl fun d hd => ?_
    simp only [mem_erase] at hd
    simp [cnt, hd.1]
  rw [this]
  simp only [cnt, ite_true, one_mul, Nat.sub_zero]
  omega

/-! ### The construction -/

theorem card_filter_hub (i d : ℕ) {P : Fin i → Prop} [DecidablePred P]
    (hP : ∀ j, P j ↔ i + (j : ℕ) = d) :
    #{j : Fin i | P j} = if i ≤ d ∧ d < 2 * i then 1 else 0 := by
  split_ifs with h
  · rw [card_eq_one]
    refine ⟨⟨d - i, by omega⟩, ?_⟩
    ext j; simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff, hP]; omega
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro j _; rw [hP]; have := j.isLt; omega

/-- **The construction of Theorem 3.** If `n` is large enough (the three numeric hypotheses),
every graph on `i₁` vertices is an induced subgraph of an `α`-proper power-law graph on `n`
vertices. -/
theorem construct (hα : 2 < α) {n : ℕ} (hi3 : 3 ≤ i₁ α n)
    (hL : 2 * i₁ α n + i₁ α n * i₁ α n + 1 ≤ ⌊C α * n⌋₊)
    (hB : 2 * i₁ α n + i₁ α n * (2 * i₁ α n) ≤ ⌊xr α n 2⌋₊)
    (H : SimpleGraph (Fin (i₁ α n))) :
    ∃ G : SimpleGraph (Fin n), IsProperPowerLaw α G ∧ Nonempty (H ↪g G) := by
  classical
  have hα1 : 1 < α := by linarith
  have hfl : i₁ α n + 1 ≤ ⌊C α * n⌋₊ := by nlinarith
  have hin : i₁ α n ≤ n := by have := i₁_le_floor_le hα1 (n := n); omega
  generalize hidef : i₁ α n = i at *
  -- the parity correction
  set S0 := ∑ j : Fin i, (i + (j : ℕ)) + ∑ d ∈ Icc 1 (i - 1), d * cnt α n 0 d with hS0
  set p := S0 % 2 with hp_def
  have hp : p ≤ 1 := by omega
  -- labelling of the non-hub vertices by their target degree
  let lo : ℕ → ℕ := fun d => if d = 0 then 0 else cnt α n p d
  let hi : ℕ → ℕ := fun d => if d = 0 then n - i else cnt α n p d
  have hsum_lo : ∑ d ∈ range i, lo d = ∑ d ∈ Icc 1 (i - 1), cnt α n p d := by
    rw [sum_range_eq_sum_Icc lo (by simp [lo])]
    refine sum_congr rfl fun d hd => ?_
    simp only [mem_Icc] at hd; simp [lo, show d ≠ 0 by omega]
  obtain ⟨g, hg, hgc⟩ := Fintype.exists_labelling (α := Fin (n - i)) i lo hi
    (fun d _ => by by_cases h : d = 0 <;> simp [lo, hi, h])
    (by rw [hsum_lo, Fintype.card_fin]; subst hidef; exact sum_cnt_le hα1 (by omega) hfl)
    (by
      rw [Fintype.card_fin]
      calc n - i = hi 0 := by simp [hi]
        _ ≤ ∑ d ∈ range i, hi d :=
          single_le_sum (fun _ _ => Nat.zero_le _) (by simp; omega))
  have hgd : ∀ d, 1 ≤ d → d < i → #{w | g w = d} = cnt α n p d := by
    intro d hd1 hdi
    have := hgc d hdi
    simp only [lo, hi, show d ≠ 0 by omega, ite_false] at this
    omega
  have hg0 : ∀ d, i ≤ d → #{w | g w = d} = 0 := by
    intro d hd; rw [card_eq_zero, filter_eq_empty_iff]; intro w _; have := hg w; omega
  -- the vertex set `Fin i ⊕ Fin (n - i)` and the targets
  let t : Fin i ⊕ Fin (n - i) → ℕ := Sum.elim (fun j => i + (j : ℕ)) g
  let H₀ : SimpleGraph (Fin i ⊕ Fin (n - i)) := H.map Function.Embedding.inl
  let A : Finset (Fin i ⊕ Fin (n - i)) := univ.map Function.Embedding.inl
  let R : Finset (Fin i ⊕ Fin (n - i)) := univ.map Function.Embedding.inr
  let B := R.filter (fun v => 2 ≤ t v)
  let L := R.filter (fun v => t v = 1)
  have hcntt : ∀ d, 1 ≤ d → #{v | t v = d} = cnt α n p d := by
    intro d hd
    rw [card_filter, Fintype.sum_sum_type, ← card_filter, ← card_filter]
    have e1 : #{j : Fin i | t (Sum.inl j) = d} = if i ≤ d ∧ d < 2 * i then 1 else 0 := by
      exact card_filter_hub i d fun j => by simp [t]
    have e2 : #{w : Fin (n - i) | t (Sum.inr w) = d} = #{w | g w = d} := by
      congr 1
    rw [e1, e2]
    by_cases hdi : d < i
    · rw [hgd d hd hdi, if_neg (by omega)]; simp
    · rw [hg0 d (by omega)]
      simp only [cnt, show d ≠ 1 by omega, ite_false, hdi]
      split_ifs <;> omega
  have hL' : L = (univ.filter (fun w => g w = 1)).map Function.Embedding.inr := by
    ext v; cases v <;> simp [L, R, t]
  have hB' : (univ.filter (fun w => g w = 2)).map Function.Embedding.inr ⊆ B := by
    intro v hv
    simp only [Finset.mem_map, mem_filter, mem_univ, true_and, Function.Embedding.inr_apply] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    simp [B, R, t, hw]
  have hcardA : #A = i := by simp [A]
  have hcardL : #L = cnt α n p 1 := by rw [hL', card_map, hgd 1 le_rfl (by omega)]
  have hcardB : ⌊xr α n 2⌋₊ ≤ #B := by
    have := card_le_card hB'
    rw [card_map, hgd 2 (by norm_num) (by omega)] at this
    simpa [cnt, hidef, show (2 : ℕ) < i by omega] using this
  have hcnt1 : cnt α n p 1 = ⌊C α * n⌋₊ - i - p := by simp [cnt, hidef]
  -- the degree sum is even
  have hsumg : ∑ w, g w = ∑ d ∈ Icc 1 (i - 1), d * cnt α n p d := by
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := range i) (g := g)
      (fun w _ => mem_range.2 (hg w)) g]
    rw [sum_range_eq_sum_Icc _ (by simp) i]
    refine sum_congr rfl fun d hd => ?_
    simp only [mem_Icc] at hd
    rw [sum_congr rfl fun w hw => (mem_filter.1 hw).2, sum_const, smul_eq_mul,
      hgd d (by omega) (by omega), mul_comm]
  have heven : Even (∑ v, t v) := by
    have h1 := sum_mul_cnt_add (α := α) (n := n) (p := p) (by omega) (by omega) hp
    rw [hidef] at h1
    have h2 : ∑ v, t v = ∑ j : Fin i, (i + (j : ℕ)) + ∑ w, g w := by
      rw [Fintype.sum_sum_type]; rfl
    rw [Nat.even_iff, h2, hsumg]
    omega
  obtain ⟨G, -, hind, hdeg⟩ := realize t H₀ A B L i (2 * i)
    (by
      rw [disjoint_left]; intro v hvA hvB
      simp only [A, Finset.mem_map, mem_univ, true_and, Function.Embedding.inl_apply] at hvA
      obtain ⟨a, rfl⟩ := hvA
      simp [B, R] at hvB)
    (by
      rw [disjoint_left]; intro v hvA hvL
      simp only [A, Finset.mem_map, mem_univ, true_and, Function.Embedding.inl_apply] at hvA
      obtain ⟨a, rfl⟩ := hvA
      simp [L, R] at hvL)
    (by
      rw [disjoint_left]; intro v hvB hvL
      simp only [B, L, mem_filter] at hvB hvL; omega)
    (by
      intro u v h
      simp only [H₀, SimpleGraph.map_adj] at h
      obtain ⟨a, b, -, rfl, rfl⟩ := h
      simp [A])
    (by
      intro v
      cases v with
      | inl a =>
        rw [show (Sum.inl a : Fin i ⊕ Fin (n - i)) = Function.Embedding.inl a from rfl,
          deg_map_apply]
        have := deg_lt_card H a
        simp only [Fintype.card_fin] at this
        simp [t]; omega
      | inr w =>
        rw [deg_map_of_notMem _ _ (fun a h => by cases h)]; exact Nat.zero_le _)
    (by
      intro v hvA hvB hvL
      cases v with
      | inl a => exact absurd (by simp [A]) hvA
      | inr w =>
        simp only [B, L, R, mem_filter, Finset.mem_map, mem_univ, true_and,
          Function.Embedding.inr_apply, exists_apply_eq_apply] at hvB hvL
        simp only [t, Sum.elim_inr] at hvB hvL ⊢
        omega)
    (by
      intro b hb
      simp only [B, R, mem_filter, Finset.mem_map, mem_univ, true_and] at hb
      obtain ⟨⟨w, rfl⟩, h2⟩ := hb
      simp only [t, Function.Embedding.inr_apply, Sum.elim_inr] at h2 ⊢
      exact ⟨by omega, (hg w).le⟩)
    (by intro l hl; simp only [L, mem_filter] at hl; exact hl.2)
    (by
      intro a ha
      simp only [A, Finset.mem_map, mem_univ, true_and] at ha
      obtain ⟨j, rfl⟩ := ha
      simp only [t, Function.Embedding.inl_apply, Sum.elim_inl]
      have := j.isLt; omega)
    (by rw [hcardA]; omega)
    (by
      rw [hcardL, hcnt1]
      exact Nat.le_sub_of_add_le (Nat.le_sub_of_add_le (by omega)))
    heven
  -- transfer to `Fin n`
  have hcardV : Fintype.card (Fin i ⊕ Fin (n - i)) = n := by simp; omega
  let e := Fintype.equivFinOfCardEq hcardV
  refine ⟨G.map e.toEmbedding, ?_, ⟨?_⟩⟩
  · subst hidef
    refine isProperPowerLaw_of_numDeg hα hi3 hfl hp _ fun d hd => ?_
    rw [numDeg_map_equiv, numDeg, ← hcntt d hd]
    congr 1; ext v; simp [hdeg v]
  · refine ⟨⟨fun a => e (Sum.inl a), fun a b h => by simpa using e.injective h⟩, ?_⟩
    intro a b
    show (G.map e.toEmbedding).Adj (e (Sum.inl a)) (e (Sum.inl b)) ↔ H.Adj a b
    rw [show e (Sum.inl a) = e.toEmbedding (Sum.inl a) from rfl,
      show e (Sum.inl b) = e.toEmbedding (Sum.inl b) from rfl, SimpleGraph.map_adj_apply,
      hind _ _ (by simp [A]) (by simp [A])]
    exact SimpleGraph.map_adj_apply (f := Function.Embedding.inl)

/-! ### Asymptotics -/

/-- For large `n`, the three numeric hypotheses of `construct` hold, and moreover
`(Cn/2)^{1/α} ≥ 4`. -/
theorem eventually_construct (hα : 2 < α) : ∀ᶠ n : ℕ in atTop,
    3 ≤ i₁ α n ∧ 2 * i₁ α n + i₁ α n * i₁ α n + 1 ≤ ⌊C α * n⌋₊ ∧
      2 * i₁ α n + i₁ α n * (2 * i₁ α n) ≤ ⌊xr α n 2⌋₊ ∧ 4 ≤ (C α * n / 2) ^ (1 / α) := by
  have hα1 : 1 < α := by linarith
  have hα0 : 0 < α := by linarith
  have hC := C_pos hα1
  have h2α : (0 : ℝ) < 2 ^ α := by positivity
  set K := C α / 2 ^ α with hK
  have hK0 : 0 < K := by positivity
  -- `n^{2/α - 1} → 0`
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 - 2 / α))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by rw [sub_pos, div_lt_one hα0]; linarith)).comp
      tendsto_natCast_atTop_atTop
  have hev1 := (tendsto_order.1 hlim).2 (K / 13) (by positivity)
  -- `(Cn/2)^{1/α} → ∞`
  have hlim2 : Tendsto (fun n : ℕ => (C α * n / 2) ^ (1 / α)) atTop atTop := by
    refine (tendsto_rpow_atTop (by positivity)).comp ?_
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (show 0 < C α / 2 by positivity)
    refine this.congr fun n => ?_
    ring
  have hev2 := hlim2.eventually_ge_atTop 4
  have hev3 := eventually_ge_atTop (1 : ℕ)
  filter_upwards [hev1, hev2, hev3] with n h1 h2 h3
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast h3
  set y := (n : ℝ) ^ (1 / α) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hn (by positivity)
  have hy2 : y ^ 2 = (n : ℝ) ^ (2 / α) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
  have hy2n : 13 * y ^ 2 ≤ K * n := by
    rw [hy2]
    have e : (n : ℝ) ^ (2 / α) = (n : ℝ) ^ (-(1 - 2 / α)) * n := by
      have : (2 / α) = -(1 - 2 / α) + 1 := by ring
      conv_lhs => rw [this]
      rw [Real.rpow_add (by positivity), Real.rpow_one]
    rw [e]
    have : (n : ℝ) ^ (-(1 - 2 / α)) * n ≤ K / 13 * n :=
      mul_le_mul_of_nonneg_right h1.le (by positivity)
    linarith
  have hi := i₁_le_rpow_add_one hα1 n
  rw [← hy] at hi
  have hlt := lt_i₁ hα1 n
  have hi3 : 3 ≤ i₁ α n := by
    have : (3 : ℝ) < i₁ α n := by linarith
    exact_mod_cast this.le
  have hiy : (i₁ α n : ℝ) ≤ 2 * y := by linarith
  have hKC : K * n ≤ C α * n := by
    rw [hK, div_mul_eq_mul_div, div_le_iff₀ h2α]
    have : (1 : ℝ) ≤ 2 ^ α := Real.one_le_rpow (by norm_num) hα0.le
    have : 0 ≤ C α * n := by positivity
    nlinarith
  refine ⟨hi3, Nat.le_floor ?_, Nat.le_floor ?_, h2⟩
  · push_cast
    have hi0 : (0 : ℝ) ≤ i₁ α n := Nat.cast_nonneg _
    nlinarith
  · push_cast
    have hi0 : (0 : ℝ) ≤ i₁ α n := Nat.cast_nonneg _
    have : xr α n 2 = K * n := by
      rw [xr, hK]; push_cast; ring
    rw [this]
    nlinarith

/-- **Theorem 3** (for the family `P'_α` of `α`-proper power-law graphs, `α > 2`): there is
`κ > 0` such that for all large `n`, every adjacency labeling scheme for the `n`-vertex graphs of
`P'_α` has labels of at least `κ n^{1/α}` bits. -/
theorem theorem3_proper (hα : 2 < α) : ∃ κ > 0, ∀ᶠ n : ℕ in atTop, ∀ X : ℝ,
    HasAdjLabeling n (IsProperPowerLaw α) X → κ * (n : ℝ) ^ (1 / α) ≤ X := by
  have hα1 : 1 < α := by linarith
  have hC := C_pos hα1
  refine ⟨(C α / 2) ^ (1 / α) / 4, by positivity, ?_⟩
  filter_upwards [eventually_construct hα] with n ⟨hi3, hL, hB, h4⟩ X hX
  have hlab : HasAdjLabeling (i₁ α n) (fun _ => True) X :=
    hX.of_embedding fun H _ => construct hα hi3 hL hB H
  have hm := moon (by omega) hlab
  have hlt := lt_i₁ hα1 n
  rw [Real.div_rpow (by positivity) (by norm_num), Real.mul_rpow hC.le (by positivity)] at hlt h4
  have hnat : (i₁ α n : ℝ) - 2 ≤ 2 * (((i₁ α n - 1) / 2 : ℕ) : ℝ) := by
    have : i₁ α n ≤ 2 * ((i₁ α n - 1) / 2) + 2 := by omega
    have : (i₁ α n : ℝ) ≤ 2 * (((i₁ α n - 1) / 2 : ℕ) : ℝ) + 2 := by exact_mod_cast this
    linarith
  rw [Real.div_rpow hC.le (by norm_num)]
  set z := C α ^ (1 / α) * (n : ℝ) ^ (1 / α) / 2 ^ (1 / α)
  have : C α ^ (1 / α) / 2 ^ (1 / α) / 4 * (n : ℝ) ^ (1 / α) = z / 4 := by ring
  rw [this]
  linarith

end Podc.PowerLawLabeling
