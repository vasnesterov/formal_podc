import Papers.PODC2026.ReachingUnivalency.RPK

/-!
# Reaching Univalency — §5: existence of good deterministic samplers

The paper (§5) derandomises the sampling of Probabilistic ε-RPK by fixing one sampling choice
that is good "for every set". This file proves the (corrected) existence statement
`exists_sampler`: for every accuracy `δ > 0` and exception rate `γ > 0` there is a sample size
`k` (independent of `n`) such that for every `n` and every non-empty response set `R ⊆ Fin n` some
sampling choice — each of the `n` processors samples `k` members of `R`, with repetitions — has,
simultaneously for **every** set `S`, at most `γ n` processors whose sample deviates from `R` on
`S` by at least `δ`.

## Proof (probabilistic method, by pure counting)

All counting is over the finite space of sampling choices `f : Fin n → Fin k → R`.

1. *Chebyshev* (`card_dev_ge_le`): for a fixed `S`, the number of single samples
   `g : Fin k → R` with `δ ≤ |dev g R S|` is at most `|R|^k / (k δ²)`. This is a second-moment
   computation (`sum_sq_sum_eq`): if `∑ h = 0` then
   `|Y| · ∑_g (∑_j h (g j))² = k |Y|^k ∑_y h y²` (cross terms vanish by independence).
2. *Many bad processors are unlikely* (`card_many_bad_le`): if a set `B` of samples has density
   `≤ α ≤ 1`, the number of `f : Fin n → X` with at least `t` coordinates in `B` is at most
   `2^n α^t |X|^n` (union over the sets `T` of bad coordinates, product structure).
3. *Union bound over `S`* (2^n sets): with `t = ⌊γ n⌋ + 1`, `L = ⌈1/γ⌉` and
   `α = 1/(k δ²) ≤ 8^{-L}` we get `α^t ≤ 8^{-n}` (as `L t ≥ n`), so the bad choices number at
   most `4^n 8^{-n} |R|^{kn} < |R|^{kn}`: a good choice exists.

No case split on `n` is needed: for small `n` (`γ n < 1`) the same bound forces *no* bad
processor at all.
-/

namespace ReachingUnivalency.RPK

open Finset

/-! ### Sums over tuples -/

/-- Splitting a sum over `(k+1)`-tuples into the first entry and the rest. -/
lemma sum_fun_succ {Y : Type*} [Fintype Y] {k : ℕ} (F : (Fin (k + 1) → Y) → ℚ) :
    ∑ g, F g = ∑ y, ∑ g : Fin k → Y, F (Fin.cons y g) := by
  rw [← (Fin.consEquiv fun _ => Y).sum_comp, Fintype.sum_prod_type]
  rfl

/-- First moment: a centred function summed along a uniformly random tuple has mean zero. -/
lemma sum_sum_eq_zero {Y : Type*} [Fintype Y] (h : Y → ℚ) (h0 : ∑ y, h y = 0) (k : ℕ) :
    ∑ g : Fin k → Y, ∑ j, h (g j) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_fun_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sum_add_distrib, ih, sum_const,
      card_univ, nsmul_eq_mul, add_zero]
    simp [h0, ← mul_sum]

/-- Second moment: for a centred `h`, `|Y| · ∑_g (∑_j h (g j))² = k |Y|^k ∑_y h y²`. -/
lemma sum_sq_sum_eq {Y : Type*} [Fintype Y] (h : Y → ℚ) (h0 : ∑ y, h y = 0) (k : ℕ) :
    (Fintype.card Y : ℚ) * ∑ g : Fin k → Y, (∑ j, h (g j)) ^ 2 =
      k * (Fintype.card Y : ℚ) ^ k * ∑ y, h y ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_fun_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hy : ∀ y, ∑ g : Fin k → Y, (h y + ∑ j, h (g j)) ^ 2 =
        (Fintype.card Y : ℚ) ^ k * h y ^ 2 + 2 * h y * ∑ g : Fin k → Y, ∑ j, h (g j) +
          ∑ g : Fin k → Y, (∑ j, h (g j)) ^ 2 := by
      intro y
      simp only [add_sq, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    simp only [hy, sum_sum_eq_zero h h0, mul_zero, add_zero, sum_add_distrib, sum_const,
      card_univ, nsmul_eq_mul, mul_add, ih, ← mul_sum]
    push_cast
    ring

/-! ### Step 1: Chebyshev by counting -/

/-- Chebyshev's inequality by counting: among all `g : Fin k → Y`, at most `|Y|^k / (k δ²)` have
an empirical frequency of `P` deviating by `≥ δ` from the true frequency of `P` in `Y`. -/
theorem card_dev_ge_le {Y : Type*} [Fintype Y] [Nonempty Y] (P : Y → Prop) [DecidablePred P]
    {k : ℕ} (hk : 0 < k) {δ : ℚ} (hδ : 0 < δ) :
    (((univ.filter fun g : Fin k → Y => δ ≤
        |((univ.filter fun j => P (g j)).card : ℚ) / k -
          ((univ.filter P).card : ℚ) / Fintype.card Y|).card : ℕ) : ℚ) ≤
      (Fintype.card Y : ℚ) ^ k / (k * δ ^ 2) := by
  set N : ℚ := (Fintype.card Y : ℚ) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast Fintype.card_pos
  set q : ℚ := ((univ.filter P).card : ℚ) / N with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one hN, hNdef]
    exact_mod_cast card_le_univ _
  set h : Y → ℚ := fun y => (if P y then 1 else 0) - q with hh
  have h0 : ∑ y, h y = 0 := by
    simp only [hh, sum_sub_distrib, sum_boole, sum_const, card_univ, nsmul_eq_mul]
    rw [hq, ← hNdef]
    field_simp
    ring
  have hsq : ∑ y, h y ^ 2 ≤ N := by
    calc ∑ y, h y ^ 2 ≤ ∑ _y : Y, (1 : ℚ) := by
          refine sum_le_sum fun y _ => ?_
          simp only [hh]
          split_ifs
          · nlinarith
          · nlinarith
      _ = N := by simp [hNdef]
  have hs : ∀ g : Fin k → Y, ∑ j, h (g j) =
      ((univ.filter fun j => P (g j)).card : ℚ) - k * q := by
    intro g
    simp [hh, sum_sub_distrib, sum_boole]
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  have hmom : ∑ g : Fin k → Y, (∑ j, h (g j)) ^ 2 ≤ k * N ^ k := by
    have := sum_sq_sum_eq h h0 k
    rw [← hNdef] at this
    have h2 : N * ∑ g : Fin k → Y, (∑ j, h (g j)) ^ 2 ≤ N * (k * N ^ k) := by
      rw [this]
      calc (k : ℚ) * N ^ k * ∑ y, h y ^ 2 ≤ k * N ^ k * N := by gcongr
        _ = N * (k * N ^ k) := by ring
    exact le_of_mul_le_mul_left h2 hN
  set A := univ.filter fun g : Fin k → Y => δ ≤
        |((univ.filter fun j => P (g j)).card : ℚ) / k - q| with hA
  have hcard : (A.card : ℚ) * (k * δ) ^ 2 ≤ k * N ^ k := by
    calc (A.card : ℚ) * (k * δ) ^ 2 = ∑ _g ∈ A, (k * δ) ^ 2 := by simp
      _ ≤ ∑ g ∈ A, (∑ j, h (g j)) ^ 2 := by
          refine sum_le_sum fun g hg => ?_
          rw [hA, mem_filter] at hg
          have e : ∑ j, h (g j) = k * (((univ.filter fun j => P (g j)).card : ℚ) / k - q) := by
            rw [hs]; field_simp
          have hle : (k : ℚ) * δ ≤ |(k : ℚ) * (((univ.filter fun j => P (g j)).card : ℚ) / k - q)| := by
            rw [abs_mul, abs_of_pos hk']
            exact mul_le_mul_of_nonneg_left hg.2 hk'.le
          rw [e]
          exact (pow_le_pow_left₀ (by positivity) hle 2).trans (sq_abs _).le
      _ ≤ ∑ g : Fin k → Y, (∑ j, h (g j)) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
      _ ≤ k * N ^ k := hmom
  rw [le_div_iff₀ (by positivity)]
  calc (A.card : ℚ) * (k * δ ^ 2) = (A.card * (k * δ) ^ 2) / k := by field_simp
    _ ≤ (k * N ^ k) / k := by gcongr
    _ = N ^ k := by field_simp

/-! ### Step 2: many bad coordinates are unlikely -/

/-- If `B` has density at most `α ≤ 1` in `X`, then at most `2^n α^t |X|^n` functions
`f : Fin n → X` have at least `t` coordinates in `B`. -/
theorem card_many_bad_le {X : Type*} [Fintype X] [DecidableEq X] (B : Finset X) {α : ℚ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hB : (B.card : ℚ) ≤ α * Fintype.card X) (n t : ℕ) :
    (((univ.filter fun f : Fin n → X => t ≤ (univ.filter fun p => f p ∈ B).card).card : ℕ) : ℚ)
      ≤ 2 ^ n * α ^ t * (Fintype.card X : ℚ) ^ n := by
  set N : ℚ := (Fintype.card X : ℚ)
  have hsub : (univ.filter fun f : Fin n → X => t ≤ (univ.filter fun p => f p ∈ B).card) ⊆
      (univ.filter fun T : Finset (Fin n) => t ≤ T.card).biUnion
        (fun T => Fintype.piFinset fun p => if p ∈ T then B else univ) := by
    intro f hf
    rw [mem_filter] at hf
    rw [mem_biUnion]
    refine ⟨univ.filter fun p => f p ∈ B, by simpa using hf.2, ?_⟩
    rw [Fintype.mem_piFinset]
    intro p
    split_ifs with hp
    · simpa using hp
    · exact mem_univ _
  have hT : ∀ T : Finset (Fin n), t ≤ T.card →
      (((Fintype.piFinset fun p => if p ∈ T then B else univ).card : ℕ) : ℚ) ≤ α ^ t * N ^ n := by
    intro T hT
    rw [Fintype.card_piFinset]
    push_cast
    calc ∏ p, (((if p ∈ T then B else univ).card : ℕ) : ℚ)
        ≤ ∏ p : Fin n, ((if p ∈ T then α else 1) * N) := by
          refine prod_le_prod₀ (fun _ _ => by positivity) fun p _ => ?_
          split_ifs
          · exact hB
          · simp [N]
      _ = α ^ T.card * N ^ n := by
          rw [prod_mul_distrib, prod_ite_mem, univ_inter, prod_const, prod_const, card_univ,
            Fintype.card_fin]
      _ ≤ α ^ t * N ^ n :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hα0 hα1 hT) (by positivity)
  calc (((univ.filter fun f : Fin n → X => t ≤ (univ.filter fun p => f p ∈ B).card).card : ℕ) : ℚ)
      ≤ (((univ.filter fun T : Finset (Fin n) => t ≤ T.card).biUnion
          (fun T => Fintype.piFinset fun p => if p ∈ T then B else univ)).card : ℚ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ T ∈ univ.filter fun T : Finset (Fin n) => t ≤ T.card,
          (((Fintype.piFinset fun p => if p ∈ T then B else univ).card : ℕ) : ℚ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _T ∈ univ.filter fun T : Finset (Fin n) => t ≤ T.card, α ^ t * N ^ n :=
        sum_le_sum fun T hTm => hT T (mem_filter.1 hTm).2
    _ ≤ ∑ _T : Finset (Fin n), α ^ t * N ^ n :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
    _ = 2 ^ n * α ^ t * N ^ n := by
        simp [Fintype.card_finset, mul_assoc]

/-! ### Step 3: the union bound -/

/-- The number of members of `R` (as a subtype) lying in `S` is `|S ∩ R|`. -/
lemma card_filter_coe_mem {n : ℕ} (R S : Finset (Fin n)) :
    (univ.filter fun y : R => (y : Fin n) ∈ S).card = (S ∩ R).card := by
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1
  ext x
  simp [and_comm]

/-- Derandomisation (§5 of the paper, corrected form): for every accuracy `δ > 0` and exception
rate `γ > 0` there is a sample size `k` such that for every `n` and every non-empty response set
`R ⊆ Fin n` some sampling choice (each of the `n` processors samples `k` members of `R`) has, for
EVERY set `S`, at most `γ n` processors whose sample deviates from `R` on `S` by `≥ δ`. -/
theorem exists_sampler {δ γ : ℚ} (hδ : 0 < δ) (hγ : 0 < γ) :
    ∃ k : ℕ, 0 < k ∧ ∀ (n : ℕ) (R : Finset (Fin n)), R.Nonempty →
      ∃ smp : Fin n → Fin k → Fin n, (∀ p j, smp p j ∈ R) ∧
        ∀ S : Finset (Fin n),
          (((univ.filter fun p => δ ≤ |dev (smp p) R S|).card : ℕ) : ℚ) ≤ γ * n := by
  classical
  set L : ℕ := ⌈1 / γ⌉₊ with hL
  refine ⟨⌈(8 : ℚ) ^ L / δ ^ 2⌉₊ + 1, Nat.succ_pos _, ?_⟩
  set k : ℕ := ⌈(8 : ℚ) ^ L / δ ^ 2⌉₊ + 1 with hkdef
  intro n R hR
  have hk : 0 < k := Nat.succ_pos _
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  have : Nonempty R := hR.to_subtype
  have hn : 0 < n := by obtain ⟨x, _⟩ := hR; exact x.pos
  -- the per-processor failure density `α = 1 / (k δ²) ≤ 8^{-L}`
  set α : ℚ := 1 / (k * δ ^ 2) with hα
  have hα0 : 0 ≤ α := by positivity
  have h8 : (8 : ℚ) ^ L < k * δ ^ 2 := by
    have : (8 : ℚ) ^ L / δ ^ 2 < k := by
      rw [hkdef]; push_cast
      exact (Nat.le_ceil _).trans_lt (lt_add_one _)
    exact (div_lt_iff₀ (by positivity)).1 this
  have hαL : α ≤ (1 / 8) ^ L := by
    rw [hα, one_div_pow]
    exact one_div_le_one_div_of_le (by positivity) h8.le
  have hα1 : α ≤ 1 := hαL.trans (pow_le_one₀ (by norm_num) (by norm_num))
  -- the bad single samples for a set `S`
  set B : Finset (Fin n) → Finset (Fin k → R) := fun S =>
    univ.filter fun g => δ ≤ |dev (fun j => (g j : Fin n)) R S| with hBdef
  set M : ℚ := (Fintype.card (Fin k → R) : ℚ) with hM
  have hMR : M = (R.card : ℚ) ^ k := by
    rw [hM, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]; push_cast; rfl
  have hB : ∀ S, ((B S).card : ℚ) ≤ α * M := by
    intro S
    have := card_dev_ge_le (Y := R) (fun y : R => (y : Fin n) ∈ S) hk hδ
    rw [card_filter_coe_mem, Fintype.card_coe] at this
    have e : ((B S).card : ℚ) ≤ (R.card : ℚ) ^ k / (k * δ ^ 2) := this
    rw [hMR, hα]
    calc ((B S).card : ℚ) ≤ (R.card : ℚ) ^ k / (k * δ ^ 2) := e
      _ = 1 / (k * δ ^ 2) * (R.card : ℚ) ^ k := by ring
  -- at least `t` bad processors violates the bound `γ n`
  set t : ℕ := ⌊γ * n⌋₊ + 1 with ht
  have hLt : n ≤ L * t := by
    have h1 : 1 / γ ≤ (L : ℚ) := Nat.le_ceil _
    have h2 : γ * n < (t : ℚ) := by rw [ht]; push_cast; exact Nat.lt_floor_add_one _
    have : (n : ℚ) ≤ L * t :=
      calc (n : ℚ) = 1 / γ * (γ * n) := by field_simp
        _ ≤ L * t := mul_le_mul h1 h2.le (by positivity) (by positivity)
    exact_mod_cast this
  have hαt : α ^ t ≤ (1 / 8) ^ n := by
    calc α ^ t ≤ ((1 / 8) ^ L) ^ t := pow_le_pow_left₀ hα0 hαL t
      _ = (1 / 8) ^ (L * t) := by rw [pow_mul]
      _ ≤ (1 / 8) ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num) hLt
  -- the bad sampling choices
  set Bad : Finset (Fin n → Fin k → R) := univ.filter fun f =>
    ∃ S : Finset (Fin n), t ≤ (univ.filter fun p => f p ∈ B S).card with hBad
  have hBadcard : (Bad.card : ℚ) < (Fintype.card (Fin n → Fin k → R) : ℚ) := by
    have hsub : Bad ⊆ (univ : Finset (Finset (Fin n))).biUnion fun S =>
        univ.filter fun f : Fin n → Fin k → R => t ≤ (univ.filter fun p => f p ∈ B S).card := by
      intro f hf
      rw [hBad, mem_filter] at hf
      obtain ⟨S, hS⟩ := hf.2
      exact mem_biUnion.2 ⟨S, mem_univ _, mem_filter.2 ⟨mem_univ _, hS⟩⟩
    have hcardM : (Fintype.card (Fin n → Fin k → R) : ℚ) = M ^ n := by
      rw [hM, Fintype.card_fun, Fintype.card_fin]; push_cast; rfl
    have hM0 : 0 < M := by rw [hM]; exact_mod_cast Fintype.card_pos
    calc (Bad.card : ℚ)
        ≤ (((univ : Finset (Finset (Fin n))).biUnion fun S =>
            univ.filter fun f : Fin n → Fin k → R =>
              t ≤ (univ.filter fun p => f p ∈ B S).card).card : ℚ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ ∑ S : Finset (Fin n), (((univ.filter fun f : Fin n → Fin k → R =>
              t ≤ (univ.filter fun p => f p ∈ B S).card).card : ℕ) : ℚ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ _S : Finset (Fin n), 2 ^ n * α ^ t * M ^ n :=
          sum_le_sum fun S _ => card_many_bad_le (B S) hα0 hα1 (hB S) n t
      _ = 2 ^ n * 2 ^ n * α ^ t * M ^ n := by
          simp [Fintype.card_finset, mul_assoc]
      _ ≤ 2 ^ n * 2 ^ n * (1 / 8) ^ n * M ^ n := by gcongr
      _ = (1 / 2) ^ n * M ^ n := by
          rw [← mul_pow, ← mul_pow, ← mul_pow, ← mul_pow]; norm_num
      _ < 1 * M ^ n := by
          gcongr
          exact pow_lt_one₀ (by norm_num) (by norm_num) hn.ne'
      _ = _ := by rw [one_mul, hcardM]
  have hlt : Bad.card < (univ : Finset (Fin n → Fin k → R)).card := by
    rw [card_univ]; exact_mod_cast hBadcard
  obtain ⟨f, -, hf⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨fun p j => (f p j : Fin n), fun p j => (f p j).2, fun S => ?_⟩
  have hfS : ¬ t ≤ (univ.filter fun p => f p ∈ B S).card := fun h =>
    hf (mem_filter.2 ⟨mem_univ _, S, h⟩)
  have heq : (univ.filter fun p => δ ≤ |dev (fun j => (f p j : Fin n)) R S|) =
      univ.filter fun p => f p ∈ B S := by
    refine filter_congr fun p _ => ?_
    simp [hBdef]
  rw [heq]
  have hle : (univ.filter fun p => f p ∈ B S).card ≤ ⌊γ * n⌋₊ := by omega
  calc (((univ.filter fun p => f p ∈ B S).card : ℕ) : ℚ) ≤ (⌊γ * n⌋₊ : ℚ) := by exact_mod_cast hle
    _ ≤ γ * n := Nat.floor_le (by positivity)

end ReachingUnivalency.RPK
