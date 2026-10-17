import Papers.PODC2026.ReachingUnivalency.RPK
import Podc.Probability.Finite.Uniform

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

All counting is over the finite space of sampling choices `f : Fin n → Fin k → R`; the two
probabilistic facts come from the finite probability library
(`Podc/Probability/Finite/Uniform.lean`).

1. *Chebyshev* (`Cslib.Probability.card_freq_dev_ge_le`): for a fixed `S`, the number of single
   samples `g : Fin k → R` with `δ ≤ |dev g R S|` is at most `|R|^k / (k δ²)` (a second-moment
   computation; cross terms vanish by independence).
2. *Many bad processors are unlikely* (`Cslib.Probability.card_many_le`): if a set `B` of samples
   has density `≤ α ≤ 1`, the number of `f : Fin n → X` with at least `t` coordinates in `B` is at
   most `2^n α^t |X|^n` (union over the sets `T` of bad coordinates, product structure).
3. *Union bound over `S`* (2^n sets): with `t = ⌊γ n⌋ + 1`, `L = ⌈1/γ⌉` and
   `α = 1/(k δ²) ≤ 8^{-L}` we get `α^t ≤ 8^{-n}` (as `L t ≥ n`), so the bad choices number at
   most `4^n 8^{-n} |R|^{kn} < |R|^{kn}`: a good choice exists.

No case split on `n` is needed: for small `n` (`γ n < 1`) the same bound forces *no* bad
processor at all.
-/

namespace ReachingUnivalency.RPK

open Finset Cslib.Probability

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
    have := card_freq_dev_ge_le (K := ℚ) (Y := R) (fun y : R => (y : Fin n) ∈ S) hk hδ
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
    ∃ S ∈ (univ : Finset (Finset (Fin n))), t ≤ (univ.filter fun p => f p ∈ B S).card with hBad
  have hBadcard : (Bad.card : ℚ) < (Fintype.card (Fin n → Fin k → R) : ℚ) := by
    have hcardM : (Fintype.card (Fin n → Fin k → R) : ℚ) = M ^ n := by
      rw [hM, Fintype.card_fun, Fintype.card_fin]; push_cast; rfl
    have hM0 : 0 < M := by rw [hM]; exact_mod_cast Fintype.card_pos
    calc (Bad.card : ℚ)
        ≤ ∑ S : Finset (Fin n), (((univ.filter fun f : Fin n → Fin k → R =>
              t ≤ (univ.filter fun p => f p ∈ B S).card).card : ℕ) : ℚ) := by
          exact_mod_cast card_filter_exists_le univ
            (fun S (f : Fin n → Fin k → R) => t ≤ (univ.filter fun p => f p ∈ B S).card)
      _ ≤ ∑ _S : Finset (Fin n), 2 ^ n * α ^ t * M ^ n := sum_le_sum fun S _ => by
          have := card_many_le (K := ℚ) (fun (_ : Fin n) (g : Fin k → R) => g ∈ B S) hα0 hα1
            (fun _ => by simpa [hM] using hB S) t
          rwa [Fintype.card_fin, hcardM] at this
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
    hf (mem_filter.2 ⟨mem_univ _, S, mem_univ _, h⟩)
  have heq : (univ.filter fun p => δ ≤ |dev (fun j => (f p j : Fin n)) R S|) =
      univ.filter fun p => f p ∈ B S := by
    refine filter_congr fun p _ => ?_
    simp [hBdef]
  rw [heq]
  have hle : (univ.filter fun p => f p ∈ B S).card ≤ ⌊γ * n⌋₊ := by omega
  calc (((univ.filter fun p => f p ∈ B S).card : ℕ) : ℚ) ≤ (⌊γ * n⌋₊ : ℚ) := by exact_mod_cast hle
    _ ≤ γ * n := Nat.floor_le (by positivity)

end ReachingUnivalency.RPK
