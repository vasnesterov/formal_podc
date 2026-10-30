import Papers.PODC2011.UniformLocalAlgorithms.SeqNumber

/-!
# Observation 4.1: sequence-number functions of additive and product bounds

* `maxLe g r`: the largest `y` with `g y ≤ r` (for `g → ∞`); `0` if there is none.
* `observation_4_1_additive`: the constant function `1` is a sequence-number function for every
  additive function `f(x) = Σ_k f_k(x_k)` with non-negative ascending `f_k`.
* `observation_4_1_product`: `s(i) = ⌈log₂ i⌉ + 1` is a sequence-number function for
  `f(x₁, x₂) = f₁(x₁) · f₂(x₂)` with ascending `f₁, f₂ ≥ 1`.

"Ascending" (non-decreasing and tending to infinity) is only used through `Tendsto f_k atTop atTop`.
-/

open Filter

namespace Podc.UniformLocalAlgorithms

/-- The largest natural number `y` with `g y ≤ r` (`0` if there is none or if they are unbounded). -/
noncomputable def maxLe (g : ℕ → ℝ) (r : ℝ) : ℕ := sSup {y | g y ≤ r}

lemma bddAbove_le_of_tendsto {g : ℕ → ℝ} (hg : Tendsto g atTop atTop) (r : ℝ) :
    BddAbove {y | g y ≤ r} := by
  obtain ⟨N, hN⟩ := (tendsto_atTop.1 hg (r + 1)).exists_forall_of_atTop
  refine ⟨N, fun y hy => ?_⟩
  by_contra h
  have := hN y (by simp at h; omega)
  change g y ≤ r at hy
  linarith

lemma le_maxLe {g : ℕ → ℝ} (hg : Tendsto g atTop atTop) {r : ℝ} {y : ℕ} (hy : g y ≤ r) :
    y ≤ maxLe g r :=
  le_csSup (bddAbove_le_of_tendsto hg r) hy

lemma maxLe_spec {g : ℕ → ℝ} (hg : Tendsto g atTop atTop) {r : ℝ} (h : ∃ y, g y ≤ r) :
    g (maxLe g r) ≤ r :=
  Nat.sSup_mem h (bddAbove_le_of_tendsto hg r)

/-- **Observation 4.1** (first item). The constant function `1` is a sequence-number function for
every additive function `f(x) = Σ_k f_k(x_k)`, where the `f_k ≥ 0` tend to infinity. -/
theorem observation_4_1_additive {ℓ : ℕ} (fk : Fin ℓ → ℕ → ℝ) (h0 : ∀ k y, 0 ≤ fk k y)
    (hinf : ∀ k, Tendsto (fk k) atTop atTop) :
    IsSeqNumber (fun x => ∑ k, fk k (x k)) (fun _ => 1) := by
  classical
  refine ⟨⟨fun _ _ _ => le_rfl, 1, by norm_num, fun _ _ => by simp⟩, ?_⟩
  let S : ℕ → Finset (Fin ℓ → ℕ) := fun i =>
    if ∀ k, ∃ y, fk k y ≤ i then {fun k => maxLe (fk k) i} else ∅
  refine ⟨⟨S, fun i y hy => ?_⟩, ℓ + 1, ⟨by positivity, fun i x hx => ?_⟩, fun i => ?_⟩
  · have hk : ∀ k, fk k (y k) ≤ i := fun k =>
      (Finset.single_le_sum (fun j _ => h0 j (y j)) (Finset.mem_univ k)).trans hy
    refine ⟨fun k => maxLe (fk k) i, ?_, fun k => le_maxLe (hinf k) (hk k)⟩
    have hall : ∀ k, ∃ y, fk k y ≤ i := fun k => ⟨y k, hk k⟩
    simp [S, hall]
  · simp only [S] at hx
    split_ifs at hx with h
    · rw [Finset.mem_singleton.1 hx]
      calc ∑ k, fk k (maxLe (fk k) i) ≤ ∑ _k : Fin ℓ, (i : ℝ) :=
            Finset.sum_le_sum fun k _ => maxLe_spec (hinf k) (h k)
        _ = ℓ * i := by simp
        _ ≤ (ℓ + 1) * i := by nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    · simp at hx
  · simp only [S]; split_ifs <;> simp

/-- **Observation 4.1** (second item). For `f(x₁, x₂) = f₁(x₁) · f₂(x₂)` with `f₁, f₂ ≥ 1` tending to
infinity, `s(i) = ⌈log₂ i⌉ + 1` is a sequence-number function. -/
theorem observation_4_1_product (f₁ f₂ : ℕ → ℝ) (h₁ : ∀ y, 1 ≤ f₁ y) (h₂ : ∀ y, 1 ≤ f₂ y)
    (hinf₁ : Tendsto f₁ atTop atTop) (hinf₂ : Tendsto f₂ atTop atTop) :
    IsSeqNumber (fun x : Fin 2 → ℕ => f₁ (x 0) * f₂ (x 1)) (fun i => Nat.clog 2 i + 1) := by
  classical
  refine ⟨⟨fun a b hab => by simpa using Nat.clog_mono_right 2 hab, 2, by norm_num,
    fun i hi => ?_⟩, ?_⟩
  · -- `⌈log₂ 2i⌉ ≤ ⌈log₂ i⌉ + 1`
    have : Nat.clog 2 (2 * i) ≤ Nat.clog 2 i + 1 := by
      apply Nat.clog_le_of_le_pow
      rw [pow_succ]
      have := Nat.le_pow_clog (by norm_num : 1 < 2) i
      omega
    show Nat.clog 2 (2 * i) + 1 ≤ 2 * (Nat.clog 2 i + 1)
    omega
  -- the pair for the "split" `j`: `f₁ ≤ 2^j` and `f₂ ≤ 2i/2^j`
  let r₂ : ℕ → ℕ → ℝ := fun i j => 2 * i / 2 ^ j
  let good : ℕ → ℕ → Prop := fun i j => (∃ y, f₁ y ≤ 2 ^ j) ∧ ∃ y, f₂ y ≤ r₂ i j
  let vec : ℕ → ℕ → (Fin 2 → ℕ) := fun i j => ![maxLe f₁ (2 ^ j), maxLe f₂ (r₂ i j)]
  let S : ℕ → Finset (Fin 2 → ℕ) := fun i =>
    ((Finset.range (Nat.clog 2 i + 1)).filter (good i)).image (vec i)
  refine ⟨⟨S, fun i y hy => ?_⟩, 2, ⟨by norm_num, fun i x hx => ?_⟩, fun i => ?_⟩
  · -- domination
    have hf1 : 1 ≤ f₁ (y 0) := h₁ _
    have hf2 : 1 ≤ f₂ (y 1) := h₂ _
    have hy1 : f₁ (y 0) ≤ i := by nlinarith
    have hex : ∃ j, f₁ (y 0) ≤ 2 ^ j := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (f₁ (y 0)) (by norm_num : (1 : ℝ) < 2)
      exact ⟨n, hn.le⟩
    set j := Nat.find hex with hj
    have hjspec : f₁ (y 0) ≤ 2 ^ j := Nat.find_spec hex
    have hji : j ≤ Nat.clog 2 i := by
      apply Nat.find_min' hex
      have := Nat.le_pow_clog (by norm_num : 1 < 2) i
      calc f₁ (y 0) ≤ i := hy1
        _ ≤ 2 ^ Nat.clog 2 i := by exact_mod_cast this
    have hf2r : f₂ (y 1) ≤ r₂ i j := by
      simp only [r₂]
      rw [le_div_iff₀ (by positivity)]
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0]; simp; nlinarith
      · have hlt : (2 : ℝ) ^ (j - 1) < f₁ (y 0) := by
          have := Nat.find_min hex (by omega : j - 1 < j)
          simpa using this
        have : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [this]
        nlinarith
    refine ⟨vec i j, Finset.mem_image.2 ⟨j, Finset.mem_filter.2
      ⟨Finset.mem_range.2 (by omega), ⟨y 0, hjspec⟩, ⟨y 1, hf2r⟩⟩, rfl⟩, ?_⟩
    intro k
    fin_cases k
    · exact le_maxLe hinf₁ hjspec
    · exact le_maxLe hinf₂ hf2r
  · -- boundedness with constant 2
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨-, hg1, hg2⟩ := Finset.mem_filter.1 hj
    have e1 := maxLe_spec hinf₁ hg1
    have e2 := maxLe_spec hinf₂ hg2
    simp only [vec, Matrix.cons_val_zero, Matrix.cons_val_one]
    have p1 : 0 ≤ f₁ (maxLe f₁ (2 ^ j)) := by linarith [h₁ (maxLe f₁ (2 ^ j))]
    calc f₁ (maxLe f₁ (2 ^ j)) * f₂ (maxLe f₂ (r₂ i j)) ≤ 2 ^ j * r₂ i j :=
          mul_le_mul e1 e2 (by linarith [h₂ (maxLe f₂ (r₂ i j))]) (by positivity)
      _ = 2 * i := by simp only [r₂]; field_simp
  · -- cardinality
    calc (S i).card ≤ ((Finset.range (Nat.clog 2 i + 1)).filter (good i)).card :=
          Finset.card_image_le
      _ ≤ (Finset.range (Nat.clog 2 i + 1)).card := Finset.card_filter_le _ _
      _ = Nat.clog 2 i + 1 := Finset.card_range _

end Podc.UniformLocalAlgorithms
