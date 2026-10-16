import Mathlib

/-!
# Leader pointers of the block counters (§3.2, Lemmas 1 and 2)

Block `i` runs a `c_i`-counter with `c_i = τ (2m)^{i+1}` (the base counter's output modulo
`c_i`). Its value is read as a pair `(r, y) ∈ [τ] × [(2m)^{i+1}]` and the block points to the
leader candidate `b = ⌊y / (2m)^i⌋ mod m`. In terms of the counter value `v`,
`b = ⌊(v mod c_i) / (τ (2m)^i)⌋ mod m` (`ptr`).

If block `i` counts as `v = (s + q) mod c`, the pointer is `⌊(q + s) / (τ (2m)^i)⌋ mod m`
(`ptr_eq`), and the arithmetic lemmas `lemma1` and `lemma2` find, for every target `β ∈ [m]`,
a window of `τ` consecutive rounds in which *all* blocks point to `β` at the same time, within
`τ (2m)^{h+1}` rounds.
-/

namespace SynchronousCounting

/-- The pointer of block `i` for counter value `v` (`b[i, j]` in the paper). -/
def ptr (τ m i v : ℕ) : ℕ := v % (τ * (2 * m) ^ (i + 1)) / (τ * (2 * m) ^ i) % m

/-- The round counter `r[i, j]` of a block for counter value `v` (`τ ∣ c_i`, so this is `v mod τ`
whatever the block). -/
def rnd (τ v : ℕ) : ℕ := v % τ

lemma ptr_eq {τ m i c : ℕ} (hc : τ * (2 * m) ^ (i + 1) ∣ c) (x : ℕ) :
    ptr τ m i (x % c) = x / (τ * (2 * m) ^ i) % m := by
  unfold ptr
  rw [Nat.mod_mod_of_dvd _ hc, pow_succ, ← mul_assoc, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Dvd.intro_left 2 rfl)]

/-- **Lemma 1** (arithmetic core). A counter whose pointer changes every `D` rounds visits every
`β ∈ [m]` for `D` consecutive rounds within any `2mD` rounds. -/
theorem lemma1 {D m : ℕ} (hD : 0 < D) (hm : 0 < m) (t s : ℕ) {β : ℕ} (hβ : β < m) :
    ∃ w, t ≤ w ∧ w + D ≤ t + 2 * m * D ∧
      ∀ q, w ≤ q → q < w + D → (q + s) / D % m = β := by
  set K₀ := (t + s + D - 1) / D with hK₀
  have hK₀lo : t + s ≤ K₀ * D := by
    have := Nat.div_add_mod (t + s + D - 1) D
    have := Nat.mod_lt (t + s + D - 1) hD
    rw [hK₀, mul_comm]; omega
  have hK₀hi : K₀ * D ≤ t + s + D - 1 := by
    rw [hK₀]; exact Nat.div_mul_le_self _ _
  have hdm := Nat.div_add_mod K₀ m
  have hmlt := Nat.mod_lt K₀ hm
  obtain ⟨K, hKm, hKge, hKle⟩ : ∃ K, K % m = β ∧ K₀ ≤ K ∧ K ≤ K₀ + (m - 1) := by
    have hmod : ∀ e, (m * (K₀ / m) + e) % m = e % m := fun e => by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    by_cases hb : K₀ % m ≤ β
    · refine ⟨m * (K₀ / m) + β, ?_, ?_, ?_⟩
      · rw [hmod, Nat.mod_eq_of_lt hβ]
      · omega
      · omega
    · refine ⟨m * (K₀ / m) + (m + β), ?_, ?_, ?_⟩
      · rw [hmod, Nat.add_mod_left, Nat.mod_eq_of_lt hβ]
      · omega
      · omega
  refine ⟨K * D - s, ?_, ?_, ?_⟩
  · have : K₀ * D ≤ K * D := Nat.mul_le_mul_right _ hKge
    omega
  · have h1 : K * D ≤ (K₀ + (m - 1)) * D := Nat.mul_le_mul_right _ hKle
    have h2 : (K₀ + (m - 1)) * D = K₀ * D + (m - 1) * D := add_mul _ _ _
    have h3 : (m - 1) * D + D = m * D := by
      rw [← Nat.succ_mul]; congr 1; omega
    have h4 : m * D + D ≤ 2 * m * D := by nlinarith
    have : K₀ * D ≤ K * D := Nat.mul_le_mul_right _ hKge
    omega
  · intro q hq1 hq2
    have : K₀ * D ≤ K * D := Nat.mul_le_mul_right _ hKge
    have hdiv : (q + s) / D = K := by
      rw [Nat.div_eq_iff hD]
      constructor <;> omega
    rw [hdiv, hKm]

/-- **Lemma 2** (arithmetic core). Blocks `0, …, h` counting with arbitrary offsets `s i` all point
to `β` simultaneously during some `τ` consecutive rounds `[u, u + τ)` with
`t ≤ u` and `u + τ ≤ t + τ (2m)^{h+1}`. -/
theorem lemma2 {τ m : ℕ} (hτ : 0 < τ) (hm : 0 < m) {β : ℕ} (hβ : β < m) (s : ℕ → ℕ) (h : ℕ) :
    ∀ t, ∃ u, t ≤ u ∧ u + τ ≤ t + τ * (2 * m) ^ (h + 1) ∧
      ∀ i ≤ h, ∀ q, u ≤ q → q < u + τ → (q + s i) / (τ * (2 * m) ^ i) % m = β := by
  induction h with
  | zero =>
    intro t
    obtain ⟨w, hw1, hw2, hw3⟩ := lemma1 (D := τ) hτ hm t (s 0) hβ
    refine ⟨w, hw1, by rw [zero_add, pow_one]; linarith, fun i hi q hq1 hq2 => ?_⟩
    obtain rfl : i = 0 := by omega
    simpa using hw3 q hq1 hq2
  | succ h ih =>
    intro t
    have hD : 0 < τ * (2 * m) ^ (h + 1) := by positivity
    obtain ⟨w, hw1, hw2, hw3⟩ := lemma1 hD hm t (s (h + 1)) hβ
    obtain ⟨u, hu1, hu2, hu3⟩ := ih w
    refine ⟨u, hw1.trans hu1, ?_, fun i hi q hq1 hq2 => ?_⟩
    · have : 2 * m * (τ * (2 * m) ^ (h + 1)) = τ * (2 * m) ^ (h + 1 + 1) := by ring
      omega
    · rcases Nat.lt_or_ge i (h + 1) with hlt | hge
      · exact hu3 i (by omega) q hq1 hq2
      · obtain rfl : i = h + 1 := by omega
        exact hw3 q (by omega) (by omega)

end SynchronousCounting
