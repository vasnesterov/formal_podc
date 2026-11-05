import Mathlib

/-!
# The `(ΔS, ·)` mobile Byzantine failure model

Bonomi, Del Pozzo, Potop-Butucaru, Tixeuil, *Optimal Mobile Byzantine Fault Tolerant Distributed
Storage*, PODC 2016 (full version: HAL hal-01348830v2). Section 3.2.

Time is real. `f` mobile Byzantine agents move simultaneously at the times `t₀ + iΔ` (`i ∈ ℤ`), so
during *period* `i`, i.e. the time interval `[t₀ + iΔ, t₀ + (i+1)Δ)`, the agents occupy a fixed set
`pos i` of at most `f` servers. A server is *faulty* at time `τ` (`s ∈ B(τ)`) iff it belongs to the set of
the period containing `τ`.

* `affected` is the paper's `B̃[a, b] = ⋃_{τ ∈ [a,b]} B(τ)` (Definition 8);
* `card_affected_le` / `exists_card_affected_eq` determine `MaxB̃(t, t+T)` (Lemma 6, corrected:
  the maximum is `min n ((⌈T/Δ⌉ + 1) f)`); `lemma6_false` refutes the literal equality;
* `lemma7` is the counting Lemma 7 (`minC̃oR(t, t+2δ) ≥ #reply_CAM > MaxB̃(t, t+2δ)`).
-/

-- CSLib candidate: `period`, `Schedule`, `affected`, `card_affected_le`, `exists_card_affected_eq`
-- (synchronized mobile Byzantine agents on real time), e.g. `Cslib/Computability/Distributed/MobileByzantine`.

namespace Podc.MobileByzantineStorage

open Finset

/-- Index of the period containing time `τ` when the agents move at the times `t₀ + iΔ`. -/
noncomputable def period (t₀ Δ τ : ℝ) : ℤ := ⌊(τ - t₀) / Δ⌋

theorem period_eq_iff {t₀ Δ τ : ℝ} (hΔ : 0 < Δ) (i : ℤ) :
    period t₀ Δ τ = i ↔ t₀ + i * Δ ≤ τ ∧ τ < t₀ + (i + 1) * Δ := by
  unfold period
  rw [Int.floor_eq_iff, le_div_iff₀ hΔ, div_lt_iff₀ hΔ]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem period_mono {t₀ Δ a b : ℝ} (hΔ : 0 < Δ) (h : a ≤ b) : period t₀ Δ a ≤ period t₀ Δ b :=
  Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hΔ.le)

/-- The number of periods met by `[a, b]` is at most `⌈(b - a)/Δ⌉ + 1`. -/
theorem period_sub_le {t₀ Δ a b : ℝ} (hΔ : 0 < Δ) :
    period t₀ Δ b - period t₀ Δ a ≤ ⌈(b - a) / Δ⌉ := by
  unfold period
  have h1 : (b - t₀) / Δ = (a - t₀) / Δ + (b - a) / Δ := by field_simp; ring
  have h2 : ⌊(b - t₀) / Δ⌋ < ⌊(a - t₀) / Δ⌋ + ⌈(b - a) / Δ⌉ + 1 := by
    rw [Int.floor_lt, h1]; push_cast
    have := Int.lt_floor_add_one ((a - t₀) / Δ)
    have := Int.le_ceil ((b - a) / Δ)
    linarith
  omega

/-- A `(ΔS)` schedule of (at most) `f` mobile Byzantine agents on `n` servers: during period `i` the
agents occupy the servers `pos i`. -/
structure Schedule (n f : ℕ) where
  /-- The servers hosting an agent during period `i`. -/
  pos : ℤ → Finset (Fin n)
  card_pos_le : ∀ i, (pos i).card ≤ f

namespace Schedule

variable {n f : ℕ} (S : Schedule n f) (t₀ Δ : ℝ)

/-- `s ∈ B(τ)`: server `s` hosts a mobile Byzantine agent at time `τ`. -/
def Faulty (s : Fin n) (τ : ℝ) : Prop := s ∈ S.pos (period t₀ Δ τ)

/-- `B̃[a, b]`: the servers affected by an agent at some time of `[a, b]` (Definition 8). -/
noncomputable def affected (a b : ℝ) : Finset (Fin n) := by
  classical exact univ.filter fun s => ∃ τ ∈ Set.Icc a b, S.Faulty t₀ Δ s τ

variable {S t₀ Δ}

theorem affected_subset {a b : ℝ} (hΔ : 0 < Δ) :
    S.affected t₀ Δ a b ⊆ (Icc (period t₀ Δ a) (period t₀ Δ b)).biUnion S.pos := by
  classical
  intro s hs
  simp only [affected, mem_filter, mem_univ, true_and] at hs
  obtain ⟨τ, ⟨h1, h2⟩, hτ⟩ := hs
  exact mem_biUnion.2 ⟨_, mem_Icc.2 ⟨period_mono hΔ h1, period_mono hΔ h2⟩, hτ⟩

/-- **Lemma 6** (upper bound): at most `(⌈T/Δ⌉ + 1) f` servers are affected during any closed
interval of length `T`. -/
theorem card_affected_le {T : ℝ} (hΔ : 0 < Δ) (hT : 0 ≤ T) (t : ℝ) :
    (S.affected t₀ Δ t (t + T)).card ≤ (⌈T / Δ⌉₊ + 1) * f := by
  classical
  refine (card_le_card (affected_subset hΔ)).trans ?_
  refine card_biUnion_le.trans ?_
  refine (sum_le_card_nsmul _ _ f fun i _ => S.card_pos_le i).trans ?_
  rw [smul_eq_mul]
  apply Nat.mul_le_mul_right
  rw [Int.card_Icc]
  have h := period_sub_le (t₀ := t₀) (a := t) (b := t + T) hΔ
  have hc : (⌈T / Δ⌉₊ : ℤ) = ⌈T / Δ⌉ := Int.natCast_ceil_eq_ceil (div_nonneg hT hΔ.le)
  simp only [add_sub_cancel_left] at h
  omega

end Schedule

/-! ### Attaining the bound: agents sweeping disjoint blocks of servers -/

/-- Block `j` of servers: `{s | j f ≤ s < (j+1) f}`. -/
def block (n f j : ℕ) : Finset (Fin n) := univ.filter fun s => j * f ≤ s.val ∧ s.val < (j + 1) * f

theorem mem_block {n f j : ℕ} {s : Fin n} (hf : 0 < f) : s ∈ block n f j ↔ s.val / f = j := by
  simp only [block, mem_filter, mem_univ, true_and]
  rw [Nat.div_eq_iff hf]
  rw [add_mul, one_mul]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> omega

theorem card_block_le (n f j : ℕ) : (block n f j).card ≤ f := by
  have : (block n f j).map Fin.valEmbedding ⊆ Ico (j * f) ((j + 1) * f) := by
    intro x hx
    simp only [mem_map, block, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply] at hx
    obtain ⟨s, ⟨h1, h2⟩, rfl⟩ := hx
    exact mem_Ico.2 ⟨h1, h2⟩
  have := card_le_card this
  rw [card_map, Nat.card_Ico] at this
  rw [add_mul, one_mul] at this
  omega

/-- The schedule in which the agents occupy block `j` during period `j` for `0 ≤ j < p` and are
idle (on no server) otherwise. -/
def blocks (n f p : ℕ) : Schedule n f where
  pos i := if 0 ≤ i ∧ i < p then block n f i.toNat else ∅
  card_pos_le i := by
    split_ifs
    · exact card_block_le _ _ _
    · simp

theorem blocks_faulty_iff {n f p : ℕ} (hf : 0 < f) {t₀ Δ τ : ℝ} {s : Fin n} :
    (blocks n f p).Faulty t₀ Δ s τ ↔ s.val < p * f ∧ ((s.val / f : ℕ) : ℤ) = period t₀ Δ τ := by
  simp only [Schedule.Faulty, blocks]
  split_ifs with h
  · rw [mem_block hf]
    constructor
    · intro h'
      refine ⟨?_, by omega⟩
      have := (Nat.div_lt_iff_lt_mul hf).1 (show s.val / f < p by omega)
      exact this
    · rintro ⟨-, h'⟩; omega
  · simp only [Finset.notMem_empty, false_iff, not_and]
    intro hs h'
    have h1 : ((s.val / f : ℕ) : ℤ) < p := by exact_mod_cast (Nat.div_lt_iff_lt_mul hf).2 hs
    have h2 := Int.natCast_nonneg (s.val / f)
    exact h ⟨by omega, by omega⟩

theorem card_filter_val_lt {n m : ℕ} :
    (univ.filter fun s : Fin n => s.val < m).card = min n m := by
  have : (univ.filter fun s : Fin n => s.val < m).map Fin.valEmbedding = range (min n m) := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range,
      lt_min_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩; exact ⟨s.2, hs⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, h1⟩, h2, rfl⟩
  rw [← card_map, this, card_range]

namespace Schedule

/-- **Lemma 6** (the bound is attained): for every interval length `T` there are a schedule and an
interval `[t, t+T]` during which `min n ((⌈T/Δ⌉ + 1) f)` servers are affected. -/
theorem exists_card_affected_eq {n f : ℕ} (hf : 0 < f) {t₀ Δ T : ℝ} (hΔ : 0 < Δ) (hT : 0 ≤ T) :
    ∃ (S : Schedule n f) (t : ℝ),
      (S.affected t₀ Δ t (t + T)).card = min n ((⌈T / Δ⌉₊ + 1) * f) := by
  classical
  set p := ⌈T / Δ⌉₊ + 1 with hp
  set ε := min Δ (T - ((⌈T / Δ⌉₊ : ℝ) - 1) * Δ) with hε
  have hc : (⌈T / Δ⌉₊ : ℝ) < T / Δ + 1 := Nat.ceil_lt_add_one (div_nonneg hT hΔ.le)
  have hεpos : 0 < ε := by
    apply lt_min hΔ
    have : ((⌈T / Δ⌉₊ : ℝ) - 1) * Δ < T := by
      have := (lt_div_iff₀ hΔ).1 (show (⌈T / Δ⌉₊ : ℝ) - 1 < T / Δ by linarith)
      linarith
    linarith
  have hεΔ : ε ≤ Δ := min_le_left _ _
  have hεT : ε ≤ T - ((⌈T / Δ⌉₊ : ℝ) - 1) * Δ := min_le_right _ _
  -- every period `0 ≤ j < p` meets `[t₀ + Δ - ε, t₀ + Δ - ε + T]`
  have hmeet : ∀ j : ℕ, j < p → ∃ τ ∈ Set.Icc (t₀ + Δ - ε) (t₀ + Δ - ε + T),
      period t₀ Δ τ = j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · refine ⟨t₀ + Δ - ε, ⟨le_rfl, by linarith⟩, ?_⟩
      rw [period_eq_iff hΔ]; push_cast; constructor <;> linarith
    · refine ⟨t₀ + j * Δ, ⟨?_, ?_⟩, ?_⟩
      · have : (1 : ℝ) ≤ j := by exact_mod_cast hj0
        nlinarith
      · have : (j : ℝ) ≤ ⌈T / Δ⌉₊ := by exact_mod_cast (show j ≤ ⌈T / Δ⌉₊ by omega)
        nlinarith
      · rw [period_eq_iff hΔ]; push_cast; constructor <;> linarith
  refine ⟨blocks n f p, t₀ + Δ - ε, ?_⟩
  rw [← card_filter_val_lt]
  congr 1
  ext s
  simp only [affected, mem_filter, mem_univ, true_and, blocks_faulty_iff hf]
  constructor
  · rintro ⟨τ, -, h, -⟩; exact h
  · intro hs
    obtain ⟨τ, hτ, hper⟩ := hmeet (s.val / f) ((Nat.div_lt_iff_lt_mul hf).2 hs)
    exact ⟨τ, hτ, hs, hper.symm⟩

end Schedule

/-- `MaxB̃(t, t+T)` (Definition 9) is the maximum, over schedules and start times, of `|B̃[t, t+T]|`.
**Lemma 6, corrected**: it equals `min n ((⌈T/Δ⌉ + 1) f)` (the paper omits the `min n`). -/
theorem lemma6 {n f : ℕ} (hf : 0 < f) {t₀ Δ T : ℝ} (hΔ : 0 < Δ) (hT : 0 ≤ T) :
    IsGreatest {c | ∃ (S : Schedule n f) (t : ℝ), c = (S.affected t₀ Δ t (t + T)).card}
      (min n ((⌈T / Δ⌉₊ + 1) * f)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨S, t, h⟩ := Schedule.exists_card_affected_eq (n := n) hf (t₀ := t₀) hΔ hT
    exact ⟨S, t, h.symm⟩
  · rintro c ⟨S, t, rfl⟩
    exact le_min ((card_le_univ _).trans (by simp)) (S.card_affected_le hΔ hT t)

/-- **Lemma 6 as stated is false**: "if `δ ≤ Δ < 3δ` and `T ≥ δ` then `MaxB̃(t, t+T) = (⌈T/Δ⌉+1) f`"
fails as soon as `(⌈T/Δ⌉+1) f > n`, e.g. for `n = 6 = 5f + 1`, `f = 1`, `δ = Δ = 1`, `T = 10`: at most
`6` servers exist, while the formula gives `11`. -/
theorem lemma6_false : ¬ ∀ (n f : ℕ) (t₀ δ Δ T : ℝ), 0 < f → 0 < δ → δ ≤ Δ → Δ < 3 * δ → δ ≤ T →
    IsGreatest {c | ∃ (S : Schedule n f) (t : ℝ), c = (S.affected t₀ Δ t (t + T)).card}
      ((⌈T / Δ⌉₊ + 1) * f) := by
  intro h
  obtain ⟨⟨S, t, hc⟩, -⟩ := h 6 1 0 1 1 10 one_pos one_pos le_rfl (by norm_num) (by norm_num)
  have h1 : (S.affected 0 1 t (t + 10)).card ≤ 6 := (card_le_univ _).trans (by simp)
  have h2 : ⌈(10 : ℝ) / 1⌉₊ = 10 := by norm_num
  rw [h2] at hc
  omega

/-- **Lemma 7**: if `kΔ ≥ 2δ` (`k ∈ {1, 2}`) and `n ≥ (k+3) f + 1`, then for every schedule and every
read `[t, t+2δ]`, the servers never affected during `[t, t+δ]` (which the paper counts as the servers
that surely reply correctly, `C̃oR(t, t+2δ)`) number at least `#reply_CAM = (k+1) f + 1`, and more
than the servers affected during `[t, t+2δ]`. -/
theorem lemma7 {n f k : ℕ} (hk : k = 1 ∨ k = 2) {t₀ δ Δ : ℝ} (hδ : 0 < δ) (hkΔ : 2 * δ ≤ k * Δ)
    (hn : (k + 3) * f + 1 ≤ n) (S : Schedule n f) (t : ℝ) :
    (k + 1) * f + 1 ≤ n - (S.affected t₀ Δ t (t + δ)).card ∧
      (S.affected t₀ Δ t (t + 2 * δ)).card < n - (S.affected t₀ Δ t (t + δ)).card := by
  have hΔ' : δ ≤ Δ := by
    rcases hk with rfl | rfl <;> push_cast at hkΔ <;> linarith
  have hΔ : 0 < Δ := by linarith
  have h1 : ⌈δ / Δ⌉₊ ≤ 1 := Nat.ceil_le.2 (by rw [div_le_iff₀ hΔ]; push_cast; linarith)
  have h2 : ⌈2 * δ / Δ⌉₊ ≤ k := Nat.ceil_le.2 (by rw [div_le_iff₀ hΔ]; linarith)
  have a1 := S.card_affected_le (t₀ := t₀) hΔ hδ.le t
  have a2 := S.card_affected_le (t₀ := t₀) hΔ (by linarith : (0 : ℝ) ≤ 2 * δ) t
  have b1 : (⌈δ / Δ⌉₊ + 1) * f ≤ 2 * f := Nat.mul_le_mul_right _ (by omega)
  have b2 : (⌈2 * δ / Δ⌉₊ + 1) * f ≤ (k + 1) * f := Nat.mul_le_mul_right _ (by omega)
  constructor
  · have : (k + 3) * f = (k + 1) * f + 2 * f := by ring
    omega
  · have : (k + 3) * f = (k + 1) * f + 2 * f := by ring
    omega

end Podc.MobileByzantineStorage
