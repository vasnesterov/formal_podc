import Papers.PODC2016.StorageCostLowerBounds.Theorem41

/-!
# Theorem 4.1 in logarithmic form and Corollary 4.2 (repaired)

`theorem41`: the paper's inequality
`∑_{𝒩} log₂|S_i| + max_{𝒩} log₂|S_i| ≥ log₂|V| + log₂(|V| - 1) - log₂(n - f)`
for every `𝒩` of `n - f` servers, under the hypotheses of `theorem41_count` (with `ReaderQuiet`).

`corollary42`: `MaxStorage ≥ c / (n - f + 1)` and `TotalStorage ≥ n c / (n - f + 1)` with
`c = log₂|V| + log₂(|V| - 1) - log₂(n - f)`. The total-storage bound needs `f ≥ 1` (the paper
assumes `f ≥ 2`); we prove it for `1 ≤ f < n`.
-/

namespace Podc.StorageCost

open Cslib.ChannelFailures Cslib.SharedMemory

variable {n : ℕ} {V : Type} {v₀ : V} {M L : Type}
variable {A : Algorithm (Node n) (register V v₀) M L}

lemma one_le_card_of_stateBound {S : Fin n → Finset L} (hS : StateBound A S) (i : Fin n) :
    1 ≤ (S i).card :=
  Finset.card_pos.2 ⟨_, hS [] (by simp) i⟩

/-- **Theorem 4.1** (logarithmic form, repaired with `ReaderQuiet`). -/
theorem theorem41 [Fintype V] {f : ℕ} (hReg : IsRegular A) (hLive : Live A f)
    (hNG : NoGossip A) (hQ : ReaderQuiet A) {S : Fin n → Finset L} (hS : StateBound A S)
    (hf : f < n) (𝒩 : Finset (Fin n)) (h𝒩 : 𝒩.card = n - f) :
    Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) - Real.logb 2 (n - f : ℕ) ≤
      ∑ i ∈ 𝒩, Real.logb 2 (S i).card + ⨆ i : 𝒩, Real.logb 2 (S i).card := by
  classical
  have hne : 𝒩.Nonempty := by rw [← Finset.card_pos, h𝒩]; omega
  have hcount := theorem41_count (A := A) (𝒩 := 𝒩) hReg hLive hNG hQ hS (by omega) hne
  have hS1 := one_le_card_of_stateBound hS
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image 𝒩 (fun i => (S i).card) hne
  have hsum : ∑ i ∈ 𝒩, (S i).card ≤ (n - f) * (S i₀).card := by
    calc ∑ i ∈ 𝒩, (S i).card ≤ ∑ _i ∈ 𝒩, (S i₀).card := Finset.sum_le_sum hmax
      _ = (n - f) * (S i₀).card := by simp [h𝒩]
  have hbdd : BddAbove (Set.range fun i : 𝒩 => Real.logb 2 (S i).card) :=
    (Set.finite_range _).bddAbove
  have hle : Real.logb 2 (S i₀).card ≤ ⨆ i : 𝒩, Real.logb 2 (S i).card :=
    le_ciSup (f := fun i : 𝒩 => Real.logb 2 (S i).card) hbdd ⟨i₀, hi₀⟩
  have hpos : ∀ i, (0 : ℝ) < (S i).card := fun i => by exact_mod_cast hS1 i
  have hprod : Real.logb 2 (∏ i ∈ 𝒩, ((S i).card : ℝ)) = ∑ i ∈ 𝒩, Real.logb 2 (S i).card :=
    Real.logb_prod _ _ (fun i _ => (hpos i).ne')
  have hsum_nonneg : 0 ≤ ∑ i ∈ 𝒩, Real.logb 2 (S i).card :=
    Finset.sum_nonneg fun i _ => Real.logb_nonneg (by norm_num) (by exact_mod_cast hS1 i)
  have hsup_nonneg : 0 ≤ ⨆ i : 𝒩, Real.logb 2 (S i).card :=
    (Real.logb_nonneg (by norm_num) (by exact_mod_cast hS1 i₀)).trans hle
  have hnf : (1 : ℝ) ≤ (n - f : ℕ) := by exact_mod_cast (show 1 ≤ n - f by omega)
  have hlnf : 0 ≤ Real.logb 2 (n - f : ℕ) := Real.logb_nonneg (by norm_num) hnf
  have hV1 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨v₀⟩
  rcases Nat.lt_or_ge (Fintype.card V) 2 with hV | hV
  · have : Fintype.card V = 1 := by omega
    rw [this]; simp only [Nat.cast_one, Real.logb_one, sub_self, Real.logb_zero, zero_add,
      zero_sub]
    linarith
  · -- cast the counting bound to the reals and take logarithms
    have hreal : ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) ≤
        (∏ i ∈ 𝒩, ((S i).card : ℝ)) * (((n - f : ℕ) : ℝ) * (S i₀).card) := by
      have h := hcount.trans (Nat.mul_le_mul_left _ hsum)
      have h' : ((Fintype.card V * (Fintype.card V - 1) : ℕ) : ℝ) ≤
          ((∏ i ∈ 𝒩, (S i).card) * ((n - f) * (S i₀).card) : ℕ) := by exact_mod_cast h
      push_cast [Nat.cast_sub (by omega : 1 ≤ Fintype.card V)] at h'
      exact h'
    have hVpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
    have hV1pos : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := by
      have : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
      linarith
    have hP : (0 : ℝ) < ∏ i ∈ 𝒩, ((S i).card : ℝ) := Finset.prod_pos fun i _ => hpos i
    have hl := Real.logb_le_logb_of_le (b := 2) (by norm_num) (mul_pos hVpos hV1pos) hreal
    have hnf0 : ((n - f : ℕ) : ℝ) ≠ 0 := ne_of_gt (by linarith)
    rw [Real.logb_mul hVpos.ne' hV1pos.ne', Real.logb_mul hP.ne' (mul_ne_zero hnf0 (hpos i₀).ne'),
      Real.logb_mul hnf0 (hpos i₀).ne', hprod] at hl
    linarith

/-- Selecting the `k` servers with the smallest storage. -/
lemma exists_smallest {ι : Type} [DecidableEq ι] (g : ι → ℝ) :
    ∀ (s : Finset ι) (k : ℕ), k ≤ s.card →
      ∃ t ⊆ s, t.card = k ∧ ∀ i ∈ t, ∀ j ∈ s, j ∉ t → g i ≤ g j := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro k hk
    rcases Nat.lt_or_ge k s.card with hlt | hge
    · have hne : s.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨y, hy, hymax⟩ := Finset.exists_max_image s g hne
      obtain ⟨t, hts, htc, ht⟩ := ih (s.erase y) (Finset.erase_ssubset hy) k
        (by rw [Finset.card_erase_of_mem hy]; omega)
      refine ⟨t, hts.trans (Finset.erase_subset _ _), htc, fun i hi j hj hjt => ?_⟩
      by_cases hjy : j = y
      · subst hjy; exact hymax i (Finset.mem_of_mem_erase (hts hi))
      · exact ht i hi j (Finset.mem_erase.2 ⟨hjy, hj⟩) hjt
    · exact ⟨s, subset_rfl, by omega, fun i _ j hj hjt => absurd hj hjt⟩

/-- **Corollary 4.2** (repaired with `ReaderQuiet`; `1 ≤ f < n`). -/
theorem corollary42 [Fintype V] {f : ℕ} (hReg : IsRegular A) (hLive : Live A f)
    (hNG : NoGossip A) (hQ : ReaderQuiet A) {S : Fin n → Finset L} (hS : StateBound A S)
    (hf1 : 1 ≤ f) (hf : f < n) :
    (Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) -
        Real.logb 2 (n - f : ℕ)) / ((n - f : ℕ) + 1) ≤ maxStorage S ∧
    n * (Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) -
        Real.logb 2 (n - f : ℕ)) / ((n - f : ℕ) + 1) ≤ totalStorage S := by
  classical
  set c := Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) -
    Real.logb 2 (n - f : ℕ)
  set g : Fin n → ℝ := fun i => Real.logb 2 (S i).card
  obtain ⟨𝒩, -, h𝒩, hsmall⟩ := exists_smallest g Finset.univ (n - f) (by simp)
  have hne : 𝒩.Nonempty := by rw [← Finset.card_pos, h𝒩]; omega
  have hth := theorem41 hReg hLive hNG hQ hS hf 𝒩 h𝒩
  set a := ⨆ i : 𝒩, g i
  have hbdd : BddAbove (Set.range fun i : 𝒩 => g i) := (Set.finite_range _).bddAbove
  have hga : ∀ i ∈ 𝒩, g i ≤ a := fun i hi => le_ciSup (f := fun i : 𝒩 => g i) hbdd ⟨i, hi⟩
  have hNonempty : Nonempty 𝒩 := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hag : ∀ j, j ∉ 𝒩 → a ≤ g j := fun j hj =>
    ciSup_le fun i => hsmall i i.2 j (Finset.mem_univ _) hj
  have hsumN : ∑ i ∈ 𝒩, g i ≤ (n - f : ℕ) * a := by
    calc ∑ i ∈ 𝒩, g i ≤ ∑ _i ∈ 𝒩, a := Finset.sum_le_sum hga
      _ = (n - f : ℕ) * a := by simp [h𝒩]
  have hc : c ≤ ((n - f : ℕ) + 1) * a := by
    have : c ≤ ∑ i ∈ 𝒩, g i + a := hth
    nlinarith
  have hpos : (0 : ℝ) < (n - f : ℕ) + 1 := by positivity
  have ha : c / ((n - f : ℕ) + 1) ≤ a := by rw [div_le_iff₀ hpos]; linarith
  have hS1 := one_le_card_of_stateBound hS
  have hgmax : ∀ i, g i ≤ maxStorage S := fun i =>
    le_ciSup (f := g) (Set.finite_range _).bddAbove i
  refine ⟨ha.trans (ciSup_le fun i => hgmax i), ?_⟩
  · -- the total storage
    have hcompl : ∑ j ∈ 𝒩ᶜ, g j ≥ f * a := by
      have : ∑ _j ∈ 𝒩ᶜ, a ≤ ∑ j ∈ 𝒩ᶜ, g j :=
        Finset.sum_le_sum fun j hj => hag j (Finset.mem_compl.1 hj)
      have hcard : (𝒩ᶜ).card = f := by
        rw [Finset.card_compl, Fintype.card_fin, h𝒩]; omega
      simpa [hcard] using this
    have htot : totalStorage S = ∑ i ∈ 𝒩, g i + ∑ j ∈ 𝒩ᶜ, g j := by
      simp only [totalStorage]; rw [Finset.sum_add_sum_compl]
    have hf1' : (1 : ℝ) ≤ f := by exact_mod_cast hf1
    have hnf : ((n - f : ℕ) : ℝ) = n - f := by rw [Nat.cast_sub hf.le]
    rw [htot, div_le_iff₀ hpos]
    have h1 : c ≤ ∑ i ∈ 𝒩, g i + a := hth
    have h2 : (f - 1) * c ≤ (f - 1) * (((n - f : ℕ) + 1) * a) :=
      mul_le_mul_of_nonneg_left hc (by linarith)
    rw [hnf] at h2 ⊢
    nlinarith

end Podc.StorageCost
