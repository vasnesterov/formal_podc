import Papers.PODC2021.UltraSparseEmulators.Analysis

/-!
# Main results of Section 2: Lemmas 2.3, 2.4, Corollaries 2.13 and 2.14

Elkin, Matar. *Ultra-Sparse Near-Additive Emulators.* PODC 2021 (arXiv:2106.01036v1).

Algorithm 1 is run with the parameters of Section 2.1.2: `deg_i = n^{2^i/κ}`,
`δ_i = (1/ε)^i + 2R_i`, phases `0, …, ℓ` with `ℓ = ⌈log₂((κ+1)/2)⌉`, and **any** order of
consideration in each phase (`ord i` lists all vertices). `κ ≥ 2` is an integer, as in the paper
(`κ = 1, 2, …`); for non-integer `κ` the bound `ℓ ≤ log₂ κ` used in Section 2.2.4 fails
(`not_numPhases_le_logb`).
-/

namespace Podc.UltraSparseEmulators

open SimpleGraph Finset Real
open scoped Classical

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- The emulator computed by Algorithm 1 with the parameters of Section 2.1.2, for accuracy `ε`,
sparsity parameter `κ` and orders `ord`. -/
noncomputable def ultraSparseEmulator (ε : ℝ) (κ : ℕ) (ord : ℕ → List V) : SimpleGraph V :=
  emulator G (δ ε) (deg κ (Fintype.card V)) ord (numPhases κ)

variable {G} {ε : ℝ} {κ : ℕ} {ord : ℕ → List V}

/-- **Lemma 2.3.** `|P_i| ≤ n^{1 - (2^i - 1)/κ}`. -/
theorem lemma_2_3 (hε : 0 < ε) (hκ : 2 ≤ κ) (hord : ∀ i x, x ∈ ord i)
    (hn : 1 ≤ Fintype.card V) (i : ℕ) :
    ((centers G (δ ε) (deg κ (Fintype.card V)) ord i).card : ℝ) ≤
      (Fintype.card V : ℝ) ^ (1 - ((2 : ℝ) ^ i - 1) / κ) := by
  have hκ0 : (0 : ℝ) < κ := by exact_mod_cast (show 0 < κ by omega)
  induction i with
  | zero => simp [centers]
  | succ i ih =>
    exact lemma_2_3_step hκ0 hn (Nat.cast_nonneg _)
      (card_centers_succ (G := G) (dg := deg κ (Fintype.card V)) hε hord i) ih

/-- Eq. (1): `|P_ℓ| ≤ deg_ℓ`, so the last phase forms no superclusters. -/
theorem eq_1_centers (hε : 0 < ε) (hκ : 2 ≤ κ) (hord : ∀ i x, x ∈ ord i) :
    ((centers G (δ ε) (deg κ (Fintype.card V)) ord (numPhases κ)).card : ℝ) ≤
      deg κ (Fintype.card V) (numPhases κ) := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hn
  · have : IsEmpty V := Fintype.card_eq_zero_iff.1 h0
    simp only [Finset.eq_empty_of_isEmpty, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact (lemma_2_3 hε hκ hord hn _).trans (eq_1 (by exact_mod_cast hκ) hn)

/-- **Lemma 2.4.** The emulator has at most `n^{1+1/κ}` edges. -/
theorem lemma_2_4 (hε : 0 < ε) (hκ : 2 ≤ κ) (hord : ∀ i x, x ∈ ord i) :
    ((ultraSparseEmulator G ε κ ord).edgeFinset.card : ℝ) ≤
      (Fintype.card V : ℝ) ^ (1 + 1 / (κ : ℝ)) := by
  have hκ0 : (0 : ℝ) < κ := by exact_mod_cast (show 0 < κ by omega)
  have hsub : (ultraSparseEmulator G ε κ ord).edgeFinset ⊆
      (Ph G ε (deg κ (Fintype.card V)) ord (numPhases κ)).E := by
    intro e he
    rw [mem_edgeFinset, ultraSparseEmulator, emulator, edgeSet_fromEdgeSet] at he
    exact he.1
  have h1 : ((ultraSparseEmulator G ε κ ord).edgeFinset.card : ℝ) ≤
      (Ph G ε (deg κ (Fintype.card V)) ord (numPhases κ)).E.card := by
    exact_mod_cast card_le_card hsub
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hn
  · have : IsEmpty V := Fintype.card_eq_zero_iff.1 h0
    have : (Ph G ε (deg κ (Fintype.card V)) ord (numPhases κ)).E = ∅ :=
      Finset.eq_empty_of_forall_notMem fun e => Sym2.inductionOn e fun a => isEmptyElim a
    rw [this] at h1
    simp only [card_empty, Nat.cast_zero] at h1
    exact h1.trans (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · have h2 := card_edges_le (G := G) (ord := ord) hε hord (fun i => one_le_deg hκ0 hn i)
      (fun i => deg_succ _ i) (numPhases κ)
    rw [deg_zero] at h2
    have hn0 : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    refine h1.trans (h2.trans (le_of_eq ?_))
    rw [Real.rpow_add hn0, Real.rpow_one, mul_comm]

/-- **Corollary 2.11** with the paper's parameters: the output is an `(α_ℓ, β_ℓ)`-emulator. -/
theorem corollary_2_11 (hε0 : 0 < ε) (hε1 : ε < 1) (hκ : 2 ≤ κ) (hord : ∀ i x, x ∈ ord i) :
    G.IsEmulator (ultraSparseEmulator G ε κ ord) G.distW (alpha ε (numPhases κ))
      (beta ε (numPhases κ)) :=
  (hierarchy (G := G) (dg := deg κ (Fintype.card V)) hε0 hord
    (eq_1_centers hε0 hκ hord)).isEmulator hε0 hε1

/-- **Corollary 2.13** (with Lemma 2.4). For `0 < ε ≤ 1/10`, integer `κ ≥ 2` and any order of
consideration, Algorithm 1 outputs a `(1 + 34εℓ, 30(1/ε)^{ℓ-1})`-emulator with at most
`n^{1+1/κ}` edges, `ℓ = ⌈log₂((κ+1)/2)⌉`. -/
theorem corollary_2_13 (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) (hκ : 2 ≤ κ) (hord : ∀ i x, x ∈ ord i) :
    ((ultraSparseEmulator G ε κ ord).edgeFinset.card : ℝ) ≤
        (Fintype.card V : ℝ) ^ (1 + 1 / (κ : ℝ)) ∧
      G.IsEmulator (ultraSparseEmulator G ε κ ord) G.distW (1 + 34 * ε * numPhases κ)
        (30 * (1 / ε) ^ (numPhases κ - 1)) :=
  ⟨lemma_2_4 hε0 hκ hord,
    (corollary_2_11 hε0 (by linarith) hκ hord).mono (eq_13 hε0 hε _)
      (eq_12 hε0 hε (one_le_numPhases (by exact_mod_cast hκ)))⟩

/-- **Corollary 2.14.** For every `0 < ε < 1` and integer `κ ≥ 2`, every `n`-vertex graph `G` has a
`(1 + ε, β)`-emulator with at most `n^{1+1/κ}` edges, `β = 30 (34 log₂ κ / ε)^{log₂ κ - 1}`;
it is computed by Algorithm 1 run with `ε/(34ℓ)` (in any order of consideration). -/
theorem corollary_2_14 (hε0 : 0 < ε) (hε1 : ε < 1) (hκ : 2 ≤ κ) (hord : ∀ i x, x ∈ ord i) :
    ((ultraSparseEmulator G (ε / (34 * numPhases κ)) κ ord).edgeFinset.card : ℝ) ≤
        (Fintype.card V : ℝ) ^ (1 + 1 / (κ : ℝ)) ∧
      G.IsEmulator (ultraSparseEmulator G (ε / (34 * numPhases κ)) κ ord) G.distW (1 + ε)
        (30 * (34 * logb 2 κ / ε) ^ (logb 2 κ - 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := rescale_natCast hκ hε0 hε1
  obtain ⟨hs, he⟩ := corollary_2_13 (G := G) h1 h2 hκ hord
  exact ⟨hs, he.mono h3.le h4⟩

/-- Corollary 2.14, existential form. -/
theorem exists_emulator (hε0 : 0 < ε) (hε1 : ε < 1) (hκ : 2 ≤ κ) :
    ∃ H : SimpleGraph V, (H.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ (1 + 1 / (κ : ℝ)) ∧
      G.IsEmulator H G.distW (1 + ε) (30 * (34 * logb 2 κ / ε) ^ (logb 2 κ - 1)) :=
  ⟨_, corollary_2_14 (G := G) (ord := fun _ => Finset.univ.toList) hε0 hε1 hκ
    (fun _ x => Finset.mem_toList.2 (Finset.mem_univ x))⟩

end Podc.UltraSparseEmulators
