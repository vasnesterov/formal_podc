import Papers.PODC2014.CongestedCliquePower.CyclesLemma18
import Papers.PODC2014.CongestedCliquePower.Lemma13

/-!
# Theorem 19: `C_ℓ`-detection needs `Ω(ex(n, C_ℓ) / (n b))` rounds

Drucker–Kuhn–Oshman, PODC 2014, Theorem 19: for every fixed `ℓ ≥ 4`, `C_ℓ`-subgraph detection requires
`Ω(ex(n, C_ℓ) / (n b))` rounds, both in CLIQUE-BCAST_{n,b} and in CONGEST-UCAST_{n,b}.

Proof: with `N = 2⌊n/ℓ⌋`, the (corrected) Lemma 18 gives an `N/n`-sparse `(C_ℓ, F)`-lower bound graph on `n`
nodes, where `F = K_{N/2,N/2}` for odd `ℓ` and `F` is an extremal `C_ℓ`-free graph for even `ℓ`. In both cases
`ex(n, C_ℓ) ≤ 2ℓ² |E_F|` (`ex(n, C_ℓ) ≤ n²/2` for odd `ℓ`; for even `ℓ` by the monotonicity of
`ex(n, H) / C(n, 2)`). Lemma 13 then gives `ex(n, C_ℓ) ≤ 2ℓ² (T n b + 2)` (BCAST) and
`ex(n, C_ℓ) ≤ 2ℓ² (2 T N b + 2)`, `N ≤ 2n/ℓ` (CONGEST).
-/

namespace Podc.CongestedCliquePower

open SimpleGraph Cslib.CongestedClique

lemma extremalNumber_le_choose_two {W : Type*} (H : SimpleGraph W) (n : ℕ) :
    extremalNumber n H ≤ n.choose 2 := by
  classical
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ _
  exact card_edgeFinset_le_card_choose_two

open Classical in
/-- The lower-bound graph used for Theorem 19, with `ex(n, C_ℓ) ≤ 2ℓ² |E_F|`. -/
theorem exists_cycle_lowerBoundGraph {ℓ n : ℕ} (hℓ : 4 ≤ ℓ) (hn : ℓ ≤ n) :
    ∃ (F : SimpleGraph (Fin (2 * (n / ℓ)))) (_ : DecidableRel F.Adj) (G' : SimpleGraph (Fin n))
      (L : LowerBoundGraph (cycleGraph ℓ) F G'), L.IsSparse ((2 * (n / ℓ) : ℕ) / (n : ℝ)) ∧
      extremalNumber n (cycleGraph ℓ) ≤ 2 * ℓ ^ 2 * Fintype.card F.edgeSet := by
  classical
  set q := n / ℓ with hq
  have hq1 : 1 ≤ q := (Nat.one_le_div_iff (by omega)).2 hn
  have hnq : n ≤ 2 * ℓ * q := by
    have := Nat.lt_div_mul_add (a := n) (b := ℓ) (by omega)
    nlinarith
  have hqn : q * ℓ ≤ n := Nat.div_mul_le_self n ℓ
  have hN : Even (2 * q) := even_two_mul q
  have hNn : ℓ * (2 * q / 2) ≤ n := by
    rw [Nat.mul_div_cancel_left q (by norm_num), mul_comm]; exact Nat.div_mul_le_self n ℓ
  have hch : n.choose 2 ≤ 2 * ℓ ^ 2 * (q * q) := by
    have h1 : n.choose 2 * 2 ≤ n * n := by
      rw [Nat.choose_two_right]
      have := Nat.div_mul_le_self (n * (n - 1)) 2
      have : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le n 1)
      omega
    have h2 : n * n ≤ (2 * ℓ * q) * (2 * ℓ * q) := Nat.mul_le_mul hnq hnq
    nlinarith
  rcases Nat.even_or_odd ℓ with he | ho
  · obtain ⟨F, _, hext, hcard, G', L, hS⟩ := lemma_18_even hℓ he hN hNn
    refine ⟨F, inferInstance, G', L, hS, ?_⟩
    rw [← edgeFinset_card, hcard]
    -- `ex(n)/C(n,2) ≤ ex(N)/C(N,2)` and `C(n,2) ≤ 2ℓ² C(N,2)`
    have hanti := antitoneOn_extremalNumber_div_choose_two (cycleGraph ℓ)
      (Set.mem_Ici.2 (by omega)) (Set.mem_Ici.2 (by omega)) (show 2 * q ≤ n by nlinarith)
    simp only at hanti
    have hcN : q * q ≤ (2 * q).choose 2 := by
      rw [Nat.choose_two_right]
      apply (Nat.le_div_iff_mul_le (by norm_num)).2
      have : 2 * q - 1 ≥ q := by omega
      nlinarith
    have hpos : (0 : ℝ) < (2 * q).choose 2 := by exact_mod_cast Nat.choose_pos (by omega)
    have hposn : (0 : ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos (by omega)
    rw [div_le_div_iff₀ hposn hpos] at hanti
    have hch' : (n.choose 2 : ℝ) ≤ 2 * ℓ ^ 2 * (2 * q).choose 2 := by
      have := hch.trans (Nat.mul_le_mul_left _ hcN)
      exact_mod_cast this
    have : (extremalNumber n (cycleGraph ℓ) : ℝ) ≤
        2 * ℓ ^ 2 * extremalNumber (2 * q) (cycleGraph ℓ) := by
      have h0 : (0 : ℝ) ≤ extremalNumber (2 * q) (cycleGraph ℓ) := Nat.cast_nonneg _
      by_contra hc
      push Not at hc
      nlinarith
    exact_mod_cast this
  · obtain ⟨_, hcard, G', L, hS⟩ := lemma_18_odd hℓ ho hN hNn
    refine ⟨halfBipartite (2 * q), inferInstance, G', L, hS, ?_⟩
    rw [← edgeFinset_card, hcard, Nat.mul_div_cancel_left q (by norm_num)]
    exact (extremalNumber_le_choose_two _ n).trans hch

/-- **Theorem 19 (CLIQUE-BCAST, deterministic).** For `ℓ ≥ 4` and `n ≥ ℓ`, every deterministic
CLIQUE-BCAST algorithm on `n` nodes with `b`-bit messages deciding `C_ℓ`-freeness in `T` rounds satisfies
`ex(n, C_ℓ) ≤ 2ℓ² (T · n · b + 2)`, i.e. `T = Ω(ex(n, C_ℓ) / (n b))` for fixed `ℓ`. -/
theorem theorem_19_bcast {ℓ n : ℕ} (hℓ : 4 ≤ ℓ) (hn : ℓ ≤ n) {σ : Type} {b : ℕ}
    (A : Bcast.Algorithm (Fin n) (Fin n → Bool) σ b) (T : ℕ)
    (hA : ∀ G : SimpleGraph (Fin n), A.Accepts (adjInput G) T ↔ (cycleGraph ℓ).Free G) :
    extremalNumber n (cycleGraph ℓ) ≤ 2 * ℓ ^ 2 * (T * (n * b) + 2) := by
  classical
  obtain ⟨F, _, G', L, -, hex⟩ := exists_cycle_lowerBoundGraph hℓ hn
  have h := L.lemma_13_bcast A T hA
  rw [Fintype.card_fin] at h
  exact hex.trans (Nat.mul_le_mul_left _ (by convert h))

/-- **Theorem 19 (CONGEST-UCAST, deterministic).** For `ℓ ≥ 4` and `n ≥ ℓ`, every deterministic CONGEST
algorithm (network = input graph, `B`-bit messages) deciding `C_ℓ`-freeness in `T` rounds satisfies
`ex(n, C_ℓ) ≤ 2ℓ² (2 · T · N · B + 2)` with `N = 2⌊n/ℓ⌋ ≤ 2n/ℓ`, i.e. `T = Ω(ex(n, C_ℓ) / (n B))`. -/
theorem theorem_19_congest {ℓ n : ℕ} (hℓ : 4 ≤ ℓ) (hn : ℓ ≤ n) {σ : Type} {B : ℕ}
    (A : Cslib.Congest.Algorithm (Fin n) (Fin n → Bool) σ B) (T : ℕ)
    (hA : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      A.Accepts G (fun v w => decide (G.Adj v w)) T ↔ (cycleGraph ℓ).Free G) :
    (extremalNumber n (cycleGraph ℓ) : ℝ) ≤ 2 * ℓ ^ 2 * (2 * T * (2 * (n / ℓ) : ℕ) * B + 2) := by
  classical
  obtain ⟨F, _, G', L, hS, hex⟩ := exists_cycle_lowerBoundGraph hℓ hn
  have h := L.lemma_13_congest_sparse A T hA _ (by convert hS)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Fintype.card_fin] at h
  have e : (2 : ℝ) * T * (((2 * (n / ℓ) : ℕ) : ℝ) / n) * n * B = 2 * T * (2 * (n / ℓ) : ℕ) * B := by
    field_simp
  rw [e] at h
  have hex' : (extremalNumber n (cycleGraph ℓ) : ℝ) ≤ 2 * ℓ ^ 2 * Fintype.card F.edgeSet := by
    exact_mod_cast hex
  have hc : (Fintype.card F.edgeSet : ℝ) ≤ 2 * T * (2 * (n / ℓ) : ℕ) * B + 2 := by
    convert h using 2
  calc _ ≤ _ := hex'
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)

end Podc.CongestedCliquePower
