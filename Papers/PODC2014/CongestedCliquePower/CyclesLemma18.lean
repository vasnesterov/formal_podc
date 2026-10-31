import Papers.PODC2014.CongestedCliquePower.CyclesConstruction

/-!
# Lemma 18 of Drucker–Kuhn–Oshman (PODC 2014): `(C_ℓ, F)`-lower bound graphs

* `Lemma18Concl ℓ N n` / `Lemma18Statement` — the paper's Lemma 18 as stated ("for some extremal
  `C_ℓ`-free graph `F` on `N` vertices there is a `(C_ℓ, F)`-lower bound graph on `n` vertices").
  It is false in general (`CyclesCounterexample.lean`: `ℓ = 5`, `N = 4`), because for odd `ℓ`
  the graph `K_{N/2,N/2}` used in the proof is extremal only for large `N`.
* `lemma_18` — the corrected statement, which is what the proof actually shows: for `ℓ ≥ 4`, even
  `N`, `n ≥ ℓ·N/2` and **any** `C_ℓ`-free `F` on `Fin N` whose edges (when `ℓ` is odd) all join
  `{i < N/2}` to `{i ≥ N/2}`, the paper's graph `G'` (relabelled by `Fin n`) is a
  `(C_ℓ, F)`-lower bound graph, and it is `N/n`-sparse.
* `lemma_18_odd` — `ℓ` odd, `F = K_{N/2,N/2}` (`N²/4` edges, `card_edgeFinset_halfBipartite`).
* `lemma_18_even` — `ℓ` even, `F` extremal `C_ℓ`-free (`extremalNumber N C_ℓ` edges); in particular
  the paper's statement holds for even `ℓ` (`lemma18Concl_of_even`).
-/

namespace Podc.CongestedCliquePower

open SimpleGraph CycleLB
open scoped Finset

/-- The paper's Lemma 18, conclusion: for some extremal `C_ℓ`-free graph `F` on `N` vertices there
exists a `(C_ℓ, F)`-lower bound graph on `n` vertices. -/
def Lemma18Concl (ℓ N n : ℕ) : Prop :=
  ∃ (F : SimpleGraph (Fin N)) (_ : DecidableRel F.Adj), F.IsExtremal (cycleGraph ℓ).Free ∧
    ∃ G' : SimpleGraph (Fin n), Nonempty (LowerBoundGraph (cycleGraph ℓ) F G')

/-- **Lemma 18** of the paper, as stated: "Fix `ℓ ≥ 4`, let `N` be an even integer, and let
`n ≥ ℓ · (N/2)`. Then for some extremal `C_ℓ`-free graph `F` on `N` vertices, there exists a
`(C_ℓ, F)`-lower bound graph on `n` vertices." (False: `not_lemma18Statement`.) -/
def Lemma18Statement : Prop :=
  ∀ ℓ N n : ℕ, 4 ≤ ℓ → Even N → ℓ * (N / 2) ≤ n → Lemma18Concl ℓ N n

/-- The path lengths of the proof of Lemma 18: `|P_i| = ⌊ℓ/2⌋ - 1` for `i ≤ N/2` and
`⌈ℓ/2⌉ - 1` for `i > N/2` (with `0`-based indices: `i < N/2`). -/
def pathLen (ℓ N : ℕ) (i : Fin N) : ℕ := if (i : ℕ) < N / 2 then ℓ / 2 - 1 else (ℓ + 1) / 2 - 1

lemma card_PV_pathLen {ℓ N : ℕ} (hℓ : 2 ≤ ℓ) (hN : Even N) :
    Fintype.card (PV (pathLen ℓ N)) = ℓ * (N / 2) := by
  rw [card_PV]
  obtain ⟨M, rfl⟩ := hN
  have hM : (M + M) / 2 = M := by omega
  simp only [pathLen]
  rw [Fin.sum_univ_eq_sum_range (fun k => (if k < (M + M) / 2 then ℓ / 2 - 1 else (ℓ + 1) / 2 - 1) + 1),
    Finset.sum_range_add, hM]
  have e1 : ∀ k ∈ Finset.range M,
      (if k < M then ℓ / 2 - 1 else (ℓ + 1) / 2 - 1) + 1 = ℓ / 2 := by
    intro k hk
    simp only [Finset.mem_range] at hk
    simp only [hk, ↓reduceIte]
    omega
  have e2 : ∀ k ∈ Finset.range M,
      (if M + k < M then ℓ / 2 - 1 else (ℓ + 1) / 2 - 1) + 1 = (ℓ + 1) / 2 := by
    intro k _
    simp only [show ¬ (M + k < M) by omega, ↓reduceIte]
    omega
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rcases Nat.even_or_odd' ℓ with ⟨k, rfl | rfl⟩
  · rw [show 2 * k / 2 = k by omega, show (2 * k + 1) / 2 = k by omega]
    ring
  · rw [show (2 * k + 1) / 2 = k by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
    ring

/-- Every vertex of `C_ℓ` has a neighbour. -/
lemma cycleGraph_exists_adj {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (a : Fin ℓ) : ∃ b, (cycleGraph ℓ).Adj a b := by
  have : NeZero ℓ := ⟨by omega⟩
  refine ⟨cyc ℓ ((a : ℕ) + 1 : ℤ), ?_⟩
  have := cyc_adj hℓ (a : ℕ)
  rwa [cyc_natCast] at this

open scoped Classical in
/-- **Lemma 18 (corrected).** Let `ℓ ≥ 4`, `N` even, `n ≥ ℓ · (N/2)`, and let `F` be a `C_ℓ`-free
graph on `Fin N` such that, if `ℓ` is odd, every edge of `F` joins `{i < N/2}` and `{i ≥ N/2}`.
Then there is a `(C_ℓ, F)`-lower bound graph `G'` on `Fin n` (the paper's construction: two copies
of `F` joined by the paths `P_i`, plus isolated vertices) which is `N/n`-sparse (the cut consists
of the last edges of the `N` paths). -/
theorem lemma_18 {ℓ N n : ℕ} (hℓ : 4 ≤ ℓ) (hN : Even N) (hn : ℓ * (N / 2) ≤ n)
    (F : SimpleGraph (Fin N)) (hF : (cycleGraph ℓ).Free F)
    (hhalf : Odd ℓ → ∀ i j, F.Adj i j → ((i : ℕ) < N / 2 ↔ N / 2 ≤ (j : ℕ))) :
    ∃ (G' : SimpleGraph (Fin n)) (L : LowerBoundGraph (cycleGraph ℓ) F G'),
      L.IsSparse ((N : ℝ) / n) := by
  set len := pathLen ℓ N with hlen
  have h1 : ∀ i, 1 ≤ len i := by
    intro i; simp only [hlen, pathLen]; split_ifs <;> omega
  have h2 : ∀ i j, F.Adj i j → len i + len j + 2 = ℓ := by
    intro i j hij
    simp only [hlen, pathLen]
    rcases Nat.even_or_odd' ℓ with ⟨k, hk | hk⟩
    · split_ifs <;> omega
    · have hh := hhalf ⟨k, hk⟩ i j hij
      by_cases hi : (i : ℕ) < N / 2
      · have := hh.1 hi
        simp only [hi, ite_true, show ¬ (j : ℕ) < N / 2 by omega, ite_false]
        omega
      · have : ¬ N / 2 ≤ (j : ℕ) := fun h => hi (hh.2 h)
        simp only [hi, ite_false, show (j : ℕ) < N / 2 by omega, ite_true]
        omega
  have h3 : ∀ i j, i ≠ j → ℓ ≤ len i + len j + 3 := by
    intro i j _
    simp only [hlen, pathLen]
    split_ifs <;> omega
  let L0 := lowerBoundGraph (len := len) (F := F) (by omega) h1 h2 h3 hF
  have hcard : Fintype.card (PV len) ≤ n := by
    rw [hlen, card_PV_pathLen (by omega) hN]; exact hn
  let e : PV len ↪ Fin n := (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb hcard)
  have hH := cycleGraph_exists_adj (ℓ := ℓ) (by omega)
  have hA : ∀ a, decide ((L0.φA a).h < len (L0.φA a).i) = true := by
    intro a
    change decide (0 < len a) = true
    exact decide_eq_true (h1 a)
  have hB : ∀ b, decide ((L0.φB b).h < len (L0.φB b).i) = false := by
    intro b
    change decide (len b < len b) = false
    simp
  have hcut := card_cut_le (F := F) (len := len) h1
  rw [Fintype.card_fin] at hcut
  have hδ : (N : ℝ) ≤ (N : ℝ) / n * Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      have : N = 0 := by
        obtain ⟨M, rfl⟩ := hN
        have : ℓ * M = 0 := by
          have : (M + M) / 2 = M := by omega
          rw [this] at hn; omega
        rcases Nat.mul_eq_zero.1 this with h | h <;> omega
      simp [this]
    · rw [div_mul_cancel₀]
      exact_mod_cast hn0.ne'
  refine ⟨_, L0.map e hH, ?_⟩
  convert L0.isSparse_map e hH (fun p => decide (p.h < len p.i)) hA hB N hcut _ hδ

/-! ### Odd `ℓ`: `F = K_{N/2,N/2}` -/

/-- The complete bipartite graph `K_{N/2,N/2}` on `Fin N` with sides `{i < N/2}` and
`{i ≥ N/2}` (the paper's `([N], [N/2] × ([N] \ [N/2]))`). -/
def halfBipartite (N : ℕ) : SimpleGraph (Fin N) where
  Adj i j := ((i : ℕ) < N / 2 ↔ N / 2 ≤ (j : ℕ))
  symm := ⟨fun i j h => by omega⟩
  loopless := ⟨fun i h => by omega⟩

instance (N : ℕ) : DecidableRel (halfBipartite N).Adj := fun i j =>
  inferInstanceAs (Decidable ((i : ℕ) < N / 2 ↔ N / 2 ≤ (j : ℕ)))

/-- `K_{N/2,N/2}` has no odd cycles. -/
lemma halfBipartite_free {ℓ : ℕ} (hℓ : 3 ≤ ℓ) (hodd : Odd ℓ) (N : ℕ) :
    (cycleGraph ℓ).Free (halfBipartite N) := by
  have : NeZero ℓ := ⟨by omega⟩
  rintro ⟨f⟩
  have hx := isCycSeq_seq (by omega) f
  set x := seq f
  let c : ℤ → Prop := fun t => (x t : ℕ) < N / 2
  have hc : ∀ t, (c (t + 1) ↔ ¬ c t) := by
    intro t
    have := hx.adj t
    change ((x t : ℕ) < N / 2 ↔ N / 2 ≤ (x (t + 1) : ℕ)) at this
    simp only [c]
    omega
  have hn : ∀ n : ℕ, (c n ↔ (c 0 ↔ Even n)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hc n
      push_cast
      rw [this, ih, Nat.even_add_one]
      tauto
  have h := hn ℓ
  have hxℓ : x ℓ = x 0 := by simpa using hx.add_period 0
  simp only [c, hxℓ, Nat.not_even_iff_odd.2 hodd] at h
  tauto

/-- `K_{N/2,N/2}` on `Fin (M + M)` is isomorphic to `completeBipartiteGraph (Fin M) (Fin M)`. -/
def halfBipartiteIso (M : ℕ) : completeBipartiteGraph (Fin M) (Fin M) ≃g halfBipartite (M + M) where
  toEquiv := finSumFinEquiv
  map_rel_iff' {a b} := by
    have hM : (M + M) / 2 = M := by omega
    change (((finSumFinEquiv a : Fin (M + M)) : ℕ) < (M + M) / 2 ↔
      (M + M) / 2 ≤ ((finSumFinEquiv b : Fin (M + M)) : ℕ)) ↔ _
    rw [hM]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [completeBipartiteGraph, a.isLt, b.isLt]

/-- `K_{N/2,N/2}` has `N²/4` edges. -/
lemma card_edgeFinset_halfBipartite {N : ℕ} (hN : Even N) :
    #(halfBipartite N).edgeFinset = (N / 2) * (N / 2) := by
  classical
  obtain ⟨M, rfl⟩ := hN
  rw [show (M + M) / 2 = M by omega, ← (halfBipartiteIso M).card_edgeFinset_eq]
  have := encard_edgeSet_completeBipartiteGraph (W₁ := Fin M) (W₂ := Fin M)
  rw [← coe_edgeFinset, Set.encard_coe_eq_coe_finsetCard] at this
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at this
  exact_mod_cast this

open scoped Classical in
/-- **Lemma 18, odd `ℓ`** (what the proof shows): for odd `ℓ ≥ 5`, even `N` and `n ≥ ℓ · N/2`
there is an `N/n`-sparse `(C_ℓ, K_{N/2,N/2})`-lower bound graph on `n` vertices; `K_{N/2,N/2}` is
`C_ℓ`-free with `N²/4` edges. (It is an *extremal* `C_ℓ`-free graph only for `N` large enough.) -/
theorem lemma_18_odd {ℓ N n : ℕ} (hℓ : 4 ≤ ℓ) (hodd : Odd ℓ) (hN : Even N)
    (hn : ℓ * (N / 2) ≤ n) :
    (cycleGraph ℓ).Free (halfBipartite N) ∧ #(halfBipartite N).edgeFinset = (N / 2) * (N / 2) ∧
    ∃ (G' : SimpleGraph (Fin n)) (L : LowerBoundGraph (cycleGraph ℓ) (halfBipartite N) G'),
      L.IsSparse ((N : ℝ) / n) :=
  ⟨halfBipartite_free (by omega) hodd N, card_edgeFinset_halfBipartite hN,
    lemma_18 hℓ hN hn _ (halfBipartite_free (by omega) hodd N) (fun _ _ _ h => h)⟩

/-! ### Even `ℓ`: `F` extremal -/

open scoped Classical in
/-- **Lemma 18, even `ℓ`** (as in the paper): for even `ℓ ≥ 4`, even `N` and `n ≥ ℓ · N/2` there
is an extremal `C_ℓ`-free graph `F` on `Fin N` (with `ex(N, C_ℓ)` edges) and an `N/n`-sparse
`(C_ℓ, F)`-lower bound graph on `n` vertices. -/
theorem lemma_18_even {ℓ N n : ℕ} (hℓ : 4 ≤ ℓ) (heven : Even ℓ) (hN : Even N)
    (hn : ℓ * (N / 2) ≤ n) :
    ∃ (F : SimpleGraph (Fin N)) (_ : DecidableRel F.Adj), F.IsExtremal (cycleGraph ℓ).Free ∧
      #F.edgeFinset = extremalNumber N (cycleGraph ℓ) ∧
      ∃ (G' : SimpleGraph (Fin n)) (L : LowerBoundGraph (cycleGraph ℓ) F G'),
        L.IsSparse ((N : ℝ) / n) := by
  have hne : cycleGraph ℓ ≠ ⊥ := by
    intro h
    have := cycleGraph_exists_adj (ℓ := ℓ) (by omega) ⟨0, by omega⟩
    rw [h] at this
    simp at this
  obtain ⟨F, hdec, hext⟩ := exists_isExtremal_free (V := Fin N) hne
  refine ⟨F, hdec, hext, ?_, lemma_18 hℓ hN hn F hext.prop
    (fun h => absurd heven (Nat.not_even_iff_odd.2 h))⟩
  rw [card_edgeFinset_of_isExtremal_free hext, Fintype.card_fin]

/-- For even `ℓ` the paper's Lemma 18 holds as stated. -/
theorem lemma18Concl_of_even {ℓ N n : ℕ} (hℓ : 4 ≤ ℓ) (heven : Even ℓ) (hN : Even N)
    (hn : ℓ * (N / 2) ≤ n) : Lemma18Concl ℓ N n := by
  obtain ⟨F, hdec, hext, -, G', L, -⟩ := lemma_18_even hℓ heven hN hn
  exact ⟨F, hdec, hext, G', ⟨L⟩⟩

end Podc.CongestedCliquePower
