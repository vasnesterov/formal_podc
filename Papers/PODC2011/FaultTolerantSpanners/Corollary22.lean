import Papers.PODC2011.FaultTolerantSpanners.Theorem21
import Cslib.Foundations.Combinatorics.SimpleGraph.GreedySpanner

/-!
# Corollary 2.2 of Dinitz–Krauthgamer (PODC'11): the greedy spanner plugged into Theorem 2.1

The paper applies Theorem 2.1 to the greedy `(2t-1)`-spanner of Althöfer et al. [ADD+93], which has
`O(n^{1 + 1/t})` edges (`k = 2t - 1`, so `1 + 2/(k+1) = 1 + 1/t`). We prove the cited fact:

* `exists_greedy_spanner` — every finite weighted graph has a subgraph `H` of girth `> 2t` which
  is a `(2t - 1)`-spanner: the greedy spanner of the shared library
  `Cslib/Foundations/Combinatorics/SimpleGraph/GreedySpanner.lean` (`IsGreedySpanner.isWSpanner`,
  `IsGreedySpanner.noShortCycles`);
* the Moore bound relative to a vertex set `S` containing all endpoints,
  `|E| ≤ |S|^{1+1/t} + |S|` (`SimpleGraph.NoShortCycles.ncard_edgeSet_le_card_rpow`,
  `Cslib/Foundations/Combinatorics/SimpleGraph/Girth.lean`);
* `greedyAlg` — hence a `SpannerAlg G w (2t-1) (fun s => s^{1+1/t} + s)`;
* `corollary_2_2` — with probability `≥ 1 - (n+1)^{-C} - α e^{-n^{1/3}/6}` the conversion outputs
  an `r`-fault-tolerant `(2t-1)`-spanner with at most `6 (8C + 26) r^{2 - 1/t} n^{1 + 1/t} ln(n+1)`
  edges, i.e. `O(r^{2 - 2/(k+1)} n^{1 + 2/(k+1)} log n)` as in the paper.
-/

open Finset SimpleGraph Cslib.Probability
open scoped ENNReal NNReal

namespace DinitzKrauthgamer

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **Greedy spanner** [ADD+93]: every finite weighted graph `G'` has a subgraph of girth `> 2t`
which is a `(2t - 1)`-spanner. -/
theorem exists_greedy_spanner (G' : SimpleGraph V) (w : Sym2 V → ℝ≥0) {t : ℕ} (ht : 1 ≤ t) :
    ∃ H ≤ G', H.NoShortCycles (2 * t) ∧
      ∀ u v, H.wdist w u v ≤ (2 * t - 1 : ℕ) * G'.wdist w u v := by
  obtain ⟨H, hH⟩ := exists_isGreedySpanner G' w ((2 * t - 1 : ℕ) : ℝ≥0)
  have hsp := hH.isWSpanner (by exact_mod_cast (by omega : 1 ≤ 2 * t - 1))
  exact ⟨H, hsp.1, hH.noShortCycles le_rfl, fun u v => by simpa using hsp.2 u v⟩

/-- The greedy `(2t-1)`-spanner as a spanner algorithm with size bound `s^{1+1/t} + s`. -/
noncomputable def greedyAlg (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) {t : ℕ} (ht : 1 ≤ t) :
    SpannerAlg G w (2 * t - 1) (fun s => (s : ℝ) ^ (1 + 1 / (t : ℝ)) + s) where
  run S := (exists_greedy_spanner (G.deleteVerts (↑S : Set V)ᶜ) w ht).choose
  le S := (exists_greedy_spanner (G.deleteVerts (↑S : Set V)ᶜ) w ht).choose_spec.1
  stretch S u v _ _ := (exists_greedy_spanner (G.deleteVerts (↑S : Set V)ᶜ) w ht).choose_spec.2.2 u v
  size S := by
    obtain ⟨hle, hcyc, -⟩ := (exists_greedy_spanner (G.deleteVerts (↑S : Set V)ᶜ) w ht).choose_spec
    refine hcyc.ncard_edgeSet_le_card_rpow ht S fun u v huv => ?_
    have := (hle huv).2.1
    simpa using this

lemma monotone_greedy_size {t : ℕ} :
    Monotone (fun s : ℕ => (s : ℝ) ^ (1 + 1 / (t : ℝ)) + s) := by
  intro a b hab
  have : (a : ℝ) ≤ b := by exact_mod_cast hab
  dsimp only
  gcongr

/-- **Corollary 2.2 of Dinitz–Krauthgamer (PODC'11).** For every weighted graph and every
`t ≥ 1` (stretch `k = 2t - 1`), `1 ≤ r ≤ n` and `C ∈ ℕ`: the conversion of Theorem 2.1 applied to the
greedy spanner outputs, with probability at least `1 - (n+1)^{-C} - α e^{-n^{1/3}/6}`
(`α = numIter n r C = O(r³ log n)`), an `r`-fault-tolerant `(2t-1)`-spanner with at most
`6 (8C + 26) r^{2 - 1/t} n^{1 + 1/t} ln(n+1)` edges. -/
theorem corollary_2_2 (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) {t : ℕ} (ht : 1 ≤ t)
    {r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ Fintype.card V) (C : ℕ) :
    1 - 1 / ((Fintype.card V : ℝ) + 1) ^ C -
        numIter (Fintype.card V) r C * Real.exp (-((Fintype.card V : ℝ) ^ ((1 : ℝ) / 3) / 6)) ≤
      uprob (fun ω : Fin (numIter (Fintype.card V) r C) → V → Fin (max r 2) =>
        IsWeightedVFTSpanner G (ftUnion (greedyAlg G w ht) ω) w r (2 * t - 1) ∧
        ((ftUnion (greedyAlg G w ht) ω).edgeSet.ncard : ℝ) ≤
          6 * (8 * C + 26) * (r : ℝ) ^ (2 - 1 / (t : ℝ)) *
            (Fintype.card V : ℝ) ^ (1 + 1 / (t : ℝ)) * Real.log ((Fintype.card V : ℝ) + 1)) := by
  set n := Fintype.card V
  have hk : 1 ≤ 2 * t - 1 := by omega
  have hf2 : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (1 + 1 / (t : ℝ)) + ((2 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (1 + 1 / (t : ℝ)) := by positivity
    push_cast; linarith
  refine (theorem_2_1 (greedyAlg G w ht) hk monotone_greedy_size hf2 hr hrn C).trans
    (uprob_mono fun ω h => ⟨h.1, h.2.trans ?_⟩)
  -- arithmetic: `r³ ln(n+1) (⌊2n/r⌋^{1+1/t} + ⌊2n/r⌋) ≤ 6 r^{2-1/t} n^{1+1/t} ln(n+1)`
  set L := Real.log ((n : ℝ) + 1)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hr.trans hrn
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrn' : (r : ℝ) ≤ n := by exact_mod_cast hrn
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hC : (0 : ℝ) ≤ 8 * C + 26 := by positivity
  set e := 1 / (t : ℝ)
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by
    rw [div_le_one (by exact_mod_cast (by omega : 0 < t))]; exact_mod_cast ht
  set y : ℝ := ((⌊2 * (n : ℝ) / r⌋₊ : ℕ) : ℝ)
  have hy0 : 0 ≤ y := Nat.cast_nonneg _
  have hy : y ≤ 2 * n / r := Nat.floor_le (by positivity)
  -- `y^{1+e} ≤ (2n/r)^{1+e} = 2^{1+e} n^{1+e} / r^{1+e}`
  have hry : (r : ℝ) ^ 3 * (y ^ (1 + e) + y) ≤ 6 * (r : ℝ) ^ (2 - e) * (n : ℝ) ^ (1 + e) := by
    have h1 : y ^ (1 + e) ≤ (2 * n / r) ^ (1 + e) := Real.rpow_le_rpow hy0 hy (by linarith)
    have hrpos : (0 : ℝ) < r := by linarith
    have h2 : (r : ℝ) ^ 3 * (2 * n / r) ^ (1 + e) ≤ 4 * (r : ℝ) ^ (2 - e) * (n : ℝ) ^ (1 + e) := by
      rw [Real.div_rpow (by positivity) hrpos.le, Real.mul_rpow (by norm_num) (by positivity)]
      have h2e : (2 : ℝ) ^ (1 + e) ≤ 4 := by
        calc (2 : ℝ) ^ (1 + e) ≤ (2 : ℝ) ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 4 := by norm_num
      have hr3 : (r : ℝ) ^ 3 / (r : ℝ) ^ (1 + e) = (r : ℝ) ^ (2 - e) := by
        rw [← Real.rpow_natCast, ← Real.rpow_sub hrpos]; norm_num; ring_nf
      calc (r : ℝ) ^ 3 * ((2 : ℝ) ^ (1 + e) * (n : ℝ) ^ (1 + e) / (r : ℝ) ^ (1 + e))
          = (2 : ℝ) ^ (1 + e) * ((r : ℝ) ^ 3 / (r : ℝ) ^ (1 + e)) * (n : ℝ) ^ (1 + e) := by ring
        _ = (2 : ℝ) ^ (1 + e) * (r : ℝ) ^ (2 - e) * (n : ℝ) ^ (1 + e) := by rw [hr3]
        _ ≤ 4 * (r : ℝ) ^ (2 - e) * (n : ℝ) ^ (1 + e) := by gcongr
    have h3 : (r : ℝ) ^ 3 * y ≤ 2 * (r : ℝ) ^ (2 - e) * (n : ℝ) ^ (1 + e) := by
      -- `r³ y ≤ 2 n r² ≤ 2 r^{2-e} n^{1+e}` since `r^e ≤ n^e`
      have hry' : (r : ℝ) ^ 3 * y ≤ 2 * n * (r : ℝ) ^ 2 := by
        calc (r : ℝ) ^ 3 * y ≤ (r : ℝ) ^ 3 * (2 * n / r) := by gcongr
          _ = 2 * n * (r : ℝ) ^ 2 := by field_simp
      have hre : (r : ℝ) ^ e ≤ (n : ℝ) ^ e := Real.rpow_le_rpow (by linarith) hrn' he0
      have hsplit1 : (r : ℝ) ^ (2 : ℝ) = (r : ℝ) ^ (2 - e) * (r : ℝ) ^ e := by
        rw [← Real.rpow_add hrpos]; ring_nf
      have hsplit2 : (n : ℝ) ^ (1 + e) = n * (n : ℝ) ^ e := by
        rw [Real.rpow_add (by linarith), Real.rpow_one]
      have hr2 : (r : ℝ) ^ 2 = (r : ℝ) ^ (2 : ℝ) := by norm_cast
      rw [hsplit2]
      calc (r : ℝ) ^ 3 * y ≤ 2 * n * (r : ℝ) ^ 2 := hry'
        _ = 2 * n * ((r : ℝ) ^ (2 - e) * (r : ℝ) ^ e) := by rw [hr2, hsplit1]
        _ ≤ 2 * n * ((r : ℝ) ^ (2 - e) * (n : ℝ) ^ e) := by gcongr
        _ = 2 * (r : ℝ) ^ (2 - e) * (n * (n : ℝ) ^ e) := by ring
    have h4 : (r : ℝ) ^ 3 * y ^ (1 + e) ≤ (r : ℝ) ^ 3 * (2 * n / r) ^ (1 + e) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h5 : (r : ℝ) ^ 3 * (y ^ (1 + e) + y) = (r : ℝ) ^ 3 * y ^ (1 + e) + (r : ℝ) ^ 3 * y := by
      ring
    linarith
  calc (8 * (C : ℝ) + 26) * (r : ℝ) ^ 3 * L * (y ^ (1 + e) + y)
      = (8 * C + 26) * L * ((r : ℝ) ^ 3 * (y ^ (1 + e) + y)) := by ring
    _ ≤ (8 * C + 26) * L * (6 * (r : ℝ) ^ (2 - e) * (n : ℝ) ^ (1 + e)) := by gcongr
    _ = 6 * (8 * C + 26) * (r : ℝ) ^ (2 - e) * (n : ℝ) ^ (1 + e) * L := by ring

end DinitzKrauthgamer
