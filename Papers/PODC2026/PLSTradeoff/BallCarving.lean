import Papers.PODC2026.PLSTradeoff.TSPartition

/-!
# Warm-up: ball carving gives an `(O(t log n), 1/t)`-TS partition in every graph

The warm-up construction of Section 1.1 of [Filtser–Fischer, *Near-Resolution of the Tradeoff
Conjecture in Distributed Proof Labeling Schemes*, PODC 2026]: in every finite graph, a simple
ball-carving process produces an ordered partition into clusters with `(1/t)`-cluster-degeneracy
(Definition 3) and weak diameter `O(t log n)`; by Lemma 3.1 this yields an
`(O(t log n), 1/t)`-TS partition.

* `aliveBall G L v j`: the alive nodes (`∈ L`) at distance `≤ j` from `v`.
* `exists_nonexpanding_ball`: for every alive set `L ∋ v₀` there is a radius `2k` with
  `1 ≤ k ≤ K := t ⌈log₂ n⌉ + 1` whose ball is non-expanding:
  `t |B_{2k}(v₀) ∩ L| ≤ (t+1) |B_{2k-2}(v₀) ∩ L|`.
* `exists_carving`: the carving process, by strong induction on the alive set `L`.
* `exists_degenerate_partition`, `exists_tsPartition`: the warm-up result, with the explicit
  weak-diameter bound `4 (t ⌈log₂ n⌉ + 1)`.

We only use even radii `2k` (the paper allows every radius `j ≥ 2`, comparing with radius
`j - 2`); this does not affect the argument.
-/

namespace PLSTradeoff

open SimpleGraph Finset Classical

variable {V : Type*}

section Numerics

/-- `(1 + 1/t)^t ≥ 2`, in the form `2 t^t ≤ (t+1)^t` (Bernoulli's inequality). -/
lemma two_mul_pow_le_succ_pow {t : ℕ} (ht : 1 ≤ t) : 2 * t ^ t ≤ (t + 1) ^ t := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have h1 : (2 : ℝ) ≤ (1 + 1 / (t : ℝ)) ^ t := by
    have h0 : (0 : ℝ) ≤ 1 / t := by positivity
    have := one_add_mul_le_pow (a := 1 / (t : ℝ)) (by linarith) t
    rwa [mul_one_div_cancel htpos.ne', show (1 : ℝ) + 1 = 2 by norm_num] at this
  have h2 : ((t : ℝ) + 1) ^ t = (t : ℝ) ^ t * (1 + 1 / (t : ℝ)) ^ t := by
    rw [← mul_pow]; congr 1; field_simp
  have : (2 : ℝ) * (t : ℝ) ^ t ≤ ((t : ℝ) + 1) ^ t := by
    rw [h2, mul_comm]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
  exact_mod_cast this

/-- If `n ≤ 2^c` and `n ≥ 1`, then `n < (1 + 1/t)^(t c + 1)`, in the form
`t^(tc+1) n < (t+1)^(tc+1)`. -/
lemma pow_mul_lt_succ_pow {t c n : ℕ} (ht : 1 ≤ t) (hn : 1 ≤ n) (hc : n ≤ 2 ^ c) :
    t ^ (t * c + 1) * n < (t + 1) ^ (t * c + 1) := by
  have hpos : 0 < n * (t ^ t) ^ c := Nat.mul_pos (by omega) (pow_pos (pow_pos (by omega) t) c)
  calc t ^ (t * c + 1) * n = (n * (t ^ t) ^ c) * t := by rw [pow_succ, pow_mul]; ring
    _ < (n * (t ^ t) ^ c) * (t + 1) := by nlinarith
    _ ≤ (2 ^ c * (t ^ t) ^ c) * (t + 1) := by gcongr
    _ = (2 * t ^ t) ^ c * (t + 1) := by rw [mul_pow]
    _ ≤ ((t + 1) ^ t) ^ c * (t + 1) := by gcongr; exact two_mul_pow_le_succ_pow ht
    _ = (t + 1) ^ (t * c + 1) := by rw [pow_succ, pow_mul]

end Numerics

variable (G : SimpleGraph V)

/-- The alive nodes (those in `L`) at distance at most `j` from `v`: `B_j(v) ∩ L`. -/
noncomputable def aliveBall (L : Finset V) (v : V) (j : ℕ) : Finset V :=
  L.filter fun u => G.edist v u ≤ j

variable {G}

lemma mem_aliveBall {L : Finset V} {v u : V} {j : ℕ} :
    u ∈ aliveBall G L v j ↔ u ∈ L ∧ G.edist v u ≤ j := by
  simp only [aliveBall, mem_filter]

lemma aliveBall_subset (L : Finset V) (v : V) (j : ℕ) : aliveBall G L v j ⊆ L :=
  filter_subset _ _

lemma aliveBall_mono {L : Finset V} {v : V} {i j : ℕ} (h : i ≤ j) :
    aliveBall G L v i ⊆ aliveBall G L v j := by
  intro u hu
  rw [mem_aliveBall] at hu ⊢
  exact ⟨hu.1, hu.2.trans (by exact_mod_cast h)⟩

lemma mem_aliveBall_self {L : Finset V} {v : V} (hv : v ∈ L) (j : ℕ) : v ∈ aliveBall G L v j :=
  mem_aliveBall.2 ⟨hv, by simp⟩

variable [Fintype V]

/-- Warm-up of Section 1.1 of [Filtser–Fischer, PODC 2026]: around every alive node `v₀` there is
a non-expanding ball of radius `2k ≤ 2 (t ⌈log₂ n⌉ + 1)`, i.e.
`|B_{2k}(v₀) ∩ L| ≤ (1 + 1/t) |B_{2k-2}(v₀) ∩ L|`. -/
theorem exists_nonexpanding_ball (L : Finset V) {v₀ : V} (hv : v₀ ∈ L) {t : ℕ} (ht : 1 ≤ t) :
    ∃ k, 1 ≤ k ∧ k ≤ t * Nat.clog 2 (Fintype.card V) + 1 ∧
      t * #(aliveBall G L v₀ (2 * k)) ≤ (t + 1) * #(aliveBall G L v₀ (2 * k - 2)) := by
  by_contra h
  push Not at h
  set K := t * Nat.clog 2 (Fintype.card V) + 1 with hK
  have key : ∀ k ≤ K, (t + 1) ^ k * #(aliveBall G L v₀ 0) ≤
      t ^ k * #(aliveBall G L v₀ (2 * k)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := h (k + 1) (by omega) hk
      have h2 : 2 * (k + 1) - 2 = 2 * k := by omega
      rw [h2] at h1
      calc (t + 1) ^ (k + 1) * #(aliveBall G L v₀ 0)
          = (t + 1) * ((t + 1) ^ k * #(aliveBall G L v₀ 0)) := by ring
        _ ≤ (t + 1) * (t ^ k * #(aliveBall G L v₀ (2 * k))) :=
          Nat.mul_le_mul_left _ (ih (by omega))
        _ = t ^ k * ((t + 1) * #(aliveBall G L v₀ (2 * k))) := by ring
        _ ≤ t ^ k * (t * #(aliveBall G L v₀ (2 * (k + 1)))) := Nat.mul_le_mul_left _ h1.le
        _ = t ^ (k + 1) * #(aliveBall G L v₀ (2 * (k + 1))) := by ring
  have hf0 : 1 ≤ #(aliveBall G L v₀ 0) := card_pos.2 ⟨v₀, mem_aliveBall_self hv 0⟩
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨v₀⟩
  have hlt := pow_mul_lt_succ_pow ht hn (Nat.le_pow_clog (by norm_num) (Fintype.card V))
  rw [← hK] at hlt
  have hle : (t + 1) ^ K ≤ t ^ K * Fintype.card V :=
    calc (t + 1) ^ K ≤ (t + 1) ^ K * #(aliveBall G L v₀ 0) := Nat.le_mul_of_pos_right _ hf0
      _ ≤ t ^ K * #(aliveBall G L v₀ (2 * K)) := key K le_rfl
      _ ≤ t ^ K * Fintype.card V := Nat.mul_le_mul_left _ (card_le_univ _)
  omega

/-- The ball-carving process of Section 1.1 of [Filtser–Fischer, PODC 2026], run on an arbitrary
alive set `L` (by strong induction on `L`): the clusters `{v ∈ L | idx v = i}` have weak diameter
`≤ 4 (t ⌈log₂ n⌉ + 1)` and `(1/t)`-cluster-degeneracy relative to `L`. The first cluster is a
non-expanding ball `B_{2k}(v₀) ∩ L`; the others are obtained recursively on the remaining nodes. -/
theorem exists_carving {t : ℕ} (ht : 1 ≤ t) (L : Finset V) :
    ∃ idx : V → ℕ,
      (∀ a ∈ L, ∀ b ∈ L, idx a = idx b →
        G.edist a b ≤ ((4 * (t * Nat.clog 2 (Fintype.card V) + 1) : ℕ) : ℕ∞)) ∧
      ∀ i, t * #{v ∈ L | idx v = i ∧ ∃ u ∈ L, i < idx u ∧ G.edist v u ≤ 2} ≤
        #{v ∈ L | idx v = i} := by
  induction L using Finset.strongInduction with
  | H L ih =>
  rcases L.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · exact ⟨fun _ => 0, by simp, by simp⟩
  obtain ⟨k, hk1, hkK, hexp⟩ := exists_nonexpanding_ball (G := G) L hv₀ ht
  obtain ⟨C, hC⟩ : ∃ C, C = aliveBall G L v₀ (2 * k) := ⟨_, rfl⟩
  have hmemC : ∀ u, u ∈ C ↔ u ∈ L ∧ G.edist v₀ u ≤ ((2 * k : ℕ) : ℕ∞) := fun u => by
    rw [hC, mem_aliveBall]
  have hCL : C ⊆ L := hC ▸ aliveBall_subset _ _ _
  have hv₀C : v₀ ∈ C := hC ▸ mem_aliveBall_self hv₀ _
  obtain ⟨idx', hdiam', hdeg'⟩ := ih (L \ C) (sdiff_ssubset hCL ⟨v₀, hv₀C⟩)
  obtain ⟨idx, hidxC, hidxN⟩ : ∃ idx : V → ℕ,
      (∀ v ∈ C, idx v = 0) ∧ (∀ v ∉ C, idx v = idx' v + 1) :=
    ⟨fun v => if v ∈ C then 0 else idx' v + 1, fun v hv => by simp [hv],
      fun v hv => by simp [hv]⟩
  have hidx0 : ∀ v, idx v = 0 ↔ v ∈ C := fun v => by
    by_cases hv : v ∈ C
    · simp [hidxC v hv, hv]
    · simp [hidxN v hv, hv]
  refine ⟨idx, ?_, ?_⟩
  · intro a ha b hb hab
    by_cases haC : a ∈ C <;> by_cases hbC : b ∈ C
    · have ha' := ((hmemC a).1 haC).2
      have hb' := ((hmemC b).1 hbC).2
      calc G.edist a b ≤ G.edist a v₀ + G.edist v₀ b := SimpleGraph.edist_triangle
        _ ≤ ((2 * k : ℕ) : ℕ∞) + ((2 * k : ℕ) : ℕ∞) := by
          rw [SimpleGraph.edist_comm]; exact add_le_add ha' hb'
        _ ≤ _ := by
          rw [← Nat.cast_add]; exact_mod_cast (by omega)
    · rw [hidxC a haC, hidxN b hbC] at hab; omega
    · rw [hidxN a haC, hidxC b hbC] at hab; omega
    · rw [hidxN a haC, hidxN b hbC] at hab
      exact hdiam' a (mem_sdiff.2 ⟨ha, haC⟩) b (mem_sdiff.2 ⟨hb, hbC⟩) (by omega)
  · intro i
    rcases i with _ | j
    · -- the first cluster `C = B_{2k}(v₀) ∩ L`
      set B := aliveBall G L v₀ (2 * k - 2) with hB
      have hBC : B ⊆ C := hC ▸ aliveBall_mono (by omega)
      have hnum : {v ∈ L | idx v = 0 ∧ ∃ u ∈ L, 0 < idx u ∧ G.edist v u ≤ 2} ⊆ C \ B := by
        intro v hv
        simp only [mem_filter] at hv
        obtain ⟨hvL, hv0, u, huL, hu, hvu⟩ := hv
        have hvC : v ∈ C := (hidx0 v).1 hv0
        have huC : u ∉ C := fun h => by rw [(hidx0 u).2 h] at hu; omega
        refine mem_sdiff.2 ⟨hvC, fun hvB => huC ((hmemC u).2 ⟨huL, ?_⟩)⟩
        have hvB' := (mem_aliveBall.1 hvB).2
        calc G.edist v₀ u ≤ G.edist v₀ v + G.edist v u := SimpleGraph.edist_triangle
          _ ≤ ((2 * k - 2 : ℕ) : ℕ∞) + ((2 : ℕ) : ℕ∞) := add_le_add hvB' hvu
          _ = ((2 * k : ℕ) : ℕ∞) := by rw [← Nat.cast_add]; congr 1; omega
      have hden : {v ∈ L | idx v = 0} = C := by
        ext v; simp only [mem_filter, hidx0]
        exact ⟨fun h => h.2, fun h => ⟨hCL h, h⟩⟩
      have hA := card_le_card hnum
      rw [card_sdiff_of_subset hBC] at hA
      have hBC' := card_le_card hBC
      rw [hden]
      rw [← hC] at hexp
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hBC'
      rw [hd] at hA hexp ⊢
      have hAd : #{v ∈ L | idx v = 0 ∧ ∃ u ∈ L, 0 < idx u ∧ G.edist v u ≤ 2} ≤ d := by omega
      nlinarith [Nat.mul_le_mul_left t hAd]
    · -- later clusters: the carving of `L \ C`, shifted by one
      have e1 : {v ∈ L | idx v = j + 1 ∧ ∃ u ∈ L, j + 1 < idx u ∧ G.edist v u ≤ 2} =
          {v ∈ L \ C | idx' v = j ∧ ∃ u ∈ L \ C, j < idx' u ∧ G.edist v u ≤ 2} := by
        ext v
        simp only [mem_filter, mem_sdiff]
        constructor
        · rintro ⟨hvL, hv, u, huL, hu, hvu⟩
          have hvC : v ∉ C := fun h => by rw [hidxC v h] at hv; omega
          have huC : u ∉ C := fun h => by rw [hidxC u h] at hu; omega
          rw [hidxN v hvC] at hv
          rw [hidxN u huC] at hu
          exact ⟨⟨hvL, hvC⟩, by omega, u, ⟨huL, huC⟩, by omega, hvu⟩
        · rintro ⟨⟨hvL, hvC⟩, hv, u, ⟨huL, huC⟩, hu, hvu⟩
          exact ⟨hvL, by rw [hidxN v hvC]; omega, u, huL, by rw [hidxN u huC]; omega, hvu⟩
      have e2 : {v ∈ L | idx v = j + 1} = {v ∈ L \ C | idx' v = j} := by
        ext v
        simp only [mem_filter, mem_sdiff]
        constructor
        · rintro ⟨hvL, hv⟩
          have hvC : v ∉ C := fun h => by rw [hidxC v h] at hv; omega
          rw [hidxN v hvC] at hv
          exact ⟨⟨hvL, hvC⟩, by omega⟩
        · rintro ⟨⟨hvL, hvC⟩, hv⟩
          exact ⟨hvL, by rw [hidxN v hvC]; omega⟩
      rw [e1, e2]
      exact hdeg' j

/-- Warm-up of Section 1.1 of [Filtser–Fischer, PODC 2026]: every finite graph has an ordered
partition into clusters with `(1/t)`-cluster-degeneracy (Definition 3) and weak diameter at most
`4 (t ⌈log₂ n⌉ + 1) = O(t log n)`. -/
theorem exists_degenerate_partition (G : SimpleGraph V) {t : ℕ} (ht : 1 ≤ t) :
    ∃ idx : V → ℕ, ClusterDegenerate G idx (1 / t) ∧
      WeaklyBounded G idx (4 * (t * Nat.clog 2 (Fintype.card V) + 1)) := by
  obtain ⟨idx, hdiam, hdeg⟩ := exists_carving (G := G) ht univ
  refine ⟨idx, fun i => ?_, fun a b hab => hdiam a (mem_univ _) b (mem_univ _) hab⟩
  have h := hdeg i
  simp only [mem_univ, true_and] at h
  have e1 : {v | idx v = i ∧ ∃ u, i < idx u ∧ G.edist v u ≤ 2} =
      ((univ.filter fun v => idx v = i ∧ ∃ u, i < idx u ∧ G.edist v u ≤ 2 : Finset V) :
        Set V) := by
    ext v; simp
  have e2 : {v | idx v = i} = ((univ.filter fun v => idx v = i : Finset V) : Set V) := by
    ext v; simp
  rw [e1, e2, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  rw [one_div_mul_eq_div, le_div_iff₀ htpos, mul_comm]
  exact_mod_cast h

/-- Warm-up of Section 1.1 of [Filtser–Fischer, PODC 2026]: an `(O(t log n), 1/t)`-TS partition
exists in every graph, namely a `(4 (t ⌈log₂ n⌉ + 1), 1/t)`-TS partition (via Lemma 3.1). -/
theorem exists_tsPartition (G : SimpleGraph V) {t : ℕ} (ht : 1 ≤ t) :
    Nonempty (TSPartition G (4 * (t * Nat.clog 2 (Fintype.card V) + 1)) (1 / t)) := by
  obtain ⟨idx, hdeg, hdiam⟩ := exists_degenerate_partition G ht
  exact ⟨TSPartition.ofDegenerate hdeg hdiam⟩


end PLSTradeoff
