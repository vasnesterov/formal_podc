import Papers.PODC2012.EquivocationPrice.Projection

/-!
# Lower bound for sublinear `h` (Lemma 6 and Theorem 5)

Jaffe, Moscibroda, Sen, *On the Price of Equivocation in Byzantine Agreement*, PODC 2012,
Section 3.

* `Crossing U F i b`: the graph `F` on `U` is `(i, b)`-crossing: every two disjoint subsets of
  `U` of sizes `i` and `b` are joined by an edge.
* `lemma_6_general`: exact double-counting form of Lemma 6:
  `C(m, i) · (m - i - b + 1) ≤ 2 · C(m - 2, i - 1) · |F|` for an `(i, b)`-crossing graph `F` on an
  `m`-set (`i + b ≤ m`).
* `lemma_6`: the paper's form for `b = m/2`, `m` even:
  `|F| ≥ m² / (2(m - i)) · (m / (2i) - 1)`.
* `theorem_5`: an `h`-disjoint 3-uniform hypergraph on `n ≥ 6h` vertices (`h ≥ 1`) has at least
  `n(n-1)(n-2) / (24 h²)` hyperedges, i.e. `Tₙ(h) = Ω(n³/h²)`;
  `theorem_5_T` is the same statement for `T n h`.
-/

namespace Podc.EquivocationPrice

open Finset

variable {V : Type*} [DecidableEq V]

/-- The graph `F` (a set of 2-element sets) is `(i, b)`-crossing on `U`: any two disjoint
subsets `X, Y ⊆ U` with `|X| = i`, `|Y| = b` are joined by an edge of `F`. -/
def Crossing (U : Finset V) (F : Finset (Finset V)) (i b : ℕ) : Prop :=
  ∀ X Y : Finset V, X ⊆ U → Y ⊆ U → Disjoint X Y → X.card = i → Y.card = b →
    ∃ f ∈ F, (f ∩ X).Nonempty ∧ (f ∩ Y).Nonempty

/-- In an `(i, b)`-crossing graph on `U` (`i + b ≤ |U|`), every `i`-subset `X` of `U` has at least
`|U| - i - b + 1` edges leaving it (otherwise the vertices of `U \ X` that are not neighbours of
`X` contain a `b`-set with no edge to `X`). -/
theorem card_leaving_ge {U : Finset V} {F : Finset (Finset V)} {i b : ℕ}
    (hF : ∀ f ∈ F, f.card = 2 ∧ f ⊆ U) (hC : Crossing U F i b) (hib : i + b ≤ U.card)
    {X : Finset V} (hXU : X ⊆ U) (hX : X.card = i) :
    U.card - i - b + 1 ≤ (F.filter (fun f => (f ∩ X).card = 1)).card := by
  set O := F.filter (fun f => (f ∩ X).card = 1) with hO
  by_contra hlt
  push Not at hlt
  set N := O.biUnion (fun f => f \ X) with hN
  have hNcard : N.card ≤ O.card := by
    calc N.card ≤ ∑ f ∈ O, (f \ X).card := card_biUnion_le
      _ ≤ ∑ _f ∈ O, 1 := by
        refine sum_le_sum fun f hf => ?_
        rw [hO, mem_filter] at hf
        have h2 := (hF f hf.1).1
        have := card_sdiff_add_card_inter f X
        omega
      _ = O.card := by rw [sum_const, smul_eq_mul, mul_one]
  have hUX : (U \ X).card = U.card - i := by rw [card_sdiff_of_subset hXU, hX]
  have hW : b ≤ ((U \ X) \ N).card := by
    have := le_card_sdiff N (U \ X)
    omega
  obtain ⟨Y, hYW, hYb⟩ := exists_subset_card_eq hW
  have hYU : Y ⊆ U := fun y hy => (mem_sdiff.mp (mem_sdiff.mp (hYW hy)).1).1
  have hXY : Disjoint X Y := by
    rw [disjoint_left]
    intro x hx hy
    exact (mem_sdiff.mp (mem_sdiff.mp (hYW hy)).1).2 hx
  obtain ⟨f, hfF, ⟨x, hx⟩, ⟨y, hy⟩⟩ := hC X Y hXU hYU hXY hX hYb
  rw [mem_inter] at hx hy
  have hyX : y ∉ X := disjoint_right.mp hXY hy.2
  have hfO : f ∈ O := by
    rw [hO, mem_filter]
    refine ⟨hfF, ?_⟩
    have h1 : 1 ≤ (f ∩ X).card := card_pos.mpr ⟨x, mem_inter.mpr hx⟩
    have h2 : (f ∩ X).card < f.card := by
      refine card_lt_card ⟨inter_subset_left, fun h => hyX (mem_inter.mp (h hy.1)).2⟩
    rw [(hF f hfF).1] at h2
    omega
  have hyN : y ∈ N := mem_biUnion.mpr ⟨f, hfO, mem_sdiff.mpr ⟨hy.1, hyX⟩⟩
  exact (mem_sdiff.mp (hYW hy.2)).2 hyN

/-- **Lemma 6** of [JMS12], exact double-counting form. If `F` is an `(i, b)`-crossing graph on
an `m`-set `U` with `i + b ≤ m`, then `C(m, i) · (m - i - b + 1) ≤ 2 · C(m - 2, i - 1) · |F|`:
each of the `C(m, i)` sets `X` has at least `m - i - b + 1` leaving edges, and each edge leaves at
most `2 · C(m - 2, i - 1)` such sets. -/
theorem lemma_6_general {U : Finset V} {F : Finset (Finset V)} {i b : ℕ}
    (hF : ∀ f ∈ F, f.card = 2 ∧ f ⊆ U) (hC : Crossing U F i b) (hib : i + b ≤ U.card) :
    U.card.choose i * (U.card - i - b + 1) ≤ 2 * (U.card - 2).choose (i - 1) * F.card := by
  calc U.card.choose i * (U.card - i - b + 1)
      = ∑ _X ∈ U.powersetCard i, (U.card - i - b + 1) := by
        rw [sum_const, smul_eq_mul, card_powersetCard]
    _ ≤ ∑ X ∈ U.powersetCard i,
          (F.bipartiteAbove (fun (X f : Finset V) => (f ∩ X).card = 1) X).card := by
        refine sum_le_sum fun X hX => ?_
        rw [mem_powersetCard] at hX
        exact card_leaving_ge hF hC hib hX.1 hX.2
    _ = ∑ f ∈ F, ((U.powersetCard i).bipartiteBelow
          (fun (X f : Finset V) => (f ∩ X).card = 1) f).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow ..
    _ ≤ ∑ _f ∈ F, 2 * (U.card - 2).choose (i - 1) := by
        refine sum_le_sum fun f hf => ?_
        have h := card_filter_inter_card_eq_one_le U f i
        rw [card_sdiff_of_subset (hF f hf).2, (hF f hf).1] at h
        exact h
    _ = _ := by rw [sum_const, smul_eq_mul, mul_comm]

/-- `C(M+2, H+1) · (H+1) · (M+1-H) = (M+2)(M+1) · C(M, H)`. -/
theorem choose_add_two_mul (M H : ℕ) :
    (M + 2).choose (H + 1) * (H + 1) * (M + 1 - H) = (M + 2) * (M + 1) * M.choose H := by
  have h1 := Nat.add_one_mul_choose_eq (M + 1) H
  have h2 := Nat.choose_mul_succ_eq M H
  calc (M + 2).choose (H + 1) * (H + 1) * (M + 1 - H)
      = (M + 2) * ((M + 1).choose H * (M + 1 - H)) := by rw [← h1]; ring
    _ = (M + 2) * (M + 1) * M.choose H := by rw [← h2]; ring

/-- `C(m, i) · i · (m - i) = m (m - 1) · C(m - 2, i - 1)` for `1 ≤ i` and `2 ≤ m`. -/
theorem choose_mul_mul_sub {m i : ℕ} (hi : 1 ≤ i) (hm : 2 ≤ m) :
    m.choose i * i * (m - i) = m * (m - 1) * (m - 2).choose (i - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 2 := ⟨m - 2, by omega⟩
  obtain ⟨H, rfl⟩ : ∃ H, i = H + 1 := ⟨i - 1, by omega⟩
  have := choose_add_two_mul M H
  rw [show M + 2 - (H + 1) = M + 1 - H by omega, show M + 2 - 1 = M + 1 by omega,
    show M + 2 - 2 = M by omega, show H + 1 - 1 = H by omega]
  exact this

/-- **Lemma 6** of [JMS12]: every `(i, m/2)`-crossing graph on `m` vertices (`m` even,
`1 ≤ i ≤ m/2`) has at least `m² / (2(m - i)) · (m / (2i) - 1)` edges. -/
theorem lemma_6 {U : Finset V} {F : Finset (Finset V)} {i : ℕ}
    (hF : ∀ f ∈ F, f.card = 2 ∧ f ⊆ U) (heven : Even U.card) (hi : 1 ≤ i)
    (hi2 : i ≤ U.card / 2) (hC : Crossing U F i (U.card / 2)) :
    ((U.card : ℝ) ^ 2 / (2 * (U.card - i))) * (U.card / (2 * i) - 1) ≤ F.card := by
  set m := U.card with hm
  obtain ⟨k, hk⟩ := heven
  have hk2 : m / 2 = k := by omega
  rw [hk2] at hi2 hC
  have hgen := lemma_6_general hF hC (by omega)
  rw [← hm] at hgen
  have hid := choose_mul_mul_sub hi (show 2 ≤ m by omega)
  have hpos : 0 < (m - 2).choose (i - 1) := Nat.choose_pos (by omega)
  -- `m (m-1) (k - i + 1) ≤ 2 i (m - i) |F|`
  have key : m * (m - 1) * (m - i - k + 1) ≤ 2 * i * (m - i) * F.card := by
    have := Nat.mul_le_mul_right (i * (m - i)) hgen
    have e : m.choose i * (m - i - k + 1) * (i * (m - i)) =
        (m - 2).choose (i - 1) * (m * (m - 1) * (m - i - k + 1)) := by
      calc m.choose i * (m - i - k + 1) * (i * (m - i))
          = (m.choose i * i * (m - i)) * (m - i - k + 1) := by ring
        _ = _ := by rw [hid]; ring
    have e2 : 2 * (m - 2).choose (i - 1) * F.card * (i * (m - i)) =
        (m - 2).choose (i - 1) * (2 * i * (m - i) * F.card) := by ring
    rw [e, e2] at this
    exact Nat.le_of_mul_le_mul_left this hpos
  have hmR : (m : ℝ) = 2 * k := by exact_mod_cast hk.trans (two_mul k).symm
  have hkey : (m : ℝ) * (m - 1) * (k - i + 1) ≤ 2 * i * (m - i) * F.card := by
    have h1 : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have h2 : ((m - i - k + 1 : ℕ) : ℝ) = k - i + 1 := by
      rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast
      rw [hmR]; ring
    have h3 : ((m - i : ℕ) : ℝ) = m - i := by rw [Nat.cast_sub (by omega)]
    have := (Nat.cast_le (α := ℝ)).mpr key
    push_cast [h1, h2, h3] at this
    exact this
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hikR : (i : ℝ) ≤ k := by exact_mod_cast hi2
  have hmi : (0 : ℝ) < m - i := by rw [hmR]; linarith
  rw [show ((m : ℝ) ^ 2 / (2 * (m - i))) * (m / (2 * i) - 1) =
      (m : ℝ) ^ 2 * (m - 2 * i) / (4 * i * (m - i)) by field_simp; ring]
  rw [div_le_iff₀ (by positivity)]
  rw [hmR] at hkey ⊢
  nlinarith

/-- `C(n, h) · h · (n - h) · (n - h - 1) = n (n - 1) (n - 2) · C(n - 3, h - 1)` for `1 ≤ h` and
`3 ≤ n`. -/
theorem choose_mul_three {n h : ℕ} (hh : 1 ≤ h) (hn : 3 ≤ n) :
    n.choose h * h * (n - h) * (n - h - 1) = n * (n - 1) * (n - 2) * (n - 3).choose (h - 1) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  obtain ⟨H, rfl⟩ : ∃ H, h = H + 1 := ⟨h - 1, by omega⟩
  have h1 := Nat.add_one_mul_choose_eq (N + 2) H
  have h2 := Nat.choose_mul_succ_eq (N + 1) H
  have h3 := Nat.choose_mul_succ_eq N H
  rw [show N + 3 - (H + 1) = N + 2 - H by omega, show N + 2 - H - 1 = N + 1 - H by omega,
    show N + 3 - 1 = N + 2 by omega, show N + 3 - 2 = N + 1 by omega,
    show N + 3 - 3 = N by omega, show H + 1 - 1 = H by omega]
  calc (N + 3).choose (H + 1) * (H + 1) * (N + 2 - H) * (N + 1 - H)
      = (N + 3) * ((N + 2).choose H * (N + 1 + 1 - H)) * (N + 1 - H) := by rw [← h1]; ring
    _ = (N + 3) * (N + 2) * ((N + 1).choose H * (N + 1 - H)) := by rw [← h2]; ring
    _ = _ := by rw [← h3]; ring

variable [Fintype V]

/-- For `|C| = h`, the projection of an `h`-disjoint hypergraph by `C` is `(h, ⌈(n-h)/2⌉)`-crossing
on the complement of `C` (proof of Theorem 5 of [JMS12]). -/
theorem crossing_proj {E : Finset (Finset V)} {h : ℕ} (hD : HDisjoint E h)
    (h6 : 3 * h ≤ Fintype.card V + 1) {C : Finset V} (hC : C.card = h) :
    Crossing (Finset.univ \ C) (proj E C) h ((Fintype.card V - h + 1) / 2) := by
  intro X Y hX hY hXY hXc hYc
  have hXC : Disjoint X C := sdiff_disjoint.mono_left hX
  have hYC : Disjoint Y C := sdiff_disjoint.mono_left hY
  obtain ⟨x, hx, y, hy, z, hz, he⟩ := hD X Y C
    ⟨hXY, hXC, hYC, hXc.ge, by omega, hC.ge, by omega⟩
  have hxy : x ≠ y := fun hxy => disjoint_left.mp hXY hx (hxy ▸ hy)
  refine ⟨{x, y}, pair_mem_proj (disjoint_left.mp hXC hx) (disjoint_left.mp hYC hy) hz hxy he,
    ⟨x, ?_⟩, ⟨y, ?_⟩⟩ <;> simp [hx, hy]

/-- **Theorem 5** of [JMS12] (with an explicit constant): if `1 ≤ h` and `6h ≤ n`, every
`h`-disjoint 3-uniform hypergraph on `n` vertices has at least `n(n-1)(n-2) / (24 h²)`
hyperedges; in particular `Tₙ(h) = Ω(n³/h²)`. -/
theorem theorem_5 {E : Finset (Finset V)} {h : ℕ} (hE : Uniform3 E) (hD : HDisjoint E h)
    (h1 : 1 ≤ h) (h6 : 6 * h ≤ Fintype.card V) :
    Fintype.card V * (Fintype.card V - 1) * (Fintype.card V - 2) ≤ 24 * h ^ 2 * E.card := by
  set n := Fintype.card V with hn
  set b := (n - h + 1) / 2 with hb
  set β := n - h - h - b + 1 with hβ
  set A := n.choose h
  set B := (n - h).choose h
  set P1 := (n - 3).choose (h - 1)
  set P2 := (n - h - 2).choose (h - 1)
  -- Lemma 6 for every projection, summed over all `h`-sets `C`
  have hmain : A * B * β ≤ 6 * P1 * P2 * E.card := by
    calc A * B * β = ∑ _C ∈ (Finset.univ : Finset V).powersetCard h, B * β := by
          rw [sum_const, smul_eq_mul, card_powersetCard, card_univ]; ring
      _ ≤ ∑ C ∈ (Finset.univ : Finset V).powersetCard h, 2 * P2 * (proj E C).card := by
          refine sum_le_sum fun C hC => ?_
          rw [mem_powersetCard] at hC
          have hU : (Finset.univ \ C).card = n - h := by
            rw [card_sdiff_of_subset (subset_univ _), card_univ, hC.2]
          have := lemma_6_general (proj_subset_compl hE) (crossing_proj hD (by omega) hC.2)
            (by rw [hU]; omega)
          rw [hU] at this
          rw [mul_assoc]
          exact this.trans_eq' (by ring) |>.trans_eq (by ring)
      _ = 2 * P2 * ∑ C ∈ (Finset.univ : Finset V).powersetCard h, (proj E C).card := by
          rw [mul_sum]
      _ ≤ 2 * P2 * (3 * P1 * E.card) := Nat.mul_le_mul_left _ (sum_card_proj_le hE h)
      _ = 6 * P1 * P2 * E.card := by ring
  have e1 : A * h * (n - h) * (n - h - 1) = n * (n - 1) * (n - 2) * P1 :=
    choose_mul_three h1 (by omega)
  have e2 : B * h * (n - h - h) = (n - h) * (n - h - 1) * P2 := by
    exact choose_mul_mul_sub h1 (show 2 ≤ n - h by omega)
  set K := (n - h) * (n - h - 1)
  set D := n - h - h
  set X := n * (n - 1) * (n - 2)
  have hP1 : 0 < P1 := Nat.choose_pos (by omega)
  have hP2 : 0 < P2 := Nat.choose_pos (by omega)
  have hK : 0 < K := Nat.mul_pos (by omega) (by omega)
  have hβpos : 0 < β := by omega
  have hD4 : D ≤ 4 * β := by omega
  have step : X * β * (P1 * P2 * K) ≤ 6 * E.card * h ^ 2 * D * (P1 * P2 * K) := by
    calc X * β * (P1 * P2 * K) = (X * P1) * (K * P2) * β := by ring
      _ = (A * h * (n - h) * (n - h - 1)) * (B * h * D) * β := by rw [← e1, ← e2]
      _ = (A * B * β) * (h ^ 2 * K * D) := by ring
      _ ≤ (6 * P1 * P2 * E.card) * (h ^ 2 * K * D) := Nat.mul_le_mul_right _ hmain
      _ = 6 * E.card * h ^ 2 * D * (P1 * P2 * K) := by ring
  have step2 : X * β ≤ 6 * E.card * h ^ 2 * D :=
    Nat.le_of_mul_le_mul_right step (by positivity)
  have step3 : X * β ≤ 24 * h ^ 2 * E.card * β :=
    step2.trans (by
      calc 6 * E.card * h ^ 2 * D ≤ 6 * E.card * h ^ 2 * (4 * β) := Nat.mul_le_mul_left _ hD4
        _ = 24 * h ^ 2 * E.card * β := by ring)
  exact Nat.le_of_mul_le_mul_right step3 hβpos

/-- The complete 3-uniform hypergraph is `h`-disjoint for every `h ≥ 1`. -/
theorem hDisjoint_complete {h : ℕ} (h1 : 1 ≤ h) :
    HDisjoint ((Finset.univ : Finset V).powersetCard 3) h := by
  rintro A B C ⟨hAB, hAC, hBC, hA, hB, hC, -⟩
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < A.card)
  obtain ⟨y, hy⟩ := card_pos.mp (by omega : 0 < B.card)
  obtain ⟨z, hz⟩ := card_pos.mp (by omega : 0 < C.card)
  refine ⟨x, hx, y, hy, z, hz, mem_powersetCard.mpr ⟨subset_univ _, ?_⟩⟩
  have hxy : x ≠ y := fun e => disjoint_left.mp hAB hx (e ▸ hy)
  have hxz : x ≠ z := fun e => disjoint_left.mp hAC hx (e ▸ hz)
  have hyz : y ≠ z := fun e => disjoint_left.mp hBC hy (e ▸ hz)
  rw [card_insert_of_notMem (by simp [hxy, hxz]), card_pair hyz]

/-- **Theorem 5** of [JMS12], stated for `Tₙ(h)`: for `1 ≤ h` and `6h ≤ n`,
`n(n-1)(n-2) ≤ 24 h² · Tₙ(h)`, i.e. `Tₙ(h) = Ω(n³/h²)`. -/
theorem theorem_5_T {n h : ℕ} (h1 : 1 ≤ h) (h6 : 6 * h ≤ n) :
    n * (n - 1) * (n - 2) ≤ 24 * h ^ 2 * T n h := by
  have hne : {m | ∃ E : Finset (Finset (Fin n)), Uniform3 E ∧ HDisjoint E h ∧ E.card = m}.Nonempty :=
    ⟨_, (Finset.univ : Finset (Fin n)).powersetCard 3,
      fun e he => (mem_powersetCard.mp he).2, hDisjoint_complete h1, rfl⟩
  obtain ⟨E, hE, hD, hcard⟩ := Nat.sInf_mem hne
  rw [T, ← hcard]
  have := theorem_5 hE hD h1 (by rwa [Fintype.card_fin])
  rwa [Fintype.card_fin] at this

end Podc.EquivocationPrice
