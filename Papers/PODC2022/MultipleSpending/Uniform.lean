import Papers.PODC2022.MultipleSpending.Trust

/-!
# The inconsistency number of the uniform model (Theorem 3.6, Example 3.7, Table 1)

`uniform q f`: every process has as quorums all `q`-sets containing it, and every set of at most
`f` processes may fail.

* `inconsistencyNumber_uniform`: for `1 ≤ q ≤ n` and **every** `f`, the inconsistency number is
  `⌊(n − m)/(q − m)⌋` with `m = min f (q − 1)`.
* `theorem_3_6`: the paper's formula `⌊(n − f)/(q − f)⌋`, under the hypotheses `f < q ≤ n` that
  the paper leaves implicit.
* `theorem_3_6_needs_q_gt_f`: for `q ≤ f` the paper's formula (whose denominator `q − f` is
  `≤ 0`) is not the inconsistency number: e.g. `n = 3`, `q = f = 1` gives `λ = 3`.
* `table_1`: the numbers of Table 1 (`n = 100`, `q = 67`, `f = 0, …, 66`).
-/

namespace Podc.MultipleSpending

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The uniform trust model `(Q_u, F_u)`: quorums are the sets of `q` processes (containing their
owner), faulty sets are the sets of at most `f` processes. -/
def uniform (q f : ℕ) : TrustModel P where
  Q p := {Q | p ∈ Q ∧ Q.card = q}
  F := {F | F.card ≤ f}

omit [Fintype P] [DecidableEq P] in
theorem uniform_selfMem (q f : ℕ) : (uniform (P := P) q f).SelfMem := fun _ _ h => h.1

omit [Fintype P] [DecidableEq P] in
theorem uniform_downClosed (q f : ℕ) : (uniform (P := P) q f).DownClosed :=
  fun _ hF _ h => (Finset.card_le_card h).trans hF

omit [DecidableEq P] in
theorem uniform_hasQuorums {q f : ℕ} (hq : 0 < q) (hqn : q ≤ Fintype.card P) :
    (uniform (P := P) q f).HasQuorums := by
  intro p
  obtain ⟨u, hpu, -, hu⟩ := Finset.exists_subsuperset_card_eq (n := q) (Finset.subset_univ {p})
    (by rw [Finset.card_singleton]; omega) (by simpa using hqn)
  exact ⟨u, hpu (Finset.mem_singleton_self p), hu⟩

/-- The counting step of the proof of Theorem 3.6: the correct parts `S p \ F` of the quorums of
an independent set are pairwise disjoint, nonempty, and have at least `q − |F|` elements. -/
theorem card_mul_le_of_isIndep {q : ℕ} {F : Finset P} {S : P → Finset P} {C : Finset P}
    (hS : ∀ p ∈ C, p ∈ S p ∧ q ≤ (S p).card) (h : IsIndep F S C) :
    C.card * max (q - F.card) 1 ≤ Fintype.card P - F.card := by
  have hdisj : (C : Set P).PairwiseDisjoint (fun p => S p \ F) := by
    intro p hp p' hp' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_sdiff] at hx hx'
    exact hx.2 (h.2 p hp p' hp' hne (Finset.mem_inter.mpr ⟨hx.1, hx'.1⟩))
  have hsub : C.biUnion (fun p => S p \ F) ⊆ Fᶜ := by
    intro x hx
    obtain ⟨p, -, hx⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Finset.card_compl] at h1
  have h2 : C.card • max (q - F.card) 1 ≤ ∑ p ∈ C, (S p \ F).card := by
    apply Finset.card_nsmul_le_sum
    intro p hp
    have hpF : p ∉ F := Finset.disjoint_left.mp h.1 hp
    refine max_le ?_ ?_
    · exact (Nat.sub_le_sub_right (hS p hp).2 _).trans (Finset.le_card_sdiff F (S p))
    · exact Finset.card_pos.mpr ⟨p, Finset.mem_sdiff.mpr ⟨(hS p hp).1, hpF⟩⟩
  rw [smul_eq_mul] at h2
  exact h2.trans h1

/-- Arithmetic part of the upper bound: monotonicity of `⌊(n − a)/(q − a)⌋` in `a < q`, and
`n − a ≤ n − q + 1` for `a ≥ q`. -/
theorem le_div_of_mul_max_le {n q f a c : ℕ} (hq : 0 < q) (hqn : q ≤ n) (ha : a ≤ f)
    (han : a ≤ n) (hc : c * max (q - a) 1 ≤ n - a) :
    c ≤ (n - min f (q - 1)) / (q - min f (q - 1)) := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  rcases le_or_gt q a with hqa | hqa
  · have hm : min f (q - 1) = q - 1 := min_eq_right (by omega)
    rw [hm]
    have : max (q - a) 1 = 1 := by omega
    rw [this, mul_one] at hc
    have : q - (q - 1) = 1 := by omega
    rw [this, mul_one]
    omega
  · set m := min f (q - 1) with hm
    have ham : a ≤ m := le_min ha (by omega)
    have hmq : m < q := by omega
    have : max (q - a) 1 = q - a := by omega
    rw [this] at hc
    -- c (q - m) ≤ n - m from c (q - a) ≤ n - a and a ≤ m
    rcases Nat.eq_zero_or_pos c with h0 | hcpos
    · simp [h0]
    · have e1 : q - a = (q - m) + (m - a) := by omega
      have e2 : n - a = (n - m) + (m - a) := by omega
      rw [e1, e2, mul_add] at hc
      have : m - a ≤ c * (m - a) := Nat.le_mul_of_pos_left _ hcpos
      omega

/-- **Inconsistency number of the uniform model, all parameters.** For `1 ≤ q ≤ n` and any
`f`, `λ(Q_u, F_u) = ⌊(n − m)/(q − m)⌋` where `m = min f (q − 1)`. -/
theorem inconsistencyNumber_uniform {q : ℕ} (f : ℕ) (hq : 0 < q) (hqn : q ≤ Fintype.card P) :
    inconsistencyNumber (uniform (P := P) q f) =
      (Fintype.card P - min f (q - 1)) / (q - min f (q - 1)) := by
  set n := Fintype.card P with hn
  set m := min f (q - 1) with hm
  apply le_antisymm
  · -- upper bound
    apply TrustModel.inconsistencyNumber_le
    intro F hF S hS C hC
    have hc := card_mul_le_of_isIndep (q := q) (fun p _ => ⟨(hS p).1, (hS p).2.ge⟩) hC
    exact le_div_of_mul_max_le hq hqn hF (Finset.card_le_univ F) hc
  · -- lower bound: `k` disjoint blocks of `q − m` correct processes plus a common faulty set
    have hmq : m < q := by omega
    set d := q - m with hd
    have hd0 : 0 < d := by omega
    set k := (n - m) / d with hk
    obtain ⟨F₀, -, hF₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset P))
      (n := m) (by rw [Finset.card_univ]; omega)
    have hY : Fintype.card {p // p ∉ F₀} = n - m := by
      simp [n, Fintype.card_subtype, Finset.filter_not, Finset.card_univ_sdiff, hF₀]
    have hcard : Fintype.card (Fin k × Fin d) ≤ Fintype.card {p // p ∉ F₀} := by
      rw [hY, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      exact Nat.div_mul_le_self _ _
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
    let z : Fin d := ⟨0, hd0⟩
    let g : Fin k → P := fun i => (e (i, z)).val
    have hg : Function.Injective g := fun i j h => by
      have := e.injective (Subtype.ext h)
      exact (Prod.mk.inj this).1
    let blk : P → Finset P := fun p =>
      (Finset.univ.filter fun ij : Fin k × Fin d => g ij.1 = p).image fun ij => (e ij).val
    let R : P → Finset P := fun p => F₀ ∪ blk p
    have hev : ∀ ij, (e ij).val ∉ F₀ := fun ij => (e ij).2
    have hblk : ∀ i, blk (g i) =
        (Finset.univ : Finset (Fin d)).image fun j => (e (i, j)).val := by
      intro i
      ext x
      simp only [blk, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨i', j⟩, hi', rfl⟩
        obtain rfl : i' = i := hg hi'
        exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨(i, j), rfl, rfl⟩
    have hblk_card : ∀ i, (blk (g i)).card = d := by
      intro i
      rw [hblk, Finset.card_image_of_injective]
      · simp
      · intro j j' h
        have := e.injective (Subtype.ext h)
        exact (Prod.mk.inj this).2
    have hC : Disjoint (Finset.univ.image g) F₀ := by
      rw [Finset.disjoint_left]
      intro p hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact hev _
    have hCcard : (Finset.univ.image g).card = k := by
      rw [Finset.card_image_of_injective _ hg]; simp
    rw [← hCcard]
    apply (uniform q f).card_le_inconsistencyNumber_of_family (uniform_hasQuorums hq hqn)
      (show F₀.card ≤ f by rw [hF₀]; exact min_le_left _ _) hC R
    · intro p hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      refine ⟨Finset.mem_union_right _ ?_, ?_⟩
      · rw [hblk]; exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩
      · have hdis : Disjoint F₀ (blk (g i)) := by
          rw [Finset.disjoint_right]
          intro x hx
          rw [hblk] at hx
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
          exact hev _
        simp only [R]
        rw [Finset.card_union_of_disjoint hdis, hblk_card, hF₀]
        omega
    · intro p hp p' hp' hne x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp hp'
      simp only [R, Finset.mem_inter, Finset.mem_union] at hx
      rcases hx with ⟨hx | hx, hx' | hx'⟩
      · exact hx
      · exact hx
      · exact hx'
      · exfalso
        rw [hblk] at hx hx'
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨j', -, h⟩ := Finset.mem_image.mp hx'
        have := e.injective (Subtype.ext h)
        exact hne (by rw [(Prod.mk.inj this).1])

/-- **Theorem 3.6** of [Bezerra–Kuznetsov]: the inconsistency number of the uniform model with
`n` processes, quorums of size `q` and at most `f` faulty processes is `⌊(n − f)/(q − f)⌋`.
The hypotheses `f < q ≤ n` are not stated in the paper (see `theorem_3_6_needs_q_gt_f`). -/
theorem theorem_3_6 {q f : ℕ} (hfq : f < q) (hqn : q ≤ Fintype.card P) :
    inconsistencyNumber (uniform (P := P) q f) = (Fintype.card P - f) / (q - f) := by
  rw [inconsistencyNumber_uniform f (by omega) hqn, min_eq_left (by omega)]

/-- For `q ≤ f` Theorem 3.6 has no meaning (the denominator `q − f` is `≤ 0`) and the actual
inconsistency number is `n − q + 1`: e.g. three processes with singleton quorums and one possible
failure have inconsistency number `3`. -/
theorem theorem_3_6_needs_q_gt_f {q f : ℕ} (hq : 0 < q) (hqf : q ≤ f)
    (hqn : q ≤ Fintype.card P) :
    inconsistencyNumber (uniform (P := P) q f) = Fintype.card P - q + 1 := by
  rw [inconsistencyNumber_uniform f hq hqn, min_eq_right (by omega)]
  have : q - (q - 1) = 1 := by omega
  rw [this, Nat.div_one]
  omega

example : inconsistencyNumber (uniform (P := Fin 3) 1 1) = 3 := by
  rw [theorem_3_6_needs_q_gt_f (by norm_num) le_rfl (by simp)]; simp

/-- **Table 1** (Example 3.7): with `n = 100` processes and the classical Byzantine quorum size
`q = 67`, the inconsistency numbers for `f = 0, …, 66` are as listed in the paper. -/
theorem table_1 :
    (List.range 67).map (fun f => inconsistencyNumber (uniform (P := Fin 100) 67 f)) =
      List.replicate 34 1 ++ List.replicate 17 2 ++ List.replicate 5 3 ++
        List.replicate 3 4 ++ [5, 5, 6, 7, 9, 12, 17, 34] := by
  have : ∀ f ∈ List.range 67, inconsistencyNumber (uniform (P := Fin 100) 67 f) =
      (100 - f) / (67 - f) := by
    intro f hf
    rw [List.mem_range] at hf
    rw [theorem_3_6 hf (by simp)]
    simp
  rw [List.map_congr_left this]
  decide

end Podc.MultipleSpending
