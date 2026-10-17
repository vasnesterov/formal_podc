import Papers.PODC2026.PLSTradeoff.CertifyTS

/-!
# Padded decompositions imply TS partitions (Section 4)

* `exists_degenerate_of_carve` (the iterative procedure of Lemma 4.3): if every nonempty alive
  set `L` contains a nonempty cluster `C ⊆ L` of weak diameter `≤ D` with at most an
  `ε`-fraction of its nodes within distance 2 of `L \ C`, then `V` has an ordered partition with
  `ε`-cluster-degeneracy and weak diameter `≤ D`.
* `PaddedDecomp G β δ Λ` (Definition 6): a probability distribution (finite weights) over
  weakly `Λ`-bounded partitions such that every ball of radius `γΛ` (`0 ≤ γ ≤ δ`) is inside the
  cluster of its centre with probability `≥ e^{-βγ}`.
* `exists_cluster_of_padded` (Lemma 4.2), `exists_tsPartition_of_padded` (Lemma 4.3).
* `tradeoff_of_padded` (Theorem 1.4 modulo the padded decompositions of Conroy–Filtser
  [CF25, Theorem 4.1], which are assumed as a hypothesis): a 1-PLS of cost `p` yields a
  `(3t+2)`-PLS of cost `4⌈log₂ n⌉ + 2⌈2β(2p+1)/t⌉ + 10`.

The paper's padded-decomposition scheme quantifies over real `Λ > 0`; we only use (and assume)
natural `Λ`. Lemma 4.2 needs `2/t ≤ δ` (the paper writes `t = Ω(1)`); for smaller `t` the
1-PLS itself is a `t`-PLS of cost `p = O(⌈p/t⌉)`.
-/

namespace PLSTradeoff

open SimpleGraph Finset Classical

variable {V : Type*} [Fintype V]

/-! ### The iterative procedure of Lemma 4.3 -/

section Carve

variable (G : SimpleGraph V)

/-- Close-to-boundary nodes of `C` with respect to the alive set `L`. -/
noncomputable def closeTo (L C : Finset V) : Finset V :=
  C.filter (fun v => ∃ u ∈ L \ C, G.edist v u ≤ 2)

variable {G}

lemma carve_aux (D : ℕ) (ε : ℝ)
    (h : ∀ L : Finset V, L.Nonempty → ∃ C ⊆ L, C.Nonempty ∧
      (∀ a ∈ C, ∀ b ∈ C, G.edist a b ≤ D) ∧ ((closeTo G L C).card : ℝ) ≤ ε * C.card)
    (L : Finset V) :
    ∃ idx : V → ℕ,
      (∀ i, (((L.filter (fun v => idx v = i ∧ ∃ u ∈ L, i < idx u ∧ G.edist v u ≤ 2)).card : ℕ) :
        ℝ) ≤ ε * (L.filter (fun v => idx v = i)).card) ∧
      (∀ a ∈ L, ∀ b ∈ L, idx a = idx b → G.edist a b ≤ D) := by
  induction L using Finset.strongInduction with
  | H L ih =>
    rcases L.eq_empty_or_nonempty with rfl | hL
    · exact ⟨fun _ => 0, fun i => by simp, fun a ha => by simp at ha⟩
    obtain ⟨C, hCL, hCne, hCd, hCc⟩ := h L hL
    obtain ⟨idx', hdeg', hdiam'⟩ := ih (L \ C) (sdiff_ssubset hCL hCne)
    refine ⟨fun v => if v ∈ C then 0 else idx' v + 1, fun i => ?_, fun a ha b hb hab => ?_⟩
    · rcases i with _ | i
      · -- the cluster `C` itself
        have h1 : L.filter (fun v => (if v ∈ C then 0 else idx' v + 1) = 0) = C := by
          ext v
          by_cases hv : v ∈ C
          · simp [hv, hCL hv]
          · simp [hv]
        have h2 : L.filter (fun v => (if v ∈ C then 0 else idx' v + 1) = 0 ∧
            ∃ u ∈ L, 0 < (if u ∈ C then 0 else idx' u + 1) ∧ G.edist v u ≤ 2) =
            closeTo G L C := by
          ext v
          simp only [closeTo, mem_filter, mem_sdiff]
          by_cases hv : v ∈ C
          · simp only [hv, ite_true, true_and, hCL hv]
            constructor
            · rintro ⟨u, hu, hu0, hvu⟩
              by_cases huC : u ∈ C
              · simp [huC] at hu0
              · exact ⟨u, ⟨hu, huC⟩, hvu⟩
            · rintro ⟨u, ⟨hu, huC⟩, hvu⟩
              exact ⟨u, hu, by simp [huC], hvu⟩
          · simp [hv]
        rw [h1, h2]; exact hCc
      · have h1 : L.filter (fun v => (if v ∈ C then 0 else idx' v + 1) = i + 1) =
            (L \ C).filter (fun v => idx' v = i) := by
          ext v; by_cases hv : v ∈ C <;> simp [hv]
        have h2 : L.filter (fun v => (if v ∈ C then 0 else idx' v + 1) = i + 1 ∧
            ∃ u ∈ L, i + 1 < (if u ∈ C then 0 else idx' u + 1) ∧ G.edist v u ≤ 2) =
            (L \ C).filter (fun v => idx' v = i ∧ ∃ u ∈ L \ C, i < idx' u ∧ G.edist v u ≤ 2) := by
          ext v
          by_cases hv : v ∈ C
          · simp [hv]
          · simp only [mem_filter, mem_sdiff, hv, ite_false, not_false_eq_true, and_true,
              add_left_inj]
            refine and_congr_right fun _ => and_congr_right fun _ => ?_
            constructor
            · rintro ⟨u, hu, hlt, hvu⟩
              by_cases huC : u ∈ C
              · simp [huC] at hlt
              · simp only [huC, ite_false] at hlt
                exact ⟨u, ⟨hu, huC⟩, by omega, hvu⟩
            · rintro ⟨u, ⟨hu, huC⟩, hlt, hvu⟩
              exact ⟨u, hu, by simp only [huC, ite_false]; omega, hvu⟩
        rw [h1, h2]; exact hdeg' i
    · by_cases haC : a ∈ C <;> by_cases hbC : b ∈ C
      · exact hCd a haC b hbC
      · simp [haC, hbC] at hab
      · simp [haC, hbC] at hab
      · simp only [haC, hbC, ite_false, add_left_inj] at hab
        exact hdiam' a (mem_sdiff.2 ⟨ha, haC⟩) b (mem_sdiff.2 ⟨hb, hbC⟩) hab

-- CSLib candidate
/-- The iterative procedure of Lemma 4.3 of [Filtser–Fischer, PODC 2026]: repeatedly carving a
good cluster out of the alive set gives an ordered partition with `ε`-cluster-degeneracy. -/
theorem exists_degenerate_of_carve (D : ℕ) (ε : ℝ)
    (h : ∀ L : Finset V, L.Nonempty → ∃ C ⊆ L, C.Nonempty ∧
      (∀ a ∈ C, ∀ b ∈ C, G.edist a b ≤ D) ∧ ((closeTo G L C).card : ℝ) ≤ ε * C.card) :
    ∃ idx : V → ℕ, ClusterDegenerate G idx ε ∧ WeaklyBounded G idx D := by
  obtain ⟨idx, hdeg, hdiam⟩ := carve_aux D ε h univ
  refine ⟨idx, fun i => ?_, fun a b hab => hdiam a (mem_univ _) b (mem_univ _) hab⟩
  have e1 : {v | idx v = i ∧ ∃ u, i < idx u ∧ G.edist v u ≤ 2}.ncard =
      (univ.filter (fun v => idx v = i ∧ ∃ u ∈ univ, i < idx u ∧ G.edist v u ≤ 2)).card := by
    rw [← Set.ncard_coe_finset]; congr 1; ext v; simp
  have e2 : {v | idx v = i}.ncard = (univ.filter (fun v => idx v = i)).card := by
    rw [← Set.ncard_coe_finset]; congr 1; ext v; simp
  rw [e1, e2]; convert hdeg i

end Carve

/-! ### Padded decompositions (Definition 6) and Lemma 4.2 -/

/-- Definition 6: a `(β, δ, Λ)`-padded decomposition of `G`, as a finitely supported
distribution (weights `w` on an index type `ι`) over partitions (`part i`, given by the cluster
of each node) that are weakly `Λ`-bounded and such that for `0 ≤ γ ≤ δ` every ball of radius
`γΛ` lies in the cluster of its centre with probability at least `e^{-βγ}`. -/
structure PaddedDecomp (G : SimpleGraph V) (β δ : ℝ) (Λ : ℕ) where
  ι : Type
  [fin : Fintype ι]
  w : ι → ℝ
  w_nonneg : ∀ i, 0 ≤ w i
  w_sum : ∑ i, w i = 1
  part : ι → V → Set V
  mem_part : ∀ i v, v ∈ part i v
  part_eq : ∀ i u v, u ∈ part i v → part i u = part i v
  bounded : ∀ i v, ∀ a ∈ part i v, ∀ b ∈ part i v, G.edist a b ≤ Λ
  padded : ∀ γ : ℝ, 0 ≤ γ → γ ≤ δ → ∀ z,
    Real.exp (-(β * γ)) ≤
      ∑ i, if (∀ u (k : ℕ), G.edist z u = k → (k : ℝ) ≤ γ * Λ → u ∈ part i z) then w i else 0

attribute [instance] PaddedDecomp.fin

/-- `G` admits a `(β, δ)`-padded decomposition scheme (for every natural `Λ ≥ 1`). -/
def AdmitsPadded (G : SimpleGraph V) (β δ : ℝ) : Prop :=
  ∀ Λ : ℕ, 1 ≤ Λ → Nonempty (PaddedDecomp G β δ Λ)

variable {G : SimpleGraph V}

/-- **Lemma 4.2** of [Filtser–Fischer, PODC 2026]: with a `(β, δ, t)`-padded decomposition and
`2/t ≤ δ`, every nonempty `L` contains a nonempty cluster `C ⊆ L` of weak diameter `≤ t` with
`|C ∩ B₂(L \ C)| ≤ (2β/t) |C|`. -/
theorem exists_cluster_of_padded {β δ : ℝ} {t : ℕ} (ht : 1 ≤ t) (hδ : (2 : ℝ) / t ≤ δ)
    (PD : PaddedDecomp G β δ t) (L : Finset V) (hL : L.Nonempty) :
    ∃ C ⊆ L, C.Nonempty ∧ (∀ a ∈ C, ∀ b ∈ C, G.edist a b ≤ t) ∧
      ((closeTo G L C).card : ℝ) ≤ (2 * β / t) * C.card := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  set ε : ℝ := 2 * β / t
  -- `Γ_i`: nodes of `L` whose 2-ball leaves their cluster
  let good : PD.ι → V → Prop := fun i z =>
    ∀ u (k : ℕ), G.edist z u = k → (k : ℝ) ≤ (2 / t : ℝ) * t → u ∈ PD.part i z
  let Γ : PD.ι → Finset V := fun i => L.filter (fun z => ¬ good i z)
  have hpad : ∀ z, ∑ i, (if good i z then 0 else PD.w i) ≤ ε := by
    intro z
    have h1 := PD.padded (2 / t) (by positivity) hδ z
    have h2 : ∑ i, (if good i z then 0 else PD.w i) =
        1 - ∑ i, (if good i z then PD.w i else 0) := by
      rw [← PD.w_sum, ← sum_sub_distrib]
      apply sum_congr rfl; intro i _; split_ifs <;> ring
    rw [h2]
    have h3 : 1 - ε ≤ Real.exp (-(β * (2 / t))) := by
      have := Real.add_one_le_exp (-(β * (2 / t)))
      simp only [ε]; field_simp at this ⊢; linarith
    linarith
  -- averaging: some `i` has `|Γ_i| ≤ ε |L|`
  have havg : ∑ i, PD.w i * (Γ i).card = ∑ z ∈ L, ∑ i, (if good i z then 0 else PD.w i) := by
    simp only [Γ, card_filter, Nat.cast_sum, mul_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [sum_comm]
    apply sum_congr rfl; intro z _; apply sum_congr rfl; intro i _
    split_ifs <;> simp
  have hle : ∑ i, PD.w i * (Γ i).card ≤ ∑ i, PD.w i * (ε * L.card) := by
    rw [havg, ← sum_mul, PD.w_sum, one_mul]
    calc ∑ z ∈ L, ∑ i, (if good i z then 0 else PD.w i) ≤ ∑ _z ∈ L, ε :=
          sum_le_sum fun z _ => hpad z
      _ = ε * L.card := by rw [sum_const, nsmul_eq_mul, mul_comm]
  obtain ⟨i, hi⟩ : ∃ i, ((Γ i).card : ℝ) ≤ ε * L.card := by
    by_contra hcon
    push Not at hcon
    have : ∑ i, PD.w i * (ε * L.card) ≤ ∑ i, PD.w i * (Γ i).card := by
      apply sum_le_sum; intro i _
      exact mul_le_mul_of_nonneg_left (hcon i).le (PD.w_nonneg i)
    have hstrict : ∑ i, PD.w i * (ε * L.card) < ∑ i, PD.w i * (Γ i).card := by
      obtain ⟨j, hj⟩ : ∃ j, 0 < PD.w j := by
        by_contra h0
        push Not at h0
        have : ∑ i, PD.w i ≤ 0 := sum_nonpos fun i _ => h0 i
        rw [PD.w_sum] at this; norm_num at this
      apply sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hcon i).le (PD.w_nonneg i))
      exact ⟨j, mem_univ _, mul_lt_mul_of_pos_left (hcon j) hj⟩
    linarith
  -- the clusters of partition `i`, restricted to `L`
  let cl : V → Finset V := fun v => L.filter (· ∈ PD.part i v)
  have hcl_eq : ∀ {u v}, u ∈ cl v → cl u = cl v := by
    intro u v hu
    simp only [cl, mem_filter] at hu
    simp only [cl, PD.part_eq i u v hu.2]
  have hclose_sub : ∀ v ∈ L, closeTo G L (cl v) ⊆ Γ i := by
    intro v hv x hx
    simp only [closeTo, mem_filter, mem_sdiff, cl] at hx
    obtain ⟨⟨hxL, hxv⟩, u, ⟨huL, hucl⟩, hxu⟩ := hx
    simp only [Γ, mem_filter, hxL, true_and]
    intro hg
    obtain ⟨k, hk⟩ : ∃ k : ℕ, G.edist x u = k :=
      (ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by decide) hxu)).imp fun _ h => h.symm
    have hk2 : (k : ℝ) ≤ (2 / t : ℝ) * t := by
      rw [div_mul_cancel₀ _ htpos.ne']
      have : k ≤ 2 := by exact_mod_cast hk ▸ hxu
      exact_mod_cast this
    have hu := hg u k hk hk2
    apply hucl
    refine ⟨huL, ?_⟩
    rw [← PD.part_eq i x v hxv]; exact hu
  -- if every cluster were bad, `|Γ_i|` would exceed `ε |L|`
  by_contra hcon
  push Not at hcon
  have hbad : ∀ v ∈ L, ε * (cl v).card < (closeTo G L (cl v)).card := by
    intro v hv
    refine hcon (cl v) (filter_subset _ _) ⟨v, by simp [cl, hv, PD.mem_part]⟩ ?_
    intro a ha b hb
    simp only [cl, mem_filter] at ha hb
    exact PD.bounded i v a ha.2 b hb.2
  let Cs : Finset (Finset V) := L.image cl
  have hdisj : (Cs : Set (Finset V)).PairwiseDisjoint id := by
    intro A hA B hB hAB
    simp only [Cs, coe_image, Set.mem_image, mem_coe] at hA hB
    obtain ⟨a, -, rfl⟩ := hA
    obtain ⟨b, -, rfl⟩ := hB
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro x hxa hxb
    exact hAB ((hcl_eq hxa).symm.trans (hcl_eq hxb))
  have hcover : Cs.biUnion id = L := by
    ext x
    simp only [mem_biUnion, Cs, mem_image, id]
    constructor
    · rintro ⟨_, ⟨v, -, rfl⟩, hx⟩; exact (mem_filter.1 hx).1
    · intro hx; exact ⟨cl x, ⟨x, hx, rfl⟩, by simp [cl, hx, PD.mem_part]⟩
  have hsumL : (L.card : ℝ) = ∑ C ∈ Cs, (C.card : ℝ) := by
    rw [← hcover, card_biUnion hdisj]; push_cast; rfl
  have hsumΓ : ∑ C ∈ Cs, ((closeTo G L C).card : ℝ) ≤ (Γ i).card := by
    have : (Cs.biUnion (closeTo G L)).card = ∑ C ∈ Cs, (closeTo G L C).card := by
      apply card_biUnion
      intro A hA B hB hAB
      have := hdisj hA hB hAB
      simp only [Function.onFun, id] at this
      exact Finset.disjoint_of_subset_left (filter_subset _ _)
        (Finset.disjoint_of_subset_right (filter_subset _ _) this)
    rw [← Nat.cast_sum, ← this]
    exact_mod_cast card_le_card (biUnion_subset.2 fun C hC => by
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hC; exact hclose_sub v hv)
  have hstrict : ε * L.card < ∑ C ∈ Cs, ((closeTo G L C).card : ℝ) := by
    rw [hsumL, mul_sum]
    apply sum_lt_sum_of_nonempty (hL.image cl)
    intro C hC
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hC
    exact hbad v hv
  linarith

/-- **Lemma 4.3** of [Filtser–Fischer, PODC 2026]: a graph admitting a `(β, δ)`-padded
decomposition scheme has a `(t, 2β/t)`-TS partition whenever `2/t ≤ δ`. -/
theorem exists_tsPartition_of_padded {β δ : ℝ} {t : ℕ} (ht : 1 ≤ t) (hδ : (2 : ℝ) / t ≤ δ)
    (hG : AdmitsPadded G β δ) : Nonempty (TSPartition G t (2 * β / t)) := by
  obtain ⟨PD⟩ := hG t ht
  obtain ⟨idx, hdeg, hdiam⟩ := exists_degenerate_of_carve (G := G) t (2 * β / t)
    (fun L hL => exists_cluster_of_padded ht hδ PD L hL)
  exact ⟨TSPartition.ofDegenerate hdeg hdiam⟩

/-- **Theorem 1.4** of [Filtser–Fischer, PODC 2026], assuming padded decompositions: if every
graph of `𝒢` admits a `(β, δ)`-padded decomposition scheme (for `K_r`-minor-free graphs this is
Theorem 4.1 of Conroy–Filtser with `β = O(log r)`, `δ = Ω(1)`, not formalized here), then for
every `t` with `2/t ≤ δ` every 1-PLS for `P` with cost `p` yields a `(3t+2)`-PLS for `P` with cost
`4⌈log₂ n⌉ + 2⌈2β(2p+1)/t⌉ + 10 = O(⌈p/t⌉ + log n)`. -/
theorem tradeoff_of_padded [LinearOrder V] {ι : Type*} {𝒢 : Set (SimpleGraph V)}
    {P : SimpleGraph V → (V → ι) → Prop} {β δ : ℝ} (h𝒢 : ∀ G ∈ 𝒢, AdmitsPadded G β δ)
    {t p : ℕ} (ht : 1 ≤ t) (hδ : (2 : ℝ) / t ≤ δ) (S1 : PLS 𝒢 P 1) (hp : S1.CostLE p) :
    ∃ St : PLS 𝒢 P (3 * t + 2),
      St.CostLE (4 * Nat.clog 2 (Fintype.card V) + 2 * ⌈2 * β * (2 * p + 1) / t⌉₊ + 10) := by
  obtain ⟨S, hS⟩ := exists_tsCert 𝒢 t (2 * β / t)
  obtain ⟨St, hSt⟩ := tradeoff_of_tsCert S hS
    (fun G hG => exists_tsPartition_of_padded ht hδ (h𝒢 G hG)) S1 hp
  have hR : max (3 * t + 2) (2 * t + 2) = 3 * t + 2 := max_eq_left (by omega)
  have hε : 2 * β / t * (2 * p + 1) = 2 * β * (2 * p + 1) / t := by ring
  refine ⟨St.mono hR.le, fun G hG I hP v => ?_⟩
  have := hSt G hG I hP v
  rw [hε] at this
  rw [PLS.mono_prov]
  omega

end PLSTradeoff
