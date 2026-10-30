import Papers.PODC2024.LocalAdvice.Schema

/-!
# Lemma 32 (well-definedness of the encoding schema), part 1: everything but the selection

We construct the ruling set `R`, the sets `Q_r`, the witness sets `S_v`, the paths `P_v` inside
`T_v` and the witness sets `S'_v` (`exists_preSchema`). The selection of the candidates `v_{r,C}`
by the Lovász Local Lemma is in `Lemma32LLL.lean`.
-/

namespace Podc.LocalAdvice

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {φ : V → Fin 3} {Δ : ℕ}

omit [Fintype V] [LinearOrder V] [DecidableRel G.Adj] in
/-- Distances along a geodesic from `r` give lower bounds on distances between its nodes. -/
lemma sub_le_edist {H : SimpleGraph V} {r a b : V} {m n : ℕ} (ha : H.edist r a = m)
    (hb : H.edist r b = n) : ((n - m : ℕ) : ℕ∞) ≤ H.edist a b := by
  have htri : H.edist r b ≤ H.edist r a + H.edist a b := H.edist_triangle
  rw [ha, hb] at htri
  rcases eq_or_ne (H.edist a b) ⊤ with h | h
  · rw [h]; exact le_top
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h
  rw [← hk] at htri ⊢
  have : n ≤ m + k := by exact_mod_cast htri
  exact_mod_cast (by omega : n - m ≤ k)

omit [Fintype V] [LinearOrder V] [DecidableRel G.Adj] in
lemma inj_of_geodesic {H : SimpleGraph V} {u : V} {f : ℕ → V} {k : ℕ}
    (hd : ∀ i ≤ k, H.edist u (f i) = i) : ∀ i ≤ k, ∀ j ≤ k, f i = f j → i = j := by
  intro i hi j hj hij
  have := hd i hi
  rw [hij, hd j hj] at this
  exact_mod_cast this.symm

/-! ### The ruling set -/

omit [DecidableRel G.Adj] in
/-- A maximal set of large nodes with pairwise distances `≥ A` is an `(A, A)`-ruling set. -/
lemma exists_rulingSet (A D : ℕ) :
    ∃ R : Finset V, (∀ r ∈ R, φ r ≠ 0 ∧ IsLarge (H23 G φ) D r) ∧
      (∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → (A : ℕ∞) ≤ (H23 G φ).edist r r') ∧
      ∀ u, φ u ≠ 0 → IsLarge (H23 G φ) D u → ∃ r ∈ R, (H23 G φ).edist u r ≤ A := by
  classical
  let L : Finset V := univ.filter fun u => φ u ≠ 0 ∧ IsLarge (H23 G φ) D u
  let Sep : Finset V → Prop := fun S =>
    ∀ r ∈ S, ∀ r' ∈ S, r ≠ r' → (A : ℕ∞) ≤ (H23 G φ).edist r r'
  let F := L.powerset.filter Sep
  have hF : F.Nonempty := ⟨∅, by simp [F, Sep]⟩
  obtain ⟨R, hRF, hmax⟩ := F.exists_max_image card hF
  simp only [F, mem_filter, mem_powerset] at hRF
  refine ⟨R, fun r hr => by simpa [L] using hRF.1 hr, hRF.2, fun u hu hL => ?_⟩
  by_contra hno
  push Not at hno
  have huR : u ∉ R := fun h => by
    have := hno u h; simp at this
  have hins : insert u R ∈ F := by
    simp only [F, mem_filter, mem_powerset]
    refine ⟨insert_subset (by simp [L, hu, hL]) hRF.1, ?_⟩
    intro r hr r' hr' hne
    rw [mem_insert] at hr hr'
    rcases hr with rfl | hr <;> rcases hr' with rfl | hr'
    · exact absurd rfl hne
    · exact (hno r' hr').le
    · rw [edist_comm]; exact (hno r hr).le
    · exact hRF.2 r hr r' hr' hne
  have := hmax _ hins
  rw [card_insert_of_notMem huR] at this
  omega

/-! ### The sets `Q_r` -/

omit [Fintype V] [DecidableRel G.Adj] in
lemma exists_Q (hΔ : 1 ≤ Δ) (r : V) : ∃ Q : Finset V, IsLarge (H23 G φ) (4000 * Δ ^ 9) r →
    Q.card = 12 * Δ ^ 6 ∧ (∀ v ∈ Q, (H23 G φ).edist r v ≤ (600 * Δ ^ 9 : ℕ)) ∧
    ∀ v ∈ Q, ∀ w ∈ Q, v ≠ w → ((50 * Δ ^ 3 : ℕ) : ℕ∞) ≤ (H23 G φ).edist v w := by
  by_cases hL : IsLarge (H23 G φ) (4000 * Δ ^ 9) r
  swap
  · exact ⟨∅, fun h => absurd h hL⟩
  have hc := pow_chain hΔ
  obtain ⟨f, -, -, hd⟩ := hL.exists_geodesic (m := 600 * Δ ^ 9) (by omega)
  set c := 50 * Δ ^ 3 with hcdef
  have hcpos : 0 < c := by omega
  have hidx : ∀ i ∈ Icc 1 (12 * Δ ^ 6), i * c ≤ 600 * Δ ^ 9 := by
    intro i hi
    rw [mem_Icc] at hi
    calc i * c ≤ (12 * Δ ^ 6) * c := Nat.mul_le_mul_right _ hi.2
      _ = 600 * Δ ^ 9 := by rw [hcdef]; ring
  have hdi : ∀ i ∈ Icc 1 (12 * Δ ^ 6), (H23 G φ).edist r (f (i * c)) = (i * c : ℕ) :=
    fun i hi => hd _ (hidx i hi)
  refine ⟨(Icc 1 (12 * Δ ^ 6)).image fun i => f (i * c), fun _ => ⟨?_, ?_, ?_⟩⟩
  · rw [card_image_of_injOn, Nat.card_Icc]
    · omega
    intro i hi j hj hij
    have h1 := hdi i hi
    simp only at hij
    rw [hij, hdi j hj] at h1
    have : j * c = i * c := by exact_mod_cast h1
    exact (Nat.eq_of_mul_eq_mul_right hcpos this).symm
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hv
    rw [hdi i hi]; exact_mod_cast hidx i hi
  · intro v hv w hw hne
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hv
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hw
    have hij : i ≠ j := fun h => hne (by rw [h])
    rcases lt_or_gt_of_ne hij with h | h
    · have := sub_le_edist (hdi i hi) (hdi j hj)
      refine le_trans (Nat.cast_le.2 ?_) this
      have : (i + 1) * c ≤ j * c := Nat.mul_le_mul_right _ h
      rw [add_mul] at this; omega
    · have := sub_le_edist (hdi j hj) (hdi i hi)
      rw [edist_comm]
      refine le_trans (Nat.cast_le.2 ?_) this
      have : (j + 1) * c ≤ i * c := Nat.mul_le_mul_right _ h
      rw [add_mul] at this; omega

/-! ### The witness sets `S_v`, the paths `P_v` and the witness sets `S'_v` -/

omit [LinearOrder V] [DecidableRel G.Adj] in
lemma IsWitness.card_le_two [DecidableEq V] {S : Finset V} (h : IsWitness G φ S) : S.card ≤ 2 := by
  rcases h with ⟨w, rfl, -⟩ | ⟨x, y, rfl, -⟩
  · simp
  · exact card_insert_le _ _

omit [LinearOrder V] in
lemma card_nbr0_le (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) : (nbr0 G φ v).card ≤ Δ := by
  refine le_trans (card_le_card ?_) ((card_neighborFinset_eq_degree G v).le.trans (hdeg v))
  intro w hw; rw [mem_nbr0] at hw; simpa using hw.1

/-- The complement of `T_S` is small: at most `2 + 2Δ + 2Δ²` nodes. -/
lemma exists_bad_set (hdeg : ∀ v, G.degree v ≤ Δ) (hΔ : 1 ≤ Δ) {S : Finset V}
    (hS : IsWitness G φ S) :
    ∃ B : Finset V, B.card ≤ 6 * Δ ^ 2 ∧ ∀ z, z ∉ B → InT G φ S z := by
  have hc := pow_chain hΔ
  let B := S ∪ S.biUnion (fun y => G.neighborFinset y) ∪
    S.biUnion (fun y => (nbr0 G φ y).biUnion fun u => G.neighborFinset u)
  refine ⟨B, ?_, ?_⟩
  · dsimp only [B]
    have h2 := hS.card_le_two
    have e1 : (S.biUnion fun y => G.neighborFinset y).card ≤ 2 * Δ := by
      refine (card_biUnion_le).trans ?_
      calc ∑ y ∈ S, (G.neighborFinset y).card ≤ ∑ _y ∈ S, Δ := sum_le_sum fun y _ => by
            rw [card_neighborFinset_eq_degree]; exact hdeg y
        _ = S.card * Δ := by rw [sum_const, smul_eq_mul]
        _ ≤ 2 * Δ := Nat.mul_le_mul_right _ h2
    have e2 : (S.biUnion fun y => (nbr0 G φ y).biUnion fun u => G.neighborFinset u).card ≤
        2 * Δ ^ 2 := by
      refine (card_biUnion_le).trans ?_
      calc ∑ y ∈ S, ((nbr0 G φ y).biUnion fun u => G.neighborFinset u).card
          ≤ ∑ _y ∈ S, Δ * Δ := sum_le_sum fun y _ => by
            refine (card_biUnion_le).trans ?_
            calc ∑ u ∈ nbr0 G φ y, (G.neighborFinset u).card ≤ ∑ _u ∈ nbr0 G φ y, Δ :=
                  sum_le_sum fun u _ => by rw [card_neighborFinset_eq_degree]; exact hdeg u
              _ = (nbr0 G φ y).card * Δ := by rw [sum_const, smul_eq_mul]
              _ ≤ Δ * Δ := Nat.mul_le_mul_right _ (card_nbr0_le hdeg y)
        _ = S.card * (Δ * Δ) := by rw [sum_const, smul_eq_mul]
        _ ≤ 2 * Δ ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ h2
    have := card_union_le (S ∪ S.biUnion fun y => G.neighborFinset y)
      (S.biUnion fun y => (nbr0 G φ y).biUnion fun u => G.neighborFinset u)
    have := card_union_le S (S.biUnion fun y => G.neighborFinset y)
    omega
  · intro z hz y hy
    simp only [B, mem_union, mem_biUnion, not_or, not_exists, not_and] at hz
    refine ⟨fun h => hz.1.1 (h ▸ hy), fun h => hz.1.2 y hy (by simpa using h.symm), ?_⟩
    rw [Finset.disjoint_left]
    intro u hu hu'
    exact hz.2 y hy u hu' (by simpa using (mem_nbr0.1 hu).1.symm)

/-- **Existence of `S_v`, `v'`, `P_v` and `S'_v`** for a node `v` of a large component. -/
lemma exists_SP (hφ : IsGreedy G φ) (hdeg : ∀ v, G.degree v ≤ Δ) (hΔ : 1 ≤ Δ) (v : V) :
    ∃ (S : Finset V) (v' : V) (P : ℕ → V) (S' : Finset V),
      (φ v ≠ 0 ∧ IsLarge (H23 G φ) (4000 * Δ ^ 9) v) →
      IsWitness G φ S ∧ (∀ z ∈ S, (H23 G φ).edist v z ≤ Δ) ∧
      (H23 G φ).edist v v' ≤ (20 * Δ ^ 3 : ℕ) ∧ P 0 = v' ∧
      (∀ i < Δ, (H23 G φ).Adj (P i) (P (i + 1))) ∧
      (∀ i ≤ Δ, ∀ j ≤ Δ, P i = P j → i = j) ∧ (∀ i ≤ Δ, InT G φ S (P i)) ∧
      IsWitness G φ S' ∧ ∀ z ∈ S', ∃ i ≤ Δ, z = P i := by
  by_cases hv : φ v ≠ 0 ∧ IsLarge (H23 G φ) (4000 * Δ ^ 9) v
  swap
  · exact ⟨∅, v, fun _ => v, ∅, fun h => absurd h hv⟩
  obtain ⟨hv0, hL⟩ := hv
  have hc := pow_chain hΔ
  -- `S_v` on a geodesic of length `Δ`
  obtain ⟨f, hf0, hfadj, hfd⟩ := hL.exists_geodesic (m := Δ) (by omega)
  obtain ⟨S, hS, hSf⟩ := exists_witness_on_path hφ hdeg f (hf0 ▸ hv0) hfadj
    (inj_of_geodesic hfd)
  have hSnear : ∀ z ∈ S, (H23 G φ).edist v z ≤ Δ := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := hSf z hz
    rw [hfd i hi]; exact_mod_cast hi
  -- a geodesic of length `20Δ³` and a block of `Δ + 1` consecutive nodes inside `T_v`
  obtain ⟨B, hBcard, hB⟩ := exists_bad_set hdeg hΔ hS
  obtain ⟨g, hg0, hgadj, hgd⟩ := hL.exists_geodesic (m := 20 * Δ ^ 3) (by omega)
  have hginj := inj_of_geodesic hgd
  have hblock : ∀ j < 6 * Δ ^ 2 + 1, ∀ i ≤ Δ, j * (Δ + 1) + i ≤ 20 * Δ ^ 3 := by
    intro j hj i hi
    have : j * (Δ + 1) ≤ 6 * Δ ^ 2 * (Δ + 1) := Nat.mul_le_mul_right _ (by omega)
    have e : 6 * Δ ^ 2 * (Δ + 1) = 6 * Δ ^ 3 + 6 * Δ ^ 2 := by ring
    omega
  have hdiv : ∀ j i, i ≤ Δ → (j * (Δ + 1) + i) / (Δ + 1) = j := by
    intro j i hi
    rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  obtain ⟨j, hj, hgood⟩ : ∃ j < 6 * Δ ^ 2 + 1, ∀ i ≤ Δ, g (j * (Δ + 1) + i) ∉ B := by
    by_contra hall
    push Not at hall
    choose ij hij hijB using hall
    let φj : ℕ → V := fun j => if h : j < 6 * Δ ^ 2 + 1 then g (j * (Δ + 1) + ij j h) else v
    have hmaps : ∀ j ∈ range (6 * Δ ^ 2 + 1), φj j ∈ B := by
      intro j hj
      rw [mem_range] at hj
      simp only [φj, dite_eq_left hj]; exact hijB j hj
    have hinj : Set.InjOn φj (range (6 * Δ ^ 2 + 1)) := by
      intro a ha b hb hab
      simp only [coe_range, Set.mem_Iio] at ha hb
      simp only [φj, dite_eq_left ha, dite_eq_left hb] at hab
      have := hginj _ (hblock a ha _ (hij a ha)) _ (hblock b hb _ (hij b hb)) hab
      rw [← hdiv a (ij a ha) (hij a ha), ← hdiv b (ij b hb) (hij b hb), this]
    have := card_le_card_of_injOn φj hmaps hinj
    rw [card_range] at this
    omega
  let P : ℕ → V := fun i => g (j * (Δ + 1) + i)
  have hPadj : ∀ i < Δ, (H23 G φ).Adj (P i) (P (i + 1)) := by
    intro i hi
    have := hgadj (j * (Δ + 1) + i) (by have := hblock j hj (i + 1) (by omega); omega)
    simpa [P, add_assoc] using this
  have hPinj : ∀ i ≤ Δ, ∀ i' ≤ Δ, P i = P i' → i = i' := by
    intro i hi i' hi' h
    have := hginj _ (hblock j hj i hi) _ (hblock j hj i' hi') h
    omega
  have hP0 : φ (P 0) ≠ 0 := by
    have := hgd (j * (Δ + 1)) (by simpa using hblock j hj 0 (by omega))
    have hP0' : P 0 = g (j * (Δ + 1)) := by simp [P]
    exact H23_edist_ne_zero (G := G) (a := v) (n := j * (Δ + 1)) (by rw [hP0', this]) hv0
  obtain ⟨S', hS', hS'P⟩ := exists_witness_on_path hφ hdeg P hP0 hPadj hPinj
  refine ⟨S, P 0, P, S', fun _ => ⟨hS, hSnear, ?_, rfl, hPadj, hPinj,
    fun i hi => hB _ (hgood i hi), hS', hS'P⟩⟩
  have := hgd (j * (Δ + 1)) (by simpa using hblock j hj 0 (by omega))
  simp only [P, add_zero, this]
  exact_mod_cast (by simpa using hblock j hj 0 (by omega))

/-- **Lemma 32, first part**: all objects of the encoding schema up to the final selection exist. -/
theorem exists_preSchema (hφ : IsGreedy G φ) (hdeg : ∀ v, G.degree v ≤ Δ) (hΔ : 1 ≤ Δ) :
    Nonempty (PreSchema G φ Δ) := by
  obtain ⟨R, hR, hRsep, hRdom⟩ := exists_rulingSet (G := G) (φ := φ) (2000 * Δ ^ 9) (4000 * Δ ^ 9)
  choose Q hQ using exists_Q (G := G) (φ := φ) hΔ
  choose S v' P S' hSP using exists_SP hφ hdeg hΔ
  have hQv : ∀ r ∈ R, ∀ v ∈ Q r, φ v ≠ 0 ∧ IsLarge (H23 G φ) (4000 * Δ ^ 9) v := by
    intro r hr v hv
    have h := (hQ r (hR r hr).2).2.1 v hv
    exact ⟨H23_edist_ne_zero h (hR r hr).1,
      (hR r hr).2.of_reachable (SimpleGraph.reachable_of_edist_le_natCast h)⟩
  exact ⟨{
    R := R, Q := Q, S := S, v' := v', P := P, S' := S'
    R_large := fun r hr => (hR r hr).2
    R_sep := hRsep
    R_dom := hRdom
    Q_card := fun r hr => (hQ r (hR r hr).2).1
    Q_near := fun r hr => (hQ r (hR r hr).2).2.1
    Q_sep := fun r hr => (hQ r (hR r hr).2).2.2
    S_wit := fun r hr v hv => (hSP v (hQv r hr v hv)).1
    S_near := fun r hr v hv => (hSP v (hQv r hr v hv)).2.1
    v'_near := fun r hr v hv => (hSP v (hQv r hr v hv)).2.2.1
    P_zero := fun r hr v hv => (hSP v (hQv r hr v hv)).2.2.2.1
    P_adj := fun r hr v hv => (hSP v (hQv r hr v hv)).2.2.2.2.1
    P_inj := fun r hr v hv => (hSP v (hQv r hr v hv)).2.2.2.2.2.1
    P_T := fun r hr v hv => (hSP v (hQv r hr v hv)).2.2.2.2.2.2.1
    S'_wit := fun r hr v hv => (hSP v (hQv r hr v hv)).2.2.2.2.2.2.2.1
    S'_P := fun r hr v hv => (hSP v (hQv r hr v hv)).2.2.2.2.2.2.2.2 }⟩

end Podc.LocalAdvice
