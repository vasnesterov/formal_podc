import Papers.PODC2024.LocalAdvice.Lemma32
import Podc.Probability.Finite.LocalLemma

/-!
# Lemma 32, part 2: selecting the candidates with the Lovász Local Lemma

For every `r ∈ R` choose `v_r ∈ Q_r` uniformly at random. For a node `u` of colour 1, the bad
event `A_u` is "`u` has neighbours in the candidate sets `S_{v_r} ∪ S'_{v_r}` of two different
`r`". As in the paper, the candidate sets of distinct pairs `(r, v)` are disjoint, so
`Pr[A_u] ≤ (Δ / 12Δ⁶)²`, and `A_u` shares variables with at most `Δ · 48Δ⁷ = 48Δ⁸` other events;
`e · Pr[A_u] · (48Δ⁸ + 1) < 1` and the symmetric local lemma
(`Cslib.Probability.exists_forall_not_of_symmetric`) gives a good selection. Together with
part 1 this proves **Lemma 32** (`lemma_32`).
-/

namespace Podc.LocalAdvice

open SimpleGraph Finset Cslib.Probability

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {φ : V → Fin 3} {Δ : ℕ}

omit [Fintype V] [DecidableRel G.Adj] in
lemma IsWitness.eq_of_mem_nbr0 [Fintype V] {S : Finset V} (h : IsWitness G φ S) {a b u : V}
    (ha : a ∈ S) (hb : b ∈ S) (hua : u ∈ nbr0 G φ a) (hub : u ∈ nbr0 G φ b) : a = b := by
  rcases h with ⟨w, rfl, -⟩ | ⟨x, y, rfl, -, hdisj⟩
  · simp only [mem_singleton] at ha hb; rw [ha, hb]
  · simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact absurd hub (Finset.disjoint_left.1 hdisj hua)
    · exact absurd hua (Finset.disjoint_left.1 hdisj hub)
    · rfl

namespace PreSchema

variable (π : PreSchema G φ Δ)

/-- The candidates `v ∈ Q r` whose candidate set contains a neighbour of `u`. -/
def hits (u r : V) : Finset V := (π.Q r).filter fun v => ∃ z ∈ π.K v, G.Adj u z

omit [DecidableRel G.Adj] in
lemma K_card_le {r v : V} (hr : r ∈ π.R) (hv : v ∈ π.Q r) : (π.K v).card ≤ 4 := by
  have h1 := (π.S_wit r hr v hv).card_le_two
  have h2 := (π.S'_wit r hr v hv).card_le_two
  exact (card_union_le _ _).trans (by omega)

omit [DecidableRel G.Adj] in
/-- Two nodes of a candidate set adjacent to the same node of colour 1 coincide. -/
lemma K_eq_of_adj {r v u z₁ z₂ : V} (hr : r ∈ π.R) (hv : v ∈ π.Q r) (hu : φ u = 0)
    (h₁ : z₁ ∈ π.K v) (h₂ : z₂ ∈ π.K v) (hu₁ : G.Adj u z₁) (hu₂ : G.Adj u z₂) : z₁ = z₂ := by
  have hS := π.S_wit r hr v hv
  have hS' := π.S'_wit r hr v hv
  have n₁ : u ∈ nbr0 G φ z₁ := mem_nbr0.2 ⟨hu₁.symm, hu⟩
  have n₂ : u ∈ nbr0 G φ z₂ := mem_nbr0.2 ⟨hu₂.symm, hu⟩
  rcases mem_union.1 h₁ with h₁ | h₁ <;> rcases mem_union.1 h₂ with h₂ | h₂
  · exact hS.eq_of_mem_nbr0 h₁ h₂ n₁ n₂
  · exact absurd n₁ (Finset.disjoint_left.1 ((π.S'_T hr hv h₂) z₁ h₁).2.2 n₂)
  · exact absurd n₂ (Finset.disjoint_left.1 ((π.S'_T hr hv h₁) z₂ h₂).2.2 n₁)
  · exact hS'.eq_of_mem_nbr0 h₁ h₂ n₁ n₂

/-- The neighbours of `u` meet at most `Δ` candidate sets (counted over all `r`):
`∑_r #(hits u r) ≤ Δ`. -/
lemma sum_card_hits_le (hdeg : ∀ v, G.degree v ≤ Δ) (hΔ : 1 ≤ Δ) (u : V) :
    ∑ r ∈ π.R, (π.hits u r).card ≤ Δ := by
  classical
  -- each neighbour `z` lies in at most one candidate set
  have hz : ∀ z, ∑ r ∈ π.R, ((π.Q r).filter fun v => z ∈ π.K v).card ≤ 1 := by
    intro z
    rw [← card_biUnion]
    · refine card_le_one.2 fun a ha b hb => ?_
      simp only [mem_biUnion, mem_filter] at ha hb
      obtain ⟨r, hr, ha, hza⟩ := ha
      obtain ⟨r', hr', hb, hzb⟩ := hb
      exact (π.K_unique hΔ hr hr' ha hb hza hzb).2
    · intro r hr r' hr' hne
      rw [Function.onFun, Finset.disjoint_left]
      intro a ha hb
      simp only [mem_filter] at ha hb
      exact hne (π.K_unique hΔ hr hr' ha.1 hb.1 ha.2 hb.2).1
  calc ∑ r ∈ π.R, (π.hits u r).card
      ≤ ∑ r ∈ π.R, ∑ z ∈ G.neighborFinset u, ((π.Q r).filter fun v => z ∈ π.K v).card := by
        refine sum_le_sum fun r _ => (card_le_card ?_).trans card_biUnion_le
        intro v hv
        simp only [hits, mem_filter] at hv
        obtain ⟨hvQ, z, hzK, huz⟩ := hv
        simp only [mem_biUnion, mem_filter, mem_neighborFinset]
        exact ⟨z, huz, hvQ, hzK⟩
    _ = ∑ z ∈ G.neighborFinset u, ∑ r ∈ π.R, ((π.Q r).filter fun v => z ∈ π.K v).card :=
        sum_comm
    _ ≤ ∑ _z ∈ G.neighborFinset u, 1 := sum_le_sum fun z _ => hz z
    _ = G.degree u := by rw [sum_const, smul_eq_mul, mul_one, card_neighborFinset_eq_degree]
    _ ≤ Δ := hdeg u

/-- At most `48Δ⁷` nodes have a neighbour in a candidate set of `Q_r`. -/
lemma card_filter_hits_le (hdeg : ∀ v, G.degree v ≤ Δ) {r : V} (hr : r ∈ π.R) :
    (univ.filter fun u => (π.hits u r).Nonempty).card ≤ 48 * Δ ^ 7 := by
  classical
  calc (univ.filter fun u => (π.hits u r).Nonempty).card
      ≤ ((π.Q r).biUnion fun v => (π.K v).biUnion fun z => G.neighborFinset z).card := by
        refine card_le_card fun u hu => ?_
        simp only [mem_filter, mem_univ, true_and] at hu
        obtain ⟨v, hv⟩ := hu
        simp only [hits, mem_filter] at hv
        obtain ⟨hvQ, z, hzK, huz⟩ := hv
        simp only [mem_biUnion, mem_neighborFinset]
        exact ⟨v, hvQ, z, hzK, huz.symm⟩
    _ ≤ ∑ v ∈ π.Q r, ((π.K v).biUnion fun z => G.neighborFinset z).card := card_biUnion_le
    _ ≤ ∑ _v ∈ π.Q r, 4 * Δ := by
        refine sum_le_sum fun v hv => card_biUnion_le.trans ?_
        calc ∑ z ∈ π.K v, (G.neighborFinset z).card ≤ ∑ _z ∈ π.K v, Δ :=
              sum_le_sum fun z _ => by rw [card_neighborFinset_eq_degree]; exact hdeg z
          _ = (π.K v).card * Δ := by rw [sum_const, smul_eq_mul]
          _ ≤ 4 * Δ := Nat.mul_le_mul_right _ (π.K_card_le hr hv)
    _ = 48 * Δ ^ 7 := by rw [sum_const, smul_eq_mul, π.Q_card r hr]; ring

/-- The real-number inequality `e · (Δ / 12Δ⁶)² · (48Δ⁸ + 1) ≤ 1` of the paper's LLL application. -/
lemma lll_numeric (hΔ : 1 ≤ Δ) :
    Real.exp 1 * (((Δ : ℝ) / (12 * (Δ : ℝ) ^ 6)) ^ 2) * ((48 * Δ ^ 8 : ℕ) + 1 : ℝ) ≤ 1 := by
  have hx : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hx0 : (0 : ℝ) < Δ := by linarith
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h8 : (1 : ℝ) ≤ (Δ : ℝ) ^ 8 := one_le_pow₀ hx
  have h10 : (Δ : ℝ) ^ 8 ≤ (Δ : ℝ) ^ 10 := pow_le_pow_right₀ hx (by norm_num)
  have hp : ((Δ : ℝ) / (12 * (Δ : ℝ) ^ 6)) ^ 2 = 1 / (144 * (Δ : ℝ) ^ 10) := by
    field_simp; ring
  rw [hp]
  push_cast
  rw [mul_one_div, div_mul_eq_mul_div, div_le_one (by positivity)]
  nlinarith [Real.exp_pos 1]

/-! ### The LLL instance -/

/-- The variables: one per ruling-set node. -/
abbrev Idx : Type _ := {r // r ∈ π.R}

/-- The range of the variable of `r`: the candidates `Q_r`. -/
abbrev Cand (r : π.Idx) : Type _ := {v // v ∈ π.Q r.1}

/-- `u` has a neighbour in the candidate set of `a`. -/
def hit (u : V) (r : π.Idx) (a : π.Cand r) : Prop := ∃ z ∈ π.K a.1, G.Adj u z

/-- The bad event `A_u`: `u` (of colour 1) has neighbours in the selected candidate sets of two
different `r`. -/
def bad (u : V) (σ : ∀ r : π.Idx, π.Cand r) : Prop :=
  φ u = 0 ∧ ∃ r r' : π.Idx, r ≠ r' ∧ π.hit u r (σ r) ∧ π.hit u r' (σ r')

/-- The variables the event `A_u` depends on. -/
noncomputable def vbl (u : V) : Finset π.Idx :=
  open scoped Classical in univ.filter fun r => (π.hits u r.1).Nonempty

lemma mem_vbl_of_hit {u : V} {r : π.Idx} {a : π.Cand r} (h : π.hit u r a) : r ∈ π.vbl u := by
  classical
  simp only [vbl, mem_filter, mem_univ, true_and]
  exact ⟨a.1, by simp only [PreSchema.hits, mem_filter]; exact ⟨a.2, h⟩⟩

lemma bad_congr (u : V) (σ τ : ∀ r : π.Idx, π.Cand r) (h : ∀ r ∈ π.vbl u, σ r = τ r) :
    π.bad u σ ↔ π.bad u τ := by
  have key : ∀ σ τ : ∀ r : π.Idx, π.Cand r, (∀ r ∈ π.vbl u, σ r = τ r) →
      π.bad u σ → π.bad u τ := by
    rintro σ τ h ⟨hu, r, r', hne, h1, h2⟩
    refine ⟨hu, r, r', hne, ?_, ?_⟩
    · rw [← h r (π.mem_vbl_of_hit h1)]; exact h1
    · rw [← h r' (π.mem_vbl_of_hit h2)]; exact h2
  exact ⟨key σ τ h, key τ σ fun r hr => (h r hr).symm⟩

omit [DecidableRel G.Adj] in
lemma card_cand (r : π.Idx) : Fintype.card (π.Cand r) = 12 * Δ ^ 6 := by
  simp only [Cand, Fintype.card_coe]; exact π.Q_card r.1 r.2

lemma card_hit_eq (u : V) (r : π.Idx) [DecidablePred (π.hit u r)] :
    (univ.filter fun a : π.Cand r => π.hit u r a).card = (π.hits u r.1).card := by
  classical
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1
  ext v
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.subtype_apply, hits]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, ha⟩
  · rintro ⟨hv, h⟩; exact ⟨⟨v, hv⟩, h, rfl⟩

lemma uprob_hit_le (u : V) (r : π.Idx) :
    uprob (fun σ : ∀ r, π.Cand r => π.hit u r (σ r)) ≤
      ((π.hits u r.1).card : ℝ) / (12 * (Δ : ℝ) ^ 6) := by
  classical
  have h := uprob_and_le_fiber (A := fun _ : ∀ r, π.Cand r => True)
    (B := fun σ : ∀ r, π.Cand r => π.hit u r (σ r)) r (fun _ _ => Iff.rfl)
    (q := ((π.hits u r.1).card : ℝ) / (12 * (Δ : ℝ) ^ 6)) (fun x => by
      simp only [Function.update_self]
      rw [uprob_eq_card_filter, π.card_cand r]
      have : (univ.filter fun a : π.Cand r => π.hit u r a).card = (π.hits u r.1).card := by
        convert π.card_hit_eq u r
      rw [this]; push_cast; rfl)
  simp only [true_and] at h
  exact h.trans (mul_le_of_le_one_right (by positivity) (uprob_le_one _))

lemma uprob_bad_le (hdeg : ∀ v, G.degree v ≤ Δ) (hΔ : 1 ≤ Δ) (u : V) :
    uprob (π.bad u) ≤ ((Δ : ℝ) / (12 * (Δ : ℝ) ^ 6)) ^ 2 := by
  classical
  set q : ℝ := 12 * (Δ : ℝ) ^ 6
  have hsum : ∑ r : π.Idx, ((π.hits u r.1).card : ℝ) / q ≤ (Δ : ℝ) / q := by
    rw [← Finset.sum_div]
    gcongr
    have := π.sum_card_hits_le hdeg hΔ u
    rw [← Finset.sum_coe_sort π.R] at this
    exact_mod_cast this
  by_cases hu : φ u = 0
  · have h1 : uprob (π.bad u) ≤ uprob (fun σ : ∀ r, π.Cand r => ∃ r ∈ (univ : Finset π.Idx),
        ∃ r' ∈ univ.erase r, π.hit u r (σ r) ∧ π.hit u r' (σ r')) := by
      apply uprob_mono
      rintro σ ⟨-, r, r', hne, h1, h2⟩
      exact ⟨r, mem_univ _, r', mem_erase.2 ⟨hne.symm, mem_univ _⟩, h1, h2⟩
    refine h1.trans ((uprob_exists_le _ _).trans ?_)
    calc ∑ r : π.Idx, uprob (fun σ : ∀ r, π.Cand r => ∃ r' ∈ univ.erase r, π.hit u r (σ r) ∧ π.hit u r' (σ r'))
        ≤ ∑ r : π.Idx, ∑ r' ∈ univ.erase r,
            uprob (fun σ : ∀ r, π.Cand r => π.hit u r (σ r) ∧ π.hit u r' (σ r')) :=
          sum_le_sum fun r _ => uprob_exists_le _ _
      _ ≤ ∑ r : π.Idx, ∑ r' : π.Idx, ((π.hits u r.1).card : ℝ) / q *
            (((π.hits u r'.1).card : ℝ) / q) := by
          refine sum_le_sum fun r _ => ?_
          refine (sum_le_sum fun r' hr' => ?_).trans
            (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => by positivity)
          have hne : r' ≠ r := (mem_erase.1 hr').1
          rw [uprob_and_eq_mul_of_dependsOn {r}
            (fun σ τ h => by rw [h r (mem_singleton_self r)])
            (fun σ τ h => by rw [h r' (by simpa using hne)])]
          exact mul_le_mul (π.uprob_hit_le u r) (π.uprob_hit_le u r') (uprob_nonneg _)
            (by positivity)
      _ = (∑ r : π.Idx, ((π.hits u r.1).card : ℝ) / q) ^ 2 := by
          rw [sq, Finset.sum_mul_sum]
      _ ≤ ((Δ : ℝ) / q) ^ 2 := by
          gcongr
  · calc uprob (π.bad u) ≤ uprob (fun _ : ∀ r, π.Cand r => False) :=
          uprob_mono fun σ h => hu h.1
      _ = 0 := uprob_false
      _ ≤ _ := by positivity

lemma card_vbl_le (hdeg : ∀ v, G.degree v ≤ Δ) (hΔ : 1 ≤ Δ) (u : V) : (π.vbl u).card ≤ Δ := by
  classical
  calc (π.vbl u).card = ∑ r ∈ π.vbl u, 1 := by rw [card_eq_sum_ones]
    _ ≤ ∑ r ∈ π.vbl u, (π.hits u r.1).card := sum_le_sum fun r hr => by
        simp only [vbl, mem_filter, mem_univ, true_and] at hr
        exact hr.card_pos
    _ ≤ ∑ r : π.Idx, (π.hits u r.1).card :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _
    _ = ∑ r ∈ π.R, (π.hits u r).card := by
        convert Finset.sum_coe_sort π.R (fun r => (π.hits u r).card)
    _ ≤ Δ := π.sum_card_hits_le hdeg hΔ u

lemma card_dependencyNbhd_le (hdeg : ∀ v, G.degree v ≤ Δ) (hΔ : 1 ≤ Δ) (u : V) :
    (dependencyNbhd π.vbl u).card ≤ 48 * Δ ^ 8 := by
  classical
  have hsub : dependencyNbhd π.vbl u ⊆
      (π.vbl u).biUnion fun r => univ.filter fun u' => (π.hits u' r.1).Nonempty := by
    intro u' hu'
    rw [mem_dependencyNbhd, Finset.not_disjoint_iff] at hu'
    obtain ⟨-, r, hr, hr'⟩ := hu'
    simp only [vbl, mem_filter, mem_univ, true_and] at hr'
    exact mem_biUnion.2 ⟨r, hr, by simpa using hr'⟩
  calc (dependencyNbhd π.vbl u).card
      ≤ ∑ r ∈ π.vbl u, (univ.filter fun u' => (π.hits u' r.1).Nonempty).card :=
        (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _r ∈ π.vbl u, 48 * Δ ^ 7 := sum_le_sum fun r _ => π.card_filter_hits_le hdeg r.2
    _ = (π.vbl u).card * (48 * Δ ^ 7) := by rw [sum_const, smul_eq_mul]
    _ ≤ Δ * (48 * Δ ^ 7) := Nat.mul_le_mul_right _ (π.card_vbl_le hdeg hΔ u)
    _ = 48 * Δ ^ 8 := by ring

end PreSchema

/-- **Lemma 32, second part**: a selection `v_r ∈ Q_r` such that every node of colour 1 has at
most one neighbour in the union of the selected candidate sets exists (Lovász Local Lemma). -/
theorem exists_sel (hdeg : ∀ v, G.degree v ≤ Δ) (hΔ : 1 ≤ Δ) (π : PreSchema G φ Δ) :
    ∃ sel : V → V, (∀ r ∈ π.R, sel r ∈ π.Q r) ∧ ∀ u, φ u = 0 →
      (nbrIn G u (π.R.biUnion fun r => π.S (sel r) ∪ π.S' (sel r))).card ≤ 1 := by
  classical
  have hqpos : 0 < 12 * Δ ^ 6 := by have := pow_chain hΔ; omega
  have : ∀ r : π.Idx, Nonempty (π.Cand r) := fun r =>
    Fintype.card_pos_iff.1 (by rw [π.card_cand r]; exact hqpos)
  obtain ⟨σ, hσ⟩ := exists_forall_not_of_symmetric (A := π.bad) π.bad_congr
    (((Δ : ℝ) / (12 * (Δ : ℝ) ^ 6)) ^ 2) (48 * Δ ^ 8) (π.uprob_bad_le hdeg hΔ)
    (π.card_dependencyNbhd_le hdeg hΔ) (PreSchema.lll_numeric hΔ)
  refine ⟨fun r => if h : r ∈ π.R then (σ ⟨r, h⟩).1 else r, fun r hr => by
    simp only [dite_eq_left hr]; exact (σ ⟨r, hr⟩).2, fun u hu => ?_⟩
  refine card_le_one.2 fun z₁ h₁ z₂ h₂ => ?_
  rw [mem_nbrIn, mem_biUnion] at h₁ h₂
  obtain ⟨hu₁, r₁, hr₁, hz₁⟩ := h₁
  obtain ⟨hu₂, r₂, hr₂, hz₂⟩ := h₂
  simp only [dite_eq_left hr₁] at hz₁
  simp only [dite_eq_left hr₂] at hz₂
  by_cases hr : r₁ = r₂
  · subst hr
    exact π.K_eq_of_adj hr₁ (σ ⟨r₁, hr₁⟩).2 hu hz₁ hz₂ hu₁ hu₂
  · exact absurd ⟨hu, ⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩, fun h => hr (congrArg Subtype.val h),
      ⟨z₁, hz₁, hu₁⟩, ⟨z₂, hz₂, hu₂⟩⟩ (hσ u)

/-- **Lemma 32** of [Balliu et al., arXiv:2405.04519]: the encoding schema is well-defined, i.e.
for a greedy 3-colouring of a graph of maximum degree `≤ Δ` (`Δ ≥ 1`) all objects it chooses
exist. -/
theorem lemma_32 (hφ : IsGreedy G φ) (hdeg : ∀ v, G.degree v ≤ Δ) (hΔ : 1 ≤ Δ) :
    Nonempty (Schema G φ Δ) := by
  obtain ⟨π⟩ := exists_preSchema hφ hdeg hΔ
  obtain ⟨sel, hsel, hgood⟩ := exists_sel hdeg hΔ π
  exact ⟨{ π with sel := sel, sel_mem := hsel, sel_good := hgood }⟩

end Podc.LocalAdvice
