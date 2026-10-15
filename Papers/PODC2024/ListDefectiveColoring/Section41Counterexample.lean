import Papers.PODC2024.ListDefectiveColoring.Section41

/-!
# The paper's defect function (10) breaks Section 4.1 of [FK24]

Fuchs, Kuhn. *Simpler and More General Distributed Coloring Based on Simple List Defective
Coloring Algorithms* (PODC 2024; arXiv:2405.04648), cited as [FK24].

Section 4.1 defines the modified defects (eq. (10))
`d'_v(x) := ⌊(d_v(x) + 1) / (7θ)⌋ - 1` and claims that they are non-negative and satisfy
`∑_{x ∈ L_v} (d'_v(x) + 1) ≥ (1/(7θ)) ∑_{x ∈ L_v} (d_v(x) + 1)` (eq. (11)). Both claims fail as soon
as `d_v(x) + 1 < 7θ`: then `d'_v(x) = -1`.

With negative defects, condition (12) never holds, so all lists `L_{v,i}` and all sets `H_i` are
empty and *no node is ever coloured* (`it_eq_none_of_neg`); the run that colours nothing is a
valid run (`isRun_none_of_neg`). Concretely, on the triangle `K₃` (maximum degree `2`, so `Δ = 2`
needs no convention) with `θ = 1`, `S = 1`, zero defects (proper list colouring) and lists of size
`85`, all hypotheses of Theorem 1.4 hold (slack `85 > 84 = 42 θ log Δ · S · deg(v)`, and also
`85 > 21 θ (⌈log Δ⌉ + 1) S deg(v)`), but the Section 4.1 algorithm *as defined with eq. (10)*
colours no node (`theorem_1_4_paper_defects_false`). This is a floor/ceiling slip in eq. (10): the
paper itself states `d' ≥ 0`, and `⌈(d+1)/(7θ)⌉ - 1 = ⌊d/(7θ)⌋` (`dPrime`, see `Section41.lean`)
makes Theorem 1.4 hold. The slip affects every colour with `d < 7θ - 1`, in particular every
proper list colouring instance, so it is not a degenerate case.
-/

open Finset SimpleGraph
open scoped Classical

namespace FK24

namespace Sec41

variable {V α : Type*}

/-- The paper's modified defect function, eq. (10) of [FK24]:
`d'_v(x) = ⌊(d_v(x) + 1) / (7θ)⌋ - 1`. -/
def dPaper (I : ListInstance V α) (θ : ℕ) (v : V) (x : α) : ℤ :=
  (((I.d v x + 1) / (7 * θ) : ℕ) : ℤ) - 1

section Negative

variable {G : SimpleGraph V} [G.LocallyFinite] {I : ListInstance V α} {d' : V → α → ℤ} {S : ℝ}
  {top : ℕ}

/-- With negative modified defects, condition (12) never holds. -/
theorem not_cond_of_neg (hneg : ∀ v x, d' v x < 0) (it : V → Option ℕ) (col : V → α) (v : V)
    (x : α) (i : ℕ) : ¬ Cond G d' it col v x i := by
  have := hneg v x
  have h1 : (0 : ℤ) ≤ dI i := Nat.cast_nonneg _
  have h2 : (0 : ℤ) ≤ aCount G it col v x i := Nat.cast_nonneg _
  simp only [Cond]
  omega

/-- With negative modified defects (and `S ≥ 0`), no node is ever in `H_i`. -/
theorem not_inH_of_neg (hneg : ∀ v x, d' v x < 0) (hS : 0 ≤ S) (it : V → Option ℕ)
    (col : V → α) (v : V) (i : ℕ) : ¬ InH G I d' S top it col v i := by
  rintro ⟨-, h⟩
  have hL : listAt G I d' top it col v i = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    simp only [listAt, mem_filter] at hx
    exact not_cond_of_neg hneg it col v x i hx.2.2.1
  rw [hL, sum_empty] at h
  have : (0 : ℝ) ≤ S * uncolCount G it v i := mul_nonneg hS (Nat.cast_nonneg _)
  linarith

/-- With negative modified defects, every run leaves all nodes uncoloured. -/
theorem it_eq_none_of_neg (hneg : ∀ v x, d' v x < 0) (hS : 0 ≤ S) {it : V → Option ℕ}
    {col : V → α} (hrun : IsRun G I d' S top it col) (v : V) : it v = none := by
  rcases h : it v with _ | i
  · rfl
  · exact absurd (hrun.colored_spec v i h).2.1 (not_inH_of_neg hneg hS it col v i)

/-- With negative modified defects, the run that colours no node is a valid run. -/
theorem isRun_none_of_neg (hneg : ∀ v x, d' v x < 0) (hS : 0 ≤ S) (col : V → α) :
    IsRun G I d' S top (fun _ => none) col where
  colored_spec v i h := by simp at h
  colored_of_inH v i _ h := absurd h (not_inH_of_neg hneg hS _ col v i)
  arbdefective i := ⟨fun _ _ => False, fun _ _ _ h => by simp at h, fun u h => by simp at h⟩

end Negative

/-! ### The concrete counterexample -/

namespace Counterexample

/-- The graph `K₃` (the triangle). -/
abbrev ceG : SimpleGraph (Fin 3) := ⊤

/-- Proper list colouring (all defects `0`) with the lists `{0, …, 84}`. -/
def ceI : ListInstance (Fin 3) ℕ := ⟨fun _ => range 85, fun _ _ => 0⟩

/-- The paper's eq. (10) yields the negative defect `-1` (the paper claims non-negativity). -/
theorem dPaper_ceI (v : Fin 3) (x : ℕ) : dPaper ceI 1 v x = -1 := by
  simp [dPaper, ceI]

/-- Eq. (11) of [FK24] fails for the paper's `d'`:
`∑_{x ∈ L_v} (d'_v(x) + 1) = 0 < 85 / 7 = (1/(7θ)) ∑_{x ∈ L_v} (d_v(x) + 1)`. -/
theorem eq11_fails (v : Fin 3) :
    ∑ x ∈ ceI.L v, ((dPaper ceI 1 v x : ℝ) + 1) = 0 ∧
      (0 : ℝ) < 1 / (7 * 1) * (ceI.weight v : ℝ) := by
  refine ⟨by simp [dPaper_ceI], ?_⟩
  simp [ListInstance.weight, ceI]

theorem clog_two : Nat.clog 2 2 = 1 := by
  simpa using Nat.clog_pow 2 1 (by norm_num)

theorem dPaper_neg : ∀ v x, dPaper ceI 1 v x < 0 := fun v x => by simp [dPaper_ceI]

theorem neighborFinset_ceG (v : Fin 3) : ceG.neighborFinset v = univ.erase v := by
  ext w
  simp [eq_comm]

theorem degree_ceG (v : Fin 3) : ceG.degree v = 2 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_ceG, card_erase_of_mem (mem_univ _)]
  simp

/-- The triangle has neighbourhood independence `1`. -/
theorem nbhdIndep_ceG : ceG.NeighborhoodIndepLE 1 := by
  intro v I _ hind
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  by_contra hab
  exact hind ha hb hab (by simpa using hab)

/-- The instance satisfies the paper's slack condition `42 θ log Δ · S` (`θ = S = 1`, `Δ = 2`). -/
theorem hasSlack_paper :
    HasSlack ceG ceI (42 * ((1 : ℕ) : ℝ) * Real.logb 2 ((2 : ℕ) : ℝ) * 1) := by
  intro v
  rw [degree_ceG]
  simp [ListInstance.weight, ceI, Real.logb_self_eq_one]
  norm_num

/-- The instance also satisfies the corrected slack condition (9),
`21 θ (⌈log Δ⌉ + 1) S · deg(v) < ∑ (d_v(x) + 1)` (`84 < 85`). -/
theorem hasSlack_eq9 : HasSlack ceG ceI (21 * ((1 : ℕ) : ℝ) * (Nat.clog 2 2 + 1) * 1) := by
  intro v
  rw [degree_ceG, clog_two]
  simp [ListInstance.weight, ceI]
  norm_num

/-- Lemma 4.2 of [FK24] fails for the paper's defect function (10): every run of the algorithm
on the counterexample leaves both nodes uncoloured. -/
theorem lemma_4_2_fails (it : Fin 3 → Option ℕ) (col : Fin 3 → ℕ)
    (hrun : IsRun ceG ceI (dPaper ceI 1) 1 (Nat.clog 2 2) it col) (v : Fin 3) : it v = none :=
  it_eq_none_of_neg dPaper_neg zero_le_one hrun v

/-- The run that colours nothing is a run of the algorithm on the counterexample (so
`lemma_4_2_fails` is not vacuous). -/
theorem isRun_ce : IsRun ceG ceI (dPaper ceI 1) 1 (Nat.clog 2 2) (fun _ => none) (fun _ => 0) :=
  isRun_none_of_neg dPaper_neg zero_le_one _

end Counterexample

open Counterexample in
/-- The Section 4.1 algorithm of [FK24] *as defined with eq. (10)* (a floor/ceiling slip; the paper
states `d' ≥ 0`) does not achieve Theorem 1.4: there is a graph
(`K₃` (the triangle), neighbourhood independence `θ = 1`, `Δ = 2`), a list defective colouring instance with the
paper's slack `42 θ log Δ · S` (`S = 1`) and `d_v(x) ≤ Δ`, and a run of the Section 4.1 algorithm
with `d' = ⌊(d + 1)/(7θ)⌋ - 1` that leaves a node uncoloured. -/
theorem theorem_1_4_paper_defects_false :
    ¬ ∀ (V : Type) (G : SimpleGraph V) [G.LocallyFinite] (I : ListInstance V ℕ) (θ Δ : ℕ) (S : ℝ)
      (it : V → Option ℕ) (col : V → ℕ),
      G.NeighborhoodIndepLE θ → 1 ≤ θ → 1 ≤ S → 2 ≤ Δ → (∀ v, G.degree v ≤ Δ) →
      (∀ v, ∀ x ∈ I.L v, I.d v x ≤ Δ) → HasSlack G I (42 * θ * Real.logb 2 Δ * S) →
      IsRun G I (dPaper I θ) S (Nat.clog 2 Δ) it col → ∀ v, ∃ i, it v = some i := by
  intro h
  have h1 := h (Fin 3) ceG ceI 1 2 1 (fun _ => none) (fun _ => 0) nbhdIndep_ceG le_rfl le_rfl
    le_rfl
  have h2 := h1 (fun v => by rw [degree_ceG]) (fun v x _ => by simp [ceI])
  have h3 := h2 hasSlack_paper
  have h4 := h3 isRun_ce 0
  obtain ⟨i, hi⟩ := h4
  exact absurd hi (by simp)

end Sec41

end FK24
