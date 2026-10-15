import Cslib.Foundations.Combinatorics.SimplicialComplex.IndexLemma
import Papers.PODC2022.ArrowTopology.SignModel

/-!
# Lemma 3.2: the input complex `N_I` is orientable (three alternatives, any number of voters)

We orient the triangle `t = {U^{σ₁}_{AB}, U^{σ₂}_{BC}, U^{σ₃}_{CA}}` of `N_I` as in the paper's proof
of Lemma 3.2: its *parity* is the product of all signs of `σ₁, σ₂, σ₃`; the orientation is
`AB → BC → CA` if the parity is `+1` and `AB → CA → BC` if it is `−1`. (We encode the parity
additively in `ZMod 2`: `parity t = 0` iff the product of the signs is `+1`.)

* `lemma_3_2`: this is an orientation in the sense of the index lemma
  (`Cslib.Simplicial.IsOriented`): on every non-boundary edge, the triangles inducing `u → w` and
  those inducing `w → u` are equinumerous.
* `isBoundary_iff`: an edge `{U^α_j, U^β_{j'}}` (`j ≠ j'`) is a boundary edge (lies in exactly one
  triangle) iff `α = β`.

The paper pairs the `2^k` triangles on an edge by "`σ₃` and `σ₃'` equal on each component but
one"; for `k ≥ 2` this relation is not a pairing. We pair by flipping the third sign vector at one
fixed coordinate where `σ₁` and `σ₂` differ.
-/

namespace Podc.ArrowTopology

open Cslib.Simplicial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Triangles of `N_I` (three alternatives): consistent sign triples. -/
abbrev Tri (ι : Type*) := {t : Fin 3 → ι → Bool // Consistent t}

/-- `+` ↦ `0`, `−` ↦ `1` (additive encoding of the sign). -/
def bz (b : Bool) : ZMod 2 := if b then 0 else 1

/-- Parity of a triangle: `0` iff the product of all its signs is `+1`. -/
def parity (t : Fin 3 → ι → Bool) : ZMod 2 := ∑ j, ∑ i, bz (t j i)

/-- The orientation of Lemma 3.2. -/
def orient (t : Tri ι) : Vtx ι × Vtx ι × Vtx ι :=
  if parity t.1 = 0 then ((0, t.1 0), (1, t.1 1), (2, t.1 2))
  else ((0, t.1 0), (2, t.1 2), (1, t.1 1))

omit [DecidableEq ι] in
theorem count_dirEdges_orient (t : Tri ι) (j j' : Fin 3) (α β : ι → Bool) :
    (dirEdges (orient t)).count ((j, α), (j', β)) =
      if ((j' = j + 1 ∧ parity t.1 = 0) ∨ (j' = j + 2 ∧ parity t.1 ≠ 0)) ∧ t.1 j = α ∧
        t.1 j' = β then 1 else 0 := by
  by_cases hp : parity t.1 = 0 <;> fin_cases j <;> fin_cases j' <;>
    simp (config := {decide := true}) [orient, dirEdges, hp, List.count_cons, Prod.ext_iff]

/-- "All three equal" does not depend on the order in which the three positions are listed. -/
theorem allEq_iff {g : Fin 3 → Bool} {j j' k : Fin 3} (h1 : j ≠ j') (h2 : k ≠ j) (h3 : k ≠ j') :
    (g 0 = g 1 ∧ g 1 = g 2) ↔ (g j = g j' ∧ g j' = g k) := by
  fin_cases j <;> fin_cases j' <;> fin_cases k <;> simp_all <;>
    constructor <;> rintro ⟨h, h'⟩ <;> simp_all

theorem third_index {j j' : Fin 3} (h : j ≠ j') : ∃ k, k ≠ j ∧ k ≠ j' := by
  fin_cases j <;> fin_cases j' <;> simp_all <;>
    first | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩ |
      exact ⟨2, by decide, by decide⟩

omit [Fintype ι] [DecidableEq ι] in
theorem consistent_iff {t : Fin 3 → ι → Bool} {j j' k : Fin 3} (h1 : j ≠ j') (h2 : k ≠ j)
    (h3 : k ≠ j') : Consistent t ↔ ∀ i, ¬ (t j i = t j' i ∧ t j' i = t k i) := by
  unfold Consistent
  exact forall_congr' fun i => not_congr (allEq_iff (g := fun m => t m i) h1 h2 h3)

/-- Flip the sign of voter `i₀` in the `k`-th sign vector. -/
def flip (t : Fin 3 → ι → Bool) (k : Fin 3) (i₀ : ι) : Fin 3 → ι → Bool :=
  Function.update t k (Function.update (t k) i₀ (!t k i₀))

omit [Fintype ι] in
theorem flip_flip (t : Fin 3 → ι → Bool) (k : Fin 3) (i₀ : ι) : flip (flip t k i₀) k i₀ = t := by
  funext m i
  by_cases hm : m = k
  · subst hm; by_cases hi : i = i₀
    · subst hi; simp [flip]
    · simp [flip]
  · simp [flip, hm]

omit [Fintype ι] in
theorem flip_apply_ne (t : Fin 3 → ι → Bool) {k m : Fin 3} (i₀ : ι) (hm : m ≠ k) :
    flip t k i₀ m = t m := by simp [flip, hm]

theorem bz_not (b : Bool) : bz (!b) = bz b + 1 := by cases b <;> decide

theorem parity_flip (t : Fin 3 → ι → Bool) (k : Fin 3) (i₀ : ι) :
    parity (flip t k i₀) = parity t + 1 := by
  have key : ∀ m i, bz (flip t k i₀ m i) = bz (t m i) + if m = k ∧ i = i₀ then 1 else 0 := by
    intro m i
    by_cases hm : m = k
    · subst hm; by_cases hi : i = i₀
      · subst hi; simp [flip, bz_not]
      · simp [flip, hi]
    · simp [flip, hm]
  simp only [parity, key, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
  · intro m _ hm; simp [hm]
  · simp

omit [Fintype ι] in
theorem consistent_flip {t : Fin 3 → ι → Bool} (ht : Consistent t) {j j' k : Fin 3}
    (h1 : j ≠ j') (h2 : k ≠ j) (h3 : k ≠ j') {i₀ : ι} (hi₀ : t j i₀ ≠ t j' i₀) :
    Consistent (flip t k i₀) := by
  rw [consistent_iff h1 h2 h3] at ht ⊢
  intro i
  rw [flip_apply_ne t i₀ (Ne.symm h2), flip_apply_ne t i₀ (Ne.symm h3)]
  by_cases hi : i = i₀
  · subst hi; exact fun h => hi₀ h.1
  · have : flip t k i₀ k i = t k i := by simp [flip, hi]
    rw [this]; exact ht i

/-- The pairing of the proof of Lemma 3.2: on an edge `{U^α_j, U^β_{j'}}` with `α ≠ β`, the
triangles of parity `+1` and `−1` are equinumerous. -/
theorem card_even_eq_card_odd {j j' : Fin 3} (hjj' : j ≠ j') {α β : ι → Bool} (hαβ : α ≠ β) :
    (Finset.univ.filter fun t : Tri ι => parity t.1 = 0 ∧ t.1 j = α ∧ t.1 j' = β).card =
      (Finset.univ.filter fun t : Tri ι => parity t.1 ≠ 0 ∧ t.1 j = α ∧ t.1 j' = β).card := by
  obtain ⟨k, hkj, hkj'⟩ := third_index hjj'
  obtain ⟨i₀, hi₀⟩ : ∃ i, α i ≠ β i := by
    by_contra h; push Not at h; exact hαβ (funext h)
  have hfj : ∀ t : Fin 3 → ι → Bool, flip t k i₀ j = t j := fun t => flip_apply_ne t i₀ hkj.symm
  have hfj' : ∀ t : Fin 3 → ι → Bool, flip t k i₀ j' = t j' :=
    fun t => flip_apply_ne t i₀ hkj'.symm
  have hz : ∀ x : ZMod 2, x ≠ 0 ↔ x + 1 = 0 := by decide
  have hz' : ∀ x : ZMod 2, x = 0 ↔ x + 1 ≠ 0 := by decide
  refine Finset.card_bij' (fun t ht => ⟨flip t.1 k i₀, ?_⟩) (fun t ht => ⟨flip t.1 k i₀, ?_⟩)
    ?_ ?_ ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact consistent_flip t.2 hjj' hkj hkj' (by rw [ht.2.1, ht.2.2]; exact hi₀)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact consistent_flip t.2 hjj' hkj hkj' (by rw [ht.2.1, ht.2.2]; exact hi₀)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    rw [parity_flip, hfj, hfj', ← hz']
    exact ht
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    rw [parity_flip, hfj, hfj', ← hz]
    exact ht
  · intro t ht; exact Subtype.ext (flip_flip _ _ _)
  · intro t ht; exact Subtype.ext (flip_flip _ _ _)

/-- An edge `{U^α_j, U^α_{j'}}` (equal sign vectors) lies in exactly one triangle: the third sign
vector is forced by transitivity. -/
theorem card_eq_one {j j' : Fin 3} (hjj' : j ≠ j') (α : ι → Bool) :
    (Finset.univ.filter fun t : Tri ι => t.1 j = α ∧ t.1 j' = α).card = 1 := by
  obtain ⟨k, hkj, hkj'⟩ := third_index hjj'
  let t₀ : Fin 3 → ι → Bool := fun m => if m = k then fun i => !α i else α
  have ht₀ : Consistent t₀ := by
    rw [consistent_iff hjj' hkj hkj']
    intro i
    simp [t₀, hkj.symm, hkj'.symm]
  rw [Finset.card_eq_one]
  refine ⟨⟨t₀, ht₀⟩, ?_⟩
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    apply Subtype.ext
    funext m i
    have hc := (consistent_iff hjj' hkj hkj').1 t.2 i
    rw [h1, h2] at hc
    by_cases hm : m = k
    · subst hm
      simp only [t₀, ite_true]
      cases h : t.1 m i <;> cases ha : α i <;> simp_all
    · rcases (show m = j ∨ m = j' by
          fin_cases m <;> fin_cases j <;> fin_cases j' <;> fin_cases k <;> simp_all) with
        rfl | rfl
      · simp [t₀, hm, h1]
      · simp [t₀, hm, h2]
  · rintro rfl
    simp [t₀, hkj.symm, hkj'.symm]

/-- Number of triangles on the edge `{U^α_j, U^β_{j'}}` of parity `+1` (`b = true`) or `−1`. -/
def cnt (b : Bool) (j j' : Fin 3) (α β : ι → Bool) : ℕ :=
  (Finset.univ.filter fun t : Tri ι => (parity t.1 = 0 ↔ b = true) ∧ t.1 j = α ∧ t.1 j' = β).card

theorem edgeCount_orient (j j' : Fin 3) (α β : ι → Bool) :
    edgeCount orient ((j, α), (j', β)) =
      if j' = j + 1 then cnt true j j' α β else if j' = j + 2 then cnt false j j' α β else 0 := by
  unfold edgeCount
  simp only [count_dirEdges_orient]
  rw [Finset.sum_boole]
  simp only [Nat.cast_id, cnt]
  fin_cases j <;> fin_cases j' <;> simp (config := {decide := true})

theorem edgeCount_orient_rev (j j' : Fin 3) (α β : ι → Bool) :
    edgeCount orient ((j', β), (j, α)) =
      if j' = j + 1 then cnt false j j' α β else if j' = j + 2 then cnt true j j' α β else 0 := by
  unfold edgeCount
  simp only [count_dirEdges_orient]
  rw [Finset.sum_boole]
  simp only [Nat.cast_id, cnt]
  fin_cases j <;> fin_cases j' <;> simp (config := {decide := true}) [and_comm]

theorem cnt_add (j j' : Fin 3) (α β : ι → Bool) :
    cnt true j j' α β + cnt false j j' α β =
      (Finset.univ.filter fun t : Tri ι => t.1 j = α ∧ t.1 j' = β).card := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext t; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · rw [Finset.disjoint_filter]; intro t _ h1 h2; simp_all

theorem cnt_eq {j j' : Fin 3} (hjj' : j ≠ j') {α β : ι → Bool} (hαβ : α ≠ β) :
    cnt true j j' α β = cnt false j j' α β := by
  have := card_even_eq_card_odd (ι := ι) hjj' hαβ
  unfold cnt; simpa using this

/-- Boundary edges of `N_I` (three alternatives): `{U^α_j, U^β_{j'}}` lies in exactly one triangle
iff `α = β` (Figure 7: the boundary consists of the `2^n` Condorcet cycles
`{U^σ_{AB}, U^σ_{BC}, U^σ_{CA}}`). -/
theorem isBoundary_iff {j j' : Fin 3} (hjj' : j ≠ j') (α β : ι → Bool) :
    IsBoundary orient (j, α) (j', β) ↔ α = β := by
  have htot : edgeCount orient ((j, α), (j', β)) + edgeCount orient ((j', β), (j, α)) =
      (Finset.univ.filter fun t : Tri ι => t.1 j = α ∧ t.1 j' = β).card := by
    rw [edgeCount_orient, edgeCount_orient_rev, ← cnt_add]
    have : j' = j + 1 ∨ j' = j + 2 := by
      fin_cases j <;> fin_cases j' <;> simp_all
    rcases this with h | h
    · simp [h]
    · have : ¬ j' = j + 1 := by rw [h]; fin_cases j <;> decide
      simp [h]; ring
  unfold IsBoundary
  rw [htot]
  constructor
  · intro h
    by_contra hαβ
    rw [← cnt_add, cnt_eq hjj' hαβ] at h
    omega
  · rintro rfl; exact card_eq_one hjj' α

/-- **Lemma 3.2** of [Rajsbaum–Raventós-Pujol, PODC 2022]: the complex `N_I` (three alternatives,
any finite set of voters) is orientable; the orientation is given by the parity of the triangles. -/
theorem lemma_3_2 : IsOriented (orient (ι := ι)) := by
  rintro ⟨j, α⟩ ⟨j', β⟩ hb
  by_cases hjj' : j = j'
  · subst hjj'
    rw [edgeCount_orient, edgeCount_orient_rev]
    have h1 : ¬ j = j + 1 := by fin_cases j <;> decide
    have h2 : ¬ j = j + 2 := by fin_cases j <;> decide
    simp [h1, h2]
  · have hαβ : α ≠ β := fun h => hb ((isBoundary_iff hjj' α β).2 h)
    rw [edgeCount_orient, edgeCount_orient_rev, cnt_eq hjj' hαβ]

end Podc.ArrowTopology
