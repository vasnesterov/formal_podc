import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Basic.Real.Basic

/-!
# Circulations on the fractional entries of a matrix with integer line sums

Let `α : ι → κ → ℝ` be a real matrix (indexed by finite types) all of whose row sums and column
sums are integers, and suppose some entry of `α` is not an integer. Then:

* `exists_circulation`: there is a nonzero matrix `Δ` with zero row and column sums whose support
  consists of non-integral entries of `α`;
* `exists_cycle_direction`: `Δ` can moreover be chosen with at most two nonzero entries in every
  row and every column (so `Δ` is supported on a cycle of the bipartite row/column graph, with
  alternating signs `±d` along each row and column).

These are the "cycle" steps of dependent rounding (Gandhi–Khuller–Parthasarathy–Srinivasan,
JACM 2006) and of the proof that the Birkhoff polytope is integral.

The proof is by linear algebra instead of explicit alternating walks: a nonempty set `T` of
entries with `#T ≥ #rows(T) + #cols(T)` carries a nonzero matrix with zero line sums
(`exists_zeroLineSums_of_card`, a dimension count), and a nonzero such matrix of minimal support
has at most two nonzero entries per line.
-/

-- CSLib candidate (the whole file)

namespace Podc.DemandAwareThroughput

open Finset

section Counting

variable {α β : Type*} [DecidableEq β]

/-- If every fibre of `f` over `s.image f` has at least two elements, then
`2 * #(s.image f) ≤ #s`. -/
lemma two_mul_card_image_le (s : Finset α) (f : α → β)
    (h : ∀ b ∈ s.image f, 2 ≤ (s.filter (fun a => f a = b)).card) :
    2 * (s.image f).card ≤ s.card := by
  rw [card_eq_sum_card_image f s, mul_comm, ← smul_eq_mul, ← sum_const]
  exact sum_le_sum h

/-- Strict version of `two_mul_card_image_le`, when some fibre has at least three elements. -/
lemma two_mul_card_image_lt (s : Finset α) (f : α → β)
    (h : ∀ b ∈ s.image f, 2 ≤ (s.filter (fun a => f a = b)).card)
    {b₀ : β} (hb₀ : b₀ ∈ s.image f) (h3 : 3 ≤ (s.filter (fun a => f a = b₀)).card) :
    2 * (s.image f).card < s.card := by
  rw [card_eq_sum_card_image f s, mul_comm, ← smul_eq_mul, ← sum_const]
  exact sum_lt_sum h ⟨b₀, hb₀, h3⟩

end Counting

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A nonempty set `T` of entries of an `ι × κ` matrix that has at least as many elements as it
touches rows plus columns supports a nonzero matrix with zero row and column sums. -/
theorem exists_zeroLineSums_of_card (T : Finset (ι × κ)) (hT : T.Nonempty)
    (hcard : (T.image Prod.fst).card + (T.image Prod.snd).card ≤ T.card) :
    ∃ Δ : ι → κ → ℝ, (∃ i j, Δ i j ≠ 0) ∧ (∀ i j, Δ i j ≠ 0 → (i, j) ∈ T) ∧
      (∀ i, ∑ j, Δ i j = 0) ∧ (∀ j, ∑ i, Δ i j = 0) := by
  obtain ⟨p₀, hp₀⟩ := hT
  set R := T.image Prod.fst with hR
  set C := (T.image Prod.snd).erase p₀.2 with hC
  have hc₀ : p₀.2 ∈ T.image Prod.snd := mem_image_of_mem _ hp₀
  let G : ι × κ → (R → ℝ) × (C → ℝ) := fun p =>
    (fun i => if p.1 = i.1 then 1 else 0, fun j => if p.2 = j.1 then 1 else 0)
  have hfin : Module.finrank ℝ ((R → ℝ) × (C → ℝ)) < Fintype.card T := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe, Fintype.card_coe,
      hC, card_erase_of_mem hc₀]
    have : 0 < (T.image Prod.snd).card := card_pos.2 ⟨_, hc₀⟩
    omega
  obtain ⟨f, hf, e, he⟩ := Fintype.not_linearIndependent_iff.mp
    (mt LinearIndependent.fintype_card_le_finrank (not_le.mpr hfin) :
      ¬ LinearIndependent ℝ (fun e : T => G e.1))
  let F : ι × κ → ℝ := fun p => if h : p ∈ T then f ⟨p, h⟩ else 0
  have hFT : ∀ p, F p ≠ 0 → p ∈ T := by
    intro p hp
    by_contra h
    exact hp (by simp [F, h])
  have hF : ∀ φ : ι × κ → ℝ, ∑ e : T, f e * φ e.1 = ∑ p, F p * φ p := by
    intro φ
    rw [← sum_subset (subset_univ T), ← sum_coe_sort T]
    · refine sum_congr rfl fun e _ => ?_
      simp [F]
    · intro p _ hp
      simp [F, hp]
  -- the row sums
  have hrow : ∀ i ∈ R, ∑ p, F p * (if p.1 = i then 1 else 0) = 0 := by
    intro i hi
    rw [← hF]
    have := congrArg (fun v => v.1 ⟨i, hi⟩) hf
    simpa [G, Prod.fst_sum, sum_apply] using this
  have hcol : ∀ j ∈ C, ∑ p, F p * (if p.2 = j then 1 else 0) = 0 := by
    intro j hj
    rw [← hF]
    have := congrArg (fun v => v.2 ⟨j, hj⟩) hf
    simpa [G, Prod.snd_sum, sum_apply] using this
  have hrow' : ∀ i, ∑ j, F (i, j) = 0 := by
    intro i
    by_cases hi : i ∈ R
    · have := hrow i hi
      rw [Fintype.sum_prod_type, Finset.sum_comm] at this; simpa [mul_ite] using this
    · refine sum_eq_zero fun j _ => ?_
      by_contra h
      exact hi (mem_image_of_mem Prod.fst (hFT _ h))
  have hcol' : ∀ j ≠ p₀.2, ∑ i, F (i, j) = 0 := by
    intro j hj
    by_cases hj' : j ∈ T.image Prod.snd
    · have := hcol j (mem_erase.2 ⟨hj, hj'⟩)
      rw [Fintype.sum_prod_type_right, Finset.sum_comm] at this; simpa [mul_ite] using this
    · refine sum_eq_zero fun i _ => ?_
      by_contra h
      exact hj' (mem_image_of_mem Prod.snd (hFT _ h))
  refine ⟨fun i j => F (i, j), ⟨e.1.1, e.1.2, ?_⟩, fun i j h => hFT _ h, hrow', ?_⟩
  · simpa [F] using he
  · intro j
    by_cases hj : j = p₀.2
    · subst hj
      have htot : ∑ j', ∑ i, F (i, j') = 0 := by
        rw [sum_comm]; exact sum_eq_zero fun i _ => hrow' i
      rw [← add_sum_erase _ _ (mem_univ p₀.2)] at htot
      rwa [sum_eq_zero fun j' hj' => hcol' j' (ne_of_mem_erase hj'), add_zero] at htot
    · exact hcol' j hj

section Lines

variable {κ' : Type*} [Fintype κ'] [DecidableEq κ']

omit [Fintype κ'] in
/-- A finite sum of integers (cast to `ℝ`) is an integer. -/
lemma exists_int_sum_of_forall (v : κ' → ℝ) (s : Finset κ')
    (h : ∀ j ∈ s, ∃ z : ℤ, v j = z) : ∃ z : ℤ, ∑ j ∈ s, v j = z := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨x, hx⟩ := h a (mem_insert_self _ _)
    obtain ⟨y, hy⟩ := ih fun j hj => h j (mem_insert_of_mem hj)
    exact ⟨x + y, by rw [sum_insert ha, hx, hy]; push_cast; ring⟩

/-- If a line has an integer sum and a non-integral entry, it has another non-integral entry. -/
lemma exists_ne_nonint_of_sum (v : κ' → ℝ) (hs : ∃ z : ℤ, ∑ j, v j = z) {j₀ : κ'}
    (h : ¬ ∃ z : ℤ, v j₀ = z) : ∃ j ≠ j₀, ¬ ∃ z : ℤ, v j = z := by
  by_contra hall
  push Not at hall
  obtain ⟨w, hw⟩ := exists_int_sum_of_forall v (univ.erase j₀)
    fun j hj => by simpa using hall j (ne_of_mem_erase hj)
  obtain ⟨z, hz⟩ := hs
  refine h ⟨z - w, ?_⟩
  rw [← add_sum_erase _ _ (mem_univ j₀), hw] at hz
  push_cast
  linarith

/-- If a line has zero sum and a nonzero entry, it has another nonzero entry. -/
lemma exists_ne_ne_zero_of_sum_eq_zero (v : κ' → ℝ) (hs : ∑ j, v j = 0) {j₀ : κ'}
    (h : v j₀ ≠ 0) : ∃ j ≠ j₀, v j ≠ 0 := by
  by_contra hall
  push Not at hall
  rw [sum_eq_single j₀ (fun j _ hj => hall j hj) (by simp)] at hs
  exact h hs

end Lines

/-- **Circulation on the fractional entries.** If all row and column sums of the real matrix `α`
are integers and some entry is not, then there is a nonzero matrix `Δ` with zero row and column
sums, supported on the non-integral entries of `α`. -/
theorem exists_circulation (α : ι → κ → ℝ) (hr : ∀ i, ∃ z : ℤ, ∑ j, α i j = z)
    (hc : ∀ j, ∃ z : ℤ, ∑ i, α i j = z) (h : ∃ i j, ¬ ∃ z : ℤ, α i j = z) :
    ∃ Δ : ι → κ → ℝ, Δ ≠ 0 ∧ (∀ i j, Δ i j ≠ 0 → ¬ ∃ z : ℤ, α i j = z) ∧
      (∀ i, ∑ j, Δ i j = 0) ∧ (∀ j, ∑ i, Δ i j = 0) := by
  classical
  set F := univ.filter fun p : ι × κ => ¬ ∃ z : ℤ, α p.1 p.2 = z with hF
  have hmem : ∀ p, p ∈ F ↔ ¬ ∃ z : ℤ, α p.1 p.2 = z := by simp [hF]
  obtain ⟨i₀, j₀, h₀⟩ := h
  have hFne : F.Nonempty := ⟨(i₀, j₀), (hmem _).2 h₀⟩
  have hR : ∀ i ∈ F.image Prod.fst, 2 ≤ (F.filter fun p => p.1 = i).card := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hi
    obtain ⟨j, hj, hjf⟩ := exists_ne_nonint_of_sum (α p.1) (hr p.1) ((hmem p).1 hp)
    refine one_lt_card.2 ⟨p, by simp [hp], (p.1, j), by simp [hmem, hjf], ?_⟩
    intro h; exact hj (congrArg Prod.snd h).symm
  have hC : ∀ j ∈ F.image Prod.snd, 2 ≤ (F.filter fun p => p.2 = j).card := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hj
    obtain ⟨i, hi, hif⟩ := exists_ne_nonint_of_sum (fun i => α i p.2) (hc p.2) ((hmem p).1 hp)
    refine one_lt_card.2 ⟨p, by simp [hp], (i, p.2), by simp [hmem, hif], ?_⟩
    intro h; exact hi (congrArg Prod.fst h).symm
  have h1 := two_mul_card_image_le F Prod.fst hR
  have h2 := two_mul_card_image_le F Prod.snd hC
  obtain ⟨Δ, ⟨i, j, hij⟩, hsupp, hrow, hcol⟩ := exists_zeroLineSums_of_card F hFne (by omega)
  refine ⟨Δ, fun h0 => hij (by simp [h0]), fun i j h => (hmem (i, j)).1 (hsupp i j h), hrow, hcol⟩

/-- **Cycle direction.** If all row and column sums of the real matrix `α` are integers and some
entry is not, then there is a nonzero matrix `Δ` with zero row and column sums, supported on the
non-integral entries of `α`, with at most two nonzero entries in every row and every column. (So
every row and column of `Δ` is either zero or has exactly two nonzero entries `d` and `-d`.) -/
theorem exists_cycle_direction (α : ι → κ → ℝ) (hr : ∀ i, ∃ z : ℤ, ∑ j, α i j = z)
    (hc : ∀ j, ∃ z : ℤ, ∑ i, α i j = z) (h : ∃ i j, ¬ ∃ z : ℤ, α i j = z) :
    ∃ Δ : ι → κ → ℝ, Δ ≠ 0 ∧ (∀ i j, Δ i j ≠ 0 → ¬ ∃ z : ℤ, α i j = z) ∧
      (∀ i, ∑ j, Δ i j = 0) ∧ (∀ j, ∑ i, Δ i j = 0) ∧
      (∀ i, (univ.filter fun j => Δ i j ≠ 0).card ≤ 2) ∧
      (∀ j, (univ.filter fun i => Δ i j ≠ 0).card ≤ 2) := by
  classical
  let Good : (ι → κ → ℝ) → Prop := fun Δ => Δ ≠ 0 ∧
    (∀ i j, Δ i j ≠ 0 → ¬ ∃ z : ℤ, α i j = z) ∧ (∀ i, ∑ j, Δ i j = 0) ∧ (∀ j, ∑ i, Δ i j = 0)
  let supp : (ι → κ → ℝ) → Finset (ι × κ) := fun Δ => univ.filter fun p => Δ p.1 p.2 ≠ 0
  have hex : ∃ k, ∃ Δ, Good Δ ∧ (supp Δ).card = k :=
    let ⟨Δ, hΔ⟩ := exists_circulation α hr hc h; ⟨_, Δ, hΔ, rfl⟩
  obtain ⟨Δ, hΔ, hk⟩ := Nat.find_spec hex
  have hmin : ∀ Δ', Good Δ' → (supp Δ).card ≤ (supp Δ').card :=
    fun Δ' h' => hk ▸ Nat.find_min' hex ⟨Δ', h', rfl⟩
  obtain ⟨hne, hfr, hrow, hcol⟩ := hΔ
  set T := supp Δ with hTdef
  have hmem : ∀ p, p ∈ T ↔ Δ p.1 p.2 ≠ 0 := by simp [hTdef, supp]
  have hR : ∀ i ∈ T.image Prod.fst, 2 ≤ (T.filter fun p => p.1 = i).card := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hi
    obtain ⟨j, hj, hjf⟩ := exists_ne_ne_zero_of_sum_eq_zero (Δ p.1) (hrow p.1) ((hmem p).1 hp)
    refine one_lt_card.2 ⟨p, by simp [hp], (p.1, j), by simp [hmem, hjf], ?_⟩
    intro h; exact hj (congrArg Prod.snd h).symm
  have hC : ∀ j ∈ T.image Prod.snd, 2 ≤ (T.filter fun p => p.2 = j).card := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hj
    obtain ⟨i, hi, hif⟩ :=
      exists_ne_ne_zero_of_sum_eq_zero (fun i => Δ i p.2) (hcol p.2) ((hmem p).1 hp)
    refine one_lt_card.2 ⟨p, by simp [hp], (i, p.2), by simp [hmem, hif], ?_⟩
    intro h; exact hi (congrArg Prod.fst h).symm
  have h1 := two_mul_card_image_le T Prod.fst hR
  have h2 := two_mul_card_image_le T Prod.snd hC
  -- `T` cannot have more entries than rows plus columns, by minimality.
  have key : ¬ (T.image Prod.fst).card + (T.image Prod.snd).card < T.card := by
    intro hlt
    obtain ⟨i, j, hij⟩ : ∃ i j, Δ i j ≠ 0 := by
      by_contra h0; push Not at h0; exact hne (funext fun i => funext fun j => h0 i j)
    have hp : (i, j) ∈ T := (hmem _).2 hij
    have hR1 : 0 < (T.image Prod.fst).card := card_pos.2 ⟨i, mem_image_of_mem _ hp⟩
    have hC1 : 0 < (T.image Prod.snd).card := card_pos.2 ⟨j, mem_image_of_mem _ hp⟩
    have hcard := card_erase_of_mem hp
    have hsub1 := card_le_card (image_subset_image (f := Prod.fst) (erase_subset (i, j) T))
    have hsub2 := card_le_card (image_subset_image (f := Prod.snd) (erase_subset (i, j) T))
    obtain ⟨Δ', ⟨i', j', hij'⟩, hsupp, hr', hc'⟩ :=
      exists_zeroLineSums_of_card (T.erase (i, j)) (card_pos.1 (by omega)) (by omega)
    have hgood : Good Δ' := ⟨fun h0 => hij' (by simp [h0]),
      fun a b hab => hfr a b ((hmem (a, b)).1 (mem_of_mem_erase (hsupp a b hab))), hr', hc'⟩
    have hle := hmin Δ' hgood
    have hle' : (supp Δ').card ≤ (T.erase (i, j)).card :=
      card_le_card fun q hq => hsupp q.1 q.2 (mem_filter.1 hq).2
    omega
  refine ⟨Δ, hne, hfr, hrow, hcol, fun i => ?_, fun j => ?_⟩
  · by_contra h3
    push Not at h3
    have hfib : 3 ≤ (T.filter fun p => p.1 = i).card := by
      refine le_trans h3 (card_le_card_of_injOn (fun j => (i, j)) ?_ ?_)
      · intro j hj; simpa [hmem] using hj
      · intro a _ b _ hab; simpa using hab
    obtain ⟨p, hp⟩ := card_pos.1 (by omega : 0 < (T.filter fun p => p.1 = i).card)
    have hi : i ∈ T.image Prod.fst := mem_image.2 ⟨p, (mem_filter.1 hp).1, (mem_filter.1 hp).2⟩
    have := two_mul_card_image_lt T Prod.fst hR hi hfib
    omega
  · by_contra h3
    push Not at h3
    have hfib : 3 ≤ (T.filter fun p => p.2 = j).card := by
      refine le_trans h3 (card_le_card_of_injOn (fun i => (i, j)) ?_ ?_)
      · intro i hi; simpa [hmem] using hi
      · intro a _ b _ hab; simpa using hab
    obtain ⟨p, hp⟩ := card_pos.1 (by omega : 0 < (T.filter fun p => p.2 = j).card)
    have hj : j ∈ T.image Prod.snd := mem_image.2 ⟨p, (mem_filter.1 hp).1, (mem_filter.1 hp).2⟩
    have := two_mul_card_image_lt T Prod.snd hC hj hfib
    omega

end Podc.DemandAwareThroughput
