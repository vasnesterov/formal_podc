import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

-- CSLib candidate: Cslib/Foundations/Combinatorics/SetPairs.lean

/-!
# Bollobás's set-pairs theorem

Let `(Aᵢ, Bᵢ)`, `i ∈ s`, be pairs of finite sets such that `Aᵢ ∩ Bⱼ = ∅` if and only if `i = j`
(a *cross-intersecting set-pair system*). Bollobás (1965) proved that
`∑ᵢ 1 / C(|Aᵢ| + |Bᵢ|, |Aᵢ|) ≤ 1`. Consequently, if `|Aᵢ| + |Bᵢ| ≤ k` for all `i`, then the
family has at most `C(k, ⌊k/2⌋)` members, and this is attained by the pairs `(S, Sᶜ)` with `S`
ranging over the `⌊k/2⌋`-subsets of a `k`-set.

## Main statements

* `Cslib.SetPairs.sum_inv_choose_le_one`: Bollobás's inequality
  (Jukna, *Extremal Combinatorics*, Theorem 9.8).
* `Cslib.SetPairs.card_le_choose_half`: the bound `#s ≤ C(k, k/2)` when `|Aᵢ| + |Bᵢ| ≤ k`.
* `Cslib.SetPairs.exists_card_eq_choose_half`: this bound is attained for every `k`.

## Proof

By strong induction on a ground set `X` containing all `Aᵢ` and `Bᵢ` (Jukna's proof). If some `Bᵢ`
is empty then `Aⱼ ∩ Bᵢ = ∅` for every `j`, so `s = {i}`. Otherwise, for each `x ∈ X` the pairs
`(Aᵢ, Bᵢ \ {x})` with `x ∉ Aᵢ` form a cross-intersecting system on `X \ {x}`; summing the induction
hypotheses over `x ∈ X` and using `|Bᵢ| / C(a + b - 1, a) = (a + b) / C(a + b, a)` gives
`|X| · ∑ᵢ 1 / C(aᵢ + bᵢ, aᵢ) ≤ |X|`.

## References

* B. Bollobás, *On generalized graphs*, Acta Math. Acad. Sci. Hungar. 16 (1965).
* S. Jukna, *Extremal Combinatorics*, 2nd ed., Theorem 9.8.
-/

namespace Cslib.SetPairs

open Finset

variable {ι α : Type*} [DecidableEq α]

/-- `C(a + b, a) · b = C(a + b - 1, a) · (a + b)` for `b ≥ 1`. -/
private lemma choose_mul_eq (a b : ℕ) (hb : 1 ≤ b) :
    (a + b).choose a * b = (a + b - 1).choose a * (a + b) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have := Nat.choose_mul_succ_eq (a + c) a
  rw [show a + (c + 1) - 1 = a + c by omega, show a + (c + 1) = a + c + 1 by omega, this,
    show a + c + 1 - a = c + 1 by omega]

/-- The contribution of one pair `(A, B)` to the double count: summing the weights of the
derived pairs `(A, B \ {x})` over `x ∈ X \ A` gives `|X|` times the weight of `(A, B)`. -/
private lemma sum_sdiff_inv_choose (X A B : Finset α) (hA : A ⊆ X) (hB : B ⊆ X)
    (hAB : Disjoint A B) (hb : B.Nonempty) :
    ∑ x ∈ X \ A, (((#A + #(B.erase x)).choose #A : ℚ))⁻¹ =
      #X * (((#A + #B).choose #A : ℚ))⁻¹ := by
  have hb1 : 1 ≤ #B := hb.card_pos
  have hsplit : ∀ x ∈ X \ A, (((#A + #(B.erase x)).choose #A : ℚ))⁻¹ =
      if x ∈ B then (((#A + #B - 1).choose #A : ℚ))⁻¹ else (((#A + #B).choose #A : ℚ))⁻¹ := by
    intro x _
    split_ifs with hx
    · rw [card_erase_of_mem hx, show #A + (#B - 1) = #A + #B - 1 by omega]
    · rw [erase_eq_of_notMem hx]
  rw [sum_congr rfl hsplit, sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h1 : (X \ A).filter (· ∈ B) = B := by
    ext x
    simp only [mem_filter, mem_sdiff, and_iff_right_iff_imp]
    exact fun hx => ⟨hB hx, fun hxA => disjoint_left.1 hAB hxA hx⟩
  have h2 : #((X \ A).filter (· ∉ B)) + #B + #A = #X := by
    have := card_filter_add_card_filter_not (s := X \ A) (p := (· ∈ B))
    rw [h1] at this
    rw [← card_sdiff_add_card_eq_card hA]
    omega
  rw [h1]
  have hc : (0 : ℚ) < (#A + #B).choose #A := by exact_mod_cast Nat.choose_pos (by omega)
  have hc' : (0 : ℚ) < (#A + #B - 1).choose #A := by exact_mod_cast Nat.choose_pos (by omega)
  have hkey : ((#A + #B).choose #A : ℚ) * #B = (#A + #B - 1).choose #A * (#A + #B) := by
    exact_mod_cast choose_mul_eq #A #B hb1
  have h2' : (#((X \ A).filter (· ∉ B)) : ℚ) + #B + #A = #X := by exact_mod_cast h2
  rw [← h2']
  field_simp
  linear_combination hkey

/-- Bollobás's inequality relative to a ground set `X` containing all the sets. -/
private lemma sum_inv_choose_le_one_of_subset (A : ι → Finset α) (X : Finset α) :
    ∀ (s : Finset ι) (B : ι → Finset α), (∀ i ∈ s, A i ⊆ X) → (∀ i ∈ s, B i ⊆ X) →
      (∀ i ∈ s, ∀ j ∈ s, Disjoint (A i) (B j) ↔ i = j) →
      ∑ i ∈ s, (((#(A i) + #(B i)).choose #(A i) : ℚ))⁻¹ ≤ 1 := by
  induction X using Finset.strongInduction with
  | H X ih =>
  intro s B hA hB h
  by_cases hdeg : ∃ i ∈ s, B i = ∅
  · -- degenerate case: an empty `Bᵢ` is disjoint from every `Aⱼ`, so `s = {i}`
    obtain ⟨i, hi, hBi⟩ := hdeg
    have hs : s ⊆ {i} := fun j hj => by
      rw [mem_singleton, ← h j hj i hi, hBi]
      exact disjoint_empty_right _
    calc ∑ j ∈ s, (((#(A j) + #(B j)).choose #(A j) : ℚ))⁻¹ ≤ ∑ _j ∈ s, (1 : ℚ) :=
          sum_le_sum fun j _ => inv_le_one_of_one_le₀ (by exact_mod_cast Nat.choose_pos (by omega))
      _ = #s := by simp
      _ ≤ 1 := by exact_mod_cast (card_le_card hs).trans (card_singleton i).le
  push Not at hdeg
  rcases s.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
  · simp
  have hXpos : (0 : ℚ) < #X := by
    exact_mod_cast card_pos.2 ((hdeg i0 hi0).mono (hB i0 hi0))
  -- induction hypothesis for the derived system on `X \ {x}`
  have hx : ∀ x ∈ X, ∑ i ∈ s.filter (fun i => x ∉ A i),
      (((#(A i) + #((B i).erase x)).choose #(A i) : ℚ))⁻¹ ≤ 1 := by
    intro x hxX
    apply ih (X.erase x) (erase_ssubset hxX) _ (fun i => (B i).erase x)
    · intro i hi y hy
      rw [mem_filter] at hi
      exact mem_erase.2 ⟨fun hyx => hi.2 (hyx ▸ hy), hA i hi.1 hy⟩
    · intro i hi
      exact erase_subset_erase x (hB i (mem_filter.1 hi).1)
    · intro i hi j hj
      rw [mem_filter] at hi hj
      rw [← h i hi.1 j hj.1, ← disjoint_erase_comm, erase_eq_of_notMem hi.2]
  have hsum := sum_le_sum hx
  rw [sum_comm' (t' := s) (s' := fun i => X \ A i) (h := by
    intro x i
    simp only [mem_filter, mem_sdiff]
    tauto)] at hsum
  rw [sum_congr rfl fun i hi => sum_sdiff_inv_choose X (A i) (B i) (hA i hi) (hB i hi)
    (h i hi i hi |>.2 rfl) (hdeg i hi), ← mul_sum] at hsum
  simp only [sum_const, nsmul_eq_mul, mul_one] at hsum
  exact le_of_mul_le_mul_left (by simpa using hsum) hXpos

/-- **Bollobás's theorem** (Theorem 9 of Aspnes, *A modular approach to shared-memory consensus*,
PODC 2010, cited from Jukna, *Extremal Combinatorics*, Theorem 9.8).
If `Aᵢ ∩ Bⱼ = ∅ ↔ i = j` for all `i, j ∈ s`, then `∑ᵢ 1 / C(|Aᵢ| + |Bᵢ|, |Aᵢ|) ≤ 1`. -/
theorem sum_inv_choose_le_one (s : Finset ι) (A B : ι → Finset α)
    (h : ∀ i ∈ s, ∀ j ∈ s, Disjoint (A i) (B j) ↔ i = j) :
    ∑ i ∈ s, (((#(A i) + #(B i)).choose #(A i) : ℚ))⁻¹ ≤ 1 :=
  sum_inv_choose_le_one_of_subset A (s.biUnion fun i => A i ∪ B i) s B
    (fun _ hi => subset_union_left.trans (subset_biUnion_of_mem (fun i => A i ∪ B i) hi))
    (fun _ hi => subset_union_right.trans (subset_biUnion_of_mem (fun i => A i ∪ B i) hi)) h

/-- Corollary of Bollobás's theorem: a cross-intersecting set-pair system with
`|Aᵢ| + |Bᵢ| ≤ k` for all `i` has at most `C(k, ⌊k/2⌋)` pairs. -/
theorem card_le_choose_half (k : ℕ) (s : Finset ι) (A B : ι → Finset α)
    (h : ∀ i ∈ s, ∀ j ∈ s, Disjoint (A i) (B j) ↔ i = j)
    (hk : ∀ i ∈ s, #(A i) + #(B i) ≤ k) :
    #s ≤ k.choose (k / 2) := by
  have hpos : (0 : ℚ) < k.choose (k / 2) := by exact_mod_cast Nat.choose_pos (Nat.div_le_self _ _)
  have key : ∀ i ∈ s, ((k.choose (k / 2) : ℚ))⁻¹ ≤
      (((#(A i) + #(B i)).choose #(A i) : ℚ))⁻¹ := by
    intro i hi
    apply inv_anti₀ (by exact_mod_cast Nat.choose_pos (by omega))
    exact_mod_cast (Nat.choose_le_middle _ _).trans
      ((Nat.choose_le_choose _ (hk i hi)).trans (Nat.choose_le_middle _ _))
  have hle := (sum_le_sum key).trans (sum_inv_choose_le_one s A B h)
  rw [sum_const, nsmul_eq_mul, mul_inv_le_iff₀ hpos, one_mul] at hle
  exact_mod_cast hle

/-- The `⌊k/2⌋`-subsets `S` of `Fin k`, paired with their complements, form a cross-intersecting
set-pair system: `S ∩ Tᶜ = ∅ ↔ S = T`. -/
theorem disjoint_compl_iff_of_mem_powersetCard {k : ℕ} {S T : Finset (Fin k)}
    (hS : S ∈ (univ : Finset (Fin k)).powersetCard (k / 2))
    (hT : T ∈ (univ : Finset (Fin k)).powersetCard (k / 2)) :
    Disjoint S Tᶜ ↔ S = T := by
  rw [disjoint_compl_right_iff]
  rw [mem_powersetCard] at hS hT
  exact ⟨fun hST => eq_of_subset_of_card_le hST (by omega), fun hST => hST ▸ le_rfl⟩

/-- Tightness of `card_le_choose_half`: for every `k` there is a cross-intersecting set-pair system
with `|Aᵢ| + |Bᵢ| ≤ k` and exactly `C(k, ⌊k/2⌋)` pairs (take `A = S`, `B = Sᶜ` for the
`⌊k/2⌋`-subsets `S` of `Fin k`). -/
theorem exists_card_eq_choose_half (k : ℕ) :
    ∃ (s : Finset (Finset (Fin k))) (A B : Finset (Fin k) → Finset (Fin k)),
      (∀ i ∈ s, ∀ j ∈ s, Disjoint (A i) (B j) ↔ i = j) ∧
      (∀ i ∈ s, #(A i) + #(B i) ≤ k) ∧ #s = k.choose (k / 2) := by
  refine ⟨univ.powersetCard (k / 2), id, compl, fun _ hi _ hj =>
    disjoint_compl_iff_of_mem_powersetCard hi hj, fun i _ => ?_, ?_⟩
  · simp only [id, card_compl, Fintype.card_fin]
    have := i.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  · simp [card_powersetCard]

end Cslib.SetPairs
