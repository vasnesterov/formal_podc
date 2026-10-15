import Papers.PODC2024.Swiper.Defs

/-!
# Swiper: the combinatorial core of Theorem 4.2 (blunt access structures)

Section 4.2 of Tonkikh–Freitas (PODC 2024). A party set `P` controls `t(P)` virtual users of a
nominal threshold scheme that needs `⌈αn T⌉` shares. The cryptographic part (security of the
nominal protocol) is out of scope; what remains is the combinatorial statement that the resulting
access structure is *blunt* with respect to the weighted adversary structure
`F_w(fw) = {P | w(P) < fw · W}` whenever `t` solves `WR(fw, αn)` and `αn ≤ 1/2`.

Definition 4.1 reads `(∀F ∈ F : F ∉ A) ∧ (∃A ∈ A : A ∩ F = ∅)` with `F` unbound in the second
conjunct; we read it as `∀ F ∈ F, ∃ A ∈ A, A ∩ F = ∅` (the honest parties of every admissible
corruption contain a qualified set).
-/

namespace Papers.PODC2024.Swiper

open Finset

variable {ι : Type*} [Fintype ι]

/-- **Definition 4.1 (blunt access structure)** w.r.t. an adversary structure `F`. -/
def IsBlunt (A F : Set (Finset ι)) : Prop :=
  (∀ X ∈ F, X ∉ A) ∧ (∀ X ∈ F, ∃ Y ∈ A, Disjoint Y X)

/-- The access structure induced by a ticket assignment and a nominal threshold `αn`: sets owning
at least `⌈αn T⌉` virtual users. -/
def ticketAccess (αn : ℝ) (t : ι → ℕ) : Set (Finset ι) :=
  {P | ⌈αn * ∑ i, (t i : ℝ)⌉₊ ≤ ∑ i ∈ P, t i}

/-- The weighted adversary structure `F_w(fw)`: sets of weight less than `fw · W`. -/
def weightAdversary (fw : ℝ) (w : ι → ℝ) : Set (Finset ι) :=
  {P | ∑ i ∈ P, w i < fw * ∑ i, w i}

/-- **Theorem 4.2 (combinatorial core).** If `t` solves Weight Restriction with `αw = fw` and
`αn ≤ 1/2`, then the threshold-`⌈αn T⌉` access structure on virtual users is blunt w.r.t.
`F_w(fw)`. -/
theorem isBlunt_of_isWR {fw αn : ℝ} {w : ι → ℝ} {t : ι → ℕ} (hαn : αn ≤ 1 / 2)
    (ht : IsWR fw αn w t) : IsBlunt (ticketAccess αn t) (weightAdversary fw w) := by
  classical
  have hc : ∀ P : Finset ι, ⌈αn * ∑ i, (t i : ℝ)⌉₊ ≤ ∑ i ∈ P, t i ↔
      αn * ∑ i, (t i : ℝ) ≤ ∑ i ∈ P, (t i : ℝ) := fun P => by
    rw [Nat.ceil_le]; push_cast; rfl
  refine ⟨fun X hX hA => ?_, fun X hX => ⟨Xᶜ, ?_, disjoint_compl_left⟩⟩
  · have h1 := ht X hX
    have h2 := (hc X).1 hA
    linarith
  · have h1 := ht X hX
    have hsplit : ∑ i ∈ Xᶜ, (t i : ℝ) = ∑ i, (t i : ℝ) - ∑ i ∈ X, (t i : ℝ) := by
      rw [← Finset.sum_compl_add_sum X]; ring
    have hT : 0 ≤ ∑ i, (t i : ℝ) := by positivity
    show Xᶜ ∈ ticketAccess αn t
    simp only [ticketAccess, Set.mem_ofPred_eq]
    rw [hc, hsplit]
    nlinarith

end Papers.PODC2024.Swiper
