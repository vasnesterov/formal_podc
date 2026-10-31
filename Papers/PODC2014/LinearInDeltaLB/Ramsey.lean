import Papers.PODC2014.LinearInDeltaLB.IDGraph
import Papers.PODC2014.LinearInDeltaLB.POCover
import Podc.Foundations.Combinatorics.HypergraphRamsey

/-!
# The saturation indicator and the Ramsey step (Section 5.4, step (i), Lemma 5)

Throughout, `F_k` carries a linear order `<` (later: the left-invariant order of Lemma 4).
A *shape* is a finite set `X ⊆ F_k` (the radius-`t` neighbourhood of a node of a PO-view, re-rooted
at `1`). For a set `S ⊆ ℕ` with `|S| = |X|`, `labelOf X S` is the order-preserving identifier
assignment `X → S`; `satColour A X S` records whether `A` saturates the root of `X` labelled by
`S` (the saturation indicator `A*` of the paper). Because `A*` is binary, Ramsey's theorem gives
large sets `I ⊆ ℕ` on which `A*` is order-invariant on all shapes inside the ball of radius `t`
(`exists_homog`, the finite version of Lemma 5 of [Naor–Stockmeyer]).
-/

namespace Podc.LinearInDeltaLB

open FreeGroup Pointwise

variable {k : ℕ} [LinearOrder (FG k)]

/-- The order-preserving identifier assignment of the shape `X` by the identifiers `S`
(`0` outside `X`, or if the sizes differ). -/
noncomputable def labelOf (X : Finset (FG k)) (S : Finset ℕ) : FG k → ℕ := fun x =>
  if h : x ∈ X ∧ S.card = X.card then
    S.orderEmbOfFin h.2 ((X.orderIsoOfFin rfl).symm ⟨x, h.1⟩)
  else 0

/-- Uniqueness of order-preserving labellings: an order-preserving `ψ` with image `S` is
`labelOf X S` on `X`. -/
theorem labelOf_eq {X : Finset (FG k)} {ψ : FG k → ℕ} (hψ : StrictMonoOn ψ X) {x : FG k}
    (hx : x ∈ X) : labelOf X (X.image ψ) x = ψ x := by
  have hc : (X.image ψ).card = X.card := Finset.card_image_of_injOn hψ.injOn
  let f : Fin X.card → ℕ := fun i => ψ (X.orderIsoOfFin rfl i)
  have hf : f = (X.image ψ).orderEmbOfFin hc := by
    apply Finset.orderEmbOfFin_unique
    · intro i; exact Finset.mem_image_of_mem _ (X.orderIsoOfFin rfl i).2
    · intro i j hij
      exact hψ (X.orderIsoOfFin rfl i).2 (X.orderIsoOfFin rfl j).2
        ((X.orderIsoOfFin rfl).strictMono hij)
  simp only [labelOf, hx, hc, and_self, ↓reduceDIte]
  rw [← hf]
  simp only [f, OrderIso.apply_symm_apply]

theorem labelOf_of_mem {X : Finset (FG k)} {S : Finset ℕ} (h : S.card = X.card) {x : FG k}
    (hx : x ∈ X) : labelOf X S x = S.orderEmbOfFin h ((X.orderIsoOfFin rfl).symm ⟨x, hx⟩) := by
  simp [labelOf, hx, h]

theorem labelOf_strictMonoOn {X : Finset (FG k)} {S : Finset ℕ} (h : S.card = X.card) :
    StrictMonoOn (labelOf X S) X := by
  intro x hx y hy hxy
  rw [labelOf_of_mem h hx, labelOf_of_mem h hy]
  apply (S.orderEmbOfFin h).strictMono
  apply (X.orderIsoOfFin rfl).symm.strictMono
  exact hxy

theorem labelOf_mem {X : Finset (FG k)} {S : Finset ℕ} (h : S.card = X.card) {x : FG k}
    (hx : x ∈ X) : labelOf X S x ∈ S := by
  rw [labelOf_of_mem h hx]; exact Finset.orderEmbOfFin_mem _ _ _

open Classical in
/-- The saturation indicator `A*` on the shape `X` labelled by `S`. -/
noncomputable def satColour (A : IDAlg) (X : Finset (FG k)) (S : Finset ℕ) : Bool :=
  decide (Sat A (idGraph X (labelOf X S)) (labelOf X S 1))

/-- `I` is homogeneous for the saturation indicator of `A` on all shapes inside `ballF k t`. -/
def Homog (A : IDAlg) (t : ℕ) (I : Finset ℕ) : Prop :=
  ∀ X : Finset (FG k), (↑X : Set (FG k)) ⊆ ballF k t →
    ∃ b, ∀ S ⊆ I, S.card = X.card → satColour A X S = b

/-- Simultaneous finite Ramsey for finitely many two-colourings `c i` of `K i`-sets. -/
theorem exists_homogeneous_family {ι : Type*} (s : Finset ι) (K : ι → ℕ)
    (c : ι → Finset ℕ → Bool) (M : ℕ) :
    ∃ N, ∀ T : Finset ℕ, N ≤ T.card → ∃ Y ⊆ T, Y.card = M ∧
      ∀ i ∈ s, ∃ b, ∀ Z ⊆ Y, Z.card = K i → c i Z = b := by
  classical
  induction s using Finset.induction_on generalizing M with
  | empty =>
    refine ⟨M, fun T hT => ?_⟩
    obtain ⟨Y, hY, hYc⟩ := Finset.exists_subset_card_eq hT
    exact ⟨Y, hY, hYc, by simp⟩
  | insert j s _ ih =>
    obtain ⟨N₁, hN₁⟩ := ih M
    obtain ⟨N, hN⟩ := Cslib.exists_homogeneous (K j) N₁
    refine ⟨N, fun T hT => ?_⟩
    obtain ⟨Y₁, hY₁T, hY₁c, b, hb⟩ := hN (c j) T hT
    obtain ⟨Y, hYY₁, hYc, hY⟩ := hN₁ Y₁ hY₁c.ge
    refine ⟨Y, hYY₁.trans hY₁T, hYc, ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨b, fun Z hZ hZc => hb Z (hZ.trans hYY₁) hZc⟩
    · exact hY i hi

/-- Lemma 5 (finite version): arbitrarily large homogeneous sets exist. -/
theorem exists_homog (A : IDAlg) (t M : ℕ) :
    ∃ I : Finset ℕ, I.card = M ∧ Homog (k := k) A t I := by
  classical
  let B : Finset (FG k) := (ballF_finite (k := k) t).toFinset
  obtain ⟨N, hN⟩ := exists_homogeneous_family B.powerset (fun X => X.card)
    (fun X => satColour A X) M
  obtain ⟨Y, -, hYc, hY⟩ := hN (Finset.range N) (by simp)
  refine ⟨Y, hYc, fun X hX => hY X ?_⟩
  rw [Finset.mem_powerset]
  intro x hx
  simpa [B] using hX hx

end Podc.LinearInDeltaLB
