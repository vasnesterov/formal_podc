import Papers.PODC2010.ArbdefectiveColoring.PartialOrientation
import Cslib.Computability.Distributed.Local.Linial

/-!
# Linial's colouring as a black box (bridge to CSLib)

CSLib's locally-iterative version of Linial's algorithm (`Cslib.LocallyIterative.linial`,
PODC'18 formalization) computes a legal colouring with fewer than `max(16Δ², 256)` colours in
`log* n + 3` rounds, starting from the identifiers. Packaged as a `DefectiveAlg` (with defect `0`)
it can be plugged into Procedure Partial-Orientation (it is a `d`-defective colouring for every
`d`), giving unconditional versions of Lemma 3.3 and Lemma 2.2(1), with `O(a² log n)` rounds
instead of `O(a log n)`:

* `linialAlg`: the black box.
* `legalColoring_linial`: Lemma 2.2(1) without hypotheses: a legal colouring with colours `≤ A` of
  every graph of arboricity `≤ a`, in `L + log* n + 4 + (L·max(16A², 256) - 1)` rounds.
-/

open Finset Cslib.Local Cslib.LocallyIterative

namespace Podc.ArbdefectiveColoring

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

/-- Linial's algorithm from the identifiers, run for `log* n + 3` rounds. -/
noncomputable def linialCol (Δ : ℕ) (G : SimpleGraph V) (v : V) : ℕ :=
  (linial (Fintype.card V) (max Δ 1)).run G (fun u => (Fintype.equivFin V u : ℕ))
    (Nat.logStar (Fintype.card V) + 3) v

lemma degree_le_of_maxDegLE {G : SimpleGraph V} {Δ : ℕ} (h : MaxDegLE G Δ) (v : V) :
    G.degree v ≤ Δ := by
  have := h v
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  convert this using 2
  simp only [deg]

/-- **Linial's colouring as a black box**: a legal (`0`-defective) colouring with fewer than
`max(16 max(Δ,1)², 256)` colours of every graph of maximum degree `≤ Δ`, in `log* n + 3` rounds. -/
noncomputable def linialAlg (Δ : ℕ) :
    DefectiveAlg V Δ 0 (max (16 * (max Δ 1) ^ 2) 256) (Nat.logStar (Fintype.card V) + 3) where
  col := linialCol Δ
  isLocal := by
    have h := ((linial (Fintype.card V) (max Δ 1)).run_isLocal (V := V)
      (Nat.logStar (Fintype.card V) + 3)).comp
      (isLocal_self (V := V) (fun v (_ : Unit) => (Fintype.equivFin V v : ℕ)))
    simpa [IsLocalG, linialCol] using h
  defective := fun G hG => by
    have hdeg : ∀ v, G.degree v ≤ max Δ 1 := fun v =>
      (degree_le_of_maxDegLE hG v).trans (le_max_left _ _)
    have hp : IsProper G (fun u => (Fintype.equivFin V u : ℕ)) := fun u v huv h =>
      huv.ne ((Fintype.equivFin V).injective (Fin.ext h))
    have := linial_isProper (n := Fintype.card V) hdeg hp (fun v => (Fintype.equivFin V v).isLt)
      (Nat.logStar (Fintype.card V) + 3)
    exact IsLegal.isDefective fun u v huv => this huv
  lt := fun G hG v => by
    have hdeg : ∀ v, G.degree v ≤ max Δ 1 := fun v =>
      (degree_le_of_maxDegLE hG v).trans (le_max_left _ _)
    have hp : IsProper G (fun u => (Fintype.equivFin V u : ℕ)) := fun u v huv h =>
      huv.ne ((Fintype.equivFin V).injective (Fin.ext h))
    exact linial_lt (le_max_right _ _) hdeg hp (fun v => (Fintype.equivFin V v).isLt) le_rfl v

/-- **Lemma 2.2(1), unconditional version** (with Linial's colouring of the H-sets instead of the
`(Δ+1)`-colouring of [BE09]): if `G` has arboricity `≤ a` and `n (2a)^L < (A+1)^L`, the procedure
computes a legal colouring with colours `≤ A`. -/
theorem legalColoring_linial {G : SimpleGraph V} {a A L : ℕ} (hG : G.ArboricityLE a)
    (hL : Fintype.card V * (2 * a) ^ L < (A + 1) ^ L) :
    IsLegal G (legalCol A L (max (16 * (max A 1) ^ 2) 256) (linialCol A) G) ∧
      ∀ v, legalCol A L (max (16 * (max A 1) ^ 2) 256) (linialCol A) G v ≤ A :=
  legalColoring_spec hG.hasOutDegLE hL (linialAlg A)

/-- The unconditional legal colouring takes `L + log* n + 4 + (L·max(16A², 256) - 1)` rounds. -/
theorem legalColoring_linial_isLocal (A L : ℕ) :
    IsLocalG (L * max (16 * (max A 1) ^ 2) 256 - 1 + (1 + (Nat.logStar (Fintype.card V) + 3 + L)))
      (legalCol (V := V) A L (max (16 * (max A 1) ^ 2) 256) (linialCol A)) :=
  legalCol_isLocal _ _ _ (linialAlg A).isLocal

end Podc.ArbdefectiveColoring
