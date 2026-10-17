import Papers.PODC2018.LocallyIterativeColoring.Main
import Cslib.Computability.Distributed.Local.Linial
import Podc.Local.Locality
import Mathlib

/-!
# Corollary 3.6 of [BEG18]: locally-iterative `(Δ + 1)`-colouring in `O(Δ) + log* n` rounds

Linial's algorithm (`Cslib/Computability/Distributed/Local/Linial.lean`: proper colouring with `< max (16Δ²) 256` colours
after `log* n + 3` rounds, from any proper colouring with colours `< n`, e.g. identifiers) followed
by `begColoring` (AG + standard colour reduction).
-/

namespace BEG18

open Cslib.LocallyIterative

/-- Palette size after Linial's phase. -/
def linialPalette (Δ : ℕ) : ℕ := max (16 * Δ ^ 2) 256

/-- Length of Linial's phase. -/
def linialRounds (n : ℕ) : ℕ := Nat.logStar n + 3

/-- The full algorithm of Corollary 3.6 of [BEG18]: Linial's algorithm for `log* n + 3` rounds, then
`begColoring` (AG for `q` rounds, then the standard colour reduction). -/
noncomputable def fullColoring (n Δ : ℕ) : Algorithm ℕ :=
  (linial n Δ).seq (linialRounds n) (begColoring Δ (linialPalette Δ))

/-- Total number of rounds of `fullColoring n Δ`. -/
noncomputable def fullRounds (n Δ : ℕ) : ℕ := linialRounds n + begRounds Δ (linialPalette Δ)

theorem fullRounds_le (n Δ : ℕ) : fullRounds n Δ ≤ Nat.logStar n + 16 * Δ + 71 := by
  have h1 := begRounds_le Δ (linialPalette Δ)
  have hK : linialPalette Δ ≤ (4 * Δ + 16) * (4 * Δ + 16) := by
    unfold linialPalette; apply max_le <;> nlinarith
  have hs : Nat.sqrt (linialPalette Δ) ≤ 4 * Δ + 16 :=
    (Nat.sqrt_le_sqrt hK).trans (Nat.sqrt_eq _).le
  unfold fullRounds linialRounds
  have : max (2 * Δ + 1) (Nat.sqrt (linialPalette Δ) + 1) ≤ 4 * Δ + 17 := by omega
  omega

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {n Δ : ℕ}

/-- **Corollary 3.6 of [BEG18] (locally-iterative property).** Every colouring computed by
`fullColoring n Δ` from a proper colouring with colours `< n` (e.g. distinct identifiers) on a
graph of maximum degree `≤ Δ` is proper. -/
theorem fullColoring_isProper (hdeg : ∀ v, G.degree v ≤ Δ) (hΔ : 1 ≤ Δ) {c₀ : V → ℕ}
    (hc₀ : IsProper G c₀) (hlt : ∀ v, c₀ v < n) (t : ℕ) :
    IsProper G ((fullColoring n Δ).run G c₀ t) := by
  rcases le_or_gt t (linialRounds n) with ht | ht
  · rw [fullColoring, Algorithm.run_seq_of_le _ _ _ ht]
    exact linial_isProper hdeg hc₀ hlt t
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht.le
    rw [fullColoring, Algorithm.run_seq_add]
    exact begColoring_isProper hdeg (linial_lt hΔ hdeg hc₀ hlt le_rfl)
      (linial_isProper hdeg hc₀ hlt _) s

/-- **Corollary 3.6 of [BEG18].** Any graph of maximum degree `≤ Δ` (`Δ ≥ 1`) with a proper
colouring by colours `< n` (e.g. distinct identifiers) is properly `(Δ + 1)`-coloured by the
locally-iterative algorithm `fullColoring n Δ` within `fullRounds n Δ ≤ log* n + 16 Δ + 71` rounds
(and stays so afterwards); all intermediate colourings are proper (`fullColoring_isProper`). -/
theorem fullColoring_le (hdeg : ∀ v, G.degree v ≤ Δ) (hΔ : 1 ≤ Δ) {c₀ : V → ℕ}
    (hc₀ : IsProper G c₀) (hlt : ∀ v, c₀ v < n) {t : ℕ} (ht : fullRounds n Δ ≤ t) (v : V) :
    (fullColoring n Δ).run G c₀ t v ≤ Δ := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le
    (show linialRounds n ≤ t by unfold fullRounds at ht; omega)
  rw [fullColoring, Algorithm.run_seq_add]
  exact begColoring_le hdeg (linial_lt hΔ hdeg hc₀ hlt le_rfl)
    (linial_isProper hdeg hc₀ hlt _) (by unfold fullRounds at ht; unfold linialPalette at ht; omega) v

omit [G.LocallyFinite] in
/-- `fullColoring n Δ` is a LOCAL algorithm with round complexity `fullRounds n Δ`: the output
colour of a node only depends on the graph and the initial colours within that distance. -/
theorem fullColoring_isLocal (n Δ : ℕ) :
    Cslib.Local.IsLocal (V := V) (fullRounds n Δ) fun G c₀ v =>
      (fullColoring n Δ).run G c₀ (fullRounds n Δ) v :=
  Algorithm.run_isLocal _ _

/-- Corollary 3.6 of [BEG18], packaged: proper `(Δ + 1)`-colouring after at most
`log* n + 16 Δ + 71` rounds, every round proper. -/
theorem corollary_3_6 (hdeg : ∀ v, G.degree v ≤ Δ) (hΔ : 1 ≤ Δ) {c₀ : V → ℕ}
    (hc₀ : IsProper G c₀) (hlt : ∀ v, c₀ v < n) :
    ∃ T ≤ Nat.logStar n + 16 * Δ + 71,
      (∀ t, IsProper G ((fullColoring n Δ).run G c₀ t)) ∧
      ∀ t ≥ T, ∀ v, (fullColoring n Δ).run G c₀ t v ≤ Δ :=
  ⟨fullRounds n Δ, fullRounds_le n Δ, fullColoring_isProper hdeg hΔ hc₀ hlt,
    fun _ ht v => fullColoring_le hdeg hΔ hc₀ hlt ht v⟩

end BEG18
