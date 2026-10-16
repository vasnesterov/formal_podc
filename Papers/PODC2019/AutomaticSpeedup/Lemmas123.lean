import Papers.PODC2019.AutomaticSpeedup.SuperweakDefs
import Papers.PODC2019.AutomaticSpeedup.Matching
import Papers.PODC2019.AutomaticSpeedup.Lemma3

/-!
# Lemmas 1–3 of Brandt (PODC 2019, §5.1)

Statements about `tritOne k`, the trit description of `Π'_1` derived from superweak
`k`-colouring.
-/

namespace AutomaticSpeedup

open Problem

-- The paper's `h_1(Δ)` consists of multisets of exactly `Δ` sets; our `nodeStepMax` (following §3)
-- also allows fewer elements, so the cardinality is a hypothesis here. Without it the statement fails
-- (`lemma_1_needs_card`: `{∅} ∈ (tritOne k).h Δ`).
/-- **Lemma 1.** If `Δ ≥ 2^(4^k + 1)`, every node configuration `Q ∈ h_1(Δ)` has a unique element
`P∞` of multiplicity at least `Δ - 2^(4^k)`, and `P∞` contains `11…1`. -/
theorem lemma_1 {k Δ : ℕ} (hk : 2 ≤ k) (hΔ : 2 ^ (4 ^ k + 1) ≤ Δ)
    {Q : Multiset (Set (Trit k))} (hQ : Q ∈ (tritOne k).h Δ) (hc : Multiset.card Q = Δ) :
    ∃ P, (Δ - 2 ^ (4 ^ k) ≤ Q.count P ∧ ones k ∈ P) ∧
      ∀ P', Δ - 2 ^ (4 ^ k) ≤ Q.count P' → P' = P :=
  lemma_1_card hk hΔ hQ hc

set_option linter.unusedVariables false in
open Classical in
/-- **Lemma 2.** Ports `0, …, Δ-1` of a node carry `Q 0, …, Q (Δ-1)` forming a configuration of
`h_1(Δ)`, and `α` marks each port `in`/`out` (`true`/`false`). Let `I` be the set of ports `i`
with `{Q i, P∞} ∉ g_1(Δ)` and `11…1 ∉ Q i`, and `N(J)` the set of ports `i` such that some
`j ∈ J` has `{Q i, Q j} ∈ g_1(Δ)` and `α i ≠ α j`. Then some `J* ⊆ I` has `|J*| > |N(J*)|` and
`α j ≠ α i` for all `j ∈ J*`, `i ∈ N(J*)`. -/
theorem lemma_2 {k Δ : ℕ} (hk : 2 ≤ k) (hΔ : 2 ^ (4 ^ k + 1) ≤ Δ) {Q : ℕ → Set (Trit k)}
    (hQ : (Multiset.range Δ).map Q ∈ (tritOne k).h Δ) {Pinf : Set (Trit k)}
    (hP : Δ - 2 ^ (4 ^ k) ≤ ((Multiset.range Δ).map Q).count Pinf ∧ ones k ∈ Pinf)
    (α : ℕ → Bool) :
    ∃ J ⊆ (Finset.range Δ).filter
        (fun i => ({Q i, Pinf} : Multiset _) ∉ (tritOne k).g Δ ∧ ones k ∉ Q i),
      ((Finset.range Δ).filter fun i =>
          ∃ j ∈ J, ({Q i, Q j} : Multiset _) ∈ (tritOne k).g Δ ∧ α i ≠ α j).card < J.card ∧
      ∀ j ∈ J, ∀ i ∈ (Finset.range Δ).filter
          (fun i => ∃ j ∈ J, ({Q i, Q j} : Multiset _) ∈ (tritOne k).g Δ ∧ α i ≠ α j),
        α j ≠ α i :=
  lemma_2_aux hΔ hQ hP α

/-- **Lemma 3.** On a class of `Δ`-regular graphs with `Δ ≥ 2^(4^k + 1)` whose inputs contain an
edge orientation, a `t`-round algorithm for `Π'_1` (in its trit description `tritOne k`) yields a
`t`-round algorithm for superweak `k'`-colouring, `k' = 2^(2^(5^k))`. -/
theorem lemma_3 {k : ℕ} (hk : 2 ≤ k) {I : Type} {n Δ t : ℕ} {𝒢 : Set (LGraph I n)}
    (hΔ : 2 ^ (4 ^ k + 1) ≤ Δ) (hreg : ∀ G ∈ 𝒢, ∀ v, G.deg v = Δ) {o : I → Bool}
    (hor : HasOrientation 𝒢 o) (h : SolvableIn 𝒢 (tritOne k) Δ t) :
    SolvableIn 𝒢 (superweak (2 ^ 2 ^ 5 ^ k)) Δ t :=
  lemma_3_aux hk hΔ hreg hor h

end AutomaticSpeedup
