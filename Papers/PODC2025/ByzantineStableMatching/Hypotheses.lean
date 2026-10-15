import Papers.PODC2025.ByzantineStableMatching.Problem
import Cslib.Computability.Distributed.Byzantine.LockStep.Agreement

/-!
# Byzantine broadcast / agreement results used as hypotheses

The paper's sufficiency proofs rely on classical protocols which we do not formalize; we state the
results we use as named propositions and take them as explicit hypotheses of the sufficiency
theorems (see `differencies.md`):

* `FitziMaurerBB` — [Fitzi–Maurer, DISC'98, Thm 2] (the paper's Theorem 10): unauthenticated
  synchronous BB on a fully-connected network against any adversary structure satisfying `Q3`.
* `DolevStrongBB` — [Dolev–Strong 1983]: authenticated synchronous BB on a fully-connected network
  against any number of corruptions (any adversary structure).
* `OmissionBA`, `OmissionBB` — the paper's Theorems 8 and 9 (Phase-King + one echo round): BA / BB
  among `L` (fully connected among themselves) tolerating `tL < k/3`, achieving BA/BB on reliable
  runs and termination + weak agreement when honest messages may be omitted.

We also prove the paper's Lemma 4 (the threshold structure satisfies `Q3`).
-/

namespace Papers.PODC2025.ByzantineStableMatching

open Cslib.Byzantine.LockStep Sum

/-- The `Q3` condition: no three admissible sets cover all parties. -/
def Q3 {P : Type*} (Z : AdvStructure P) : Prop :=
  ∀ B₁ ∈ Z, ∀ B₂ ∈ Z, ∀ B₃ ∈ Z, B₁ ∪ B₂ ∪ B₃ ≠ Set.univ

/-- [Fitzi–Maurer 1998, Theorem 2] (Theorem 10 of the paper), for finite value domains. -/
def FitziMaurerBB : Prop :=
  ∀ (P : Type) [Fintype P] [DecidableEq P] (V : Type) [Finite V] [Nonempty V]
    (Z : AdvStructure P), Q3 Z → ∀ s : P, Solvable (⊤ : SimpleGraph P) Z (BB s : Spec P V V)

/-- [Dolev–Strong 1983]: authenticated BB tolerating any set of corruptions. -/
def DolevStrongBB : Prop :=
  ∀ (P : Type) [Fintype P] [DecidableEq P] (V : Type) [Finite V] [Nonempty V]
    (Z : AdvStructure P) (s : P), SolvableAuth (⊤ : SimpleGraph P) Z (BB s : Spec P V V)

variable {k : ℕ}

/-- **Lemma 4** (combinatorial core): the threshold adversary structure satisfies `Q3` when
`tL < k/3` or `tR < k/3`. -/
theorem lemma4_Q3 {tL tR : ℕ} (h : 3 * tL < k ∨ 3 * tR < k) : Q3 (thresholds k tL tR) := by
  intro B₁ h₁ B₂ h₂ B₃ h₃ hU
  have key : ∀ (f : Fin k → Party k), Function.Injective f →
      (f ⁻¹' B₁).ncard + (f ⁻¹' B₂).ncard + (f ⁻¹' B₃).ncard ≥ k := by
    intro f _
    have : f ⁻¹' (B₁ ∪ B₂ ∪ B₃) = Set.univ := by rw [hU]; rfl
    have h' : (Set.univ : Set (Fin k)).ncard ≤ (f ⁻¹' B₁).ncard + (f ⁻¹' B₂).ncard +
        (f ⁻¹' B₃).ncard := by
      rw [← this, Set.preimage_union, Set.preimage_union]
      exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_right (Set.ncard_union_le _ _) _)
    simpa [Set.ncard_univ] using h'
  rcases h with h | h
  · have := key inl inl_injective
    have := h₁.1; have := h₂.1; have := h₃.1; omega
  · have := key inr inr_injective
    have := h₁.2; have := h₂.2; have := h₃.2; omega

/-- **Lemma 4**: BB is solvable on the fully-connected unauthenticated network if `tL < k/3` or
`tR < k/3` (assuming the Fitzi–Maurer theorem). -/
theorem lemma4 (hFM : FitziMaurerBB) {tL tR : ℕ} (h : 3 * tL < k ∨ 3 * tR < k)
    (V : Type) [Finite V] [Nonempty V] (s : Party k) :
    Solvable (fully k) (thresholds k tL tR) (BB s : Spec (Party k) V V) :=
  hFM (Party k) V _ (lemma4_Q3 h) s

/-! ## Theorems 8 and 9 (BA/BB among `L` with omissions) -/

/-- The network in which only the parties of `L` are (pairwise) connected; `R` is isolated. -/
def lClique (k : ℕ) : SimpleGraph (Party k) where
  Adj p q := p ≠ q ∧ p.isLeft ∧ q.isLeft
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] lemma lClique_adj (p q : Party k) :
    (lClique k).Adj p q ↔ p ≠ q ∧ p.isLeft ∧ q.isLeft := Iff.rfl

/-- Restrict a specification to the honest parties of `L`. -/
def onL {I O : Type*} (spec : Spec (Party k) I O) : Spec (Party k) I O :=
  fun x H dec => spec x {p | p ∈ H ∧ p.isLeft} dec

/-- **Theorem 8** of the paper (as a hypothesis): for `tL < k/3` there is a BA protocol among the
`k` parties of `L` (fully connected among themselves) which achieves BA (with non-`⊥` outputs) when
no message is omitted, and termination within `T` rounds and weak agreement even if honest messages
are omitted. Stated on `Party k` with `R` isolated (the `R`-parties' behaviour is irrelevant);
Byzantine sets may contain any parties of `R`. -/
def OmissionBA (k tL : ℕ) : Prop :=
  ∀ (V : Type) [Finite V] [Nonempty V], ∃ (M : Type) (alg : Protocol (Party k) V M (Option V))
    (T : ℕ), SolvesWithOmissions (lClique k) alg (thresholds k tL k)
      (onL (SomeSpec BA)) (onL WeakAgreement) T

/-- **Theorem 9** of the paper (as a hypothesis): BB among `L` with sender `inl s`, same guarantees
as `OmissionBA`. -/
def OmissionBB (k tL : ℕ) : Prop :=
  ∀ (V : Type) [Finite V] [Nonempty V] (s : Fin k), ∃ (M : Type)
    (alg : Protocol (Party k) V M (Option V)) (T : ℕ),
    SolvesWithOmissions (lClique k) alg (thresholds k tL k)
      (onL (SomeSpec (BB (inl s)))) (onL WeakAgreement) T

end Papers.PODC2025.ByzantineStableMatching
