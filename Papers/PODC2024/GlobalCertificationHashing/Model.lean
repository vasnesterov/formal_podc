import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic

/-!
# Global certification (Bousquet–Feuilloley–Zeitoun, PODC 2024, Section 2)

The model of *global certification*: every node of a network sees its own identifier, the set of
identifiers of its neighbours, and one **global** certificate shared by all nodes; a *verification
algorithm* is an arbitrary predicate on such views.

Identifiers are natural numbers in `{0, …, M(n) - 1}`, assigned injectively. Certificates of size
`s(n)` are `s(n)`-bit strings, which we encode as natural numbers `c < 2 ^ s(n)`. This encoding
fixes the certificate set of size `2 ^ s(n)` of the paper's definition to `{0, …, 2 ^ s(n) - 1}`
for every `n`: in particular the verifier does **not** learn `n` (or `s(n)`) from the certificate
for free. `IsGlobalScheme.toAbstract` shows that our notion implies the paper's literal definition
(where the certificate set may be any set of size `2 ^ s(n)`), so upper bounds proved here are
upper bounds in the paper's sense.
-/

namespace Podc.GlobalCertificationHashing

/-- A graph property, for graphs on an arbitrary finite vertex type. -/
abbrev GraphProperty := ∀ (V : Type) [Fintype V], SimpleGraph V → Prop

/-- A verification algorithm (Definition 5): any predicate (no computability required) on the
view of a node — its identifier, the set of its neighbours' identifiers, and the global
certificate. -/
abbrev Verifier := ℕ → Set ℕ → ℕ → Prop

/-- An identifier assignment with range `M`: an injective map `V → {0, …, M - 1}`. -/
def IsIdAssignment {V : Type} (M : ℕ) (Id : V → ℕ) : Prop :=
  Function.Injective Id ∧ ∀ v, Id v < M

/-- The view of `u`: own identifier and the set of identifiers of its neighbours. All nodes accept
the global certificate `c`. -/
def Accepts {V : Type} (A : Verifier) (G : SimpleGraph V) (Id : V → ℕ) (c : ℕ) : Prop :=
  ∀ u, A (Id u) (Id '' {v | G.Adj u v}) c

/-- `A` is a global certification scheme for `P` with size `s` and identifier range `M`
(Section 2): for every graph `G` with `n` vertices, `G` satisfies `P` iff for every identifier
assignment with range `M n` there is a certificate of `s n` bits accepted by every node. -/
def IsGlobalScheme (P : GraphProperty) (M s : ℕ → ℕ) (A : Verifier) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    P V G ↔ ∀ Id : V → ℕ, IsIdAssignment (M (Fintype.card V)) Id →
      ∃ c < 2 ^ s (Fintype.card V), Accepts A G Id c

/-- There is a global certification scheme for `P` with size `s` and identifier range `M`. -/
def HasGlobalScheme (P : GraphProperty) (M s : ℕ → ℕ) : Prop :=
  ∃ A, IsGlobalScheme P M s A

/-- The paper's definition verbatim, with certificates from an arbitrary type `U`: one verifier
`A`, and for each `n` a certificate set `C` of size `2 ^ s(n)`. -/
def IsGlobalSchemeAbstract (U : Type) (P : GraphProperty) (M s : ℕ → ℕ)
    (A : ℕ → Set ℕ → U → Prop) : Prop :=
  ∀ n, ∃ C : Finset U, C.card = 2 ^ s n ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    Fintype.card V = n →
      (P V G ↔ ∀ Id : V → ℕ, IsIdAssignment (M n) Id →
        ∃ c ∈ C, ∀ u, A (Id u) (Id '' {v | G.Adj u v}) c)

/-- Our notion (certificates `c < 2 ^ s n`) is an instance of the paper's definition. -/
theorem IsGlobalScheme.toAbstract {P : GraphProperty} {M s : ℕ → ℕ} {A : Verifier}
    (h : IsGlobalScheme P M s A) : IsGlobalSchemeAbstract ℕ P M s A := by
  intro n
  refine ⟨Finset.range (2 ^ s n), Finset.card_range _, fun V _ G hV => ?_⟩
  subst hV
  rw [h V G]
  simp [Accepts]

/-- Schemes transfer along equivalent properties. -/
theorem IsGlobalScheme.congr {P Q : GraphProperty} {M s : ℕ → ℕ} {A : Verifier}
    (h : IsGlobalScheme P M s A) (hPQ : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      P V G ↔ Q V G) : IsGlobalScheme Q M s A :=
  fun V _ G => (hPQ V G).symm.trans (h V G)

end Podc.GlobalCertificationHashing
