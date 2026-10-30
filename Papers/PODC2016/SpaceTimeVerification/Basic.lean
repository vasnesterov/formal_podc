import Mathlib
import Cslib.Computability.Distributed.Local.Locality

/-!
# `t`-round proof labeling schemes: the model

Basic notions for *Space-Time Tradeoffs for Distributed Verification* (R. Ostrovsky, M. Perry,
W. Rosenbaum; PODC 2016 brief announcement by M. Baruch, R. Ostrovsky, W. Rosenbaum; full version
arXiv:1605.06814).

* A *configuration* is a graph `G : SimpleGraph V` on a vertex type `V : Type` with states
  (inputs) `I : V → ι`. Configurations of all sizes live on different vertex types, so one scheme
  can be run on a graph and on a connected component of it (Theorem 7 needs this).
* `BallIso t G x v G' x' w`: the labelled radius-`t` balls of `v` in `G` and of `w` in `G'` are
  isomorphic. Explicitly, a map `φ` sends `v` to `w`, is injective on the ball, preserves the
  labelling `x` on the nodes at distance `≤ t`, and is a bijection between the neighbourhoods of
  every node at distance `< t` and of its image. This is exactly the information a node gathers
  in `t` synchronous rounds when it may use identifiers but its output does not depend on them
  (the paper's rule, Section 2.1: "an algorithm has the same output for all legal assignments of
  unique IDs"): the nodes at distance `≤ t` with their states and labels, and the edges incident
  to nodes at distance `< t`. Edges between two nodes at distance exactly `t` are not seen.
* `TPLS ι Λ F P t`: a `t`-PLS for the predicate `P` on the family `F`: a prover, a verifier whose
  output at `v` is invariant under `BallIso t`, completeness and soundness on all finite
  configurations of `F`.
* The three ways to produce `BallIso` used in the lower bounds: `ballIso_of_gAgree` (same vertex
  type, the graphs agree around `v` in the sense of CSLib's `GAgree`), `ballIso_comap` (renaming
  the vertices by an equivalence) and `ballIso_induce` (restriction to a union of connected
  components).
-/

namespace Podc.SpaceTimeVerification

open SimpleGraph

-- CSLib candidate
/-- The labelled radius-`t` ball of `v` in `G` (labelling `x`) is isomorphic to that of `w` in `G'`
(labelling `x'`), witnessed by `φ`: `φ v = w`, `φ` is injective on the ball, preserves labels on
it, and maps the neighbourhood of every node at distance `< t` bijectively onto the neighbourhood
of its image. -/
def BallIso {V W α : Type*} (t : ℕ) (G : SimpleGraph V) (x : V → α) (v : V)
    (G' : SimpleGraph W) (x' : W → α) (w : W) : Prop :=
  ∃ φ : V → W, φ v = w ∧
    (∀ a b, G.edist v a ≤ t → G.edist v b ≤ t → φ a = φ b → a = b) ∧
    (∀ a, G.edist v a ≤ t → x' (φ a) = x a) ∧
    (∀ a, G.edist v a < t → ∀ b, G.Adj a b → G'.Adj (φ a) (φ b)) ∧
    (∀ a, G.edist v a < t → ∀ b', G'.Adj (φ a) b' → ∃ b, G.Adj a b ∧ φ b = b')

/-- A property of configurations (graph and states) of every vertex type. -/
abbrev CProp (ι : Type) := ∀ V : Type, SimpleGraph V → (V → ι) → Prop

-- CSLib candidate
/-- A `t`-round proof labeling scheme (`t`-PLS, Section 2.2) for the predicate `P` on the family
`F`, with labels in `Λ`. The verifier's output at `v` (`verify G I ℓ v`: "`v` accepts") depends
only on the labelled radius-`t` ball of `v` up to isomorphism (`isLocal`). Completeness: on every
legal configuration the prover's labels are accepted everywhere. Soundness: if every node accepts
some labelling, the configuration is legal. -/
structure TPLS (ι Λ : Type) (F P : CProp ι) (t : ℕ) where
  /-- The prover (an oracle that sees the whole configuration). -/
  prove : ∀ {V : Type}, SimpleGraph V → (V → ι) → V → Λ
  /-- The verifier: `verify G I ℓ v` means that `v` outputs `true`. -/
  verify : ∀ {V : Type}, SimpleGraph V → (V → ι) → (V → Λ) → V → Prop
  /-- The output only depends on the labelled `t`-ball up to isomorphism. -/
  isLocal : ∀ {V W : Type} (G : SimpleGraph V) (I : V → ι) (ℓ : V → Λ) (v : V)
    (G' : SimpleGraph W) (I' : W → ι) (ℓ' : W → Λ) (w : W),
    BallIso t G (fun u => (I u, ℓ u)) v G' (fun u => (I' u, ℓ' u)) w →
      verify G I ℓ v → verify G' I' ℓ' w
  /-- Completeness. -/
  complete : ∀ {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι), F V G I → P V G I →
    ∀ v, verify G I (prove G I) v
  /-- Soundness. -/
  sound : ∀ {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι), F V G I →
    ∀ ℓ : V → Λ, (∀ v, verify G I ℓ v) → P V G I

/-- The label size of a `t`-PLS on legal configurations with `n` nodes is at most `L n`
(the paper's *verification complexity*), for a size function `size` on labels. -/
def TPLS.CostLE {ι Λ : Type} {F P : CProp ι} {t : ℕ} (S : TPLS ι Λ F P t) (size : Λ → ℕ)
    (L : ℕ → ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (I : V → ι), F V G I → P V G I →
    ∀ v, size (S.prove G I v) ≤ L (Fintype.card V)

/-! ### Producing ball isomorphisms -/

section BallIso

variable {V W α : Type*} {t : ℕ}

/-- Same vertex type: if `G` and `G'` have the same edges at all nodes at distance `< t` from `v`
(CSLib's `GAgree`, distances in `G`) and the labellings agree on the `t`-ball, the balls are
isomorphic (via the identity). -/
lemma ballIso_of_gAgree {G G' : SimpleGraph V} {x x' : V → α} {v : V}
    (hG : Cslib.Local.GAgree G G' v t) (hx : ∀ a, G.edist v a ≤ t → x' a = x a) :
    BallIso t G x v G' x' v :=
  ⟨id, rfl, fun _ _ _ _ h => h, hx, fun _ ha b hab => (hG ha b).1 hab,
    fun _ ha b' hab => ⟨b', (hG ha b').2 hab, rfl⟩⟩

/-- Renaming the vertices by an equivalence `e` gives an isomorphic ball. -/
lemma ballIso_comap (e : V ≃ W) (G : SimpleGraph V) (x : V → α) (v : V) :
    BallIso t G x v (G.comap e.symm) (x ∘ e.symm) (e v) := by
  refine ⟨e, rfl, fun _ _ _ _ h => e.injective h, fun _ _ => by simp, fun _ _ b hab => ?_,
    fun _ _ b' hab => ⟨e.symm b', ?_, by simp⟩⟩
  · simpa using hab
  · simpa using hab

/-- A node of a set closed under adjacency (a union of connected components) only reaches nodes
of that set. -/
lemma mem_of_reachable {G : SimpleGraph V} {S : Set V} (hS : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S)
    {a b : V} (ha : a ∈ S) (h : G.Reachable a b) : b ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ha
  | cons hadj _ ih => exact ih (hS _ ha _ hadj)

/-- Restricting to a union of connected components `S` does not change the ball of a node of
`S`. -/
lemma ballIso_induce {G : SimpleGraph V} {S : Set V} (hS : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S)
    (x : V → α) (w : S) : BallIso t G x w.1 (G.induce S) (x ∘ Subtype.val) w := by
  classical
  have hmem : ∀ a, G.edist w.1 a ≤ t → a ∈ S := fun a ha =>
    mem_of_reachable hS w.2 (edist_ne_top_iff_reachable.1 (ne_top_of_le_ne_top
      (by simp) ha))
  let φ : V → S := fun a => if h : a ∈ S then ⟨a, h⟩ else w
  have hφ : ∀ a (h : a ∈ S), φ a = ⟨a, h⟩ := fun a h => by simp [φ, h]
  refine ⟨φ, by simp [hφ w.1 w.2], fun a b ha hb h => ?_, fun a ha => ?_,
    fun a ha b hab => ?_, fun a ha b' hab => ?_⟩
  · rw [hφ a (hmem a ha), hφ b (hmem b hb)] at h
    exact congrArg Subtype.val h
  · simp [hφ a (hmem a ha)]
  · have ha' := hmem a ha.le
    rw [hφ a ha', hφ b (hS a ha' b hab)]
    simpa using hab
  · have ha' := hmem a ha.le
    refine ⟨b'.1, ?_, ?_⟩
    · rw [hφ a ha'] at hab
      simpa using hab
    · simp [hφ b'.1 b'.2]

end BallIso

end Podc.SpaceTimeVerification
