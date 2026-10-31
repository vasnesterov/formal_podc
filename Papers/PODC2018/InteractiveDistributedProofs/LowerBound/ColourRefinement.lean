import Mathlib

/-!
# Colour-refinement certificates for asymmetry and non-isomorphism

To show that a concrete finite graph has no non-trivial automorphism, or that two concrete graphs are
not isomorphic, without enumerating permutations, we check a *colour-refinement certificate* by
`decide`.

Graphs are given by Boolean adjacency functions `g : V → V → Bool`, `h : W → W → Bool`. A refinement
step from colourings `(c, d)` (of `V` and `W`) to `(c', d')` is valid (`RefineStep`) if two vertices
`v ∈ V`, `w ∈ W` that have the same old colour and, for every old colour `κ`, the same number of
neighbours of colour `κ`, get the same new colour. Every adjacency-preserving bijection `ρ : V → W`
maps a vertex to a vertex of the same colour at every step of a valid chain starting from a constant
colouring (`preserve_chain`). Consequently:

* `eq_id_of_refine`: if the final colouring of a graph is injective, every automorphism is the
  identity;
* `not_iso_of_refine`: if some final colour of `V` does not occur in `W`, there is no adjacency
  preserving bijection `V → W`.

The colourings are supplied as literal tables (`tbl`), produced by an external run of colour
refinement; only the certificate is checked in Lean.
-/

-- CSLib candidate (general graph-theory tool)

open Finset

namespace Podc.InteractiveDistributedProofs.LowerBound.ColourRefinement

variable {V W : Type*} [Fintype V] [Fintype W]

/-- The number of `g`-neighbours of `v` having colour `κ` under `c`. -/
def nbrCount (g : V → V → Bool) (c : V → ℕ) (v : V) (κ : ℕ) : ℕ :=
  (univ.filter fun u => g v u = true ∧ c u = κ).card

/-- A valid refinement step from colourings `(c, d)` to `(c', d')` of the graphs `g` on `V` and `h` on
`W`: equal old colour and equal neighbour-colour counts (for every colour occurring in `c` or `d`)
force equal new colours. -/
def RefineStep (g : V → V → Bool) (h : W → W → Bool) (c c' : V → ℕ) (d d' : W → ℕ) : Prop :=
  ∀ v w, c v = d w → (∀ u, nbrCount g c v (c u) = nbrCount h d w (c u)) →
    (∀ u, nbrCount g c v (d u) = nbrCount h d w (d u)) → c' v = d' w

instance (g : V → V → Bool) (h : W → W → Bool) (c c' : V → ℕ) (d d' : W → ℕ) :
    Decidable (RefineStep g h c c' d d') :=
  inferInstanceAs (Decidable (∀ v w, c v = d w → (∀ u, nbrCount g c v (c u) = nbrCount h d w (c u)) →
    (∀ u, nbrCount g c v (d u) = nbrCount h d w (d u)) → c' v = d' w))

variable {g : V → V → Bool} {h : W → W → Bool}

/-- An adjacency-preserving bijection that preserves a colouring preserves the neighbour counts. -/
theorem nbrCount_map {ρ : V → W} (hρ : Function.Bijective ρ)
    (hadj : ∀ u v, h (ρ u) (ρ v) = g u v) {c : V → ℕ} {d : W → ℕ} (hc : ∀ v, d (ρ v) = c v)
    (v : V) (κ : ℕ) : nbrCount h d (ρ v) κ = nbrCount g c v κ := by
  unfold nbrCount
  symm
  refine Finset.card_equiv (Equiv.ofBijective ρ hρ) fun u => ?_
  simp [hadj, hc]

/-- One valid step preserves colour-preservation by `ρ`. -/
theorem RefineStep.preserve {c c' : V → ℕ} {d d' : W → ℕ} (hs : RefineStep g h c c' d d')
    {ρ : V → W} (hρ : Function.Bijective ρ) (hadj : ∀ u v, h (ρ u) (ρ v) = g u v)
    (hc : ∀ v, d (ρ v) = c v) (v : V) : d' (ρ v) = c' v :=
  (hs v (ρ v) (hc v).symm (fun _ => (nbrCount_map hρ hadj hc v _).symm)
    (fun _ => (nbrCount_map hρ hadj hc v _).symm)).symm

/-- Along a valid chain of refinement steps starting from colourings that agree everywhere, every
adjacency-preserving bijection preserves the colours. -/
theorem preserve_chain (c : ℕ → V → ℕ) (d : ℕ → W → ℕ) (n : ℕ) (h0 : ∀ v w, c 0 v = d 0 w)
    (hs : ∀ j < n, RefineStep g h (c j) (c (j + 1)) (d j) (d (j + 1)))
    {ρ : V → W} (hρ : Function.Bijective ρ) (hadj : ∀ u v, h (ρ u) (ρ v) = g u v) :
    ∀ v, d n (ρ v) = c n v := by
  induction n with
  | zero => exact fun v => (h0 v (ρ v)).symm
  | succ n ih =>
    exact (hs n n.lt_succ_self).preserve hρ hadj
      (ih fun j hj => hs j (Nat.lt_succ_of_lt hj))

/-- **Asymmetry certificate.** If a valid chain ends in an injective colouring, the only
adjacency-preserving bijection of `g` is the identity. -/
theorem eq_id_of_refine (c : ℕ → V → ℕ) (n : ℕ) (h0 : ∀ v w, c 0 v = c 0 w)
    (hs : ∀ j < n, RefineStep g g (c j) (c (j + 1)) (c j) (c (j + 1)))
    (hinj : ∀ u v, c n u = c n v → u = v)
    {ρ : V → V} (hρ : Function.Bijective ρ) (hadj : ∀ u v, g (ρ u) (ρ v) = g u v) : ρ = id :=
  funext fun v => hinj _ _ (preserve_chain c c n h0 hs hρ hadj v)

/-- **Non-isomorphism certificate.** If after a valid joint chain some colour of `V` occurs nowhere in
`W`, there is no adjacency-preserving bijection `V → W`. -/
theorem not_iso_of_refine (c : ℕ → V → ℕ) (d : ℕ → W → ℕ) (n : ℕ) (h0 : ∀ v w, c 0 v = d 0 w)
    (hs : ∀ j < n, RefineStep g h (c j) (c (j + 1)) (d j) (d (j + 1)))
    (hnew : ∃ v, ∀ w, d n w ≠ c n v)
    {ρ : V → W} (hρ : Function.Bijective ρ) (hadj : ∀ u v, h (ρ u) (ρ v) = g u v) : False := by
  obtain ⟨v, hv⟩ := hnew
  exact hv (ρ v) (preserve_chain c d n h0 hs hρ hadj v)

/-- A colouring sequence read off a literal table: row `j`, entry at position `idx v`. -/
def tbl (idx : V → ℕ) (t : List (List ℕ)) : ℕ → V → ℕ :=
  fun j v => (t.getD j []).getD (idx v) 0

end Podc.InteractiveDistributedProofs.LowerBound.ColourRefinement
