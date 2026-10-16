import Podc.Graphs.ShortestWalks

/-!
# Restorable shortest path tiebreaking — definitions

Bodwin–Parter, *Restorable Shortest Path Tiebreaking for Edge-Faulty Graphs*, PODC 2021
(arXiv:2102.10174v4), Sections 2–3.

**Model.** `G` is a finite undirected unweighted graph (`SimpleGraph V`, `[Fintype V]`).
A fault set is a finset `F` of unordered pairs (`Sym2 V`); `G \ F` is `G.deleteEdges F`.
Paths are walks of `G` (type `G.Walk s t`, so selected paths for different fault sets live in the
same type); "a shortest path of `G \ F`" is `p.IsShortestIn F` (it avoids `F` and has length
`d_{G \ F}(s, t)`; such walks are automatically paths, `IsShortestIn.isPath`).
Distances are `edist` (`ℕ∞`, `⊤` for disconnected pairs).

* `Scheme G` — a replacement path tiebreaking scheme `π(s, t | F)`: an optional selected walk for
  every fault set and ordered pair (`none` plays the role of the paper's `π(s, t) := ∅`).
* `IsRPTS G f π` (Definitions 12, 15), `IsSymmetric` (13), `IsConsistent` (14), `IsStable` (16),
  `IsRestorable` (17, with the connectivity hypothesis that the paper's Definition 17 omits; the
  literal version is `IsRestorableLiteral`).
* `IsMinWalk G r A p`, `IsATW G f r` (Definition 18) and the generated scheme `atwScheme G r`.
-/

open Finset SimpleGraph SimpleGraph.Walk

namespace RestorableTiebreaking

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- A replacement path tiebreaking scheme: `π F s t` is the selected `s ⇝ t` path of `G \ F`
(`none` if there is none). -/
abbrev Scheme := Finset (Sym2 V) → ∀ s t : V, Option (G.Walk s t)

/-- Definition 12 for the graph `G \ F`: `π(·, · | F)` selects a shortest `s ⇝ t` path of `G \ F`
for every pair that is connected in `G \ F` (and nothing otherwise). -/
def IsTiebreakingFor (π : Scheme G) (F : Finset (Sym2 V)) : Prop :=
  (∀ s t p, π F s t = some p → p.IsShortestIn (F : Set (Sym2 V))) ∧
    ∀ s t, (G.deleteEdges F).Reachable s t → (π F s t).isSome

/-- Definition 15: an `f`-replacement path tiebreaking scheme (`f`-RPTS). -/
def IsRPTS (f : ℕ) (π : Scheme G) : Prop :=
  ∀ F : Finset (Sym2 V), #F ≤ f → IsTiebreakingFor G π F

/-- Definition 13: symmetry (`π(s, t | F)` and `π(t, s | F)` are the same undirected path). -/
def IsSymmetric (f : ℕ) (π : Scheme G) : Prop :=
  ∀ F : Finset (Sym2 V), #F ≤ f → ∀ s t, π F t s = (π F s t).map Walk.reverse

/-- Definition 14: consistency (if `u` precedes `v` on `π(s, t | F)`, then `π(u, v | F)` is the
contiguous subpath of `π(s, t | F)` from `u` to `v`). -/
def IsConsistent (f : ℕ) (π : Scheme G) : Prop :=
  ∀ F : Finset (Sym2 V), #F ≤ f → ∀ s t p, π F s t = some p →
    ∀ u v (p₁ : G.Walk s u) (q : G.Walk u v) (p₂ : G.Walk v t),
      p = p₁.append (q.append p₂) → π F u v = some q

/-- Definition 16: stability (a selected path only changes if one of its edges fails). -/
def IsStable (f : ℕ) (π : Scheme G) : Prop :=
  ∀ F : Finset (Sym2 V), #F + 1 ≤ f → ∀ (e : Sym2 V) s t p, π F s t = some p → e ∉ p.edges →
    π (insert e F) s t = some p

/-- Definition 17 (with the connectivity hypothesis of Theorem 2): for every nonempty fault set
`F` with `|F| ≤ f` and every pair `s, t` still connected in `G \ F`, there are a proper subset
`F' ⊊ F` and a vertex `x` such that `π(s, x | F') ∘ π(t, x | F')⁻¹` is a shortest `s ⇝ t` path
of `G \ F`. -/
def IsRestorable (f : ℕ) (π : Scheme G) : Prop :=
  ∀ F : Finset (Sym2 V), #F ≤ f → F.Nonempty → ∀ s t, (G.deleteEdges F).Reachable s t →
    ∃ F' ⊂ F, ∃ (x : V) (p : G.Walk s x) (q : G.Walk t x),
      π F' s x = some p ∧ π F' t x = some q ∧ (p.append q.reverse).IsShortestIn (F : Set (Sym2 V))

/-- Definition 17 read literally (no connectivity hypothesis). No graph with a bridge admits such
a scheme (`not_isRestorableLiteral`). -/
def IsRestorableLiteral (f : ℕ) (π : Scheme G) : Prop :=
  ∀ F : Finset (Sym2 V), #F ≤ f → F.Nonempty → ∀ s t,
    ∃ F' ⊂ F, ∃ (x : V) (p : G.Walk s x) (q : G.Walk t x),
      π F' s x = some p ∧ π F' t x = some q ∧ (p.append q.reverse).IsShortestIn (F : Set (Sym2 V))

/-! ### Antisymmetric tiebreaking weights -/

/-- The weights of the reweighted digraph `G*`: `w(u, v) = 1 + r(u, v)`. -/
def wstar (r : V → V → ℝ) : V → V → ℝ := fun a b => 1 + r a b

/-- `p` is the unique shortest `s ⇝ t` walk of `G* \ A`: it avoids `A` and every other walk
avoiding `A` is strictly heavier. -/
def IsMinWalk (r : V → V → ℝ) (A : Set (Sym2 V)) {s t : V} (p : G.Walk s t) : Prop :=
  p.Avoids A ∧ ∀ q : G.Walk s t, q.Avoids A → q ≠ p → p.dwt (wstar r) < q.dwt (wstar r)

/-- In `G* \ A`, every pair connected in `G \ A` has a unique shortest walk, and it is a shortest
walk of the unweighted graph `G \ A`. -/
def HasMinWalks (r : V → V → ℝ) (A : Set (Sym2 V)) : Prop :=
  ∀ s t, (G.deleteEdges A).Reachable s t →
    ∃ p : G.Walk s t, IsMinWalk G r A p ∧ p.IsShortestIn A

/-- Definition 18: an antisymmetric `f`-fault tiebreaking weight (ATW) function. -/
structure IsATW (f : ℕ) (r : V → V → ℝ) : Prop where
  antisymm : ∀ u v, G.Adj u v → r u v = - r v u
  tiebreak : ∀ F : Finset (Sym2 V), #F ≤ f → HasMinWalks G r F

/-- The RPTS generated by a weight function `r`: `π(s, t | F)` is the unique shortest `s ⇝ t`
walk of `G* \ F` (if any). -/
noncomputable def atwScheme (r : V → V → ℝ) : Scheme G := fun F s t =>
  open Classical in
  if h : ∃ p : G.Walk s t, IsMinWalk G r (F : Set (Sym2 V)) p then some h.choose else none

end RestorableTiebreaking
