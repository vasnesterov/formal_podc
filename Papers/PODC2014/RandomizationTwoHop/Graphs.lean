import Mathlib

-- CSLib candidate (paper-local for now; see README)

/-!
# Labelled graphs, 2-hop colourings, factors and prime graphs

Emek, Pfister, Seidel, Wattenhofer, *Anonymous Networks: Randomization = 2-Hop Coloring*,
PODC 2014, §1.1 and §2.3.1.

* `LGraph L`: a labelled graph `G = (V, E, ℓ)`: finite, connected, simple, labels in `L`.
* `IsKHopColoring G k c`: `c u ≠ c v` whenever `u ≠ v` are joined by a walk of length `≤ k`;
  `IsTwoHopColoring` is the case `k = 2` (`isTwoHopColoring_iff`: adjacent nodes and nodes with a
  common neighbour get different colours).
* `IsLocalIso`: a label-preserving map whose restriction to every neighbourhood `Γ(v)` is a
  bijection onto `Γ(f v)` (a covering map). `IsFactorMap X Y f`: a surjective local isomorphism;
  then `Y` is a *factor* of `X` (paper: `Y ≤_f X`).
* `Isomorphic X Y`, `Prime X` (every factor of `X` is isomorphic to `X`).
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph

/-- A labelled graph (paper §1.1): a finite connected simple graph with a labelling `lab`. -/
structure LGraph (L : Type) where
  /-- The nodes. -/
  V : Type
  [finite : Finite V]
  /-- The (simple, undirected) graph. -/
  G : SimpleGraph V
  /-- Only connected graphs are considered. -/
  conn : G.Connected
  /-- The labelling function. -/
  lab : V → L

attribute [instance] LGraph.finite

namespace LGraph

variable {L L' : Type}

/-- The same graph with another labelling. -/
def withLab (X : LGraph L) (l : X.V → L') : LGraph L' := ⟨X.V, X.G, X.conn, l⟩

/-- Apply a function to all labels (e.g. forget a component of a tuple label). -/
abbrev map (f : L → L') (X : LGraph L) : LGraph L' := X.withLab (f ∘ X.lab)

instance (X : LGraph L) : Nonempty X.V := X.conn.nonempty

end LGraph

/-- `c` is a `k`-hop colouring of `G` (§1.1): nodes `u ≠ v` joined by a walk with at most `k`
edges get different colours. -/
def IsKHopColoring {V C : Type} (G : SimpleGraph V) (k : ℕ) (c : V → C) : Prop :=
  ∀ u v, u ≠ v → (∃ p : G.Walk u v, p.length ≤ k) → c u ≠ c v

/-- A 2-hop colouring. -/
abbrev IsTwoHopColoring {V C : Type} (G : SimpleGraph V) (c : V → C) : Prop :=
  IsKHopColoring G 2 c

theorem isTwoHopColoring_iff {V C : Type} (G : SimpleGraph V) (c : V → C) :
    IsTwoHopColoring G c ↔
      (∀ u v, G.Adj u v → c u ≠ c v) ∧ ∀ w u v, G.Adj w u → G.Adj w v → u ≠ v → c u ≠ c v := by
  constructor
  · intro h
    refine ⟨fun u v huv => h u v huv.ne ⟨Walk.cons huv Walk.nil, by simp⟩, ?_⟩
    intro w u v hwu hwv hne
    exact h u v hne ⟨Walk.cons hwu.symm (Walk.cons hwv Walk.nil), by simp⟩
  · rintro ⟨h1, h2⟩ u v hne ⟨p, hp⟩
    match p, hp with
    | .nil, _ => exact absurd rfl hne
    | .cons h .nil, _ => exact h1 _ _ h
    | .cons h (.cons h' .nil), _ => exact h2 _ _ _ h.symm h' hne

variable {L : Type}

/-- A 2-hop colouring of `G` makes neighbours of a node have pairwise different colours. -/
theorem IsTwoHopColoring.injOn_nbhd {V C : Type} {G : SimpleGraph V} {c : V → C}
    (h : IsTwoHopColoring G c) (v : V) : Set.InjOn c (G.neighborSet v) := by
  intro x hx y hy hxy
  by_contra hne
  exact ((isTwoHopColoring_iff G c).1 h).2 v x y hx hy hne hxy

theorem IsTwoHopColoring.ne_of_adj {V C : Type} {G : SimpleGraph V} {c : V → C}
    (h : IsTwoHopColoring G c) {u v : V} (huv : G.Adj u v) : c u ≠ c v :=
  ((isTwoHopColoring_iff G c).1 h).1 u v huv

/-- A colouring that refines a 2-hop colouring is a 2-hop colouring. -/
theorem IsTwoHopColoring.of_comp {V C D : Type} {G : SimpleGraph V} {c : V → C} (g : C → D)
    (h : IsTwoHopColoring G (g ∘ c)) : IsTwoHopColoring G c := by
  intro u v hne hp hc
  exact h u v hne hp (by simp [hc])

/-! ### Local isomorphisms (covering maps) and factors -/

/-- `f` is a label-preserving local isomorphism from `(G, lG)` to `(H, lH)`: for every node `v`,
the restriction of `f` to `Γ(v)` is a bijection onto `Γ(f v)` (property 3 of a factorizing map,
§2.3.1), and labels are preserved (property 2). -/
structure IsLocalIso {V W : Type} (G : SimpleGraph V) (lG : V → L) (H : SimpleGraph W)
    (lH : W → L) (f : V → W) : Prop where
  lab : ∀ v, lH (f v) = lG v
  bij : ∀ v, Set.BijOn f (G.neighborSet v) (H.neighborSet (f v))

/-- `f : X.V → Y.V` is a *factorizing map* (§2.3.1): surjective, label-preserving, and a local
isomorphism. Then `Y` is a *factor* of `X` (paper: `Y ≤_f X`) and `X` a *product* of `Y`. -/
structure IsFactorMap (X Y : LGraph L) (f : X.V → Y.V) : Prop extends
    IsLocalIso X.G X.lab Y.G Y.lab f where
  surj : Function.Surjective f

/-- `Y` is a factor of `X`. -/
def IsFactor (Y X : LGraph L) : Prop := ∃ f, IsFactorMap X Y f

/-- Isomorphic labelled graphs: a bijective factorizing map exists. -/
def Isomorphic (X Y : LGraph L) : Prop := ∃ f, IsFactorMap X Y f ∧ Function.Bijective f

/-- A labelled graph is *prime* (§2.3.1, cf. Boldi–Vigna) if all its factors are isomorphic to
it. -/
def Prime (X : LGraph L) : Prop := ∀ (Y : LGraph L) (f : X.V → Y.V), IsFactorMap X Y f → Isomorphic X Y

section
variable {V W U : Type} {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph U}
  {lG : V → L} {lH : W → L} {lK : U → L}

theorem IsLocalIso.adj {f : V → W} (hf : IsLocalIso G lG H lH f) {u v : V} (h : G.Adj u v) :
    H.Adj (f u) (f v) := (hf.bij u).mapsTo h

theorem IsLocalIso.comp {f : V → W} {g : W → U} (hf : IsLocalIso G lG H lH f)
    (hg : IsLocalIso H lH K lK g) : IsLocalIso G lG K lK (g ∘ f) where
  lab v := by simp [hg.lab, hf.lab]
  bij v := (hg.bij (f v)).comp (hf.bij v)

theorem IsLocalIso.id : IsLocalIso G lG G lG id where
  lab _ := rfl
  bij _ := Set.bijOn_id _

/-- A bijective local isomorphism reflects adjacency. -/
theorem IsLocalIso.adj_iff_of_injective {f : V → W} (hf : IsLocalIso G lG H lH f)
    (hi : Function.Injective f) {u v : V} : H.Adj (f u) (f v) ↔ G.Adj u v := by
  refine ⟨fun h => ?_, hf.adj⟩
  obtain ⟨x, hx, hxv⟩ := (hf.bij u).surjOn h
  rw [hi hxv] at hx
  exact hx

/-- The image of a 2-hop coloured graph (with colours read off the labels) under a surjective
local isomorphism is 2-hop coloured. (§2.3.1: "the factor of a 2-hop colored graph is also 2-hop
colored".) -/
theorem IsLocalIso.twoHop {C : Type} (g : L → C) {f : V → W} (hf : IsLocalIso G lG H lH f)
    (hs : Function.Surjective f) (h : IsTwoHopColoring G (g ∘ lG)) :
    IsTwoHopColoring H (g ∘ lH) := by
  rw [isTwoHopColoring_iff] at h ⊢
  refine ⟨fun u' v' huv => ?_, fun w' u' v' hu hv hne => ?_⟩
  · obtain ⟨u, rfl⟩ := hs u'
    obtain ⟨v, hv, rfl⟩ := (hf.bij u).surjOn huv
    have := h.1 u v hv
    simpa [Function.comp, hf.lab] using this
  · obtain ⟨w, rfl⟩ := hs w'
    obtain ⟨u, hu', rfl⟩ := (hf.bij w).surjOn hu
    obtain ⟨v, hv', rfl⟩ := (hf.bij w).surjOn hv
    have hne' : u ≠ v := fun e => hne (e ▸ rfl)
    have := h.2 w u v hu' hv' hne'
    simpa [Function.comp, hf.lab] using this

end

theorem IsFactorMap.comp {X Y Z : LGraph L} {f : X.V → Y.V} {g : Y.V → Z.V}
    (hf : IsFactorMap X Y f) (hg : IsFactorMap Y Z g) : IsFactorMap X Z (g ∘ f) :=
  { hf.toIsLocalIso.comp hg.toIsLocalIso with surj := hg.surj.comp hf.surj }

theorem IsFactorMap.id (X : LGraph L) : IsFactorMap X X id :=
  { IsLocalIso.id with surj := Function.surjective_id }

/-- Isomorphism is symmetric. -/
theorem Isomorphic.symm {X Y : LGraph L} (h : Isomorphic X Y) : Isomorphic Y X := by
  obtain ⟨f, hf, hb⟩ := h
  let e := Equiv.ofBijective f hb
  refine ⟨e.symm, ⟨⟨fun v => ?_, fun v => ?_⟩, e.symm.surjective⟩, e.symm.bijective⟩
  · conv_lhs => rw [← hf.lab (e.symm v)]
    simp [e, Equiv.ofBijective_apply_symm_apply]
  · refine ⟨fun x hx => ?_, e.symm.injective.injOn, fun x hx => ⟨e x, ?_, by simp⟩⟩
    · have : Y.G.Adj (f (e.symm v)) (f (e.symm x)) := by simpa [e, Equiv.ofBijective_apply_symm_apply] using hx
      exact (hf.adj_iff_of_injective hb.1).1 this
    · have : X.G.Adj (e.symm v) x := hx
      have := hf.adj this
      simpa [e, Equiv.ofBijective_apply_symm_apply] using this

/-- Being prime is the same as: every factorizing map out of `X` is bijective. -/
theorem prime_iff_bijective (X : LGraph L) :
    Prime X ↔ ∀ (Y : LGraph L) (f : X.V → Y.V), IsFactorMap X Y f → Function.Bijective f := by
  constructor
  · intro h Y f hf
    obtain ⟨g, -, hg⟩ := h Y f hf
    have hcard : Nat.card X.V = Nat.card Y.V := Nat.card_eq_of_bijective g hg
    exact hf.surj.bijective_of_nat_card_le hcard.le
  · intro h Y f hf
    exact ⟨f, hf, h Y f hf⟩

end Podc.RandomizationTwoHop
