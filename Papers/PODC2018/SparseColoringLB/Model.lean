import Mathlib
import Cslib.Computability.Distributed.Local.OnlineLocalLocality

-- CSLib candidate: Cslib/Computability/Distributed/Local/BallLowerBound.lean (BallAgree, BallLocal,
-- coloring_of_views, ballAgree_of_le, BallAgree.map, observation_2_4) and
-- Cslib/Foundations/Combinatorics/SimpleGraph/Ball.lean (Hom.edist_le, edist_map_embedding).

/-!
# The LOCAL model for colouring lower bounds (Aboulker–Bonamy–Bousquet–Esperet, PODC 2018)

A deterministic `r`-round LOCAL colouring algorithm on `n`-node networks is a map
`A : SimpleGraph V → V → β`, where `V` is the identifier space (`Fintype.card V = n`, every node knows
`n` because it knows `V`), and `A G v` is the colour output by node `v` in the network `G`. Following the
paper ("the output of each vertex `v` only depends on the labelled ball of radius `r` of `v`"), the
algorithm is `r`-local if `A G v` only depends on the subgraph induced by the closed ball of radius `r`
around `v` (`BallAgree`, `BallLocal`). This is slightly *more* information than `r` rounds of the LOCAL
model give (CSLib's `Cslib.Local.GAgree` does not contain the edges between two nodes at distance
exactly `r`), so lower bounds for `BallLocal` algorithms are stronger; see `BallLocal.of_isLocal`.

An algorithm `A` *colours* a graph `Γ` on a vertex type `W` if for every assignment of distinct
identifiers `e : W ≃ V`, adjacent nodes output different colours (`ColoursGraph`).

## Main results

* `coloring_of_views`: the indistinguishability argument behind Observation 2.4, in the sharp form
  used by our proofs: if every edge `xy` of a graph `K` (with identifiers `e₂`) is seen, from `x` and
  from `y`, exactly as some edge of an identifier assignment of `Γ`, then every `r`-local algorithm
  colouring `Γ` yields a colouring of `K` with the same colours.
* `ballAgree_of_le`: deleting edges far from `u` does not change the `r`-ball of `u`.
* `BallAgree.map`: agreement is preserved by renaming vertices injectively.
* `observation_2_4`: Observation 2.4 of the paper (Linial's argument) as stated, with rooted
  isomorphisms of induced balls.
-/

namespace Podc.SparseColoringLB

open SimpleGraph Cslib.Local

universe u₁ u₂ u₃ u₄

variable {V : Type u₁} {W : Type u₂} {W' : Type u₃} {β : Type u₄}

/-! ### Distances under graph homomorphisms and injective renamings -/

/-- Graph homomorphisms do not increase distances. -/
lemma Hom.edist_le {G : SimpleGraph W} {G' : SimpleGraph V} (φ : G →g G') (a b : W) :
    G'.edist (φ a) (φ b) ≤ G.edist a b := by
  by_cases h : G.Reachable a b
  · obtain ⟨w, hw⟩ := h.exists_walk_length_eq_edist
    rw [← hw]
    simpa using SimpleGraph.edist_le (w.map φ)
  · simp [edist_eq_top_of_not_reachable h]

/-- Renaming the vertices injectively preserves distances. -/
lemma edist_map_embedding (G : SimpleGraph W) (f : W ↪ V) (a b : W) :
    (G.map f).edist (f a) (f b) = G.edist a b := by
  apply le_antisymm
  · exact Hom.edist_le (Embedding.map f G).toHom a b
  · classical
    have : Nonempty W := ⟨a⟩
    let g : V → W := Function.invFun f
    have hg : ∀ x, g (f x) = x := Function.leftInverse_invFun f.injective
    let φ : G.map f →g G :=
      { toFun := g
        map_rel' := by
          intro x y hxy
          rw [map_adj] at hxy
          obtain ⟨x, y, hxy, rfl, rfl⟩ := hxy
          simpa [hg] using hxy }
    have := Hom.edist_le φ (f a) (f b)
    simpa [φ, hg] using this

/-- In `G.map f`, a vertex outside the range of `f` is isolated, hence at infinite distance. -/
lemma edist_map_of_notMem_range (G : SimpleGraph W) (f : W ↪ V) {a : W} {v : V}
    (hv : v ∉ Set.range f) : (G.map f).edist (f a) v = ⊤ := by
  apply edist_eq_top_of_not_reachable
  intro h
  obtain ⟨w⟩ := h
  -- every vertex of a walk starting in `range f` stays in `range f`
  have key : ∀ {x y : V} (p : (G.map f).Walk x y), x ∈ Set.range f → y ∈ Set.range f := by
    intro x y p
    induction p with
    | nil => exact id
    | cons h _ ih =>
      intro _
      rw [map_adj] at h
      obtain ⟨_, b, _, _, rfl⟩ := h
      exact ih ⟨b, rfl⟩
  exact hv (key w ⟨a, rfl⟩)

/-! ### Balls and local algorithms -/

/-- `u` sees the same labelled ball of radius `r` in `G` and `G'`: the same nodes at distance `≤ r`
(at the same distances) and the same edges among them, i.e. the same induced subgraph on the
closed ball. Node names are identifiers. -/
def BallAgree (G G' : SimpleGraph V) (u : V) (r : ℕ) : Prop :=
  GAgree G G' u r ∧
    ∀ x y, G.edist u x ≤ r → G.edist u y ≤ r → (G.Adj x y ↔ G'.Adj x y)

/-- An algorithm `A` (output `A G v` of node `v` in network `G`) is `r`-local: the output of a node
only depends on its labelled ball of radius `r` (the paper's model of an `r`-round LOCAL algorithm). -/
def BallLocal (r : ℕ) (A : SimpleGraph V → V → β) : Prop :=
  ∀ G G' u, BallAgree G G' u r → A G u = A G' u

/-- `A` colours `Γ`: for every assignment `e` of distinct identifiers to the nodes of `Γ`, adjacent
nodes output different colours. -/
def ColoursGraph (A : SimpleGraph V → V → β) (Γ : SimpleGraph W) : Prop :=
  ∀ e : W ≃ V, ∀ x y, Γ.Adj x y →
    A (Γ.map e.toEmbedding) (e x) ≠ A (Γ.map e.toEmbedding) (e y)

namespace BallAgree

variable {G G' G'' : SimpleGraph V} {u : V} {r : ℕ}

lemma refl (G : SimpleGraph V) (u : V) (r : ℕ) : BallAgree G G u r :=
  ⟨GAgree.rfl, fun _ _ _ _ => Iff.rfl⟩

lemma symm (h : BallAgree G G' u r) : BallAgree G' G u r :=
  ⟨h.1.symm, fun x y hx hy =>
    (h.2 x y ((h.1.edist_le_iff le_rfl).1 hx) ((h.1.edist_le_iff le_rfl).1 hy)).symm⟩

lemma trans (h₁ : BallAgree G G' u r) (h₂ : BallAgree G' G'' u r) : BallAgree G G'' u r :=
  ⟨h₁.1.trans h₂.1, fun x y hx hy =>
    (h₁.2 x y hx hy).trans
      (h₂.2 x y ((h₁.1.edist_le_iff le_rfl).2 hx) ((h₁.1.edist_le_iff le_rfl).2 hy))⟩

/-- Ball agreement gives ball agreement with any smaller radius. -/
lemma mono_radius (h : BallAgree G G' u r) {ρ : ℕ} (hρ : ρ ≤ r) : BallAgree G G' u ρ :=
  ⟨h.1.mono_radius hρ, fun x y hx hy =>
    h.2 x y (hx.trans (by exact_mod_cast hρ)) (hy.trans (by exact_mod_cast hρ))⟩

/-- Ball agreement with radius `r + 1` around `u` gives ball agreement with radius `r` around
every neighbour of `u`. -/
lemma of_adj (h : BallAgree G G' u (r + 1)) {v : V} (huv : G.Adj u v) : BallAgree G G' v r := by
  have hv : G.edist u v ≤ 1 := by rw [edist_eq_one_iff_adj.2 huv]
  refine ⟨h.1.mono hv (by omega), fun x y hx hy => h.2 x y ?_ ?_⟩
  · simpa [add_comm] using edist_le_natCast_add hv hx
  · simpa [add_comm] using edist_le_natCast_add hv hy

/-- Renaming vertices injectively preserves ball agreement. -/
lemma map {G G' : SimpleGraph W} {u : W} (f : W ↪ V) (h : BallAgree G G' u r) :
    BallAgree (G.map f) (G'.map f) (f u) r := by
  have hG : ∀ x, (G.map f).edist (f u) x ≤ r → ∃ a, f a = x := by
    intro x hx
    by_contra hne
    push Not at hne
    rw [edist_map_of_notMem_range G f (by rintro ⟨a, rfl⟩; exact hne a rfl)] at hx
    simp at hx
  refine ⟨?_, ?_⟩
  · intro x hx y
    obtain ⟨a, rfl⟩ := hG x (le_of_lt hx)
    rw [edist_map_embedding] at hx
    rw [map_adj, map_adj]
    constructor
    · rintro ⟨a', b, hab, ha, rfl⟩
      rw [f.injective ha] at hab
      exact ⟨a, b, (h.1 hx b).1 hab, rfl, rfl⟩
    · rintro ⟨a', b, hab, ha, rfl⟩
      rw [f.injective ha] at hab
      have := h.1.symm ((h.1.edist_lt_iff le_rfl).2 hx) b
      exact ⟨a, b, this.1 hab, rfl, rfl⟩
  · intro x y hx hy
    obtain ⟨a, rfl⟩ := hG x hx
    obtain ⟨b, rfl⟩ := hG y hy
    rw [edist_map_embedding] at hx hy
    simp only [map_adj_apply]
    exact h.2 a b hx hy

end BallAgree

/-- A `GAgree`-local algorithm (CSLib's notion of an `r`-round LOCAL algorithm; no inputs) is
`BallLocal r`: lower bounds for `BallLocal` algorithms apply to it. -/
lemma BallLocal.of_isLocal {r : ℕ} {A : SimpleGraph V → V → β}
    (h : IsLocal r (fun G (_ : V → Unit) v => A G v)) : BallLocal r A :=
  fun G G' u hu => h G (fun _ => ()) G' (fun _ => ()) u ⟨hu.1, fun _ _ => rfl⟩

/-- Conversely, a `BallLocal r` algorithm is computed in `r + 1` rounds (CSLib's `IsLocal`). -/
lemma BallLocal.isLocal_succ {r : ℕ} {A : SimpleGraph V → V → β} (h : BallLocal r A) :
    IsLocal (r + 1) (fun G (_ : V → Unit) v => A G v) := by
  intro G x G' x' u hu
  refine h G G' u ⟨hu.1.mono_radius (by omega), fun a b ha _ => hu.1 ?_ b⟩
  exact lt_of_le_of_lt ha (by exact_mod_cast Nat.lt_succ_self r)

/-- Relabelling a graph along an automorphism does not change it. -/
lemma map_trans_eq_of_aut {K : SimpleGraph W} (σ : Equiv.Perm W)
    (hσ : ∀ p q, K.Adj (σ p) (σ q) ↔ K.Adj p q) (e₂ : W ↪ V) :
    K.map (σ.symm.toEmbedding.trans e₂) = K.map e₂ := by
  ext a b
  simp only [map_adj, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨u, v, h, rfl, rfl⟩
    exact ⟨σ.symm u, σ.symm v, by rwa [← hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply],
      rfl, rfl⟩
  · rintro ⟨u, v, h, rfl, rfl⟩
    exact ⟨σ u, σ v, (hσ u v).2 h, by simp, by simp⟩

/-! ### Deleting far edges -/

/-- Deleting edges of `G` that lie outside the `r`-ball of `u` (measured in the smaller graph `G'`)
does not change the labelled `r`-ball of `u`. Hypotheses: every deleted edge has both endpoints at
`G'`-distance `≥ r` from `u`, and at least one at `G'`-distance `> r`. -/
lemma ballAgree_of_le {G G' : SimpleGraph V} {u : V} {r : ℕ} (hle : G' ≤ G)
    (hfar₁ : ∀ a b, G.Adj a b → ¬ G'.Adj a b → (r : ℕ∞) ≤ G'.edist u a)
    (hfar₂ : ∀ a b, G.Adj a b → ¬ G'.Adj a b →
      (r : ℕ∞) < G'.edist u a ∨ (r : ℕ∞) < G'.edist u b) :
    BallAgree G G' u r := by
  have hA : GAgree G' G u r := by
    intro x hx y
    refine ⟨fun h => hle h, fun h => ?_⟩
    by_contra h'
    exact absurd (hfar₁ x y h h') (not_le.2 hx)
  refine ⟨hA.symm, fun x y hx hy => ⟨fun h => ?_, fun h => hle h⟩⟩
  by_contra h'
  have hx' : G'.edist u x ≤ r := (hA.symm.edist_le_iff le_rfl).2 hx
  have hy' : G'.edist u y ≤ r := (hA.symm.edist_le_iff le_rfl).2 hy
  rcases hfar₂ x y h h' with h1 | h1
  · exact absurd hx' (not_le.2 h1)
  · exact absurd hy' (not_le.2 h1)

/-! ### Extending identifier assignments -/

/-- An injective identifier assignment on a part `ι(W')` of `W` extends to a bijection `W ≃ V` when
`W` and `V` have the same size. -/
lemma exists_equiv_extend [Finite W] (ι : W' ↪ W) (e₂ : W' ↪ V) (hWV : Nonempty (W ≃ V)) :
    ∃ e : W ≃ V, ∀ w, e (ι w) = e₂ w := by
  classical
  let f : Set.range ι ↪ V :=
    ⟨fun x => e₂ (Classical.choose x.2), by
      rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ h
      have ha := Classical.choose_spec (⟨a, rfl⟩ : ∃ w, ι w = ι a)
      have hb := Classical.choose_spec (⟨b, rfl⟩ : ∃ w, ι w = ι b)
      have := e₂.injective h
      simp only at this
      apply Subtype.ext
      simp only
      rw [← ha, ← hb, this]⟩
  obtain ⟨g, hg⟩ := Cardinal.extend_function_finite f hWV
  refine ⟨g, fun w => ?_⟩
  have := hg ⟨ι w, w, rfl⟩
  simp only [f] at this
  rw [this]
  show e₂ _ = e₂ w
  congr 1
  exact ι.injective (Classical.choose_spec (⟨w, rfl⟩ : ∃ w', ι w' = ι w))

/-! ### The indistinguishability argument -/

/-- **The lower-bound principle (sharp form of Observation 2.4), family version.** Let `𝒢` be a
family of networks on the identifier set `V` that the algorithm `A` colours properly, and let `K` be a
graph whose nodes get identifiers `e₂`. Suppose that every edge `xy` of `K` is, as seen from `x` and
from `y` within radius `r`, an edge of some network `G ∈ 𝒢`. Then `A` gives a colouring of `K`
with the same set of colours: node `v` of `K` takes the output of `A` at `e₂ v` in the network
`K` (identifiers `e₂`). -/
theorem coloring_of_views_family {r : ℕ} {A : SimpleGraph V → V → β} (hA : BallLocal r A)
    {𝒢 : Set (SimpleGraph V)} (hcol : ∀ G ∈ 𝒢, ∀ u v, G.Adj u v → A G u ≠ A G v)
    {K : SimpleGraph W'} (e₂ : W' ↪ V)
    (hview : ∀ x y, K.Adj x y → ∃ G ∈ 𝒢, G.Adj (e₂ x) (e₂ y) ∧
      BallAgree G (K.map e₂) (e₂ x) r ∧ BallAgree G (K.map e₂) (e₂ y) r) :
    Nonempty (K.Coloring β) := by
  refine ⟨Coloring.mk (fun v => A (K.map e₂) (e₂ v)) fun {x y} hxy => ?_⟩
  obtain ⟨G, hG, hadj, hbx, hby⟩ := hview x y hxy
  have h := hcol G hG _ _ hadj
  rwa [hA _ _ _ hbx, hA _ _ _ hby] at h

/-- **The lower-bound principle (sharp form of Observation 2.4).** Let `K` be a graph whose nodes
get identifiers `e₂`. Suppose that every edge `xy` of `K` is, as seen from `x` and from `y` within
radius `r`, an edge `x'y'` of `Γ` under some identifier assignment `e`. Then every `r`-local
algorithm colouring `Γ` gives a colouring of `K` with the same set of colours. -/
theorem coloring_of_views {r : ℕ} {A : SimpleGraph V → V → β} (hA : BallLocal r A)
    {Γ : SimpleGraph W} (hcol : ColoursGraph A Γ) {K : SimpleGraph W'} (e₂ : W' ↪ V)
    (hview : ∀ x y, K.Adj x y → ∃ (e : W ≃ V) (x' y' : W), Γ.Adj x' y' ∧ e x' = e₂ x ∧
      e y' = e₂ y ∧ BallAgree (Γ.map e.toEmbedding) (K.map e₂) (e₂ x) r ∧
      BallAgree (Γ.map e.toEmbedding) (K.map e₂) (e₂ y) r) :
    Nonempty (K.Coloring β) := by
  refine coloring_of_views_family hA (𝒢 := Set.range fun e : W ≃ V => Γ.map e.toEmbedding)
    ?_ e₂ fun x y hxy => ?_
  · rintro _ ⟨e, rfl⟩ u v huv
    rw [map_adj] at huv
    obtain ⟨x, y, hxy, rfl, rfl⟩ := huv
    exact hcol e x y hxy
  · obtain ⟨e, x', y', hadj, hx, hy, hbx, hby⟩ := hview x y hxy
    refine ⟨_, ⟨e, rfl⟩, ?_, hbx, hby⟩
    rw [← hx, ← hy]
    exact (map_adj_apply (f := e.toEmbedding)).2 hadj

/-- Corollary of `coloring_of_views`: if `K` has no colouring with the colours `β`, no `r`-local
algorithm with outputs in `β` colours `Γ`. -/
theorem not_colours_of_views {r : ℕ} {A : SimpleGraph V → V → β} (hA : BallLocal r A)
    {Γ : SimpleGraph W} {K : SimpleGraph W'} (hK : IsEmpty (K.Coloring β)) (e₂ : W' ↪ V)
    (hview : ∀ x y, K.Adj x y → ∃ (e : W ≃ V) (x' y' : W), Γ.Adj x' y' ∧ e x' = e₂ x ∧
      e y' = e₂ y ∧ BallAgree (Γ.map e.toEmbedding) (K.map e₂) (e₂ x) r ∧
      BallAgree (Γ.map e.toEmbedding) (K.map e₂) (e₂ y) r) :
    ¬ ColoursGraph A Γ := fun hcol =>
  hK.false (coloring_of_views hA hcol e₂ hview).some

/-! ### Observation 2.4 as stated in the paper -/

section Observation

variable {G : SimpleGraph W} {H : SimpleGraph W'}

/-- A rooted isomorphism between the subgraphs induced by the closed balls of radius `ρ` preserves
distances to the centre (one direction). -/
lemma edist_le_of_ballIso {x : W} {x' : W'} {ρ : ℕ}
    (φ : {v // G.edist x v ≤ ρ} ≃ {v // H.edist x' v ≤ ρ}) (hφx : (φ ⟨x, by simp⟩).1 = x')
    (hadj : ∀ a b, G.Adj a.1 b.1 → H.Adj (φ a).1 (φ b).1) :
    ∀ (d : ℕ) (a : {v // G.edist x v ≤ ρ}), G.edist x a.1 = d → H.edist x' (φ a).1 ≤ d := by
  intro d
  induction d with
  | zero =>
    intro a ha
    simp only [Nat.cast_zero, edist_eq_zero_iff] at ha
    have : a = ⟨x, by simp⟩ := Subtype.ext ha.symm
    subst this
    simp [hφx]
  | succ d ih =>
    intro a ha
    obtain ⟨b, hb, hba⟩ := exists_adj_of_edist_eq_succ ha
    have hbρ : G.edist x b ≤ ρ := by
      rw [hb]
      have := a.2
      rw [ha] at this
      exact le_trans (by exact_mod_cast Nat.le_succ d) this
    have h1 := ih ⟨b, hbρ⟩ hb
    have h2 := hadj ⟨b, hbρ⟩ a hba
    calc H.edist x' (φ a).1 ≤ H.edist x' (φ ⟨b, hbρ⟩).1 + 1 := edist_le_add_one_of_adj h2
      _ ≤ d + 1 := by gcongr
      _ = ((d + 1 : ℕ) : ℕ∞) := by push_cast; rfl

/-- A rooted isomorphism between the subgraphs induced by the closed balls of radius `ρ` preserves
distances to the centre. -/
lemma edist_eq_of_ballIso {x : W} {x' : W'} {ρ : ℕ}
    (φ : {v // G.edist x v ≤ ρ} ≃ {v // H.edist x' v ≤ ρ}) (hφx : (φ ⟨x, by simp⟩).1 = x')
    (hadj : ∀ a b, G.Adj a.1 b.1 ↔ H.Adj (φ a).1 (φ b).1) (a : {v // G.edist x v ≤ ρ}) :
    H.edist x' (φ a).1 = G.edist x a.1 := by
  have hφx' : (φ.symm ⟨x', by simp⟩).1 = x := by
    have : φ ⟨x, by simp⟩ = ⟨x', by simp⟩ := Subtype.ext hφx
    rw [← this, Equiv.symm_apply_apply]
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 (edist_ne_top_of_le_natCast a.2)
  obtain ⟨d', hd'⟩ := ENat.ne_top_iff_exists.1 (edist_ne_top_of_le_natCast (φ a).2)
  have h1 := edist_le_of_ballIso φ hφx (fun a b h => (hadj a b).1 h) d a hd.symm
  have h2 := edist_le_of_ballIso φ.symm hφx' (fun a b h => by
    rw [hadj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact h) d' (φ a) hd'.symm
  rw [Equiv.symm_apply_apply] at h2
  have h2' : (d : ℕ∞) ≤ d' := hd ▸ h2
  rw [← hd]
  exact le_antisymm h1 (hd' ▸ h2')

/-- A rooted isomorphism of radius-`ρ` balls, with matching identifiers, gives agreement of the
labelled balls of radius `ρ`. -/
lemma ballAgree_of_ballIso (f : W ↪ V) (g : W' ↪ V) {x : W} {x' : W'} {ρ : ℕ}
    (φ : {v // G.edist x v ≤ ρ} ≃ {v // H.edist x' v ≤ ρ}) (hφx : (φ ⟨x, by simp⟩).1 = x')
    (hadj : ∀ a b, G.Adj a.1 b.1 ↔ H.Adj (φ a).1 (φ b).1) (hfg : ∀ a, g (φ a).1 = f a.1) :
    BallAgree (G.map f) (H.map g) (f x) ρ := by
  have hdist := edist_eq_of_ballIso φ hφx hadj
  -- nodes of the `G`-ball and of the `H`-ball
  have hG : ∀ v, (G.map f).edist (f x) v ≤ ρ → ∃ a : {v // G.edist x v ≤ ρ}, f a.1 = v := by
    intro v hv
    by_cases h : v ∈ Set.range f
    · obtain ⟨a, rfl⟩ := h
      rw [edist_map_embedding] at hv
      exact ⟨⟨a, hv⟩, rfl⟩
    · rw [edist_map_of_notMem_range G f h] at hv; simp at hv
  have hH : ∀ b', H.edist x' b' ≤ ρ → ∃ a : {v // G.edist x v ≤ ρ}, (φ a).1 = b' :=
    fun b' hb' => ⟨φ.symm ⟨b', hb'⟩, by simp⟩
  -- adjacency of two ball nodes
  have hadjV : ∀ a b : {v // G.edist x v ≤ ρ},
      ((G.map f).Adj (f a.1) (f b.1) ↔ (H.map g).Adj (f a.1) (f b.1)) := by
    intro a b
    rw [map_adj_apply, ← hfg a, ← hfg b, map_adj_apply]
    exact hadj a b
  -- a `G`-neighbour of a node at distance `< ρ` is in the ball; same in `H`
  have hGn : ∀ (a : {v // G.edist x v ≤ ρ}), G.edist x a.1 < ρ → ∀ b, G.Adj a.1 b →
      G.edist x b ≤ ρ := by
    intro a ha b hab
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt ha)
    rw [← hd] at ha
    have hdρ : d < ρ := by exact_mod_cast ha
    calc G.edist x b ≤ G.edist x a.1 + 1 := edist_le_add_one_of_adj hab
      _ ≤ ρ := by rw [← hd]; exact_mod_cast hdρ
  have hHn : ∀ (a : {v // G.edist x v ≤ ρ}), G.edist x a.1 < ρ → ∀ b', H.Adj (φ a).1 b' →
      H.edist x' b' ≤ ρ := by
    intro a ha b' hab
    rw [← hdist a] at ha
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt ha)
    rw [← hd] at ha
    have hdρ : d < ρ := by exact_mod_cast ha
    calc H.edist x' b' ≤ H.edist x' (φ a).1 + 1 := edist_le_add_one_of_adj hab
      _ ≤ ρ := by rw [← hd]; exact_mod_cast hdρ
  refine ⟨?_, ?_⟩
  · intro v hv y
    obtain ⟨a, rfl⟩ := hG v hv.le
    rw [edist_map_embedding] at hv
    constructor
    · intro h
      rw [map_adj] at h
      obtain ⟨a', b, hab, ha', rfl⟩ := h
      rw [f.injective ha'] at hab
      exact (hadjV a ⟨b, hGn a hv b hab⟩).1 ((map_adj_apply).2 hab)
    · intro h
      rw [← hfg a, map_adj] at h
      obtain ⟨a', b', hab, ha', rfl⟩ := h
      rw [g.injective ha'] at hab
      obtain ⟨b, rfl⟩ := hH b' (hHn a hv b' hab)
      rw [hfg b]
      exact (hadjV a b).2 (by rw [← hfg a, ← hfg b]; exact (map_adj_apply).2 hab)
  · intro v w hv hw
    obtain ⟨a, rfl⟩ := hG v hv
    obtain ⟨b, rfl⟩ := hG w hw
    exact hadjV a b

/-- **Observation 2.4** of the paper (Linial). Let `G` be a graph, and `H` a graph with at most
`|V(G)|` vertices, such that each ball of radius `r + 1` in `H` is isomorphic (as a rooted induced
subgraph) to some ball of radius `r + 1` in `G`. Then every `r`-round algorithm colouring `G` with
colours `β` yields a colouring of `H` with colours `β`: no distributed algorithm can colour `G` with
less than `χ(H)` colours in at most `r` rounds. -/
theorem observation_2_4 [Finite W] {r : ℕ} {A : SimpleGraph V → V → β} (hA : BallLocal r A)
    (hcol : ColoursGraph A G) (hWV : Nonempty (W ≃ V)) (e₂ : W' ↪ V)
    (hball : ∀ x : W', ∃ (x' : W) (φ : {v // H.edist x v ≤ ((r + 1 : ℕ) : ℕ∞)} ≃
      {v // G.edist x' v ≤ ((r + 1 : ℕ) : ℕ∞)}),
      (φ ⟨x, by simp⟩).1 = x' ∧ ∀ a b, H.Adj a.1 b.1 ↔ G.Adj (φ a).1 (φ b).1) :
    Nonempty (H.Coloring β) := by
  refine coloring_of_views hA hcol e₂ fun x y hxy => ?_
  obtain ⟨x', φ, hφx, hadj⟩ := hball x
  -- identifiers on `G`: those of `H` on the ball, arbitrary elsewhere
  let ι : {v // G.edist x' v ≤ ((r + 1 : ℕ) : ℕ∞)} ↪ W := Function.Embedding.subtype _
  let g : {v // G.edist x' v ≤ ((r + 1 : ℕ) : ℕ∞)} ↪ V :=
    (φ.symm.toEmbedding.trans (Function.Embedding.subtype _)).trans e₂
  obtain ⟨e, he⟩ := exists_equiv_extend ι g hWV
  have hy : H.edist x y ≤ ((r + 1 : ℕ) : ℕ∞) := by
    rw [edist_eq_one_iff_adj.2 hxy]; exact_mod_cast Nat.le_add_left 1 r
  have hb : BallAgree (H.map e₂) (G.map e.toEmbedding) (e₂ x) (r + 1) := by
    refine ballAgree_of_ballIso e₂ e.toEmbedding φ hφx hadj fun a => ?_
    have := he (φ a)
    simpa [ι, g] using this
  have hex : e x' = e₂ x := by
    have := he (φ ⟨x, by simp⟩)
    simp only [ι, g, Function.Embedding.coe_subtype, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Equiv.symm_apply_apply] at this
    rw [← hφx]; exact this
  have hey : e (φ ⟨y, hy⟩).1 = e₂ y := by
    have := he (φ ⟨y, hy⟩)
    simp only [ι, g, Function.Embedding.coe_subtype, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Equiv.symm_apply_apply] at this
    exact this
  have hGadj : G.Adj x' (φ ⟨y, hy⟩).1 := by
    have := (hadj ⟨x, by simp⟩ ⟨y, hy⟩).1 hxy
    rwa [hφx] at this
  refine ⟨e, x', (φ ⟨y, hy⟩).1, hGadj, hex, hey, ?_, ?_⟩
  · exact (hb.mono_radius (Nat.le_succ r)).symm
  · exact (hb.of_adj ((map_adj_apply).2 hxy)).symm

end Observation

/-- `G` is a copy of `Γ` with identifiers, plus isolated nodes (the identifiers not used). -/
def IsCopyOf (Γ : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ f : W ↪ V, G = Γ.map f

end Podc.SparseColoringLB
