import Mathlib

/-!
# The sign model of `N_I` and `N_O` for three alternatives

For three alternatives `A, B, C` we name the three pairs by `j : Fin 3`
(`0 = AB`, `1 = BC`, `2 = CA`, the representatives of Remark 2.1 of the paper). A vertex
`U^σ_{αβ}` of the input complex `N_I` is then a pair `(j, σ)` with `σ : ι → Bool` the vector of
signs (`true = +`: voter `i` ranks the first alternative of the pair above the second). A vertex
of `N_O` is `(j, s)` with `s : Bool`.

A triangle of `N_I` (a profile) is a sign vector for each pair, `t : Fin 3 → ι → Bool`, which is
`Consistent`: no voter has a Condorcet cycle (`t 0 i = t 1 i = t 2 i` would mean
`A ≻ B ≻ C ≻ A` or the converse). `Papers/PODC2022/ArrowTopology/ThreeAlt.lean` proves that
consistent sign triples are exactly the signatures of profiles.

A chromatic map `f : N_I → N_O` is encoded by its *sign function* `s : Fin 3 × (ι → Bool) → Bool`
(`f (U^σ_j) = U^{s (j, σ)}_j`). Then:
* `SignUnanimous s`: `f` is unanimous;
* `SignSimplicial s`: `f` is simplicial, i.e. no triangle of `N_I` is sent to one of the two hollow
  triangles `{U^+_{AB}, U^+_{BC}, U^+_{CA}}`, `{U^-_{AB}, U^-_{BC}, U^-_{CA}}` of `N_O`;
* `SignProjection s k`: `f` is the projection to voter `k`.

Domain-restricted versions (`…On E`) only look at the triangles in a set `E`.
-/

namespace Podc.ArrowTopology

variable {ι : Type*}

/-- Vertices of `N_I` for three alternatives: a pair index (`0 = AB`, `1 = BC`, `2 = CA`) and a
sign vector. -/
abbrev Vtx (ι : Type*) := Fin 3 × (ι → Bool)

/-- A triangle of `N_I`: sign vectors for `AB`, `BC`, `CA`, with no voter having a cyclic
preference. -/
def Consistent (t : Fin 3 → ι → Bool) : Prop := ∀ i, ¬ (t 0 i = t 1 i ∧ t 1 i = t 2 i)

instance [Fintype ι] [DecidableEq ι] (t : Fin 3 → ι → Bool) : Decidable (Consistent t) :=
  inferInstanceAs (Decidable (∀ i, ¬ (t 0 i = t 1 i ∧ t 1 i = t 2 i)))

/-- The vertices of the triangle `t`. -/
def triVtx (t : Fin 3 → ι → Bool) (j : Fin 3) : Vtx ι := (j, t j)

/-- The three output signs `(a, b, c)` of `AB, BC, CA` form a triangle of `N_O` (are not all
equal, which would be a Condorcet cycle). -/
def OutTri (a b c : Bool) : Prop := ¬ (a = b ∧ b = c)

instance (a b c : Bool) : Decidable (OutTri a b c) := inferInstanceAs (Decidable ¬ _)

/-- The sign function of a unanimous map: `U^{(+,…,+)}_j ↦ U^+_j` and `U^{(−,…,−)}_j ↦ U^-_j`. -/
def SignUnanimous (s : Vtx ι → Bool) : Prop := ∀ j b, s (j, fun _ => b) = b

/-- The sign function of a simplicial map: every triangle of `N_I` goes to a triangle of `N_O`. -/
def SignSimplicial (s : Vtx ι → Bool) : Prop :=
  ∀ t, Consistent t → OutTri (s (0, t 0)) (s (1, t 1)) (s (2, t 2))

/-- The sign function of the projection to voter `k`. -/
def SignProjection (s : Vtx ι → Bool) (k : ι) : Prop := ∀ v, s v = v.2 k

/-! ### Restricted domains: a set `E` of triangles. -/

/-- Unanimity on the vertices of the triangles in `E`. -/
def SignUnanimousOn (E : Set (Fin 3 → ι → Bool)) (s : Vtx ι → Bool) : Prop :=
  ∀ t ∈ E, ∀ j b, t j = (fun _ => b) → s (j, t j) = b

/-- Simpliciality on the triangles in `E`. -/
def SignSimplicialOn (E : Set (Fin 3 → ι → Bool)) (s : Vtx ι → Bool) : Prop :=
  ∀ t ∈ E, OutTri (s (0, t 0)) (s (1, t 1)) (s (2, t 2))

/-- `s` is the projection to voter `k` on the vertices of the triangles in `E`. -/
def SignProjectionOn (E : Set (Fin 3 → ι → Bool)) (s : Vtx ι → Bool) (k : ι) : Prop :=
  ∀ t ∈ E, ∀ j, s (j, t j) = t j k

end Podc.ArrowTopology
