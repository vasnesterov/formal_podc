import Mathlib
import Podc.Local.Locality

/-!
# Proof labeling schemes: the model

Basic notions for *Near-Resolution of the Tradeoff Conjecture in Distributed Proof Labeling
Schemes* (A. Filtser, O. Fischer, PODC 2026).

* The node set is a fixed finite type `V`; its elements are the node identifiers. A configuration
  is a graph `G : SimpleGraph V` together with inputs `I : V → ι`; a configuration family is a set
  of graphs `𝒢` together with all input assignments (the paper's `(𝒢, ℐ)`).
* Labels are bit strings (`Label = List Bool`); the cost of a label is its length.
* `ViewEq R G I ℓ G' I' ℓ' v`: the two labelled configurations look the same from `v` within
  radius `R` — the edges incident to nodes at distance `< R` agree (`GAgree`), and inputs and
  labels agree on all nodes at distance `≤ R` (`viewEq_iff`). This is exactly what `v` learns in
  `R` rounds of the LOCAL model; for `R = 1` it is the classical PLS view (own and neighbours'
  identifiers, inputs and labels). It is the shared `Cslib.Local.ViewEq`
  (`Podc/Local/Locality.lean`) for the labelling `u ↦ (I u, ℓ u)`.
* `IsLocal R f`: `f G I ℓ v` only depends on the `R`-view of `v` (`isLocal_iff`); again the shared
  `Cslib.Local.IsLocal` for the paired labelling.
* `PLS 𝒢 P R`: an `R`-PLS (Definition 1), with prover, verifier, locality, completeness and
  soundness; `PLS.CostLE` bounds the cost on yes-instances.
* `loc G v R` and `mask G v R f` (shared, `Cslib.Local`): the part of a configuration that `v`
  sees within radius `R`. Defining a verifier as a function of `loc`/`mask` makes it local by
  construction (`viewEq_loc_eq`, `viewEq_mask_eq`); `ver_loc_mask` transfers a local function
  between the full configuration and the localized one.
-/

namespace PLSTradeoff

open SimpleGraph
open Cslib.Local (GAgree loc mask mask_of_le mask_comp viewEq_loc)

/-- Labels (certificates) are bit strings. -/
abbrev Label := List Bool

variable {V : Type*} {ι : Type*}

/-- `v` sees the same labelled configuration within radius `R` in `(G, I, ℓ)` and `(G', I', ℓ')`:
the edges incident to nodes at distance `< R` agree, and inputs and labels agree on all nodes at
distance `≤ R` (the information gathered in `R` rounds of the LOCAL model; `viewEq_iff`). -/
abbrev ViewEq {α : Type*} (R : ℕ) (G : SimpleGraph V) (I : V → ι) (ℓ : V → α)
    (G' : SimpleGraph V) (I' : V → ι) (ℓ' : V → α) (v : V) : Prop :=
  Cslib.Local.ViewEq R G (fun u => (I u, ℓ u)) G' (fun u => (I' u, ℓ' u)) v

/-- `f G I ℓ v` depends only on the radius-`R` view of `v` (`isLocal_iff`). -/
abbrev IsLocal {α β : Type*} (R : ℕ) (f : SimpleGraph V → (V → ι) → (V → α) → V → β) : Prop :=
  Cslib.Local.IsLocal R (fun G (x : V → ι × α) v => f G (fun u => (x u).1) (fun u => (x u).2) v)

lemma viewEq_iff {α : Type*} {R : ℕ} {G G' : SimpleGraph V} {I I' : V → ι} {ℓ ℓ' : V → α}
    {v : V} : ViewEq R G I ℓ G' I' ℓ' v ↔
      GAgree G G' v R ∧ ∀ u, G.edist v u ≤ R → I u = I' u ∧ ℓ u = ℓ' u := by
  simp only [ViewEq, Cslib.Local.ViewEq, Prod.mk.injEq]

/-- The locality condition of Definition 1, unfolded. -/
lemma isLocal_iff {α β : Type*} {R : ℕ} {f : SimpleGraph V → (V → ι) → (V → α) → V → β} :
    IsLocal R f ↔ ∀ G I ℓ G' I' ℓ' v, ViewEq R G I ℓ G' I' ℓ' v → f G I ℓ v = f G' I' ℓ' v :=
  ⟨fun h _ _ _ _ _ _ _ hv => h _ _ _ _ _ hv, fun h _ _ _ _ _ hv => h _ _ _ _ _ _ _ hv⟩

lemma IsLocal.eq {α β : Type*} {R : ℕ} {f : SimpleGraph V → (V → ι) → (V → α) → V → β}
    (h : IsLocal R f) (G : SimpleGraph V) (I : V → ι) (ℓ : V → α) (G' : SimpleGraph V)
    (I' : V → ι) (ℓ' : V → α) (v : V) (hv : ViewEq R G I ℓ G' I' ℓ' v) :
    f G I ℓ v = f G' I' ℓ' v :=
  isLocal_iff.1 h G I ℓ G' I' ℓ' v hv

/-- Definition 1: a `R`-hop proof labeling scheme (`R`-PLS) for the predicate `P` on the
configuration family `𝒢` (all graphs in `𝒢`, all inputs). `ver G I ℓ v = true` means that `v`
accepts. -/
structure PLS (𝒢 : Set (SimpleGraph V)) (P : SimpleGraph V → (V → ι) → Prop) (R : ℕ) where
  /-- The honest prover. -/
  prov : SimpleGraph V → (V → ι) → V → Label
  /-- The verifier. -/
  ver : SimpleGraph V → (V → ι) → (V → Label) → V → Bool
  isLocal : IsLocal R ver
  complete : ∀ G ∈ 𝒢, ∀ I, P G I → ∀ v, ver G I (prov G I) v = true
  sound : ∀ G ∈ 𝒢, ∀ I (ℓ : V → Label), (∀ v, ver G I ℓ v = true) → P G I

/-- The cost of a PLS (maximal label length of the honest prover on yes-instances) is at most
`p`. -/
def PLS.CostLE {𝒢 : Set (SimpleGraph V)} {P : SimpleGraph V → (V → ι) → Prop} {R : ℕ}
    (S : PLS 𝒢 P R) (p : ℕ) : Prop :=
  ∀ G ∈ 𝒢, ∀ I, P G I → ∀ v, (S.prov G I v).length ≤ p

/-! ### Basic facts about views -/

section Views

variable {G G' : SimpleGraph V}

lemma viewEq_loc_eq {α : Type*} {R : ℕ} {I I' : V → ι} {ℓ ℓ' : V → α} {v : V}
    (h : ViewEq R G I ℓ G' I' ℓ' v) : loc G v R = loc G' v R :=
  Cslib.Local.ViewEq.loc_eq h

lemma viewEq_mask_eq {α : Type*} {R : ℕ} {I I' : V → ι} {ℓ ℓ' : V → α} {v : V}
    (h : ViewEq R G I ℓ G' I' ℓ' v) :
    mask G v R I = mask G' v R I' ∧ mask G v R ℓ = mask G' v R ℓ' := by
  have h1 := congrArg (Prod.fst ∘ ·) (Cslib.Local.ViewEq.mask_eq h)
  have h2 := congrArg (Prod.snd ∘ ·) (Cslib.Local.ViewEq.mask_eq h)
  simp only [← mask_comp] at h1 h2
  exact ⟨h1, h2⟩

/-- Transfer for a local function: evaluating `f` (local with radius `ρ`) at a node `u` with
`d(v, u) + ρ ≤ R` gives the same result in the localized configuration as in the full one. -/
lemma ver_loc_mask {α β : Type*} {R ρ a : ℕ} {f : SimpleGraph V → (V → ι) → (V → α) → V → β}
    (hf : IsLocal ρ f) (I : V → ι) (ℓ ℓ' : V → α) {v u : V}
    (hu : G.edist v u ≤ a) (h : a + ρ ≤ R) (hℓ : ∀ w, G.edist v w ≤ R → ℓ' w = ℓ w) :
    f (loc G v R) (mask G v R I) ℓ' u = f G I ℓ u :=
  hf.eq _ _ _ _ _ _ _ (viewEq_loc (x := fun w => (I w, ℓ w)) hu h fun w hw => by
    rw [mask_of_le hw, hℓ w hw])

/-- An `R`-PLS is also an `R'`-PLS for `R ≤ R'` (same prover and verifier). -/
def PLS.mono {𝒢 : Set (SimpleGraph V)} {P : SimpleGraph V → (V → ι) → Prop} {R R' : ℕ}
    (S : PLS 𝒢 P R) (h : R ≤ R') : PLS 𝒢 P R' :=
  { S with isLocal := S.isLocal.mono h }

@[simp] lemma PLS.mono_prov {𝒢 : Set (SimpleGraph V)} {P : SimpleGraph V → (V → ι) → Prop}
    {R R' : ℕ} (S : PLS 𝒢 P R) (h : R ≤ R') : (S.mono h).prov = S.prov := rfl

end Views

end PLSTradeoff
