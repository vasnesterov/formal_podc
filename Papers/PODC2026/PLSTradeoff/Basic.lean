import Papers.PODC2026.SinklessOrientation.Basic

/-!
# Proof labeling schemes: the model

Basic notions for *Near-Resolution of the Tradeoff Conjecture in Distributed Proof Labeling
Schemes* (A. Filtser, O. Fischer, PODC 2026).

* The node set is a fixed finite type `V`; its elements are the node identifiers. A configuration
  is a graph `G : SimpleGraph V` together with inputs `I : V → ι`; a configuration family is a set
  of graphs `𝒢` together with all input assignments (the paper's `(𝒢, ℐ)`).
* Labels are bit strings (`Label = List Bool`); the cost of a label is its length.
* `ViewEq R G I ℓ G' I' ℓ' v`: the two labelled configurations look the same from `v` within
  radius `R` — the edges incident to nodes at distance `< R` agree (`GAgree`, imported from
  `Papers/PODC2026/SinklessOrientation/Basic.lean`), and inputs and labels agree on all nodes at
  distance `≤ R`. This is exactly what `v` learns in `R` rounds of the LOCAL model; for `R = 1` it
  is the classical PLS view (own and neighbours' identifiers, inputs and labels).
* `IsLocal R f`: `f G I ℓ v` only depends on the `R`-view of `v`.
* `PLS 𝒢 P R`: an `R`-PLS (Definition 1), with prover, verifier, locality, completeness and
  soundness; `PLS.CostLE` bounds the cost on yes-instances.
* `loc G v R` and `mask G v R f`: the part of a configuration that `v` sees within radius `R`.
  Defining a verifier as a function of `loc`/`mask` makes it local by construction
  (`viewEq_loc_eq`, `viewEq_mask_eq`); `ver_loc_mask` transfers a local function between the full
  configuration and the localized one.
-/

namespace PLSTradeoff

open SimpleGraph SinklessOrientation

/-- Labels (certificates) are bit strings. -/
abbrev Label := List Bool

variable {V : Type*} {ι : Type*}

-- CSLib candidate
/-- `v` sees the same labelled configuration within radius `R` in `(G, I, ℓ)` and `(G', I', ℓ')`:
the edges incident to nodes at distance `< R` agree, and inputs and labels agree on all nodes at
distance `≤ R` (the information gathered in `R` rounds of the LOCAL model). -/
def ViewEq {α : Type*} (R : ℕ) (G : SimpleGraph V) (I : V → ι) (ℓ : V → α)
    (G' : SimpleGraph V) (I' : V → ι) (ℓ' : V → α) (v : V) : Prop :=
  GAgree G G' v R ∧ ∀ u, G.edist v u ≤ R → I u = I' u ∧ ℓ u = ℓ' u

/-- `f G I ℓ v` depends only on the radius-`R` view of `v`. -/
def IsLocal {α β : Type*} (R : ℕ) (f : SimpleGraph V → (V → ι) → (V → α) → V → β) : Prop :=
  ∀ G I ℓ G' I' ℓ' v, ViewEq R G I ℓ G' I' ℓ' v → f G I ℓ v = f G' I' ℓ' v

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

lemma ViewEq.mono {α : Type*} {R R' : ℕ} {I I' : V → ι} {ℓ ℓ' : V → α} {v : V}
    (h : ViewEq R G I ℓ G' I' ℓ' v) (hR : R' ≤ R) : ViewEq R' G I ℓ G' I' ℓ' v :=
  ⟨h.1.mono_radius hR, fun u hu => h.2 u (hu.trans (by exact_mod_cast hR))⟩

lemma IsLocal.mono {α β : Type*} {R R' : ℕ} {f : SimpleGraph V → (V → ι) → (V → α) → V → β}
    (h : IsLocal R f) (hR : R ≤ R') : IsLocal R' f :=
  fun _ _ _ _ _ _ _ hv => h _ _ _ _ _ _ _ (hv.mono hR)

-- CSLib candidate
/-- The part of `G` seen from `v` within radius `R`: the edges incident to nodes at distance
`< R` from `v`. -/
def loc (G : SimpleGraph V) (v : V) (R : ℕ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (G.edist v x < R ∨ G.edist v y < R)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

lemma loc_le (G : SimpleGraph V) (v : V) (R : ℕ) : loc G v R ≤ G := fun _ _ h => h.1

lemma gagree_loc (G : SimpleGraph V) (v : V) (R : ℕ) : GAgree G (loc G v R) v R :=
  fun _ hx _ => ⟨fun h => ⟨h, Or.inl hx⟩, fun h => h.1⟩

lemma edist_le_edist_loc {G : SimpleGraph V} {v : V} {R : ℕ} {x y : V} :
    G.edist x y ≤ (loc G v R).edist x y :=
  edist_anti (loc_le G v R)

/-- Restrict a function to the radius-`R` ball around `v` (outside, it takes the value at `v`). -/
noncomputable def mask {α : Type*} (G : SimpleGraph V) (v : V) (R : ℕ) (f : V → α) : V → α :=
  open scoped Classical in fun u => if G.edist v u ≤ R then f u else f v

lemma mask_of_le {α : Type*} {v : V} {R : ℕ} {f : V → α} {u : V} (h : G.edist v u ≤ R) :
    mask G v R f u = f u := by
  classical
  simp [mask, h]

lemma loc_eq_of_gagree {v : V} {R : ℕ} (h : GAgree G G' v R) : loc G v R = loc G' v R := by
  ext x y
  simp only [loc]
  constructor
  · rintro ⟨hxy, hx | hy⟩
    · exact ⟨(h hx y).1 hxy, Or.inl ((h.edist_lt_iff le_rfl).2 hx)⟩
    · exact ⟨((h hy x).1 hxy.symm).symm, Or.inr ((h.edist_lt_iff le_rfl).2 hy)⟩
  · rintro ⟨hxy, hx | hy⟩
    · have hx' := (h.edist_lt_iff le_rfl).1 hx
      exact ⟨(h hx' y).2 hxy, Or.inl hx'⟩
    · have hy' := (h.edist_lt_iff le_rfl).1 hy
      exact ⟨((h hy' x).2 hxy.symm).symm, Or.inr hy'⟩

lemma viewEq_loc_eq {α : Type*} {R : ℕ} {I I' : V → ι} {ℓ ℓ' : V → α} {v : V}
    (h : ViewEq R G I ℓ G' I' ℓ' v) : loc G v R = loc G' v R :=
  loc_eq_of_gagree h.1

lemma viewEq_mask_eq {α : Type*} {R : ℕ} {I I' : V → ι} {ℓ ℓ' : V → α} {v : V}
    (h : ViewEq R G I ℓ G' I' ℓ' v) :
    mask G v R I = mask G' v R I' ∧ mask G v R ℓ = mask G' v R ℓ' := by
  classical
  have hv : G.edist v v ≤ R := by simp
  constructor <;> funext u <;> simp only [mask] <;>
    by_cases hu : G.edist v u ≤ R
  · rw [ite_eq_left hu, ite_eq_left ((h.1.edist_le_iff le_rfl).2 hu)]; exact (h.2 u hu).1
  · rw [ite_eq_right hu, ite_eq_right (fun h' => hu ((h.1.edist_le_iff le_rfl).1 h'))]; exact (h.2 v hv).1
  · rw [ite_eq_left hu, ite_eq_left ((h.1.edist_le_iff le_rfl).2 hu)]; exact (h.2 u hu).2
  · rw [ite_eq_right hu, ite_eq_right (fun h' => hu ((h.1.edist_le_iff le_rfl).1 h'))]; exact (h.2 v hv).2

/-- Transfer for a local function: evaluating `f` (local with radius `ρ`) at a node `u` with
`d(v, u) + ρ ≤ R` gives the same result in the localized configuration as in the full one. -/
lemma viewEq_loc_mask {α : Type*} {R ρ a : ℕ} (I : V → ι) (ℓ ℓ' : V → α) {v u : V}
    (hu : G.edist v u ≤ a) (h : a + ρ ≤ R) (hℓ : ∀ w, G.edist v w ≤ R → ℓ' w = ℓ w) :
    ViewEq ρ (loc G v R) (mask G v R I) ℓ' G I ℓ u := by
  have hA : GAgree G (loc G v R) u ρ := (gagree_loc G v R).mono hu h
  refine ⟨hA.symm, fun w hw => ?_⟩
  have hw' : G.edist u w ≤ ρ := edist_le_edist_loc.trans hw
  have hvw : G.edist v w ≤ R := by
    calc G.edist v w ≤ G.edist v u + G.edist u w := SimpleGraph.edist_triangle
      _ ≤ a + ρ := add_le_add hu hw'
      _ ≤ R := by exact_mod_cast h
  exact ⟨mask_of_le hvw, hℓ w hvw⟩

lemma ver_loc_mask {α β : Type*} {R ρ a : ℕ} {f : SimpleGraph V → (V → ι) → (V → α) → V → β}
    (hf : IsLocal ρ f) (I : V → ι) (ℓ ℓ' : V → α) {v u : V}
    (hu : G.edist v u ≤ a) (h : a + ρ ≤ R) (hℓ : ∀ w, G.edist v w ≤ R → ℓ' w = ℓ w) :
    f (loc G v R) (mask G v R I) ℓ' u = f G I ℓ u :=
  hf _ _ _ _ _ _ _ (viewEq_loc_mask I ℓ ℓ' hu h hℓ)

/-- Distances up to `ρ` from a node `u` with `d(v,u) + ρ ≤ R` are the same in `loc G v R`. -/
lemma loc_edist_le_iff {R ρ a : ℕ} {v u w : V} (hu : G.edist v u ≤ a) (h : a + ρ ≤ R) {m : ℕ}
    (hm : m ≤ ρ) : (loc G v R).edist u w ≤ m ↔ G.edist u w ≤ m :=
  ((gagree_loc G v R).mono hu h).edist_le_iff hm

lemma loc_adj_iff {R a : ℕ} {v u w : V} (hu : G.edist v u ≤ a) (h : a + 1 ≤ R) :
    (loc G v R).Adj u w ↔ G.Adj u w :=
  (((gagree_loc G v R).mono hu h) (by simp) w).symm

/-- An `R`-PLS is also an `R'`-PLS for `R ≤ R'` (same prover and verifier). -/
def PLS.mono {𝒢 : Set (SimpleGraph V)} {P : SimpleGraph V → (V → ι) → Prop} {R R' : ℕ}
    (S : PLS 𝒢 P R) (h : R ≤ R') : PLS 𝒢 P R' :=
  { S with isLocal := S.isLocal.mono h }

@[simp] lemma PLS.mono_prov {𝒢 : Set (SimpleGraph V)} {P : SimpleGraph V → (V → ι) → Prop}
    {R R' : ℕ} (S : PLS 𝒢 P R) (h : R ≤ R') : (S.mono h).prov = S.prov := rfl

end Views

end PLSTradeoff
