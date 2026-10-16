import Papers.PODC2019.AutomaticSpeedup.PNModel

/-!
# Theorems 1 and 2 and Corollary 1 in the port-numbering model (Brandt, PODC 2019, §4.1–4.2)

We instantiate the abstract `ViewSystem` with input-labelled port-numbered graphs and their
full-information views (`viewSystem`), and obtain:

* `theorem_1_forward`: (1) ⇒ (2) of Theorem 1, exactly under the paper's hypotheses
  (`t`-independence; maximum degree `≤ Δ`). The girth hypothesis is not needed: our views *are*
  "the information a node can obtain in `t` rounds", which is how the paper defines `N^t(v)`; girth
  only serves to make `t`-independence plausible and views tree-like.
* `theorem_1_backward`: (2) ⇒ (1) under the extra hypothesis `EdgeAsym` (the two endpoints of
  every edge can be told apart from the radius-`t` view of the edge). Without it, (2) ⇒ (1) is false:
  see `Counterexample.lean`.
* `theorem_1`: the equivalence under both hypotheses; `corollary_1`.
* `theorem_2`: the equivalence for the simplified problem `Π'_1` when the inputs contain an edge
  orientation (the paper's hypothesis); `theorem_2_of_edgeAsym` with `EdgeAsym` only.
-/

namespace AutomaticSpeedup

open Cslib.PortNumbering Problem

variable {I : Type} {n : ℕ} {L : Type}

/-- Clause 1 of `(s+1)`-independence (§3): for every edge `e = {u, v}` of a graph of the class, and
any two graphs of the class in which the edge view `N^{s+1}(e)` occurs (as seen from `v`,
resp. from `u`), the two node views `N^{s+1}(v)`, `N^{s+1}(u)` there (equivalently, the two
extensions `Ext_v(e)`, `Ext_u(e)`) occur together around a single edge of a graph of the class. -/
def IndepClause1 (𝒢 : Set (LGraph I n)) (s : ℕ) : Prop :=
  ∀ G ∈ 𝒢, ∀ v, ∀ i < G.deg v,
    ∀ H₁ ∈ 𝒢, ∀ w₁, ∀ k₁ < H₁.deg w₁, H₁.eview s w₁ k₁ = G.eview s v i →
    ∀ H₂ ∈ 𝒢, ∀ w₂, ∀ k₂ < H₂.deg w₂,
      H₂.eview s w₂ k₂ = G.eview s (G.nbr v i) (G.rport v i) →
    ∃ H ∈ 𝒢, ∃ w, ∃ k < H.deg w, H.eview s w k = G.eview s v i ∧
      H.view (s + 1) w = H₁.view (s + 1) w₁ ∧ H.view (s + 1) (H.nbr w k) = H₂.view (s + 1) w₂

/-- Clause 2 of `(s+1)`-independence (§3): for every node `v` of a graph of the class, and for each
port `i` of `v` a graph `Hs i` of the class with a node `ws i` having the same radius-`s` view as
`v`, there is a graph of the class with a node `w` having this radius-`s` view and, at every port
`i`, the radius-`(s+1)` edge view of port `i` of `ws i` (i.e. all the extensions occur together). -/
def IndepClause2 (𝒢 : Set (LGraph I n)) (s : ℕ) : Prop :=
  ∀ G ∈ 𝒢, ∀ v, ∀ (Hs : ℕ → LGraph I n) (ws : ℕ → Fin n),
    (∀ i < G.deg v, Hs i ∈ 𝒢 ∧ (Hs i).view s (ws i) = G.view s v) →
    ∃ H ∈ 𝒢, ∃ w, H.view s w = G.view s v ∧ ∀ i < G.deg v, H.eview s w i = (Hs i).eview s (ws i) i

/-- `t`-independence of a class of `n`-node graphs (§3; defined for positive `t`). -/
def IsIndependent (𝒢 : Set (LGraph I n)) : ℕ → Prop
  | 0 => True
  | s + 1 => IndepClause1 𝒢 s ∧ IndepClause2 𝒢 s

/-- Edge symmetry breaking at radius `t = s + 1`: for every edge, the endpoints have different
radius-`s` views or the edge has different port numbers at its endpoints. Equivalently, the two
endpoints see the radius-`t` neighbourhood of the edge differently. Not assumed in the paper's
Theorem 1, but necessary for (2) ⇒ (1) (`Counterexample.lean`). -/
def EdgeAsym (𝒢 : Set (LGraph I n)) : ℕ → Prop
  | 0 => True
  | s + 1 => ∀ G ∈ 𝒢, ∀ v, ∀ i < G.deg v,
      G.view s (G.nbr v i) ≠ G.view s v ∨ G.rport v i ≠ i

/-- The inputs contain an orientation of every edge (as in Theorem 2): `o` reads, from the input
label of `(v, e)`, whether `e` is oriented away from `v`; the two ends always disagree. -/
def HasOrientation (𝒢 : Set (LGraph I n)) (o : I → Bool) : Prop :=
  ∀ G ∈ 𝒢, ∀ v, ∀ i < G.deg v, o (G.inp (G.nbr v i) (G.rport v i)) ≠ o (G.inp v i)

theorem HasOrientation.edgeAsym {𝒢 : Set (LGraph I n)} {o : I → Bool} (h : HasOrientation 𝒢 o)
    {t : ℕ} (ht : 1 ≤ t) : EdgeAsym 𝒢 t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  intro G hG v i hi
  by_contra hc
  rw [not_or, not_not, not_not] at hc
  obtain ⟨h1, h2⟩ := hc
  have := congrArg (fun w : ViewT I s => w.inputs[i]?) h1
  simp only [LGraph.inputs_view, LGraph.inputs] at this
  have hj : i < G.deg (G.nbr v i) := by
    have := G.G.rport_lt hi; rwa [show G.G.rport v i = i from h2] at this
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_range hj, List.getElem?_range hi] at this
  simp only [Option.map_some, Option.some.injEq] at this
  apply h G hG v i hi
  rw [← this, show G.rport v i = i from h2]

/-! ### The view system of a class of graphs -/

/-- The view system of the class `𝒢` at radius `t = s + 1`. -/
def viewSystem (𝒢 : Set (LGraph I n)) (s : ℕ) : ViewSystem.{0} where
  Graph := 𝒢
  Node _ := Fin n
  deg G := G.1.deg
  nbr G := G.1.nbr
  rport G := G.1.rport
  rport_lt G _ _ h := G.1.G.rport_lt h
  nbr_nbr G _ _ h := G.1.G.nbr_nbr h
  rport_rport G _ _ h := G.1.G.rport_rport h
  NV := ViewT I (s + 1)
  EV := ViewT I s × ℕ × ViewT I s × ℕ
  PV := ViewT I s
  nv G := G.1.view (s + 1)
  ev G := G.1.eview s
  pv G := G.1.view s
  evOf w i := (w.restrict, i, (w.child i).1, (w.child i).2)
  ev_eq G v i h := by
    simp only [LGraph.eview, LGraph.restrict_view, LGraph.child_view _ _ _ h]
  degN w := w.deg
  deg_eq_degN G v := (LGraph.deg_view _ _ _).symm
  pvOf x := x.1
  pv_eq _ _ _ _ := rfl
  portOf x := x.2.1
  portOf_ev _ _ _ _ := rfl
  flip x := (x.2.2.1, x.2.2.2, x.1, x.2.1)
  ev_flip G v i h := by
    simp only [LGraph.eview, PNGraph.nbr_nbr _ h, PNGraph.rport_rport _ h]
  degP p := p.deg
  deg_eq_degP G v := (LGraph.deg_view _ _ _).symm

variable {𝒢 : Set (LGraph I n)} {s : ℕ}

theorem solvesN_iff {P : Problem L} {Δ : ℕ} {A : ViewT I (s + 1) → ℕ → L} :
    (viewSystem 𝒢 s).SolvesN P Δ A ↔ ∀ G ∈ 𝒢, Solves P Δ G fun v i => A (G.view (s + 1) v) i :=
  ⟨fun h G hG => h ⟨G, hG⟩, fun h G => h G.1 G.2⟩

theorem solvesP_iff {P : Problem L} {Δ : ℕ} {C : ViewT I s → ℕ → L} :
    (viewSystem 𝒢 s).SolvesP P Δ C ↔ ∀ G ∈ 𝒢, Solves P Δ G fun v i => C (G.view s v) i :=
  ⟨fun h G hG => h ⟨G, hG⟩, fun h G => h G.1 G.2⟩

theorem ind1_of (h : IndepClause1 𝒢 s) : (viewSystem 𝒢 s).Ind1 := by
  intro G v i hi H₁ w₁ k₁ hk₁ he₁ H₂ w₂ k₂ hk₂ he₂
  obtain ⟨H, hH, w, k, hk, he, hn₁, hn₂⟩ :=
    h G.1 G.2 v i hi H₁.1 H₁.2 w₁ k₁ hk₁ he₁ H₂.1 H₂.2 w₂ k₂ hk₂ he₂
  exact ⟨⟨H, hH⟩, w, k, hk, he, hn₁, hn₂⟩

theorem ind2_of (h : IndepClause2 𝒢 s) : (viewSystem 𝒢 s).Ind2 := by
  intro G v Hs ws hws
  obtain ⟨H, hH, w, hw, hev⟩ := h G.1 G.2 v (fun i => (Hs i).1) ws fun i hi => ⟨(Hs i).2, hws i hi⟩
  exact ⟨⟨H, hH⟩, w, hw, hev⟩

theorem edgeAsym_of (h : EdgeAsym 𝒢 (s + 1)) : (viewSystem 𝒢 s).EdgeAsym := by
  intro G v i hi he
  have he' : (G.1.view s (G.1.nbr v i), G.1.rport v i, G.1.view s (G.1.nbr (G.1.nbr v i)
      (G.1.rport v i)), G.1.rport (G.1.nbr v i) (G.1.rport v i)) = G.1.eview s v i := he
  simp only [LGraph.eview, Prod.mk.injEq] at he'
  rcases h G.1 G.2 v i hi with h1 | h1
  · exact h1 he'.1
  · exact h1 he'.2.1

/-! ### Theorem 1 -/

/-- **Theorem 1, (1) ⇒ (2).** On a `t`-independent class of `n`-node graphs of maximum degree
`≤ Δ`, a `t`-round algorithm for `Π` yields a `(t-1)`-round algorithm for `Π_1`. -/
theorem theorem_1_forward {Δ t : ℕ} (ht : 1 ≤ t) (hΔ : ∀ G ∈ 𝒢, ∀ v, G.deg v ≤ Δ)
    (hind : IsIndependent 𝒢 t) {P : Problem L} (h : SolvableIn 𝒢 P Δ t) :
    SolvableIn 𝒢 P.speedup Δ (t - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  obtain ⟨A, hA⟩ := (solvableIn_iff_view _ _ _ _).1 h
  rw [solvableIn_iff_view]
  exact ⟨_, solvesP_iff.1 (ViewSystem.speedup_forward (ind1_of hind.1) (ind2_of hind.2)
    (fun G v => hΔ G.1 G.2 v) (solvesN_iff.2 hA))⟩

/-- **Theorem 1, (2) ⇒ (1)**, under edge symmetry breaking (`EdgeAsym`), which the paper omits.
No independence is needed for this direction. -/
theorem theorem_1_backward [Nonempty L] {Δ t : ℕ} (ht : 1 ≤ t) (hasym : EdgeAsym 𝒢 t)
    {P : Problem L} (h : SolvableIn 𝒢 P.speedup Δ (t - 1)) : SolvableIn 𝒢 P Δ t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  obtain ⟨C, hC⟩ := (solvableIn_iff_view _ _ _ _).1 h
  rw [solvableIn_iff_view]
  exact ⟨_, solvesN_iff.1 (ViewSystem.speedup_backward (edgeAsym_of hasym) (solvesP_iff.2 hC))⟩

/-- **Theorem 1** (corrected): for a `t`-independent class of `n`-node graphs of maximum degree
`≤ Δ` in which the endpoints of every edge can be told apart at radius `t`, `Π` is solvable in
`t` rounds iff `Π_1` is solvable in `t - 1` rounds. -/
theorem theorem_1 [Nonempty L] {Δ t : ℕ} (ht : 1 ≤ t) (hΔ : ∀ G ∈ 𝒢, ∀ v, G.deg v ≤ Δ)
    (hind : IsIndependent 𝒢 t) (hasym : EdgeAsym 𝒢 t) (P : Problem L) :
    SolvableIn 𝒢 P Δ t ↔ SolvableIn 𝒢 P.speedup Δ (t - 1) :=
  ⟨theorem_1_forward ht hΔ hind, theorem_1_backward ht hasym⟩

/-- **Corollary 1** (corrected as Theorem 1): for classes `𝒢 n Δ` of `n`-node graphs of maximum
degree `≤ Δ` and a time bound `T n Δ ≥ 1` such that each `𝒢 n Δ` is `T n Δ`-independent and has
edge symmetry breaking at radius `T n Δ`. (Algorithms know `n` and `Δ`, so an algorithm for the
whole class is a family of algorithms, one per `(n, Δ)`.) -/
theorem corollary_1 [Nonempty L] (𝒢 : (n : ℕ) → ℕ → Set (LGraph I n)) (T : ℕ → ℕ → ℕ)
    (hT : ∀ n Δ, 1 ≤ T n Δ) (hΔ : ∀ n Δ, ∀ G ∈ 𝒢 n Δ, ∀ v, G.deg v ≤ Δ)
    (hind : ∀ n Δ, IsIndependent (𝒢 n Δ) (T n Δ)) (hasym : ∀ n Δ, EdgeAsym (𝒢 n Δ) (T n Δ))
    (P : Problem L) :
    (∀ n Δ, SolvableIn (𝒢 n Δ) P Δ (T n Δ)) ↔
      ∀ n Δ, SolvableIn (𝒢 n Δ) P.speedup Δ (T n Δ - 1) :=
  forall₂_congr fun n Δ => theorem_1 (hT n Δ) (hΔ n Δ) (hind n Δ) (hasym n Δ) P

/-! ### Theorem 2 -/

/-- **Theorem 2** with edge symmetry breaking in the general form `EdgeAsym`. -/
theorem theorem_2_of_edgeAsym [Nonempty L] {Δ t : ℕ} (ht : 1 ≤ t)
    (hΔ : ∀ G ∈ 𝒢, ∀ v, G.deg v ≤ Δ) (hind : IsIndependent 𝒢 t) (hasym : EdgeAsym 𝒢 t)
    (P : Problem L) :
    SolvableIn 𝒢 P Δ t ↔ SolvableIn 𝒢 P.speedupMax Δ (t - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel, solvableIn_iff_view, solvableIn_iff_view]
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨C, hC⟩ := ViewSystem.speedupMax_forward (ind1_of hind.1) (ind2_of hind.2)
      (edgeAsym_of hasym) (fun G v => hΔ G.1 G.2 v) (solvesN_iff.2 hA)
    exact ⟨C, solvesP_iff.1 hC⟩
  · rintro ⟨C, hC⟩
    obtain ⟨A, hA⟩ := ViewSystem.speedupMax_backward (edgeAsym_of hasym) (solvesP_iff.2 hC)
    exact ⟨A, solvesN_iff.1 hA⟩

/-- The backward direction for the "half-simplified" problem `(Π'_{1/2})_1` (used in §4.5, where
only the first half step is simplified). -/
theorem solvableIn_of_edgeStepMax_nodeStep [Nonempty L] {Δ t : ℕ} (ht : 1 ≤ t)
    (hasym : EdgeAsym 𝒢 t) {P : Problem L}
    (h : SolvableIn 𝒢 P.edgeStepMax.nodeStep Δ (t - 1)) : SolvableIn 𝒢 P Δ t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  obtain ⟨C, hC⟩ := (solvableIn_iff_view _ _ _ _).1 h
  rw [solvableIn_iff_view]
  have h2 := ViewSystem.solvesE_ofPrev (edgeAsym_of hasym) (solvesP_iff (𝒢 := 𝒢).2 hC)
  have h3 : (viewSystem 𝒢 s).SolvesE P.edgeStep Δ (ViewSystem.ofPrev P.edgeStepMax Δ C) :=
    fun G => (h2 G).mono subset_rfl (edgeStepMax_g_subset _ _) subset_rfl
  exact ⟨_, solvesN_iff.1 (ViewSystem.solvesN_ofEdge h3)⟩

/-- **Theorem 2.** If, in addition to the hypotheses of Theorem 1 (`t`-independence, maximum
degree `≤ Δ`), the inputs contain an orientation of every edge, then `Π` is solvable in `t` rounds
iff the simplified problem `Π'_1` is solvable in `t - 1` rounds. -/
theorem theorem_2 [Nonempty L] {Δ t : ℕ} (ht : 1 ≤ t) (hΔ : ∀ G ∈ 𝒢, ∀ v, G.deg v ≤ Δ)
    (hind : IsIndependent 𝒢 t) {o : I → Bool} (hor : HasOrientation 𝒢 o) (P : Problem L) :
    SolvableIn 𝒢 P Δ t ↔ SolvableIn 𝒢 P.speedupMax Δ (t - 1) :=
  theorem_2_of_edgeAsym ht hΔ hind (hor.edgeAsym ht) P

/-! ### Non-vacuity: a graph with distinct input lists -/

/-- If the nodes of `G` have pairwise distinct input lists (e.g. the inputs contain unique
identifiers), the class `{G}` is `t`-independent for every `t` and has edge symmetry breaking, so
all hypotheses of Theorems 1 and 2 (except the orientation of `theorem_2`) are satisfiable. -/
theorem isIndependent_singleton_of_injective {G : LGraph I n} (hs : G.G.IsSimple)
    (hinj : Function.Injective G.inputs) (t : ℕ) : IsIndependent ({G} : Set (LGraph I n)) t ∧ EdgeAsym ({G} : Set (LGraph I n)) t := by
  have hv : ∀ s, Function.Injective (G.view s) := fun s' u v h => hinj (by
    have := congrArg ViewT.inputs h; simpa using this)
  cases t with
  | zero => exact ⟨trivial, trivial⟩
  | succ s =>
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro G' hG' v i hi H₁ hH₁ w₁ k₁ hk₁ he₁ H₂ hH₂ w₂ k₂ hk₂ he₂
      obtain rfl : G' = G := hG'
      obtain rfl : H₁ = G' := hH₁
      obtain rfl : H₂ = H₁ := hH₂
      simp only [LGraph.eview, Prod.mk.injEq] at he₁ he₂
      obtain rfl := hv s he₁.1
      obtain rfl := he₁.2.1
      obtain rfl := hv s he₂.1
      exact ⟨_, rfl, w₁, k₁, hk₁, rfl, rfl, rfl⟩
    · intro G' hG' v Hs ws hws
      obtain rfl : G' = G := hG'
      refine ⟨_, rfl, v, rfl, fun i hi => ?_⟩
      obtain ⟨hH, he⟩ := hws i hi
      obtain rfl : Hs i = G' := hH
      rw [hv s he]
    · intro G' hG' v i hi
      obtain rfl : G' = G := hG'
      exact Or.inl fun h => hs.1 v i hi (hv s h)

end AutomaticSpeedup
