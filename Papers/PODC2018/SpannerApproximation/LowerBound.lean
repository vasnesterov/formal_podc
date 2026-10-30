import Papers.PODC2018.SpannerApproximation.Graph
import Podc.Computability.Distributed.Congest.AliceOutput
import Podc.Computability.CommunicationComplexity.GapDisjointness

/-!
# CONGEST lower bounds for directed `k`-spanner approximation (§2.1–2.2)

* `ofArcs`: a family of lower-bound graphs given by input-dependent arc sets (network = underlying
  undirected graph, node input = directions of incident arcs).
* `family e`: the family `G(ℓ, β)` (with `p` padding vertices) transported to an arbitrary vertex
  type `V ≃ Vtx ℓ β p`; Alice simulates `V \ Y1`, Bob simulates `Y1`; `3ℓ` cut arcs.
* `lemma_2_7` (deterministic, via gap disjointness, Lemma 2.5) and `lemma_2_4` (randomized,
  conditional on the randomized communication complexity of set disjointness, Lemma 2.1).
* `theorem_2_8`: deterministic `Ω(n / (√α · B))` bound; `theorem_1_1`: randomized
  `Ω(√(n/α) / B)` bound (`B = O(log n)` gives the paper's bounds).
-/

namespace Podc.SpannerApproximation

open Finset Relation Cslib.Congest Cslib.CommunicationComplexity Protocol

/-! ### Families of lower-bound digraphs -/

section OfArcs

variable {V : Type*} [Fintype V] [DecidableEq V]

-- CSLib candidate
/-- A family of lower-bound graphs whose members are digraphs `E x y` (arc sets): the network is
the underlying undirected graph `net (E x y)`, the input of node `v` is `view (E x y) v` (its
outgoing and incoming arcs). Only the independence conditions on the arcs have to be checked. -/
def ofArcs {X Y : Type*} (E : X → Y → Finset (V × V)) (alice : V → Bool)
    (Ecut : Finset (V × V)) (Ecut_sub : ∀ p ∈ Ecut, alice p.1 = true ∧ alice p.2 = false)
    (cut : ∀ x y a b, alice a = true → alice b = false → ((a, b) ∈ E x y ∨ (b, a) ∈ E x y) →
      (a, b) ∈ Ecut)
    (indep_y : ∀ x y y' u v, (alice u = true ∨ alice v = true) →
      ((u, v) ∈ E x y ↔ (u, v) ∈ E x y'))
    (indep_x : ∀ x x' y u v, (alice u = false ∨ alice v = false) →
      ((u, v) ∈ E x y ↔ (u, v) ∈ E x' y)) :
    LBFamily X Y V (DInput V) where
  G x y := net (E x y)
  inp x y := view (E x y)
  alice := alice
  Ecut := Ecut
  Ecut_sub := Ecut_sub
  adj_cut x y a b ha hb h := cut x y a b ha hb h.2
  adj_alice x y y' a b ha hb := by
    simp only [net, indep_y x y y' a b (Or.inl ha), indep_y x y y' b a (Or.inl hb)]
  adj_bob x x' y a b ha hb := by
    simp only [net, indep_x x x' y a b (Or.inl ha), indep_x x x' y b a (Or.inl hb)]
  adj_fixed x x' y y' a b ha hb := by
    simp only [net, indep_y x y y' a b (Or.inl ha), indep_y x y y' b a (Or.inr ha),
      indep_x x x' y' a b (Or.inr hb), indep_x x x' y' b a (Or.inl hb)]
  inp_alice x y y' v hv := by
    funext w
    simp only [view, indep_y x y y' v w (Or.inl hv), indep_y x y y' w v (Or.inr hv)]
  inp_bob x x' y v hv := by
    funext w
    simp only [view, indep_x x x' y v w (Or.inl hv), indep_x x x' y w v (Or.inr hv)]

instance {X Y : Type*} {E : X → Y → Finset (V × V)} {alice : V → Bool} {Ecut : Finset (V × V)}
    {h1 h2 h3 h4} (x : X) (y : Y) :
    DecidableRel ((ofArcs E alice Ecut h1 h2 h3 h4).G x y).Adj :=
  inferInstanceAs (DecidableRel (net (E x y)).Adj)

end OfArcs

/-! ### Relabelled intersections -/

section Relabel

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

lemma card_mapArcs_inter (e : V ≃ W) (H : Finset (V × V)) (D : Finset (W × W)) :
    (mapArcs e H ∩ D).card = (H ∩ mapArcs e.symm D).card := by
  have : mapArcs e H ∩ D = mapArcs e (H ∩ mapArcs e.symm D) := by
    ext q; simp
  rw [this, card_mapArcs]

end Relabel

/-! ### The gadget family on an arbitrary vertex type -/

namespace Vtx

variable {ℓ β p : ℕ}

/-- The cut arcs `(a, b)`, `a ∈ V_A`, `b ∈ V_B = Y1`: the matching and the arcs `y²ᵢ → y³ᵢ`. -/
def cutPair : Vtx ℓ β p → Vtx ℓ β p → Bool
  | x1 i, y1 i' => decide (i = i')
  | x2 i, y2 i' => decide (i = i')
  | y3 i, y2 i' => decide (i = i')
  | _, _ => false

lemma cutPair_spec {u v : Vtx ℓ β p} (h : cutPair u v = true) :
    bobSide u = false ∧ bobSide v = true := by
  cases u <;> cases v <;> simp_all [cutPair, bobSide]

lemma arc_cut {a b : Inp ℓ} {u v : Vtx ℓ β p} (hu : bobSide u = false) (hv : bobSide v = true)
    (h : arc a b u v = true ∨ arc a b v u = true) : cutPair u v = true := by
  cases u <;> cases v <;> simp_all [arc, bobSide, cutPair, eq_comm]

lemma arc_indep_b {a b b' : Inp ℓ} {u v : Vtx ℓ β p}
    (h : bobSide u = false ∨ bobSide v = false) : arc a b u v = arc a b' u v := by
  cases u <;> cases v <;> simp_all [arc, bobSide]

lemma arc_indep_a {a a' b : Inp ℓ} {u v : Vtx ℓ β p}
    (h : bobSide u = true ∨ bobSide v = true) : arc a b u v = arc a' b u v := by
  cases u <;> cases v <;> simp_all [arc, bobSide]

lemma isD_bobSide {u v : Vtx ℓ β p} (h : isD u v = true) :
    bobSide u = false ∧ bobSide v = false := by
  cases u <;> cases v <;> simp_all [isD, bobSide]

end Vtx

open Vtx

variable {V : Type*} [Fintype V] [DecidableEq V] {ℓ β p : ℕ}

/-- The digraph `G(ℓ, β)` (with `p` padding vertices) on the vertex type `V ≃ Vtx ℓ β p`. -/
def Ev (e : V ≃ Vtx ℓ β p) (a b : Inp ℓ) : Finset (V × V) := mapArcs e.symm (arcs a b)

omit [Fintype V] [DecidableEq V] in
@[simp] lemma mem_Ev (e : V ≃ Vtx ℓ β p) (a b : Inp ℓ) (q : V × V) :
    q ∈ Ev e a b ↔ arc a b (e q.1) (e q.2) = true := by
  simp [Ev]

/-- The arcs of `D` on `V`. -/
def Dv (e : V ≃ Vtx ℓ β p) : Finset (V × V) := mapArcs e.symm dArcs

/-- The cut arcs on `V`. -/
def cutV (e : V ≃ Vtx ℓ β p) : Finset (V × V) := univ.filter fun q => cutPair (e q.1) (e q.2)

/-- The family of lower-bound graphs `G(ℓ, β)` on `V` (Alice: `V \ Y1`; Bob: `Y1`). -/
def family (e : V ≃ Vtx ℓ β p) : LBFamily (Inp ℓ) (Inp ℓ) V (DInput V) :=
  ofArcs (Ev e) (fun v => !bobSide (e v)) (cutV e)
    (fun q hq => by
      have := cutPair_spec (by simpa [cutV] using hq)
      simp [this])
    (fun x y u v hu hv h => by
      simp only [Bool.not_eq_true', Bool.not_eq_false'] at hu hv
      simpa [cutV] using arc_cut hu hv (by simpa using h))
    (fun x y y' u v h => by
      simp only [Bool.not_eq_true'] at h
      simp only [mem_Ev]
      rw [arc_indep_b (b' := y') h])
    (fun x x' y u v h => by
      simp only [Bool.not_eq_false'] at h
      simp only [mem_Ev]
      rw [arc_indep_a (a' := x') h])

instance (e : V ≃ Vtx ℓ β p) (a b : Inp ℓ) : DecidableRel ((family e).G a b).Adj :=
  inferInstanceAs (DecidableRel (net (Ev e a b)).Adj)

/-- The cut has at most `3ℓ` arcs. -/
lemma card_cutV_le (e : V ≃ Vtx ℓ β p) : (cutV e).card ≤ 3 * ℓ := by
  classical
  let f : Fin 3 × Fin ℓ → V × V := fun q => match q.1 with
    | 0 => (e.symm (x1 q.2), e.symm (y1 q.2))
    | 1 => (e.symm (x2 q.2), e.symm (y2 q.2))
    | 2 => (e.symm (y3 q.2), e.symm (y2 q.2))
  have hsub : cutV e ⊆ univ.image f := by
    rintro ⟨u, v⟩ h
    simp only [cutV, mem_filter, mem_univ, true_and] at h
    simp only [mem_image, mem_univ, true_and, Prod.exists]
    have hu : u = e.symm (e u) := by simp
    have hv : v = e.symm (e v) := by simp
    generalize e u = u' at hu h
    generalize e v = v' at hv h
    subst hu hv
    cases u' <;> cases v' <;> simp [cutPair] at h <;> subst h
    · exact ⟨0, _, rfl⟩
    · exact ⟨1, _, rfl⟩
    · exact ⟨2, _, rfl⟩
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  simp

lemma family_alice_of_Dv (e : V ≃ Vtx ℓ β p) (q : V × V) (hq : q ∈ Dv e) :
    (family e).alice q.1 = true ∧ (family e).alice q.2 = true := by
  have := isD_bobSide (by simpa [Dv, dArcs] using hq)
  simp [family, ofArcs, this]

omit [Fintype V] [DecidableEq V] in
/-- The digraphs of the family have no loops. -/
lemma Ev_loopless (e : V ≃ Vtx ℓ β p) (a b : Inp ℓ) (v : V) : (v, v) ∉ Ev e a b := by
  simp [arc_irrefl]

omit [Fintype V] [DecidableEq V] in
/-- The networks of the family are connected (`ℓ, β ≥ 1`). -/
lemma Ev_connected (e : V ≃ Vtx ℓ β p) (a b : Inp ℓ) (hℓ : 0 < ℓ) (hβ : 0 < β) :
    (net (Ev e a b)).Connected := by
  let iso : net (Ev e a b) ≃g net (arcs a b : Finset (Vtx ℓ β p × _)) :=
    { toEquiv := e
      map_rel_iff' := by
        intro u v
        simp [net, Ev] }
  exact iso.connected_iff.2 (net_connected a b hℓ hβ)

/-! ### Lemma 2.7 (deterministic) -/

/-- Alice's decision: "more than `τ` arcs of `D` are selected". -/
noncomputable def decideD (e : V ≃ Vtx ℓ β p) {σ : Type*} (pick : V → σ → V → V → Bool) (τ : ℝ)
    (_ : Inp ℓ) (st : V → σ) : Bool := by
  classical
  exact decide (τ < ((selected pick st ∩ Dv e).card : ℝ))

lemma decideD_congr (e : V ≃ Vtx ℓ β p) {σ : Type*} (pick : V → σ → V → V → Bool) (τ : ℝ)
    (x : Inp ℓ) (st st' : V → σ) (h : ∀ v, (family e).alice v = true → st v = st' v) :
    decideD e pick τ x st = decideD e pick τ x st' := by
  simp only [decideD]
  rw [selected_inter_eq pick (fun v => (family e).alice v = true) (Dv e)
    (fun q hq => family_alice_of_Dv e q hq) h]

omit [Fintype V] [DecidableEq V] in
/-- The arcs not in `D`, on `V`: a `k`-spanner of `Ev e a b` for disjoint inputs. -/
lemma nonD_isDiSpanner_Ev (e : V ≃ Vtx ℓ β p) {a b : Inp ℓ}
    (hab : ∀ q, ¬(a q = true ∧ b q = true)) {k : ℕ} (hk : 5 ≤ k) :
    IsDiSpanner (Ev e a b) (mapArcs e.symm (nonD a b)) k :=
  (isDiSpanner_mapArcs e.symm).2 (nonD_isDiSpanner hab hk)

omit [Fintype V] in
/-- Every spanner of `Ev e a b` contains `β² · |a ∩ b|` arcs of `D`. -/
lemma card_inter_Dv_ge (e : V ≃ Vtx ℓ β p) {a b : Inp ℓ} {H : Finset (V × V)} {k : ℕ}
    (hH : IsDiSpanner (Ev e a b) H k) : β ^ 2 * (inter a b).card ≤ (H ∩ Dv e).card := by
  have h' : IsDiSpanner (arcs a b) (mapArcs e H) k := by
    have := (isDiSpanner_mapArcs e (E := Ev e a b) (H := H)).2 hH
    simpa [Ev, mapArcs_symm_mapArcs] using this
  have := card_inter_D_ge h'
  rwa [card_mapArcs_inter] at this

lemma disj_eq_true_iff {ι : Type*} [Fintype ι] {x y : ι → Bool} :
    disj x y = true ↔ ∀ q, ¬(x q = true ∧ y q = true) := by
  simp [disj]

/-- The bound on the number of non-`D` arcs, `2ℓβ + 2ℓ² + 3ℓ + p`. -/
abbrev nonDBound (ℓ β p : ℕ) : ℕ := 2 * ℓ * β + 2 * ℓ ^ 2 + 3 * ℓ + p

/-- **Lemma 2.7.** Let `A` be a deterministic CONGEST algorithm with `B`-bit messages that, within
`T` rounds, outputs an `α`-approximate minimum directed `k`-spanner (`k ≥ 5`) of every graph of
the family `G(ℓ, β)`. If the threshold `t = 2ℓβ + 2ℓ² + 3ℓ + p` (an upper bound on the optimum for
disjoint inputs) satisfies `α · t < β²ℓ²/12` (the number of `D`-arcs forced for inputs that are
far from disjoint), then `ℓ² ≤ 3 · (6ℓ · B · T + 1)`, i.e. `T = Ω(ℓ / B)`. -/
theorem lemma_2_7 {σ : Type*} {B : ℕ} (e : V ≃ Vtx ℓ β p) {α : ℝ} (hα : 0 ≤ α) {k : ℕ}
    (hk : 5 ≤ k) (hgap : 12 * (α * nonDBound ℓ β p) < β ^ 2 * ℓ ^ 2)
    (A : Algorithm V (DInput V) σ B) (pick : V → σ → V → V → Bool) (T : ℕ)
    (hA : ∀ a b, IsApproxDiSpanner α (Ev e a b) (outArcs A pick (Ev e a b) T) k) :
    ℓ ^ 2 ≤ 3 * (T * (2 * (3 * ℓ * B)) + 1) := by
  classical
  set τ : ℝ := α * nonDBound ℓ β p
  obtain ⟨P, hc, hP⟩ := (family e).simulation_alice A T (decideD e pick τ)
    (decideD_congr e pick τ)
  have key : ∀ a b, P.eval a b =
      decide (τ < ((outArcs A pick (Ev e a b) T ∩ Dv e).card : ℝ)) := by
    intro a b
    rw [hP a b]
    simp only [decideD]
    unfold outArcs
    congr
  have h := gapDisj_lowerBound (P := P) false (fun a b hd => ?_) (fun a b hfar => ?_) hc
  · simp only [Fintype.card_prod, Fintype.card_fin] at h
    have hcut : (family e).Ecut.card ≤ 3 * ℓ := card_cutV_le e
    calc ℓ ^ 2 = ℓ * ℓ := sq ℓ
      _ ≤ _ := h
      _ ≤ _ := by gcongr
  · rw [key, decide_eq_false_iff_not, not_lt]
    have hsp := nonD_isDiSpanner_Ev e (disj_eq_true_iff.1 hd) hk
    have h1 := (hA a b).2 _ hsp
    rw [card_mapArcs] at h1
    have h2 : ((nonD a b : Finset (Vtx ℓ β p × _)).card : ℝ) ≤ nonDBound ℓ β p := by
      exact_mod_cast card_nonD_le a b
    have h3 : ((outArcs A pick (Ev e a b) T ∩ Dv e).card : ℝ) ≤
        (outArcs A pick (Ev e a b) T).card := by
      exact_mod_cast card_le_card inter_subset_left
    calc _ ≤ _ := h3
      _ ≤ _ := h1
      _ ≤ τ := mul_le_mul_of_nonneg_left h2 hα
  · rw [key]
    simp only [Bool.not_false, decide_eq_true_eq]
    have h1 := card_inter_Dv_ge e (hA a b).1
    simp only [Fintype.card_prod, Fintype.card_fin] at hfar
    have hfar' : ((ℓ : ℝ) ^ 2) ≤ 12 * ((inter a b).card : ℝ) := by
      rw [sq]; exact_mod_cast hfar
    have h1' : (β : ℝ) ^ 2 * (inter a b).card ≤ ((outArcs A pick (Ev e a b) T ∩ Dv e).card) := by
      exact_mod_cast h1
    have hgap' : 12 * τ < (β : ℝ) ^ 2 * ℓ ^ 2 := by exact_mod_cast hgap
    nlinarith [sq_nonneg (β : ℝ)]

/-! ### Lemma 2.4 (randomized) -/

/-- The randomized communication complexity of (the complement of) set disjointness is at least
`κ · K` for protocols with error `≤ δ` (Lemma 2.1; Kalyanasundaram–Schnitger, Razborov). **Not
proved**: it enters the randomized results as a hypothesis. Coin spaces are nonempty: otherwise
every protocol is vacuously correct and the hypothesis would force `κ ≤ 0`. -/
def RandDisjLB (δ κ : ℝ) : Prop :=
  ∀ (ι RA RB : Type) [Fintype ι] [Fintype RA] [Fintype RB] [Nonempty RA] [Nonempty RB]
    (P : Protocol ((ι → Bool) × RA) ((ι → Bool) × RB) Bool) (c : ℕ),
    P.RandComputes (fun x y => !disj x y) δ → P.CostLE c → κ * Fintype.card ι ≤ c

/-- **Lemma 2.4** (randomized), conditional on `RandDisjLB δ κ`. Let `A` be a randomized CONGEST
algorithm (private random strings `r v : ρ`) with `B`-bit messages that, on every graph of the
family `G(ℓ, β)`, outputs within `T` rounds an `α`-approximate minimum directed `k`-spanner
(`k ≥ 5`) except with probability `≤ δ`. If `α · t < β²` for `t = 2ℓβ + 2ℓ² + 3ℓ + p` (the
optimum for disjoint inputs is `≤ t`, every spanner for intersecting inputs has `≥ β²` arcs of
`D`), then `κ · ℓ² ≤ 6ℓ · B · T + 1`. -/
theorem lemma_2_4 {V ρ σ : Type} [Fintype V] [DecidableEq V] [Fintype ρ] [Nonempty ρ] {B : ℕ}
    (e : V ≃ Vtx ℓ β p) {α : ℝ} (hα : 0 ≤ α) {k : ℕ} (hk : 5 ≤ k) {δ κ : ℝ}
    (hDisj : RandDisjLB δ κ) (hgap : α * nonDBound ℓ β p < β ^ 2)
    (A : Algorithm V (DInput V × ρ) σ B) (pick : V → σ → V → V → Bool) (T : ℕ)
    (hA : ∀ a b, (failCount A pick (Ev e a b) T α k : ℝ) ≤ δ * Fintype.card (V → ρ)) :
    κ * ℓ ^ 2 ≤ T * (2 * (3 * ℓ * B)) + 1 := by
  classical
  set τ : ℝ := α * nonDBound ℓ β p
  obtain ⟨P, hc, hP⟩ := (family e).rand_simulation_alice (ρ := ρ) A T (decideD e pick τ)
    (decideD_congr e pick τ)
  -- on every good random string, Alice's answer is `¬DISJ`
  have good : ∀ a b (r : V → ρ), IsApproxDiSpanner α (Ev e a b) (outArcsR A pick (Ev e a b) T r) k →
      decideD e pick τ a (A.run ((family e).G a b) (fun v => ((family e).inp a b v, r v)) T) =
        !disj a b := by
    intro a b r hr
    have hrun : A.run ((family e).G a b) (fun v => ((family e).inp a b v, r v)) T =
        A.run (net (Ev e a b)) (fun v => (view (Ev e a b) v, r v)) T := rfl
    simp only [decideD, hrun]
    cases hd : disj a b
    · simp only [Bool.not_false, decide_eq_true_eq]
      change τ < ((outArcsR A pick (Ev e a b) T r ∩ Dv e).card : ℝ)
      have hq : ∃ q, a q = true ∧ b q = true := by simpa [disj] using hd
      obtain ⟨q, hq⟩ := hq
      have h1 := card_inter_Dv_ge e hr.1
      have hpos : 1 ≤ (inter a b).card := card_pos.2 ⟨q, by simp [inter, hq]⟩
      have h1' : (β : ℝ) ^ 2 * (inter a b).card ≤ ((outArcsR A pick (Ev e a b) T r ∩ Dv e).card) := by
        exact_mod_cast h1
      have hpos' : (1 : ℝ) ≤ (inter a b).card := by exact_mod_cast hpos
      nlinarith [sq_nonneg (β : ℝ)]
    · simp only [Bool.not_true, decide_eq_false_iff_not, not_lt]
      change ((outArcsR A pick (Ev e a b) T r ∩ Dv e).card : ℝ) ≤ τ
      have hsp := nonD_isDiSpanner_Ev e (disj_eq_true_iff.1 hd) hk
      have h1 := hr.2 _ hsp
      rw [card_mapArcs] at h1
      have h2 : ((nonD a b : Finset (Vtx ℓ β p × _)).card : ℝ) ≤ nonDBound ℓ β p := by
        exact_mod_cast card_nonD_le a b
      have h3 : ((outArcsR A pick (Ev e a b) T r ∩ Dv e).card : ℝ) ≤
          (outArcsR A pick (Ev e a b) T r).card := by
        exact_mod_cast card_le_card inter_subset_left
      calc _ ≤ _ := h3
        _ ≤ _ := h1
        _ ≤ τ := mul_le_mul_of_nonneg_left h2 hα
  have hcard : (Fintype.card ({v // (family e).alice v = true} → ρ) : ℝ) *
      Fintype.card ({v // (family e).alice v = false} → ρ) = Fintype.card (V → ρ) := by
    rw [← Nat.cast_mul, ← Fintype.card_prod,
      Fintype.card_congr ((family e).combineEquiv (ρ := ρ))]
  have hrand : P.RandComputes (fun x y => !disj x y) δ := by
    intro a b
    rw [(family e).errCount_simulation_alice A T _ _ P hP a b, hcard]
    refine le_trans ?_ (hA a b)
    simp only [failCount]
    norm_cast
    refine card_le_card fun r => ?_
    simp only [mem_filter, mem_univ, true_and]
    intro hr hok
    exact hr (good a b r hok)
  have h := hDisj _ _ _ P _ hrand hc
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  have hcut : ((family e).Ecut.card : ℝ) ≤ 3 * ℓ := by exact_mod_cast card_cutV_le e
  have hκ : κ * ℓ ^ 2 = κ * ((ℓ * ℓ : ℕ) : ℝ) := by push_cast; ring
  rw [hκ]
  refine h.trans ?_
  push_cast
  have : (T : ℝ) * (2 * ((family e).Ecut.card * B)) ≤ T * (2 * (3 * ℓ * B)) := by
    gcongr
  linarith

end Podc.SpannerApproximation
