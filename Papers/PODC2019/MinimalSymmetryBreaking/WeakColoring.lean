import Mathlib
import Cslib.Computability.Distributed.Local.Locality

/-!
# Lemma 2 of Balliu–Hirvonen–Olivetti–Suomela (PODC 2019): weak colorings reduce to each other

A. Balliu, J. Hirvonen, D. Olivetti, J. Suomela, *Hardness of minimal symmetry breaking in
distributed computing*, PODC 2019 (arXiv:1811.01643), Section 3.1.

Model: deterministic LOCAL, extensional locality (`Cslib.Local.IsLocal R f`: the output of a node
depends only on its radius-`R` view). The algorithm below is anonymous (it does not use the node
names / identifiers) and works on arbitrary simple graphs (no finiteness or degree bound).

## Main definitions

* `IsDistWeakColoring G k φ` (Definition 1): every node has a node of a different colour within
  distance `k`.
* `IsWeakColoring G ψ`: every node has a neighbour of a different colour.
* `dmin k G φ v`: the distance from `v` to the closest node of a different colour (searched within
  distance `k`); `parityColor k G φ v = (φ v, dmin k G φ v mod 2)`.
* `greedyAlg`: the locally-iterative greedy MIS by colour classes on the subgraph of
  bichromatic edges; `weakTwo N G col`: its output after `N` rounds.
* `lemma2Alg k c`: the composed algorithm.

## Main results

* `parityColor_isWeakColoring` (first step of the proof of Lemma 2): `(φ, dmin mod 2)` is a weak
  `2c`-colouring, computed in `k` rounds (`parityColor_isLocal`).
* `weakTwo_isWeakColoring`, `weakTwo_isLocal`: a weak colouring with values `< N` gives a weak
  2-colouring in `N` rounds (greedy MIS of the bichromatic subgraph by colour classes).
* `lemma_2_explicit`, `lemma_2` (Lemma 2): from a distance-`k` weak `c`-colouring a weak
  2-colouring is computed in `k + 2c` rounds.
-/

namespace Podc.MinimalSymmetryBreaking

open SimpleGraph Cslib.Local Cslib.LocallyIterative

variable {V C : Type*}

/-! ### Definitions -/

/-- Definition 1 of [BHOS19]: `φ` is a *distance-`k` weak colouring* of `G` if every node `v` has a
node `u` with `dist(v, u) ≤ k` and `φ u ≠ φ v`. -/
def IsDistWeakColoring (G : SimpleGraph V) (k : ℕ) (φ : V → C) : Prop :=
  ∀ v, ∃ u, G.edist v u ≤ k ∧ φ u ≠ φ v

/-- `ψ` is a *weak colouring* of `G`: every node has a neighbour of a different colour. -/
def IsWeakColoring (G : SimpleGraph V) (ψ : V → C) : Prop :=
  ∀ v, ∃ u, G.Adj v u ∧ ψ u ≠ ψ v

/-- A distance-1 weak colouring is the same as a weak colouring (Definition 1 of [BHOS19]). -/
lemma isDistWeakColoring_one_iff {G : SimpleGraph V} {φ : V → C} :
    IsDistWeakColoring G 1 φ ↔ IsWeakColoring G φ := by
  refine forall_congr' fun v => exists_congr fun u => ?_
  constructor
  · rintro ⟨h1, hne⟩
    refine ⟨?_, hne⟩
    rcases eq_or_ne v u with rfl | huv
    · exact absurd rfl hne
    · have h0 : G.edist v u ≠ 0 := by simpa using huv
      have : G.edist v u = 1 := by
        have : G.edist v u ≤ 1 := by exact_mod_cast h1
        exact le_antisymm this (Order.one_le_iff_ne_zero.2 h0)
      exact edist_eq_one_iff_adj.1 this
  · rintro ⟨hadj, hne⟩
    exact ⟨by rw [edist_eq_one_iff_adj.2 hadj]; simp, hne⟩

/-- Weak colourings transfer along injective maps of colours. -/
lemma IsWeakColoring.comp {D : Type*} {G : SimpleGraph V} {ψ : V → C} (h : IsWeakColoring G ψ)
    {e : C → D} (he : Function.Injective e) : IsWeakColoring G (e ∘ ψ) := fun v => by
  obtain ⟨u, huv, hne⟩ := h v
  exact ⟨u, huv, fun h' => hne (he h')⟩

/-! ### Generic locality lemmas -/

/-- Post-composing a local algorithm with a function on outputs keeps it local. -/
-- CSLib candidate
lemma isLocal_map {α β γ : Type*} {R : ℕ} {f : SimpleGraph V → (V → α) → V → β}
    (hf : IsLocal R f) (g : β → γ) : IsLocal R (fun G x v => g (f G x v)) :=
  fun _ _ _ _ _ hv => congrArg g (hf _ _ _ _ _ hv)

/-! ### Step 1: a weak `2c`-colouring from a distance-`k` weak `c`-colouring -/

/-- The distances `d ≤ k` such that some node of a colour different from `φ v` is within distance
`d` of `v`. -/
def nearSet (k : ℕ) (G : SimpleGraph V) (φ : V → C) (v : V) : Set ℕ :=
  {d | d ≤ k ∧ ∃ u, G.edist v u ≤ d ∧ φ u ≠ φ v}

/-- The distance from `v` to the closest node of a different colour, if it is at most `k`
(otherwise `0`). -/
noncomputable def dmin (k : ℕ) (G : SimpleGraph V) (φ : V → C) (v : V) : ℕ :=
  sInf (nearSet k G φ v)

/-- The weak `2c`-colouring of the proof of Lemma 2: `φ' v = (φ v, dmin v mod 2)`. -/
noncomputable def parityColor (k : ℕ) (G : SimpleGraph V) (φ : V → C) (v : V) : C × Fin 2 :=
  (φ v, ⟨dmin k G φ v % 2, Nat.mod_lt _ two_pos⟩)

lemma dmin_le {k : ℕ} {G : SimpleGraph V} {φ : V → C} {v u : V} {d : ℕ} (hd : d ≤ k)
    (hu : G.edist v u ≤ d) (hne : φ u ≠ φ v) : dmin k G φ v ≤ d :=
  Nat.sInf_le ⟨hd, u, hu, hne⟩

/-- Under a distance-`k` weak colouring, `dmin` is attained. -/
lemma exists_edist_eq_dmin {k : ℕ} {G : SimpleGraph V} {φ : V → C}
    (hφ : IsDistWeakColoring G k φ) (v : V) :
    dmin k G φ v ≤ k ∧ ∃ u, G.edist v u = dmin k G φ v ∧ φ u ≠ φ v := by
  obtain ⟨u₀, hu₀, hne₀⟩ := hφ v
  obtain ⟨hk, u, hu, hne⟩ := Nat.sInf_mem (s := nearSet k G φ v) ⟨k, le_rfl, u₀, hu₀, hne₀⟩
  refine ⟨hk, u, ?_, hne⟩
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (edist_ne_top_of_le_natCast hu)
  rw [← hj] at hu ⊢
  have hjD : j ≤ dmin k G φ v := by exact_mod_cast hu
  have : dmin k G φ v ≤ j := dmin_le (hjD.trans hk) (by rw [← hj]) hne
  exact_mod_cast le_antisymm hjD this

/-- The first step of the proof of Lemma 2 of [BHOS19]: `(φ, dmin mod 2)` is a weak colouring. -/
theorem parityColor_isWeakColoring {k : ℕ} {G : SimpleGraph V} {φ : V → C}
    (hφ : IsDistWeakColoring G k φ) : IsWeakColoring G (parityColor k G φ) := by
  intro v
  obtain ⟨hk, u, hu, hne⟩ := exists_edist_eq_dmin hφ v
  rcases hD : dmin k G φ v with _ | m
  · rw [hD] at hu
    simp only [Nat.cast_zero, edist_eq_zero_iff] at hu
    exact absurd (congrArg φ hu).symm hne
  · rw [hD] at hu hk
    rw [edist_comm] at hu
    obtain ⟨w, hw, hwv⟩ := exists_adj_of_edist_eq_succ hu
    refine ⟨w, hwv.symm, ?_⟩
    by_cases hφw : φ w = φ v
    · -- `w` has the same colour as `v`, hence `dmin w = m`
      have hle : dmin k G φ w ≤ m :=
        dmin_le (by omega) (by rw [edist_comm, hw]) (by rw [hφw]; exact hne)
      have hge : m ≤ dmin k G φ w := by
        obtain ⟨-, u', hu', hne'⟩ := exists_edist_eq_dmin hφ w
        have h1 : G.edist v w ≤ (1 : ℕ) := by rw [edist_eq_one_iff_adj.2 hwv.symm]; simp
        have h2 := edist_le_natCast_add h1 hu'.le
        have := dmin_le (k := k) (φ := φ) (by omega) h2 (by rw [← hφw]; exact hne')
        omega
      have hm : dmin k G φ w = m := le_antisymm hle hge
      intro h
      have := congrArg (fun p => (p.2 : ℕ)) h
      simp only [parityColor, hm, hD] at this
      omega
    · intro h
      exact hφw (congrArg Prod.fst h)

/-- The first step of the proof of Lemma 2 is computed in `k` rounds. -/
theorem parityColor_isLocal (k : ℕ) : IsLocal (V := V) (α := C) k (parityColor k) := by
  intro G x G' x' v hv
  have hxv : x v = x' v := hv.2 v (by simp)
  have hS : nearSet k G x v = nearSet k G' x' v := by
    ext d
    simp only [nearSet, Set.mem_ofPred_eq]
    refine and_congr_right fun hd => exists_congr fun u => ?_
    rw [hv.1.edist_le_iff (x := u) hd, hxv]
    exact and_congr_right fun hu => by rw [hv.2 u (hu.trans (by exact_mod_cast hd))]
  simp only [parityColor, dmin, hxv, hS]

/-! ### Step 2: from a weak `N`-colouring to a weak 2-colouring in `N` rounds -/

open scoped Classical in
/-- Greedy maximal independent set of the bichromatic subgraph `H` (edges of `G` whose endpoints
have different colours) by colour classes, as a locally-iterative algorithm. The state of a node is
`(colour, joined?)`; in round `t` a node of colour `t` joins iff no `H`-neighbour has joined yet. -/
noncomputable def greedyAlg : Algorithm (ℕ × Bool) where
  step t s N := (s.1, s.2 || decide (s.1 = t ∧ ∀ y ∈ N, y.1 ≠ s.1 → y.2 = false))

/-- The greedy MIS state after `t` rounds, starting from the colouring `col`. -/
noncomputable def mis (G : SimpleGraph V) (col : V → ℕ) (t : ℕ) (v : V) : ℕ × Bool :=
  greedyAlg.run G (fun u => (col u, false)) t v

/-- Output of the weak 2-colouring algorithm: membership in the greedy MIS after `N` rounds. -/
noncomputable def weakTwo (N : ℕ) (G : SimpleGraph V) (col : V → ℕ) (v : V) : Bool :=
  (mis G col N v).2

section Greedy

variable {G : SimpleGraph V} {col : V → ℕ}

lemma mis_fst (t : ℕ) (v : V) : (mis G col t v).1 = col v := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih => simp only [mis, Algorithm.run_succ_apply, greedyAlg] at ih ⊢; exact ih v

open scoped Classical in
lemma mis_succ (t : ℕ) (v : V) : (mis G col (t + 1) v).2 = true ↔
    (mis G col t v).2 = true ∨
      (col v = t ∧ ∀ u, G.Adj v u → col u ≠ col v → (mis G col t u).2 = false) := by
  show ((mis G col t v).2 || decide _) = true ↔ _
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  change (_ ∨ ((mis G col t v).1 = t ∧ ∀ y ∈ nbrColors G (mis G col t) v,
    y.1 ≠ (mis G col t v).1 → y.2 = false)) ↔ _
  rw [mis_fst]
  refine or_congr_right (and_congr_right fun _ => ?_)
  simp only [mem_nbrColors, forall_exists_index, and_imp]
  constructor
  · intro H u huv hc; exact H _ u huv rfl (by rw [mis_fst]; exact hc)
  · rintro H y u huv rfl hc; rw [mis_fst] at hc; exact H u huv hc

lemma mis_mono {t t' : ℕ} (h : t ≤ t') {v : V} (hv : (mis G col t v).2 = true) :
    (mis G col t' v).2 = true := by
  induction h with
  | refl => exact hv
  | step _ ih => exact (mis_succ _ v).2 (Or.inl ih)

/-- Only nodes of colour `< t` have joined after `t` rounds. -/
lemma col_lt_of_mis {t : ℕ} {v : V} (hv : (mis G col t v).2 = true) : col v < t := by
  induction t with
  | zero => simp [mis] at hv
  | succ t ih =>
    rcases (mis_succ t v).1 hv with h | ⟨h, -⟩
    · exact (ih h).trans (Nat.lt_succ_self t)
    · omega

/-- Independence in the bichromatic subgraph. -/
lemma mis_independent (t : ℕ) {u v : V} (huv : G.Adj u v) (hc : col u ≠ col v)
    (hu : (mis G col t u).2 = true) (hv : (mis G col t v).2 = true) : False := by
  induction t generalizing u v with
  | zero => simp [mis] at hu
  | succ t ih =>
    rcases (mis_succ t u).1 hu with hu' | ⟨hcu, Hu⟩ <;>
      rcases (mis_succ t v).1 hv with hv' | ⟨hcv, Hv⟩
    · exact ih huv hc hu' hv'
    · simp [Hv u huv.symm hc] at hu'
    · simp [Hu v huv hc.symm] at hv'
    · exact hc (hcu.trans hcv.symm)

/-- Maximality in the bichromatic subgraph. -/
lemma mis_maximal {t : ℕ} {v : V} (ht : col v < t) :
    (mis G col t v).2 = true ∨ ∃ u, G.Adj v u ∧ col u ≠ col v ∧ (mis G col t u).2 = true := by
  by_cases H : ∃ u, G.Adj v u ∧ col u ≠ col v ∧ (mis G col (col v) u).2 = true
  · obtain ⟨u, huv, hc, hu⟩ := H
    exact Or.inr ⟨u, huv, hc, mis_mono ht.le hu⟩
  · refine Or.inl (mis_mono ht ((mis_succ _ v).2 (Or.inr ⟨rfl, fun u huv hc => ?_⟩)))
    simpa using fun h => H ⟨u, huv, hc, h⟩

/-- A weak colouring with values `< N` yields a weak 2-colouring (membership in the greedy MIS of
the bichromatic subgraph after `N` rounds). -/
theorem weakTwo_isWeakColoring {N : ℕ} (hN : ∀ v, col v < N) (hcol : IsWeakColoring G col) :
    IsWeakColoring G (weakTwo N G col) := by
  intro v
  by_cases hv : (mis G col N v).2 = true
  · obtain ⟨u, huv, hc⟩ := hcol v
    refine ⟨u, huv, fun h => ?_⟩
    simp only [weakTwo] at h
    exact mis_independent N huv hc.symm hv (by rw [h]; exact hv)
  · rcases mis_maximal (hN v) with h | ⟨u, huv, -, hu⟩
    · exact absurd h hv
    · exact ⟨u, huv, by simp only [weakTwo]; rw [hu]; simpa using hv⟩

end Greedy

/-- The greedy step runs in `N` rounds. -/
theorem weakTwo_isLocal (N : ℕ) : IsLocal (V := V) N (weakTwo N) := by
  have h1 : IsLocal (V := V) 0 (fun _ (col : V → ℕ) u => (col u, false)) :=
    isLocal_map (g := fun n : ℕ => (n, false)) isLocal_zero_label
  have h2 := (Algorithm.run_isLocal (V := V) greedyAlg N).comp h1
  exact isLocal_map h2 Prod.snd

/-! ### Lemma 2 -/

/-- Encoding of the `2c` colours `Fin c × Fin 2` as natural numbers `< 2c`. -/
def enc {c : ℕ} (p : Fin c × Fin 2) : ℕ := 2 * p.1 + p.2

lemma enc_injective {c : ℕ} : Function.Injective (enc (c := c)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [enc] at h
  have := b.isLt; have := b'.isLt
  ext <;> simp <;> omega

lemma enc_lt {c : ℕ} (p : Fin c × Fin 2) : enc p < 2 * c := by
  have := p.1.isLt; have := p.2.isLt; simp only [enc]; omega

/-- The algorithm of Lemma 2: compute the weak `2c`-colouring `(φ, dmin mod 2)` (`k` rounds), then
the greedy MIS of the bichromatic subgraph by its `2c` colour classes (`2c` rounds), and output
membership in it. -/
noncomputable def lemma2Alg (k c : ℕ) (G : SimpleGraph V) (φ : V → Fin c) : V → Bool :=
  weakTwo (2 * c) G (fun v => enc (parityColor k G φ v))

/-- Lemma 2 of [BHOS19] (explicit version): the algorithm `lemma2Alg k c` runs in `k + 2c` rounds
of the LOCAL model and turns every distance-`k` weak `c`-colouring into a weak 2-colouring. It is
anonymous (uses no identifiers) and needs no bound on the degree. -/
theorem lemma_2_explicit (k c : ℕ) :
    IsLocal (V := V) (k + 2 * c) (lemma2Alg k c) ∧
      ∀ (G : SimpleGraph V) (φ : V → Fin c), IsDistWeakColoring G k φ →
        IsWeakColoring G (lemma2Alg k c G φ) := by
  refine ⟨?_, fun G φ hφ => ?_⟩
  · have := (weakTwo_isLocal (V := V) (2 * c)).comp (isLocal_map (parityColor_isLocal (V := V) (C := Fin c) k) (enc (c := c)))
    rw [Nat.add_comm]; exact this
  · exact weakTwo_isWeakColoring (fun v => enc_lt _)
      ((parityColor_isWeakColoring hφ).comp enc_injective)

/-- Lemma 2 of [BHOS19]: given a distance-`k` weak `c`-colouring, a weak 2-colouring can be
computed in `O(1)` rounds (for `k, c = O(1)`; here: `k + 2c` rounds). -/
theorem lemma_2 (k c : ℕ) : ∃ R, ∃ f : SimpleGraph V → (V → Fin c) → V → Bool, IsLocal R f ∧
    ∀ G φ, IsDistWeakColoring G k φ → IsWeakColoring G (f G φ) :=
  ⟨_, _, lemma_2_explicit k c⟩

/-! ### Non-vacuity -/

/-- A proper colouring of a graph without isolated nodes is a distance-1 weak colouring. -/
lemma isDistWeakColoring_one_of_proper {G : SimpleGraph V} {φ : V → C}
    (hφ : ∀ ⦃u v⦄, G.Adj u v → φ u ≠ φ v) (hdeg : ∀ v, ∃ u, G.Adj v u) :
    IsDistWeakColoring G 1 φ :=
  isDistWeakColoring_one_iff.2 fun v => by
    obtain ⟨u, hu⟩ := hdeg v
    exact ⟨u, hu, (hφ hu).symm⟩

/-- Non-vacuity: on the path `0 - 1 - 2 - 3`, the colouring `0, 0, 1, 1` is a distance-2 weak
2-colouring which is *not* a proper colouring, and Lemma 2 applies to it. -/
example : IsDistWeakColoring (pathGraph 4) 2 (![0, 0, 1, 1] : Fin 4 → Fin 2) ∧
    IsWeakColoring (pathGraph 4) (lemma2Alg 2 2 (pathGraph 4) ![0, 0, 1, 1]) := by
  have h : IsDistWeakColoring (pathGraph 4) 2 (![0, 0, 1, 1] : Fin 4 → Fin 2) := by
    have h1 : ∀ i j : Fin 4, (pathGraph 4).Adj i j → (pathGraph 4).edist i j ≤ (2 : ℕ) := by
      intro i j hij; rw [edist_eq_one_iff_adj.2 hij]; norm_num
    have h2 : ∀ i j l : Fin 4, (pathGraph 4).Adj i j → (pathGraph 4).Adj j l →
        (pathGraph 4).edist i l ≤ (2 : ℕ) := fun i j l hij hjl =>
      edist_le_natCast_add (m := 1) (n := 1) (by rw [edist_eq_one_iff_adj.2 hij]; simp)
        (by rw [edist_eq_one_iff_adj.2 hjl]; simp)
    intro v
    fin_cases v
    · exact ⟨2, h2 0 1 2 (by simp [pathGraph_adj]) (by simp [pathGraph_adj]), by decide⟩
    · exact ⟨2, h1 _ _ (by simp [pathGraph_adj]), by decide⟩
    · exact ⟨1, h1 _ _ (by simp [pathGraph_adj]), by decide⟩
    · exact ⟨1, h2 3 2 1 (by simp [pathGraph_adj]) (by simp [pathGraph_adj]), by decide⟩
  exact ⟨h, (lemma_2_explicit 2 2).2 _ _ h⟩

end Podc.MinimalSymmetryBreaking
