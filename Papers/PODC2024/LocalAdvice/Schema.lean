import Papers.PODC2024.LocalAdvice.Lemma31

/-!
# The encoding schema for 3-colouring with one bit of advice (Appendix D)

`Schema G φ Δ` collects all objects that the encoding schema of Appendix D computes, with the
properties the paper requires of them:

* a ruling set `R` of the large components of `G_{2,3}` (diameter `> 4000Δ⁹`), with pairwise
  distances `≥ 2000Δ⁹` and domination radius `2000Δ⁹` (distances in `G_{2,3}`; nodes of
  different components are at distance `⊤`, so the per-component ruling sets `R_C` of the paper are
  the traces of `R`);
* for `r ∈ R` a set `Q r` of `12Δ⁶` nodes within distance `600Δ⁹` of `r`, pairwise `≥ 50Δ³` apart;
* for every candidate `v` a witness set `S v` (Lemma 31) within distance `Δ` of `v`, a node `v' v`
  with `dist(v, v' v) ≤ 20Δ³` and a path `P v 0 = v' v, …, P v Δ` inside `T_v` (nodes not in,
  not adjacent to and without a common colour-1 neighbour with `S v`), and a second witness set
  `S' v` on this path;
* a selection `sel r ∈ Q r` such that every node of colour 1 has at most one neighbour in the union
  of the selected candidate sets `K (sel r) = S (sel r) ∪ S' (sel r)`.

The advice bit (`Schema.bit`) is `1` on colour 1 and on the sets `X r` (`X_s` if the smallest
identifier `s` of `K (sel r)` has colour 2, all of `K (sel r)` if it has colour 3).

Main results: **Lemma 33** (`Schema.lemma_33`) and the facts about the advice that the decoder
uses (`Schema.zone_eq`, `Schema.X_spec`).
-/

namespace Podc.LocalAdvice

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V} {φ : V → Fin 3} {Δ : ℕ}

/-- The neighbours of `u` in the set `U`. -/
noncomputable def nbrIn (G : SimpleGraph V) (u : V) (U : Finset V) : Finset V :=
  open scoped Classical in univ.filter fun w => G.Adj u w ∧ w ∈ U

@[simp] lemma mem_nbrIn {u w : V} {U : Finset V} : w ∈ nbrIn G u U ↔ G.Adj u w ∧ w ∈ U := by
  classical
  simp [nbrIn]

/-- `z ∈ T_S`: `z` is not in `S`, not adjacent to a node of `S`, and shares no neighbour of
colour 1 with a node of `S`. -/
def InT (G : SimpleGraph V) (φ : V → Fin 3) (S : Finset V) (z : V) : Prop :=
  ∀ y ∈ S, z ≠ y ∧ ¬ G.Adj z y ∧ Disjoint (nbr0 G φ z) (nbr0 G φ y)

/-- The data of the encoding schema of Appendix D before the final selection of candidates
(see the module docstring). The paper's colours 1, 2, 3 are `0, 1, 2`. -/
structure PreSchema (G : SimpleGraph V) (φ : V → Fin 3) (Δ : ℕ) where
  /-- The ruling set (union of the ruling sets `R_C` of the large components `C`). -/
  R : Finset V
  /-- The sets `Q_r`. -/
  Q : V → Finset V
  /-- The witness sets `S_v`. -/
  S : V → Finset V
  /-- The nodes `v'`. -/
  v' : V → V
  /-- The paths `P_v` (`P v 0 = v' v`, length `Δ`). -/
  P : V → ℕ → V
  /-- The witness sets `S'_v`. -/
  S' : V → Finset V
  R_large : ∀ r ∈ R, IsLarge (H23 G φ) (4000 * Δ ^ 9) r
  R_sep : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → ((2000 * Δ ^ 9 : ℕ) : ℕ∞) ≤ (H23 G φ).edist r r'
  R_dom : ∀ u, φ u ≠ 0 → IsLarge (H23 G φ) (4000 * Δ ^ 9) u →
    ∃ r ∈ R, (H23 G φ).edist u r ≤ (2000 * Δ ^ 9 : ℕ)
  Q_card : ∀ r ∈ R, (Q r).card = 12 * Δ ^ 6
  Q_near : ∀ r ∈ R, ∀ v ∈ Q r, (H23 G φ).edist r v ≤ (600 * Δ ^ 9 : ℕ)
  Q_sep : ∀ r ∈ R, ∀ v ∈ Q r, ∀ w ∈ Q r, v ≠ w → ((50 * Δ ^ 3 : ℕ) : ℕ∞) ≤ (H23 G φ).edist v w
  S_wit : ∀ r ∈ R, ∀ v ∈ Q r, IsWitness G φ (S v)
  S_near : ∀ r ∈ R, ∀ v ∈ Q r, ∀ z ∈ S v, (H23 G φ).edist v z ≤ Δ
  v'_near : ∀ r ∈ R, ∀ v ∈ Q r, (H23 G φ).edist v (v' v) ≤ (20 * Δ ^ 3 : ℕ)
  P_zero : ∀ r ∈ R, ∀ v ∈ Q r, P v 0 = v' v
  P_adj : ∀ r ∈ R, ∀ v ∈ Q r, ∀ i < Δ, (H23 G φ).Adj (P v i) (P v (i + 1))
  P_inj : ∀ r ∈ R, ∀ v ∈ Q r, ∀ i ≤ Δ, ∀ j ≤ Δ, P v i = P v j → i = j
  P_T : ∀ r ∈ R, ∀ v ∈ Q r, ∀ i ≤ Δ, InT G φ (S v) (P v i)
  S'_wit : ∀ r ∈ R, ∀ v ∈ Q r, IsWitness G φ (S' v)
  S'_P : ∀ r ∈ R, ∀ v ∈ Q r, ∀ z ∈ S' v, ∃ i ≤ Δ, z = P v i

/-- The candidate set `S_v ∪ S'_v`. -/
def PreSchema.K {G : SimpleGraph V} {φ : V → Fin 3} {Δ : ℕ} (σ : PreSchema G φ Δ) (v : V) :
    Finset V := σ.S v ∪ σ.S' v

/-- The data of the encoding schema of Appendix D (see the module docstring), including the
selection `sel r = v_{r,C}` made with the Lovász Local Lemma. -/
structure Schema (G : SimpleGraph V) (φ : V → Fin 3) (Δ : ℕ) extends PreSchema G φ Δ where
  /-- The selected candidates `v_{r,C}`. -/
  sel : V → V
  sel_mem : ∀ r ∈ R, sel r ∈ Q r
  sel_good : ∀ u, φ u = 0 →
    (nbrIn G u (R.biUnion (fun r => S (sel r) ∪ S' (sel r)))).card ≤ 1

namespace Schema

variable (σ : Schema G φ Δ)

/-- The set of nodes of `K (sel r)` that receive bit 1: with `s` the smallest identifier in
`K (sel r)`, the one of `S, S'` containing `s` if `s` has (paper) colour 2, else all of it. -/
noncomputable def X (r : V) : Finset V :=
  if h : (σ.K (σ.sel r)).Nonempty then
    if φ ((σ.K (σ.sel r)).min' h) = 1 then
      (if (σ.K (σ.sel r)).min' h ∈ σ.S (σ.sel r) then σ.S (σ.sel r) else σ.S' (σ.sel r))
    else σ.K (σ.sel r)
  else ∅

/-- The advice bit of the encoding schema. -/
noncomputable def bit (u : V) : Bool :=
  open scoped Classical in decide (φ u = 0 ∨ ∃ r ∈ σ.R, u ∈ σ.X r)

lemma bit_eq_true {u : V} : σ.bit u = true ↔ φ u = 0 ∨ ∃ r ∈ σ.R, u ∈ σ.X r := by
  classical
  simp [bit]

lemma X_subset (r : V) : σ.X r ⊆ σ.K (σ.sel r) := by
  unfold X
  split_ifs <;> simp [PreSchema.K, Finset.subset_union_left, Finset.subset_union_right]

end Schema

/-! ### Elementary facts -/

/-- Powers of `Δ ≥ 1` used to compare the constants of the schema. -/
lemma pow_chain (hΔ : 1 ≤ Δ) :
    1 ≤ Δ ∧ Δ ≤ Δ ^ 2 ∧ Δ ^ 2 ≤ Δ ^ 3 ∧ Δ ^ 3 ≤ Δ ^ 6 ∧ Δ ^ 6 ≤ Δ ^ 8 ∧ Δ ^ 8 ≤ Δ ^ 9 := by
  refine ⟨hΔ, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using Nat.pow_le_pow_right hΔ (show 1 ≤ 2 by norm_num)
  all_goals exact Nat.pow_le_pow_right hΔ (by norm_num)

omit [Fintype V] [LinearOrder V] in
/-- Nodes reachable in `G_{2,3}` from a node of colour `≠ 1` have colour `≠ 1`. -/
lemma H23_reachable_ne_zero {a b : V} (h : (H23 G φ).Reachable a b) (ha : φ a ≠ 0) :
    φ b ≠ 0 := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ha
  | cons hadj _ ih => exact ih hadj.2.2

omit [Fintype V] [LinearOrder V] in
lemma H23_edist_ne_zero {a b : V} {n : ℕ} (h : (H23 G φ).edist a b ≤ n) (ha : φ a ≠ 0) :
    φ b ≠ 0 :=
  H23_reachable_ne_zero (SimpleGraph.reachable_of_edist_le_natCast h) ha

omit [Fintype V] [LinearOrder V] in
/-- A node of colour 1 is isolated in `G_{2,3}`, hence never in a large component. -/
lemma IsLarge.ne_zero {D : ℕ} {u : V} (h : IsLarge (H23 G φ) D u) : φ u ≠ 0 := by
  intro hu
  have key : ∀ x, (H23 G φ).Reachable u x → x = u := by
    intro x ⟨p⟩
    cases p with
    | nil => rfl
    | cons hadj _ => exact absurd hu hadj.2.1
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  rw [key x hx, key y hy, dist_self] at hxy
  omega

/-- Two nodes of a witness set are at distance `≤ 1` in `G_{2,3}`. -/
lemma IsWitness.edist_le_one {S : Finset V} (h : IsWitness G φ S) {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) : (H23 G φ).edist a b ≤ 1 := by
  rcases h with ⟨w, rfl, -⟩ | ⟨x, y, rfl, hxy, -⟩
  · simp only [mem_singleton] at ha hb; subst ha hb; simp
  · simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp [edist_eq_one_iff_adj.2 hxy, edist_eq_one_iff_adj.2 hxy.symm]

omit [Fintype V] [LinearOrder V] in
/-- Along a path `f 0, …, f k` the distance from `f 0` to `f i` is at most `i`. -/
lemma edist_path_le {H : SimpleGraph V} {f : ℕ → V} {k : ℕ} (hadj : ∀ i < k, H.Adj (f i) (f (i + 1))) :
    ∀ i ≤ k, H.edist (f 0) (f i) ≤ i := by
  intro i
  induction i with
  | zero => intro; simp
  | succ i ih =>
    intro hi
    calc H.edist (f 0) (f (i + 1)) ≤ H.edist (f 0) (f i) + 1 :=
          SimpleGraph.edist_le_add_one_of_adj (hadj i (by omega))
      _ ≤ i + 1 := by gcongr; exact ih (by omega)
      _ = ((i + 1 : ℕ) : ℕ∞) := by push_cast; rfl

/-- `Z` is connected in `H`: any two nodes of `Z` are joined by a path inside `Z`. -/
def ZConn (H : SimpleGraph V) (Z : Finset V) : Prop :=
  ∀ a ∈ Z, ∀ b ∈ Z, (restrict H (· ∈ Z)).Reachable a b

lemma IsWitness.zConn {S : Finset V} (h : IsWitness G φ S) : ZConn (H23 G φ) S := by
  intro a ha b hb
  rcases h with ⟨w, rfl, -⟩ | ⟨x, y, rfl, hxy, -⟩
  · simp only [mem_singleton] at ha hb; subst ha hb; rfl
  · simp only [mem_insert, mem_singleton] at ha hb
    have e : (restrict (H23 G φ) (· ∈ ({x, y} : Finset V))).Adj x y := ⟨hxy, by simp, by simp⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact e.reachable
    · exact e.symm.reachable
    · rfl

omit [Fintype V] [LinearOrder V] in
/-- In `G_{2,3}` the colours alternate between 2 and 3: the parity of the distance between two
connected nodes tells whether they have the same colour. -/
lemma even_dist_iff (hφ : IsGreedy G φ) {a b : V} (h : (H23 G φ).Reachable a b) (ha : φ a ≠ 0) :
    Even ((H23 G φ).dist a b) ↔ φ a = φ b := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  rw [← hp]
  clear hp h
  induction p with
  | nil => simp
  | cons hadj p ih =>
    rename_i u w z
    have hw := hadj.2.2
    have hne : φ u ≠ φ w := hφ.1 _ _ hadj.1
    rw [Walk.length_cons, Nat.even_add_one, ih hw]
    have h3 : ∀ c : Fin 3, c ≠ 0 → c = 1 ∨ c = 2 := by decide
    rcases h3 _ ha with h1 | h1 <;> rcases h3 _ hw with h2 | h2 <;>
      rcases h3 _ (H23_reachable_ne_zero p.reachable hw) with h4 | h4 <;>
      simp_all

namespace PreSchema

section Facts

variable {σ : PreSchema G φ Δ} (hΔ : 1 ≤ Δ)
include hΔ

omit hΔ in
/-- Nodes of `S'_v` lie in `T_v`. -/
lemma S'_T {r v : V} (hr : r ∈ σ.R) (hv : v ∈ σ.Q r) {z : V} (hz : z ∈ σ.S' v) :
    InT G φ (σ.S v) z := by
  obtain ⟨i, hi, rfl⟩ := σ.S'_P r hr v hv z hz
  exact σ.P_T r hr v hv i hi

omit hΔ in
/-- Nodes of `S'_v` are within distance `20Δ³ + Δ` of `v`. -/
lemma S'_near {r v : V} (hr : r ∈ σ.R) (hv : v ∈ σ.Q r) {z : V} (hz : z ∈ σ.S' v) :
    (H23 G φ).edist v z ≤ (20 * Δ ^ 3 + Δ : ℕ) := by
  obtain ⟨i, hi, rfl⟩ := σ.S'_P r hr v hv z hz
  have h1 := edist_path_le (σ.P_adj r hr v hv) i hi
  rw [σ.P_zero r hr v hv] at h1
  exact (SimpleGraph.edist_le_natCast_add (σ.v'_near r hr v hv) h1).trans
    (Nat.cast_le.2 (by omega))

omit hΔ in
/-- Candidate-set nodes are within distance `20Δ³ + Δ` of the candidate. -/
lemma K_near {r v : V} (hr : r ∈ σ.R) (hv : v ∈ σ.Q r) {z : V} (hz : z ∈ σ.K v) :
    (H23 G φ).edist v z ≤ (20 * Δ ^ 3 + Δ : ℕ) := by
  rcases mem_union.1 hz with hz | hz
  · exact (σ.S_near r hr v hv z hz).trans (Nat.cast_le.2 (by omega))
  · exact S'_near hr hv hz

/-- Candidate-set nodes of `Q_r` are within distance `700Δ⁹` of `r`. -/
lemma K_near_r {r v : V} (hr : r ∈ σ.R) (hv : v ∈ σ.Q r) {z : V} (hz : z ∈ σ.K v) :
    (H23 G φ).edist r z ≤ (700 * Δ ^ 9 : ℕ) := by
  have := pow_chain hΔ
  exact (SimpleGraph.edist_le_natCast_add (σ.Q_near r hr v hv) (K_near hr hv hz)).trans
    (Nat.cast_le.2 (by omega))

/-- The candidate sets of all pairs `(r, v)`, `v ∈ Q_r`, are pairwise disjoint. -/
lemma K_unique {r r' v v' z : V} (hr : r ∈ σ.R) (hr' : r' ∈ σ.R) (hv : v ∈ σ.Q r)
    (hv' : v' ∈ σ.Q r') (hz : z ∈ σ.K v) (hz' : z ∈ σ.K v') : r = r' ∧ v = v' := by
  have hc := pow_chain hΔ
  have hrr' : r = r' := by
    by_contra hne
    have h1 := SimpleGraph.edist_le_natCast_add (K_near_r hΔ hr hv hz)
      (by rw [edist_comm]; exact K_near_r hΔ hr' hv' hz')
    have := (σ.R_sep r hr r' hr' hne).trans h1
    norm_cast at this
    omega
  subst hrr'
  refine ⟨rfl, ?_⟩
  by_contra hne
  have h1 := SimpleGraph.edist_le_natCast_add (K_near hr hv hz)
    (by rw [edist_comm]; exact K_near hr hv' hz')
  have := (σ.Q_sep r hr v hv v' hv' hne).trans h1
  norm_cast at this
  omega

/-- Two nodes of a candidate set are within distance `30Δ³`. -/
lemma K_pair {r v : V} (hr : r ∈ σ.R) (hv : v ∈ σ.Q r) {a b : V} (ha : a ∈ σ.K v)
    (hb : b ∈ σ.K v) : (H23 G φ).edist a b ≤ (30 * Δ ^ 3 : ℕ) := by
  have hc := pow_chain hΔ
  have hS := σ.S_wit r hr v hv
  have hS' := σ.S'_wit r hr v hv
  have h1 : (1 : ℕ∞) ≤ (30 * Δ ^ 3 : ℕ) := Nat.one_le_cast.2 (by omega)
  rcases mem_union.1 ha with ha | ha <;> rcases mem_union.1 hb with hb | hb
  · exact (hS.edist_le_one ha hb).trans h1
  · have := SimpleGraph.edist_le_natCast_add
      (by rw [edist_comm]; exact σ.S_near r hr v hv a ha) (S'_near hr hv hb)
    exact this.trans (Nat.cast_le.2 (by omega))
  · have := SimpleGraph.edist_le_natCast_add
      (by rw [edist_comm]; exact S'_near hr hv ha) (σ.S_near r hr v hv b hb)
    exact this.trans (Nat.cast_le.2 (by omega))
  · exact (hS'.edist_le_one ha hb).trans h1

end Facts

end PreSchema

namespace Schema

variable (σ : Schema G φ Δ)

open PreSchema

/-- For a node of colour `≠ 1`, bit 1 means membership in some `X r`. -/
lemma bit_iff_of_ne_zero {u : V} (hu : φ u ≠ 0) : σ.bit u = true ↔ ∃ r ∈ σ.R, u ∈ σ.X r := by
  rw [bit_eq_true]; simp [hu]

/-- A node of `X r` lies in a witness set (`S` or `S'` of the selected candidate) contained in
`X r`. -/
lemma exists_witness_of_mem_X {r : V} (hr : r ∈ σ.R) {u : V} (hu : u ∈ σ.X r) :
    ∃ Y, IsWitness G φ Y ∧ u ∈ Y ∧ Y ⊆ σ.X r := by
  have hv := σ.sel_mem r hr
  have hS := σ.S_wit r hr _ hv
  have hS' := σ.S'_wit r hr _ hv
  unfold X at hu ⊢
  split_ifs at hu ⊢ with h1 h2 h3
  · exact ⟨_, hS, hu, subset_rfl⟩
  · exact ⟨_, hS', hu, subset_rfl⟩
  · rcases mem_union.1 hu with hu | hu
    · exact ⟨_, hS, hu, subset_union_left⟩
    · exact ⟨_, hS', hu, subset_union_right⟩
  · simp at hu

/-- The structure of `X r` read by the decoder: it is nonempty, and either it is connected and its
smallest identifier has (paper) colour 2, or it is disconnected and its smallest identifier has
(paper) colour 3. -/
lemma X_spec {r : V} (hr : r ∈ σ.R) :
    ∃ h : (σ.X r).Nonempty, (ZConn (H23 G φ) (σ.X r) ∧ φ ((σ.X r).min' h) = 1) ∨
      (¬ ZConn (H23 G φ) (σ.X r) ∧ φ ((σ.X r).min' h) = 2) := by
  have hv := σ.sel_mem r hr
  have hS := σ.S_wit r hr _ hv
  have hS' := σ.S'_wit r hr _ hv
  have hK : (σ.K (σ.sel r)).Nonempty := hS.nonempty.mono subset_union_left
  set s := (σ.K (σ.sel r)).min' hK with hs
  have hsK : s ∈ σ.K (σ.sel r) := min'_mem _ _
  have hsmin : ∀ y ∈ σ.K (σ.sel r), s ≤ y := fun y hy => min'_le _ _ hy
  have hcolK : ∀ z ∈ σ.K (σ.sel r), φ z ≠ 0 := by
    intro z hz
    rcases mem_union.1 hz with hz | hz
    · exact hS.color_ne_zero z hz
    · exact hS'.color_ne_zero z hz
  have hmin_eq : ∀ (Y : Finset V) (hY : Y.Nonempty), s ∈ Y → Y ⊆ σ.K (σ.sel r) →
      Y.min' hY = s := fun Y hY hsY hYK =>
    le_antisymm (min'_le _ _ hsY) (le_min' _ _ _ fun y hy => hsmin y (hYK hy))
  by_cases h1 : φ s = 1
  · -- `X r` is the witness set containing `s`
    have hX : σ.X r = if s ∈ σ.S (σ.sel r) then σ.S (σ.sel r) else σ.S' (σ.sel r) := by
      unfold X; rw [dite_eq_left hK, ← hs, ite_eq_left h1]
    have hsX : s ∈ σ.X r := by
      rw [hX]; split_ifs with h
      · exact h
      · exact (mem_union.1 hsK).resolve_left h
    have hwit : IsWitness G φ (σ.X r) := by rw [hX]; split_ifs <;> assumption
    have hne : (σ.X r).Nonempty := ⟨s, hsX⟩
    refine ⟨hne, Or.inl ⟨hwit.zConn, ?_⟩⟩
    rw [hmin_eq _ hne hsX (σ.X_subset r)]; exact h1
  · have hX : σ.X r = σ.K (σ.sel r) := by
      unfold X; rw [dite_eq_left hK, ← hs, ite_eq_right h1]
    have h2 : φ s = 2 := by
      have := hcolK s hsK
      revert h1 this; generalize φ s = c; decide +revert
    refine ⟨⟨s, hX ▸ hsK⟩, Or.inr ⟨?_, ?_⟩⟩
    · -- `S` and `S'` are not joined by an edge, so `S ∪ S'` is disconnected
      rw [hX]
      intro hconn
      obtain ⟨a, ha⟩ := hS.nonempty
      obtain ⟨b, hb⟩ := hS'.nonempty
      have hreach := hconn a (mem_union_left _ ha) b (mem_union_right _ hb)
      have key : ∀ x y, (restrict (H23 G φ) (· ∈ σ.K (σ.sel r))).Adj x y →
          (x ∈ σ.S (σ.sel r)) = (y ∈ σ.S (σ.sel r)) := by
        intro x y hxy
        apply propext
        have hx := hxy.2.1
        have hy := hxy.2.2
        constructor
        · intro hxS
          by_contra hyS
          have hyS' := (mem_union.1 hy).resolve_left hyS
          exact ((S'_T hr hv hyS') x hxS).2.1 hxy.1.1.symm
        · intro hyS
          by_contra hxS
          have hxS' := (mem_union.1 hx).resolve_left hxS
          exact ((S'_T hr hv hxS') y hyS).2.1 hxy.1.1
      have hbS : b ∈ σ.S (σ.sel r) := by
        have := hreach.apply_eq_of_forall_adj key
        rw [← this]; exact ha
      exact ((S'_T hr hv hb) b hbS).1 rfl
    · simp only [hX]; rw [hmin_eq _ _ hsK subset_rfl]; exact h2

/-- **The zone around a 1-bit.** If `w` has colour `≠ 1` and bit 1, say `w ∈ X r`, then the nodes
with bit 1 within distance `30Δ³` of `w` in `G_{2,3}` are exactly `X r`. -/
lemma zone_eq (hΔ : 1 ≤ Δ) [DecidableRel (H23 G φ).Adj] {r w : V} (hr : r ∈ σ.R)
    (hw : w ∈ σ.X r) (hw0 : φ w ≠ 0) :
    (open scoped Classical in
      univ.filter fun z => (H23 G φ).edist w z ≤ (30 * Δ ^ 3 : ℕ) ∧ σ.bit z = true) = σ.X r := by
  classical
  have hc := pow_chain hΔ
  have hv := σ.sel_mem r hr
  ext z
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hd, hb⟩
    have hz0 := H23_edist_ne_zero hd hw0
    obtain ⟨r', hr', hz⟩ := (σ.bit_iff_of_ne_zero hz0).1 hb
    by_cases hrr : r = r'
    · exact hrr ▸ hz
    · exfalso
      have h1 := K_near_r hΔ hr hv (σ.X_subset r hw)
      have h2 := K_near_r hΔ hr' (σ.sel_mem r' hr') (σ.X_subset r' hz)
      have h3 := SimpleGraph.edist_le_natCast_add (SimpleGraph.edist_le_natCast_add h1 hd)
        (by rw [edist_comm]; exact h2)
      have := (σ.R_sep r hr r' hr' hrr).trans h3
      norm_cast at this
      omega
  · intro hz
    exact ⟨K_pair hΔ hr hv (σ.X_subset r hw) (σ.X_subset r hz),
      (σ.bit_eq_true).2 (Or.inr ⟨r, hr, hz⟩)⟩

/-- **Lemma 33** of [Balliu et al., arXiv:2405.04519]. A node has colour 1 in the fixed greedy
colouring iff it has bit 1 and at most one neighbour with bit 1. -/
theorem lemma_33 (hφ : IsGreedy G φ) (v : V) :
    φ v = 0 ↔ σ.bit v = true ∧
      (nbrIn G v (open scoped Classical in univ.filter fun w => σ.bit w = true)).card ≤ 1 := by
  classical
  constructor
  · intro hv
    refine ⟨σ.bit_eq_true.2 (Or.inl hv), le_trans (card_le_card ?_) (σ.sel_good v hv)⟩
    intro w hw
    rw [mem_nbrIn, mem_filter] at hw
    obtain ⟨hvw, -, hb⟩ := hw
    have hw0 : φ w ≠ 0 := fun h => hφ.1 v w hvw (hv.trans h.symm)
    obtain ⟨r, hr, hwX⟩ := (σ.bit_iff_of_ne_zero hw0).1 hb
    rw [mem_nbrIn, mem_biUnion]
    exact ⟨hvw, r, hr, σ.X_subset r hwX⟩
  · rintro ⟨hb, hcard⟩
    by_contra hv
    obtain ⟨r, hr, hvX⟩ := (σ.bit_iff_of_ne_zero hv).1 hb
    obtain ⟨Y, hY, hvY, hYX⟩ := σ.exists_witness_of_mem_X hr hvX
    have hbit : ∀ z ∈ σ.X r, σ.bit z = true := fun z hz => σ.bit_eq_true.2 (Or.inr ⟨r, hr, hz⟩)
    have hsub0 : nbr0 G φ v ⊆ nbrIn G v (univ.filter fun w => σ.bit w = true) := by
      intro z hz
      rw [mem_nbr0] at hz
      simp [hz.1, σ.bit_eq_true, hz.2]
    rcases hY with ⟨w, rfl, -, h2⟩ | ⟨x, y, rfl, hxy, hdisj⟩
    · simp only [mem_singleton] at hvY; subst hvY
      have := card_le_card hsub0
      omega
    · obtain ⟨u0, hu0⟩ := hφ.nbr0_nonempty hv
      have hu0' := mem_nbr0.1 hu0
      -- the other node of the pair
      obtain ⟨o, hvo, ho⟩ : ∃ o, G.Adj v o ∧ o ∈ ({x, y} : Finset V) := by
        simp only [mem_insert, mem_singleton] at hvY
        rcases hvY with rfl | rfl
        · exact ⟨y, hxy.1, by simp⟩
        · exact ⟨x, hxy.1.symm, by simp⟩
      have ho0 : φ o ≠ 0 := (IsWitness.color_ne_zero (Or.inr ⟨x, y, rfl, hxy, hdisj⟩) o ho)
      have hne : o ≠ u0 := fun h => ho0 (h ▸ hu0'.2)
      have hsub : ({o, u0} : Finset V) ⊆ nbrIn G v (univ.filter fun w => σ.bit w = true) := by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · simp [hvo, hbit z (hYX ho)]
        · exact hsub0 hu0
      have := card_le_card hsub
      rw [card_pair hne] at this
      omega

end Schema

end Podc.LocalAdvice
