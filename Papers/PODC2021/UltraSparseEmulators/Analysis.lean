import Papers.PODC2021.UltraSparseEmulators.Phase

/-!
# Analysis of Algorithm 1 across phases (Section 2.2: Lemmas 2.1–2.5, 2.7–2.9)

Elkin, Matar. *Ultra-Sparse Near-Additive Emulators.* PODC 2021 (arXiv:2106.01036v1).

We run Algorithm 1 with thresholds `δ ε i`, arbitrary degrees `dg i` and arbitrary orders
`ord i` (each containing every vertex).

* `card_edges_le` (Lemmas 2.1, 2.2 and 2.4, eqs. (2)–(4)): if `dg i ≥ 1` and `dg (i+1) = dg i ^ 2`,
  the emulator built by phases `0, …, i` has at most `dg 0 · n` edges, whatever `i`. The
  telescoping of eq. (4) does not need `P_{ℓ+1} = ∅`.
* `card_centers_succ` (Lemmas 2.1, 2.2): `|P_{i+1}| (dg i + 1) ≤ |P_i|`.
* `hierarchy`: if the last phase `ℓ` has `|P_ℓ| ≤ dg ℓ` (eq. (1)), the clusters form a
  `Hierarchy` (Lemmas 2.5, 2.7, 2.8, 2.9), so the stretch analysis of `Stretch.lean` applies.

Clusters are reconstructed from the centers: `ctr 0 v = v`, `ctr (i+1) v = par_i (ctr i v)`; `v`
is still clustered at phase `i` (`Alive i v`) iff none of `ctr 0 v, …, ctr (i-1) v` was
unclustered.
-/

namespace Podc.UltraSparseEmulators

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] (G : SimpleGraph V) (ε : ℝ) (dg : ℕ → ℝ) (ord : ℕ → List V)

/-- Shorthand for the state at the end of phase `i`. -/
noncomputable abbrev Ph (i : ℕ) : St V := run G (δ ε) dg ord i

/-- The center of the cluster of `P_i` containing `v`. -/
noncomputable def ctr : ℕ → V → V
  | 0, v => v
  | i + 1, v => (Ph G ε dg ord i).par (ctr i v)

/-- `v` belongs to a cluster of `P_i` (it has not been `U`-clustered before phase `i`). -/
def Alive (i : ℕ) (v : V) : Prop := ∀ j < i, (Ph G ε dg ord j).stat (ctr G ε dg ord j v) ≠ .U

variable {G ε dg ord}
variable (hε : 0 < ε) (hord : ∀ i x, x ∈ ord i)
include hε hord

omit [Fintype V] hord in
lemma δ_nonneg' (i : ℕ) : 0 ≤ δ ε i := by
  have := R_nonneg hε i; unfold δ; positivity

/-- The invariants at the end of phase `i`. -/
lemma spec (i : ℕ) :
    PInv G (δ ε i) (dg i) (centers G (δ ε) dg ord i) (edgesBefore G (δ ε) dg ord i) (Ph G ε dg ord i) ∧
      ∀ x, (Ph G ε dg ord i).stat x ≠ .S ∧ (Ph G ε dg ord i).stat x ≠ .N := by
  simp only [Ph]; rw [run_eq]
  exact phase_spec (δ_nonneg' hε i) _ _ (hord i)

lemma edges_mono {i j : ℕ} (hij : i ≤ j) : (Ph G ε dg ord i).E ⊆ (Ph G ε dg ord j).E := by
  induction hij with
  | refl => exact subset_refl _
  | step _ ih => exact ih.trans (spec (G := G) (dg := dg) hε hord (_ + 1)).1.sub

lemma centers_succ_subset (i : ℕ) :
    centers G (δ ε) dg ord (i + 1) ⊆ centers G (δ ε) dg ord i := by
  intro x hx
  simp only [centers, mem_filter, mem_univ, true_and] at hx
  exact (spec (G := G) (dg := dg) hε hord i).1.mem_of_stat hx (by decide)

lemma centers_anti {i j : ℕ} (hij : i ≤ j) :
    centers G (δ ε) dg ord j ⊆ centers G (δ ε) dg ord i := by
  induction hij with
  | refl => exact subset_refl _
  | step _ ih => exact (centers_succ_subset hε hord _).trans ih

omit hε hord in
lemma stat_T_of_mem_centers_succ {i : ℕ} {x : V} (hx : x ∈ centers G (δ ε) dg ord (i + 1)) :
    (Ph G ε dg ord i).stat x = .T := by
  simpa [centers] using hx

omit hε hord in
lemma card_centers_succ_eq (i : ℕ) :
    (centers G (δ ε) dg ord (i + 1)).card = (Ph G ε dg ord i).cnt .T := rfl

/-- **Lemmas 2.1 and 2.2** (counted): `|P_{i+1}| · (deg_i + 1) ≤ |P_i|`. -/
lemma card_centers_succ (i : ℕ) :
    ((centers G (δ ε) dg ord (i + 1)).card : ℝ) * (dg i + 1) ≤ (centers G (δ ε) dg ord i).card := by
  obtain ⟨hs, hend⟩ := spec (G := G) (dg := dg) hε hord i
  have h1 := card_eq_of_end hs hend
  have h2 := hs.cntT
  rw [card_centers_succ_eq, h1]
  push_cast
  have := (Nat.cast_nonneg ((Ph G ε dg ord i).cnt .U) : (0 : ℝ) ≤ _)
  nlinarith

/-- Eq. (4): phase `i` adds at most `deg_i |P_i| − deg_i² |P_{i+1}|` edges. -/
lemma card_edges_phase (hdg : ∀ i, 1 ≤ dg i) (i : ℕ) :
    ((Ph G ε dg ord i).E.card : ℝ) ≤ (edgesBefore G (δ ε) dg ord i).card +
      dg i * (centers G (δ ε) dg ord i).card -
      dg i ^ 2 * (centers G (δ ε) dg ord (i + 1)).card := by
  obtain ⟨hs, hend⟩ := spec (G := G) (dg := dg) hε hord i
  have h1 := card_eq_of_end hs hend
  have h2 := hs.cntT
  have h3 := hs.cntE
  rw [card_centers_succ_eq, h1]
  push_cast
  set u := ((Ph G ε dg ord i).cnt .U : ℝ)
  set t := ((Ph G ε dg ord i).cnt .T : ℝ)
  set j := ((Ph G ε dg ord i).cnt .J : ℝ)
  have hd := hdg i
  have hu : 0 ≤ u := Nat.cast_nonneg _
  -- `dU + J ≤ d(U+T+J) - d²T` ⟸ `(d-1)(J - dT) ≥ 0`
  nlinarith [mul_nonneg (sub_nonneg.2 hd) (sub_nonneg.2 h2)]

/-- **Lemma 2.4** (generalized): with `deg_i ≥ 1` and `deg_{i+1} = deg_i²`, after any number of
phases the emulator has at most `deg_0 · n` edges. -/
theorem card_edges_le (hdg : ∀ i, 1 ≤ dg i) (hsq : ∀ i, dg (i + 1) = dg i ^ 2) (i : ℕ) :
    ((Ph G ε dg ord i).E.card : ℝ) ≤ dg 0 * Fintype.card V := by
  have key : ∀ i, ((Ph G ε dg ord i).E.card : ℝ) ≤
      dg 0 * Fintype.card V - dg (i + 1) * (centers G (δ ε) dg ord (i + 1)).card := by
    intro i
    induction i with
    | zero =>
      have := card_edges_phase (G := G) (dg := dg) hε hord hdg 0
      simp only [edgesBefore, card_empty, Nat.cast_zero, zero_add, centers, card_univ] at this
      rw [hsq 0]; simpa [centers] using this
    | succ k ih =>
      have := card_edges_phase (G := G) (dg := dg) hε hord hdg (k + 1)
      simp only [edgesBefore] at this
      rw [hsq (k + 1)]; linarith
  have h := key i
  have : 0 ≤ dg (i + 1) * (centers G (δ ε) dg ord (i + 1)).card :=
    mul_nonneg (by linarith [hdg (i + 1)]) (Nat.cast_nonneg _)
  linarith

/-- The edges of the emulator join vertices connected in `G`. -/
lemma reach_of_mem (i : ℕ) : ∀ a b, s(a, b) ∈ (Ph G ε dg ord i).E → G.Reachable a b := by
  induction i with
  | zero =>
    intro a b h
    exact (spec (G := G) (dg := dg) hε hord 0).1.reach a b h (by simp [edgesBefore])
  | succ k ih =>
    intro a b h
    by_cases h0 : s(a, b) ∈ edgesBefore G (δ ε) dg ord (k + 1)
    · exact ih a b h0
    · exact (spec (G := G) (dg := dg) hε hord (k + 1)).1.reach a b h h0

/-! ### The cluster hierarchy -/

omit hε hord in
lemma alive_succ {i : ℕ} {v : V} : Alive G ε dg ord (i + 1) v ↔
    Alive G ε dg ord i v ∧ (Ph G ε dg ord i).stat (ctr G ε dg ord i v) ≠ .U := by
  constructor
  · intro h; exact ⟨fun j hj => h j (by omega), h i (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact h1 j hj
    · exact h2

omit hε hord in
lemma alive_anti {i j : ℕ} {v : V} (hij : j ≤ i) (h : Alive G ε dg ord i v) :
    Alive G ε dg ord j v := fun k hk => h k (by omega)

/-- At the end of a phase, a center is unclustered, a new supercluster center, or joined. -/
lemma stat_cases {i : ℕ} {c : V} (hc : c ∈ centers G (δ ε) dg ord i) :
    (Ph G ε dg ord i).stat c = .U ∨ (Ph G ε dg ord i).stat c = .T ∨
      (Ph G ε dg ord i).stat c = .J := by
  obtain ⟨hs, hend⟩ := spec (G := G) (dg := dg) hε hord i
  have h1 := hend c
  have h2 : (Ph G ε dg ord i).stat c ≠ .out := fun h => (hs.out_iff c).1 h hc
  rcases hsc : (Ph G ε dg ord i).stat c <;> simp_all

/-- The center of the `P_i`-cluster of an alive vertex is a center of `P_i`. -/
lemma alive_mem {i : ℕ} {v : V} (h : Alive G ε dg ord i v) :
    ctr G ε dg ord i v ∈ centers G (δ ε) dg ord i := by
  induction i with
  | zero => simp [centers]
  | succ i ih =>
    obtain ⟨h1, h2⟩ := alive_succ.1 h
    have hc := ih h1
    obtain ⟨hs, -⟩ := spec (G := G) (dg := dg) hε hord i
    simp only [centers, mem_filter, mem_univ, true_and, ctr]
    rcases stat_cases hε hord hc with h3 | h3 | h3
    · exact absurd h3 h2
    · rw [hs.T_par _ h3]; exact h3
    · exact (hs.J_par _ h3).1

lemma ctr_self {j : ℕ} {c : V} (hc : c ∈ centers G (δ ε) dg ord j) :
    ∀ k ≤ j, ctr G ε dg ord k c = c := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [ctr]
    rw [ih (by omega)]
    exact (spec (G := G) (dg := dg) hε hord k).1.T_par c
      (stat_T_of_mem_centers_succ (centers_anti hε hord hk hc))

lemma ctr_shift {j : ℕ} {v : V} (h : Alive G ε dg ord j v) (m : ℕ) :
    ctr G ε dg ord (j + m) (ctr G ε dg ord j v) = ctr G ε dg ord (j + m) v := by
  induction m with
  | zero => exact ctr_self hε hord (alive_mem hε hord h) j le_rfl
  | succ m ih =>
    show (Ph G ε dg ord (j + m)).par (ctr G ε dg ord (j + m) (ctr G ε dg ord j v)) =
      (Ph G ε dg ord (j + m)).par (ctr G ε dg ord (j + m) v)
    rw [ih]

/-- The level of `v`: the phase `i` in which the cluster of `v` joined `U_i`. -/
noncomputable def lev (G : SimpleGraph V) (ε : ℝ) (dg : ℕ → ℝ) (ord : ℕ → List V) (v : V) : ℕ :=
  if h : ∃ i, ¬ Alive G ε dg ord (i + 1) v then Nat.find h else 0

variable {ℓ : ℕ} (hlast : ((centers G (δ ε) dg ord ℓ).card : ℝ) ≤ dg ℓ)
include hlast

/-- Eq. (1) and its consequence `P_{ℓ+1} = ∅`: no vertex is alive after phase `ℓ`. -/
lemma not_alive_last (v : V) : ¬ Alive G ε dg ord (ℓ + 1) v := by
  intro h
  have hm := alive_mem hε hord h
  have hT := stat_T_of_mem_centers_succ hm
  exact (spec (G := G) (dg := dg) hε hord ℓ).1.noT hlast _ hT

lemma alive_iff {i : ℕ} {v : V} : Alive G ε dg ord i v ↔ i ≤ lev G ε dg ord v := by
  have hex : ∃ i, ¬ Alive G ε dg ord (i + 1) v := ⟨ℓ, not_alive_last hε hord hlast v⟩
  simp only [lev, hex, dite_true]
  constructor
  · intro h
    by_contra hlt
    exact Nat.find_spec hex (alive_anti (by omega) h)
  · intro hi
    rcases i with _ | k
    · intro j hj; omega
    · have := Nat.find_min hex (show k < Nat.find hex by omega)
      exact not_not.1 this

lemma lev_le (v : V) : lev G ε dg ord v ≤ ℓ := by
  by_contra h
  exact not_alive_last hε hord hlast v ((alive_iff hε hord hlast).2 (by omega))

lemma stat_lev (v : V) :
    (Ph G ε dg ord (lev G ε dg ord v)).stat (ctr G ε dg ord (lev G ε dg ord v) v) = .U := by
  have h1 : ¬ Alive G ε dg ord (lev G ε dg ord v + 1) v := fun h =>
    absurd ((alive_iff hε hord hlast).1 h) (by omega)
  rw [alive_succ] at h1
  by_contra h2
  exact h1 ⟨(alive_iff hε hord hlast).2 le_rfl, h2⟩

omit hlast in
lemma adj_of_mem {i : ℕ} (hi : i ≤ ℓ) {a b : V} (hab : s(a, b) ∈ (Ph G ε dg ord i).E)
    (hne : a ≠ b) : (emulator G (δ ε) dg ord ℓ).Adj a b := by
  rw [emulator, fromEdgeSet_adj]
  exact ⟨edges_mono hε hord hi hab, hne⟩

omit hlast in
/-- **Lemma 2.5.** `d_H(ctr_i v, v) ≤ R_i` for `v` in a cluster of `P_i`. -/
lemma radius_le : ∀ i, i ≤ ℓ → ∀ v, Alive G ε dg ord i v →
    HD G (emulator G (δ ε) dg ord ℓ) (ctr G ε dg ord i v) v (R ε i) := by
  intro i
  induction i with
  | zero => intro _ v _; simpa [ctr, R_zero] using HD.refl (G := G) (H := emulator G (δ ε) dg ord ℓ) v
  | succ i ih =>
    intro hi v h
    obtain ⟨h1, h2⟩ := alive_succ.1 h
    have hc := alive_mem hε hord h1
    have IH := ih (by omega) v h1
    obtain ⟨hs, -⟩ := spec (G := G) (dg := dg) hε hord i
    have hR := R_nonneg hε i
    have hδ := δ_nonneg' hε i
    rw [R_succ]
    simp only [ctr]
    rcases stat_cases hε hord hc with h3 | h3 | h3
    · exact absurd h3 h2
    · rw [hs.T_par _ h3]; exact IH.mono (by linarith)
    · obtain ⟨h4, h5, h6⟩ := hs.J_par _ h3
      have hne : (Ph G ε dg ord i).par (ctr G ε dg ord i v) ≠ ctr G ε dg ord i v := by
        intro e; rw [e, h3] at h4; cases h4
      have hadj := adj_of_mem (ℓ := ℓ) hε hord (by omega) h6 hne
      have := (HD.of_adj (G := G) hadj).mono h5.2
      exact this.trans IH (by positivity) hR

/-- The hierarchy of clusters built by Algorithm 1 (Lemmas 2.5, 2.7, 2.8, 2.9). -/
noncomputable def hierarchy :
    Hierarchy G (emulator G (δ ε) dg ord ℓ) ε ℓ where
  lev := lev G ε dg ord
  ctr := ctr G ε dg ord
  lev_le := lev_le hε hord hlast
  ctr_zero := fun _ => rfl
  radius := fun i v hi =>
    radius_le (ℓ := ℓ) hε hord i (hi.trans (lev_le hε hord hlast v)) v ((alive_iff hε hord hlast).2 hi)
  nest := by
    intro j i v hji hi
    have hv := (alive_iff hε hord hlast).2 hi
    have hvj := alive_anti hji hv
    have hc := alive_mem hε hord hvj
    have hshift : ∀ k, j ≤ k → ctr G ε dg ord k (ctr G ε dg ord j v) = ctr G ε dg ord k v := by
      intro k hk
      have := ctr_shift hε hord hvj (k - j)
      rwa [Nat.add_sub_cancel' hk] at this
    refine ⟨(alive_iff hε hord hlast).1 fun k hk => ?_, hshift i hji⟩
    by_cases hkj : k < j
    · rw [ctr_self hε hord hc k hkj.le]
      rw [stat_T_of_mem_centers_succ (centers_anti hε hord (by omega : k + 1 ≤ j) hc)]
      decide
    · rw [hshift k (by omega)]; exact hv k hk
  inter := by
    intro i v w hv hw hreach hdist
    have hU := stat_lev hε hord hlast v
    rw [hv] at hU
    have hcw := alive_mem hε hord ((alive_iff hε hord hlast).2 hw)
    have hiℓ : i ≤ ℓ := hv ▸ lev_le hε hord hlast v
    by_cases he : ctr G ε dg ord i w = ctr G ε dg ord i v
    · rw [he]; exact (HD.refl _).mono (by positivity)
    · have := (spec (G := G) (dg := dg) hε hord i).1.U_edge _ _ hU hcw he ⟨hreach, hdist⟩
      exact HD.of_adj (adj_of_mem (ℓ := ℓ) hε hord hiℓ this (Ne.symm he))
  reach := by
    intro x y h
    rw [emulator, fromEdgeSet_adj] at h
    exact reach_of_mem hε hord ℓ x y h.1

end Podc.UltraSparseEmulators
