import Papers.PODC2013.AsyncRendezvousPoly.Meet
import Papers.PODC2013.AsyncRendezvousPoly.Bounds

/-!
# Synchronization lemmas (Lemmas 3.2–3.6)

Dieudonné, Pelc, Villain, *How to meet asynchronously at polynomial cost*, PODC 2013
(arXiv:1301.7119v2), §3.2.

Two agents `x`, `y` (`Agent`: modified label, start node, walk chosen by the adversary) execute
Algorithm RV-asynch-poly in a connected graph of size `n`. All statements are of the form "if the
agents have not met before, then by the time agent `y` completes part `Y` of its route, agent `x`
has completed part `X` of its route", i.e. an inequality between completion times `τ`. The
hypothesis "not met before" is `NoMeet E x y Ex Ey`: no meeting at a time `t` at which `x` has
completed at most `Ex` and `y` at most `Ey` edge traversals.

Instead of the paper's `n + l` we use any `N0 ≥ n` (the paper's choice is `N0 = n + l`); the
synchronization lemmas do not use `l`. Segments are `0`-indexed (Lean segment `i` is the paper's
`S_{i+1}`, Lean border `i` is the paper's `K_{i+1,i+2}`).
-/

namespace Podc.AsyncRendezvousPoly

open Traj

/-- An agent executing the algorithm: its modified label `bits`, its start node `v`, and the walk
`W` chosen by the adversary on its route. -/
structure Agent (V : Type*) where
  /-- The modified label `M(x)`. -/
  bits : List Bool
  /-- The start node. -/
  v : V
  /-- The adversary's walk. -/
  W : Walk

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {P : ℕ → ℕ}
  (E : Explorer G P)

/-- The route of agent `x`. -/
abbrev Explorer.rt (x : Agent V) : ℕ → V := E.route x.bits x.v

/-- No meeting at any time at which `x` has completed at most `Ex` and `y` at most `Ey` edge
traversals. -/
def NoMeet (x y : Agent V) (Ex Ey : ℕ) : Prop :=
  ∀ t, Meet (E.rt x) (E.rt y) x.W y.W t → t ≤ x.W.τ Ex → t ≤ y.W.τ Ey → False

variable {E}

omit [Fintype V] in
theorem NoMeet.symm {x y : Agent V} {Ex Ey : ℕ} (h : NoMeet E x y Ex Ey) : NoMeet E y x Ey Ex :=
  fun t ht h1 h2 => h t ht.symm h2 h1

omit [Fintype V] in
/-- Use of `NoMeet` with intermediate bounds. -/
theorem NoMeet.elim {x y : Agent V} {Ex Ey : ℕ} (h : NoMeet E x y Ex Ey) {t : ℝ}
    (ht : Meet (E.rt x) (E.rt y) x.W y.W t) {i j : ℕ} (h1 : t ≤ x.W.τ i) (hi : i ≤ Ex)
    (h2 : t ≤ y.W.τ j) (hj : j ≤ Ey) : False :=
  h t ht (h1.trans (x.W.τ_le hi)) (h2.trans (y.W.τ_le hj))

variable (hG : G.Connected) (hP : Monotone P)
include hG

/-! ### Specialised meeting lemmas -/

omit [Fintype V] [DecidableEq V] hG in
theorem lenK_pos (E : Explorer G P) (k : ℕ) : 1 ≤ lenK P k := by
  have := le_lenK E.P_pos k; have := lenA_pos P E.P_pos (8 * k); omega

omit [Fintype V] [DecidableEq V] hG in
/-- End of the fence `Ω(k)`. -/
theorem fence_end (E : Explorer G P) {bs : List Bool} (hbs : bs ≠ []) {k : ℕ} (hk : 1 ≤ k) (v : V) :
    fS P bs k + (2 * k - 1) * lenK P k * (2 * (E.R k v).len) = iS P bs (k + 1) := by
  rw [iS_succ P bs hbs hk, E.len_eq]; unfold lenOm lenX; ring

omit [Fintype V] [DecidableEq V] hG in
/-- End of the border after segment `i`. -/
theorem border_end (E : Explorer G P) {bs : List Bool} {k i : ℕ} (hi : i + 1 < nSeg bs k) (v : V) :
    segS P bs k i + 2 * lenAtom P (bit bs i) k +
      2 * (lenB P (4 * k) + lenA P (8 * k)) * (2 * (E.R k v).len) = segS P bs k (i + 1) := by
  rw [segS_succ_border P bs k i hi, E.len_eq]; unfold lenK lenX; ring

omit hG in
/-- (Counting against a fence.) If `y` follows its fence `Ω(k)`, `k ≥ n`, while `x` performs at most
`(2k-1)|K(k)|` edge traversals, they meet. -/
theorem count_fence {x y : Agent V} (hx : x.bits ≠ []) (hy : y.bits ≠ []) {k : ℕ} (hk1 : 1 ≤ k)
    (hkn : Fintype.card V ≤ k) {j0 : ℕ} (h1 : x.W.τ j0 ≤ y.W.τ (fS P y.bits k))
    (h2 : y.W.τ (iS P y.bits (k + 1)) ≤ x.W.τ (j0 + (2 * k - 1) * lenK P k)) :
    ∃ t, Meet (E.rt x) (E.rt y) x.W y.W t ∧ t ≤ y.W.τ (iS P y.bits (k + 1)) := by
  have hc : 1 ≤ (2 * k - 1) * lenK P k := one_le_mul (by omega) (lenK_pos E k)
  have hend := fence_end E hy hk1 y.v
  obtain ⟨t, ht, hte⟩ := meet_of_count (E.isRoute_route x.bits hx x.v) (E.covers_R hkn y.v)
    (E.rep_fence y.bits hy y.v hk1) hc h1 (by rw [hend]; exact h2)
  exact ⟨t, ht, by rwa [hend] at hte⟩

omit hG in
/-- (Counting against a border.) -/
theorem count_border {x y : Agent V} (hx : x.bits ≠ []) (hy : y.bits ≠ []) {k i : ℕ}
    (hk1 : 1 ≤ k) (hkn : Fintype.card V ≤ k) (hi : i + 1 < nSeg y.bits k) {j0 : ℕ}
    (h1 : x.W.τ j0 ≤ y.W.τ (segS P y.bits k i + 2 * lenAtom P (bit y.bits i) k))
    (h2 : y.W.τ (segS P y.bits k (i + 1)) ≤
      x.W.τ (j0 + 2 * (lenB P (4 * k) + lenA P (8 * k)))) :
    ∃ t, Meet (E.rt x) (E.rt y) x.W y.W t ∧ t ≤ y.W.τ (segS P y.bits k (i + 1)) := by
  have hc : 1 ≤ 2 * (lenB P (4 * k) + lenA P (8 * k)) := by
    have := lenA_pos P E.P_pos (8 * k); omega
  have hend := border_end E hi y.v
  obtain ⟨t, ht, hte⟩ := meet_of_count (E.isRoute_route x.bits hx x.v) (E.covers_R hkn y.v)
    (E.rep_border y.bits hy y.v hk1 hi) hc h1 (by rw [hend]; exact h2)
  exact ⟨t, ht, by rwa [hend] at hte⟩

omit [Fintype V] [DecidableEq V] hG in
/-- An atom `B(2k)` of agent `x` is a repetition of `Y'(2k)`. -/
theorem rep_atomB (E : Explorer G P) {x : Agent V} (hx : x.bits ≠ []) {k i α : ℕ} (hk1 : 1 ≤ k)
    (hi : i < nSeg x.bits k) (hb : bit x.bits i = true)
    (hα : α = segS P x.bits k i ∨ α = segS P x.bits k i + lenAtom P (bit x.bits i) k) :
    RepOcc (E.Y' (2 * k) x.v) (2 * lenA P (4 * (2 * k))) α (E.rt x) := by
  apply E.B_rep
  rcases hα with rfl | rfl
  · have := E.occ_atom1 x.bits hx x.v hk1 hi; rwa [hb] at this
  · have := E.occ_atom2 x.bits hx x.v hk1 hi; rw [hb] at this; rwa [hb]

omit [Fintype V] [DecidableEq V] hG in
theorem atomB_end {k : ℕ} (v : V) :
    2 * lenA P (4 * (2 * k)) * (2 * (E.Y' (2 * k) v).len) = lenB P (2 * k) := by
  rw [E.Y'_len]; unfold lenB lenY; ring

omit hG in
/-- (Counting against an atom `B`.) -/
theorem count_atomB {x y : Agent V} (hx : x.bits ≠ []) (hy : y.bits ≠ []) {k i α : ℕ}
    (hk1 : 1 ≤ k) (hkn : Fintype.card V ≤ 2 * k) (hi : i < nSeg y.bits k)
    (hb : bit y.bits i = true)
    (hα : α = segS P y.bits k i ∨ α = segS P y.bits k i + lenAtom P (bit y.bits i) k) {j0 : ℕ}
    (h1 : x.W.τ j0 ≤ y.W.τ α)
    (h2 : y.W.τ (α + lenB P (2 * k)) ≤ x.W.τ (j0 + 2 * lenA P (4 * (2 * k)))) :
    ∃ t, Meet (E.rt x) (E.rt y) x.W y.W t ∧ t ≤ y.W.τ (α + lenB P (2 * k)) := by
  have hc : 1 ≤ 2 * lenA P (4 * (2 * k)) := by have := lenA_pos P E.P_pos (4 * (2 * k)); omega
  have hend := atomB_end (E := E) (k := k) y.v
  obtain ⟨t, ht, hte⟩ := meet_of_count (E.isRoute_route x.bits hx x.v) (E.covers_Y' hkn y.v)
    (rep_atomB E hy hk1 hi hb hα) hc h1 (by rw [hend]; exact h2)
  exact ⟨t, ht, by rwa [hend] at hte⟩

/-- (Catching inside an atom.) If `x` keeps repeating `X(m', v_x)` while `y` follows a whole atom
of its iteration `k` (`m' ≤ 2k`, `n ≤ 2k`), they meet. -/
theorem rep_atom_R {x y : Agent V} (hy : y.bits ≠ []) {k i α : ℕ}
    (hk1 : 1 ≤ k) (hkn : Fintype.card V ≤ 2 * k) (hi : i < nSeg y.bits k)
    (hα : α = segS P y.bits k i ∨ α = segS P y.bits k i + lenAtom P (bit y.bits i) k)
    {m' β c : ℕ} (hm1 : 1 ≤ m') (hm : m' ≤ 2 * k) (hrep : RepOcc (E.R m' x.v) c β (E.rt x))
    (h1 : x.W.τ β ≤ y.W.τ α)
    (h2 : y.W.τ (α + lenAtom P (bit y.bits i) k) ≤ x.W.τ (β + c * (2 * P m'))) :
    ∃ t, Meet (E.rt x) (E.rt y) x.W y.W t ∧ t ≤ y.W.τ (α + lenAtom P (bit y.bits i) k) := by
  have hocc : Occ (E.atom (bit y.bits i) k y.v) (E.rt y) α := by
    rcases hα with rfl | rfl
    · exact E.occ_atom1 y.bits hy y.v hk1 hi
    · exact E.occ_atom2 y.bits hy y.v hk1 hi
  obtain ⟨δ, hδ⟩ : ∃ δ, OccIn (E.R m' x.v) (E.atom (bit y.bits i) k y.v) δ := by
    unfold Explorer.atom; split_ifs
    · exact E.R_in_B hG hkn hm1 hm y.v x.v
    · exact E.R_in_A hG (by omega) hm1 (by omega) y.v x.v
  have hlen := hδ.1
  rw [E.atom_len, E.len_eq] at hlen
  have hT : 1 ≤ (E.R m' x.v).len := by rw [E.len_eq]; exact E.P_pos m'
  obtain ⟨t, ht, hte⟩ := meet_of_rep hT (hδ.occ hocc) hrep
    (h1.trans (y.W.τ_le (by omega)))
    (by rw [E.len_eq]; exact (y.W.τ_le (by omega)).trans h2)
  refine ⟨t, ht.symm, hte.2.trans (y.W.τ_le ?_)⟩
  rw [E.len_eq]; omega

/-- (Catching inside an atom `A`.) If `x` keeps repeating `Y'(m', v_x)` while `y` follows a whole
atom `A(4k)` (`m' ≤ 4k`, `n ≤ 4k`), they meet. -/
theorem rep_atomA_Y' {x y : Agent V} (hy : y.bits ≠ []) {k i α : ℕ}
    (hk1 : 1 ≤ k) (hkn : Fintype.card V ≤ 4 * k) (hi : i < nSeg y.bits k)
    (hb : bit y.bits i = false)
    (hα : α = segS P y.bits k i ∨ α = segS P y.bits k i + lenAtom P (bit y.bits i) k)
    {m' β c : ℕ} (hm1 : 1 ≤ m') (hm : m' ≤ 4 * k) (hrep : RepOcc (E.Y' m' x.v) c β (E.rt x))
    (h1 : x.W.τ β ≤ y.W.τ α)
    (h2 : y.W.τ (α + lenA P (4 * k)) ≤ x.W.τ (β + c * (2 * lenY' P m'))) :
    ∃ t, Meet (E.rt x) (E.rt y) x.W y.W t ∧ t ≤ y.W.τ (α + lenA P (4 * k)) := by
  have hocc : Occ (E.A (4 * k) y.v) (E.rt y) α := by
    rcases hα with rfl | rfl
    · have := E.occ_atom1 y.bits hy y.v hk1 hi; rwa [hb] at this
    · have := E.occ_atom2 y.bits hy y.v hk1 hi; rw [hb] at this ⊢; exact this
  obtain ⟨δ, hδ⟩ := E.Y'_in_A hG hkn hm1 hm y.v x.v
  have hlen := hδ.1
  rw [E.A_len, E.Y'_len] at hlen
  have hT : 1 ≤ (E.Y' m' x.v).len := by
    rw [E.Y'_len]; unfold lenY'; have := E.P_pos m'; omega
  obtain ⟨t, ht, hte⟩ := meet_of_rep hT (hδ.occ hocc) hrep
    (h1.trans (y.W.τ_le (by omega)))
    (by rw [E.Y'_len]; exact (y.W.τ_le (by omega)).trans h2)
  refine ⟨t, ht.symm, hte.2.trans (y.W.τ_le ?_)⟩
  rw [E.Y'_len]; omega

omit [Fintype V] [DecidableEq V] hG in
/-- A segment of two atoms `B(2k)` is a repetition of `Y'(2k)`. -/
theorem rep_segB (E : Explorer G P) {x : Agent V} (hx : x.bits ≠ []) {k i : ℕ} (hk1 : 1 ≤ k)
    (hi : i < nSeg x.bits k) (hb : bit x.bits i = true) :
    RepOcc (E.Y' (2 * k) x.v) (2 * lenA P (4 * (2 * k)) + 2 * lenA P (4 * (2 * k)))
      (segS P x.bits k i) (E.rt x) := by
  apply RepOcc.append (rep_atomB E hx hk1 hi hb (Or.inl rfl))
  have := rep_atomB E hx hk1 hi hb (Or.inr rfl)
  rw [hb] at this; simp only [lenAtom, ite_true] at this
  rw [atomB_end]; exact this

/-! ### Lemma 3.2 -/

include hP

/-- **Lemma 3.2** of [DPV13] (with `N0 ≥ n` for the paper's `n + l`). If the agents have not met
before, then by the time `y` completes its `(N0 + i)`-th fence, `x` has completed its `(i+1)`-th
piece (first component), and by the time `y` completes its `(N0 + i + 1)`-th piece, `x` has
completed its `(i+1)`-th fence (second component, used in the induction). -/
theorem lemma_3_2 {x y : Agent V} (hx : x.bits ≠ []) (hy : y.bits ≠ []) {N0 : ℕ}
    (hN0 : Fintype.card V ≤ N0) {Ex Ey : ℕ} (hno : NoMeet E x y Ex Ey) (i : ℕ) :
    (fS P x.bits (i + 1) ≤ Ex → iS P y.bits (N0 + i + 1) ≤ Ey →
      x.W.τ (fS P x.bits (i + 1)) ≤ y.W.τ (iS P y.bits (N0 + i + 1))) ∧
    (iS P x.bits (i + 2) ≤ Ex → fS P y.bits (N0 + i + 1) ≤ Ey →
      x.W.τ (iS P x.bits (i + 2)) ≤ y.W.τ (fS P y.bits (N0 + i + 1))) := by
  have hP1 := E.P_pos
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 hG.nonempty
  -- part (a) from the start of piece `i+1`
  have partA : ∀ i, x.W.τ (iS P x.bits (i + 1)) ≤ y.W.τ (fS P y.bits (N0 + i)) →
      fS P x.bits (i + 1) ≤ Ex → iS P y.bits (N0 + i + 1) ≤ Ey →
      x.W.τ (fS P x.bits (i + 1)) ≤ y.W.τ (iS P y.bits (N0 + i + 1)) := by
    intro i hstart hEx hEy
    by_contra hlt; rw [not_le] at hlt
    have hpiece := fS_le_piece x.bits hP hP1 hx (show 1 ≤ i + 1 by omega)
    have hK := lenK_mono hP (show i + 1 ≤ N0 + i by omega)
    have hc : (2 * (i + 1) - 1) * lenK P (i + 1) ≤ (2 * (N0 + i) - 1) * lenK P (N0 + i) :=
      Nat.mul_le_mul (by omega) hK
    obtain ⟨t, ht, hte⟩ := count_fence hx hy (k := N0 + i) (by omega) (by omega) hstart
      (hlt.le.trans (x.W.τ_le (by omega)))
    exact hno.elim ht ((hte.trans hlt.le)) hEx hte hEy
  -- part (b) from part (a)
  have partB : ∀ i, x.W.τ (fS P x.bits (i + 1)) ≤ y.W.τ (iS P y.bits (N0 + i + 1)) →
      iS P x.bits (i + 2) ≤ Ex → fS P y.bits (N0 + i + 1) ≤ Ey →
      x.W.τ (iS P x.bits (i + 2)) ≤ y.W.τ (fS P y.bits (N0 + i + 1)) := by
    intro i ha hEx hEy
    by_contra hlt; rw [not_le] at hlt
    have hfirst := iS_lt_fS y.bits hP1 hy (show 1 ≤ N0 + i + 1 by omega)
    have hend := fence_end E hx (show 1 ≤ i + 1 by omega) x.v
    rw [E.len_eq] at hend
    obtain ⟨t, ht, hte⟩ := rep_atom_R hG hy (k := N0 + i + 1) (i := 0)
      (α := segS P y.bits (N0 + i + 1) 0) (by omega) (by omega) (nSeg_pos _ hy (by omega))
      (Or.inl rfl) (m' := i + 1) (show 1 ≤ i + 1 by omega) (by omega)
      (E.rep_fence x.bits hx x.v (show 1 ≤ i + 1 by omega)) (by rw [segS_zero]; exact ha)
      (by rw [hend, show i + 1 + 1 = i + 2 by ring, segS_zero]
          exact (y.W.τ_le hfirst.le).trans hlt.le)
    rw [segS_zero] at hte
    have hte' := hte.trans (y.W.τ_le hfirst.le)
    exact hno.elim ht (hte'.trans hlt.le) hEx hte' hEy
  induction i with
  | zero =>
    have ha := partA 0 (by
      simp only [zero_add, iS, Nat.sub_self, Finset.range_zero, Finset.sum_empty, x.W.τ_zero]
      exact y.W.τ_nonneg _)
    exact ⟨ha, fun h1 h2 => partB 0 (ha (le_trans (fS_lt_iS_succ x.bits hP1 hx le_rfl).le h1)
      (le_trans (iS_le_fS y.bits hP1 hy (by omega)) h2)) h1 h2⟩
  | succ i ih =>
    have ha : fS P x.bits (i + 1 + 1) ≤ Ex → iS P y.bits (N0 + (i + 1) + 1) ≤ Ey →
        x.W.τ (fS P x.bits (i + 1 + 1)) ≤ y.W.τ (iS P y.bits (N0 + (i + 1) + 1)) := by
      intro h1 h2
      refine partA (i + 1) ?_ h1 h2
      have := ih.2 (le_trans (iS_le_fS x.bits hP1 hx (by omega)) h1)
        (le_trans (fS_lt_iS_succ y.bits hP1 hy (by omega)).le h2)
      rwa [show i + 2 = i + 1 + 1 by ring, show N0 + i + 1 = N0 + (i + 1) by ring] at this
    refine ⟨ha, fun h1 h2 => partB (i + 1) (ha ?_ ?_) h1 h2⟩
    · exact le_trans (fS_lt_iS_succ x.bits hP1 hx (by omega)).le h1
    · exact le_trans (iS_le_fS y.bits hP1 hy (by omega)) h2

end Podc.AsyncRendezvousPoly
