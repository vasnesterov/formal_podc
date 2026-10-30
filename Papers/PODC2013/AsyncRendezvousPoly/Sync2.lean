import Papers.PODC2013.AsyncRendezvousPoly.Sync

/-!
# Synchronization lemmas 3.3–3.6 and the meeting on the differing bit

Dieudonné, Pelc, Villain, *How to meet asynchronously at polynomial cost*, PODC 2013
(arXiv:1301.7119v2), §3.2.

Throughout, `y` is the agent that first completes its `(2 N0)`-th fence (the paper's `b`) and `x`
is the other agent (the paper's `a`); `N0 ≥ n` stands for the paper's `n + l`, and `N = 2 N0 + 1`.
Positions in the route: `segS k i` = start of segment `i` (0-indexed) of iteration `k`,
`segS k i + lenAtom` = end of its first atom, `segS k i + 2 lenAtom` = end of the segment (= start
of the following border/fence), `segS k (i+1)` = end of the border, `fS k` = start of the fence
`Ω(k)`, `iS (k+1)` = end of `Ω(k)`. The last atom `M` of the `j`-th piece starts at
`lastA j = fS j - lenAtom`.
-/

namespace Podc.AsyncRendezvousPoly

open Traj

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {P : ℕ → ℕ}
  {E : Explorer G P}

/-- Start of the last atom `M` of the `j`-th piece. -/
def lastA (P : ℕ → ℕ) (bs : List Bool) (j : ℕ) : ℕ :=
  segS P bs j (nSeg bs j - 1) + lenAtom P (bit bs (nSeg bs j - 1)) j

theorem lastA_add (P : ℕ → ℕ) (bs : List Bool) (j : ℕ) :
    lastA P bs j + lenAtom P (bit bs (nSeg bs j - 1)) j = fS P bs j := by
  unfold lastA fS; ring

variable (hG : G.Connected) (hP : Monotone P)
include hG hP

/-- **Lemma 3.3** of [DPV13]. Let `y` be the first agent to complete its `(2 N0)`-th fence. If the
agents have not met before, then during the time segment in which `y` follows its `(2 N0)`-th
fence, `x` follows a trajectory included in `M Ω_x(j) N` for some `N0 + 1 ≤ j ≤ 2 N0` (`M` = last
atom of its `j`-th piece, `N` = first atom of its `(j+1)`-th piece): `x` has started `M` when `y`
starts the fence, and has not completed `N` when `y` completes the fence. -/
theorem lemma_3_3 {x y : Agent V} (hx : x.bits ≠ []) (hy : y.bits ≠ []) {N0 : ℕ}
    (hN0 : Fintype.card V ≤ N0)
    (hfirst : y.W.τ (iS P y.bits (2 * N0 + 1)) ≤ x.W.τ (iS P x.bits (2 * N0 + 1)))
    {Ex Ey : ℕ} (hno : NoMeet E x y Ex Ey) (hEx : iS P x.bits (2 * N0 + 1) ≤ Ex)
    (hEy : iS P y.bits (2 * N0 + 1) ≤ Ey) :
    ∃ j, N0 + 1 ≤ j ∧ j ≤ 2 * N0 ∧
      x.W.τ (lastA P x.bits j) ≤ y.W.τ (fS P y.bits (2 * N0)) ∧
      y.W.τ (iS P y.bits (2 * N0 + 1)) ≤
        x.W.τ (iS P x.bits (j + 1) + lenAtom P (bit x.bits 0) (j + 1)) := by
  classical
  have hP1 := E.P_pos
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 hG.nonempty
  have hN1 : 1 ≤ N0 := hn.trans hN0
  set s := y.W.τ (fS P y.bits (2 * N0)) with hs
  set e := y.W.τ (iS P y.bits (2 * N0 + 1)) with he
  have hse : s ≤ e := y.W.τ_le (fS_lt_iS_succ y.bits hP1 hy (by omega)).le
  have L32 := lemma_3_2 hG hP hx hy hN0 hno
  have hxN : ∀ k, 1 ≤ k → k ≤ 2 * N0 → fS P x.bits k ≤ iS P x.bits (2 * N0 + 1) := fun k hk1 hk2 =>
    (fS_lt_iS_succ x.bits hP1 hx hk1).le.trans (iS_mono P x.bits (by omega))
  -- (ii) by the end of `Ω_y(2 N0)`, `x` has completed its `(N0+1)`-th piece
  have hA1 : x.W.τ (fS P x.bits (N0 + 1)) ≤ e := by
    have := (L32 N0).1 ((hxN (N0 + 1) (by omega) (by omega)).trans hEx)
      (by rw [show N0 + N0 + 1 = 2 * N0 + 1 by ring]; exact hEy)
    rwa [show N0 + N0 + 1 = 2 * N0 + 1 by ring] at this
  -- (iv) `x` cannot follow an entire atom of an iteration `k ≥ N0` during `Ω_y(2 N0)`
  have hiv : ∀ k i α, N0 ≤ k → i < nSeg x.bits k →
      (α = segS P x.bits k i ∨ α = segS P x.bits k i + lenAtom P (bit x.bits i) k) →
      s ≤ x.W.τ α → x.W.τ (α + lenAtom P (bit x.bits i) k) ≤ e → False := by
    intro k i α hk hi hα h1 h2
    have hend := fence_end E hy (show 1 ≤ 2 * N0 by omega) y.v
    rw [E.len_eq] at hend
    obtain ⟨t, ht, hte⟩ := rep_atom_R hG (x := y) (y := x) hx (k := k) (by omega) (by omega) hi hα
      (m' := 2 * N0) (by omega) (by omega) (E.rep_fence y.bits hy y.v (by omega)) h1
      (by rw [hend]; exact h2)
    exact hno.symm.elim ht (hte.trans h2) hEy ((hte.trans h2).trans hfirst) hEx
  -- (v) `x` cannot stay inside one piece `T_x(k)`, `k ≤ 2 N0`, during `Ω_y(2 N0)`
  have hv : ∀ k, 1 ≤ k → k ≤ 2 * N0 → x.W.τ (iS P x.bits k) ≤ s →
      e ≤ x.W.τ (fS P x.bits k) → False := by
    intro k hk1 hk2 h1 h2
    have hpiece := fS_le_piece x.bits hP hP1 hx hk1
    have hc : (2 * k - 1) * lenK P k ≤ (2 * (2 * N0) - 1) * lenK P (2 * N0) :=
      Nat.mul_le_mul (by omega) (lenK_mono hP hk2)
    obtain ⟨t, ht, hte⟩ := count_fence hx hy (k := 2 * N0) (by omega) (by omega) h1
      (h2.trans (x.W.τ_le (by omega)))
    exact hno.elim ht (hte.trans hfirst) hEx hte hEy
  set j := Nat.findGreatest (fun k => x.W.τ (fS P x.bits k) ≤ e) (2 * N0) with hjdef
  have hj1 : N0 + 1 ≤ j := Nat.le_findGreatest (by omega) hA1
  have hj2 : j ≤ 2 * N0 := Nat.findGreatest_le _
  have hjspec : x.W.τ (fS P x.bits j) ≤ e :=
    Nat.findGreatest_spec (P := fun k => x.W.τ (fS P x.bits k) ≤ e) (m := N0 + 1) (by omega) hA1
  have hjnext : e < x.W.τ (fS P x.bits (j + 1)) := by
    by_cases h : j + 1 ≤ 2 * N0
    · exact not_le.1 (Nat.findGreatest_is_greatest (Nat.lt_succ_self j) h)
    · have hj : j = 2 * N0 := by omega
      rw [hj]
      exact hfirst.trans_lt (x.W.τ_lt ((Nat.le_add_right _ _).trans_lt
        (iS_lt_fS x.bits hP1 hx (by omega))))
  refine ⟨j, hj1, hj2, ?_, ?_⟩
  · by_contra h
    rw [not_le] at h
    have hm := nSeg_pos x.bits hx (show 1 ≤ j by omega)
    exact hiv j (nSeg x.bits j - 1) (lastA P x.bits j) (by omega) (by omega) (Or.inr rfl) h.le
      (by rw [lastA_add]; exact hjspec)
  · by_contra h
    rw [not_le] at h
    by_cases hs' : s ≤ x.W.τ (iS P x.bits (j + 1))
    · exact hiv (j + 1) 0 (iS P x.bits (j + 1)) (by omega) (nSeg_pos x.bits hx (by omega))
        (Or.inl (segS_zero P x.bits _).symm) hs' h.le
    · rw [not_le] at hs'
      by_cases hj' : j + 1 ≤ 2 * N0
      · exact hv (j + 1) (by omega) hj' hs'.le hjnext.le
      · have hj : j + 1 = 2 * N0 + 1 := by omega
        rw [hj] at hs'
        linarith

omit hG in
/-- **Lemma 3.4** of [DPV13]. In the situation of Lemma 3.3, by the time `y` completes its
`(2 N0)`-th fence, `x` has completed the last atom `M` of its `j`-th piece. -/
theorem lemma_3_4 {x y : Agent V} (hx : x.bits ≠ []) (hy : y.bits ≠ []) {N0 : ℕ}
    (hN0 : Fintype.card V ≤ N0)
    (hfirst : y.W.τ (iS P y.bits (2 * N0 + 1)) ≤ x.W.τ (iS P x.bits (2 * N0 + 1)))
    {Ex Ey : ℕ} (hno : NoMeet E x y Ex Ey) (hEx : iS P x.bits (2 * N0 + 1) ≤ Ex)
    (hEy : iS P y.bits (2 * N0 + 1) ≤ Ey) {j : ℕ} (hj1 : N0 + 1 ≤ j) (hj2 : j ≤ 2 * N0)
    (hM : x.W.τ (lastA P x.bits j) ≤ y.W.τ (fS P y.bits (2 * N0))) :
    x.W.τ (fS P x.bits j) ≤ y.W.τ (iS P y.bits (2 * N0 + 1)) := by
  have hP1 := E.P_pos
  by_contra h
  rw [not_le] at h
  have hA : 2 * lenAtom P (bit x.bits (nSeg x.bits j - 1)) j ≤ lenK P j :=
    (two_lenAtom_le_lenK hP _ j).trans (le_lenK hP1 j)
  have hK := lenK_mono hP hj2
  have hc : lenK P (2 * N0) ≤ (2 * (2 * N0) - 1) * lenK P (2 * N0) :=
    Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨t, ht, hte⟩ := count_fence hx hy (k := 2 * N0) (by omega) (by omega) hM
    (h.le.trans (x.W.τ_le (by rw [← lastA_add]; omega)))
  exact hno.elim ht (hte.trans hfirst) hEx hte hEy

omit hP in
/-- **Lemma 3.5** of [DPV13]. In the situation of Lemma 3.3, by the time `y` completes the first
atom of its segment `S_1(2 N0 + 1)`, `x` has completed its `j`-th fence. -/
theorem lemma_3_5 {x y : Agent V} (hx : x.bits ≠ []) (hy : y.bits ≠ []) {N0 : ℕ}
    (hN0 : Fintype.card V ≤ N0) {Ex Ey : ℕ} (hno : NoMeet E x y Ex Ey)
    (hEx : iS P x.bits (2 * N0 + 1) ≤ Ex) (hEy : fS P y.bits (2 * N0 + 1) ≤ Ey) {j : ℕ}
    (hj1 : N0 + 1 ≤ j) (hj2 : j ≤ 2 * N0)
    (h34 : x.W.τ (fS P x.bits j) ≤ y.W.τ (iS P y.bits (2 * N0 + 1))) :
    x.W.τ (iS P x.bits (j + 1)) ≤
      y.W.τ (iS P y.bits (2 * N0 + 1) + lenAtom P (bit y.bits 0) (2 * N0 + 1)) := by
  have hP1 := E.P_pos
  by_contra h
  rw [not_le] at h
  have hend := fence_end E hx (show 1 ≤ j by omega) x.v
  rw [E.len_eq] at hend
  obtain ⟨t, ht, hte⟩ := rep_atom_R hG hy (x := x) (y := y) (k := 2 * N0 + 1) (i := 0)
    (α := segS P y.bits (2 * N0 + 1) 0) (by omega) (by omega)
    (nSeg_pos y.bits hy (by omega)) (Or.inl rfl) (m' := j) (by omega) (by omega)
    (E.rep_fence x.bits hx x.v (by omega)) (by rw [segS_zero]; exact h34)
    (by rw [hend, segS_zero]; exact h.le)
  rw [segS_zero] at hte
  exact hno.elim ht ((hte.trans h.le).trans (x.W.τ_le (iS_mono P x.bits (by omega)))) hEx
    (hte.trans (y.W.τ_le (iS_lt_fS y.bits hP1 hy (by omega)).le)) hEy

/-- **Lemma 3.6** of [DPV13]. In the situation of Lemmas 3.3–3.5 (with `x` in iteration
`j + 1` and `y` in iteration `N = 2 N0 + 1`), if the agents do not meet before the first of them
completes its `N`-th piece, then for every segment index `i` (0-indexed) for which the objects
exist:
* Property 1: `x` completes `S_i(j+1)` before `y` completes the border `K_{i,i+1}(N)`;
* Property 2: `y` completes `S_i(N)` before `x` completes `K_{i,i+1}(j+1)`;
* Property 3: `x` completes `K_{i,i+1}(j+1)` before `y` completes the first atom of `S_{i+1}(N)`;
* Property 4: `y` completes `K_{i,i+1}(N)` before `x` completes the first atom of `S_{i+1}(j+1)`.
-/
theorem lemma_3_6 {x y : Agent V} (hx : x.bits ≠ []) (hy : y.bits ≠ []) {N0 : ℕ}
    (hN0 : Fintype.card V ≤ N0)
    (hno : NoMeet E x y (fS P x.bits (2 * N0 + 1)) (fS P y.bits (2 * N0 + 1))) {j : ℕ}
    (hj1 : N0 + 1 ≤ j) (hj2 : j ≤ 2 * N0)
    (h33 : y.W.τ (iS P y.bits (2 * N0 + 1)) ≤
      x.W.τ (iS P x.bits (j + 1) + lenAtom P (bit x.bits 0) (j + 1)))
    (h35 : x.W.τ (iS P x.bits (j + 1)) ≤
      y.W.τ (iS P y.bits (2 * N0 + 1) + lenAtom P (bit y.bits 0) (2 * N0 + 1))) :
    ∀ i, i + 1 < nSeg x.bits (j + 1) → i + 1 < nSeg y.bits (2 * N0 + 1) →
      x.W.τ (segS P x.bits (j + 1) i + 2 * lenAtom P (bit x.bits i) (j + 1)) <
        y.W.τ (segS P y.bits (2 * N0 + 1) (i + 1)) ∧
      y.W.τ (segS P y.bits (2 * N0 + 1) i + 2 * lenAtom P (bit y.bits i) (2 * N0 + 1)) <
        x.W.τ (segS P x.bits (j + 1) (i + 1)) ∧
      x.W.τ (segS P x.bits (j + 1) (i + 1)) <
        y.W.τ (segS P y.bits (2 * N0 + 1) (i + 1) +
          lenAtom P (bit y.bits (i + 1)) (2 * N0 + 1)) ∧
      y.W.τ (segS P y.bits (2 * N0 + 1) (i + 1)) <
        x.W.τ (segS P x.bits (j + 1) (i + 1) + lenAtom P (bit x.bits (i + 1)) (j + 1)) := by
  have hP1 := E.P_pos
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 hG.nonempty
  set ka := j + 1 with hka
  set kb := 2 * N0 + 1 with hkb
  have hfx : fS P x.bits ka ≤ fS P x.bits kb := fS_mono x.bits hP1 hx (by omega) (by omega)
  -- the step: from the lower bounds `Lx`, `Ly` for level `i`, all four properties at level `i`
  have step : ∀ i, i + 1 < nSeg x.bits ka → i + 1 < nSeg y.bits kb →
      x.W.τ (segS P x.bits ka i) ≤
        y.W.τ (segS P y.bits kb i + 2 * lenAtom P (bit y.bits i) kb) →
      y.W.τ (segS P y.bits kb i) ≤
        x.W.τ (segS P x.bits ka i + 2 * lenAtom P (bit x.bits i) ka) →
      x.W.τ (segS P x.bits ka i + 2 * lenAtom P (bit x.bits i) ka) <
        y.W.τ (segS P y.bits kb (i + 1)) ∧
      y.W.τ (segS P y.bits kb i + 2 * lenAtom P (bit y.bits i) kb) <
        x.W.τ (segS P x.bits ka (i + 1)) ∧
      x.W.τ (segS P x.bits ka (i + 1)) <
        y.W.τ (segS P y.bits kb (i + 1) + lenAtom P (bit y.bits (i + 1)) kb) ∧
      y.W.τ (segS P y.bits kb (i + 1)) <
        x.W.τ (segS P x.bits ka (i + 1) + lenAtom P (bit x.bits (i + 1)) ka) := by
    intro i hix hiy Lx Ly
    have hxE : ∀ q, q < nSeg x.bits ka → segS P x.bits ka q + 2 * lenAtom P (bit x.bits q) ka ≤
        fS P x.bits kb := fun q hq => (segE_le_fS P x.bits ka q hq).trans hfx
    have hyE : ∀ q, q < nSeg y.bits kb → segS P y.bits kb q + 2 * lenAtom P (bit y.bits q) kb ≤
        fS P y.bits kb := fun q hq => segE_le_fS P y.bits kb q hq
    -- Property 1
    have p1 : x.W.τ (segS P x.bits ka i + 2 * lenAtom P (bit x.bits i) ka) <
        y.W.τ (segS P y.bits kb (i + 1)) := by
      by_contra h; rw [not_lt] at h
      have hA := two_lenAtom_le_of_le hP (bit x.bits i) (show ka ≤ 2 * kb by omega)
      obtain ⟨t, ht, hte⟩ := count_border hx hy (k := kb) (i := i) (by omega) (by omega) hiy Lx
        (h.trans (x.W.τ_le (by omega)))
      exact hno.elim ht (hte.trans h) (hxE i (by omega)) hte
        ((le_add_right le_rfl).trans (hyE (i + 1) hiy))
    -- Property 2
    have p2 : y.W.τ (segS P y.bits kb i + 2 * lenAtom P (bit y.bits i) kb) <
        x.W.τ (segS P x.bits ka (i + 1)) := by
      by_contra h; rw [not_lt] at h
      have hA := two_lenAtom_le_of_le hP (bit y.bits i) (show kb ≤ 2 * ka by omega)
      obtain ⟨t, ht, hte⟩ := count_border hy hx (x := y) (y := x) (k := ka) (i := i) (by omega)
        (by omega) hix Ly (h.trans (y.W.τ_le (by omega)))
      exact hno.symm.elim ht (hte.trans h) (hyE i (by omega)) hte
        ((le_add_right le_rfl).trans (hxE (i + 1) hix))
    -- Property 3
    have p3 : x.W.τ (segS P x.bits ka (i + 1)) <
        y.W.τ (segS P y.bits kb (i + 1) + lenAtom P (bit y.bits (i + 1)) kb) := by
      by_contra h; rw [not_lt] at h
      have hb := border_end E hix x.v
      rw [E.len_eq] at hb
      obtain ⟨t, ht, hte⟩ := rep_atom_R hG hy (x := x) (y := y) (k := kb) (i := i + 1)
        (α := segS P y.bits kb (i + 1)) (by omega) (by omega) hiy (Or.inl rfl) (m' := ka)
        (by omega) (by omega) (E.rep_border x.bits hx x.v (by omega) hix) p1.le
        (by rw [hb]; exact h)
      exact hno.elim ht (hte.trans h) ((le_add_right le_rfl).trans (hxE (i + 1) hix)) hte
        ((Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by omega)) _).trans (hyE (i + 1) hiy))
    -- Property 4
    have p4 : y.W.τ (segS P y.bits kb (i + 1)) <
        x.W.τ (segS P x.bits ka (i + 1) + lenAtom P (bit x.bits (i + 1)) ka) := by
      by_contra h; rw [not_lt] at h
      have hb := border_end E hiy y.v
      rw [E.len_eq] at hb
      obtain ⟨t, ht, hte⟩ := rep_atom_R hG hx (x := y) (y := x) (k := ka) (i := i + 1)
        (α := segS P x.bits ka (i + 1)) (by omega) (by omega) hix (Or.inl rfl) (m' := kb)
        (by omega) (by omega) (E.rep_border y.bits hy y.v (by omega) hiy) p2.le
        (by rw [hb]; exact h)
      exact hno.symm.elim ht (hte.trans h) ((le_add_right le_rfl).trans (hyE (i + 1) hiy)) hte
        ((Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by omega)) _).trans (hxE (i + 1) hix))
    exact ⟨p1, p2, p3, p4⟩
  intro i
  induction i with
  | zero =>
    intro hix hiy
    refine step 0 hix hiy ?_ ?_
    · rw [segS_zero]
      exact h35.trans (y.W.τ_le (by rw [segS_zero]; omega))
    · rw [segS_zero]
      exact h33.trans (x.W.τ_le (by rw [segS_zero]; omega))
  | succ i ih =>
    intro hix hiy
    obtain ⟨-, -, p3, p4⟩ := ih (by omega) (by omega)
    exact step (i + 1) hix hiy (p3.le.trans (y.W.τ_le (by omega)))
      (p4.le.trans (x.W.τ_le (by omega)))

/-- **The meeting on the differing bit** (end of the proof of Theorem 3.1). If agent `x` processes
bit `1` and agent `y` bit `0` in their segments `d` of iterations `kx`, `ky` (`n ≤ kx ≤ 2 ky`,
`n ≤ ky ≤ 2 kx`), and each starts its segment before the other completes the first atom of its
own segment, then they meet before either completes its segment. -/
theorem meet_of_diff_bits {x y : Agent V} (hx : x.bits ≠ []) (hy : y.bits ≠ [])
    {kx ky d : ℕ} (hkx1 : 1 ≤ kx) (hky1 : 1 ≤ ky)
    (hny : Fintype.card V ≤ ky) (hxy : kx ≤ 2 * ky) (hyx : ky ≤ 2 * kx)
    (hdx : d < nSeg x.bits kx) (hdy : d < nSeg y.bits ky)
    (hbx : bit x.bits d = true) (hby : bit y.bits d = false)
    (h3 : x.W.τ (segS P x.bits kx d) < y.W.τ (segS P y.bits ky d + lenAtom P (bit y.bits d) ky))
    (h4 : y.W.τ (segS P y.bits ky d) < x.W.τ (segS P x.bits kx d + lenAtom P (bit x.bits d) kx)) :
    ∃ t, Meet (E.rt x) (E.rt y) x.W y.W t ∧
      t ≤ x.W.τ (segS P x.bits kx d + 2 * lenAtom P (bit x.bits d) kx) ∧
      t ≤ y.W.τ (segS P y.bits ky d + 2 * lenAtom P (bit y.bits d) ky) := by
  have hlB : lenAtom P (bit x.bits d) kx = lenB P (2 * kx) := by simp [lenAtom, hbx]
  have hlA : lenAtom P (bit y.bits d) ky = lenA P (4 * ky) := by simp [lenAtom, hby]
  set σx := segS P x.bits kx d
  set σy := segS P y.bits ky d
  set lB := lenAtom P (bit x.bits d) kx
  set lA := lenAtom P (bit y.bits d) ky
  -- Case A: an atom `B(2kx)` of `x` is followed entirely within `y`'s segment.
  have caseA : ∀ α, (α = σx ∨ α = σx + lB) → y.W.τ σy ≤ x.W.τ α →
      x.W.τ (α + lB) ≤ y.W.τ (σy + 2 * lA) → ∃ t, Meet (E.rt x) (E.rt y) x.W y.W t ∧
        t ≤ x.W.τ (σx + 2 * lB) ∧ t ≤ y.W.τ (σy + 2 * lA) := by
    intro α hα h1 h2
    have hmono := lenA_mono hP (show 4 * ky ≤ 4 * (2 * kx) by omega)
    obtain ⟨t, ht, hte⟩ := count_atomB hy hx (x := y) (y := x) (k := kx) (i := d) hkx1
      (by omega) hdx hbx hα (j0 := σy) h1
      (by rw [← hlB]; exact h2.trans (y.W.τ_le (by rw [hlA] at *; omega)))
    rw [← hlB] at hte
    refine ⟨t, ht.symm, hte.trans (x.W.τ_le ?_), hte.trans h2⟩
    rcases hα with rfl | rfl <;> omega
  -- Case B: an atom `A(4ky)` of `y` is followed entirely within `x`'s segment.
  have caseB : ∀ α, (α = σy ∨ α = σy + lA) → x.W.τ σx ≤ y.W.τ α →
      y.W.τ (α + lA) ≤ x.W.τ (σx + 2 * lB) → ∃ t, Meet (E.rt x) (E.rt y) x.W y.W t ∧
        t ≤ x.W.τ (σx + 2 * lB) ∧ t ≤ y.W.τ (σy + 2 * lA) := by
    intro α hα h1 h2
    have hend := atomB_end (E := E) (k := kx) x.v
    rw [E.Y'_len] at hend
    obtain ⟨t, ht, hte⟩ := rep_atomA_Y' hG hy (x := x) (y := y) (k := ky) (i := d) hky1
      (by omega) hdy hby hα (m' := 2 * kx) (by omega) (by omega)
      (rep_segB E hx hkx1 hdx hbx) h1
      (by rw [← hlA, add_mul, hend, ← hlB]; convert h2 using 2; ring)
    rw [← hlA] at hte
    refine ⟨t, ht, hte.trans h2, hte.trans (y.W.τ_le ?_)⟩
    rcases hα with rfl | rfl <;> omega
  by_cases hc1 : y.W.τ σy ≤ x.W.τ σx
  · by_cases hc2 : x.W.τ (σx + lB) ≤ y.W.τ (σy + 2 * lA)
    · exact caseA σx (Or.inl rfl) hc1 hc2
    · rw [not_le] at hc2
      exact caseB (σy + lA) (Or.inr rfl) h3.le
        (by rw [add_assoc, ← two_mul]; exact hc2.le.trans (x.W.τ_le (by omega)))
  · rw [not_le] at hc1
    by_cases hc3 : y.W.τ (σy + lA) ≤ x.W.τ (σx + 2 * lB)
    · exact caseB σy (Or.inl rfl) hc1.le hc3
    · rw [not_le] at hc3
      exact caseA (σx + lB) (Or.inr rfl) h4.le
        (by rw [add_assoc, ← two_mul]; exact hc3.le.trans (y.W.τ_le (by omega)))

end Podc.AsyncRendezvousPoly
